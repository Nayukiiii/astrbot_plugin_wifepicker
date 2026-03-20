"""
affinity_composer.py
─────────────────────────────────────────────────────────────────────
将 QQ 头像合成到带透明区域的 CG 图中，自动检测每个透明洞的位置/尺寸。

使用方式（在 _send_love_effect 里调用）：
    composer = AffinityComposer(cg_path)
    result_b64 = await composer.compose(qq_a, qq_b, session)   # aiohttp session
    # result_b64 是完整的 base64 PNG 字符串（不含 data: 前缀）
─────────────────────────────────────────────────────────────────────
"""

from __future__ import annotations

import asyncio
import base64
import io
import logging
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

import aiohttp
from PIL import Image, ImageDraw, ImageFilter

logger = logging.getLogger(__name__)


# ─────────────────────────────────────────────
# 数据结构
# ─────────────────────────────────────────────

@dataclass
class AvatarSlot:
    """一个透明区域对应的插槽信息"""
    x: int          # 左上角 x
    y: int          # 左上角 y
    w: int          # 宽度
    h: int          # 高度
    cx: float       # 质心 x（用于排序）
    cy: float       # 质心 y
    radius: int     # 建议圆角半径（w/h 的 1/8，最大 12px）


@dataclass
class AvatarInfo:
    """对应 HTML 模板注入用"""
    x: int
    y: int
    w: int
    h: int
    radius: int
    data_uri: str   # base64 data URI


# ─────────────────────────────────────────────
# 透明区域检测
# ─────────────────────────────────────────────

def _detect_transparent_slots(
    img: Image.Image,
    alpha_threshold: int = 30,
    min_area: int = 400,
    merge_gap: int = 8,
) -> list[AvatarSlot]:
    """
    检测 PNG 中所有透明区域，返回按从左到右排列的 AvatarSlot 列表。

    算法：
    1. 提取 alpha 通道，二值化（< threshold → 透明）
    2. 用连通域标注（手写 BFS，避免引入 scipy 依赖）
    3. 对每个连通域计算 bounding-box
    4. 过滤太小的区域（噪点/边缘抗锯齿）
    5. 按质心 x 从左到右排序
    """
    if img.mode != "RGBA":
        img = img.convert("RGBA")

    alpha = img.split()[3]  # PIL Image, mode='L'
    W, H = alpha.size
    alpha_data = alpha.load()

    # 二值 mask：True = 透明
    transparent = [[alpha_data[x, y] < alpha_threshold for x in range(W)] for y in range(H)]

    visited = [[False] * W for _ in range(H)]
    slots: list[AvatarSlot] = []

    def bfs(sx: int, sy: int) -> Optional[AvatarSlot]:
        """BFS 找一个连通透明域，返回其 AvatarSlot"""
        queue = [(sx, sy)]
        visited[sy][sx] = True
        min_x, min_y, max_x, max_y = sx, sy, sx, sy
        pixels: list[tuple[int, int]] = [(sx, sy)]

        head = 0
        while head < len(queue):
            cx, cy = queue[head]; head += 1
            for dx, dy in ((-1,0),(1,0),(0,-1),(0,1)):
                nx, ny = cx+dx, cy+dy
                if 0 <= nx < W and 0 <= ny < H and not visited[ny][nx] and transparent[ny][nx]:
                    visited[ny][nx] = True
                    queue.append((nx, ny))
                    pixels.append((nx, ny))
                    min_x = min(min_x, nx); max_x = max(max_x, nx)
                    min_y = min(min_y, ny); max_y = max(max_y, ny)

        area = len(pixels)
        if area < min_area:
            return None

        bw = max_x - min_x + 1
        bh = max_y - min_y + 1
        # 质心
        ccx = sum(p[0] for p in pixels) / area
        ccy = sum(p[1] for p in pixels) / area
        radius = min(12, max(4, min(bw, bh) // 8))
        return AvatarSlot(min_x, min_y, bw, bh, ccx, ccy, radius)

    for y in range(H):
        for x in range(W):
            if transparent[y][x] and not visited[y][x]:
                slot = bfs(x, y)
                if slot is not None:
                    slots.append(slot)

    # 合并距离很近的连通域（同一个洞被抗锯齿割裂的情况）
    slots = _merge_nearby_slots(slots, merge_gap)

    # 按质心 x 从左到右
    slots.sort(key=lambda s: s.cx)
    return slots


def _merge_nearby_slots(slots: list[AvatarSlot], gap: int) -> list[AvatarSlot]:
    """把 bounding-box 相互重叠或间距 < gap 的 slot 合并"""
    if len(slots) <= 1:
        return slots

    merged = True
    while merged:
        merged = False
        result: list[AvatarSlot] = []
        used = [False] * len(slots)
        for i, a in enumerate(slots):
            if used[i]: continue
            combined = a
            for j, b in enumerate(slots):
                if i == j or used[j]: continue
                # 检查是否重叠/紧邻
                if (a.x - gap <= b.x + b.w and a.x + a.w + gap >= b.x and
                    a.y - gap <= b.y + b.h and a.y + a.h + gap >= b.y):
                    nx = min(combined.x, b.x)
                    ny = min(combined.y, b.y)
                    nw = max(combined.x + combined.w, b.x + b.w) - nx
                    nh = max(combined.y + combined.h, b.y + b.h) - ny
                    ncx = (combined.cx + b.cx) / 2
                    ncy = (combined.cy + b.cy) / 2
                    nrad = min(12, max(4, min(nw, nh) // 8))
                    combined = AvatarSlot(nx, ny, nw, nh, ncx, ncy, nrad)
                    used[j] = True
                    merged = True
            used[i] = True
            result.append(combined)
        slots = result

    return slots


# ─────────────────────────────────────────────
# 头像下载
# ─────────────────────────────────────────────

QQ_AVATAR_URL = "https://q4.qlogo.cn/headimg_dl?dst_uin={qq}&spec=640"

async def _fetch_avatar(qq: str, session: aiohttp.ClientSession) -> Image.Image:
    """下载 QQ 头像，返回 RGBA PIL Image"""
    url = QQ_AVATAR_URL.format(qq=qq)
    try:
        async with session.get(url, timeout=aiohttp.ClientTimeout(total=10)) as resp:
            data = await resp.read()
        img = Image.open(io.BytesIO(data)).convert("RGBA")
        return img
    except Exception as e:
        logger.warning(f"头像下载失败 qq={qq}: {e}，使用占位图")
        # 返回一个粉色占位图
        placeholder = Image.new("RGBA", (200, 200), (200, 120, 150, 255))
        return placeholder


# ─────────────────────────────────────────────
# 头像处理
# ─────────────────────────────────────────────

def _make_circle_avatar(avatar: Image.Image, diameter: int) -> Image.Image:
    """
    将头像裁成正圆，返回尺寸恰好为 (diameter, diameter)。
    圆形外像素完全透明，无任何外扩。
    """
    w = h = diameter
    src_w, src_h = avatar.size
    scale = max(w / src_w, h / src_h)
    new_w = math.ceil(src_w * scale)
    new_h = math.ceil(src_h * scale)
    resized = avatar.resize((new_w, new_h), Image.LANCZOS)
    left = (new_w - w) // 2
    top  = (new_h - h) // 2
    cropped = resized.crop((left, top, left + w, top + h)).convert("RGBA")

    mask = Image.new("L", (w, h), 0)
    ImageDraw.Draw(mask).ellipse([0, 0, w - 1, h - 1], fill=255)

    result = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    result.paste(cropped, (0, 0))
    result.putalpha(mask)
    return result


# ─────────────────────────────────────────────
# 主合成器
# ─────────────────────────────────────────────

class AffinityComposer:
    """
    CG 图 + QQ 头像 → 合成 PNG (base64)

    构造时传入 CG 图路径（PNG，带透明区域），
    会自动检测插槽并缓存结果。
    每次 compose() 调用只做：下载头像 + 填充 + 编码，速度快。
    """

    # 类级别缓存：{cg_path_str: (mtime, slots)}
    _slot_cache: dict[str, tuple[float, list[AvatarSlot]]] = {}

    def __init__(self, cg_path: str | Path):
        self.cg_path = Path(cg_path)
        self._cg_image: Optional[Image.Image] = None
        self._slots: Optional[list[AvatarSlot]] = None

    # ── 懒加载 & 缓存 ──

    def _load_cg(self) -> Image.Image:
        if self._cg_image is None:
            self._cg_image = Image.open(self.cg_path).convert("RGBA")
        return self._cg_image

    def get_slots(self) -> list[AvatarSlot]:
        """获取插槽列表，带文件修改时间缓存"""
        path_str = str(self.cg_path)
        try:
            mtime = self.cg_path.stat().st_mtime
        except FileNotFoundError:
            raise FileNotFoundError(f"CG 图不存在：{self.cg_path}")

        cached = AffinityComposer._slot_cache.get(path_str)
        if cached and cached[0] == mtime:
            return cached[1]

        logger.info(f"[AffinityComposer] 检测透明区域：{self.cg_path.name}")
        cg = self._load_cg()
        slots = _detect_transparent_slots(cg)
        logger.info(f"[AffinityComposer] 检测到 {len(slots)} 个插槽")
        AffinityComposer._slot_cache[path_str] = (mtime, slots)
        self._slots = slots
        return slots

    # ── 主接口 ──

    async def compose(
        self,
        qq_a: str,
        qq_b: str,
        session: aiohttp.ClientSession,
    ) -> tuple[str, list[AvatarInfo]]:
        """
        合成图像。

        返回：
            (base64_png_str, avatar_infos)
            - base64_png_str：完整合成图的 base64（不含 data: 前缀）
            - avatar_infos：给 HTML 模板用的 AvatarInfo 列表（含 data_uri）

        如果检测到的插槽数 != 2，会 fallback 到把两张头像并排放在画面底部。
        """
        slots = self.get_slots()

        # 并发下载两张头像（IO，不阻塞event loop）
        av_a, av_b = await asyncio.gather(
            _fetch_avatar(qq_a, session),
            _fetch_avatar(qq_b, session),
        )

        # Pillow合成是CPU密集操作，丢到线程池避免阻塞event loop
        loop = asyncio.get_event_loop()
        result_b64, avatar_infos = await loop.run_in_executor(
            None, self._compose_sync, av_a, av_b, slots
        )
        return result_b64, avatar_infos

    def _compose_sync(
        self,
        av_a: "Image.Image",
        av_b: "Image.Image",
        slots: list,
    ) -> tuple[str, list[AvatarInfo]]:
        """同步Pillow合成，在线程池里执行。"""
        cg = self._load_cg().copy()

        if len(slots) < 2:
            slots = _fallback_slots(cg.width, cg.height)

        slot_a, slot_b = slots[0], slots[1]
        avatars_raw = [(av_a, slot_a), (av_b, slot_b)]

        avatar_infos: list[AvatarInfo] = []
        for av_img, slot in avatars_raw:
            diameter = min(slot.w, slot.h)
            cx = slot.x + slot.w // 2
            cy = slot.y + slot.h // 2
            composed_av = _make_circle_avatar(av_img, diameter)
            paste_x = cx - diameter // 2
            paste_y = cy - diameter // 2
            cg.paste(composed_av, (paste_x, paste_y), composed_av)

            buf = io.BytesIO()
            composed_av.save(buf, format="PNG")
            b64 = base64.b64encode(buf.getvalue()).decode()
            data_uri = f"data:image/png;base64,{b64}"

            avatar_infos.append(AvatarInfo(
                x=paste_x, y=paste_y, w=diameter, h=diameter,
                radius=diameter // 2, data_uri=data_uri,
            ))

        out_buf = io.BytesIO()
        cg.save(out_buf, format="PNG", optimize=True)
        result_b64 = base64.b64encode(out_buf.getvalue()).decode()

        return result_b64, avatar_infos


def _fallback_slots(img_w: int, img_h: int) -> list[AvatarSlot]:
    """
    CG 图没有检测到足够插槽时的保底布局：
    在画面底部左右各放一个 90×90 的头像框。
    """
    size = 90
    margin = img_w // 6
    y = img_h - size - 20
    return [
        AvatarSlot(margin, y, size, size, margin + size/2, y + size/2, 8),
        AvatarSlot(img_w - margin - size, y, size, size,
                   img_w - margin - size/2, y + size/2, 8),
    ]