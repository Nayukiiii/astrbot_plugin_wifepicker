import asyncio
import json
import os
import random
import re
import time
import asyncio
import base64
import tempfile
import uuid
from .affinity_composer import AffinityComposer
#from datetime import datetime
from datetime import datetime, timedelta

# ============================================================
# 日群友 - 指令名称（在这里修改）
# ============================================================
CMD_RI            = "日群友"        # 触发日群友
CMD_RI_RANKING    = "日群友排行"    # 查看谁日的最多
CMD_RI_GRAPH      = "日群友关系图"  # 今日日群友关系图
# ============================================================

import astrbot.api.message_components as Comp
from astrbot.api import AstrBotConfig, logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.star import Context, Star, StarTools
from astrbot.core.platform.sources.aiocqhttp.aiocqhttp_message_event import (
    AiocqhttpMessageEvent,
)
from astrbot.core.star.filter.permission import PermissionTypeFilter
from astrbot.core.star.star_handler import star_handlers_registry
from astrbot.core.utils.astrbot_path import get_astrbot_plugin_data_path

from .keyword_trigger import KeywordRoute, KeywordRouter, MatchMode, PermissionLevel
from .onebot_api import extract_message_id
from .waifu_relations import maybe_add_other_half_record

from .src.constants import _DEFAULT_KEYWORD_ROUTES
from .src.utils import (
    load_json,
    save_json,
    normalize_user_id_set,
    extract_target_id_from_message,
    is_allowed_group,           # 新增
    resolve_member_name,        # 新增
)

from .src.debug_utils import run_debug_graph
# 新增：导入 core helpers
from .src.core import (
    send_onebot_message,
    schedule_onebot_delete_msg,
    record_active,
    clean_rbq_stats,
    draw_excluded_users,
    force_marry_excluded_users,
    ensure_today_records,
    get_group_records,
    auto_set_other_half_enabled,
    auto_withdraw_enabled,
    auto_withdraw_delay_seconds,
    can_onebot_withdraw,
    cleanup_inactive,
)

class RandomWifePlugin(Star):
    def __init__(self, context: Context, config: AstrBotConfig = None):
        super().__init__(context)
        self.config = config

        self.curr_dir = os.path.dirname(__file__)

        self._withdraw_tasks: set[asyncio.Task] = set()
        
        # 数据存储相对路径
        self.data_dir = os.path.join(get_astrbot_plugin_data_path(), "random_wife")
        self.records_file = os.path.join(self.data_dir, "wife_records.json")
        self.active_file = os.path.join(self.data_dir, "active_users.json")
        self.forced_file = os.path.join(self.data_dir, "forced_marriage.json")
        self.rbq_stats_file = os.path.join(self.data_dir, "rbq_stats.json")
        self.usage_stats_file = os.path.join(self.data_dir, "usage_stats.json")
        self.anime_link_file = os.path.join(self.data_dir, "anime_link_daily.json")
        
        if not os.path.exists(self.data_dir):
            os.makedirs(self.data_dir, exist_ok=True)
            
        self.records = load_json(self.records_file, {"date": "", "groups": {}})
        self.active_users = load_json(self.active_file, {})
        self.forced_records = load_json(self.forced_file, {})
        self.rbq_stats = load_json(self.rbq_stats_file, {})
        self.usage_stats = load_json(
            self.usage_stats_file,
            {"commands": {}, "groups": {}, "users": {}, "daily": {}},
        )
        self.anime_link_daily = load_json(
            self.anime_link_file, {"date": "", "groups": {}}
        )

        # 日群友数据文件
        self.ri_stats_file = os.path.join(self.data_dir, "ri_stats.json")
        self.ri_records_file = os.path.join(self.data_dir, "ri_records.json")
        self.ri_daily_file = os.path.join(self.data_dir, "ri_daily.json")   # 每日一次限制
        self.ri_target_daily_file = os.path.join(self.data_dir, "ri_target_daily.json")  # 目标每日被日次数
        self.ri_invite_daily_file = os.path.join(self.data_dir, "ri_invite_daily.json")  # 每日跟日次数
        self.ri_stats = load_json(self.ri_stats_file, {})        # {group_id: {user_id: [timestamps...]}}
        self.ri_records = load_json(self.ri_records_file, {"date": "", "groups": {}})  # 今日关系图
        self.ri_daily = load_json(self.ri_daily_file, {"date": "", "groups": {}})      # {date, groups:{gid:{uid:True}}}
        self.ri_target_daily = load_json(self.ri_target_daily_file, {"date": "", "groups": {}})  # {date, groups:{gid:{uid:count}}}
        self.ri_invite_daily = load_json(self.ri_invite_daily_file, {"date": "", "groups": {}})  # {date, groups:{gid:{uid:count}}}

        # 强娶上锁数据 {group_id: {target_id: {"count": int, "date": str, "by": str}}}
        self.force_lock_file = os.path.join(self.data_dir, "force_lock.json")
        self.force_lock = load_json(self.force_lock_file, {})

        # ===== 恋爱系统 =====
        # {group_id: {"A_B": {"user_a": str, "user_b": str, "date": str}}}
        self.pure_love_file = os.path.join(self.data_dir, "pure_love.json")
        self.pure_love = load_json(self.pure_love_file, {})
        # 恋爱邀请等待 {group_id: {target_id: {"from": uid, "expire": ts, "from_name": str, "target_name": str}}}
        self._pure_love_pending: dict[str, dict[str, dict]] = {}

        # ===== 好感度系统 =====
        # {group_id: {"A->B": {"value": float, "last_force_date": str, "first_100": bool, "last_decay_date": str, "last_reset_month": str}}}
        self.affinity_file = os.path.join(self.data_dir, "affinity.json")
        self.affinity = load_json(self.affinity_file, {})
        # CG 图目录：插件目录下的 cg/ 子文件夹，放若干透明头像槽 PNG
        self._cg_dir = os.path.join(self.curr_dir, "cg")
        # AffinityComposer 缓存：{cg_filename: AffinityComposer}
        self._composers: dict[str, AffinityComposer] = {}

        # ===== 强娶每日次数(daily模式) =====
        # {group_id: {user_id: {"date": str, "count": int}}}
        self.force_daily_file = os.path.join(self.data_dir, "force_daily.json")
        self.force_daily = load_json(self.force_daily_file, {})

        self._keyword_router = KeywordRouter(routes=_DEFAULT_KEYWORD_ROUTES)
        self._keyword_handlers = {
            "draw_wife": self._cmd_draw_wife,
            "show_history": self._cmd_show_history,
            "force_marry": self._cmd_force_marry,
            "show_graph": self._cmd_show_graph,
            "rbq_ranking": self.rbq_ranking,
            "show_help": self._cmd_show_help,
            "reset_records": self._cmd_reset_records,
            "reset_force_cd": self._cmd_reset_force_cd,
            "ri": self._cmd_ri,
            "wo_ye_ri": self._cmd_wo_ye_ri,
            "ri_ranking": self._cmd_ri_ranking,
            "ri_graph": self._cmd_ri_graph,
            "affinity_query": self._cmd_affinity,
            "affinity_ranking": self._cmd_affinity_ranking,
            "love_ranking": self._cmd_love_ranking,
            "today_status": self._cmd_today_status,
        }
        self._keyword_action_to_command_handler = {
            "draw_wife": "draw_wife",
            "show_history": "show_history",
            "force_marry": "force_marry",
            "show_graph": "show_graph",
            "rbq_ranking": "rbq_ranking",
            "show_help": "show_help",
            "reset_records": "reset_records",
            "reset_force_cd": "reset_force_cd",
            "ri": CMD_RI,
            "wo_ye_ri": "我也日",
            "ri_ranking": CMD_RI_RANKING,
            "ri_graph": CMD_RI_GRAPH,
            "affinity_query": "好感度",
            "affinity_ranking": "好感度排行",
            "love_ranking": "恩爱排行",
            "today_status": "今日玩法",
        }
        self._keyword_trigger_block_prefixes = ("/", "!", "！")
        global _PLUGIN_INSTANCE
        _PLUGIN_INSTANCE = self
        logger.info(f"抽老婆插件已加载。数据目录: {self.data_dir}")

    # ============================================================
    # 跨插件联动 API（供 animewifex 等读取）
    # ============================================================

    def get_lover(self, group_id: str, user_id: str) -> str | None:
        """读取 user_id 今日恋爱绑定对象。无副作用。"""
        try:
            return self._get_pure_love_partner(str(group_id), str(user_id))
        except Exception:
            return None

    async def silent_draw_group_friend(self, event, *, group_id: str, user_id: str,
                                        nick: str, anime_wife_img: str | None = None) -> dict | None:
        """供 animewifex 反向调用：在 wifepicker 里抽今日老婆（群友），
        同时跑同担判定并缓存。返回 dict 或 None。

        返回字段：
          wife_id, wife_name, avatar_url, remaining,
          already_drawn (bool), tongdan (dict | None),
          partner_id (str | None: 恋爱绑定中则直接返回伴侣),
          all_tongdan: list[dict] 全群本命同担群友列表
        """
        try:
            group_id = str(group_id)
            user_id = str(user_id)
            logger.info(f"[联动] silent_draw_group_friend enter gid={group_id} uid={user_id}")
            if not is_allowed_group(group_id, self.config):
                logger.info(f"[联动] bail: 群 {group_id} 不在 wifepicker 白名单")
                return None

            # 恋爱绑定：直接返回伴侣信息，不抽
            partner_id = self._get_pure_love_partner(group_id, user_id)
            if partner_id:
                partner_name = f"用户({partner_id})"
                try:
                    if event.get_platform_name() == "aiocqhttp":
                        _members = await event.bot.api.call_action(
                            "get_group_member_list", group_id=int(group_id))
                        if isinstance(_members, dict) and "data" in _members:
                            _members = _members["data"]
                        partner_name = resolve_member_name(_members, user_id=partner_id, fallback=partner_name)
                except Exception:
                    pass
                return {
                    "partner_id": partner_id,
                    "partner_name": partner_name,
                    "avatar_url": f"https://q4.qlogo.cn/headimg_dl?dst_uin={partner_id}&spec=640",
                }

            # 已达每日上限：返回已抽信息
            daily_limit = self.config.get("daily_limit", 3)
            group_records = self._get_group_records(group_id)
            user_recs = [r for r in group_records if r["user_id"] == user_id]
            logger.info(f"[联动] user_recs={len(user_recs)} daily_limit={daily_limit}")
            if len(user_recs) >= daily_limit:
                last = user_recs[-1]
                wife_id = str(last.get("wife_id", ""))
                if wife_id:
                    tongdan = self._refresh_tongdan_for_pair(
                        group_id, user_id, wife_id, anime_wife_img
                    )
                    # 已抽满路径也做一次扫全群同担
                    members_al: list = []
                    try:
                        if event.get_platform_name() == "aiocqhttp":
                            members_al = await event.bot.api.call_action(
                                "get_group_member_list", group_id=int(group_id))
                            if isinstance(members_al, dict) and "data" in members_al:
                                members_al = members_al["data"]
                    except Exception:
                        pass
                    scan_candidates = list(self.active_users.get(group_id, {}).keys())
                    if members_al:
                        cm = {str(m.get("user_id")) for m in members_al}
                        scan_candidates = [u for u in scan_candidates if u in cm]
                    all_td = self._scan_all_tongdan(
                        group_id, user_id, anime_wife_img, scan_candidates, members_al
                    )
                    return {
                        "wife_id": wife_id,
                        "wife_name": last.get("wife_name", f"用户({wife_id})"),
                        "avatar_url": f"https://q4.qlogo.cn/headimg_dl?dst_uin={wife_id}&spec=640",
                        "remaining": 0,
                        "already_drawn": True,
                        "tongdan": tongdan,
                        "all_tongdan": all_td,
                    }
                return None

            self._track_usage(event, "draw_wife")
            self._cleanup_inactive(group_id)
            bot_id = str(event.get_self_id())

            members: list = []
            current_member_ids: list[str] = []
            try:
                if event.get_platform_name() == "aiocqhttp":
                    members = await event.bot.api.call_action(
                        "get_group_member_list", group_id=int(group_id))
                    if isinstance(members, dict) and "data" in members:
                        members = members["data"]
                    current_member_ids = [str(m.get("user_id")) for m in members]
            except Exception:
                pass

            active_pool = self.active_users.get(group_id, {})
            excluded = self._draw_excluded_users()
            excluded.update([bot_id, user_id, "0"])
            excluded.update(self._get_all_pure_love_users(group_id))
            if current_member_ids:
                pool = [uid for uid in active_pool.keys()
                        if uid not in excluded and uid in current_member_ids]
            else:
                pool = [uid for uid in active_pool.keys() if uid not in excluded]
            logger.info(f"[联动] active_pool={len(active_pool)} excluded={len(excluded)} "
                        f"current_members={len(current_member_ids)} pool={len(pool)}")
            if not pool:
                logger.info("[联动] bail: 活跃池/群成员过滤后为空")
                return None

            wife_id = random.choice(pool)
            wife_name = f"用户({wife_id})"
            try:
                wife_name = resolve_member_name(members, user_id=wife_id, fallback=wife_name)
            except Exception:
                pass

            timestamp = datetime.now().isoformat()
            group_records.append({
                "user_id": user_id, "wife_id": wife_id,
                "wife_name": wife_name, "timestamp": timestamp,
            })
            maybe_add_other_half_record(
                records=group_records, user_id=user_id, user_name=nick,
                wife_id=wife_id, wife_name=wife_name,
                enabled=self._auto_set_other_half_enabled(), timestamp=timestamp,
            )
            save_json(self.records_file, self.records, self.records_file, self.config)

            tongdan = self._refresh_tongdan_for_pair(
                group_id, user_id, wife_id, anime_wife_img
            )
            # 扫全群同担：对所有活跃成员（含未被抽中的人）做一次本命匹配
            scan_candidates = list(active_pool.keys())
            if current_member_ids:
                scan_candidates = [u for u in scan_candidates if u in current_member_ids]
            all_td = self._scan_all_tongdan(
                group_id, user_id, anime_wife_img, scan_candidates, members
            )
            return {
                "wife_id": wife_id,
                "wife_name": wife_name,
                "avatar_url": f"https://q4.qlogo.cn/headimg_dl?dst_uin={wife_id}&spec=640",
                "remaining": max(0, daily_limit - len(user_recs) - 1),
                "already_drawn": False,
                "tongdan": tongdan,
                "all_tongdan": all_td,
            }
        except Exception as e:
            logger.warning(f"[联动] silent_draw_group_friend 失败: {e}")
            return None

    def _refresh_tongdan_for_pair(self, group_id: str, user_id: str,
                                   friend_id: str, user_anime_img: str | None) -> dict | None:
        """对 (user_id, friend_id) 计算并缓存当天同担判定。"""
        inst = self._animewifex_instance()
        if inst is None:
            return None
        friend_anime_img = None
        try:
            f_wife = inst.get_today_wife_simple(group_id, friend_id)
            friend_anime_img = f_wife["img"] if f_wife else None
        except Exception:
            pass
        td = self._detect_tongdan(
            group_id, user_id, friend_id,
            user_wife_img=user_anime_img, friend_wife_img=friend_anime_img,
        )
        if td:
            self._save_tongdan_cache(group_id, user_id, friend_id, td)
        return td

    def _scan_all_tongdan(self, group_id: str, user_id: str, user_anime_img: str | None,
                          candidates: list[str], members: list) -> list[dict]:
        """扫描候选群友里所有跟当前用户本命有重叠 / 老婆互为本命 的人。
        命中时缓存配对 buff，便于强娶时生效。
        返回 [{uid, name, shared, reason, mult}]，按 shared 数量降序。
        """
        inst = self._animewifex_instance()
        if inst is None:
            return []
        try:
            my_ben = set(inst.get_benming_chars(group_id, user_id))
        except Exception:
            return []
        if not my_ben and not user_anime_img:
            return []
        out = []
        for fid in candidates:
            fid = str(fid)
            if fid == user_id:
                continue
            try:
                f_ben = set(inst.get_benming_chars(group_id, fid))
            except Exception:
                f_ben = set()
            f_wife_img = None
            try:
                f_wife = inst.get_today_wife_simple(group_id, fid)
                f_wife_img = f_wife["img"] if f_wife else None
            except Exception:
                pass
            td = self._detect_tongdan(
                group_id, user_id, fid,
                user_wife_img=user_anime_img, friend_wife_img=f_wife_img,
            )
            if not td:
                continue
            self._save_tongdan_cache(group_id, user_id, fid, td)
            name = f"用户({fid})"
            try:
                name = resolve_member_name(members, user_id=fid, fallback=name)
            except Exception:
                pass
            out.append({
                "uid": fid, "name": name,
                "shared": td["shared"], "reason": td["reason"], "mult": td["mult"],
            })
        out.sort(key=lambda x: len(x["shared"]), reverse=True)
        return out

    def add_force_marry_cooldown_minutes(self, group_id: str, user_id: str, minutes: int = 30) -> bool:
        """供 animewifex 反向调：给 user_id 加强娶冷却（NTR 传染）。
        - cd_mode=cooldown: 把 forced_records 时间戳推到 (now - cooldown) + minutes
        - cd_mode=daily: 直接给 force_daily 计数 +1（相当于扣一次次数）
        失败/无影响时返回 False。
        """
        try:
            group_id, user_id = str(group_id), str(user_id)
            cd_mode = self.config.get("force_marry_cd_mode", "daily")
            if cd_mode == "daily":
                self._increment_force_daily(group_id, user_id)
                return True
            # cooldown 模式：把 last_force_time 推到 "now - (cooldown_total - minutes_to_wait)"
            cd_total = int(self.config.get("force_marry_cooldown", 3600))
            wait = max(60, minutes * 60)
            target_last = time.time() - max(0, cd_total - wait)
            self.forced_records.setdefault(group_id, {})[user_id] = target_last
            save_json(self.forced_file, self.forced_records)
            return True
        except Exception as e:
            logger.warning(f"[联动] add_force_marry_cooldown_minutes 失败: {e}")
            return False

    def grant_force_marry_bonus(self, group_id: str, user_id: str, n: int = 1) -> bool:
        """供 animewifex 反向调：给 user_id 加 n 次额外强娶次数。
        daily 模式 → force_daily 计数 -n（相当于退还 n 次）
        cooldown 模式 → 直接把上次冷却抹掉
        """
        try:
            group_id, user_id = str(group_id), str(user_id)
            cd_mode = self.config.get("force_marry_cd_mode", "daily")
            if cd_mode == "daily":
                today = datetime.now().strftime("%Y-%m-%d")
                grp = self.force_daily.setdefault(group_id, {})
                rec = grp.get(user_id, {"date": today, "count": 0})
                if rec.get("date") != today:
                    rec = {"date": today, "count": 0}
                rec["count"] = max(0, int(rec.get("count", 0)) - int(n))
                grp[user_id] = rec
                save_json(self.force_daily_file, self.force_daily)
            else:
                self.forced_records.setdefault(group_id, {}).pop(user_id, None)
                save_json(self.forced_file, self.forced_records)
            return True
        except Exception as e:
            logger.warning(f"[联动] grant_force_marry_bonus 失败: {e}")
            return False

    def is_cp_protected(self, group_id: str, a: str, b: str) -> bool:
        """CP 双向保护：好感度达到该对随机锁定的阈值即生效。"""
        try:
            a, b = str(a), str(b)
            # 恋爱绑定一定保护
            partner = self.get_lover(group_id, a)
            if partner == b:
                return True
            # 随机阈值保护
            rec = self._get_affinity_record(str(group_id), a, b)
            value = float(rec.get("value", 0))
            threshold = float(rec.get("cp_protect_threshold", 0))
            return threshold > 0 and value >= threshold
        except Exception:
            return False

    # ============================================================
    # 恋爱系统 helpers
    # ============================================================

    def _ensure_today_pure_love(self) -> None:
        today = datetime.now().strftime("%Y-%m-%d")
        changed = False
        for gid in list(self.pure_love.keys()):
            group_data = self.pure_love[gid]
            expired = [k for k, v in group_data.items() if v.get("date") != today]
            for k in expired:
                del group_data[k]
                changed = True
            if not group_data:
                del self.pure_love[gid]
                changed = True
        if changed:
            save_json(self.pure_love_file, self.pure_love)

    def _get_pure_love_partner(self, group_id: str, user_id: str) -> str | None:
        self._ensure_today_pure_love()
        for v in self.pure_love.get(group_id, {}).values():
            if v.get("user_a") == user_id:
                return v.get("user_b")
            if v.get("user_b") == user_id:
                return v.get("user_a")
        return None

    def _get_all_pure_love_users(self, group_id: str) -> set[str]:
        self._ensure_today_pure_love()
        users = set()
        for v in self.pure_love.get(group_id, {}).values():
            users.add(v.get("user_a", ""))
            users.add(v.get("user_b", ""))
        users.discard("")
        return users

    def _create_pure_love(self, group_id: str, user_a: str, user_b: str) -> None:
        today = datetime.now().strftime("%Y-%m-%d")
        key = f"{min(user_a, user_b)}_{max(user_a, user_b)}"
        if group_id not in self.pure_love:
            self.pure_love[group_id] = {}
        self.pure_love[group_id][key] = {"user_a": user_a, "user_b": user_b, "date": today}
        save_json(self.pure_love_file, self.pure_love)

    # ============================================================
    # 好感度系统 helpers
    # ============================================================

    def _affinity_key(self, a: str, b: str) -> str:
        return f"{min(a,b)}->{max(a,b)}"

    def _get_affinity_record(self, group_id: str, a: str, b: str) -> dict:
        key = self._affinity_key(a, b)
        default = {
            "value": 0, "last_force_date": "", "first_100": False,
            "first_100_date": "", "last_decay_date": "", "last_reset_month": "",
            "last_gain": 0, "last_gain_date": "",
            "cp_protect_threshold": 0,
        }
        return self.affinity.get(group_id, {}).get(key, dict(default))

    def _ensure_affinity_monthly_reset(self, group_id: str) -> None:
        cm = datetime.now().strftime("%Y-%m")
        changed = False
        for key, rec in self.affinity.get(group_id, {}).items():
            if rec.get("last_reset_month", "") != cm:
                rec["value"] = 0
                rec["first_100"] = False
                rec["first_100_date"] = ""      # ★ 新增
                rec["last_gain"] = 0             # ★ 新增
                rec["last_gain_date"] = ""       # ★ 新增
                rec["last_reset_month"] = cm
                changed = True
        if changed:
            save_json(self.affinity_file, self.affinity)

    def _process_affinity_decay(self, group_id: str, a: str, b: str) -> None:
        key = self._affinity_key(a, b)
        rec = self.affinity.get(group_id, {}).get(key)
        if not rec or rec.get("value", 0) <= 0:
            return
        today = datetime.now().strftime("%Y-%m-%d")
        cm = datetime.now().strftime("%Y-%m")
        if rec.get("last_reset_month", "") != cm:
            rec["value"] = 0; rec["first_100"] = False; rec["last_reset_month"] = cm
            save_json(self.affinity_file, self.affinity); return
        last_decay = rec.get("last_decay_date", "")
        if not last_decay or last_decay >= today:
            return
        if rec.get("last_force_date", "") == today:
            rec["last_decay_date"] = today; return
        try:
            days = (datetime.strptime(today, "%Y-%m-%d") - datetime.strptime(last_decay, "%Y-%m-%d")).days
        except Exception:
            days = 1
        for _ in range(days):
            rec["value"] = max(0, rec.get("value", 0) - random.randint(1, 10))
            if rec["value"] <= 0:
                break
        rec["last_decay_date"] = today
        save_json(self.affinity_file, self.affinity)

    def _get_affinity_value(self, group_id: str, a: str, b: str) -> float:
        self._process_affinity_decay(group_id, a, b)
        return self._get_affinity_record(group_id, a, b).get("value", 0)

    def _increase_affinity(self, group_id: str, a: str, b: str) -> tuple[float, bool, dict]:
        """返回 (value, first_100, meta)
        meta: {fated: bool, fated_char: str|None, tongdan_mult: float|None, gain: int}
        """
        meta: dict = {"fated": False, "fated_char": None, "tongdan_mult": None, "gain": 0}
        base_gain = random.randint(1, 10)

        # 命中注定：A 的本命角色 == B 当天的二次元老婆（互相检查双向）
        fated, fated_char = self._check_fated_match(group_id, a, b)
        if fated:
            gain = 30
            source = "force_marry_fated"
            meta["fated"] = True
            meta["fated_char"] = fated_char
        else:
            # 本命同担命中：好感度增益按当天缓存的随机倍率放大
            tongdan = self._get_tongdan_cache(group_id, a, b) or self._get_tongdan_cache(group_id, b, a)
            if tongdan and tongdan.get("shared"):
                mult = float(tongdan.get("mult", 1.0))
                gain = int(round(base_gain * mult))
                meta["tongdan_mult"] = mult
                source = "force_marry_tongdan"
            else:
                gain = base_gain
                source = "force_marry"
        meta["gain"] = gain
        value, first_time, actual = self._increase_affinity_by(
            group_id, a, b, gain, source=source
        )
        meta["actual_gain"] = actual
        return value, first_time, meta

    def _check_fated_match(self, group_id: str, a: str, b: str) -> tuple[bool, str | None]:
        """命中注定：a 的本命 ∩ {b 今日二次元老婆} 不空 → 触发。双向。"""
        inst = self._animewifex_instance()
        if inst is None:
            return False, None
        try:
            a_ben = set(inst.get_benming_chars(group_id, a))
            b_ben = set(inst.get_benming_chars(group_id, b))
            a_wife = inst.get_today_wife_simple(group_id, a)
            b_wife = inst.get_today_wife_simple(group_id, b)
            a_wife_img = a_wife["img"] if a_wife else None
            b_wife_img = b_wife["img"] if b_wife else None
            if b_wife_img and b_wife_img in a_ben:
                return True, b_wife_img
            if a_wife_img and a_wife_img in b_ben:
                return True, a_wife_img
        except Exception:
            return False, None
        return False, None

    def _animewifex_is_karma_locked(self, group_id: str, uid: str) -> bool:
        inst = self._animewifex_instance()
        if inst is None:
            return False
        try:
            return bool(inst.is_karma_locked(str(group_id), str(uid)))
        except Exception:
            return False

    def _increase_affinity_by(
        self, group_id: str, a: str, b: str, gain: int, *, source: str = ""
    ) -> tuple[float, bool, int]:
        key = self._affinity_key(a, b)
        if group_id not in self.affinity:
            self.affinity[group_id] = {}
        if key not in self.affinity[group_id]:
            # CP 双向保护阈值：每对首次互动时锁定一个 50~100 的随机值
            self.affinity[group_id][key] = {
                "value": 0, "last_force_date": "", "first_100": False,
                "first_100_date": "", "last_decay_date": "", "last_reset_month": "",
                "last_gain": 0, "last_gain_date": "",
                "cp_protect_threshold": random.randint(50, 100),
            }
        rec = self.affinity[group_id][key]
        if "cp_protect_threshold" not in rec:
            rec["cp_protect_threshold"] = random.randint(50, 100)
        today = datetime.now().strftime("%Y-%m-%d")
        cm = datetime.now().strftime("%Y-%m")
        if rec.get("last_reset_month", "") != cm:
            rec["value"] = 0
            rec["first_100"] = False
            rec["first_100_date"] = ""
            rec["last_gain"] = 0
            rec["last_gain_date"] = ""
            rec["last_reset_month"] = cm
        self._process_affinity_decay(group_id, a, b)
        gain = max(0, int(gain))
        old_value = rec.get("value", 0)
        rec["value"] = min(100, old_value + gain)
        actual_gain = rec["value"] - old_value  # 可能被 min(100) 截断
        rec["last_force_date"] = today
        rec["last_decay_date"] = today
        if source:
            rec["last_source"] = source
        # ★ 记录今日增量（同一天多次强娶累加）
        if rec.get("last_gain_date") == today:
            rec["last_gain"] = rec.get("last_gain", 0) + actual_gain
        else:
            rec["last_gain"] = actual_gain
            rec["last_gain_date"] = today
        first_time = False
        if rec["value"] >= 100 and not rec.get("first_100", False):
            rec["first_100"] = True
            rec["first_100_date"] = today   # ★ 记录达成日期
            first_time = True
        save_json(self.affinity_file, self.affinity)
        return rec["value"], first_time, actual_gain

    def _get_all_affinity_pairs(self, group_id: str) -> list[dict]:
        self._ensure_affinity_monthly_reset(group_id)
        pairs = []
        for key, rec in self.affinity.get(group_id, {}).items():
            if rec.get("value", 0) <= 0:
                continue
            parts = key.split("->")
            if len(parts) != 2:
                continue
            pairs.append({
                "user_a": parts[0], "user_b": parts[1],
                "value": rec.get("value", 0),
                "first_100": rec.get("first_100", False),
                "first_100_date": rec.get("first_100_date", ""),
            })
        pairs.sort(key=lambda x: x["value"], reverse=True)
        return pairs

    # ============================================================
    # 强娶每日次数 helpers
    # ============================================================

    def _get_force_daily_count(self, group_id: str, user_id: str) -> int:
        today = datetime.now().strftime("%Y-%m-%d")
        rec = self.force_daily.get(group_id, {}).get(user_id, {})
        return rec.get("count", 0) if rec.get("date") == today else 0

    def _increment_force_daily(self, group_id: str, user_id: str) -> int:
        today = datetime.now().strftime("%Y-%m-%d")
        if group_id not in self.force_daily:
            self.force_daily[group_id] = {}
        rec = self.force_daily[group_id].get(user_id, {})
        if rec.get("date") != today:
            rec = {"date": today, "count": 0}
        rec["count"] = rec.get("count", 0) + 1
        self.force_daily[group_id][user_id] = rec
        save_json(self.force_daily_file, self.force_daily)
        return rec["count"]

    def _decrement_force_daily(self, group_id: str, user_id: str) -> int:
        """退还强娶次数（拒绝/超时时调用）"""
        today = datetime.now().strftime("%Y-%m-%d")
        if group_id not in self.force_daily:
            return 0
        rec = self.force_daily[group_id].get(user_id, {})
        if rec.get("date") != today:
            return 0
        rec["count"] = max(0, rec.get("count", 0) - 1)
        self.force_daily[group_id][user_id] = rec
        save_json(self.force_daily_file, self.force_daily)
        return rec["count"]

    def _get_keyword_trigger_mode(self) -> MatchMode:
        """从配置中获取匹配模式，默认用开头匹配降低上手成本。"""
        # 这里的 config.get 会读取插件配置，建议在控制面板设置里加上这个 key
        raw = self.config.get("keyword_trigger_mode", "starts_with")
        try:
            return MatchMode(str(raw))
        except ValueError:
            return MatchMode.STARTS_WITH

    def _clean_rbq_stats(self):
        return clean_rbq_stats(self)

    def _draw_excluded_users(self) -> set[str]:
        return draw_excluded_users(self)

    def _force_marry_excluded_users(self) -> set[str]:
        return force_marry_excluded_users(self)

    def _ensure_today_records(self) -> None:
        return ensure_today_records(self)

    def _get_group_records(self, group_id: str) -> list[dict]:
        return get_group_records(self, group_id)

    def _auto_set_other_half_enabled(self) -> bool:
        return auto_set_other_half_enabled(self)

    def _auto_withdraw_enabled(self) -> bool:
        return auto_withdraw_enabled(self)

    def _auto_withdraw_delay_seconds(self) -> int:
        return auto_withdraw_delay_seconds(self)

    def _can_onebot_withdraw(self, event: AstrMessageEvent) -> bool:
        return can_onebot_withdraw(self, event)

    async def _send_onebot_message(
        self, event: AstrMessageEvent, *, message: list[dict]
    ) -> object:
        return await send_onebot_message(self, event, message=message)

    def _schedule_onebot_delete_msg(self, client, *, message_id: object) -> None:
        return schedule_onebot_delete_msg(self, client, message_id=message_id)

    def _record_active(self, event: AstrMessageEvent) -> None:
        return record_active(self, event)

    def _inc_counter(self, data: dict, key: str, amount: int = 1) -> None:
        data[key] = int(data.get(key, 0)) + amount

    def _track_usage(self, event: AstrMessageEvent, command: str) -> None:
        group_id = str(event.get_group_id() or "private")
        user_id = str(event.get_sender_id() or "unknown")
        today = datetime.now().strftime("%Y-%m-%d")
        now = datetime.now().isoformat(timespec="seconds")

        stats = self.usage_stats
        stats.setdefault("commands", {})
        stats.setdefault("groups", {})
        stats.setdefault("users", {})
        stats.setdefault("daily", {})

        self._inc_counter(stats["commands"], command)

        group_stats = stats["groups"].setdefault(group_id, {"commands": {}, "users": {}})
        group_stats.setdefault("commands", {})
        group_stats.setdefault("users", {})
        self._inc_counter(group_stats["commands"], command)
        self._inc_counter(group_stats["users"], user_id)

        user_key = f"{group_id}:{user_id}"
        user_stats = stats["users"].setdefault(
            user_key,
            {"first_seen": now, "last_seen": now, "commands": {}, "days": {}},
        )
        user_stats["last_seen"] = now
        user_stats.setdefault("commands", {})
        user_stats.setdefault("days", {})
        self._inc_counter(user_stats["commands"], command)
        self._inc_counter(user_stats["days"], today)

        daily_stats = stats["daily"].setdefault(today, {"commands": {}, "groups": {}})
        daily_stats.setdefault("commands", {})
        daily_stats.setdefault("groups", {})
        self._inc_counter(daily_stats["commands"], command)
        daily_group = daily_stats["groups"].setdefault(
            group_id, {"commands": {}, "users": {}}
        )
        daily_group.setdefault("commands", {})
        daily_group.setdefault("users", {})
        self._inc_counter(daily_group["commands"], command)
        self._inc_counter(daily_group["users"], user_id)

        save_json(self.usage_stats_file, self.usage_stats)

    def _engagement_hint(self, kind: str = "default") -> str:
        if not self.config.get("engagement_hints_enabled", True):
            return ""

        hints = {
            "draw": "下一步：发「好感度」看进度，或「强娶 @TA」冲恋爱线。",
            "limit": "今天还能玩「关系图」「好感度排行」「日群友」，不只抽一次就结束。",
            "pool_empty": "让群里再有几个人随便说句话，活跃池热起来后就能开抽。",
            "force": "继续线索：发「好感度 @TA」看进度；好感度满 100 会进恩爱榜。",
            "ri": "群友可以接着发「我也日 @TA」，或者看「日群友关系图」。",
            "status": "今日入口：抽老婆 / 强娶 @某人 / 好感度排行 / 关系图。",
        }
        return hints.get(kind, hints["draw"])

    def _today_key(self) -> str:
        return datetime.now().strftime("%Y-%m-%d")

    # ============================================================
    # 跨插件联动：animewifex 实例 / 本命同担缓存
    # ============================================================

    def _animewifex_instance(self):
        """获取 animewifex 插件实例。未加载时返回 None。
        AstrBot 加载的插件不一定能通过顶层 import 找到，遍历 sys.modules。"""
        try:
            import sys
            mod = None
            for name, m in list(sys.modules.items()):
                if m is None:
                    continue
                if name.endswith("astrbot_plugin_animewifex.main") or name == "astrbot_plugin_animewifex":
                    mod = m
                    break
            if mod is None:
                return None
            get_instance = getattr(mod, "get_instance", None)
            if get_instance is None:
                return None
            return get_instance()
        except Exception:
            return None

    def _ensure_today_tongdan_cache(self) -> None:
        """同担 buff 缓存：{date, pairs: {gid: {"uid->fid": {mult, shared, anime_wife}}}}"""
        today = self._today_key()
        if self.anime_link_daily.get("date") != today or "pairs" not in self.anime_link_daily:
            self.anime_link_daily = {"date": today, "pairs": {}}

    def _tongdan_pair_key(self, a: str, b: str) -> str:
        return f"{a}->{b}"

    def _detect_tongdan(self, group_id: str, user_id: str, friend_id: str,
                        user_wife_img: str | None, friend_wife_img: str | None) -> dict | None:
        """判定本命同担：
        - 双方本命列表有交集，或
        - 一方今日二次元老婆 ∈ 另一方本命列表
        命中则返回 {shared: [...], reason: str, mult: float}，否则 None。
        倍率每次命中时在 1.3~2.0 之间随机。
        """
        inst = self._animewifex_instance()
        if inst is None:
            return None
        try:
            ben_a = set(inst.get_benming_chars(group_id, user_id))
            ben_b = set(inst.get_benming_chars(group_id, friend_id))
        except Exception:
            return None
        shared = list(ben_a & ben_b)
        reasons = []
        if shared:
            reasons.append("本命重叠")
        cross = []
        if friend_wife_img and friend_wife_img in ben_a:
            cross.append(friend_wife_img)
            reasons.append("TA 今日老婆是你的本命")
        if user_wife_img and user_wife_img in ben_b:
            cross.append(user_wife_img)
            reasons.append("你今日老婆是 TA 的本命")
        all_hits = list({*shared, *cross})
        if not all_hits:
            return None
        return {
            "shared": all_hits,
            "reason": " / ".join(reasons),
            "mult": round(random.uniform(1.3, 2.0), 2),
        }

    def _save_tongdan_cache(self, group_id: str, user_id: str, friend_id: str, info: dict) -> None:
        self._ensure_today_tongdan_cache()
        pairs = self.anime_link_daily["pairs"].setdefault(group_id, {})
        pairs[self._tongdan_pair_key(user_id, friend_id)] = info
        save_json(self.anime_link_file, self.anime_link_daily)

    def _get_tongdan_cache(self, group_id: str, user_id: str, friend_id: str) -> dict | None:
        self._ensure_today_tongdan_cache()
        pairs = self.anime_link_daily.get("pairs", {}).get(group_id, {})
        return pairs.get(self._tongdan_pair_key(user_id, friend_id))

    @filter.event_message_type(filter.EventMessageType.GROUP_MESSAGE)
    async def keyword_trigger(self, event: AstrMessageEvent):
        # 1. 检查开关
        if not self.config.get("keyword_trigger_enabled", True):
            return

        message_str = event.message_str
        if not message_str: return

        # 2. @bot / 唤醒前缀场景下跳过（仅使用关键词触发，无斜杠指令）
        if event.is_at_or_wake_command:
            return

        # 3. 如果消息本身就带了 / 或 !，跳过（本插件仅关键词触发）
        if message_str.startswith(self._keyword_trigger_block_prefixes):
            return
        # 3. 开始匹配关键词（例如：今日老婆）
        mode = self._get_keyword_trigger_mode()
        route = self._keyword_router.match_route(message_str, mode=mode)
        # 兼容模式：如果没有精准匹配，尝试命令式匹配
        if route is None:
            route = self._keyword_router.match_command_route(message_str)
        if route:
            if route.permission != PermissionLevel.MEMBER:
                yield event.plain_result("管理员命令请使用带前缀的正式指令触发。")
                event.stop_event()
                return
            # 记录活跃（既然说话了就要进池子）
            self._record_active(event)
            # 找到对应的函数，比如 _cmd_draw_wife
            handler = self._keyword_handlers.get(route.action)
            if handler:
                # 核心：手动运行你的函数并获取结果
                async for result in handler(event):
                    yield result
                
                # 处理完了，停止事件，防止再触发别的
                event.stop_event()
   
    @filter.event_message_type(filter.EventMessageType.ALL)
    async def track_active(self, event: AstrMessageEvent):
        self._record_active(event)

    def _cleanup_inactive(self, group_id: str):
        return cleanup_inactive(self, group_id)

    @filter.command("今日老婆", alias={"抽老婆"})
    async def draw_wife(self, event: AstrMessageEvent):
        async for result in self._cmd_draw_wife(event):
            yield result

    async def _cmd_draw_wife(self, event: AstrMessageEvent):
        # 清理完不在群的人后
        
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return

        group_id = str(event.get_group_id())
        save_json(self.active_file, self.active_users, self.active_file, self.config)
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "draw_wife")

        user_id, bot_id = str(event.get_sender_id()), str(event.get_self_id())
        self._cleanup_inactive(group_id)

        # ★ 恋爱检查：直接显示恋爱对象
        partner_id = self._get_pure_love_partner(group_id, user_id)
        if partner_id:
            partner_name = f"用户({partner_id})"
            try:
                if event.get_platform_name() == "aiocqhttp":
                    assert isinstance(event, AiocqhttpMessageEvent)
                    _members = await event.bot.api.call_action(
                        "get_group_member_list", group_id=int(group_id))
                    if isinstance(_members, dict) and "data" in _members:
                        _members = _members["data"]
                    partner_name = resolve_member_name(_members, user_id=partner_id, fallback=partner_name)
            except Exception:
                pass
            avatar_url = f"https://q4.qlogo.cn/headimg_dl?dst_uin={partner_id}&spec=640"
            text = f" 你与【{partner_name}】今日恋爱绑定中💕\n只属于彼此的一天哦~"
            if self._can_onebot_withdraw(event):
                message_id = await self._send_onebot_message(event, message=[
                    {"type": "at", "data": {"qq": user_id}},
                    {"type": "text", "data": {"text": text}},
                    {"type": "image", "data": {"file": avatar_url}},
                ])
                if message_id is not None:
                    self._schedule_onebot_delete_msg(event.bot, message_id=message_id)
                return
            chain = [Comp.At(qq=user_id), Comp.Plain(text), Comp.Image.fromURL(avatar_url)]
            yield event.chain_result(chain)
            return

        daily_limit = self.config.get("daily_limit", 3)
        group_records = self._get_group_records(group_id)
        user_recs = [r for r in group_records if r["user_id"] == user_id]
        today_count = len(user_recs)

        if today_count >= daily_limit:
            if daily_limit == 1:
                wife_record = user_recs[0]
                wife_name, wife_id = wife_record["wife_name"], wife_record["wife_id"]
                wife_avatar = (
                    f"https://q4.qlogo.cn/headimg_dl?dst_uin={wife_id}&spec=640"
                )
                if self._can_onebot_withdraw(event):
                    message_id = await self._send_onebot_message(
                        event,
                        message=[
                            {"type": "at", "data": {"qq": user_id}},
                            {
                                "type": "text",
                                "data": {
                                    "text": (
                                        f" 你今天已经有老婆了哦❤️~\n她是：【{wife_name}】\n"
                                        f"{self._engagement_hint('limit')}"
                                    )
                                },
                            },
                            {"type": "image", "data": {"file": wife_avatar}},
                        ],
                    )
                    if message_id is not None:
                        self._schedule_onebot_delete_msg(event.bot, message_id=message_id)
                    return

                chain = [
                    Comp.At(qq=user_id),
                    Comp.Plain(
                        f" 你今天已经有老婆了哦❤️~\n她是：【{wife_name}】\n"
                        f"{self._engagement_hint('limit')}"
                    ),
                    Comp.Image.fromURL(wife_avatar),
                ]
                yield event.chain_result(chain)
            else:
                text = (
                    f"你今天已经抽了{today_count}次老婆了，明天再来吧！\n"
                    f"{self._engagement_hint('limit')}"
                )
                if self._can_onebot_withdraw(event):
                    message_id = await self._send_onebot_message(
                        event, message=[{"type": "text", "data": {"text": text}}]
                    )
                    if message_id is not None:
                        self._schedule_onebot_delete_msg(event.bot, message_id=message_id)
                    return

                yield event.plain_result(text)
            return

        # --- 增强：获取最新的群成员列表以过滤退群者 ---
        current_member_ids: list[str] = []
        members = []
        try:
            if event.get_platform_name() == "aiocqhttp":
                assert isinstance(event, AiocqhttpMessageEvent)
                members = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id)
                )
                if (
                    isinstance(members, dict)
                    and "data" in members
                    and isinstance(members["data"], list)
                ):
                    members = members["data"]
                current_member_ids = [str(m.get("user_id")) for m in members]
        except Exception as e:
            logger.error(f"获取群成员列表失败，将使用缓存池: {e}")

        active_pool = self.active_users.get(group_id, {})
        excluded = self._draw_excluded_users()
        excluded.update([bot_id, user_id, "0"])
        # ★ 排除恋爱中的用户
        excluded.update(self._get_all_pure_love_users(group_id))

        # 核心逻辑：如果在 aiocqhttp 平台，只从【当前还在群里】的人中抽取
        if current_member_ids:
            pool = [
                uid
                for uid in active_pool.keys()
                if uid not in excluded and uid in current_member_ids
            ]

            # 同时顺便清理一下 active_users，把不在群里的人删掉
            removed_uids = [
                uid for uid in active_pool.keys() if uid not in current_member_ids
            ]
            if removed_uids:
                for r_uid in removed_uids:
                    del self.active_users[group_id][r_uid]
                save_json(self.active_file, self.active_users)
        else:
            pool = [uid for uid in active_pool.keys() if uid not in excluded]

        if not pool:
            yield event.plain_result(
                "老婆池还是空的（候选人需要在本群 30 天内发过言）。\n"
                f"{self._engagement_hint('pool_empty')}"
            )
            return

        wife_id = random.choice(pool)
        wife_name = f"用户({wife_id})"
        user_name = event.get_sender_name() or f"用户({user_id})"

        try:
            if event.get_platform_name() == "aiocqhttp":
                wife_name = resolve_member_name(
                    members, user_id=wife_id, fallback=wife_name
                )
                user_name = resolve_member_name(
                    members, user_id=user_id, fallback=user_name
                )
        except Exception:
            pass

        timestamp = datetime.now().isoformat()
        group_records.append(
            {
                "user_id": user_id,
                "wife_id": wife_id,
                "wife_name": wife_name,
                "timestamp": timestamp,
            }
        )

        maybe_add_other_half_record(
            records=group_records,
            user_id=user_id,
            user_name=user_name,
            wife_id=wife_id,
            wife_name=wife_name,
            enabled=self._auto_set_other_half_enabled(),
            timestamp=timestamp,
        )

        save_json(self.records_file, self.records, self.records_file, self.config)

        avatar_url = f"https://q4.qlogo.cn/headimg_dl?dst_uin={wife_id}&spec=640"
        suffix_text = (
            "\n请好好对待她哦❤️~ \n"
            f"剩余抽取次数：{max(0, daily_limit - today_count - 1)}次\n"
            f"{self._engagement_hint('draw')}"
        )
        if self._can_onebot_withdraw(event):
            message_id = await self._send_onebot_message(
                event,
                message=[
                    {"type": "at", "data": {"qq": user_id}},
                    {"type": "text", "data": {"text": f" 你的今日老婆是：\n\n【{wife_name}】\n"}},
                    {"type": "image", "data": {"file": avatar_url}},
                    {"type": "text", "data": {"text": suffix_text}},
                ],
            )
            if message_id is not None:
                self._schedule_onebot_delete_msg(event.bot, message_id=message_id)
            return

        chain = [
            Comp.At(qq=user_id),
            Comp.Plain(f" 你的今日老婆是：\n\n【{wife_name}】\n"),
            Comp.Image.fromURL(avatar_url),
            Comp.Plain(suffix_text),
        ]
        yield event.chain_result(chain)

    def _anime_char_display(self, img: str) -> str:
        name = os.path.splitext(str(img or ""))[0].split("/")[-1]
        if "!" in name:
            src, chara = name.split("!", 1)
            return f"《{src}》{chara}"
        return name or "?"

    @filter.command("我的老婆", alias={"抽取历史"})
    async def show_history(self, event: AstrMessageEvent):
        async for result in self._cmd_show_history(event):
            yield result

    async def _cmd_show_history(self, event: AstrMessageEvent):
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "show_history")

        user_id = str(event.get_sender_id())
        today = datetime.now().strftime("%Y-%m-%d")
        if self.records.get("date") != today:
            yield event.plain_result("你今天还没有抽过老婆哦~\n先发「抽老婆」开局。")
            return

        group_recs = self.records.get("groups", {}).get(group_id, {}).get("records", [])
        user_recs = [r for r in group_recs if r["user_id"] == user_id]
        if not user_recs:
            yield event.plain_result("你今天还没有抽过老婆哦~")
            return

        daily_limit = self.config.get("daily_limit", 3)
        res = [f"🌸 你今日的老婆记录 ({len(user_recs)}/{daily_limit})："]
        for i, r in enumerate(user_recs, 1):
            time_str = datetime.fromisoformat(r["timestamp"]).strftime("%H:%M")
            res.append(f"{i}. 【{r['wife_name']}】 ({time_str})")
        res.append(f"\n剩余次数：{max(0, daily_limit - len(user_recs))}次")
        res.append(self._engagement_hint("draw"))
        yield event.plain_result("\n".join(res))

    @filter.command("强娶")
    async def force_marry(self, event: AstrMessageEvent):
        async for result in self._cmd_force_marry(event):
            yield result

    async def _cmd_force_marry(self, event: AstrMessageEvent):
        """强娶 — 恋爱系统 + 好感度 + daily多次"""
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return

        user_id = str(event.get_sender_id())
        bot_id = str(event.get_self_id())
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "force_marry")

        now = time.time()
        today_str = datetime.now().strftime("%Y-%m-%d")

        # ★ 检查1：A 是否在恋爱中？
        partner_id = self._get_pure_love_partner(group_id, user_id)
        if partner_id:
            partner_name = f"用户({partner_id})"
            try:
                if event.get_platform_name() == "aiocqhttp":
                    assert isinstance(event, AiocqhttpMessageEvent)
                    _m = await event.bot.api.call_action("get_group_member_list", group_id=int(group_id))
                    if isinstance(_m, dict) and "data" in _m: _m = _m["data"]
                    partner_name = resolve_member_name(_m, user_id=partner_id, fallback=partner_name)
            except Exception:
                pass
            avatar_url = f"https://q4.qlogo.cn/headimg_dl?dst_uin={partner_id}&spec=640"
            text = f" 你与【{partner_name}】今日恋爱绑定中💕\n彼此是唯一哦~"
            if self._can_onebot_withdraw(event):
                mid = await self._send_onebot_message(event, message=[
                    {"type": "at", "data": {"qq": user_id}},
                    {"type": "text", "data": {"text": text}},
                    {"type": "image", "data": {"file": avatar_url}},
                ])
                if mid is not None: self._schedule_onebot_delete_msg(event.bot, message_id=mid)
                return
            yield event.chain_result([Comp.At(qq=user_id), Comp.Plain(text), Comp.Image.fromURL(avatar_url)])
            return

        # ★ 检查2：强娶次数
        cd_mode = self.config.get("force_marry_cd_mode", "daily")
        if cd_mode == "daily":
            daily_limit = int(self.config.get("force_marry_daily_limit", 2))
            used = self._get_force_daily_count(group_id, user_id)
            if used >= daily_limit:
                tomorrow = datetime.combine(datetime.now().date() + timedelta(days=1), datetime.min.time())
                rem = (tomorrow - datetime.now()).total_seconds()
                yield event.plain_result(
                    f"你今天的强娶次数已用完（{used}/{daily_limit}）！\n"
                    f"明天 00:00 刷新，还剩 {int(rem//3600)}小时{int((rem%3600)//60)}分。\n"
                    f"{self._engagement_hint('limit')}")
                return
        else:
            last_time = self.forced_records.setdefault(group_id, {}).get(user_id, 0)
            last_dt = datetime.fromtimestamp(last_time) if last_time else datetime.fromtimestamp(0)
            cd_days = self.config.get("force_marry_cd", 3)
            target_reset_dt = datetime.combine(last_dt.date(), datetime.min.time()) + timedelta(days=cd_days)
            remaining = target_reset_dt.timestamp() - now
            if remaining > 0:
                d, h, m = int(remaining // 86400), int((remaining % 86400) // 3600), int((remaining % 3600) // 60)
                yield event.plain_result(
                    f"你已经强娶过啦！\n请等待：{d}天{h}小时{m}分后再试。\n"
                    f"(重置时间：{target_reset_dt.strftime('%m-%d %H:%M')})\n"
                    f"{self._engagement_hint('limit')}")
                return

        # ★ 检查3：@目标
        target_id = extract_target_id_from_message(event)
        if not target_id or target_id == "all":
            yield event.plain_result(
                "请 @ 一个你想强娶的人。\n"
                "例：强娶 @某人；成功后会增加好感度。"
            )
            return
        if target_id == user_id:
            yield event.plain_result("不能娶自己！")
            return
        force_excluded = self._force_marry_excluded_users()
        force_excluded.update({bot_id, "0"})
        if target_id in force_excluded:
            yield event.plain_result("该用户在强娶排除列表中，无法被强娶。")
            return

        # 业力镜像保护：animewifex 业力锁的对象当天免被强娶
        if self._animewifex_is_karma_locked(group_id, target_id):
            yield event.plain_result("TA 今天背着二次元业力惩罚，正在面壁，强娶失败~")
            return

        # ★ 检查4：B 是否在恋爱中？
        target_partner = self._get_pure_love_partner(group_id, target_id)
        if target_partner:
            tp_name = f"用户({target_partner})"
            try:
                if event.get_platform_name() == "aiocqhttp":
                    _m = await event.bot.api.call_action("get_group_member_list", group_id=int(group_id))
                    if isinstance(_m, dict) and "data" in _m: _m = _m["data"]
                    tp_name = resolve_member_name(_m, user_id=target_partner, fallback=tp_name)
            except Exception:
                pass
            yield event.plain_result(f"对方已与【{tp_name}】建立恋爱关系💕，无法被强娶哦~")
            return

        # ★ 检查5：B 是否被上锁？
        lock_threshold = int(self.config.get("force_marry_lock_count", 2))
        lock_data = self.force_lock.get(group_id, {}).get(target_id, {})
        is_locked = lock_data.get("date") == today_str and lock_data.get("count", 0) >= lock_threshold
        lock_by = lock_data.get("by", "")
        triggered_pure_love_invite = False

        if is_locked:
            bypass_threshold = int(self.config.get("affinity_bypass_lock_threshold", 50))
            aff = self._get_affinity_value(group_id, user_id, target_id)
            if aff >= bypass_threshold:
                pass  # 好感度够高，无视锁
            elif lock_by == user_id:
                # 锁是自己造成的 → 恋爱邀请
                triggered_pure_love_invite = True
            else:
                yield event.plain_result(
                    f"对方今天已经被强娶了 {lock_threshold} 次，已上锁保护中！\n"
                    f"（好感度达到 {bypass_threshold} 可无视上锁）\n"
                    f"（需被日群友@指定日满 {self.config.get('force_marry_unlock_ri_count', 3)} 次才能解锁）")
                return

        # ★ 获取名字
        target_name = f"用户({target_id})"
        user_name = event.get_sender_name() or f"用户({user_id})"
        members = []
        try:
            if event.get_platform_name() == "aiocqhttp":
                assert isinstance(event, AiocqhttpMessageEvent)
                members = await event.bot.api.call_action("get_group_member_list", group_id=int(group_id))
                if isinstance(members, dict) and "data" in members and isinstance(members["data"], list):
                    members = members["data"]
                target_name = resolve_member_name(members, user_id=target_id, fallback=target_name)
                user_name = resolve_member_name(members, user_id=user_id, fallback=user_name)
        except Exception:
            pass

        # 如果触发恋爱邀请（锁住+锁是自己造成的）
        if triggered_pure_love_invite:
            # 消耗强娶次数
            if cd_mode == "daily":
                self._increment_force_daily(group_id, user_id)
            else:
                self.forced_records.setdefault(group_id, {})[user_id] = now
                save_json(self.forced_file, self.forced_records)
            # 好感度增加
            new_aff, _, _meta = self._increase_affinity(group_id, user_id, target_id)
            # 发送恋爱邀请
            yield event.plain_result(
                f"对方已被你锁住💕 好感度：{new_aff}%\n"
                f"系统已向对方发送恋爱邀请...")
            async for r in self._send_pure_love_invite(event, group_id, user_id, target_id, user_name, target_name, cd_mode):
                yield r
            return

        # ★ 正常强娶逻辑
        group_records = self._get_group_records(group_id)

        # ★ 检查今日老婆数上限
        wife_limit = int(self.config.get("force_marry_wife_limit", 1))
        today_wives = set(r["wife_id"] for r in group_records if r["user_id"] == user_id)
        if len(today_wives) >= wife_limit:
            yield event.plain_result(
                f"你今天已经强娶了 {len(today_wives)} 个老婆，达到上限（{wife_limit}）！\n"
                f"明天 00:00 刷新~")
            return

        # rbq 统计
        if group_id not in self.rbq_stats: self.rbq_stats[group_id] = {}
        if target_id not in self.rbq_stats[group_id]: self.rbq_stats[group_id][target_id] = []
        self.rbq_stats[group_id][target_id].append(time.time())
        self._clean_rbq_stats()
        save_json(self.rbq_stats_file, self.rbq_stats)

        # 叠加记录（不删旧老婆，同一目标不重复追加）
        already_has = any(r["user_id"] == user_id and r["wife_id"] == target_id for r in group_records)
        if not already_has:
            timestamp = datetime.now().isoformat()
            group_records.append({
                "user_id": user_id, "wife_id": target_id, "wife_name": target_name,
                "timestamp": timestamp, "forced": True,
            })
            maybe_add_other_half_record(
                records=group_records, user_id=user_id, user_name=user_name,
                wife_id=target_id, wife_name=target_name,
                enabled=self._auto_set_other_half_enabled(), timestamp=timestamp,
            )

        # 更新CD
        if cd_mode == "daily":
            self._increment_force_daily(group_id, user_id)
        else:
            self.forced_records.setdefault(group_id, {})[user_id] = now
            save_json(self.forced_file, self.forced_records)

        # ★ 更新上锁计数（含 by 字段）
        if group_id not in self.force_lock: self.force_lock[group_id] = {}
        t_lock = self.force_lock[group_id].get(target_id, {})
        if t_lock.get("date") != today_str:
            t_lock = {"date": today_str, "count": 0, "by": user_id}
        t_lock["count"] = t_lock.get("count", 0) + 1
        t_lock["by"] = user_id
        self.force_lock[group_id][target_id] = t_lock
        save_json(self.force_lock_file, self.force_lock)
        save_json(self.records_file, self.records)

        # ★ 检查是否刚触发上锁 → 直接发邀请并 return
        just_locked = (t_lock["count"] >= lock_threshold and not is_locked)

        if just_locked:
            new_aff, _, _meta = self._increase_affinity(group_id, user_id, target_id)
            avatar_url_jl = f"https://q4.qlogo.cn/headimg_dl?dst_uin={target_id}&spec=640"
            text_jl = (
                f" 💕 你强娶【{target_name}】触发了恋爱邀请！\n"
                f"好感度：{new_aff}%\n正在向对方发送恋爱邀请...\n"
                f"{self._engagement_hint('force')}"
            )
            if self._can_onebot_withdraw(event):
                mid_jl = await self._send_onebot_message(event, message=[
                    {"type": "at", "data": {"qq": user_id}},
                    {"type": "text", "data": {"text": text_jl}},
                    {"type": "image", "data": {"file": avatar_url_jl}},
                ])
                if mid_jl is not None:
                    self._schedule_onebot_delete_msg(event.bot, message_id=mid_jl)
            else:
                yield event.chain_result([
                    Comp.At(qq=user_id),
                    Comp.Plain(text_jl),
                    Comp.Image.fromURL(avatar_url_jl),
                ])
            async for r in self._send_pure_love_invite(
                event, group_id, user_id, target_id, user_name, target_name, cd_mode
            ):
                yield r
            return

        # ★ 好感度增加（非 just_locked 时）
        new_aff, first_100, meta = self._increase_affinity(group_id, user_id, target_id)
        aff_msg = f"\n💗 与 {target_name} 的好感度：{new_aff}%"
        if meta.get("fated"):
            # 命中注定：本命撞 TA 今日二次元老婆 → 大额奖励 + 群广播 + 称号
            fated_char_disp = self._anime_char_display(meta.get("fated_char") or "")
            aff_msg += (
                f"\n🌟 命中注定！你/TA 的本命就是对方今日的二次元老婆【{fated_char_disp}】"
                f"\n   好感度直接 +{meta.get('actual_gain', 30)}！"
            )
            # 给双方各发一个称号到 animewifex
            inst_aw = self._animewifex_instance()
            if inst_aw is not None:
                try:
                    title = f"命中注定·{datetime.now().strftime('%Y%m%d')}"
                    inst_aw.grant_title(group_id, user_id, title)
                    inst_aw.grant_title(group_id, target_id, title)
                except Exception:
                    pass
        elif meta.get("tongdan_mult"):
            aff_msg += f"\n✨ 本命同担 ×{meta['tongdan_mult']} 加成已生效"

        # ★ 恩爱特效文字
        love_msg = ""
        if first_100:
            love_msg = "\n🌸✨ 好感度满100！恩爱认证！✨🌸"
            # 资源互喂：100% 好感度 → 双方各送 1 张 animewifex 补签券
            inst_aw = self._animewifex_instance()
            if inst_aw is not None:
                try:
                    n_a = inst_aw.grant_streak_freeze(group_id, user_id, 1)
                    n_b = inst_aw.grant_streak_freeze(group_id, target_id, 1)
                    love_msg += f"\n🎁 双方各获 animewifex 补签券 ×1（你 {n_a} / TA {n_b}）"
                except Exception:
                    pass

        avatar_url = f"https://q4.qlogo.cn/headimg_dl?dst_uin={target_id}&spec=640"
        text = f" 你今天强娶了【{target_name}】哦❤️~\n请对她好一点哦~{aff_msg}{love_msg}\n"
        text += self._engagement_hint("force")

        if self._can_onebot_withdraw(event):
            mid = await self._send_onebot_message(event, message=[
                {"type": "at", "data": {"qq": user_id}},
                {"type": "text", "data": {"text": text}},
                {"type": "image", "data": {"file": avatar_url}},
            ])
            if mid is not None: self._schedule_onebot_delete_msg(event.bot, message_id=mid)
            return
        yield event.chain_result([Comp.At(qq=user_id), Comp.Plain(text), Comp.Image.fromURL(avatar_url)])

        # 恩爱特效
        if first_100:
            async for r in self._send_love_effect(event, group_id, user_id, target_id, user_name, target_name):
                yield r
                
    # ============================================================
    # 恋爱邀请流程
    # ============================================================

    async def _send_pure_love_invite(self, event, group_id, from_id, target_id, from_name, target_name, cd_mode="daily"):
        if group_id not in self._pure_love_pending:
            self._pure_love_pending[group_id] = {}
        self._pure_love_pending[group_id][target_id] = {
            "from": from_id, "from_name": from_name,
            "target_name": target_name, "expire": time.time() + 90,
            "cd_mode": cd_mode,
        }
        invite_text = (
            f" 💕 恋爱邀请 💕\n"
            f"【{from_name}】想和你建立今日恋爱关系！\n"
            f"回复「接受恋爱」或「拒绝恋爱」（90秒内有效）"
        )
        if self._can_onebot_withdraw(event):
            await self._send_onebot_message(event, message=[
                {"type": "at", "data": {"qq": target_id}},
                {"type": "text", "data": {"text": invite_text}},
            ])
        else:
            yield event.chain_result([Comp.At(qq=target_id), Comp.Plain(invite_text)])

    @filter.event_message_type(filter.EventMessageType.GROUP_MESSAGE)
    async def pure_love_response_listener(self, event: AstrMessageEvent):
        if event.is_private_chat():
            return
        group_id = str(event.get_group_id())
        user_id = str(event.get_sender_id())
        pending = self._pure_love_pending.get(group_id, {}).get(user_id)
        if not pending:
            return
        msg = event.message_str.strip()
        if msg not in ("接受恋爱", "拒绝恋爱"):
            return
        if time.time() > pending.get("expire", 0):
            del self._pure_love_pending[group_id][user_id]
            # 超时退还次数
            _cd_mode_exp = pending.get("cd_mode", "daily")
            _from_id_exp = pending.get("from", "")
            if _cd_mode_exp == "daily" and _from_id_exp:
                self._decrement_force_daily(group_id, _from_id_exp)
            yield event.plain_result("恋爱邀请已过期，强娶次数已退还~")
            event.stop_event()
            return
        from_id = pending["from"]
        from_name = pending.get("from_name", f"用户({from_id})")
        target_name = pending.get("target_name", f"用户({user_id})")
        cd_mode = pending.get("cd_mode", "daily")
        del self._pure_love_pending[group_id][user_id]
        if msg == "接受恋爱":
            self._create_pure_love(group_id, from_id, user_id)
            # 更新B今日老婆记录为A
            group_records = self._get_group_records(group_id)
            b_recs = [r for r in group_records if r["user_id"] == user_id]
            if b_recs:
                b_recs[-1]["wife_id"] = from_id
                b_recs[-1]["wife_name"] = from_name
            else:
                group_records.append({
                    "user_id": user_id, "wife_id": from_id, "wife_name": from_name,
                    "timestamp": datetime.now().isoformat(), "forced": True, "via_love_invite": True,
                })
            save_json(self.records_file, self.records)
            text = f"🌸💕 恋爱关系建立！💕🌸\n【{from_name}】 ❤️ 【{target_name}】\n今天只属于彼此~"
        else:
            # 拒绝退还次数
            if cd_mode == "daily":
                self._decrement_force_daily(group_id, from_id)
            text = f"【{target_name}】拒绝了恋爱邀请...💔\n（{from_name} 的强娶次数已退还）"
        if self._can_onebot_withdraw(event):
            await self._send_onebot_message(event, message=[{"type": "text", "data": {"text": text}}])
        else:
            yield event.plain_result(text)
        event.stop_event()

    # ============================================================
    # 恩爱特效
    # ============================================================

    async def _send_love_effect(self, event, group_id, user_a, user_b, name_a, name_b):
        """
        好感度满100特效：随机选 cg/ 目录里的一张 PNG，
        用 Pillow 合成 QQ 头像后直接发图。
        cg/ 为空时 fallback 纯文字。
        """
        import aiohttp as _aiohttp

        cg_files = self._list_cg_files()
        if not cg_files:
            yield event.plain_result(
                f"🌸✨ 【{name_a}】 ❤️ 【{name_b}】好感度满100！恩爱认证！✨🌸"
            )
            return

        import random as _rnd
        cg_name = _rnd.choice(cg_files)
        cg_path = os.path.join(self._cg_dir, cg_name)

        if cg_name not in self._composers:
            self._composers[cg_name] = AffinityComposer(cg_path)
        composer = self._composers[cg_name]

        try:
            async with _aiohttp.ClientSession() as session:
                result_b64, _ = await asyncio.wait_for(
                    composer.compose(user_a, user_b, session), timeout=20.0
                )
        except Exception as e:
            logger.error(f"CG 合成失败: {e}")
            yield event.plain_result(
                f"🌸✨ 【{name_a}】 ❤️ 【{name_b}】好感度满100！恩爱认证！✨🌸"
            )
            return

        tmp = os.path.join(tempfile.gettempdir(), f"ae_{uuid.uuid4().hex}.png")
        try:
            with open(tmp, "wb") as f:
                f.write(base64.b64decode(result_b64))
            yield event.image_result(tmp)
        except Exception as e:
            logger.error(f"发送 CG 特效图失败: {e}")
            yield event.plain_result(
                f"🌸✨ 【{name_a}】 ❤️ 【{name_b}】好感度满100！恩爱认证！✨🌸"
            )
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass
                
    def _list_cg_files(self) -> list[str]:
        """返回 cg/ 目录下所有 PNG 文件名列表（排序后）。"""
        if not os.path.isdir(self._cg_dir):
            return []
        return sorted(
            f for f in os.listdir(self._cg_dir)
            if f.lower().endswith(".png")
        )

    def _parse_cg_command(self, message_str: str, event) -> dict | None:
        """
        解析 /CG 命令参数，返回:
            {"id_a": str, "side_a": "left"|"right",
             "id_b": str, "side_b": "left"|"right",
             "cg": str}
        解析失败返回 None。

        支持格式：
            /CG @A @B 夜景.png
            /CG @A左 @B右 夜景.png
            /CG @A右 @B左 夜景.png
        """
        import re as _re

        # 提取所有 At 的 QQ 号
        # AstrBot message_str 格式：@昵称(QQ号) 或 [CQ:at,qq=QQ号]
        at_ids: list[str] = []
        cq_ids = _re.findall(r'\[CQ:at,qq=(\d+)\]', message_str)
        if cq_ids:
            at_ids = [uid for uid in cq_ids if uid != "0"]
        else:
            at_ids = _re.findall(r'@[^(]+\((\d+)\)', message_str)

        if len(at_ids) < 2:
            return None

        id_a, id_b = at_ids[0], at_ids[1]

        # 从原始消息里提取左右标记
        # 支持：@昵称左(QQ) 或 @昵称(QQ)左
        side_a, side_b = "left", "right"
        m_sides = (_re.findall(r'@[^(左右]*?(左|右)\(', message_str)
                   or _re.findall(r'@[^(]+\(\d+\)(左|右)', message_str))
        if len(m_sides) >= 2:
            side_a = "left" if m_sides[0] == "左" else "right"
            side_b = "left" if m_sides[1] == "左" else "right"
        elif len(m_sides) == 1:
            side_a = "left" if m_sides[0] == "左" else "right"
            side_b = "right" if side_a == "left" else "left"

        # 提取文件名
        clean = _re.sub(r'\[CQ:at,[^\]]*\]', '', message_str)
        clean = _re.sub(r'@\S+', '', clean).strip()
        m_file = _re.search(r'(\S+\.png)', clean, _re.IGNORECASE) \
                 or _re.search(r'(\S+\.png)', message_str, _re.IGNORECASE)
        if not m_file:
            return None

        return {
            "id_a": id_a, "side_a": side_a,
            "id_b": id_b, "side_b": side_b,
            "cg":   m_file.group(1),
        }

    # ============================================================
    # /好感度
    # ============================================================

    @filter.command("好感度")
    async def _cmd_affinity(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config): return
        self._track_usage(event, "affinity")
        user_id = str(event.get_sender_id())
        target_id = extract_target_id_from_message(event)

        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                _m = await event.bot.api.call_action("get_group_member_list", group_id=int(group_id))
                if isinstance(_m, dict) and "data" in _m: _m = _m["data"]
                for m in _m:
                    uid = str(m.get("user_id"))
                    user_map[uid] = m.get("card") or m.get("nickname") or uid
        except Exception:
            pass

        # ===== @某人模式：不变 =====
        if target_id and target_id != user_id:
            value = self._get_affinity_value(group_id, user_id, target_id)
            tname = user_map.get(target_id, f"用户({target_id})")
            bar = "█" * int(value / 5) + "░" * (20 - int(value / 5))
            yield event.plain_result(f"💗 你与【{tname}】的好感度\n[{bar}] {value}%")
            return

        # ===== 无@模式：今日老婆 + 今日增量 + CP列表 =====
        today = datetime.now().strftime("%Y-%m-%d")

        # 找今日老婆（从今日记录里取最新一条）
        group_records = self._get_group_records(group_id)
        today_wife = None
        for r in reversed(group_records):
            if r.get("user_id") == user_id:
                today_wife = r
                break

        lines = ["我的好感度"]

        if today_wife:
            wife_id = today_wife.get("wife_id", "")
            wife_name = user_map.get(wife_id, today_wife.get("wife_name", f"用户({wife_id})"))
            # 今日增量
            gain = 0
            if wife_id:
                rec = self._get_affinity_record(group_id, user_id, wife_id)
                if rec.get("last_gain_date") == today:
                    gain = rec.get("last_gain", 0)
            lines.append(f"今日老婆：【{wife_name}】")
            if gain > 0:
                lines.append(f"今日好感度 +{gain}%")
        else:
            lines.append("今日还没有抽老婆哦~")

        # CP列表
        self._ensure_affinity_monthly_reset(group_id)
        pairs = []
        for key, rec in self.affinity.get(group_id, {}).items():
            parts = key.split("->")
            if len(parts) != 2 or user_id not in parts: continue
            other = parts[1] if parts[0] == user_id else parts[0]
            val = rec.get("value", 0)
            if val > 0:
                pairs.append({"other": other, "value": val})

        if pairs:
            pairs.sort(key=lambda x: x["value"], reverse=True)
            lines.append("─────────────")
            lines.append("本月恋人好感度：")
            for p in pairs[:10]:
                name = user_map.get(p["other"], f"用户({p['other']})")
                bar = "█" * int(p["value"] / 10) + "░" * (10 - int(p["value"] / 10))
                lines.append(f"  {name}: [{bar}] {p['value']}%")
        else:
            lines.append("本月还没有好感度记录~")

        yield event.plain_result("\n".join(lines))

    # ============================================================
    # /查同担
    # ============================================================

    @filter.command("查同担", alias={"本命同担", "同担列表"})
    async def check_tongdan_cmd(self, event: AstrMessageEvent):
        async for r in self._cmd_check_tongdan(event):
            yield r

    async def _cmd_check_tongdan(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        user_id = str(event.get_sender_id())
        self._track_usage(event, "check_tongdan")

        inst = self._animewifex_instance()
        if inst is None:
            yield event.plain_result("没装/没启用 animewifex，本命同担功能不可用。")
            return
        my_ben = list(inst.get_benming_chars(group_id, user_id))
        my_wife = inst.get_today_wife_simple(group_id, user_id)
        my_wife_img = my_wife["img"] if my_wife else None
        if not my_ben:
            yield event.plain_result(
                "你还没设置本命，先在 animewifex 发「设置本命」选 3 个本命再来~"
            )
            return

        # 指定 @ 单独查
        target_id = ""
        for comp in event.get_messages():
            if hasattr(comp, "qq") and getattr(comp, "qq", None):
                tid = str(comp.qq)
                if tid != user_id and tid != "0":
                    target_id = tid
                    break

        members = []
        try:
            if event.get_platform_name() == "aiocqhttp":
                members = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id))
                if isinstance(members, dict) and "data" in members:
                    members = members["data"]
        except Exception:
            pass

        def _disp(img: str) -> str:
            name = os.path.splitext(str(img or ""))[0].split("/")[-1]
            if "!" in name:
                src, ch = name.split("!", 1)
                return f"《{src}》{ch}"
            return name or "?"

        if target_id:
            t_ben = list(inst.get_benming_chars(group_id, target_id))
            t_wife = inst.get_today_wife_simple(group_id, target_id)
            t_wife_img = t_wife["img"] if t_wife else None
            td = self._detect_tongdan(
                group_id, user_id, target_id,
                user_wife_img=my_wife_img, friend_wife_img=t_wife_img,
            )
            t_name = f"用户({target_id})"
            try:
                t_name = resolve_member_name(members, user_id=target_id, fallback=t_name)
            except Exception:
                pass
            if not td:
                yield event.plain_result(
                    f"你和【{t_name}】没本命同担：\n"
                    f"  你的本命：{', '.join(_disp(b) for b in my_ben) or '（空）'}\n"
                    f"  TA 的本命：{', '.join(_disp(b) for b in t_ben) or '（空）'}"
                )
                return
            self._save_tongdan_cache(group_id, user_id, target_id, td)
            shared_txt = "、".join(_disp(s) for s in td["shared"])
            yield event.plain_result(
                f"✨ 你和【{t_name}】本命同担命中（{td['reason']}）\n"
                f"共担：{shared_txt}\n"
                f"今天强娶 TA 时好感度 ×{td['mult']} 加成已锁定。"
            )
            return

        # 默认：扫全群活跃池
        active = list(self.active_users.get(group_id, {}).keys())
        if members:
            cm = {str(m.get("user_id")) for m in members}
            active = [u for u in active if u in cm]
        all_td = self._scan_all_tongdan(group_id, user_id, my_wife_img, active, members)
        if not all_td:
            yield event.plain_result(
                "本群活跃池里暂时没人跟你本命同担。\n"
                f"你的本命：{', '.join(_disp(b) for b in my_ben)}\n"
                "让群友也设个本命试试，发「设置本命」即可~"
            )
            return
        lines = [f"🎴 本群与你本命同担的群友（共 {len(all_td)} 位）"]
        for x in all_td[:15]:
            shared_disp = "、".join(_disp(s) for s in (x.get("shared") or [])[:3])
            lines.append(f"  · {x['name']}：{shared_disp} ×{x['mult']}")
        if len(all_td) > 15:
            lines.append(f"  …还有 {len(all_td) - 15} 位（仅显示前 15）")
        lines.append("\n强娶任意一位都触发同担 buff。")
        yield event.plain_result("\n".join(lines))

    # ============================================================
    # /好感度排行
    # ============================================================

    @filter.command("好感度排行")
    async def affinity_ranking_cmd(self, event: AstrMessageEvent):
        async for result in self._cmd_affinity_ranking(event):
            yield result

    async def _cmd_affinity_ranking(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("私聊看不了榜单哦~"); return
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config): return
        self._track_usage(event, "affinity_ranking")
        pairs = self._get_all_affinity_pairs(group_id)
        if not pairs:
            yield event.plain_result("本群还没有好感度记录~"); return
        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                _m = await event.bot.api.call_action("get_group_member_list", group_id=int(group_id))
                if isinstance(_m, dict) and "data" in _m: _m = _m["data"]
                for m in _m:
                    uid = str(m.get("user_id"))
                    user_map[uid] = m.get("card") or m.get("nickname") or uid
        except Exception:
            pass
        top = pairs[:10]
        ranking = [{"rank": i+1, "user_a": p["user_a"], "user_b": p["user_b"],
                     "name_a": user_map.get(p["user_a"], f"用户({p['user_a']})"),
                     "name_b": user_map.get(p["user_b"], f"用户({p['user_b']})"),
                     "value": p["value"]} for i, p in enumerate(top)]

        template_path = os.path.join(self.curr_dir, "affinity_ranking.html")
        if os.path.exists(template_path):
            with open(template_path, "r", encoding="utf-8") as f:
                tpl = f.read()
            h = 100 + len(ranking) * 80 + 50
            try:
                url = await asyncio.wait_for(self.html_render(tpl,
                    {"ranking": ranking, "title": "🌸 好感度排行 🌸"},
                    options={"type": "png", "quality": None, "full_page": False,
                             "clip": {"x": 0, "y": 0, "width": 480, "height": h},
                             "scale": "device", "device_scale_factor_level": "ultra"}), timeout=30.0)
                yield event.image_result(url); return
            except Exception as e:
                logger.error(f"渲染好感度排行失败: {e}")
        # fallback
        lines = ["🌸 好感度排行 🌸"]
        for r in ranking:
            lines.append(f"#{r['rank']} {r['name_a']} ❤️ {r['name_b']}: {r['value']}%")
        yield event.plain_result("\n".join(lines))

    # ============================================================
    # /恩爱排行
    # ============================================================

    @filter.command("恩爱排行")
    async def love_ranking_cmd(self, event: AstrMessageEvent):
        async for result in self._cmd_love_ranking(event):
            yield result

    async def _cmd_love_ranking(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("私聊看不了榜单哦~"); return
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config): return
        self._track_usage(event, "love_ranking")

        all_pairs = self._get_all_affinity_pairs(group_id)
        # 只取达成过100%的CP
        pairs = [p for p in all_pairs if p.get("first_100") and p.get("first_100_date")]
        if not pairs:
            yield event.plain_result("本月还没有情侣达成100%好感度呢~"); return

        # 按达成日期从早到晚排（越早越靠前）
        pairs.sort(key=lambda x: x["first_100_date"])

        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                _m = await event.bot.api.call_action("get_group_member_list", group_id=int(group_id))
                if isinstance(_m, dict) and "data" in _m: _m = _m["data"]
                for m in _m:
                    uid = str(m.get("user_id"))
                    user_map[uid] = m.get("card") or m.get("nickname") or uid
        except Exception:
            pass

        top = pairs[:10]
        ranking = [
            {
                "rank": i + 1,
                "user_a": p["user_a"], "user_b": p["user_b"],
                "name_a": user_map.get(p["user_a"], f"用户({p['user_a']})"),
                "name_b": user_map.get(p["user_b"], f"用户({p['user_b']})"),
                "value": p["value"],
                "first_100_date": p["first_100_date"],
            }
            for i, p in enumerate(top)
        ]

        for tpl_name in ("love_ranking.html", "affinity_ranking.html"):
            tp = os.path.join(self.curr_dir, tpl_name)
            if os.path.exists(tp):
                with open(tp, "r", encoding="utf-8") as f:
                    tpl = f.read()
                h = 100 + len(ranking) * 80 + 50
                try:
                    url = await asyncio.wait_for(self.html_render(tpl,
                        {"ranking": ranking, "title": " 恩爱排行 "},
                        options={"type": "png", "quality": None, "full_page": False,
                                 "clip": {"x": 0, "y": 0, "width": 480, "height": h},
                                 "scale": "device", "device_scale_factor_level": "ultra"}), timeout=30.0)
                    yield event.image_result(url); return
                except Exception as e:
                    logger.error(f"渲染恩爱排行失败: {e}")
        # fallback 文字
        lines = [" 恩爱排行（本月最快达成100%）"]
        for r in ranking:
            lines.append(f"#{r['rank']} {r['name_a']} ❤️ {r['name_b']}  达成日期：{r['first_100_date']}")
        yield event.plain_result("\n".join(lines))

    @filter.command("CG")
    async def cmd_cg(self, event: AstrMessageEvent):
        async for r in self._cmd_cg(event):
            yield r

    async def _cmd_cg(self, event: AstrMessageEvent):
        """
        /CG @A @B 夜景.png
        任意群友可用，立即生成并发送 CG 合成图。
        两人需有好感度记录。文件名不对时显示可用列表。
        """
        import aiohttp as _aiohttp

        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "cg")

        cg_files = self._list_cg_files()

        def _list_reply() -> str:
            if not cg_files:
                return "⚠️ cg/ 目录下暂无 PNG 图片。"
            names = "\n".join(f"  {i+1}. {f}" for i, f in enumerate(cg_files))
            return f"📁 可用 CG 列表：\n{names}"

        parsed = self._parse_cg_command(event.message_str, event)
        if parsed is None:
            yield event.plain_result(
                "格式：/CG @A @B 文件名.png\n"
                "可选：/CG @A左 @B右 文件名.png\n\n"
                + _list_reply()
            )
            return

        id_a, side_a = parsed["id_a"], parsed["side_a"]
        id_b, side_b = parsed["id_b"], parsed["side_b"]
        cg_name = parsed["cg"]

        # 校验文件
        if cg_name not in cg_files:
            yield event.plain_result(
                f"❌ 找不到 CG 图：{cg_name}\n\n" + _list_reply()
            )
            return

        # 校验 CP 有好感度记录
        key = self._affinity_key(id_a, id_b)
        if group_id not in self.affinity or key not in self.affinity[group_id]:
            yield event.plain_result("❌ 这两人还没有好感度记录，无法生成 CG 哦~")
            return

        # 左右冲突时以 side_a 为准
        if side_a == side_b:
            side_b = "right" if side_a == "left" else "left"

        left_id  = id_a if side_a == "left" else id_b
        right_id = id_a if side_a == "right" else id_b

        # 获取名字（可选，用于日志）
        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                _m = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id))
                if isinstance(_m, dict) and "data" in _m:
                    _m = _m["data"]
                for m in _m:
                    uid = str(m.get("user_id"))
                    user_map[uid] = m.get("card") or m.get("nickname") or uid
        except Exception:
            pass

        # Pillow 合成
        cg_path = os.path.join(self._cg_dir, cg_name)
        if cg_name not in self._composers:
            self._composers[cg_name] = AffinityComposer(cg_path)
        composer = self._composers[cg_name]

        try:
            async with _aiohttp.ClientSession() as session:
                result_b64, _ = await asyncio.wait_for(
                    composer.compose(left_id, right_id, session), timeout=20.0
                )
        except Exception as e:
            logger.error(f"/CG 合成失败: {e}")
            yield event.plain_result("❌ 生成 CG 图失败，请稍后再试。")
            return

        tmp = os.path.join(tempfile.gettempdir(), f"cg_{uuid.uuid4().hex}.png")
        try:
            with open(tmp, "wb") as f:
                f.write(base64.b64decode(result_b64))
            yield event.image_result(tmp)
        except Exception as e:
            logger.error(f"/CG 发图失败: {e}")
            yield event.plain_result("❌ 发送图片失败。")
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass

    @filter.command("关系图")
    async def show_graph(self, event: AstrMessageEvent):
        async for result in self._cmd_show_graph(event):
            yield result

    async def _cmd_show_graph(self, event: AstrMessageEvent):
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "show_graph")

        iter_count = self.config.get("iterations", 140)

        # --- 新增：读取 JS 文件内容 ---
        vis_js_path = os.path.join(self.curr_dir, "vis-network.min.js")
        vis_js_content = ""
        if os.path.exists(vis_js_path):
            with open(vis_js_path, "r", encoding="utf-8") as f:
                vis_js_content = f.read()
        else:
            logger.error(f"找不到 JS 文件: {vis_js_path}")
        # ---------------------------

        # 1. 读取模板文件内容
        template_path = os.path.join(self.curr_dir, "graph_template.html")
        if not os.path.exists(template_path):
            yield event.plain_result(f"错误：找不到模板文件 {template_path}")
            return

        with open(template_path, "r", encoding="utf-8") as f:
            graph_html = f.read()

        # 2. 获取数据 (假设你已经从 self.records 获取了 group_data)
        group_data = self.records.get("groups", {}).get(group_id, {}).get("records", [])

        group_name = "未命名群聊"
        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                # 获取群信息
                info = await event.bot.api.call_action(
                    "get_group_info", group_id=int(group_id)
                )
                if isinstance(info, dict) and "data" in info and isinstance(info["data"], dict):
                    info = info["data"]
                group_name = info.get("group_name", "未命名群聊")

                # 获取群成员列表构建映射
                members = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id)
                )
                if isinstance(members, dict) and "data" in members and isinstance(members["data"], list):
                    members = members["data"]

                if isinstance(members, list):
                    for m in members:
                        uid = str(m.get("user_id"))
                        name = m.get("card") or m.get("nickname") or uid
                        user_map[uid] = name

        except Exception as e:
            logger.warning(f"获取群信息失败: {e}")

        # 3. 渲染图片
        # 根据节点数量动态计算高度，避免拥挤
        # 动态计算你想要裁剪的区域大小
        unique_nodes = set()
        for r in group_data:
            unique_nodes.add(str(r.get("user_id")))
            unique_nodes.add(str(r.get("wife_id")))
        node_count = len(unique_nodes)

        # 假设我们想要从左上角 (0,0) 开始，裁剪一个动态高度的区域
        clip_width = 1920
        clip_height = 1080 + (max(0, node_count - 10) * 60)

        # 关系图叠层：从 animewifex 读取每位群友今日二次元老婆图 + 本命同担配对
        anime_wifes: dict = {}
        tongdan_pairs: list = []
        inst_aw = self._animewifex_instance()
        if inst_aw is not None:
            try:
                for uid in unique_nodes:
                    info = inst_aw.get_today_wife_simple(group_id, uid)
                    if not info:
                        continue
                    url = inst_aw.wife_image_url(info["img"])
                    if not url:
                        continue
                    anime_wifes[uid] = {"url": url, "name": info["name"]}
            except Exception as e:
                logger.warning(f"[关系图] 拉取二次元老婆失败: {e}")
            try:
                self._ensure_today_tongdan_cache()
                grp_pairs = self.anime_link_daily.get("pairs", {}).get(group_id, {})
                seen = set()
                for key, info in grp_pairs.items():
                    if not isinstance(info, dict) or not info.get("shared"):
                        continue
                    if "->" not in key:
                        continue
                    a, b = key.split("->", 1)
                    pair_k = tuple(sorted([a, b]))
                    if pair_k in seen:
                        continue
                    seen.add(pair_k)
                    tongdan_pairs.append({
                        "a": a, "b": b,
                        "mult": info.get("mult", 1.0),
                        "shared": len(info.get("shared") or []),
                    })
            except Exception as e:
                logger.warning(f"[关系图] 拉取同担对失败: {e}")

        try:
            url = await self.html_render(
                graph_html,
                {
                    "vis_js_content": vis_js_content,
                    "group_id": group_id,
                    "group_name": group_name,
                    "user_map": user_map,
                    "records": group_data,
                    "iterations": iter_count,
                    "anime_wifes": anime_wifes,
                    "tongdan_pairs": tongdan_pairs,
                },
                options={
                    "type": "png",
                    "quality": None,
                    "scale": "device",
                    # 必须传齐这四个参数，且必须是 int 或 float，不能是字符串
                    "clip": {
                        "x": 0,
                        "y": 0,
                        "width": clip_width,
                        "height": clip_height,
                    },
                    # 注意：使用 clip 时通常建议将 full_page 设为 False
                    "full_page": False,
                    "device_scale_factor_level": "ultra",
                },
            )
            yield event.image_result(url)
        except Exception as e:
            logger.error(f"渲染失败: {e}")

    @filter.command("rbq排行")
    async def rbq_ranking(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("私聊看不了榜单哦~")
            return
            
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "rbq_ranking")
        self._clean_rbq_stats() # 渲染前强制清理一次过期数据
        
        group_data = self.rbq_stats.get(group_id, {})
        if not group_data:
            yield event.plain_result("本群近30天还没有人被强娶过，大家都很有礼貌呢。")
            return

        # 获取群成员名字映射 (仿照关系图逻辑)
        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                members = await event.bot.api.call_action('get_group_member_list', group_id=int(group_id))
                for m in members:
                    uid = str(m.get("user_id"))
                    user_map[uid] = m.get("card") or m.get("nickname") or uid
        except Exception:
            pass

        # 构造排序数据
        sorted_list = []
        for uid, ts_list in group_data.items():
            sorted_list.append({
                "uid": uid,
                "name": user_map.get(uid, f"用户({uid})"),
                "count": len(ts_list)
            })
        
        # 按次数从大到小排，取前10
        sorted_list.sort(key=lambda x: x["count"], reverse=True)
        top_10 = sorted_list[:10]

        current_rank = 1
        for i, user in enumerate(top_10):
            if i > 0 and user["count"] < top_10[i-1]["count"]:
                current_rank = i + 1  # 排名跳跃到当前位置
            user["rank"] = current_rank

        # 读取新模板
        template_path = os.path.join(self.curr_dir, "rbq_ranking.html")
        if not os.path.exists(template_path):
            yield event.plain_result("错误：找不到排行模板 rbq_ranking.html")
            return
            
        with open(template_path, "r", encoding="utf-8") as f:
            template_content = f.read()

        try:
            # 计算数据行数，动态调整高度（10人大约550px就够了）
            #dynamic_height = 160 + (len(top_10) * 85)
            
            header_h = 100
            item_h = 60
            footer_h = 50
            rank_width = 400

            dynamic_height = header_h + (len(top_10) * item_h) + footer_h
            # 渲染图片
            url = await self.html_render(template_content, {
                "group_id": group_id,
                "ranking": top_10,
                "title": "❤️ 群rbq月榜 ❤️"
            },
            options={
                "type": "png",
                "quality": None,
                "full_page": False, # 关闭全页面，配合 clip 使用
                "clip": {
                    "x": 0,
                    "y": 0,
                    "width": rank_width,
                    "height": dynamic_height # 裁切的高度
                },
                "scale": "device",
                "device_scale_factor_level": "ultra"
            }
            )
            yield event.image_result(url)
        except Exception as e:
            logger.error(f"渲染RBQ排行失败: {e}")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("重置记录")
    async def reset_records(self, event: AstrMessageEvent):
        async for result in self._cmd_reset_records(event):
            yield result

    async def _cmd_reset_records(self, event: AstrMessageEvent):
        self.records = {"date": datetime.now().strftime("%Y-%m-%d"), "groups": {}}
        save_json(self.records_file, self.records)
        yield event.plain_result("今日抽取记录已重置！")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("好感度调整")
    async def cmd_affinity_adjust(self, event: AstrMessageEvent):
        async for r in self._cmd_affinity_adjust(event):
            yield r

    async def _cmd_affinity_adjust(self, event: AstrMessageEvent):
        """
        管理员调整已建立关系的 CP 好感度。
        格式：好感度调整 @A @B +20 | -10 | =50
        范围 0~100，不触发 first_100 特效。
        """
        import re as _re

        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return
        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return

        # 提取两个 At
        import re as _re2
        at_ids: list[str] = []
        cq_ids = _re2.findall(r'\[CQ:at,qq=(\d+)\]', event.message_str)
        if cq_ids:
            at_ids = [uid for uid in cq_ids if uid != "0"]
        else:
            at_ids = _re2.findall(r'@[^(]+\((\d+)\)', event.message_str)

        if len(at_ids) < 2:
            yield event.plain_result(
                "格式：好感度调整 @A @B +20\n"
                "支持 +N（加）、-N（减）、=N（设置），范围 0~100\n"
                "仅限已有好感度记录的 CP。"
            )
            return

        id_a, id_b = at_ids[0], at_ids[1]

        # 检查 affinity 记录
        key = self._affinity_key(id_a, id_b)
        if group_id not in self.affinity or key not in self.affinity[group_id]:
            yield event.plain_result("❌ 这两人还没有好感度记录，无法调整。")
            return

        # 解析调整值
        clean = _re.sub(r'\[CQ:at,[^\]]*\]', '', event.message_str)
        clean = _re.sub(r'@\S+', '', clean).strip()
        m = _re.search(r'([+\-=])(\d+)', clean)
        if not m:
            yield event.plain_result(
                "❌ 未找到调整值。\n"
                "格式：好感度调整 @A @B +20 / -10 / =50"
            )
            return

        op, num = m.group(1), int(m.group(2))
        rec = self.affinity[group_id][key]
        old_val = rec.get("value", 0)

        if op == "+":
            new_val = min(100, old_val + num)
        elif op == "-":
            new_val = max(0, old_val - num)
        else:
            new_val = max(0, min(100, num))

        rec["value"] = new_val
        save_json(self.affinity_file, self.affinity)

        # 获取名字
        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                _m = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id))
                if isinstance(_m, dict) and "data" in _m:
                    _m = _m["data"]
                for mem in _m:
                    uid = str(mem.get("user_id"))
                    user_map[uid] = mem.get("card") or mem.get("nickname") or uid
        except Exception:
            pass

        name_a = user_map.get(id_a, f"用户({id_a})")
        name_b = user_map.get(id_b, f"用户({id_b})")
        op_str = f"+{num}" if op == "+" else (f"-{num}" if op == "-" else f"={num}")

        yield event.plain_result(
            f"✅ 好感度调整成功\n"
            f"【{name_a}】 ❤️ 【{name_b}】\n"
            f"{old_val}% → {new_val}%（{op_str}）"
        )

    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("重置强娶时间")
    async def reset_force_cd(self, event: AstrMessageEvent):
        async for result in self._cmd_reset_force_cd(event):
            yield result

    async def _cmd_reset_force_cd(self, event: AstrMessageEvent):
        group_id = str(event.get_group_id())

        if hasattr(self, "forced_records") and group_id in self.forced_records:
            self.forced_records[group_id] = {}
            save_json(self.forced_file, self.forced_records)

        # 也清理 daily 模式的计数
        if hasattr(self, "force_daily") and group_id in self.force_daily:
            self.force_daily[group_id] = {}
            save_json(self.force_daily_file, self.force_daily)

        # 同时清 force_lock（上锁记录），避免重置后残留导致误判
        if hasattr(self, "force_lock") and group_id in self.force_lock:
            self.force_lock[group_id] = {}
            save_json(self.force_lock_file, self.force_lock)

        logger.info(f"[Wife] 已重置群 {group_id} 的强娶冷却时间")
        yield event.plain_result("✅ 本群强娶冷却时间已重置！现在大家可以再次强娶了。")

    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("重置强娶次数")
    async def reset_force_daily_count(self, event: AstrMessageEvent):
        async for result in self._cmd_reset_force_daily_count(event):
            yield result

    async def _cmd_reset_force_daily_count(self, event: AstrMessageEvent):
        group_id = str(event.get_group_id())
        today = datetime.now().strftime("%Y-%m-%d")
        if group_id in self.force_daily and self.force_daily[group_id]:
            for uid in self.force_daily[group_id]:
                self.force_daily[group_id][uid] = {"date": today, "count": 0}
            save_json(self.force_daily_file, self.force_daily)
            logger.info(f"[Wife] 已重置群 {group_id} 的今日强娶次数")
            yield event.plain_result("✅ 本群今日强娶次数已重置！（冷却时间不变）")
        else:
            yield event.plain_result("💡 本群今日还没有人使用过强娶。")

    @filter.command("抽老婆帮助", alias={"老婆插件帮助"})
    async def show_help(self, event: AstrMessageEvent):
        async for result in self._cmd_show_help(event):
            yield result

    async def _cmd_show_help(self, event: AstrMessageEvent):
        if not is_allowed_group(str(event.get_group_id()), self.config):
            return
        self._track_usage(event, "help")
        daily_limit = self.config.get("daily_limit", 3)
        force_daily = self.config.get("force_marry_daily_limit", 2)
        ri_prob = self.config.get("ri_probability", 80)
        help_text = (
            "===== 🌸 今日怎么玩 =====\n"
            "先发【抽老婆】开局，再用【强娶 @某人】推进好感度。\n"
            "装了 animewifex 时，抽老婆会顺手抽今日二次元老婆，本命同担命中强娶有 buff。\n"
            "想看局势：发【今日玩法】或【关系图】。\n"
            "\n===== 核心入口 =====\n"
            "抽老婆：随机抽取今日老婆（自动联动 animewifex）\n"
            "我的老婆：查看今日历史与剩余次数\n"
            "强娶 @某人：指定目标并增加好感度\n"
            "好感度 / 好感度 @某人：查看恋爱进度\n"
            "\n===== 群内看点 =====\n"
            "好感度排行 / 恩爱排行 / rbq排行\n"
            "日群友 / 我也日 @某人 / 日群友排行 / 日群友关系图\n"
            f"\n当前节奏：抽老婆每日 {daily_limit} 次，强娶每日 {force_daily} 次，日群友概率 {ri_prob}%。\n"
            "小提示：关键词触发开启后，不带 / 也能直接玩。"
        )
        yield event.plain_result(help_text)

    @filter.command("今日玩法", alias={"老婆状态", "老婆日报"})
    async def today_status(self, event: AstrMessageEvent):
        async for result in self._cmd_today_status(event):
            yield result

    async def _cmd_today_status(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return

        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "today_status")

        self._ensure_today_records()
        self._ensure_today_ri_records()
        self._ensure_today_tongdan_cache()
        group_records = self.records.get("groups", {}).get(group_id, {}).get("records", [])
        ri_records = self.ri_records.get("groups", {}).get(group_id, {}).get("records", [])
        tongdan_pairs = self.anime_link_daily.get("pairs", {}).get(group_id, {})
        tongdan_count = sum(1 for v in tongdan_pairs.values() if isinstance(v, dict) and v.get("shared"))
        active_count = len(self.active_users.get(group_id, {}))
        drawers = {str(r.get("user_id")) for r in group_records}
        wife_targets = {str(r.get("wife_id")) for r in group_records}
        forced_count = sum(1 for r in group_records if r.get("forced"))
        locked_count = sum(
            1
            for rec in self.force_lock.get(group_id, {}).values()
            if rec.get("date") == datetime.now().strftime("%Y-%m-%d")
            and rec.get("count", 0) >= int(self.config.get("force_marry_lock_count", 2))
        )

        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                members = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id)
                )
                if isinstance(members, dict) and "data" in members:
                    members = members["data"]
                for m in members:
                    uid = str(m.get("user_id"))
                    user_map[uid] = m.get("card") or m.get("nickname") or uid
        except Exception:
            pass

        pairs = self._get_all_affinity_pairs(group_id)
        top_pair = "暂无"
        if pairs:
            top = pairs[0]
            name_a = user_map.get(top["user_a"], f"用户({top['user_a']})")
            name_b = user_map.get(top["user_b"], f"用户({top['user_b']})")
            top_pair = f"{name_a} -> {name_b}：{top['value']}%"

        lines = [
            "===== 今日老婆局势 =====",
            f"活跃池：{active_count} 人",
            f"已抽老婆：{len(drawers)} 人 / {len(group_records)} 次",
            f"今日被抽中：{len(wife_targets)} 人",
            f"强娶记录：{forced_count} 次，上锁保护：{locked_count} 人",
            f"日群友：{len(ri_records)} 次",
            f"本命同担命中：{tongdan_count} 对",
            f"最高好感度：{top_pair}",
            "",
            self._engagement_hint("status"),
        ]
        yield event.plain_result("\n".join(lines))

    @filter.permission_type(filter.PermissionType.ADMIN)
    @filter.command("老婆插件数据", alias={"老婆数据", "老婆留存"})
    async def usage_stats_cmd(self, event: AstrMessageEvent):
        async for result in self._cmd_usage_stats(event):
            yield result

    async def _cmd_usage_stats(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return

        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "usage_stats")

        stats = self.usage_stats
        group_stats = stats.get("groups", {}).get(group_id, {})
        command_counts = group_stats.get("commands", {})
        user_counts = group_stats.get("users", {})
        top_commands = sorted(command_counts.items(), key=lambda x: x[1], reverse=True)[:6]
        top_text = "、".join(f"{name}:{count}" for name, count in top_commands) or "暂无"

        today = datetime.now().date()
        daily = stats.get("daily", {})
        rows = []
        total_7d_users: set[str] = set()
        for i in range(6, -1, -1):
            day = (today - timedelta(days=i)).strftime("%Y-%m-%d")
            group_daily = daily.get(day, {}).get("groups", {}).get(group_id, {})
            users = set(group_daily.get("users", {}).keys())
            total_7d_users.update(users)
            rows.append(f"{day[5:]}：{len(users)}人/{sum(group_daily.get('commands', {}).values())}次")

        yesterday = (today - timedelta(days=1)).strftime("%Y-%m-%d")
        today_key = today.strftime("%Y-%m-%d")
        users_today = set(
            daily.get(today_key, {}).get("groups", {}).get(group_id, {}).get("users", {}).keys()
        )
        users_yesterday = set(
            daily.get(yesterday, {}).get("groups", {}).get(group_id, {}).get("users", {}).keys()
        )
        d1_return = len(users_today & users_yesterday)

        lines = [
            "===== 老婆插件数据 =====",
            f"本群累计使用用户：{len(user_counts)} 人",
            f"近 7 天使用用户：{len(total_7d_users)} 人",
            f"昨日到今日回访：{d1_return} 人",
            f"热门命令：{top_text}",
            "",
            "近 7 天：",
            *rows,
            "",
            "观察建议：如果近 7 天人数低，先开关键词触发、提高每日次数，再用「今日玩法」把入口贴到群里。",
        ]
        yield event.plain_result("\n".join(lines))

    @filter.command("debug_graph")
    async def debug_graph(self, event: AstrMessageEvent):
        '''
        调试关系图渲染
        '''
        # 直接调用外部函数，将 self (插件实例) 和 event 传进去
        async for result in run_debug_graph(self, event):
            yield result

    # ==================================================================
    # 日群友相关
    # ==================================================================

    def _ensure_today_ri_records(self) -> None:
        today = datetime.now().strftime("%Y-%m-%d")
        if self.ri_records.get("date") != today:
            self.ri_records = {"date": today, "groups": {}}

    def _ensure_today_ri_daily(self) -> None:
        today = datetime.now().strftime("%Y-%m-%d")
        if self.ri_daily.get("date") != today:
            self.ri_daily = {"date": today, "groups": {}}

    def _get_ri_group_records(self, group_id: str) -> list:
        self._ensure_today_ri_records()
        if group_id not in self.ri_records["groups"]:
            self.ri_records["groups"][group_id] = {"records": []}
        return self.ri_records["groups"][group_id]["records"]

    def _has_ri_today(self, group_id: str, user_id: str, mode: str = "random") -> bool:
        """检查该用户今天指定模式的额度是否已用完。mode: 'random' 或 'at'"""
        self._ensure_today_ri_daily()
        user_data = self.ri_daily["groups"].get(group_id, {}).get(user_id, {})
        # 兼容旧格式（True/False）
        if isinstance(user_data, bool):
            return user_data
        return user_data.get(mode, False)

    def _mark_ri_today(self, group_id: str, user_id: str, mode: str = "random") -> None:
        """标记该用户今天指定模式的额度已用完。mode: 'random' 或 'at'"""
        self._ensure_today_ri_daily()
        if group_id not in self.ri_daily["groups"]:
            self.ri_daily["groups"][group_id] = {}
        user_data = self.ri_daily["groups"][group_id].get(user_id, {})
        # 兼容旧格式（True/False）
        if isinstance(user_data, bool):
            user_data = {"random": user_data, "at": user_data}
        user_data[mode] = True
        self.ri_daily["groups"][group_id][user_id] = user_data
        save_json(self.ri_daily_file, self.ri_daily)

    def _get_invite_count(self, group_id: str, user_id: str) -> int:
        """获取该用户今天跟日次数"""
        today = datetime.now().strftime("%Y-%m-%d")
        if self.ri_invite_daily.get("date") != today:
            self.ri_invite_daily = {"date": today, "groups": {}}
        return self.ri_invite_daily["groups"].get(group_id, {}).get(user_id, 0)

    def _increment_invite_count(self, group_id: str, user_id: str) -> int:
        """跟日次数+1，返回当前次数"""
        today = datetime.now().strftime("%Y-%m-%d")
        if self.ri_invite_daily.get("date") != today:
            self.ri_invite_daily = {"date": today, "groups": {}}
        if group_id not in self.ri_invite_daily["groups"]:
            self.ri_invite_daily["groups"][group_id] = {}
        count = self.ri_invite_daily["groups"][group_id].get(user_id, 0) + 1
        self.ri_invite_daily["groups"][group_id][user_id] = count
        save_json(self.ri_invite_daily_file, self.ri_invite_daily)
        return count

    def _ensure_today_ri_target_daily(self) -> None:
        today = datetime.now().strftime("%Y-%m-%d")
        if self.ri_target_daily.get("date") != today:
            self.ri_target_daily = {"date": today, "groups": {}}

    def _get_ri_target_count(self, group_id: str, target_id: str) -> int:
        """获取目标今天被日的次数"""
        self._ensure_today_ri_target_daily()
        return self.ri_target_daily["groups"].get(group_id, {}).get(target_id, 0)

    def _increment_ri_target(self, group_id: str, target_id: str) -> int:
        """目标被日次数+1，返回当前次数"""
        self._ensure_today_ri_target_daily()
        if group_id not in self.ri_target_daily["groups"]:
            self.ri_target_daily["groups"][group_id] = {}
        count = self.ri_target_daily["groups"][group_id].get(target_id, 0) + 1
        self.ri_target_daily["groups"][group_id][target_id] = count
        save_json(self.ri_target_daily_file, self.ri_target_daily)
        return count

    def _clean_ri_stats(self) -> None:
        """清理30天前的日群友记录"""
        now = time.time()
        thirty_days = 30 * 24 * 3600
        new_stats = {}
        for gid, users in self.ri_stats.items():
            new_users = {}
            for uid, ts_list in users.items():
                valid = [ts for ts in ts_list if now - ts < thirty_days]
                if valid:
                    new_users[uid] = valid
            if new_users:
                new_stats[gid] = new_users
        self.ri_stats = new_stats
        save_json(self.ri_stats_file, self.ri_stats)

    @filter.command(CMD_RI)
    async def ri(self, event: AstrMessageEvent):
        async for result in self._cmd_ri(event):
            yield result

    async def _cmd_ri(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return

        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "ri")

        user_id = str(event.get_sender_id())
        bot_id = str(event.get_self_id())

        # 获取群成员列表
        members = []
        current_member_ids: list[str] = []
        try:
            if event.get_platform_name() == "aiocqhttp":
                assert isinstance(event, AiocqhttpMessageEvent)
                members = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id)
                )
                if isinstance(members, dict) and "data" in members and isinstance(members["data"], list):
                    members = members["data"]
                current_member_ids = [str(m.get("user_id")) for m in members]
        except Exception as e:
            logger.error(f"获取群成员列表失败: {e}")

        at_target_id = extract_target_id_from_message(event)
        excluded = {bot_id, user_id, "0"}

        # 概率配置
        ri_prob = float(self.config.get("ri_probability", 80))
        ri_prob = max(0.0, min(100.0, ri_prob))
        ri_at_prob = float(self.config.get("ri_at_probability", 80))
        ri_at_prob = max(0.0, min(100.0, ri_at_prob))
        ri_target_max = int(self.config.get("ri_target_max", 3))

        if at_target_id and at_target_id not in excluded:
            # ===== @指定模式 =====
            # ★ 恋爱保护检查
            target_pl_partner = self._get_pure_love_partner(group_id, at_target_id)
            if target_pl_partner:
                pl_name = f"用户({target_pl_partner})"
                try:
                    if event.get_platform_name() == "aiocqhttp":
                        pl_name = resolve_member_name(members, user_id=target_pl_partner, fallback=pl_name)
                except Exception:
                    pass
                yield event.plain_result(f"该用户已与【{pl_name}】建立恋爱关系💕，无法被日哦~")
                return

            if current_member_ids and at_target_id not in current_member_ids:
                yield event.plain_result("该用户不在本群，无法指定哦~")
                return

            # 检查目标今日被日次数上限
            target_count = self._get_ri_target_count(group_id, at_target_id)
            if target_count >= ri_target_max:
                yield event.plain_result(f"对方今天已经被日了 {ri_target_max} 次，请放过他/她吧~")
                return

            # 概率判定（失败不消耗额度）
            if random.uniform(0, 100) > ri_at_prob:
                fake_pct = random.randint(1, 99)
                yield event.plain_result(
                    f"在 {fake_pct}% 的时候群友跑掉了。\n"
                    "这次不消耗额度，可以再试一次。"
                )
                return

            # 概率成功后，检查发起者@指定模式今日额度
            if self._has_ri_today(group_id, user_id, mode="at"):
                yield event.plain_result("你今天的@指定额度已经用完了，明天再来吧！")
                return

            target_id = at_target_id
            user_name = event.get_sender_name() or f"用户({user_id})"
            target_name = f"用户({target_id})"
            try:
                if event.get_platform_name() == "aiocqhttp":
                    user_name = resolve_member_name(members, user_id=user_id, fallback=user_name)
                    target_name = resolve_member_name(members, user_id=target_id, fallback=target_name)
            except Exception:
                pass

            # 标记发起者@指定额度已用，目标次数+1
            self._mark_ri_today(group_id, user_id, mode="at")
            new_count = self._increment_ri_target(group_id, target_id)
            remaining = ri_target_max - new_count

            # 检查是否触发强娶解锁
            unlock_count = self.config.get("force_marry_unlock_ri_count", 3)
            today_str = datetime.now().strftime("%Y-%m-%d")
            target_lock = self.force_lock.get(group_id, {}).get(target_id, {})
            unlock_msg = ""
            if target_lock.get("date") == today_str and target_lock.get("count", 0) >= self.config.get("force_marry_lock_count", 2):
                # ★ 恋爱保护：恋爱中的人不能通过日群友解锁
                target_pl = self._get_pure_love_partner(group_id, target_id)
                if target_pl:
                    pl_name = f"用户({target_pl})"
                    try:
                        pl_name = resolve_member_name(members, user_id=target_pl, fallback=pl_name)
                    except Exception:
                        pass
                    unlock_msg = f"\n💕 {target_name} 与【{pl_name}】处于恋爱关系中，无法解锁。"
                else:
                    ri_on_target_today = new_count
                    if ri_on_target_today >= unlock_count:
                        # 解锁
                        self.force_lock.setdefault(group_id, {})[target_id] = {"date": today_str, "count": 0}
                        save_json(self.force_lock_file, self.force_lock)
                        unlock_msg = f"\n🔓 {target_name} 的强娶锁已被日群友解锁！"
                    else:
                        unlock_msg = f"\n🔒 {target_name} 今日被日 {ri_on_target_today}/{unlock_count} 次，再日 {unlock_count - ri_on_target_today} 次可解锁强娶保护。"

            # 统计记录
            if group_id not in self.ri_stats:
                self.ri_stats[group_id] = {}
            if user_id not in self.ri_stats[group_id]:
                self.ri_stats[group_id][user_id] = []
            self.ri_stats[group_id][user_id].append(time.time())
            self._clean_ri_stats()
            save_json(self.ri_stats_file, self.ri_stats)

            # 今日关系图记录
            group_ri_records = self._get_ri_group_records(group_id)
            group_ri_records.append({
                "user_id": user_id,
                "user_name": user_name,
                "target_id": target_id,
                "target_name": target_name,
                "timestamp": datetime.now().isoformat(),
                "type": "at",
            })
            save_json(self.ri_records_file, self.ri_records)

            text = (
                f" 日群友成功！🎉\n【{user_name}】今天日了【{target_name}】！\n"
                f"{target_name} 今天还剩 {remaining} 次可以被日\n"
                f"（你的@指定额度已用完，今日无法再@指定日群友）\n"
                f"群友们可以发送 /我也日 @{target_name} 一起来日！"
                f"{unlock_msg}\n"
                f"{self._engagement_hint('ri')}"
            )
            target_avatar = f"https://q4.qlogo.cn/headimg_dl?dst_uin={target_id}&spec=640"

            if self._can_onebot_withdraw(event):
                message_id = await self._send_onebot_message(
                    event,
                    message=[
                        {"type": "at", "data": {"qq": user_id}},
                        {"type": "text", "data": {"text": text}},
                        {"type": "image", "data": {"file": target_avatar}},
                    ],
                )
                if message_id is not None:
                    self._schedule_onebot_delete_msg(event.bot, message_id=message_id)
                return

            chain = [
                Comp.At(qq=user_id),
                Comp.Plain(text),
                Comp.Image.fromURL(target_avatar),
            ]
            yield event.chain_result(chain)

        else:
            # ===== 随机模式 =====
            if self._has_ri_today(group_id, user_id, mode="random"):
                yield event.plain_result("你今天的随机额度已经用完了，明天再来吧！")
                return

            if random.uniform(0, 100) > ri_prob:
                fake_pct = random.randint(1, 99)
                yield event.plain_result(
                    f"在 {fake_pct}% 的时候群友跑掉了。\n"
                    "这次不消耗额度，可以再试一次。"
                )
                return

            active_pool = self.active_users.get(group_id, {})
            if current_member_ids:
                pool = [uid for uid in active_pool.keys() if uid not in excluded and uid in current_member_ids]
            else:
                pool = [uid for uid in active_pool.keys() if uid not in excluded]

            if not pool:
                yield event.plain_result(
                    "群友池为空，没有可以互动的人（需有人在 30 天内发言）。\n"
                    f"{self._engagement_hint('pool_empty')}"
                )
                return

            target_id = random.choice(pool)

            # ★ 恋爱保护：选到恋爱中的人提示跑掉，不消耗额度
            target_pl_random = self._get_pure_love_partner(group_id, target_id)
            if target_pl_random:
                target_name_tmp = f"用户({target_id})"
                try:
                    if event.get_platform_name() == "aiocqhttp":
                        target_name_tmp = resolve_member_name(members, user_id=target_id, fallback=target_name_tmp)
                except Exception:
                    pass
                yield event.plain_result(f"【{target_name_tmp}】正在谈恋爱，跑掉了💕")
                return  # 不消耗额度，直接return

            user_name = event.get_sender_name() or f"用户({user_id})"
            target_name = f"用户({target_id})"
            try:
                if event.get_platform_name() == "aiocqhttp":
                    user_name = resolve_member_name(members, user_id=user_id, fallback=user_name)
                    target_name = resolve_member_name(members, user_id=target_id, fallback=target_name)
            except Exception:
                pass

            # 标记发起者随机额度已用
            self._mark_ri_today(group_id, user_id, mode="random")

            # 统计记录
            if group_id not in self.ri_stats:
                self.ri_stats[group_id] = {}
            if user_id not in self.ri_stats[group_id]:
                self.ri_stats[group_id][user_id] = []
            self.ri_stats[group_id][user_id].append(time.time())
            self._clean_ri_stats()
            save_json(self.ri_stats_file, self.ri_stats)

            # 今日关系图记录
            group_ri_records = self._get_ri_group_records(group_id)
            group_ri_records.append({
                "user_id": user_id, "user_name": user_name,
                "target_id": target_id, "target_name": target_name,
                "timestamp": datetime.now().isoformat(), "type": "random",
            })
            save_json(self.ri_records_file, self.ri_records)

            text = (
                f" 日群友成功！🎉\n【{user_name}】今天日了【{target_name}】！\n"
                f"（你的随机额度已用完，今日无法再随机日群友）\n"
                f"{self._engagement_hint('ri')}"
            )
            target_avatar = f"https://q4.qlogo.cn/headimg_dl?dst_uin={target_id}&spec=640"

            if self._can_onebot_withdraw(event):
                message_id = await self._send_onebot_message(
                    event,
                    message=[
                        {"type": "at", "data": {"qq": user_id}},
                        {"type": "text", "data": {"text": text}},
                        {"type": "image", "data": {"file": target_avatar}},
                    ],
                )
                if message_id is not None:
                    self._schedule_onebot_delete_msg(event.bot, message_id=message_id)
                return

            chain = [
                Comp.At(qq=user_id),
                Comp.Plain(text),
                Comp.Image.fromURL(target_avatar),
            ]
            yield event.chain_result(chain)
    @filter.command("我也日")
    async def wo_ye_ri(self, event: AstrMessageEvent):
        async for result in self._cmd_wo_ye_ri(event):
            yield result

    async def _cmd_wo_ye_ri(self, event: AstrMessageEvent):
        """跟进日群友：/我也日 @目标"""
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return

        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "wo_ye_ri")

        user_id = str(event.get_sender_id())
        bot_id = str(event.get_self_id())

        target_id = extract_target_id_from_message(event)
        if not target_id or target_id == "all":
            yield event.plain_result("请 @ 一个你想日的目标。")
            return
        if target_id == user_id:
            yield event.plain_result("不能日自己！")
            return
        if target_id == bot_id:
            yield event.plain_result("不能日我！")
            return

        # ★ 恋爱保护
        target_pl = self._get_pure_love_partner(group_id, target_id)
        if target_pl:
            pl_name = f"用户({target_pl})"
            try:
                if event.get_platform_name() == "aiocqhttp":
                    assert isinstance(event, AiocqhttpMessageEvent)
                    _m = await event.bot.api.call_action("get_group_member_list", group_id=int(group_id))
                    if isinstance(_m, dict) and "data" in _m: _m = _m["data"]
                    pl_name = resolve_member_name(_m, user_id=target_pl, fallback=pl_name)
            except Exception:
                pass
            yield event.plain_result(f"该用户已与【{pl_name}】建立恋爱关系💕，无法被日哦~")
            return

        # 检查邀请额度（invite模式，每天3次）
        invite_used = self._get_invite_count(group_id, user_id)
        invite_max = int(self.config.get("ri_invite_max", 3))
        if invite_used >= invite_max:
            yield event.plain_result(f"你今天的跟日额度已用完（{invite_max}次），明天再来吧！")
            return

        # 检查目标今日是否还有被日余量
        ri_target_max = int(self.config.get("ri_target_max", 3))
        target_count = self._get_ri_target_count(group_id, target_id)
        if target_count >= ri_target_max:
            yield event.plain_result(f"对方今天已经被日了 {ri_target_max} 次，已经结束了~")
            return

        # 检查目标是否真的被@指定日过（必须存在at记录才能跟进）
        self._ensure_today_ri_records()
        group_ri_records = self.ri_records.get("groups", {}).get(group_id, {}).get("records", [])
        at_records = [r for r in group_ri_records if r.get("target_id") == target_id and r.get("type") == "at"]
        if not at_records:
            yield event.plain_result("这个人今天还没有被@指定日过，无法跟进哦~")
            return

        # 获取名字
        members = []
        user_name = event.get_sender_name() or f"用户({user_id})"
        target_name = f"用户({target_id})"
        try:
            if event.get_platform_name() == "aiocqhttp":
                assert isinstance(event, AiocqhttpMessageEvent)
                members = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id)
                )
                if isinstance(members, dict) and "data" in members and isinstance(members["data"], list):
                    members = members["data"]
                user_name = resolve_member_name(members, user_id=user_id, fallback=user_name)
                target_name = resolve_member_name(members, user_id=target_id, fallback=target_name)
        except Exception:
            pass

        # 消耗跟日额度
        self._increment_invite_count(group_id, user_id)
        new_count = self._increment_ri_target(group_id, target_id)
        remaining = ri_target_max - new_count

        # 统计记录
        if group_id not in self.ri_stats:
            self.ri_stats[group_id] = {}
        if user_id not in self.ri_stats[group_id]:
            self.ri_stats[group_id][user_id] = []
        self.ri_stats[group_id][user_id].append(time.time())
        self._clean_ri_stats()
        save_json(self.ri_stats_file, self.ri_stats)

        # 关系图记录
        group_ri_records = self._get_ri_group_records(group_id)
        group_ri_records.append({
            "user_id": user_id,
            "user_name": user_name,
            "target_id": target_id,
            "target_name": target_name,
            "timestamp": datetime.now().isoformat(),
            "type": "invite",
        })
        save_json(self.ri_records_file, self.ri_records)

        invite_remaining = invite_max - (invite_used + 1)
        if remaining <= 0:
            suffix = f"\n{target_name} 今天已经被日完了，邀请结束！"
        else:
            suffix = f"\n{target_name} 今天还剩 {remaining} 次可以被日"
        text = (
            f" 跟日成功！🔥\n【{user_name}】也日了【{target_name}】！{suffix}\n"
            f"（你今天还剩 {invite_remaining} 次跟日额度）\n"
            f"{self._engagement_hint('ri')}"
        )
        target_avatar = f"https://q4.qlogo.cn/headimg_dl?dst_uin={target_id}&spec=640"

        if self._can_onebot_withdraw(event):
            message_id = await self._send_onebot_message(
                event,
                message=[
                    {"type": "at", "data": {"qq": user_id}},
                    {"type": "text", "data": {"text": text}},
                    {"type": "image", "data": {"file": target_avatar}},
                ],
            )
            if message_id is not None:
                self._schedule_onebot_delete_msg(event.bot, message_id=message_id)
            return

        chain = [
            Comp.At(qq=user_id),
            Comp.Plain(text),
            Comp.Image.fromURL(target_avatar),
        ]
        yield event.chain_result(chain)
        
    @filter.command("日群友排行")  # ← 加这一行
    async def ri_ranking(self, event: AstrMessageEvent):
        async for result in self._cmd_ri_ranking(event):
            yield result

    async def _cmd_ri_ranking(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("私聊看不了榜单哦~")
            return

        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "ri_ranking")
        self._clean_ri_stats()

        group_data = self.ri_stats.get(group_id, {})
        if not group_data:
            yield event.plain_result("本群近30天还没有人日过群友，大家都很文明呢。")
            return

        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                members = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id)
                )
                if isinstance(members, dict) and "data" in members:
                    members = members["data"]
                for m in members:
                    uid = str(m.get("user_id"))
                    user_map[uid] = m.get("card") or m.get("nickname") or uid
        except Exception:
            pass

        logger.info(f"[日排行] 群成员获取完成，共 {len(user_map)} 人")  # ← 加这里

        sorted_list = sorted(
            [{"uid": uid, "name": user_map.get(uid, f"用户({uid})"), "count": len(ts_list)}
             for uid, ts_list in group_data.items()],
            key=lambda x: x["count"], reverse=True
        )[:10]

        current_rank = 1
        for i, user in enumerate(sorted_list):
            if i > 0 and user["count"] < sorted_list[i - 1]["count"]:
                current_rank = i + 1
            user["rank"] = current_rank

        template_path = os.path.join(self.curr_dir, "ri_ranking.html")
        if not os.path.exists(template_path):
            yield event.plain_result("错误：找不到排行模板 ri_ranking.html")
            return

        with open(template_path, "r", encoding="utf-8") as f:
            template_content = f.read()

        rank_width = 400
        dynamic_height = 100 + len(sorted_list) * 60 + 50
        logger.info(f"[日排行] 模板读取完成，开始渲染，高度={dynamic_height}")  # ← 加这里

        try:
            url = await asyncio.wait_for(
                self.html_render(
                    template_content,
                    {"group_id": group_id, "ranking": sorted_list, "title": "💦 日群友月榜 💦"},
                    options={
                        "type": "png", "quality": None, "full_page": False,
                        "clip": {"x": 0, "y": 0, "width": rank_width, "height": dynamic_height},
                        "scale": "device", "device_scale_factor_level": "ultra",
                    },
                ),
                timeout=30.0
            )
            logger.info(f"[日排行] 渲染完成: {url}")  # ← 加这里
            yield event.image_result(url)
        except asyncio.TimeoutError:
            logger.error("渲染日群友排行超时")
        except Exception as e:
            logger.error(f"渲染日群友排行失败: {e}")

    @filter.command(CMD_RI_GRAPH)
    async def ri_graph(self, event: AstrMessageEvent):
        async for result in self._cmd_ri_graph(event):
            yield result

    async def _cmd_ri_graph(self, event: AstrMessageEvent):
        if event.is_private_chat():
            yield event.plain_result("此功能仅在群聊中可用哦~")
            return

        group_id = str(event.get_group_id())
        if not is_allowed_group(group_id, self.config):
            return
        self._track_usage(event, "ri_graph")

        self._ensure_today_ri_records()
        group_ri_records = self.ri_records.get("groups", {}).get(group_id, {}).get("records", [])

        if not group_ri_records:
            yield event.plain_result("今天还没有人日过群友哦~")
            return

        group_name = "未命名群聊"
        user_map = {}
        try:
            if event.get_platform_name() == "aiocqhttp":
                assert isinstance(event, AiocqhttpMessageEvent)
                info = await event.bot.api.call_action("get_group_info", group_id=int(group_id))
                if isinstance(info, dict) and "data" in info:
                    info = info["data"]
                group_name = info.get("group_name", "未命名群聊")

                members = await event.bot.api.call_action(
                    "get_group_member_list", group_id=int(group_id)
                )
                if isinstance(members, dict) and "data" in members:
                    members = members["data"]
                if isinstance(members, list):
                    for m in members:
                        uid = str(m.get("user_id"))
                        user_map[uid] = m.get("card") or m.get("nickname") or uid
        except Exception as e:
            logger.warning(f"获取群信息失败: {e}")

        vis_js_path = os.path.join(self.curr_dir, "vis-network.min.js")
        vis_js_content = ""
        if os.path.exists(vis_js_path):
            with open(vis_js_path, "r", encoding="utf-8") as f:
                vis_js_content = f.read()

        template_path = os.path.join(self.curr_dir, "ri_graph_template.html")
        if not os.path.exists(template_path):
            yield event.plain_result("错误：找不到模板文件 ri_graph_template.html")
            return

        with open(template_path, "r", encoding="utf-8") as f:
            graph_html = f.read()

        unique_nodes = set()
        for r in group_ri_records:
            unique_nodes.add(r["user_id"])
            unique_nodes.add(r["target_id"])
        node_count = len(unique_nodes)
        clip_width = 1920
        # 图例条约50px，header约80px，每个节点按200px估算布局空间，最低1080
        clip_height = max(1080, 130 + node_count * 200)
        iter_count = self.config.get("iterations", 140)

        try:
            url = await self.html_render(
                graph_html,
                {
                    "vis_js_content": vis_js_content,
                    "group_id": group_id,
                    "group_name": group_name,
                    "user_map": user_map,
                    "records": group_ri_records,
                    "iterations": iter_count,
                },
                options={
                    "type": "png", "quality": None, "scale": "device",
                    "clip": {"x": 0, "y": 0, "width": clip_width, "height": clip_height},
                    "full_page": False, "device_scale_factor_level": "ultra",
                },
            )
            yield event.image_result(url)
        except Exception as e:
            logger.error(f"渲染日群友关系图失败: {e}")

    # ==================================================================

    async def terminate(self):
        save_json(self.records_file, self.records)
        save_json(self.active_file, self.active_users)
        save_json(self.forced_file, self.forced_records)
        save_json(self.rbq_stats_file, self.rbq_stats)
        save_json(self.ri_stats_file, self.ri_stats)
        save_json(self.ri_records_file, self.ri_records)
        save_json(self.ri_daily_file, self.ri_daily)
        save_json(self.ri_target_daily_file, self.ri_target_daily)
        save_json(self.ri_invite_daily_file, self.ri_invite_daily)
        save_json(self.force_lock_file, self.force_lock)
        save_json(self.pure_love_file, self.pure_love)
        save_json(self.affinity_file, self.affinity)
        save_json(self.force_daily_file, self.force_daily)
        save_json(self.usage_stats_file, self.usage_stats)
        save_json(self.anime_link_file, self.anime_link_daily)

        # 取消尚未执行的撤回任务，避免插件卸载后仍调用协议端。
        for task in tuple(self._withdraw_tasks):
            task.cancel()
        self._withdraw_tasks.clear()

        global _PLUGIN_INSTANCE
        _PLUGIN_INSTANCE = None


# ==================== 模块级联动入口 ====================
# 供 animewifex 等其他插件 try-import 调用。

_PLUGIN_INSTANCE: "RandomWifePlugin | None" = None


def get_instance() -> "RandomWifePlugin | None":
    return _PLUGIN_INSTANCE

