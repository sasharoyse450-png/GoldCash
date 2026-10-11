import os, json, hmac, hashlib, logging, asyncio, time, math, random
from urllib.parse import parse_qsl
from contextlib import asynccontextmanager
from math import comb
from collections import Counter
from datetime import datetime, timezone, timedelta

import httpx
from fastapi import FastAPI, Header, HTTPException, Depends, Request, WebSocket, WebSocketDisconnect
from fastapi.middleware.cors import CORSMiddleware
from aiogram import Bot, Dispatcher, F, BaseMiddleware
from aiogram.types import (Message, CallbackQuery, InlineKeyboardMarkup,
                           InlineKeyboardButton, WebAppInfo, TelegramObject)
from aiogram.filters import Command, CommandObject
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.context import FSMContext
from supabase import create_client, Client

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("casino")

# ================== ENV ==================
BOT_TOKEN = os.environ["BOT_TOKEN"]
WEBAPP_URL = os.environ["WEBAPP_URL"]
SUPABASE_URL = os.environ["SUPABASE_URL"]
SUPABASE_SERVICE_KEY = os.environ["SUPABASE_SERVICE_KEY"]
XROCKET_API_KEY = os.environ["XROCKET_API_KEY"]
XROCKET_WEBHOOK_SECRET = os.environ["XROCKET_WEBHOOK_SECRET"]
XROCKET_API_BASE = os.environ.get("XROCKET_API_BASE", "https://pay.api.xrocket.exchange")

CHANNEL_ID = os.environ.get("CHANNEL_ID", "")
CHANNEL_URL = os.environ.get("CHANNEL_URL", "")

DAILY_BONUS = float(os.environ.get("DAILY_BONUS", "0"))
BONUS_COOLDOWN_H = int(os.environ.get("BONUS_COOLDOWN_H", "24"))

HOUSE_EDGE = float(os.environ.get("HOUSE_EDGE", "0.04"))
MIN_BET = float(os.environ.get("MIN_BET", "0.1"))
MAX_BET = float(os.environ.get("MAX_BET", "1000"))
MIN_DEPOSIT = float(os.environ.get("MIN_DEPOSIT", "0.1"))
MIN_WITHDRAW = float(os.environ.get("MIN_WITHDRAW", "0.5"))
MAX_DEPOSIT = float(os.environ.get("MAX_DEPOSIT", "100000"))
WITHDRAW_COOLDOWN_MIN = int(os.environ.get("WITHDRAW_COOLDOWN_MIN", "15"))
MAX_WITHDRAW_DAILY = float(os.environ.get("MAX_WITHDRAW_DAILY", "500"))
REFERRAL_SHARE = float(os.environ.get("REFERRAL_SHARE", "0.05"))
WAGER_RESET_THRESHOLD = float(os.environ.get("WAGER_RESET_THRESHOLD", "0.1"))
ANTIFRAUD_ENABLED = os.environ.get("ANTIFRAUD_ENABLED", "1") == "1"
AUTO_FLAG_SCORE = int(os.environ.get("AUTO_FLAG_SCORE", "50"))

ADMIN_IDS = set(int(x) for x in os.environ.get("ADMIN_IDS", "").split(",") if x.strip().isdigit())

DICE_PAYOUT = round(6 * (1 - HOUSE_EDGE), 4)
ROUL_RB_PAYOUT = round(2 * (1 - HOUSE_EDGE), 4)
ROUL_DOZEN_PAYOUT = round(3 * (1 - HOUSE_EDGE), 4)
ROUL_NUM_PAYOUT = round(36 * (1 - HOUSE_EDGE), 4)

RATE_LIMITS = {"bet": (5, 10), "withdraw": (1, 30), "deposit": (1, 5)}
SUPPORTED_CURRENCIES = ["USDT", "TON", "BTC", "ETH", "TRX"]
CRASH_BETTING_SEC = 10
CRASH_COOLDOWN_SEC = 4
MAINTENANCE = False
START_TIME = time.time()

GAMES_ENABLED = {
    "crash": True, "mines": True, "roulette": True, "dice": True,
    "plinko": True, "blackjack": True, "tower": True,
    "keno": True, "hilo": True, "scratch": True,
    "duel": True,
}

def ensure_game_enabled(game: str):
    if not GAMES_ENABLED.get(game, True):
        raise HTTPException(503, f"игра {game} временно отключена")

# ================== Rakeback claim ==================
RAKEBACK_CLAIM_COOLDOWN_MIN = 10
RAKEBACK_MIN_CLAIM = 0.01

# ================== XP / Levels ==================
MAX_LEVEL = 50
LEVEL_REWARDS = {
    5: 0.5, 10: 1.0, 15: 2.0, 20: 5.0, 25: 10.0,
    30: 20.0, 40: 50.0, 50: 150.0,
}

def xp_for_level(level: int) -> float:
    if level <= 1: return 0
    return round(30 * (level - 1) * level, 2)

def level_from_xp(xp: float) -> int:
    xp = float(xp or 0)
    level = 1
    while level < MAX_LEVEL and xp >= xp_for_level(level + 1):
        level += 1
    return level

def xp_info(p: dict) -> dict:
    xp = float(p.get("xp") or 0)
    level = int(p.get("level") or level_from_xp(xp))
    cur = xp_for_level(level)
    nxt = xp_for_level(level + 1) if level < MAX_LEVEL else cur
    progress = 0.0
    if nxt > cur:
        progress = (xp - cur) / (nxt - cur)
    return {
        "level": level, "xp": round(xp, 2), "max_level": MAX_LEVEL,
        "xp_current": round(cur, 2), "xp_next": round(nxt, 2),
        "xp_to_next": round(max(0.0, nxt - xp), 2),
        "progress": round(max(0.0, min(1.0, progress)) * 100, 1),
        "next_reward_level": next((l for l in sorted(LEVEL_REWARDS) if l > level), None),
        "next_reward_amount": next((LEVEL_REWARDS[l] for l in sorted(LEVEL_REWARDS) if l > level), None),
    }

# ================== VIP TIERS ==================
VIP_TIERS = [
    {"id": "bronze",   "name": "🥉 Бронза",  "wagered": 0,     "rakeback": 0.010, "max_bet_mult": 1.0},
    {"id": "silver",   "name": "🥈 Серебро", "wagered": 100,   "rakeback": 0.020, "max_bet_mult": 2.0},
    {"id": "gold",     "name": "🥇 Золото",  "wagered": 500,   "rakeback": 0.030, "max_bet_mult": 3.0},
    {"id": "platinum", "name": "💎 Платина", "wagered": 2000,  "rakeback": 0.050, "max_bet_mult": 5.0},
    {"id": "diamond",  "name": "💠 Даймонд", "wagered": 10000, "rakeback": 0.070, "max_bet_mult": 10.0},
]

def compute_vip_tier(wagered: float) -> dict:
    tier = VIP_TIERS[0]
    for t in VIP_TIERS:
        if wagered >= t["wagered"]: tier = t
    return tier

def vip_info(p: dict) -> dict:
    wagered = float(p.get("total_wagered") or 0)
    cur = compute_vip_tier(wagered)
    nxt = None
    for t in VIP_TIERS:
        if t["wagered"] > wagered:
            nxt = t; break
    can_claim = True; next_claim_in = 0
    last = p.get("last_rakeback_at")
    if last:
        try:
            dt = datetime.fromisoformat(str(last).replace("Z", "+00:00"))
            left = RAKEBACK_CLAIM_COOLDOWN_MIN * 60 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0:
                can_claim = False; next_claim_in = int(left)
        except Exception: pass
    return {
        "tier": cur["id"], "tier_name": cur["name"],
        "rakeback": cur["rakeback"], "max_bet_mult": cur["max_bet_mult"],
        "total_wagered": round(wagered, 2),
        "rakeback_earned": round(float(p.get("rakeback_earned") or 0), 2),
        "rakeback_pending": round(float(p.get("rakeback_pending") or 0), 8),
        "rakeback_can_claim": can_claim,
        "rakeback_next_in": next_claim_in,
        "rakeback_cooldown_min": RAKEBACK_CLAIM_COOLDOWN_MIN,
        "rakeback_min": RAKEBACK_MIN_CLAIM,
        "next_tier": nxt["id"] if nxt else None,
        "next_tier_name": nxt["name"] if nxt else None,
        "next_tier_at": nxt["wagered"] if nxt else 0,
        "next_required": nxt["wagered"] if nxt else 0,
    }

async def update_vip_tier(uid):
    try:
        r = await sb(supabase.table("profiles").select("total_wagered, vip_tier").eq("id", uid))
        if not r.data: return
        wagered = float(r.data[0].get("total_wagered") or 0)
        new_tier = compute_vip_tier(wagered)["id"]
        if r.data[0].get("vip_tier") != new_tier:
            await sb(supabase.table("profiles").update({"vip_tier": new_tier}).eq("id", uid))
    except Exception: log.exception("update_vip_tier failed")

async def add_wager(uid, amount):
    try:
        amount = float(amount)
        if amount <= 0: return
        r = await sb(supabase.table("profiles").select(
            "total_wagered, rakeback_pending, xp, level").eq("id", uid))
        if not r.data: return
        row = r.data[0]
        new_wagered = round(float(row.get("total_wagered") or 0) + amount, 8)
        tier = compute_vip_tier(new_wagered)
        rakeback_add = round(amount * tier["rakeback"], 8)
        new_rakeback = round(float(row.get("rakeback_pending") or 0) + rakeback_add, 8)
        old_xp = float(row.get("xp") or 0)
        new_xp = round(old_xp + amount, 2)
        old_level = int(row.get("level") or level_from_xp(old_xp))
        new_level = level_from_xp(new_xp)
        upd = {"total_wagered": new_wagered, "rakeback_pending": new_rakeback, "xp": new_xp}
        if new_level > old_level: upd["level"] = new_level
        await sb(supabase.table("profiles").update(upd).eq("id", uid))
        if new_level > old_level:
            for lvl in range(old_level + 1, new_level + 1):
                if lvl in LEVEL_REWARDS:
                    reward = float(LEVEL_REWARDS[lvl])
                    await sb_rpc("change_balance", {"p_user_id": uid, "p_delta": reward})
                    await sb(supabase.table("transactions").insert({
                        "user_id": uid, "type": "bonus", "amount": reward,
                        "currency": "USDT", "status": "completed",
                        "meta": {"source": "level_up", "level": lvl}}))
                    try:
                        prof = (await sb(supabase.table("profiles").select("telegram_id").eq("id", uid))).data
                        if prof:
                            await bot.send_message(prof[0]["telegram_id"],
                                f"🎉 <b>Уровень {lvl}!</b>\n\nНаграда: <b>+{reward:.2f} ₮</b>",
                                parse_mode="HTML")
                    except Exception: pass
        asyncio.create_task(update_vip_tier(uid))
    except Exception: log.exception("add_wager failed")

# ================== DUEL (против бота) ==================
DUEL_BETS    = [0.5, 1, 5, 10, 25, 50]
DUEL_TARGETS = [1, 2, 3]
DUEL_PAYOUT  = round(2 * (1 - HOUSE_EDGE), 4)

DICE_FACES = {1:"⚀",2:"⚁",3:"⚂",4:"⚃",5:"⚄",6:"⚅"}

_duel_last_cfg: dict[int, dict] = {}

def _count_word(n: int) -> str:
    if n == 1: return "куб"
    if n in (2, 3, 4): return "куба"
    return "кубов"

def _faces(vals):
    return " ".join(DICE_FACES.get(v, "🎲") for v in vals)

def _fmt_name(user_dump: dict) -> str:
    if not user_dump: return "Игрок"
    name = (user_dump.get("first_name") or "").strip()
    uname = user_dump.get("username")
    if not name: name = uname or "Игрок"
    if uname: return f"{name} @{uname}"
    return name

def _score_block(ps: int, bs: int, player_name: str) -> str:
    return (f"🎲 <b>Score</b>\n"
            f"{player_name}: {ps} очков\n"
            f"🤖 {BOT_NAME}: {bs} очков")

def duel_home_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎲 1 куб",   callback_data="duel:cfg:1:0"),
         InlineKeyboardButton(text="🎲 2 куба",  callback_data="duel:cfg:2:0"),
         InlineKeyboardButton(text="🎲 3 куба",  callback_data="duel:cfg:3:0")],
        [InlineKeyboardButton(text="🌀 Крэзи 1", callback_data="duel:cfg:1:1"),
         InlineKeyboardButton(text="🌀 Крэзи 2", callback_data="duel:cfg:2:1"),
         InlineKeyboardButton(text="🌀 Крэзи 3", callback_data="duel:cfg:3:1")],
        [InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])

def duel_target_kb(count: int, crazy: int):
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="До 1 очка",  callback_data=f"duel:tgt:{count}:{crazy}:1"),
         InlineKeyboardButton(text="До 2 очков", callback_data=f"duel:tgt:{count}:{crazy}:2"),
         InlineKeyboardButton(text="До 3 очков", callback_data=f"duel:tgt:{count}:{crazy}:3")],
        [InlineKeyboardButton(text="⬅️ Назад", callback_data="duel:home")]])

def duel_bet_kb(count: int, crazy: int, target: int):
    rows = []
    for i in range(0, len(DUEL_BETS), 3):
        rows.append([InlineKeyboardButton(
            text=f"{b} ₮",
            callback_data=f"duel:bet:{count}:{crazy}:{target}:{b}"
        ) for b in DUEL_BETS[i:i+3]])
    rows.append([InlineKeyboardButton(text="✏️ Своя сумма", callback_data=f"duel:betcustom:{count}:{crazy}:{target}")])
    rows.append([InlineKeyboardButton(text="⬅️ Назад", callback_data=f"duel:cfg:{count}:{crazy}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def duel_roll_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎲 Кинуть кости", callback_data="duel:roll")],
        [InlineKeyboardButton(text="🏳️ Сдаться",      callback_data="duel:surrender")]])

def duel_again_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔁 Ещё раз",   callback_data="duel:again")],
        [InlineKeyboardButton(text="🎲 Настройки", callback_data="duel:home"),
         InlineKeyboardButton(text="🏠 Меню",      callback_data="menu:main")]])

class DuelState(StatesGroup):
    custom_bet = State()

# ================== KENO ==================
KENO_PAYOUTS = {
    1:  {0: 0, 1: 3.4},
    2:  {0: 0, 1: 0, 2: 12},
    3:  {0: 0, 1: 0, 2: 2.2, 3: 40},
    4:  {0: 0, 1: 0, 2: 1.4, 3: 6, 4: 100},
    5:  {0: 0, 1: 0, 2: 0.8, 3: 3, 4: 20, 5: 300},
    6:  {0: 0, 1: 0, 2: 0.5, 3: 1.5, 4: 8, 5: 60, 6: 800},
    7:  {0: 0, 1: 0, 2: 0.4, 3: 1.2, 4: 5, 5: 25, 6: 200, 7: 2000},
    8:  {0: 0, 1: 0, 2: 0.3, 3: 1, 4: 3, 5: 15, 6: 80, 7: 500, 8: 5000},
    9:  {0: 0, 1: 0, 2: 0.3, 3: 0.9, 4: 3, 5: 10, 6: 50, 7: 200, 8: 1000, 9: 10000},
    10: {0: 0, 1: 0, 2: 0.3, 3: 0.8, 4: 2, 5: 6, 6: 25, 7: 100, 8: 500, 9: 2500, 10: 25000},
}

# ================== HI-LO ==================
HILO_TOTAL = 13
HILO_NAMES = {1:"A",2:"2",3:"3",4:"4",5:"5",6:"6",7:"7",8:"8",9:"9",10:"10",11:"J",12:"Q",13:"K"}
HILO_EDGE = 0.01

def hilo_prob_mult(current, direction):
    current = int(current)
    favorable = (HILO_TOTAL - current + 1) if direction == "higher" else current
    p = favorable / HILO_TOTAL
    return round(p, 4), round((1 - HILO_EDGE) / p, 2)

def hilo_draw_card(ss, cs, nonce, step):
    return int(pf_rand(ss, cs, nonce * 100 + step) * HILO_TOTAL) + 1

# ================== SCRATCH ==================
SCRATCH_SYMBOLS = ["0x", "0.5x", "1x", "2x", "2.5x", "4x", "5x", "7.5x", "10x", "14x"]
SCRATCH_VALUES  = [0.0, 0.5, 1.0, 2.0, 2.5, 4.0, 5.0, 7.5, 10.0, 14.0]

SCRATCH_TIERS = [
    {"id":"mat",      "name":"Мать",       "bet":0.20,  "color":"#10b981", "max":14,
     "weights": [83, 32, 30, 18, 8,   5,   3.5, 2,   0.9, 0.6]},
    {"id":"lazur",    "name":"Лазурь",     "bet":0.50,  "color":"#3b82f6", "max":14,
     "weights": [77, 30, 28, 16, 7,   4.5, 3,   1.8, 1,   0.7]},
    {"id":"violet",   "name":"Виолет",     "bet":1.00,  "color":"#a855f7", "max":14,
     "weights": [79, 28, 26, 15, 6.5, 4,   3,   2,   1.2, 0.8]},
    {"id":"sunset",   "name":"Закат",      "bet":2.00,  "color":"#f97316", "max":14,
     "weights": [83, 26, 24, 14, 6,   4,   3,   2,   1.5, 1]},
    {"id":"gold",     "name":"Золото",     "bet":5.00,  "color":"#fbbf24", "max":14,
     "weights": [92, 24, 22, 13, 6,   4,   3,   2.5, 1.8, 1.2]},
    {"id":"obsidian", "name":"Обисидиан",  "bet":10.00, "color":"#e5e7eb", "max":14,
     "weights": [98, 22, 20, 12, 6,   4,   3,   2.5, 2,   1.5]},
]
SCRATCH_TIER_MAP = {t["id"]: t for t in SCRATCH_TIERS}

def _weighted_pick(weights, r):
    total = sum(weights)
    if total <= 0: return 0
    target = r * total; cum = 0.0
    for i, w in enumerate(weights):
        cum += w
        if target < cum: return i
    return len(weights) - 1

def scratch_draw(ss, cs, nonce, tier):
    idx = _weighted_pick(tier["weights"], pf_rand(ss, cs, nonce * 13 + 1))
    win_sym = SCRATCH_SYMBOLS[idx]; win_val = SCRATCH_VALUES[idx]
    positions = list(range(9))
    st = int.from_bytes(hashlib.sha256(f"{ss}:{cs}:{nonce}:pos".encode()).digest()[:8], "big")
    for i in range(8, 0, -1):
        st = (st * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
        j = st % (i + 1)
        positions[i], positions[j] = positions[j], positions[i]
    win_pos = set(positions[:3])
    others_idx = [j for j in range(len(SCRATCH_SYMBOLS)) if j != idx]
    cells = [None] * 9
    for i in range(9):
        if i in win_pos: cells[i] = win_sym
        else:
            r = pf_rand(ss, cs, nonce * 100 + i)
            cells[i] = SCRATCH_SYMBOLS[others_idx[int(r * len(others_idx))]]
    return cells, win_val

supabase: Client = create_client(SUPABASE_URL, SUPABASE_SERVICE_KEY)
BOT_USERNAME: str | None = None
BOT_NAME: str = "Raika"

crash_state = {"round_id": None, "status": "idle", "server_seed": None,
               "crash_point": None, "started_at": None, "betting_ends_at": None, "auto_task": None}

class AmountInput(StatesGroup):
    deposit = State(); withdraw = State()

class AdminInput(StatesGroup):
    broadcast = State()

def is_admin(user_id: int) -> bool:
    return user_id in ADMIN_IDS

async def sb(builder):
    return await asyncio.to_thread(builder.execute)

async def sb_rpc(name, params):
    return await asyncio.to_thread(lambda: supabase.rpc(name, params).execute())

async def check_rate_limit(uid: str, action: str):
    max_calls, window = RATE_LIMITS.get(action, (10, 60))
    since = (datetime.now(timezone.utc) - timedelta(seconds=window)).isoformat()
    r = await sb(supabase.table("action_log").select("id")
                 .eq("user_id", uid).eq("action", action).gte("created_at", since))
    if len(r.data or []) >= max_calls:
        raise HTTPException(429, f"слишком часто. Подожди {window} сек.")
    await sb(supabase.table("action_log").insert({"user_id": uid, "action": action}))

async def ensure_not_banned(profile):
    if profile.get("is_banned"):
        raise HTTPException(403, f"аккаунт заблокирован: {profile.get('ban_reason') or 'нарушение правил'}")

# ================== ANTIFRAUD ==================
def get_client_ip(request: Request) -> str:
    for h in ("x-forwarded-for", "x-real-ip", "cf-connecting-ip"):
        v = request.headers.get(h)
        if v: return v.split(",")[0].strip()
    return request.client.host if request.client else "0.0.0.0"

async def log_antifraud(uid, event: str, details: dict = None, ip=None, fingerprint=None):
    try:
        await sb(supabase.table("antifraud_log").insert({
            "user_id": uid, "event": event,
            "details": details or {}, "ip": ip, "fingerprint": fingerprint}))
    except Exception: log.exception("log_antifraud failed")

async def antifraud_check(tg_user, ip: str, fingerprint: str):
    if not ANTIFRAUD_ENABLED: return
    try:
        uid = int(tg_user["id"])
        r = await sb(supabase.table("profiles").select("id, device_fingerprint, last_ip, signup_ip, risk_score")
                     .eq("telegram_id", uid))
        if not r.data: return
        me = r.data[0]; my_id = me["id"]
        updates = {"last_ip": ip}
        if not me.get("device_fingerprint") and fingerprint: updates["device_fingerprint"] = fingerprint
        if not me.get("signup_ip"): updates["signup_ip"] = ip
        risk_delta = 0; flag_reason = None
        if fingerprint:
            others = await sb(supabase.table("profiles").select("id, telegram_id")
                              .eq("device_fingerprint", fingerprint).neq("id", my_id))
            if others.data:
                risk_delta += 30 * len(others.data)
                flag_reason = f"device shared with {len(others.data)} accounts"
                for o in others.data:
                    try:
                        await sb(supabase.table("alt_accounts").insert({
                            "user_id": my_id, "linked_user_id": o["id"],
                            "reason": "same_device", "confidence": 80}))
                    except Exception: pass
                await log_antifraud(my_id, "multi_device", {"count": len(others.data)}, ip, fingerprint)
        if ip:
            others = await sb(supabase.table("profiles").select("id, telegram_id")
                              .eq("last_ip", ip).neq("id", my_id))
            if others.data and len(others.data) >= 3:
                risk_delta += 20
                if not flag_reason: flag_reason = f"IP shared with {len(others.data)} accounts"
                await log_antifraud(my_id, "multi_ip", {"count": len(others.data)}, ip, fingerprint)
        if risk_delta > 0:
            new_score = int(me.get("risk_score") or 0) + risk_delta
            updates["risk_score"] = new_score
            if new_score >= AUTO_FLAG_SCORE:
                updates["auto_flagged"] = True
                updates["flag_reason"] = flag_reason or "auto-flagged"
            await sb(supabase.table("profiles").update(updates).eq("id", my_id))
        else:
            await sb(supabase.table("profiles").update(updates).eq("id", my_id))
    except Exception: log.exception("antifraud_check failed")

# ================== SUBSCRIPTION ==================
SUB_STATUSES = ("member", "administrator", "creator")
_sub_cache: dict[int, tuple[bool, float]] = {}
SUB_CACHE_TTL = 30

async def is_subscribed(user_id: int, skip_cache: bool = False) -> bool:
    if is_admin(user_id): return True
    if not CHANNEL_ID: return True
    now = time.time()
    if not skip_cache:
        cached = _sub_cache.get(user_id)
        if cached and (now - cached[1]) < SUB_CACHE_TTL: return cached[0]
    for attempt in range(2):
        try:
            member = await bot.get_chat_member(chat_id=CHANNEL_ID, user_id=user_id)
            status = member.status
            if status == "restricted": result = bool(getattr(member, "is_member", False))
            elif status == "left": result = False
            else: result = status in SUB_STATUSES
            _sub_cache[user_id] = (result, now)
            return result
        except Exception as e:
            log.warning("is_subscribed attempt %s: %s", attempt + 1, e)
            if attempt == 0: await asyncio.sleep(0.4); continue
            return False
    return False

def sub_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📢 Подписаться", url=CHANNEL_URL)],
        [InlineKeyboardButton(text="✅ Я подписался", callback_data="check_sub")]])

async def send_sub_prompt(message: Message):
    if not CHANNEL_URL:
        await message.answer("⚠️ Канал не настроен. Обратись к администратору.")
        return
    ch_name = CHANNEL_URL.replace("https://t.me/", "@").replace("http://t.me/", "@")
    await message.answer(
        "🔒 <b>Доступ только для подписчиков</b>\n\n"
        f"Подпишись на канал:\n👉 {ch_name}\n\n"
        "После подписки нажми <b>«✅ Я подписался»</b>.",
        parse_mode="HTML", reply_markup=sub_kb(), disable_web_page_preview=True)

class SubscriptionMiddleware(BaseMiddleware):
    async def __call__(self, handler, event: TelegramObject, data: dict):
        user = data.get("event_from_user")
        if user is None: return await handler(event, data)
        try:
            if hasattr(event, "text") and event.text and event.text.startswith("/start"):
                return await handler(event, data)
            if hasattr(event, "data") and event.data == "check_sub":
                return await handler(event, data)
        except Exception: pass
        if not await is_subscribed(user.id):
            if isinstance(event, CallbackQuery):
                try: await event.answer("🔒 Сначала подпишись на канал", show_alert=True)
                except: pass
                try: await send_sub_prompt(event.message)
                except: pass
                return
            try: await send_sub_prompt(event)
            except: pass
            return
        return await handler(event, data)

# ================== XROCKET ==================
async def xrocket_request(method: str, path: str, body: dict | None = None) -> dict:
    url = f"{XROCKET_API_BASE}{path}"
    headers = {"Authorization": f"Bearer {XROCKET_API_KEY}", "Content-Type": "application/json"}
    async with httpx.AsyncClient(timeout=30) as http:
        r = await http.request(method, url, json=body or {}, headers=headers)
        try: data = r.json()
        except Exception: data = {"raw": r.text}
        log.info("xRocket %s %s -> %s", method, path, r.status_code)
        if r.status_code not in (200, 201):
            msg = (data.get("detail") or data.get("message") or data.get("error") or f"HTTP {r.status_code}")
            if isinstance(msg, dict): msg = json.dumps(msg, ensure_ascii=False)
            raise Exception(msg)
        return data

async def xrocket_create_invoice(amount, description, client_id, currency="USDT"):
    cur = currency.upper(); amt = str(float(amount))
    payload = {"currency": cur, "amount": amt, "priceCurrency": cur,
               "priceAmount": amt, "description": description, "clientInvoiceId": client_id}
    data = await xrocket_request("POST", "/api/v1/invoices", payload)
    links = data.get("links") or {}
    link = (links.get("telegramBotLink") or links.get("telegramMiniAppLink") or links.get("webLink"))
    if not link: raise Exception(f"xRocket не вернул ссылку: {data}")
    return {"id": data.get("id"), "link": link, "raw": data}

async def xrocket_create_payout(user_id, amount, comment, client_id, currency="USDT"):
    payload = {"clientPayoutId": client_id, "userId": int(user_id),
               "currency": currency.upper(), "amount": float(amount),
               "description": comment or "Withdraw"}
    data = await xrocket_request("POST", "/api/v1/payouts", payload)
    return {"id": data.get("payoutId") or data.get("id"),
            "status": data.get("status") or "pending", "raw": data}

async def xrocket_get_invoice(invoice_id: str):
    try: return await xrocket_request("GET", f"/api/v1/invoices/{invoice_id}")
    except Exception as e:
        log.warning("xrocket_get_invoice %s failed: %s", invoice_id, e); return None

async def check_pending_deposits(user_id: str):
    try:
        r = await sb(supabase.table("transactions").select("*")
                     .eq("user_id", user_id).eq("type", "deposit")
                     .eq("status", "pending").order("created_at", desc=True).limit(10))
        for tx in r.data or []:
            inv_id = (tx.get("meta") or {}).get("invoice_id")
            if not inv_id: continue
            data = await xrocket_get_invoice(inv_id)
            if not data: continue
            if (data.get("status") or "").lower() in ("paid", "completed", "success"):
                claim = await sb(supabase.table("transactions")
                                 .update({"status": "processing"})
                                 .eq("id", tx["id"]).eq("status", "pending"))
                if not claim.data: continue
                await sb_rpc("change_balance",
                             {"p_user_id": tx["user_id"], "p_delta": float(tx["amount"])})
                await sb(supabase.table("transactions").update({
                    "status": "completed",
                    "meta": {**(tx.get("meta") or {}),
                             "credited_at": datetime.now(timezone.utc).isoformat(),
                             "source": "poll"},
                }).eq("id", tx["id"]))
    except Exception: log.exception("check_pending_deposits failed")

# ================== MATH / PF ==================
def pf_rand(ss, cs, n):
    h = hmac.new(ss.encode(), f"{cs}:{n}".encode(), hashlib.sha256).hexdigest()
    return int(h[:13], 16) / float(0xFFFFFFFFFFFFF)

def crash_point(ss, cs, n):
    r = pf_rand(ss, cs, n)
    if r < HOUSE_EDGE: return 1.00
    return round(min(1000.0, (1 - HOUSE_EDGE) / (1 - r)), 2)

def crash_mult(elapsed): return round(max(1.0, 1.07 ** elapsed), 2)
def roulette_number(ss, cs, n): return int(pf_rand(ss, cs, n) * 37)

def mine_positions(ss, cs, n, mines):
    state = int.from_bytes(hashlib.sha256(f"{ss}:{cs}:{n}".encode()).digest()[:8], "big")
    pos = list(range(25))
    for i in range(24, 0, -1):
        state = (state * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
        j = state % (i + 1)
        pos[i], pos[j] = pos[j], pos[i]
    return pos[:mines]

def mines_mult(mines, revealed):
    if revealed <= 0: return 1.0
    safe = 25 - mines
    if revealed > safe: return 0.0
    return round((1 - HOUSE_EDGE) / (comb(safe, revealed) / comb(25, revealed)), 4)

def dice_result(ss, cs, n): return int(pf_rand(ss, cs, n) * 6) + 1

def plinko_path(ss, cs, n, rows):
    idx = 0; path = []
    for i in range(rows):
        step = 1 if pf_rand(ss, cs, n * 1000 + i) >= 0.5 else 0
        path.append(step); idx += step
    return idx, path

def tower_step_positions(ss, cs, n, levels=6):
    return [int(pf_rand(ss, cs, n * 100 + i) * 3) for i in range(levels)]

def tower_mult(level):
    if level <= 0: return 1.0
    return round((1 - HOUSE_EDGE) * (3/2) ** level, 4)

def bj_deck(ss, cs, n):
    deck = [f"{s}{r}" for s in "SHDC" for r in "23456789TJQKA"]
    state = int.from_bytes(hashlib.sha256(f"{ss}:{cs}:{n}".encode()).digest()[:8], "big")
    for i in range(51, 0, -1):
        state = (state * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
        j = state % (i + 1)
        deck[i], deck[j] = deck[j], deck[i]
    return deck

def bj_value(cards):
    total = 0; aces = 0
    for c in cards:
        r = c[1]
        if r in "TJQK": total += 10
        elif r == "A": aces += 1; total += 11
        else: total += int(r)
    while total > 21 and aces > 0: total -= 10; aces -= 1
    return total

def keno_draw(ss, cs, n, count=20):
    state = int.from_bytes(hashlib.sha256(f"{ss}:{cs}:{n}:keno".encode()).digest()[:8], "big")
    pool = list(range(1, 81))
    for i in range(len(pool) - 1, 0, -1):
        state = (state * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
        j = state % (i + 1)
        pool[i], pool[j] = pool[j], pool[i]
    return sorted(pool[:count])

# ================== AUTH ==================
def validate_init_data(init_data, bot_token):
    try:
        parsed = dict(parse_qsl(init_data, keep_blank_values=True))
        rh = parsed.pop("hash", None)
        if not rh: return None
        ad = parsed.get("auth_date")
        if ad:
            try:
                if time.time() - int(ad) > 7200: return None
            except (ValueError, TypeError): pass
        dcs = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
        sk = hmac.new(b"WebAppData", bot_token.encode(), hashlib.sha256).digest()
        calc = hmac.new(sk, dcs.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, rh): return None
        u = json.loads(parsed.get("user", "{}"))
        return u if u.get("id") else None
    except Exception:
        log.exception("validate_init_data failed"); return None

async def get_current_user(
    request: Request,
    x_telegram_init_data: str = Header(None, alias="X-Telegram-Init-Data"),
    x_device_id: str = Header(None, alias="X-Device-Id"),
):
    if not x_telegram_init_data: raise HTTPException(401, "missing init data")
    u = validate_init_data(x_telegram_init_data, BOT_TOKEN)
    if not u: raise HTTPException(401, "invalid init data")
    if not await is_subscribed(int(u["id"])):
        raise HTTPException(403, "subscription_required")
    if ANTIFRAUD_ENABLED:
        asyncio.create_task(antifraud_check(u, get_client_ip(request), x_device_id or ""))
    return u

# ================== DB ==================
async def notify_admin_new_user(tg_user, profile):
    try:
        name = tg_user.get("first_name") or "без имени"
        username = f"@{tg_user['username']}" if tg_user.get("username") else "—"
        text = (f"🆕 <b>Новый пользователь</b>\n"
                f"👤 <b>{name}</b>\n🔗 {username}\n"
                f"🆔 <code>{tg_user['id']}</code>\n"
                f"💰 Баланс: {float(profile.get('balance') or 0):.2f} ₮")
        for aid in ADMIN_IDS:
            try: await bot.send_message(aid, text, parse_mode="HTML")
            except Exception: pass
    except Exception: log.exception("notify_admin_new_user failed")

async def get_or_create_profile(tg_user):
    tg_id = int(tg_user["id"])
    r = await sb(supabase.table("profiles").select("*").eq("telegram_id", tg_id))
    if r.data: return r.data[0]
    ins = await sb(supabase.table("profiles").insert({
        "telegram_id": tg_id, "username": tg_user.get("username"),
        "first_name": tg_user.get("first_name"), "preferred_currency": "USDT"}))
    new_profile = ins.data[0]
    asyncio.create_task(notify_admin_new_user(tg_user, new_profile))
    return new_profile

async def get_profile_by_tg(tg_id: int):
    r = await sb(supabase.table("profiles").select("*").eq("telegram_id", tg_id))
    return r.data[0] if r.data else None

async def get_active_round(uid):
    r = await sb(supabase.table("active_rounds").select("*").eq("user_id", uid))
    return r.data[0] if r.data else None

async def clear_active_round(uid):
    await sb(supabase.table("active_rounds").delete().eq("user_id", uid))

async def log_round(uid, game, bet, result, profit, ss, nonce):
    try:
        await sb(supabase.table("game_rounds").insert({
            "user_id": uid, "game_type": game, "bet_amount": bet,
            "result": result, "profit": profit, "server_seed": ss, "nonce": nonce}))
    except Exception: log.exception("log_round failed")

async def get_user_stats(uid):
    tx = (await sb(supabase.table("transactions").select("type, amount, status").eq("user_id", uid))).data or []
    rounds = (await sb(supabase.table("game_rounds").select("bet_amount, profit").eq("user_id", uid))).data or []
    dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    bets = sum(float(r["bet_amount"]) for r in rounds)
    profits = sum(float(r["profit"]) for r in rounds)
    wins = sum((float(r["profit"]) + float(r["bet_amount"])) for r in rounds if float(r["profit"]) > 0)
    return {"games": len(rounds), "deposits": round(dep, 2), "withdrawals": round(wd, 2),
            "bets": round(bets, 2), "wins": round(wins, 2), "net": round(profits, 2)}

async def credit_referrer_on_loss(uid, bet_amount):
    try:
        r = await sb(supabase.table("profiles").select("referrer_id").eq("id", uid))
        if not r.data or not r.data[0].get("referrer_id"): return
        ref_id = r.data[0]["referrer_id"]
        reward = round(bet_amount * REFERRAL_SHARE, 8)
        if reward <= 0: return
        await sb_rpc("change_balance", {"p_user_id": ref_id, "p_delta": reward})
        cur = await sb(supabase.table("profiles").select("ref_earnings").eq("id", ref_id))
        cur_earn = float(cur.data[0]["ref_earnings"] or 0) if cur.data else 0
        await sb(supabase.table("profiles").update({"ref_earnings": round(cur_earn + reward, 8)}).eq("id", ref_id))
        await sb(supabase.table("transactions").insert({
            "user_id": ref_id, "type": "ref_reward", "amount": reward,
            "currency": "USDT", "status": "completed",
            "meta": {"from_user": uid, "bet": bet_amount}}))
    except Exception: log.exception("credit_referrer_on_loss failed")

def referral_info_sync(profile):
    ref_link = f"https://t.me/{BOT_USERNAME}?start=ref_{profile['telegram_id']}" if BOT_USERNAME else ""
    return {"link": ref_link, "share": REFERRAL_SHARE}

# ================== WAGER ==================
async def apply_wager_progress(uid, bet: float):
    try:
        bet = float(bet)
        if bet <= 0: return
        r = await sb(supabase.table("profiles").select(
            "wager_required, wager_progress, bonus_active").eq("id", uid))
        if not r.data: return
        row = r.data[0]
        if not row.get("bonus_active"): return
        new_progress = round(float(row["wager_progress"] or 0) + bet, 8)
        req = float(row["wager_required"] or 0)
        done = new_progress >= req
        update = {"wager_progress": new_progress}
        if done: update["bonus_active"] = False
        await sb(supabase.table("profiles").update(update).eq("id", uid))
    except Exception: log.exception("apply_wager_progress failed")

async def check_and_reset_wager_if_broke(uid):
    try:
        r = await sb(supabase.table("profiles").select("balance, bonus_active").eq("id", uid))
        if not r.data or not r.data[0].get("bonus_active"): return False
        bal = float(r.data[0].get("balance") or 0)
        if bal >= WAGER_RESET_THRESHOLD: return False
        await sb(supabase.table("profiles").update({
            "bonus_active": False, "wager_required": 0, "wager_progress": 0,
            "bonus_amount": 0, "bonus_code": None, "bonus_max_bet": None,
            "bonus_allowed_games": None}).eq("id", uid))
        return True
    except Exception:
        log.exception("check_and_reset_wager_if_broke failed"); return False

async def check_wager_lock(profile):
    if not profile.get("bonus_active"): return
    req = float(profile.get("wager_required") or 0)
    prog = float(profile.get("wager_progress") or 0)
    if prog < req:
        raise HTTPException(400, f"🎰 Бонус активен. Отыграй ещё {round(req-prog,2)} ₮ ({prog:.2f}/{req:.2f})")

async def check_bonus_max_bet(profile, bet):
    if not profile.get("bonus_active"): return
    mb = profile.get("bonus_max_bet")
    if mb and float(bet) > float(mb):
        raise HTTPException(400, f"🎰 Пока бонус активен, макс. ставка {float(mb):.2f} ₮")

async def check_bonus_game(profile, game):
    if not profile.get("bonus_active"): return
    allowed = profile.get("bonus_allowed_games")
    if allowed is None or not isinstance(allowed, list): return
    if game not in allowed:
        if not allowed: raise HTTPException(400, "🎰 Бонус можно только отыграть выводом.")
        raise HTTPException(400, f"🎰 С бонусом доступны только: {', '.join(allowed)}")

def _bonus_info(p):
    return {
        "bonus_active": bool(p.get("bonus_active")),
        "wager_required": float(p.get("wager_required") or 0),
        "wager_progress": float(p.get("wager_progress") or 0),
        "bonus_amount": float(p.get("bonus_amount") or 0),
        "bonus_code": p.get("bonus_code"),
        "bonus_max_bet": float(p["bonus_max_bet"]) if p.get("bonus_max_bet") else None,
        "bonus_allowed_games": p.get("bonus_allowed_games"),
    }

# ================== PAYMENTS ==================
async def create_deposit_invoice(profile, amount, currency="USDT"):
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "неподдерживаемая валюта")
    cid = f"dep_{profile['id'][:8]}_{int(time.time())}"
    inv = await xrocket_create_invoice(amount, "GoldCash deposit", cid, currency)
    await sb(supabase.table("transactions").insert({
        "user_id": profile["id"], "type": "deposit", "amount": amount,
        "currency": currency, "external_id": cid, "status": "pending",
        "meta": {"invoice_id": inv.get("id")}}))
    return {"link": inv["link"], "invoice_id": inv.get("id"), "cid": cid}

async def daily_withdrawn(uid):
    since = (datetime.now(timezone.utc) - timedelta(hours=24)).isoformat()
    r = await sb(supabase.table("transactions").select("amount, status")
                 .eq("user_id", uid).eq("type", "withdraw")
                 .in_("status", ["completed", "pending", "processing"])
                 .gte("created_at", since))
    return sum(float(x["amount"]) for x in r.data or [])

async def do_withdraw(profile, tg_id, amount, currency="USDT"):
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "неподдерживаемая валюта")
    last = await sb(supabase.table("transactions").select("created_at")
                    .eq("user_id", profile["id"]).eq("type", "deposit").eq("status", "completed")
                    .order("created_at", desc=True).limit(1))
    if last.data:
        try:
            dt = datetime.fromisoformat(last.data[0]["created_at"].replace("Z", "+00:00"))
            left = WITHDRAW_COOLDOWN_MIN * 60 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0:
                m, s = divmod(int(left), 60)
                raise HTTPException(400, f"после депозита подожди {m}м {s}с")
        except HTTPException: raise
        except Exception: pass
    spent = await daily_withdrawn(profile["id"])
    if spent + amount > MAX_WITHDRAW_DAILY:
        raise HTTPException(400, f"дневной лимит. Осталось {max(0, MAX_WITHDRAW_DAILY - spent):.2f}")
    cid = f"wd_{profile['id'][:8]}_{int(time.time())}"
    await sb_rpc("change_balance", {"p_user_id": profile["id"], "p_delta": -amount})
    await sb(supabase.table("transactions").insert({
        "user_id": profile["id"], "type": "withdraw", "amount": amount,
        "currency": currency, "external_id": cid, "status": "pending", "meta": {}}))
    try:
        payout = await xrocket_create_payout(tg_id, amount, "GoldCash withdraw", cid, currency)
        await sb(supabase.table("transactions")
                 .update({"meta": {"payout_id": payout.get("id"),
                                    "payout_status": payout.get("status")}})
                 .eq("external_id", cid))
        if payout.get("status") in ("completed", "paid", "success"):
            await sb(supabase.table("transactions")
                     .update({"status": "completed"}).eq("external_id", cid))
        return payout
    except Exception as e:
        log.exception("xRocket payout failed, refunding")
        await sb_rpc("change_balance", {"p_user_id": profile["id"], "p_delta": amount})
        await sb(supabase.table("transactions")
                 .update({"status": "failed", "meta": {"error": str(e)}})
                 .eq("external_id", cid))
        raise

# ================== CRASH LOOP ==================
async def crash_auto_cashout_watcher(round_id, started_at, crash_point_val):
    try:
        while True:
            elapsed = time.time() - started_at
            if elapsed > 120: break
            current = crash_mult(elapsed)
            if current >= crash_point_val: break
            try:
                active = (await sb(supabase.table("crash_bets").select("*")
                                   .eq("round_id", round_id).eq("status", "active")
                                   .not_.is_("auto_cashout_mult", "null"))).data or []
            except Exception: active = []
            for b in active:
                auto = float(b["auto_cashout_mult"])
                if auto <= 0: continue
                if current >= auto:
                    amount = float(b["amount"]); mult = auto
                    payout = round(amount * mult, 8); profit = round(payout - amount, 8)
                    try:
                        await sb(supabase.table("crash_bets").update({
                            "status": "cashed", "cashout_mult": mult, "payout": payout,
                            "auto_cashout_mult": None}).eq("id", b["id"]))
                        await sb_rpc("change_balance", {"p_user_id": b["user_id"], "p_delta": payout})
                        await sb(supabase.table("transactions").insert({
                            "user_id": b["user_id"], "type": "win", "amount": profit,
                            "currency": "USDT", "status": "completed",
                            "meta": {"game": "crash_auto", "mult": mult}}))
                        await log_round(b["user_id"], "crash", amount,
                                        {"auto": True, "mult": mult}, profit, "", 0)
                    except Exception: log.exception("auto cashout failed")
            await asyncio.sleep(0.15)
    except asyncio.CancelledError: pass
    except Exception: log.exception("watcher error")

async def crash_loop():
    global crash_state
    await asyncio.sleep(3)
    while True:
        try:
            ss = os.urandom(16).hex()
            cp = crash_point(ss, "global", 0)
            now = time.time()
            res = await sb(supabase.table("crash_rounds").insert({
                "status": "betting", "server_seed": ss, "crash_point": cp}))
            rid = res.data[0]["id"]
            crash_state.update({"round_id": rid, "status": "betting", "server_seed": ss,
                                "crash_point": cp, "started_at": None,
                                "betting_ends_at": now + CRASH_BETTING_SEC})
            await asyncio.sleep(CRASH_BETTING_SEC)
            started = time.time()
            await sb(supabase.table("crash_rounds").update({
                "status": "running",
                "started_at": datetime.now(timezone.utc).isoformat()}).eq("id", rid))
            crash_state["status"] = "running"; crash_state["started_at"] = started
            auto_task = asyncio.create_task(crash_auto_cashout_watcher(rid, started, cp))
            crash_state["auto_task"] = auto_task
            duration = max(0.4, math.log(cp) / math.log(1.07)) if cp > 1.0 else 0.4
            await asyncio.sleep(duration)
            if not auto_task.done(): auto_task.cancel()
            await sb(supabase.table("crash_rounds").update({
                "status": "crashed",
                "ended_at": datetime.now(timezone.utc).isoformat()}).eq("id", rid))
            crash_state["status"] = "crashed"
            lost = (await sb(supabase.table("crash_bets").select("*")
                             .eq("round_id", rid).eq("status", "active"))).data or []
            for b in lost:
                await sb(supabase.table("crash_bets").update({"status": "lost"}).eq("id", b["id"]))
                await log_round(b["user_id"], "crash", float(b["amount"]),
                                {"crashed_at": cp}, -float(b["amount"]), ss, 0)
                await credit_referrer_on_loss(b["user_id"], float(b["amount"]))
                asyncio.create_task(check_and_reset_wager_if_broke(b["user_id"]))
            await asyncio.sleep(CRASH_COOLDOWN_SEC)
            crash_state["status"] = "idle"; crash_state["round_id"] = None
        except Exception as e:
            log.exception("crash loop error: %s", e)
            await asyncio.sleep(5)

# ================== AIOGRAM ==================
bot = Bot(token=BOT_TOKEN)
dp = Dispatcher()

def main_menu():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎲 Дуэль с ботом", callback_data="duel:home")],
        [InlineKeyboardButton(text="💰 Пополнить", callback_data="menu:deposit"),
         InlineKeyboardButton(text="💸 Вывести", callback_data="menu:withdraw")],
        [InlineKeyboardButton(text="👥 Друзья", callback_data="menu:ref"),
         InlineKeyboardButton(text="📊 Статистика", callback_data="menu:stats")],
        [InlineKeyboardButton(text="📖 Помощь", callback_data="menu:help")],
        [InlineKeyboardButton(text="🌐 Открыть казино", web_app=WebAppInfo(url=WEBAPP_URL))]])

def back_kb():
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])

def fmt_stats(s, balance, first_name, vip=None):
    base = (f"👤 <b>{first_name or 'игрок'}</b>\n\n"
            f"💎 <b>Баланс:</b> {balance:.2f}\n━━━━━━━━━━━━━━━\n"
            f"📥 Пополнено: <b>{s['deposits']:.2f}</b>\n📤 Выведено: <b>{s['withdrawals']:.2f}</b>\n"
            f"🎯 Ставок: <b>{s['bets']:.2f}</b>\n🏆 Выигрышей: <b>{s['wins']:.2f}</b>\n"
            f"🎮 Игр: <b>{s['games']}</b>\n📊 Профит: <b>{s['net']:+.2f}</b>")
    if vip:
        base += (f"\n━━━━━━━━━━━━━━━\n<b>{vip['tier_name']}</b>\n"
                 f"Оборот: {vip['total_wagered']:.2f} ₮\n"
                 f"Рейкбек: {vip['rakeback']*100:.1f}%\n"
                 f"Заработано: {vip['rakeback_earned']:.2f} ₮")
        if vip["next_tier_name"]:
            left = vip["next_tier_at"] - vip["total_wagered"]
            base += f"\nДо {vip['next_tier_name']}: {left:.2f} ₮"
    return base

# ================== DUEL FLOW ==================
async def _duel_bot_roll(chat_id: int, n: int):
    msgs = await asyncio.gather(*[bot.send_dice(chat_id=chat_id, emoji="🎲") for _ in range(n)])
    await asyncio.sleep(3.6)
    return [m.dice.value for m in msgs]


@dp.callback_query(F.data == "duel:home")
async def cb_duel_home(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    text = ("🎲 <b>Дуэль против бота</b>\n\n"
            "Выбери количество кубиков.\n"
            "Обычная игра — побеждает тот, кто выбросит <b>больше</b>.\n"
            "🌀 Крэзи — побеждает тот, кто выбросит <b>меньше</b>.\n\n"
            "Ты кидаешь кубики сам — просто отправь 🎲 в чат.\n"
            "Победитель раунда получает 1 очко. Кто первый дойдёт до цели — забирает банк.")
    try:
        await cb.message.edit_text(text, parse_mode="HTML", reply_markup=duel_home_kb())
    except Exception:
        await bot.send_message(cb.message.chat.id, text, parse_mode="HTML", reply_markup=duel_home_kb())


@dp.callback_query(F.data.startswith("duel:cfg:"))
async def cb_duel_cfg(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    _, _, count_s, crazy_s = cb.data.split(":")
    count = int(count_s); crazy = int(crazy_s)
    icon = "🌀" if crazy else "🎲"
    mode = "Крэзи (меньше — лучше)" if crazy else "Обычная (больше — лучше)"
    text = f"{icon} <b>{count} {_count_word(count)}.</b> · {mode}\n\nДо скольких очков играем?"
    await cb.message.edit_text(text, parse_mode="HTML", reply_markup=duel_target_kb(count, crazy))


@dp.callback_query(F.data.startswith("duel:tgt:"))
async def cb_duel_tgt(cb: CallbackQuery, state: FSMContext):
    _, _, count_s, crazy_s, target_s = cb.data.split(":")
    count = int(count_s); crazy = int(crazy_s); target = int(target_s)
    text = (f"💰 <b>Ставка</b>\n\n"
            f"🎲 {count} {_count_word(count)} · {'🌀 Крэзи' if crazy else '🎲 Обычная'} · до {target} очк.\n"
            f"Победитель получает <b>×{DUEL_PAYOUT}</b> от ставки.")
    await cb.message.edit_text(text, parse_mode="HTML", reply_markup=duel_bet_kb(count, crazy, target))


@dp.callback_query(F.data.startswith("duel:betcustom:"))
async def cb_duel_betcustom(cb: CallbackQuery, state: FSMContext):
    _, _, count_s, crazy_s, target_s = cb.data.split(":")
    await state.set_state(DuelState.custom_bet)
    await state.update_data(count=int(count_s), crazy=int(crazy_s), target=int(target_s))
    await cb.message.edit_text(
        f"✏️ Введи ставку ({MIN_BET}–{MAX_BET} ₮):",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="⬅️ Назад",
                callback_data=f"duel:tgt:{count_s}:{crazy_s}:{target_s}")]]))


@dp.message(DuelState.custom_bet)
async def fsm_duel_custom_bet(message: Message, state: FSMContext):
    data = await state.get_data()
    try: bet = float((message.text or "").replace(",", ".").strip())
    except (TypeError, ValueError): return await message.answer("❌ Введи число")
    if not (MIN_BET <= bet <= MAX_BET):
        return await message.answer(f"❌ Ставка должна быть {MIN_BET}–{MAX_BET}")
    count = int(data["count"]); crazy = int(data["crazy"]); target = int(data["target"])
    await state.clear()
    await _duel_start(message, message.from_user.model_dump(), count, crazy, target, bet, edit=False)


@dp.callback_query(F.data.startswith("duel:bet:"))
async def cb_duel_bet(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    _, _, count_s, crazy_s, target_s, bet_s = cb.data.split(":")
    count = int(count_s); crazy = int(crazy_s); target = int(target_s)
    try: bet = float(bet_s)
    except ValueError: return await cb.answer("Ошибка", show_alert=True)
    await _duel_start(cb.message, cb.from_user.model_dump(), count, crazy, target, bet, edit=True)


async def _duel_start(msg, tg_user, count, crazy, target, bet, edit=False):
    if not (MIN_BET <= bet <= MAX_BET):
        return await _answer(msg, f"❌ Ставка {MIN_BET}–{MAX_BET}", edit)
    p = await get_or_create_profile(tg_user)
    try:
        await ensure_not_banned(p)
        await check_bonus_max_bet(p, bet)
        await check_bonus_game(p, "duel")
        await check_rate_limit(p["id"], "bet")
    except HTTPException as e:
        return await _answer(msg, e.detail, edit)
    if float(p["balance"]) < bet:
        return await _answer(msg, "❌ Недостаточно средств", edit)
    if await get_active_round(p["id"]):
        return await _answer(msg, "❌ Есть незавершённая игра. Заверши её сначала.", edit)

    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))

    st = {"count": count, "crazy": crazy, "target": target, "bet": bet,
          "ps": 0, "bs": 0, "round": 1, "phase": "idle",
          "bot_rolls": [], "player_rolls": []}
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "duel", "bet_amount": bet,
        "state": st, "server_seed": "", "nonce": 0}))

    _duel_last_cfg[int(tg_user["id"])] = {
        "count": count, "crazy": crazy, "target": target, "bet": bet
    }

    icon = "🌀" if crazy else "🎲"
    text = (f"{icon} <b>Дуэль началась!</b>\n\n"
            f"🎲 {count} {_count_word(count)} · {'Крэзи' if crazy else 'Обычная'} · до {target} очк.\n"
            f"Ставка: {bet:.2f} ₮\n\n"
            f"{_score_block(0, 0, _fmt_name(tg_user))}\n\n"
            f"Раунд 1 — жми кнопку.")
    if edit:
        try: await msg.edit_text(text, parse_mode="HTML", reply_markup=duel_roll_kb())
        except Exception:
            await bot.send_message(msg.chat.id, text, parse_mode="HTML", reply_markup=duel_roll_kb())
    else:
        await msg.answer(text, parse_mode="HTML", reply_markup=duel_roll_kb())


async def _answer(target, text, edit):
    try:
        if edit: await target.edit_text(f"⚠️ {text}")
        else: await target.answer(f"⚠️ {text}")
    except Exception: pass


@dp.callback_query(F.data == "duel:roll")
async def cb_duel_roll(cb: CallbackQuery, state: FSMContext):
    p = await get_or_create_profile(cb.from_user.model_dump())
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "duel":
        return await cb.answer("Нет активной дуэли", show_alert=True)
    st = ar["state"]
    if st.get("phase", "idle") != "idle":
        return await cb.answer("Раунд уже идёт", show_alert=True)

    count = int(st["count"])
    round_no = st.get("round", 1)
    player_name = _fmt_name(cb.from_user.model_dump())

    await cb.answer()
    st["phase"] = "bot_rolling"
    await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))

    try: await cb.message.edit_text(f"🎲 Раунд {round_no}\n\n🤖 {BOT_NAME} бросает...")
    except Exception: pass

    try:
        bot_rolls = await _duel_bot_roll(cb.message.chat.id, count)
    except Exception:
        log.exception("duel bot roll failed")
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": float(st["bet"])})
        await clear_active_round(p["id"])
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "admin", "amount": float(st["bet"]),
            "currency": "USDT", "status": "completed",
            "meta": {"action": "duel_refund", "reason": "bot_roll_failed"}}))
        return await bot.send_message(cb.message.chat.id,
            "❌ Ошибка анимации. Ставка возвращена.", reply_markup=duel_again_kb())

    bot_sum = sum(bot_rolls)
    st["bot_rolls"] = bot_rolls
    st["player_rolls"] = []
    st["phase"] = "awaiting_player_roll"
    await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))

    word = _count_word(count)
    await bot.send_message(cb.message.chat.id,
        f"🤖 {BOT_NAME}: {_faces(bot_rolls)} = <b>{bot_sum}</b>\n\n"
        f"👤 {player_name}, твой ход!\n"
        f"Отправь 🎲 в чат <b>{count} {word}</b> (можно без ответа на сообщение).\n"
        f"Прогресс: 0/{count}",
        parse_mode="HTML")


@dp.message(F.dice)
async def on_dice_message(message: Message):
    """Ловим кубики, отправленные игроком."""
    if not message.dice or message.dice.emoji != "🎲":
        return

    p = await get_profile_by_tg(message.from_user.id)
    if not p: return

    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "duel":
        return

    st = ar["state"]
    if st.get("phase") != "awaiting_player_roll":
        try: await message.reply("⚠️ Сейчас не твой ход. Нажми «🎲 Кинуть кости».")
        except Exception: pass
        return

    count = int(st["count"]); crazy = int(st["crazy"]); target = int(st["target"])
    bet = float(st["bet"]); ps = int(st["ps"]); bs = int(st["bs"])
    round_no = st.get("round", 1)
    player_name = _fmt_name(message.from_user.model_dump())

    val = message.dice.value
    player_rolls = st.get("player_rolls") or []
    if len(player_rolls) >= count:
        return

    player_rolls.append(val)
    st["player_rolls"] = player_rolls

    try: await message.delete()
    except Exception: pass

    if len(player_rolls) < count:
        await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))
        await bot.send_message(message.chat.id,
            f"🎲 Бросок {len(player_rolls)}/{count}: <b>{val}</b>\n"
            f"Отправь ещё 🎲 ({len(player_rolls)+1}/{count})",
            parse_mode="HTML")
        return

    bot_rolls = st.get("bot_rolls") or []
    bot_sum = sum(bot_rolls); player_sum = sum(player_rolls)

    tie = (player_sum == bot_sum)
    if tie:
        result_line = "🤝 Ничья — раунд переигрывается!"
    elif crazy:
        if player_sum < bot_sum:
            ps += 1; result_line = "✅ Ты выиграл раунд!"
        else:
            bs += 1; result_line = "❌ Бот выиграл раунд"
    else:
        if player_sum > bot_sum:
            ps += 1; result_line = "✅ Ты выиграл раунд!"
        else:
            bs += 1; result_line = "❌ Бот выиграл раунд"

    st["ps"] = ps; st["bs"] = bs
    st["round"] = round_no + 1

    if ps >= target or bs >= target:
        player_won = ps >= target
        payout = 0.0; profit = -bet

        if player_won:
            payout = round(bet * DUEL_PAYOUT, 8)
            profit = round(payout - bet, 8)
            await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
            await sb(supabase.table("transactions").insert({
                "user_id": p["id"], "type": "win", "amount": profit,
                "currency": "USDT", "status": "completed",
                "meta": {"game": "duel", "won": True,
                         "count": count, "crazy": bool(crazy), "target": target}}))
        else:
            asyncio.create_task(credit_referrer_on_loss(p["id"], bet))

        await log_round(p["id"], "duel", bet,
                        {"count": count, "crazy": bool(crazy), "target": target,
                         "player": ps, "bot": bs, "won": player_won},
                        profit, "", 0)
        await clear_active_round(p["id"])

        p2 = await get_or_create_profile(message.from_user.model_dump())
        bal = float(p2["balance"])
        wager_reset = False
        if not player_won and bal < WAGER_RESET_THRESHOLD:
            wager_reset = await check_and_reset_wager_if_broke(p2["id"])

        if player_won:
            final = (f"🏆 <b>ПОБЕДА!</b>\n\n"
                     f"🤖 {BOT_NAME}: {_faces(bot_rolls)} = {bot_sum}\n"
                     f"👤 {player_name}: {_faces(player_rolls)} = {player_sum}\n\n"
                     f"{result_line}\n\n"
                     f"{_score_block(ps, bs, player_name)}\n\n"
                     f"💰 Выплата: +{payout:.2f} ₮ (×{DUEL_PAYOUT})\n"
                     f"💵 Чистыми: +{profit:.2f} ₮\n"
                     f"💎 Баланс: <b>{bal:.2f} ₮</b>")
        else:
            final = (f"💀 <b>Проигрыш</b>\n\n"
                     f"🤖 {BOT_NAME}: {_faces(bot_rolls)} = {bot_sum}\n"
                     f"👤 {player_name}: {_faces(player_rolls)} = {player_sum}\n\n"
                     f"{result_line}\n\n"
                     f"{_score_block(ps, bs, player_name)}\n\n"
                     f"😢 Потеряно: −{bet:.2f} ₮\n"
                     f"💎 Баланс: <b>{bal:.2f} ₮</b>")
        if wager_reset:
            final += "\n♻️ Бонус сброшен (баланс ниже порога)"

        await bot.send_message(message.chat.id, final, parse_mode="HTML",
                              reply_markup=duel_again_kb())
        return

    st["phase"] = "idle"
    st["player_rolls"] = []
    st["bot_rolls"] = []
    await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))

    icon = "🌀" if crazy else "🎲"
    text = (f"{icon} Раунд {round_no} завершён\n\n"
            f"🤖 {BOT_NAME}: {_faces(bot_rolls)} = <b>{bot_sum}</b>\n"
            f"👤 {player_name}: {_faces(player_rolls)} = <b>{player_sum}</b>\n\n"
            f"{result_line}\n\n"
            f"{_score_block(ps, bs, player_name)}\n\n"
            f"Раунд {st['round']} — жми кнопку.")
    await bot.send_message(message.chat.id, text, parse_mode="HTML",
                          reply_markup=duel_roll_kb())


@dp.callback_query(F.data == "duel:again")
async def cb_duel_again(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    cfg = _duel_last_cfg.get(cb.from_user.id)
    if not cfg:
        return await cb_duel_home(cb, state)
    await _duel_start(cb.message, cb.from_user.model_dump(),
                      int(cfg["count"]), int(cfg["crazy"]),
                      int(cfg["target"]), float(cfg["bet"]), edit=True)


@dp.callback_query(F.data == "duel:surrender")
async def cb_duel_surrender(cb: CallbackQuery, state: FSMContext):
    p = await get_or_create_profile(cb.from_user.model_dump())
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "duel":
        return await cb.answer("Нет активной дуэли", show_alert=True)
    st = ar["state"]; bet = float(st["bet"]); ps = int(st["ps"]); bs = int(st["bs"])
    player_name = _fmt_name(cb.from_user.model_dump())
    await clear_active_round(p["id"])
    await log_round(p["id"], "duel", bet,
                    {"count": st["count"], "crazy": bool(st["crazy"]),
                     "target": st["target"], "surrender": True,
                     "player": ps, "bot": bs, "won": False},
                    -bet, "", 0)
    asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
    asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    bal = float((await get_or_create_profile(cb.from_user.model_dump()))["balance"])
    await cb.message.edit_text(
        f"🏳️ <b>Сдался</b>\n\n"
        f"{_score_block(ps, bs, player_name)}\n\n"
        f"Потеряно: −{bet:.2f} ₮\n"
        f"💎 Баланс: <b>{bal:.2f} ₮</b>",
        parse_mode="HTML", reply_markup=duel_again_kb())

# ================== ADMIN HELPERS ==================
def admin_only(message: Message) -> bool:
    return message.from_user and is_admin(message.from_user.id)

async def admin_get_user(message: Message, arg: str):
    arg = (arg or "").strip()
    if not arg: return None
    if arg.startswith("@"):
        r = await sb(supabase.table("profiles").select("*").eq("username", arg[1:]))
        return r.data[0] if r.data else None
    try: return await get_profile_by_tg(int(arg))
    except Exception: return None

# ================== ADMIN COMMANDS ==================
@dp.message(Command("ahelp"))
async def cmd_ahelp(message: Message):
    if not admin_only(message): return
    await message.answer(
        "<b>🛠 АДМИН-КОМАНДЫ</b>\n"
        "/astatus /aon GAME /aoff GAME /aonall /aoffall\n"
        "/aendgame ID [lose] /aendgameall /aactive ID /aactivelist /acleargames\n"
        "/auser /afind /awhois /agive /atake /asetbal\n"
        "/aban /aunban /abanlist /apause /aunpause /anote /anotes\n"
        "/aresetnonce /aresetserver /asetvip ID TIER /arak ID [сумма]\n"
        "/arisk ID /aflag ID [reason] /aunflag ID /aalts ID /aantifraud /asamelist\n"
        "/astats /aggr /abalances /aonline /arich /adaily /aweekly /agames\n"
        "/atop /atopdep /atopwd /arp /avip [ID] /aduelinfo\n"
        "/atx /atxlast /arefund /acheckpending\n"
        "/anewpromo CODE SUM [WAGER] [USES] [MAX_BET] [GAMES]\n"
        "/alistpromos /adelpromo /adelallpromos /apromoinfo /awager /aresetwager\n"
        "/apromogames /asetbonusgames\n"
        "/abroadcast /apush /asettings /asetrtp /asetminbet /asetmaxbet\n"
        "/asetmindep /asetminwd /asetmaxwd /asetref /asetcooldown /amaintenance\n"
        "/ahealth /alogs /aclearlogs /aadmins", parse_mode="HTML")

@dp.message(Command("admin"))
async def cmd_admin(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"🏦 <b>Админ-панель</b>\nRTP {100-HOUSE_EDGE*100:.0f}% · HE {HOUSE_EDGE*100:.1f}%\n"
        f"Bet {MIN_BET}-{MAX_BET} · Деп {MIN_DEPOSIT} · Вывод {MIN_WITHDRAW}\n"
        f"Лимит вывода {MAX_WITHDRAW_DAILY}/сутки · Кулдаун {WITHDRAW_COOLDOWN_MIN}м\n"
        f"Рефералка {REFERRAL_SHARE*100:.0f}% · Daily {DAILY_BONUS}₮/{BONUS_COOLDOWN_H}ч\n"
        f"Antifraud: {'✅' if ANTIFRAUD_ENABLED else '❌'} (порог {AUTO_FLAG_SCORE})\n"
        f"Maintenance: {'🚫 ON' if MAINTENANCE else '✅ OFF'}\n"
        f"Игры: {sum(1 for v in GAMES_ENABLED.values() if v)}/{len(GAMES_ENABLED)}\n"
        f"Канал: {CHANNEL_ID or '— не задан —'}\n"
        f"Все команды: /ahelp", parse_mode="HTML")

@dp.message(Command("astatus"))
async def cmd_astatus(message: Message):
    if not admin_only(message): return
    lines = [f"{'✅' if v else '⛔'} <code>{k}</code>" for k, v in GAMES_ENABLED.items()]
    await message.answer("<b>🎮 Статус</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("aon"))
async def cmd_aon(message: Message, command: CommandObject):
    if not admin_only(message): return
    g = (command.args or "").strip().lower()
    if g not in GAMES_ENABLED: return await message.answer(f"❌ {g}")
    GAMES_ENABLED[g] = True
    await message.answer(f"✅ <b>{g}</b> вкл", parse_mode="HTML")

@dp.message(Command("aoff"))
async def cmd_aoff(message: Message, command: CommandObject):
    if not admin_only(message): return
    g = (command.args or "").strip().lower()
    if g not in GAMES_ENABLED: return await message.answer(f"❌ {g}")
    GAMES_ENABLED[g] = False
    await message.answer(f"⛔ <b>{g}</b> выкл", parse_mode="HTML")

@dp.message(Command("aonall"))
async def cmd_aonall(message: Message):
    if not admin_only(message): return
    for g in GAMES_ENABLED: GAMES_ENABLED[g] = True
    await message.answer("✅ Все игры вкл")

@dp.message(Command("aoffall"))
async def cmd_aoffall(message: Message):
    if not admin_only(message): return
    for g in GAMES_ENABLED: GAMES_ENABLED[g] = False
    await message.answer("⛔ Все игры выкл")

@dp.message(Command("aduelinfo"))
async def cmd_aduelinfo(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"🎲 <b>Дуэль</b>\n\n"
        f"Множитель победы: <b>×{DUEL_PAYOUT}</b>\n"
        f"HE: <b>{100-HOUSE_EDGE*100:.1f}%</b>\n"
        f"Ставки: {', '.join(str(b) for b in DUEL_BETS)}\n"
        f"Режимы: 1/2/3 куба · обычная/крэзи\n"
        f"Цели: до 1/2/3 очков\n"
        f"Игрок бросает кубики сам (отправляет 🎲)",
        parse_mode="HTML")

@dp.message(Command("acheckpending"))
async def cmd_acheckpending(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("transactions").select("*")
                 .eq("type", "deposit").eq("status", "pending")
                 .order("created_at", desc=True).limit(50))
    txs = r.data or []
    if not txs: return await message.answer("Нет pending депозитов")
    await message.answer(f"🔎 Проверяю {len(txs)} pending…")
    credited = 0; failed = 0
    for tx in txs:
        inv_id = (tx.get("meta") or {}).get("invoice_id")
        if not inv_id: failed += 1; continue
        data = await xrocket_get_invoice(inv_id)
        if not data: failed += 1; continue
        if (data.get("status") or "").lower() in ("paid", "completed", "success"):
            claim = await sb(supabase.table("transactions")
                             .update({"status": "processing"})
                             .eq("id", tx["id"]).eq("status", "pending"))
            if not claim.data: failed += 1; continue
            await sb_rpc("change_balance", {"p_user_id": tx["user_id"], "p_delta": float(tx["amount"])})
            await sb(supabase.table("transactions").update({
                "status": "completed",
                "meta": {**(tx.get("meta") or {}),
                         "credited_at": datetime.now(timezone.utc).isoformat(),
                         "source": "admin_check"},
            }).eq("id", tx["id"]))
            credited += 1
        else: failed += 1
    await message.answer(f"✅ Зачислено: <b>{credited}</b>\n⏳ Ещё в ожидании: <b>{failed}</b>", parse_mode="HTML")

@dp.message(Command("avip"))
async def cmd_avip(message: Message, command: CommandObject):
    if not admin_only(message): return
    if command.args:
        p = await admin_get_user(message, command.args)
        if not p: return await message.answer("Не найден")
        v = vip_info(p)
        await message.answer(
            f"👤 <b>{p['telegram_id']}</b>\n{v['tier_name']} · оборот {v['total_wagered']:.2f}\n"
            f"Рейкбек {v['rakeback']*100:.1f}% · накоплено {v['rakeback_earned']:.2f}\n"
            + (f"До {v['next_tier_name']}: {v['next_tier_at']-v['total_wagered']:.2f}"
               if v['next_tier_name'] else "Максимум"), parse_mode="HTML")
        return
    r = await sb(supabase.table("profiles").select(
        "telegram_id, first_name, total_wagered, vip_tier").order("total_wagered", desc=True).limit(15))
    lines = [f"{i+1}. <b>{x.get('first_name') or x['telegram_id']}</b> — "
             f"{float(x.get('total_wagered') or 0):.2f} [{x.get('vip_tier')}]"
             for i, x in enumerate(r.data or [])]
    await message.answer("<b>💎 Топ VIP</b>\n" + ("\n".join(lines) if lines else "—"), parse_mode="HTML")

@dp.message(Command("asetvip"))
async def cmd_asetvip(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) != 2: return await message.answer("/asetvip <id> <tier>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    tier = parts[1].strip().lower()
    if tier not in [t["id"] for t in VIP_TIERS]: return await message.answer("Нет тира")
    await sb(supabase.table("profiles").update({"vip_tier": tier}).eq("id", p["id"]))
    await message.answer(f"✅ {p['telegram_id']} → {tier}")

@dp.message(Command("arak"))
async def cmd_arak(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if not parts: return await message.answer("/arak <id> [сумма]")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    try: amount = float(parts[1].replace(",", ".")) if len(parts) > 1 else 0
    except: return await message.answer("Числом")
    if amount <= 0: amount = round(float(p.get("total_wagered") or 0) * 0.005, 4)
    if amount <= 0: return await message.answer("Нечего начислять")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    cur = float(p.get("rakeback_earned") or 0)
    await sb(supabase.table("profiles").update(
        {"rakeback_earned": round(cur + amount, 8),
         "last_rakeback_at": datetime.now(timezone.utc).isoformat()}).eq("id", p["id"]))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": amount,
        "currency": "USDT", "status": "completed", "meta": {"source": "rakeback"}}))
    await message.answer(f"✅ Рейкбек +{amount:.2f} → {p['telegram_id']}")

@dp.message(Command("atestsub"))
async def cmd_atestsub(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not CHANNEL_ID: return await message.answer("❌ CHANNEL_ID не задан")
    target_id = message.from_user.id
    if command.args and command.args.strip().lstrip("-").isdigit():
        target_id = int(command.args.strip())
    try:
        member = await bot.get_chat_member(chat_id=CHANNEL_ID, user_id=target_id)
        await message.answer(
            f"<b>🔍 Проверка</b>\nCHANNEL_ID: <code>{CHANNEL_ID}</code>\n"
            f"User: <code>{target_id}</code>\nStatus: <b>{member.status}</b>\n"
            f"Result: <b>{'✅ PASS' if member.status in ('member','administrator','creator') else '❌ FAIL'}</b>",
            parse_mode="HTML")
    except Exception as e:
        await message.answer(f"❌ <b>Ошибка:</b>\n<code>{e}</code>", parse_mode="HTML")

@dp.message(Command("arisk"))
async def cmd_arisk(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    await message.answer(
        f"👤 <code>{p['telegram_id']}</code>\nRisk: <b>{p.get('risk_score', 0)}</b>\n"
        f"Flagged: {'🚩 YES' if p.get('auto_flagged') else '✅ no'}\n"
        f"Reason: {p.get('flag_reason') or '—'}\n"
        f"IP (last): {p.get('last_ip') or '—'}\nIP (signup): {p.get('signup_ip') or '—'}\n"
        f"Fingerprint: <code>{(p.get('device_fingerprint') or '—')[:24]}</code>", parse_mode="HTML")

@dp.message(Command("aflag"))
async def cmd_aflag(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if not parts: return await message.answer("/aflag <id> [reason]")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    reason = parts[1] if len(parts) > 1 else "manual flag"
    await sb(supabase.table("profiles").update({"auto_flagged": True, "flag_reason": reason}).eq("id", p["id"]))
    await log_antifraud(p["id"], "manual_flag", {"reason": reason, "by": message.from_user.id})
    await message.answer(f"🚩 Зафлагован {p['telegram_id']}: {reason}")

@dp.message(Command("aunflag"))
async def cmd_aunflag(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    await sb(supabase.table("profiles").update({"auto_flagged": False, "flag_reason": None, "risk_score": 0}).eq("id", p["id"]))
    await message.answer(f"✅ Разфлагован {p['telegram_id']}")

@dp.message(Command("aalts"))
async def cmd_aalts(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    r = await sb(supabase.table("alt_accounts").select("*").eq("user_id", p["id"]))
    if not r.data: return await message.answer("Связей нет")
    ids = [x["linked_user_id"] for x in r.data]
    prof = await sb(supabase.table("profiles").select("id, telegram_id, first_name").in_("id", ids))
    nm = {x["id"]: x for x in prof.data or []}
    lines = [f"• <code>{nm.get(x['linked_user_id'], {}).get('telegram_id')}</code> "
             f"{nm.get(x['linked_user_id'], {}).get('first_name') or ''} — {x['reason']} ({x['confidence']}%)"
             for x in r.data]
    await message.answer(f"<b>🔗 Связи {p['telegram_id']}</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("aantifraud"))
async def cmd_aantifraud(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(hours=24)).isoformat()
    r = await sb(supabase.table("antifraud_log").select("*")
                 .gte("created_at", since).order("created_at", desc=True).limit(30))
    if not r.data: return await message.answer("Событий нет")
    lines = [f"• {x['event']} · {str(x['user_id'])[:8]} · {x['created_at'][:16]}" for x in r.data]
    await message.answer("<b>🚨 Antifraud (24ч)</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("asamelist"))
async def cmd_asamelist(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("alt_accounts").select("*").order("created_at", desc=True).limit(50))
    if not r.data: return await message.answer("Связей нет")
    ids = list(set([x["user_id"] for x in r.data] + [x["linked_user_id"] for x in r.data]))
    prof = await sb(supabase.table("profiles").select("id, telegram_id").in_("id", ids))
    nm = {x["id"]: x["telegram_id"] for x in prof.data or []}
    lines = [f"• {nm.get(x['user_id'], '?')} ↔ {nm.get(x['linked_user_id'], '?')} ({x['reason']})" for x in r.data]
    await message.answer("<b>🔗 Мульти-аккаунты</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("aendgame"))
async def cmd_aendgame(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if not parts: return await message.answer("/aendgame <id> [lose]")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    mode = parts[1].lower() if len(parts) > 1 else "refund"
    ar = await get_active_round(p["id"])
    if not ar: return await message.answer("Нет активной игры")
    bet = float(ar["bet_amount"])
    if mode != "lose":
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": bet})
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "admin", "amount": bet, "currency": "USDT",
            "status": "completed", "meta": {"action": "endgame"}}))
    await clear_active_round(p["id"])
    await message.answer(f"✅ {ar['game_type']} завершена ({mode})")

@dp.message(Command("aendgameall"))
async def cmd_aendgameall(message: Message):
    if not admin_only(message): return
    rounds = (await sb(supabase.table("active_rounds").select("*"))).data or []
    ok = 0; total = 0.0
    for ar in rounds:
        bet = float(ar["bet_amount"]); uid = ar["user_id"]
        try:
            await sb_rpc("change_balance", {"p_user_id": uid, "p_delta": bet})
            await sb(supabase.table("active_rounds").delete().eq("user_id", uid))
            total += bet; ok += 1
        except Exception: pass
    await message.answer(f"✅ {ok} игр, возвращено {total:.2f}")

@dp.message(Command("aactive"))
async def cmd_aactive(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    ar = await get_active_round(p["id"])
    if not ar: return await message.answer("Нет активной игры")
    await message.answer(f"🎮 {ar['game_type']} · {float(ar['bet_amount']):.2f}\n"
                         f"<code>{json.dumps(ar.get('state', {}))[:400]}</code>", parse_mode="HTML")

@dp.message(Command("aactivelist"))
async def cmd_aactivelist(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("active_rounds").select("*").order("started_at", desc=True).limit(30))
    if not r.data: return await message.answer("Нет активных")
    lines = [f"• {x['game_type']} · {float(x['bet_amount']):.2f} · {str(x['user_id'])[:8]}" for x in r.data]
    await message.answer("<b>🎮 Активные</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("acleargames"))
async def cmd_acleargames(message: Message):
    if not admin_only(message): return
    await sb(supabase.table("active_rounds").delete().neq("user_id", "00000000-0000-0000-0000-000000000000"))
    await message.answer("✅ Очищено")

@dp.message(Command("auser"))
async def cmd_auser(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    s = await get_user_stats(p["id"]); v = vip_info(p)
    ban = "🚫" if p.get("is_banned") else "✅"
    flag = "🚩" if p.get("auto_flagged") else ""
    await message.answer(
        f"👤 <b>{p.get('first_name') or '—'}</b> @{p.get('username') or '—'}\n"
        f"🆔 <code>{p['telegram_id']}</code>\n💎 <b>{float(p['balance']):.2f}</b> {ban}{flag}\n"
        f"{v['tier_name']} · оборот {v['total_wagered']:.2f}\n"
        f"📥 {s['deposits']:.2f} · 📤 {s['withdrawals']:.2f}\n"
        f"🎯 {s['bets']:.2f} · 🏆 {s['wins']:.2f}\n🎮 {s['games']} · 📊 {s['net']:+.2f}", parse_mode="HTML")

@dp.message(Command("afind"))
async def cmd_afind(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    s = await get_user_stats(p["id"])
    await message.answer(
        f"👤 {p.get('first_name') or '—'} @{p.get('username') or '—'}\n"
        f"🆔 <code>{p['telegram_id']}</code>\n💎 {float(p['balance']):.2f}\n"
        f"Игр: {s['games']} · профит: {s['net']:+.2f}", parse_mode="HTML")

@dp.message(Command("awhois"))
async def cmd_awhois(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    ar = await get_active_round(p["id"])
    extra = f"\n🎮 {ar['game_type']}" if ar else ""
    await message.answer(
        f"👤 {p.get('first_name') or '—'} @{p.get('username') or '—'}\n"
        f"🆔 <code>{p['telegram_id']}</code>\n💎 {float(p['balance']):.2f}{extra}", parse_mode="HTML")

@dp.message(Command("agive"))
async def cmd_agive(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) != 2: return await message.answer("/agive <id> <сумма>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    try: amount = float(parts[1].replace(",", "."))
    except: return await message.answer("Числом")
    if amount <= 0: return await message.answer("> 0")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "admin", "amount": amount, "currency": "USDT",
        "status": "completed", "meta": {"by": message.from_user.id}}))
    await message.answer(f"✅ +{amount} → {p['telegram_id']}")

@dp.message(Command("atake"))
async def cmd_atake(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) != 2: return await message.answer("/atake <id> <сумма>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    try: amount = float(parts[1].replace(",", "."))
    except: return await message.answer("Числом")
    if float(p["balance"]) < amount: return await message.answer("Мало")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -amount})
    await message.answer(f"✅ −{amount} у {p['telegram_id']}")

@dp.message(Command("asetbal"))
async def cmd_asetbal(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) != 2: return await message.answer("/asetbal <id> <сумма>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    try: nb = float(parts[1].replace(",", "."))
    except: return await message.answer("Числом")
    diff = nb - float(p["balance"])
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": diff})
    await message.answer(f"✅ Баланс {p['telegram_id']} = {nb:.2f}")

@dp.message(Command("aban"))
async def cmd_aban(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if not parts: return await message.answer("/aban <id> [reason]")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    reason = parts[1] if len(parts) > 1 else "нарушение"
    await sb(supabase.table("profiles").update({"is_banned": True, "ban_reason": reason}).eq("id", p["id"]))
    await message.answer(f"🚫 {p['telegram_id']} забанен: {reason}")

@dp.message(Command("aunban"))
async def cmd_aunban(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    await sb(supabase.table("profiles").update({"is_banned": False, "ban_reason": None}).eq("id", p["id"]))
    await message.answer(f"✅ {p['telegram_id']} разбанен")

@dp.message(Command("abanlist"))
async def cmd_abanlist(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("profiles").select("telegram_id, first_name, ban_reason")
                 .eq("is_banned", True).limit(50))
    if not r.data: return await message.answer("Пусто")
    lines = [f"• <code>{x['telegram_id']}</code> — {x.get('ban_reason') or '—'}" for x in r.data]
    await message.answer("<b>🚫 Банлист</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("apause"))
async def cmd_apause(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    await sb(supabase.table("profiles").update({"is_banned": True, "ban_reason": "paused"}).eq("id", p["id"]))
    await message.answer(f"⏸ {p['telegram_id']}")

@dp.message(Command("aunpause"))
async def cmd_aunpause(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    await sb(supabase.table("profiles").update({"is_banned": False, "ban_reason": None}).eq("id", p["id"]))
    await message.answer(f"▶️ {p['telegram_id']}")

@dp.message(Command("anote"))
async def cmd_anote(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2: return await message.answer("/anote <id> <text>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    meta = p.get("admin_notes") or []
    if not isinstance(meta, list): meta = []
    meta.append({"by": message.from_user.id, "text": parts[1], "at": datetime.now(timezone.utc).isoformat()})
    await sb(supabase.table("profiles").update({"admin_notes": meta}).eq("id", p["id"]))
    await message.answer("✅")

@dp.message(Command("anotes"))
async def cmd_anotes(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    meta = p.get("admin_notes") or []
    if not meta: return await message.answer("Пусто")
    lines = [f"• {n.get('text')}" for n in meta]
    await message.answer("<b>📝</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("aresetnonce"))
async def cmd_aresetnonce(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    await sb(supabase.table("profiles").update({"nonce": 0}).eq("id", p["id"]))
    await message.answer("✅")

@dp.message(Command("aresetserver"))
async def cmd_aresetserver(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    seed = os.urandom(16).hex()
    await sb(supabase.table("profiles").update({"client_seed": seed}).eq("id", p["id"]))
    await message.answer(f"✅ <code>{seed}</code>", parse_mode="HTML")

@dp.message(Command("astats"))
async def cmd_astats(message: Message):
    if not admin_only(message): return
    users = (await sb(supabase.table("profiles").select("id, balance, total_wagered"))).data or []
    tx = (await sb(supabase.table("transactions").select("type, amount, status"))).data or []
    rounds = (await sb(supabase.table("game_rounds").select("bet_amount, profit"))).data or []
    dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    bets = sum(float(r["bet_amount"]) for r in rounds)
    ggr = -sum(float(r["profit"]) for r in rounds)
    await message.answer(
        f"👥 Юзеров: <b>{len(users)}</b>\n💰 Балансов: <b>{sum(float(u['balance']) for u in users):.2f}</b>\n"
        f"📥 Депозиты: <b>{dep:.2f}</b>\n📤 Выводы: <b>{wd:.2f}</b>\n"
        f"🎯 Оборот: <b>{bets:.2f}</b>\n📈 GGR: <b>{ggr:+.2f}</b>\n🎮 Игр: {len(rounds)}", parse_mode="HTML")

@dp.message(Command("aggr"))
async def cmd_aggr(message: Message):
    if not admin_only(message): return
    rounds = (await sb(supabase.table("game_rounds").select("bet_amount, profit"))).data or []
    turnover = sum(float(r["bet_amount"]) for r in rounds)
    ggr = -sum(float(r["profit"]) for r in rounds)
    rtp = (turnover - ggr) / turnover if turnover else 0
    await message.answer(f"<b>📈 GGR</b>\nОборот {turnover:.2f}\nGGR {ggr:+.2f}\nRTP {rtp*100:.2f}%", parse_mode="HTML")

@dp.message(Command("abalances"))
async def cmd_abalances(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("profiles").select("balance"))
    total = sum(float(x["balance"]) for x in r.data or [])
    await message.answer(f"💰 Всего: {total:.2f}")

@dp.message(Command("aonline"))
async def cmd_aonline(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(minutes=5)).isoformat()
    r = await sb(supabase.table("action_log").select("user_id").gte("created_at", since))
    await message.answer(f"👥 Онлайн: {len(set(x['user_id'] for x in r.data or []))}")

@dp.message(Command("arich"))
async def cmd_arich(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("profiles").select("telegram_id, first_name, balance")
                 .order("balance", desc=True).limit(15))
    lines = [f"{i+1}. <b>{x.get('first_name') or x['telegram_id']}</b> — {float(x['balance']):.2f}"
             for i, x in enumerate(r.data or [])]
    await message.answer("<b>💰 Топ</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("adaily"))
async def cmd_adaily(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(days=1)).isoformat()
    tx = (await sb(supabase.table("transactions").select("type, amount, status").gte("created_at", since))).data or []
    rounds = (await sb(supabase.table("game_rounds").select("bet_amount, profit").gte("created_at", since))).data or []
    dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    bets = sum(float(r["bet_amount"]) for r in rounds)
    ggr = -sum(float(r["profit"]) for r in rounds)
    await message.answer(f"<b>📅 24ч</b>\nДепозиты {dep:.2f}\nВыводы {wd:.2f}\nОборот {bets:.2f}\nGGR {ggr:+.2f}", parse_mode="HTML")

@dp.message(Command("aweekly"))
async def cmd_aweekly(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(days=7)).isoformat()
    tx = (await sb(supabase.table("transactions").select("type, amount, status").gte("created_at", since))).data or []
    rounds = (await sb(supabase.table("game_rounds").select("bet_amount, profit").gte("created_at", since))).data or []
    dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    bets = sum(float(r["bet_amount"]) for r in rounds)
    ggr = -sum(float(r["profit"]) for r in rounds)
    await message.answer(f"<b>📅 7д</b>\nДепозиты {dep:.2f}\nВыводы {wd:.2f}\nОборот {bets:.2f}\nGGR {ggr:+.2f}", parse_mode="HTML")

@dp.message(Command("agames"))
async def cmd_agames(message: Message):
    if not admin_only(message): return
    rounds = (await sb(supabase.table("game_rounds").select("game_type, bet_amount, profit"))).data or []
    agg = {}
    for r in rounds:
        g = r["game_type"]
        a = agg.setdefault(g, {"count": 0, "bets": 0.0, "ggr": 0.0})
        a["count"] += 1; a["bets"] += float(r["bet_amount"]); a["ggr"] -= float(r["profit"])
    lines = [f"<b>{g}</b>: {a['count']} · GGR {a['ggr']:+.2f} · RTP {(a['bets']-a['ggr'])/a['bets']*100 if a['bets'] else 0:.1f}%"
             for g, a in sorted(agg.items(), key=lambda x: -x[1]["ggr"])]
    await message.answer("<b>🎲 По играм</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("atop"))
async def cmd_atop(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(days=30)).isoformat()
    r = await sb(supabase.table("game_rounds").select("user_id, profit, profiles(telegram_id, first_name)")
                 .gte("created_at", since))
    agg = {}
    for row in r.data or []:
        uid = row["user_id"]; pr = row.get("profiles") or {}
        a = agg.setdefault(uid, {"name": pr.get("first_name") or str(pr.get("telegram_id")), "profit": 0.0})
        a["profit"] += float(row["profit"])
    items = sorted(agg.items(), key=lambda x: -x[1]["profit"])[:15]
    lines = [f"{i+1}. <b>{a['name']}</b> {a['profit']:+.2f}" for i, (u, a) in enumerate(items)]
    await message.answer("<b>🏆 30д</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("atopdep"))
async def cmd_atopdep(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(days=30)).isoformat()
    r = await sb(supabase.table("transactions").select("user_id, amount, profiles(first_name)")
                 .eq("type", "deposit").eq("status", "completed").gte("created_at", since))
    agg = {}
    for row in r.data or []:
        uid = row["user_id"]; pr = row.get("profiles") or {}
        a = agg.setdefault(uid, {"name": pr.get("first_name") or uid[:8], "sum": 0.0})
        a["sum"] += float(row["amount"])
    items = sorted(agg.items(), key=lambda x: -x[1]["sum"])[:15]
    lines = [f"{i+1}. <b>{a['name']}</b> {a['sum']:.2f}" for i, (u, a) in enumerate(items)]
    await message.answer("<b>💎 Топ деп (30д)</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("atopwd"))
async def cmd_atopwd(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(days=30)).isoformat()
    r = await sb(supabase.table("transactions").select("user_id, amount, profiles(first_name)")
                 .eq("type", "withdraw").eq("status", "completed").gte("created_at", since))
    agg = {}
    for row in r.data or []:
        uid = row["user_id"]; pr = row.get("profiles") or {}
        a = agg.setdefault(uid, {"name": pr.get("first_name") or uid[:8], "sum": 0.0})
        a["sum"] += float(row["amount"])
    items = sorted(agg.items(), key=lambda x: -x[1]["sum"])[:15]
    lines = [f"{i+1}. <b>{a['name']}</b> {a['sum']:.2f}" for i, (u, a) in enumerate(items)]
    await message.answer("<b>📤 Топ вывод (30д)</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("arp"))
async def cmd_arp(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"📊 RTP общий: <b>{100-HOUSE_EDGE*100:.2f}%</b>\n\n"
        f"🎲 Дуэль · 💥 Crash · 💎 Mines · 🎡 Roulette\n"
        f"🎲 Dice · 🃏 BJ · 🎰 Plinko · 🗼 Tower · 🎯 Keno · 🃏 Hi-Lo · 🎟 Scratch",
        parse_mode="HTML")

@dp.message(Command("atx"))
async def cmd_atx(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    r = await sb(supabase.table("transactions").select("*").eq("user_id", p["id"])
                 .order("created_at", desc=True).limit(20))
    lines = [f"• {x['created_at'][:16]} {x['type']} {float(x['amount']):.2f} {x['status']}" for x in r.data or []]
    await message.answer("<b>💸 Транзы</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("atxlast"))
async def cmd_atxlast(message: Message, command: CommandObject):
    if not admin_only(message): return
    n = 20
    if command.args:
        try: n = min(50, int(command.args))
        except: pass
    r = await sb(supabase.table("transactions").select("*").order("created_at", desc=True).limit(n))
    lines = [f"• {x['created_at'][:16]} {x['type']} {float(x['amount']):.2f}" for x in r.data or []]
    await message.answer("<b>💸 Последние</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("arefund"))
async def cmd_arefund(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/arefund <tx_id>")
    r = await sb(supabase.table("transactions").select("*").eq("id", command.args.strip()))
    if not r.data: return await message.answer("Нет")
    tx = r.data[0]
    amt = float(tx["amount"])
    refund = -amt if tx["type"] in ("deposit", "win", "bonus", "ref_reward") else amt
    await sb_rpc("change_balance", {"p_user_id": tx["user_id"], "p_delta": refund})
    await message.answer(f"✅ {abs(refund):.2f}")

# ================== PROMO ADMIN ==================
@dp.message(Command("anewpromo"))
async def cmd_anewpromo(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) < 2:
        return await message.answer(
            "<code>/anewpromo CODE AMOUNT [WAGER] [USES] [MAX_BET] [GAMES]</code>",
            parse_mode="HTML")
    code = parts[0].upper().strip()
    try: amount = float(parts[1].replace(",", "."))
    except: return await message.answer("Сумма числом")
    wager = 0.0
    if len(parts) >= 3:
        try: wager = float(parts[2].replace(",", ".").rstrip("xX"))
        except: pass
    max_uses = None
    if len(parts) >= 4:
        try: max_uses = int(parts[3])
        except: pass
    max_bet = None
    if len(parts) >= 5:
        try: max_bet = float(parts[4].replace(",", "."))
        except: pass
    allowed_games = None
    if len(parts) >= 6:
        g = parts[5].lower()
        if g == "all": allowed_games = None
        elif g == "none": allowed_games = []
        else: allowed_games = [x.strip() for x in g.split(",") if x.strip()]
    try:
        await sb(supabase.table("promo_codes").insert({
            "code": code, "amount": amount, "wager_mult": wager,
            "max_uses": max_uses, "max_bet": max_bet,
            "allowed_games": allowed_games, "created_by": message.from_user.id}))
        await message.answer(f"✅ {code} создан")
    except Exception as e:
        await message.answer(f"❌ {e}")

@dp.message(Command("alistpromos"))
async def cmd_alistpromos(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("promo_codes").select("*").order("created_at", desc=True).limit(20))
    if not r.data: return await message.answer("Нет")
    lines = []
    for p in r.data:
        uses = f"{p['uses']}/{p['max_uses']}" if p['max_uses'] else f"{p['uses']}/∞"
        w = p.get("wager_mult") or 0
        lines.append(f"• <code>{p['code']}</code> {float(p['amount']):.2f}₮ ×{w} · {uses}")
    await message.answer("<b>🎟</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("adelpromo"))
async def cmd_adelpromo(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/adelpromo CODE")
    await sb(supabase.table("promo_codes").delete().eq("code", command.args.upper()))
    await message.answer("✅")

@dp.message(Command("adelallpromos"))
async def cmd_adelallpromos(message: Message):
    if not admin_only(message): return
    await sb(supabase.table("promo_codes").delete().neq("code", "__none__"))
    await message.answer("✅")

@dp.message(Command("apromoinfo"))
async def cmd_apromoinfo(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/apromoinfo CODE")
    code = command.args.strip().upper()
    r = await sb(supabase.table("promo_codes").select("*").eq("code", code))
    if not r.data: return await message.answer("Нет")
    p = r.data[0]
    uses = await sb(supabase.table("promo_uses").select("user_id, amount").eq("code", code))
    lines = [f"• {str(u['user_id'])[:8]} — {float(u['amount']):.2f}" for u in uses.data or []]
    w = float(p.get("wager_mult") or 0)
    ag = p.get("allowed_games")
    games_txt = "все" if ag is None else ("нет" if ag == [] else ", ".join(ag))
    await message.answer(
        f"<b>🎟 {code}</b>\nБонус {float(p['amount']):.2f}₮ · ×{w}\n"
        f"Макс.ставка {p.get('max_bet') or '—'} · Игры: {games_txt}\n"
        f"Использований {p['uses']}/{p['max_uses'] or '∞'}\n\n"
        + ("\n".join(lines) if lines else "—"), parse_mode="HTML")

@dp.message(Command("apromogames"))
async def cmd_apromogames(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2: return await message.answer("/apromogames CODE all|none|games")
    code = parts[0].upper(); val = parts[1].lower()
    if val == "all": nv, lbl = None, "все"
    elif val == "none": nv, lbl = [], "нет"
    else: nv, lbl = [x.strip() for x in val.split(",") if x.strip()], val
    await sb(supabase.table("promo_codes").update({"allowed_games": nv}).eq("code", code))
    await message.answer(f"✅ {code} → {lbl}")

@dp.message(Command("asetbonusgames"))
async def cmd_asetbonusgames(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2: return await message.answer("/asetbonusgames ID all|none|games")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    val = parts[1].lower()
    if val == "all": nv = None
    elif val == "none": nv = []
    else: nv = [x.strip() for x in val.split(",") if x.strip()]
    await sb(supabase.table("profiles").update({"bonus_allowed_games": nv}).eq("id", p["id"]))
    await message.answer("✅")

@dp.message(Command("awager"))
async def cmd_awager(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    if not p.get("bonus_active"): return await message.answer("Нет бонуса")
    req = float(p.get("wager_required") or 0); prog = float(p.get("wager_progress") or 0)
    await message.answer(f"🎰 {prog:.2f}/{req:.2f} ({prog/req*100 if req else 0:.1f}%)")

@dp.message(Command("aresetwager"))
async def cmd_aresetwager(message: Message, command: CommandObject):
    if not admin_only(message): return
    p = await admin_get_user(message, command.args or "")
    if not p: return await message.answer("Не найден")
    await sb(supabase.table("profiles").update({
        "bonus_active": False, "wager_required": 0, "wager_progress": 0,
        "bonus_amount": 0, "bonus_code": None, "bonus_max_bet": None,
        "bonus_allowed_games": None}).eq("id", p["id"]))
    await message.answer("✅")

# ================== SETTINGS ==================
@dp.message(Command("asettings"))
async def cmd_asettings(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"<b>⚙️</b>\nBet {MIN_BET}-{MAX_BET} · Деп {MIN_DEPOSIT} · Вывод {MIN_WITHDRAW}\n"
        f"Лимит/сут {MAX_WITHDRAW_DAILY} · Кулдаун {WITHDRAW_COOLDOWN_MIN}м\n"
        f"HE {HOUSE_EDGE} · RTP {(1-HOUSE_EDGE)*100:.1f}% · Ref {REFERRAL_SHARE}\n"
        f"Daily {DAILY_BONUS}₮/{BONUS_COOLDOWN_H}ч\n"
        f"Antifraud {'✅' if ANTIFRAUD_ENABLED else '❌'} порог {AUTO_FLAG_SCORE}\n"
        f"Maint {'ON' if MAINTENANCE else 'OFF'}\n"
        f"Канал: {CHANNEL_ID or '— не задан —'}", parse_mode="HTML")

@dp.message(Command("asetminbet"))
async def cmd_asetminbet(message: Message, command: CommandObject):
    global MIN_BET
    if not admin_only(message): return
    try: MIN_BET = float(command.args); await message.answer(f"✅ {MIN_BET}")
    except: await message.answer("/asetminbet 0.1")

@dp.message(Command("asetmaxbet"))
async def cmd_asetmaxbet(message: Message, command: CommandObject):
    global MAX_BET
    if not admin_only(message): return
    try: MAX_BET = float(command.args); await message.answer(f"✅ {MAX_BET}")
    except: await message.answer("/asetmaxbet 1000")

@dp.message(Command("asetmindep"))
async def cmd_asetmindep(message: Message, command: CommandObject):
    global MIN_DEPOSIT
    if not admin_only(message): return
    try: MIN_DEPOSIT = float(command.args); await message.answer(f"✅ {MIN_DEPOSIT}")
    except: await message.answer("/asetmindep 0.1")

@dp.message(Command("asetminwd"))
async def cmd_asetminwd(message: Message, command: CommandObject):
    global MIN_WITHDRAW
    if not admin_only(message): return
    try: MIN_WITHDRAW = float(command.args); await message.answer(f"✅ {MIN_WITHDRAW}")
    except: await message.answer("/asetminwd 0.5")

@dp.message(Command("asetmaxwd"))
async def cmd_asetmaxwd(message: Message, command: CommandObject):
    global MAX_WITHDRAW_DAILY
    if not admin_only(message): return
    try: MAX_WITHDRAW_DAILY = float(command.args); await message.answer(f"✅ {MAX_WITHDRAW_DAILY}")
    except: await message.answer("/asetmaxwd 500")

@dp.message(Command("asetrtp"))
async def cmd_asetrtp(message: Message, command: CommandObject):
    global HOUSE_EDGE, DICE_PAYOUT, ROUL_RB_PAYOUT, ROUL_DOZEN_PAYOUT, ROUL_NUM_PAYOUT, DUEL_PAYOUT
    if not admin_only(message): return
    try: rtp = float(command.args)
    except: return await message.answer("/asetrtp 0.96")
    if not (0.90 <= rtp <= 0.99): return await message.answer("0.90-0.99")
    HOUSE_EDGE = round(1 - rtp, 4)
    DICE_PAYOUT = round(6 * (1 - HOUSE_EDGE), 4)
    ROUL_RB_PAYOUT = round(2 * (1 - HOUSE_EDGE), 4)
    ROUL_DOZEN_PAYOUT = round(3 * (1 - HOUSE_EDGE), 4)
    ROUL_NUM_PAYOUT = round(36 * (1 - HOUSE_EDGE), 4)
    DUEL_PAYOUT = round(2 * (1 - HOUSE_EDGE), 4)
    await message.answer(f"✅ RTP = {rtp*100:.1f}%\nDuel payout ×{DUEL_PAYOUT}")

@dp.message(Command("asetref"))
async def cmd_asetref(message: Message, command: CommandObject):
    global REFERRAL_SHARE
    if not admin_only(message): return
    try: v = float(command.args); REFERRAL_SHARE = v; await message.answer(f"✅ {v*100:.1f}%")
    except: await message.answer("/asetref 0.05")

@dp.message(Command("asetcooldown"))
async def cmd_asetcooldown(message: Message, command: CommandObject):
    global WITHDRAW_COOLDOWN_MIN
    if not admin_only(message): return
    try: WITHDRAW_COOLDOWN_MIN = int(command.args); await message.answer(f"✅ {WITHDRAW_COOLDOWN_MIN}")
    except: await message.answer("/asetcooldown 15")

@dp.message(Command("amaintenance"))
async def cmd_amaintenance(message: Message, command: CommandObject):
    global MAINTENANCE
    if not admin_only(message): return
    v = (command.args or "").strip().lower()
    MAINTENANCE = v in ("on", "1", "true", "yes")
    await message.answer(f"✅ Maint {'ON' if MAINTENANCE else 'OFF'}")

@dp.message(Command("ahealth"))
async def cmd_ahealth(message: Message):
    if not admin_only(message): return
    try:
        await sb(supabase.table("profiles").select("id").limit(1)); sb_st = "✅"
    except Exception as e: sb_st = f"❌ {type(e).__name__}"
    try:
        async with httpx.AsyncClient(timeout=8) as http:
            rr = await http.get(f"{XROCKET_API_BASE}/api/v1/me",
                                headers={"Authorization": f"Bearer {XROCKET_API_KEY}"})
            xr_st = f"✅ {rr.status_code}" if rr.status_code < 500 else f"⚠️ {rr.status_code}"
    except Exception as e: xr_st = f"❌ {type(e).__name__}"
    active = len((await sb(supabase.table("active_rounds").select("user_id"))).data or [])
    enabled = sum(1 for v in GAMES_ENABLED.values() if v)
    await message.answer(
        f"<b>🩺</b>\nSupabase: {sb_st}\nXroket: {xr_st}\nCrash: {crash_state['status']}\n"
        f"Активных игр: {active}\nИгр вкл: {enabled}/{len(GAMES_ENABLED)}\n"
        f"Канал: {CHANNEL_ID or '— не задан —'}\n"
        f"Maint: {'ON' if MAINTENANCE else 'OFF'}\nUptime: {int(time.time()-START_TIME)}s",
        parse_mode="HTML")

@dp.message(Command("alogs"))
async def cmd_alogs(message: Message, command: CommandObject):
    if not admin_only(message): return
    n = 20
    if command.args:
        try: n = min(100, int(command.args))
        except: pass
    r = await sb(supabase.table("action_log").select("*").order("created_at", desc=True).limit(n))
    lines = [f"• {x['created_at'][:16]} {x['action']}" for x in r.data or []]
    await message.answer("<b>📋 Логи</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("aclearlogs"))
async def cmd_aclearlogs(message: Message, command: CommandObject):
    if not admin_only(message): return
    days = 7
    if command.args:
        try: days = int(command.args)
        except: pass
    cutoff = (datetime.now(timezone.utc) - timedelta(days=days)).isoformat()
    await sb(supabase.table("action_log").delete().lt("created_at", cutoff))
    await message.answer(f"✅ >{days}д")

@dp.message(Command("aadmins"))
async def cmd_aadmins(message: Message):
    if not admin_only(message): return
    lines = [f"• <code>{aid}</code>" for aid in sorted(ADMIN_IDS)]
    await message.answer("<b>🛡</b>\n" + "\n".join(lines), parse_mode="HTML")

# ================== BROADCAST ==================
@dp.message(Command("abroadcast"))
async def cmd_abroadcast(message: Message, command: CommandObject, state: FSMContext):
    if not admin_only(message): return
    if not command.args:
        await state.set_state(AdminInput.broadcast)
        return await message.answer("✍️ текст или /cancel")
    await do_broadcast(message, command.args)

@dp.message(Command("cancel"))
async def cmd_cancel(message: Message, state: FSMContext):
    await state.clear(); await message.answer("Отменено")

@dp.message(AdminInput.broadcast)
async def fsm_broadcast(message: Message, state: FSMContext):
    if not admin_only(message): return
    await state.clear()
    await do_broadcast(message, message.text or "")

async def do_broadcast(message: Message, text: str):
    text = (text or "").strip()
    if not text: return await message.answer("Пусто")
    users = (await sb(supabase.table("profiles").select("telegram_id"))).data or []
    await message.answer(f"📢 {len(users)}…")
    ok = 0
    for u in users:
        try: await bot.send_message(int(u["telegram_id"]), text); ok += 1
        except: pass
        await asyncio.sleep(0.05)
    await message.answer(f"✅ {ok}")

@dp.message(Command("apush"))
async def cmd_apush(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2: return await message.answer("/apush <id> <text>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    try:
        await bot.send_message(p["telegram_id"], f"📢 {parts[1]}")
        await message.answer("✅")
    except Exception as e: await message.answer(f"❌ {e}")

# ================== USER COMMANDS ==================
@dp.message(Command("start"))
async def cmd_start(message: Message, command: CommandObject, state: FSMContext):
    if not await is_subscribed(message.from_user.id, skip_cache=True):
        return await send_sub_prompt(message)
    await state.clear()
    p = await get_or_create_profile(message.from_user.model_dump())
    if command.args and command.args.startswith("ref_") and not p.get("referrer_id"):
        try: ref_tg = int(command.args[4:])
        except: ref_tg = None
        if ref_tg and ref_tg != message.from_user.id:
            ref = await get_profile_by_tg(ref_tg)
            if ref:
                await sb(supabase.table("profiles").update({"referrer_id": ref["id"]}).eq("id", p["id"]))
                try: await bot.send_message(ref_tg, f"👥 Новый реферал: <b>{message.from_user.first_name}</b>", parse_mode="HTML")
                except: pass
    p = await get_or_create_profile(message.from_user.model_dump())
    extra = "\n\n🔐 /admin" if is_admin(message.from_user.id) else ""
    bonus_line = f"\n🎁 Daily {DAILY_BONUS}₮" if DAILY_BONUS > 0 else ""
    cur = p.get("preferred_currency") or "USDT"
    await message.answer(
        f"👋 <b>GoldCash!</b>\n\n💎 Баланс: <b>{float(p['balance']):.2f} {cur}</b>{bonus_line}\n\n"
        f"🎲 Дуэль с ботом · 🌐 Mini App (Mines, Roulette, Plinko, Blackjack, Tower, Crash, Keno, Hi-Lo, Scratch)\n"
        f"💰 Пополнение / вывод через @xRocket\n👥 Друзья: {REFERRAL_SHARE*100:.0f}%\n\n"
        f"/help{extra}",
        reply_markup=main_menu(), parse_mode="HTML")

@dp.callback_query(F.data == "check_sub")
async def cb_check_sub(cb: CallbackQuery, state: FSMContext):
    await cb.answer("⏳ Проверяю…")
    await asyncio.sleep(1.0)
    ok = await is_subscribed(cb.from_user.id, skip_cache=True)
    if not ok:
        return await cb.answer(
            "❌ Ты ещё не подписан на канал\n\n"
            "1. Подпишись по кнопке выше\n"
            "2. Подожди 10 сек\n"
            "3. Нажми «Я подписался» снова",
            show_alert=True)
    _sub_cache[cb.from_user.id] = (True, time.time())
    try: await cb.message.delete()
    except: pass
    await state.clear()
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    await cb.message.answer(
        f"✅ <b>Подписка подтверждена!</b>\n\n"
        f"💎 Баланс: <b>{float(p['balance']):.2f} {cur}</b>\n\n"
        f"Команды: /help",
        reply_markup=main_menu(), parse_mode="HTML")

@dp.message(Command("help"))
async def cmd_help(message: Message):
    await message.answer(
        "📖 <b>GoldCash</b>\n"
        "🎲 Дуэль с ботом: 1-3 куба · обычная или 🌀 Крэзи · до 1/2/3 очков\n"
        "🌐 Mini App: Mines, Roulette, Plinko, Blackjack, Tower, Crash, Keno, Hi-Lo, Scratch\n"
        f"💰 Мин.вывод {MIN_WITHDRAW}₮ · Кулдаун {WITHDRAW_COOLDOWN_MIN}м · Лимит {MAX_WITHDRAW_DAILY}/сутки\n"
        f"👥 Рефералка {REFERRAL_SHARE*100:.0f}%\n"
        "💎 VIP-уровни с рейкбеком!\n\n"
        "/balance · /stats · /currency · /promo КОД · /bonus · /vip",
        parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("balance"))
async def cmd_balance(message: Message):
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"; v = vip_info(p)
    bonus = ""
    if p.get("bonus_active"):
        bonus = (f"\n🎰 Бонус: {float(p.get('wager_progress') or 0):.2f}"
                 f"/{float(p.get('wager_required') or 0):.2f}")
    await message.answer(
        f"💎 Баланс: <b>{float(p['balance']):.2f} {cur}</b>{bonus}\n"
        f"{v['tier_name']} · рейкбек {v['rakeback']*100:.1f}%",
        parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("vip"))
async def cmd_vip(message: Message):
    p = await get_or_create_profile(message.from_user.model_dump())
    v = vip_info(p)
    txt = (f"👑 <b>VIP-программа</b>\n\nТвой уровень: <b>{v['tier_name']}</b>\n"
           f"Оборот: <b>{v['total_wagered']:.2f} ₮</b>\n"
           f"Рейкбек: <b>{v['rakeback']*100:.1f}%</b> (заработано {v['rakeback_earned']:.2f} ₮)\n"
           f"Макс.ставка ×{v['max_bet_mult']:.0f}\n\n")
    if v["next_tier_name"]:
        left = v["next_tier_at"] - v["total_wagered"]
        txt += f"До <b>{v['next_tier_name']}</b>: {left:.2f} ₮\n\n"
    txt += "<b>Все уровни:</b>\n"
    for t in VIP_TIERS:
        marker = "▶️" if t["id"] == v["tier"] else "  "
        txt += f"{marker} {t['name']} — от {t['wagered']} ₮ · рейкбек {t['rakeback']*100:.1f}%\n"
    await message.answer(txt, parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("stats"))
async def cmd_stats(message: Message):
    p = await get_or_create_profile(message.from_user.model_dump())
    s = await get_user_stats(p["id"]); v = vip_info(p)
    await message.answer(fmt_stats(s, float(p["balance"]), message.from_user.first_name, v),
                         parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("promo"))
async def cmd_promo(message: Message, command: CommandObject):
    if not command.args: return await message.answer("/promo КОД")
    await try_redeem_promo(message, command.args.strip().upper())

@dp.message(Command("currency"))
async def cmd_currency(message: Message, command: CommandObject):
    if not command.args:
        return await message.answer(f"Валюты: {', '.join(SUPPORTED_CURRENCIES)}")
    cur = command.args.strip().upper()
    if cur not in SUPPORTED_CURRENCIES: return await message.answer("❌")
    p = await get_or_create_profile(message.from_user.model_dump())
    await sb(supabase.table("profiles").update({"preferred_currency": cur}).eq("id", p["id"]))
    await message.answer(f"✅ {cur}", reply_markup=back_kb())

@dp.message(Command("bonus"))
async def cmd_bonus(message: Message):
    if DAILY_BONUS <= 0: return await message.answer("Отключён")
    p = await get_or_create_profile(message.from_user.model_dump())
    last = p.get("last_bonus_at")
    if last:
        try:
            dt = datetime.fromisoformat(str(last).replace("Z", "+00:00"))
            left = BONUS_COOLDOWN_H * 3600 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0:
                return await message.answer(f"⏳ {int(left//60)} мин")
        except: pass
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": DAILY_BONUS})
    await sb(supabase.table("profiles").update(
        {"last_bonus_at": datetime.now(timezone.utc).isoformat()}).eq("id", p["id"]))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": DAILY_BONUS,
        "currency": "USDT", "status": "completed", "meta": {"source": "daily"}}))
    await message.answer(f"🎁 +{DAILY_BONUS}", reply_markup=back_kb())

async def try_redeem_promo(message: Message, code: str):
    p = await get_or_create_profile(message.from_user.model_dump())
    if p.get("bonus_active"):
        return await message.answer("🎰 Сначала отыграй текущий бонус")
    r = await sb(supabase.table("promo_codes").select("*").eq("code", code))
    if not r.data: return await message.answer("❌ не найден")
    promo = r.data[0]
    if promo.get("max_uses") and promo["uses"] >= promo["max_uses"]:
        return await message.answer("❌ исчерпан")
    used = await sb(supabase.table("promo_uses").select("id").eq("code", code).eq("user_id", p["id"]))
    if used.data: return await message.answer("❌ уже использовал")
    amount = float(promo["amount"])
    wager_mult = float(promo.get("wager_mult") or 0)
    wager_required = round(amount * wager_mult, 8) if wager_mult > 0 else 0
    max_bet = promo.get("max_bet")
    allowed = promo.get("allowed_games")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    await sb(supabase.table("profiles").update({
        "bonus_active": wager_required > 0, "bonus_amount": amount,
        "wager_required": wager_required, "wager_progress": 0,
        "bonus_code": code, "bonus_max_bet": float(max_bet) if max_bet else None,
        "bonus_allowed_games": allowed}).eq("id", p["id"]))
    await sb(supabase.table("promo_uses").insert({"code": code, "user_id": p["id"], "amount": amount}))
    await sb(supabase.table("promo_codes").update({"uses": promo["uses"] + 1}).eq("code", code))
    txt = f"✅ +{amount}₮"
    if wager_required > 0: txt += f"\n🎰 Вейджер ×{wager_mult} ({wager_required:.2f}₮)"
    await message.answer(txt)

# ================== MENU CALLBACKS ==================
@dp.callback_query(F.data == "menu:main")
async def cb_menu(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await cb.message.edit_text("🏠", reply_markup=main_menu())

@dp.callback_query(F.data == "menu:help")
async def cb_help(cb: CallbackQuery):
    await cb.message.edit_text("📖 Справка:\n/help", reply_markup=back_kb())

@dp.callback_query(F.data == "menu:stats")
async def cb_stats(cb: CallbackQuery):
    p = await get_or_create_profile(cb.from_user.model_dump())
    s = await get_user_stats(p["id"]); v = vip_info(p)
    await cb.message.edit_text(fmt_stats(s, float(p["balance"]), cb.from_user.first_name, v),
                               parse_mode="HTML", reply_markup=back_kb())

@dp.callback_query(F.data == "menu:deposit")
async def cb_deposit(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    await cb.message.edit_text(f"💰 Пополнение ({cur})\nМин: {MIN_DEPOSIT}", reply_markup=deposit_kb())

@dp.callback_query(F.data.startswith("dep:"))
async def cb_dep_amount(cb: CallbackQuery, state: FSMContext):
    val = cb.data.split(":")[1]
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if val == "custom":
        await state.set_state(AmountInput.deposit)
        await cb.message.edit_text(f"💰 Сумма ({cur}, мин {MIN_DEPOSIT}):",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="⬅️", callback_data="menu:deposit")]]))
        return
    amount = float(val)
    try: inv = await create_deposit_invoice(p, amount, cur)
    except Exception as e: return await cb.answer(f"❌ {e}", show_alert=True)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💳 Оплатить", url=inv["link"])],
        [InlineKeyboardButton(text="🏠", callback_data="menu:main")]])
    await cb.message.edit_text(f"💰 Счёт {amount} {cur}", reply_markup=kb)

@dp.callback_query(F.data == "menu:withdraw")
async def cb_withdraw(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    p = await get_or_create_profile(cb.from_user.model_dump())
    bal = float(p["balance"]); cur = p.get("preferred_currency") or "USDT"
    spent = await daily_withdrawn(p["id"]); left = MAX_WITHDRAW_DAILY - spent
    warn = ""
    if p.get("bonus_active"):
        req = float(p.get("wager_required") or 0); prog = float(p.get("wager_progress") or 0)
        if prog < req: warn = f"\n🎰 Отыграй ещё {req-prog:.2f}₮"
    await cb.message.edit_text(
        f"💸 Вывод ({cur})\nБаланс: {bal:.2f}\nЛимит/сутки: {max(0,left):.2f}/{MAX_WITHDRAW_DAILY}\n"
        f"Минимум: {MIN_WITHDRAW}{warn}\n\n⚠️ На @xRocket\nВыбери сумму:",
        parse_mode="HTML", reply_markup=withdraw_kb(bal))

@dp.callback_query(F.data.startswith("wd:"))
async def cb_wd_amount(cb: CallbackQuery, state: FSMContext):
    val = cb.data.split(":")[1]
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if val == "custom":
        await state.set_state(AmountInput.withdraw)
        await cb.message.edit_text(f"💸 Сумма ({cur}, мин {MIN_WITHDRAW}):",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="⬅️", callback_data="menu:withdraw")]]))
        return
    amount = float(val)
    if amount < MIN_WITHDRAW: return await cb.answer(f"Мин {MIN_WITHDRAW}", show_alert=True)
    if float(p["balance"]) < amount: return await cb.answer("Мало", show_alert=True)
    await check_and_reset_wager_if_broke(p["id"])
    p = await get_or_create_profile(cb.from_user.model_dump())
    try: await check_wager_lock(p)
    except HTTPException as e: return await cb.answer(e.detail, show_alert=True)
    await cb.message.edit_text("⏳…", reply_markup=back_kb())
    try: await do_withdraw(p, cb.from_user.id, amount, cur)
    except HTTPException as e: return await cb.message.edit_text(f"❌ {e.detail}", reply_markup=back_kb())
    except Exception as e: return await cb.message.edit_text(f"❌ {e}", reply_markup=back_kb())
    await cb.message.edit_text(f"✅ {amount} {cur}", reply_markup=back_kb())

@dp.message(AmountInput.deposit)
async def fsm_deposit_amount(message: Message, state: FSMContext):
    try: amount = float(message.text.replace(",", ".").strip())
    except: return await message.answer("❌")
    if amount < MIN_DEPOSIT or amount > MAX_DEPOSIT: return await message.answer("❌")
    await state.clear()
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    try: inv = await create_deposit_invoice(p, amount, cur)
    except Exception as e: return await message.answer(f"❌ {e}")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💳 Оплатить", url=inv["link"])],
        [InlineKeyboardButton(text="🏠", callback_data="menu:main")]])
    await message.answer(f"💰 Счёт {amount} {cur}", reply_markup=kb)

@dp.message(AmountInput.withdraw)
async def fsm_withdraw_amount(message: Message, state: FSMContext):
    try: amount = float(message.text.replace(",", ".").strip())
    except: return await message.answer("❌")
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if amount < MIN_WITHDRAW or float(p["balance"]) < amount: return await message.answer("❌")
    await check_and_reset_wager_if_broke(p["id"])
    p = await get_or_create_profile(message.from_user.model_dump())
    try: await check_wager_lock(p)
    except HTTPException as e: return await message.answer(f"❌ {e.detail}")
    await state.clear()
    msg = await message.answer("⏳…")
    try: await do_withdraw(p, message.from_user.id, amount, cur)
    except HTTPException as e: return await msg.edit_text(f"❌ {e.detail}")
    except Exception as e: return await msg.edit_text(f"❌ {e}")
    await msg.edit_text(f"✅ {amount} {cur}")

def deposit_kb():
    amounts = [1, 5, 10, 25, 50, 100]
    rows = [[InlineKeyboardButton(text=f"{a} ₮", callback_data=f"dep:{a}") for a in amounts[i:i+3]]
            for i in range(0, len(amounts), 3)]
    rows.append([InlineKeyboardButton(text="✏️ Своя", callback_data="dep:custom")])
    rows.append([InlineKeyboardButton(text="🏠", callback_data="menu:main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def withdraw_kb(balance):
    cand = [1, 5, 10, 25, 50, 100, 250, 500]
    amounts = [a for a in cand if a <= balance and a >= MIN_WITHDRAW]
    rows = []
    for i in range(0, len(amounts), 3):
        rows.append([InlineKeyboardButton(text=f"{a} ₮", callback_data=f"wd:{a}") for a in amounts[i:i+3]])
    rows.append([InlineKeyboardButton(text="✏️ Своя", callback_data="wd:custom")])
    rows.append([InlineKeyboardButton(text="🏠", callback_data="menu:main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

@dp.callback_query(F.data == "menu:ref")
async def cb_ref_menu(cb: CallbackQuery):
    p = await get_or_create_profile(cb.from_user.model_dump())
    info = referral_info_sync(p)
    share_url = f"https://t.me/share/url?url={info['link']}&text=GoldCash"
    invited = (await sb(supabase.table("profiles").select("first_name, created_at")
                        .eq("referrer_id", p["id"]).limit(50))).data or []
    txt = (f"👥 <b>Друзья</b>\n{REFERRAL_SHARE*100:.0f}% с их проигрыша\n\n"
           f"Приглашено: <b>{len(invited)}</b>\n"
           f"Заработано: <b>{float(p.get('ref_earnings') or 0):.2f}</b>\n\n"
           f"<code>{info['link']}</code>")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📤 Поделиться", url=share_url)],
        [InlineKeyboardButton(text="🏠", callback_data="menu:main")]])
    await cb.message.edit_text(txt, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)

# ================== MIDDLEWARE ==================
dp.message.middleware(SubscriptionMiddleware())
dp.callback_query.middleware(SubscriptionMiddleware())

# ================== FASTAPI ==================
@asynccontextmanager
async def lifespan(app):
    global BOT_USERNAME, BOT_NAME
    me = await bot.get_me()
    BOT_USERNAME = me.username
    BOT_NAME = me.first_name or me.username or "Raika"
    log.info("start · HE=%.3f · admins=%s · bot=@%s name=%s · channel=%s · antifraud=%s",
             HOUSE_EDGE, ADMIN_IDS, BOT_USERNAME, BOT_NAME, CHANNEL_ID or "—", ANTIFRAUD_ENABLED)
    try:
        await sb(supabase.table("crash_rounds").update({"status": "crashed"})
                 .in_("status", ["running", "betting"]))
        await sb(supabase.table("crash_bets").update({"status": "lost"})
                 .eq("status", "active"))
        log.info("cleanup crash rounds done")
    except Exception:
        log.exception("cleanup crash rounds failed")
    task_bot = asyncio.create_task(dp.start_polling(bot))
    task_crash = asyncio.create_task(crash_loop())
    yield
    task_bot.cancel(); task_crash.cancel()
    for t in (task_bot, task_crash):
        try: await t
        except asyncio.CancelledError: pass
    await bot.session.close()

app = FastAPI(lifespan=lifespan)
app.add_middleware(CORSMiddleware, allow_origins=["*"], allow_credentials=False,
                   allow_methods=["*"], allow_headers=["*"])

@app.get("/")
async def root(): return {"status": "ok"}

@app.get("/api/config")
async def config():
    return {
        "min_bet": MIN_BET, "max_bet": MAX_BET, "house_edge": HOUSE_EDGE,
        "min_deposit": MIN_DEPOSIT, "min_withdraw": MIN_WITHDRAW,
        "withdraw_cooldown_min": WITHDRAW_COOLDOWN_MIN, "max_withdraw_daily": MAX_WITHDRAW_DAILY,
        "referral_share": REFERRAL_SHARE, "currencies": SUPPORTED_CURRENCIES,
        "maintenance": MAINTENANCE, "games_enabled": GAMES_ENABLED,
        "channel_url": CHANNEL_URL,
        "daily_bonus": DAILY_BONUS, "bonus_cooldown_h": BONUS_COOLDOWN_H,
        "wager_reset_threshold": WAGER_RESET_THRESHOLD,
        "rtp": round(1 - HOUSE_EDGE, 4),
        "vip_tiers": VIP_TIERS,
        "payouts": {"dice": DICE_PAYOUT, "roulette_rb": ROUL_RB_PAYOUT,
                    "roulette_dozen": ROUL_DOZEN_PAYOUT, "roulette_number": ROUL_NUM_PAYOUT,
                    "plinko": PLINKO_MULTS},
        "duel_payout": DUEL_PAYOUT,
        "duel_bets": DUEL_BETS,
        "scratch_tiers": [{"id":t["id"],"name":t["name"],"bet":t["bet"],
                           "color":t["color"],"max":t["max"]} for t in SCRATCH_TIERS],
        "rakeback_cooldown_min": RAKEBACK_CLAIM_COOLDOWN_MIN,
        "rakeback_min": RAKEBACK_MIN_CLAIM,
        "max_level": MAX_LEVEL,
        "level_rewards": LEVEL_REWARDS,
    }

def _profile_sync(user):
    tg_id = int(user["id"])
    r = supabase.table("profiles").select("*").eq("telegram_id", tg_id).execute()
    p = r.data[0] if r.data else supabase.table("profiles").insert({
        "telegram_id": tg_id, "username": user.get("username"),
        "first_name": user.get("first_name"), "preferred_currency": "USDT"}).execute().data[0]
    try:
        tx = supabase.table("transactions").select("type, amount, status").eq("user_id", p["id"]).execute().data or []
        rounds = supabase.table("game_rounds").select("bet_amount, profit").eq("user_id", p["id"]).execute().data or []
    except Exception: tx, rounds = [], []
    dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    bets = sum(float(rr["bet_amount"]) for rr in rounds)
    profits = sum(float(rr["profit"]) for rr in rounds)
    wins = sum((float(rr["profit"]) + float(rr["bet_amount"])) for rr in rounds if float(rr["profit"]) > 0)
    return {"id": p["id"], "telegram_id": p["telegram_id"], "username": p.get("username"),
            "first_name": p.get("first_name"), "balance": float(p["balance"]),
            "client_seed": p.get("client_seed") or "", "nonce": int(p.get("nonce") or 0),
            "ref_earnings": float(p.get("ref_earnings") or 0),
            "preferred_currency": p.get("preferred_currency") or "USDT",
            "is_banned": bool(p.get("is_banned")),
            "is_admin": is_admin(tg_id),
            "bonus": _bonus_info(p),
            "vip": vip_info(p),
            "level_info": xp_info(p),
            "stats": {"total_games": len(rounds), "total_wagered": round(bets, 2),
                      "total_profit": round(profits, 2),
                      "deposits": round(dep, 2), "withdrawals": round(wd, 2), "wins": round(wins, 2)}}

@app.get("/api/profile")
async def profile(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    asyncio.create_task(check_pending_deposits(p["id"]))
    return await asyncio.to_thread(_profile_sync, user)

@app.get("/api/vip")
async def api_vip(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    return vip_info(p)

@app.post("/api/vip/claim")
async def vip_claim(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    pending = float(p.get("rakeback_pending") or 0)
    if pending < RAKEBACK_MIN_CLAIM:
        raise HTTPException(400, f"минимум для вывода {RAKEBACK_MIN_CLAIM} ₮")
    last = p.get("last_rakeback_at")
    if last:
        try:
            dt = datetime.fromisoformat(str(last).replace("Z", "+00:00"))
            left = RAKEBACK_CLAIM_COOLDOWN_MIN * 60 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0:
                m, s = divmod(int(left), 60)
                raise HTTPException(400, f"забрать можно раз в {RAKEBACK_CLAIM_COOLDOWN_MIN} мин. Подожди {m}м {s}с")
        except HTTPException: raise
        except Exception: pass
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": pending})
    earned = float(p.get("rakeback_earned") or 0) + pending
    await sb(supabase.table("profiles").update({
        "rakeback_pending": 0,
        "rakeback_earned": round(earned, 8),
        "last_rakeback_at": datetime.now(timezone.utc).isoformat(),
    }).eq("id", p["id"]))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": pending,
        "currency": "USDT", "status": "completed",
        "meta": {"source": "rakeback_claim"}}))
    return {"ok": True, "amount": round(pending, 8)}

def _require_admin(user: dict):
    if not is_admin(int(user["id"])):
        raise HTTPException(403, "admin only")

@app.get("/api/admin/promos")
async def admin_promos_list(user: dict = Depends(get_current_user)):
    _require_admin(user)
    r = await sb(supabase.table("promo_codes").select("*").order("created_at", desc=True).limit(100))
    return r.data or []

@app.post("/api/admin/promos")
async def admin_promos_create(body: dict, user: dict = Depends(get_current_user)):
    _require_admin(user)
    code = (body.get("code") or "").strip().upper()
    if not code: raise HTTPException(400, "код пуст")
    try: amount = float(body.get("amount", 0))
    except: raise HTTPException(400, "сумма")
    wager = float(body.get("wager_mult") or 0)
    max_uses = body.get("max_uses") or None
    max_bet = body.get("max_bet") or None
    allowed_games = body.get("allowed_games")
    try:
        if max_uses is not None: max_uses = int(max_uses)
        if max_bet is not None: max_bet = float(max_bet)
    except: raise HTTPException(400, "числа")
    if allowed_games is not None and not isinstance(allowed_games, list):
        raise HTTPException(400, "allowed_games: null / [] / [..]")
    try:
        await sb(supabase.table("promo_codes").insert({
            "code": code, "amount": amount, "wager_mult": wager,
            "max_uses": max_uses, "max_bet": max_bet,
            "allowed_games": allowed_games, "created_by": int(user["id"])}))
    except Exception as e:
        raise HTTPException(400, str(e))
    return {"ok": True, "code": code}

@app.delete("/api/admin/promos/{code}")
async def admin_promos_delete(code: str, user: dict = Depends(get_current_user)):
    _require_admin(user)
    await sb(supabase.table("promo_codes").delete().eq("code", code.upper()))
    return {"ok": True}

@app.get("/api/admin/antifraud")
async def admin_antifraud(user: dict = Depends(get_current_user)):
    _require_admin(user)
    r = await sb(supabase.table("profiles").select(
        "id, telegram_id, first_name, username, risk_score, auto_flagged, flag_reason, last_ip")
        .order("risk_score", desc=True).limit(50))
    return r.data or []

def _live_sync():
    r = supabase.table("game_rounds").select("game_type, profit, bet_amount, profiles(username, first_name)") \
        .gt("profit", 0).order("created_at", desc=True).limit(30).execute()
    out = []
    for row in r.data or []:
        pr = row.get("profiles") or {}
        name = pr.get("first_name") or pr.get("username") or "anon"
        mult = round((float(row["profit"]) + float(row["bet_amount"])) / float(row["bet_amount"]), 2) \
               if float(row["bet_amount"]) else 1.0
        out.append({"game": row["game_type"], "name": name,
                    "profit": round(float(row["profit"]), 2), "mult": mult})
    return out

@app.get("/api/live")
async def live():
    try: return await asyncio.to_thread(_live_sync)
    except Exception: return []

@app.get("/api/leaderboard")
async def leaderboard(period: str = "week"):
    def _run():
        days = {"day": 1, "week": 7, "month": 30}.get(period, 7)
        since = (datetime.now(timezone.utc) - timedelta(days=days)).isoformat()
        r = supabase.table("game_rounds").select("user_id, profit, bet_amount, profiles(username, first_name)") \
            .gte("created_at", since).execute()
        agg = {}
        for row in r.data or []:
            uid = row["user_id"]; pr = row.get("profiles") or {}
            a = agg.setdefault(uid, {"name": pr.get("first_name") or pr.get("username") or "anon",
                                     "profit": 0.0, "bets": 0.0, "games": 0})
            a["profit"] += float(row["profit"]); a["bets"] += float(row["bet_amount"]); a["games"] += 1
        items = [{"uid": k, **v, "profit": round(v["profit"], 2), "bets": round(v["bets"], 2)}
                 for k, v in agg.items()]
        items.sort(key=lambda x: x["profit"], reverse=True)
        return {"period": period, "items": items[:20]}
    try: return await asyncio.to_thread(_run)
    except Exception: return {"period": period, "items": []}

@app.get("/api/referral")
async def api_referral(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    info = referral_info_sync(p)
    invited = (await sb(supabase.table("profiles").select("first_name, username, created_at")
                        .eq("referrer_id", p["id"]).limit(50))).data or []
    info["earnings"] = float(p.get("ref_earnings") or 0)
    info["invited_count"] = len(invited)
    return info

@app.post("/api/promo/redeem")
async def api_promo_redeem(body: dict, user: dict = Depends(get_current_user)):
    code = (body.get("code") or "").strip().upper()
    if not code: raise HTTPException(400, "пустой код")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    if p.get("bonus_active"): raise HTTPException(400, "активный бонус")
    r = await sb(supabase.table("promo_codes").select("*").eq("code", code))
    if not r.data: raise HTTPException(404, "не найден")
    promo = r.data[0]
    if promo.get("max_uses") and promo["uses"] >= promo["max_uses"]: raise HTTPException(400, "исчерпан")
    used = await sb(supabase.table("promo_uses").select("id").eq("code", code).eq("user_id", p["id"]))
    if used.data: raise HTTPException(400, "уже использовал")
    amount = float(promo["amount"])
    wager_mult = float(promo.get("wager_mult") or 0)
    wager_required = round(amount * wager_mult, 8) if wager_mult > 0 else 0
    max_bet = promo.get("max_bet")
    allowed = promo.get("allowed_games")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    await sb(supabase.table("profiles").update({
        "bonus_active": wager_required > 0, "bonus_amount": amount,
        "wager_required": wager_required, "wager_progress": 0,
        "bonus_code": code, "bonus_max_bet": float(max_bet) if max_bet else None,
        "bonus_allowed_games": allowed}).eq("id", p["id"]))
    await sb(supabase.table("promo_uses").insert({"code": code, "user_id": p["id"], "amount": amount}))
    await sb(supabase.table("promo_codes").update({"uses": promo["uses"] + 1}).eq("code", code))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": amount,
        "currency": "USDT", "status": "completed",
        "meta": {"source": "promo", "code": code}}))
    return {"ok": True, "amount": amount, "wager_required": wager_required,
            "wager_mult": wager_mult, "allowed_games": allowed}

@app.get("/api/bonus/daily")
async def bonus_status(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    if DAILY_BONUS <= 0: return {"available": False, "amount": 0, "next_in_sec": 0}
    last = p.get("last_bonus_at")
    if last:
        try:
            dt = datetime.fromisoformat(str(last).replace("Z", "+00:00"))
            left = BONUS_COOLDOWN_H * 3600 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0: return {"available": False, "amount": DAILY_BONUS, "next_in_sec": int(left)}
        except Exception: pass
    return {"available": True, "amount": DAILY_BONUS, "next_in_sec": 0}

@app.post("/api/bonus/daily")
async def bonus_claim(user: dict = Depends(get_current_user)):
    if DAILY_BONUS <= 0: raise HTTPException(400, "off")
    p = await get_or_create_profile(user)
    last = p.get("last_bonus_at")
    if last:
        try:
            dt = datetime.fromisoformat(str(last).replace("Z", "+00:00"))
            left = BONUS_COOLDOWN_H * 3600 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0: raise HTTPException(400, f"{int(left//60)} мин")
        except HTTPException: raise
        except Exception: pass
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": DAILY_BONUS})
    await sb(supabase.table("profiles").update(
        {"last_bonus_at": datetime.now(timezone.utc).isoformat()}).eq("id", p["id"]))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": DAILY_BONUS,
        "currency": "USDT", "status": "completed", "meta": {"source": "daily"}}))
    return {"ok": True, "amount": DAILY_BONUS}

@app.get("/api/history/games")
async def history_games(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    return (await sb(supabase.table("game_rounds").select("*").eq("user_id", p["id"])
                     .order("created_at", desc=True).limit(30))).data or []

@app.get("/api/history/transactions")
async def history_tx(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    return (await sb(supabase.table("transactions").select("*").eq("user_id", p["id"])
                     .order("created_at", desc=True).limit(30))).data or []

@app.get("/api/fairness")
async def fairness(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    r = await sb(supabase.table("game_rounds").select("*").eq("user_id", p["id"])
                 .order("created_at", desc=True).limit(10))
    out = []
    for row in r.data or []:
        ss = row.get("server_seed") or ""
        out.append({"id": row["id"], "game": row["game_type"], "bet": float(row["bet_amount"]),
                    "profit": float(row["profit"]), "result": row["result"], "server_seed": ss,
                    "server_seed_hash": hashlib.sha256(ss.encode()).hexdigest() if ss else "",
                    "client_seed": p["client_seed"], "nonce": row.get("nonce"),
                    "created_at": row["created_at"]})
    return out

@app.post("/api/payments/deposit")
async def api_deposit(body: dict, user: dict = Depends(get_current_user)):
    amount = float(body.get("amount", 0)); currency = (body.get("currency") or "USDT").upper()
    if amount < MIN_DEPOSIT: raise HTTPException(400, f"min {MIN_DEPOSIT}")
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "currency")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "deposit")
    try: inv = await create_deposit_invoice(p, amount, currency)
    except Exception as e:
        log.exception("create_invoice failed"); raise HTTPException(400, str(e))
    return {"link": inv["link"], "invoice_id": inv.get("invoice_id")}

@app.post("/api/payments/withdraw")
async def api_withdraw(body: dict, user: dict = Depends(get_current_user)):
    amount = float(body.get("amount", 0)); currency = (body.get("currency") or "USDT").upper()
    if amount < MIN_WITHDRAW: raise HTTPException(400, f"min {MIN_WITHDRAW}")
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "currency")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "withdraw")
    await check_and_reset_wager_if_broke(p["id"])
    p = await get_or_create_profile(user)
    await check_wager_lock(p)
    if float(p["balance"]) < amount: raise HTTPException(400, "balance")
    try: payout = await do_withdraw(p, user["id"], amount, currency)
    except HTTPException: raise
    except Exception as e:
        log.exception("payout failed"); raise HTTPException(400, str(e))
    return {"ok": True, "payout_id": payout.get("id")}

# ================== WEBHOOK ==================
@app.post("/api/webhook/xrocket")
async def xrocket_webhook(request: Request):
    raw = await request.body()
    sig = request.headers.get("Signature")
    ver = request.headers.get("Signature-Version")
    ts  = request.headers.get("Signature-Timestamp")

    log.info("🔔 WEBHOOK raw=%s headers(sig=%s ver=%s ts=%s)",
             raw[:500], sig, ver, ts)

    if not all([sig, ver, ts]):
        log.warning("webhook missing headers")
        raise HTTPException(401, "missing sig")
    if ver != "v1":
        raise HTTPException(401, "unsupported version")
    try:
        if abs(int(time.time() * 1000) - int(ts)) > 300_000:
            raise HTTPException(401, "timestamp too old")
    except (ValueError, TypeError):
        raise HTTPException(401, "bad ts")

    expected = hmac.new(
        XROCKET_WEBHOOK_SECRET.encode(),
        f"{ts}.{raw.decode()}".encode(),
        hashlib.sha256,
    ).hexdigest()
    if not hmac.compare_digest(expected, sig):
        log.error("webhook BAD SIGNATURE")
        raise HTTPException(401, "bad sig")

    event = json.loads(raw)
    log.info("✅ xRocket webhook verified")

    data_block = event.get("data") or {}
    outer_type = event.get("type")
    inner_event = data_block.get("event") or ""

    invoice = data_block.get("invoice") or {}
    payment = data_block.get("payment") or {}

    cid = invoice.get("clientInvoiceId") or data_block.get("clientInvoiceId")
    invoice_id = invoice.get("id") or data_block.get("invoiceId")
    inv_status = (invoice.get("status") or "").lower()

    log.info("📦 parsed: outer_type=%s inner_event=%s cid=%s invoice_id=%s status=%s",
             outer_type, inner_event, cid, invoice_id, inv_status)

    if outer_type == "invoice" and inner_event == "invoice_status_changed":
        if inv_status in ("paid", "completed", "success"):
            if not cid and not invoice_id:
                log.warning("⚠️ no cid / invoice_id in webhook")
                return {"ok": True}
            tx = []
            if cid:
                tx = (await sb(supabase.table("transactions").select("*")
                               .eq("external_id", str(cid))
                               .eq("status", "pending"))).data or []
            if not tx and invoice_id:
                tx = (await sb(supabase.table("transactions").select("*")
                               .eq("meta->>invoice_id", str(invoice_id))
                               .eq("status", "pending"))).data or []
            if tx:
                row = tx[0]
                claim = await sb(supabase.table("transactions")
                                 .update({"status": "processing"})
                                 .eq("id", row["id"]).eq("status", "pending"))
                if not claim.data:
                    log.info("already claimed: %s", row["id"])
                    return {"ok": True}
                await sb_rpc("change_balance",
                             {"p_user_id": row["user_id"], "p_delta": float(row["amount"])})
                await sb(supabase.table("transactions").update({
                    "status": "completed",
                    "meta": {**(row.get("meta") or {}),
                             "credited_at": datetime.now(timezone.utc).isoformat(),
                             "invoice_id": invoice_id,
                             "source": "webhook"},
                }).eq("id", row["id"]))
                log.info("✅ DEPOSIT CREDITED user=%s amount=%s", row["user_id"], row["amount"])
                try:
                    prof = (await sb(supabase.table("profiles")
                                     .select("first_name, username, telegram_id")
                                     .eq("id", row["user_id"]))).data
                    if prof:
                        pr = prof[0]
                        nm = pr.get("first_name") or pr.get("username") or "anon"
                        for aid in ADMIN_IDS:
                            try:
                                await bot.send_message(
                                    aid,
                                    f"💰 <b>Депозит зачислен</b>\n"
                                    f"👤 {nm} (<code>{pr['telegram_id']}</code>)\n"
                                    f"+{float(row['amount']):.2f} {row.get('currency','USDT')}",
                                    parse_mode="HTML")
                            except: pass
                except: pass
            else:
                log.warning("⚠️ transaction not found: cid=%s invoice_id=%s", cid, invoice_id)

    if outer_type == "payout" or inner_event == "payout_status_changed":
        payout = data_block.get("payout") or {}
        pcid = (payout.get("clientPayoutId")
                or data_block.get("clientPayoutId"))
        pstatus = (payout.get("status") or "").lower()
        if pcid:
            tx = (await sb(supabase.table("transactions").select("*")
                           .eq("external_id", str(pcid)))).data or []
            if tx:
                row = tx[0]
                if pstatus in ("completed", "paid", "success"):
                    await sb(supabase.table("transactions")
                             .update({"status": "completed"}).eq("id", row["id"]))
                    log.info("✅ payout completed: %s", pcid)
                elif pstatus in ("failed", "rejected", "cancelled"):
                    await sb_rpc("change_balance",
                                 {"p_user_id": row["user_id"], "p_delta": float(row["amount"])})
                    await sb(supabase.table("transactions")
                             .update({"status": "failed",
                                      "meta": {"error": (payout.get("reason") or "unknown")}})
                             .eq("id", row["id"]))
                    log.warning("❌ payout failed, refunded: %s", pcid)

    return {"ok": True}

# ================== CRASH API ==================
def _crash_state_sync(p):
    status = crash_state["status"]; mult = 1.0
    if status == "running" and crash_state["started_at"]:
        mult = crash_mult(time.time() - crash_state["started_at"])
    elif status == "crashed": mult = crash_state["crash_point"] or 1.0
    bets = []; my_bet = None; rid = crash_state["round_id"]
    if rid:
        r = supabase.table("crash_bets").select("user_id, username, amount, cashout_mult, payout, status, auto_cashout_mult") \
            .eq("round_id", rid).order("created_at", desc=True).execute()
        for b in r.data or []:
            item = {"user_id": b["user_id"], "username": b.get("username") or "anon",
                    "amount": float(b["amount"]),
                    "cashout_mult": float(b["cashout_mult"]) if b["cashout_mult"] else None,
                    "auto_cashout_mult": float(b["auto_cashout_mult"]) if b.get("auto_cashout_mult") else None,
                    "payout": float(b["payout"] or 0), "status": b["status"],
                    "is_me": b["user_id"] == p["id"]}
            bets.append(item)
            if item["is_me"]: my_bet = item
    recent = supabase.table("crash_rounds").select("crash_point, created_at") \
        .eq("status", "crashed").order("created_at", desc=True).limit(10).execute()
    return {"status": status, "mult": mult,
            "crash_point": crash_state["crash_point"] if status == "crashed" else None,
            "started_at": crash_state["started_at"],
            "betting_ends_in": max(0, (crash_state.get("betting_ends_at") or 0) - time.time()) if status == "betting" else 0,
            "bets": bets, "my_bet": my_bet,
            "recent": [{"crash_point": float(x["crash_point"])} for x in recent.data or []],
            "balance": float(p["balance"]), "round_id": rid}

@app.get("/api/crash/state")
async def crash_state_endpoint(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    return await asyncio.to_thread(_crash_state_sync, p)

@app.post("/api/crash/bet")
async def crash_bet(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("crash")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    if crash_state["status"] != "betting": raise HTTPException(400, "closed")
    bet = float(body.get("bet", 0)); auto = body.get("auto_cashout_mult")
    auto = float(auto) if auto else None
    if auto is not None and (auto < 1.01 or auto > 100): raise HTTPException(400, "auto")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "crash")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    rid = crash_state["round_id"]
    ex = await sb(supabase.table("crash_bets").select("id").eq("round_id", rid).eq("user_id", p["id"]))
    if ex.data: raise HTTPException(400, "dup")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    row = {"round_id": rid, "user_id": p["id"],
           "username": p.get("first_name") or p.get("username") or "anon",
           "amount": bet, "status": "active"}
    if auto is not None: row["auto_cashout_mult"] = auto
    await sb(supabase.table("crash_bets").insert(row))
    return {"ok": True}

@app.post("/api/crash/cashout")
async def crash_cashout(user: dict = Depends(get_current_user)):
    if crash_state["status"] != "running": raise HTTPException(400, "not running")
    mult = crash_mult(time.time() - crash_state["started_at"])
    if mult >= crash_state["crash_point"]: raise HTTPException(400, "late")
    p = await get_or_create_profile(user); await ensure_not_banned(p)
    rid = crash_state["round_id"]
    b = await sb(supabase.table("crash_bets").select("*").eq("round_id", rid).eq("user_id", p["id"]).eq("status", "active"))
    if not b.data: raise HTTPException(400, "no bet")
    bet = b.data[0]; amount = float(bet["amount"])
    payout = round(amount * mult, 8); profit = round(payout - amount, 8)
    await sb(supabase.table("crash_bets").update({
        "status": "cashed", "cashout_mult": mult, "payout": payout,
        "auto_cashout_mult": None}).eq("id", bet["id"]))
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit,
        "currency": "USDT", "status": "completed", "meta": {"game": "crash"}}))
    await log_round(p["id"], "crash", amount, {"mult": mult, "round": rid}, profit, "", 0)
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit}

# ================== CRASH WEBSOCKET ==================
@app.websocket("/ws/crash")
async def ws_crash(websocket: WebSocket):
    await websocket.accept()
    log.info("ws_crash connected: %s", websocket.client)
    try:
        last_state_key = None
        while True:
            status = crash_state["status"]
            rid = crash_state["round_id"]
            key = (status, rid)
            server_time = time.time()
            if key != last_state_key:
                try:
                    recent = await asyncio.to_thread(lambda: supabase.table("crash_rounds")
                        .select("crash_point").eq("status", "crashed")
                        .order("created_at", desc=True).limit(10).execute())
                    recent_list = [{"crash_point": float(x["crash_point"])}
                                   for x in (recent.data or [])]
                except Exception:
                    recent_list = []
                await websocket.send_json({
                    "type": "state", "status": status, "round_id": rid,
                    "started_at": crash_state["started_at"],
                    "betting_ends_at": crash_state.get("betting_ends_at"),
                    "crash_point": crash_state["crash_point"] if status == "crashed" else None,
                    "server_seed": crash_state["server_seed"] if status == "crashed" else None,
                    "server_time": server_time, "recent": recent_list,
                })
                last_state_key = key
            else:
                await websocket.send_json({
                    "type": "tick", "status": status, "server_time": server_time,
                })
            await asyncio.sleep(0.15)
    except WebSocketDisconnect:
        log.info("ws_crash disconnected")
    except Exception:
        log.exception("ws_crash error")
    finally:
        try: await websocket.close()
        except Exception: pass

# ================== DICE ==================
@app.post("/api/games/dice/bet")
async def dice_webapp(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("dice")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    bet = float(body.get("bet", 0)); chosen = int(body.get("chosen", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    if not (1 <= chosen <= 6): raise HTTPException(400, "chosen")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "dice")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    result = dice_result(ss, p["client_seed"], nonce)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    win = (result == chosen); profit = -bet; payout = 0
    if win:
        payout = round(bet * DICE_PAYOUT, 8); profit = round(payout - bet, 8)
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    await log_round(p["id"], "dice", bet, {"result": result, "chosen": chosen, "win": win}, profit, ss, nonce)
    return {"ok": True, "result": result, "win": win, "profit": profit, "payout": payout}

# ================== PLINKO ==================
PLINKO_MULTS = {
    8:  [5.6, 2.1, 1.1, 1.0, 0.5, 1.0, 1.1, 2.1, 5.6],
    12: [10, 3, 1.6, 1.4, 1.1, 1.0, 0.5, 1.0, 1.1, 1.4, 1.6, 3, 10],
    16: [16, 9, 2, 1.4, 1.4, 1.2, 1.1, 1.0, 0.5, 1.0, 1.1, 1.2, 1.4, 1.4, 2, 9, 16],
}

@app.post("/api/games/plinko/drop")
async def plinko_drop(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("plinko")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    bet = float(body.get("bet", 0)); rows = int(body.get("rows", 8))
    if rows not in (8, 12, 16): raise HTTPException(400, "rows")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "plinko")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    idx, path = plinko_path(ss, p["client_seed"], nonce, rows)
    mult = PLINKO_MULTS[rows][idx]
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    if profit < 0:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    await log_round(p["id"], "plinko", bet, {"rows": rows, "slot": idx, "mult": mult}, profit, ss, nonce)
    return {"ok": True, "slot": idx, "mult": mult, "payout": payout, "profit": profit, "rows": rows, "path": path}

# ================== BLACKJACK ==================
@app.get("/api/games/blackjack/state")
async def bj_state(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "blackjack": return {"active": False}
    st = ar["state"]
    return {"active": True, "player": st["player"], "dealer": [st["dealer"][0], "??"],
            "player_value": bj_value(st["player"]),
            "dealer_value": bj_value([st["dealer"][0]]),
            "finished": False, "bet": float(ar["bet_amount"])}

@app.post("/api/games/blackjack/start")
async def bj_start(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("blackjack")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    bet = float(body.get("bet", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "blackjack")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    ar = await get_active_round(p["id"])
    if ar:
        if ar["game_type"] == "blackjack":
            st = ar["state"]
            return {"ok": True, "resumed": True, "player": st["player"],
                    "dealer": [st["dealer"][0], "??"],
                    "player_value": bj_value(st["player"]),
                    "dealer_value": bj_value([st["dealer"][0]]), "finished": False}
        raise HTTPException(400, f"active: {ar['game_type']}")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    deck = bj_deck(ss, p["client_seed"], nonce)
    player = [deck[0], deck[2]]; dealer = [deck[1], deck[3]]; rest = deck[4:]
    player_v = bj_value(player)
    state = {"player": player, "dealer": dealer, "rest": rest, "bet": bet, "status": "player_turn"}
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "blackjack", "bet_amount": bet,
        "state": state, "server_seed": ss, "nonce": nonce}))
    if player_v == 21:
        dealer_full = bj_value(dealer)
        if dealer_full == 21: payout = bet; profit = 0
        else: payout = round(bet * 2.5, 8); profit = round(payout - bet, 8)
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
        await log_round(p["id"], "blackjack", bet, {"bj": True}, profit, ss, nonce)
        await clear_active_round(p["id"])
        return {"ok": True, "player": player, "dealer": dealer,
                "player_value": player_v, "dealer_value": dealer_full,
                "finished": True, "win": profit > 0, "push": profit == 0,
                "profit": profit, "payout": payout}
    return {"ok": True, "player": player, "dealer": [dealer[0], "??"],
            "player_value": player_v, "dealer_value": bj_value([dealer[0]]), "finished": False}

@app.post("/api/games/blackjack/hit")
async def bj_hit(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "blackjack": raise HTTPException(400, "no game")
    st = ar["state"]
    if st["status"] != "player_turn": raise HTTPException(400, "not turn")
    rest = st["rest"]
    if not rest: raise HTTPException(400, "empty deck")
    card = rest.pop(0); st["player"].append(card); st["rest"] = rest
    pv = bj_value(st["player"])
    if pv > 21:
        await log_round(p["id"], "blackjack", float(st["bet"]),
                        {"bust": True}, -float(st["bet"]), ar["server_seed"], ar["nonce"])
        asyncio.create_task(credit_referrer_on_loss(p["id"], float(st["bet"])))
        await clear_active_round(p["id"])
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
        return {"ok": True, "player": st["player"], "dealer": st["dealer"],
                "player_value": pv, "dealer_value": bj_value(st["dealer"]),
                "finished": True, "win": False, "push": False,
                "profit": -float(st["bet"]), "payout": 0}
    await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))
    return {"ok": True, "player": st["player"], "dealer": [st["dealer"][0], "??"],
            "player_value": pv, "dealer_value": bj_value([st["dealer"][0]]), "finished": False}

@app.post("/api/games/blackjack/stand")
async def bj_stand(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "blackjack": raise HTTPException(400, "no game")
    st = ar["state"]
    rest = st["rest"]
    while bj_value(st["dealer"]) < 17 and rest: st["dealer"].append(rest.pop(0))
    pv = bj_value(st["player"]); dv = bj_value(st["dealer"])
    bet = float(st["bet"]); profit = -bet; payout = 0; push = False; win = False
    if dv > 21 or pv > dv:
        win = True; payout = round(bet * 2, 8); profit = round(payout - bet, 8)
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    elif pv == dv:
        push = True; profit = 0; payout = bet
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": bet})
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    await log_round(p["id"], "blackjack", bet, {"win": win, "push": push},
                    profit, ar["server_seed"], ar["nonce"])
    await clear_active_round(p["id"])
    return {"ok": True, "player": st["player"], "dealer": st["dealer"],
            "player_value": pv, "dealer_value": dv,
            "finished": True, "win": win, "push": push,
            "profit": profit, "payout": payout}

# ================== TOWER ==================
@app.get("/api/games/tower/state")
async def tower_state(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "tower": return {"active": False}
    st = ar["state"]
    return {"active": True, "level": st["level"], "mult": tower_mult(st["level"]),
            "next_mult": tower_mult(st["level"] + 1),
            "bet": float(ar["bet_amount"]),
            "revealed": st.get("revealed", []),
            "mine_positions": st["mine_positions"]}

@app.post("/api/games/tower/start")
async def tower_start(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("tower")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    bet = float(body.get("bet", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "tower")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    ar = await get_active_round(p["id"])
    if ar:
        if ar["game_type"] == "tower":
            st = ar["state"]
            return {"ok": True, "resumed": True, "level": st["level"],
                    "mult": tower_mult(st["level"]),
                    "next_mult": tower_mult(st["level"] + 1)}
        raise HTTPException(400, "active")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    positions = tower_step_positions(ss, p["client_seed"], nonce, 6)
    state = {"level": 0, "mine_positions": positions, "bet": bet, "revealed": []}
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "tower", "bet_amount": bet,
        "state": state, "server_seed": ss, "nonce": nonce}))
    return {"ok": True, "level": 0, "mult": 1.0, "next_mult": tower_mult(1)}

@app.post("/api/games/tower/step")
async def tower_step(body: dict, user: dict = Depends(get_current_user)):
    door = int(body.get("door", -1))
    if not (0 <= door <= 2): raise HTTPException(400, "door")
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "tower": raise HTTPException(400, "no game")
    st = ar["state"]
    level = st["level"]
    if level >= len(st["mine_positions"]): raise HTTPException(400, "max")
    mine = st["mine_positions"][level]
    bet = float(st["bet"])
    if door == mine:
        await log_round(p["id"], "tower", bet, {"level": level, "lost": True}, -bet, ar["server_seed"], ar["nonce"])
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        await clear_active_round(p["id"])
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
        return {"ok": True, "lost": True, "mine": mine, "level": level}
    st["level"] = level + 1
    st["revealed"].append({"level": level, "door": door, "mine": mine})
    await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))
    return {"ok": True, "lost": False, "level": st["level"],
            "mult": tower_mult(st["level"]), "next_mult": tower_mult(st["level"] + 1),
            "mine": mine, "all_levels": st["mine_positions"]}

@app.post("/api/games/tower/cashout")
async def tower_cashout(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "tower": raise HTTPException(400, "no game")
    st = ar["state"]
    if st["level"] <= 0: raise HTTPException(400, "no level")
    bet = float(st["bet"]); mult = tower_mult(st["level"])
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await log_round(p["id"], "tower", bet, {"level": st["level"], "mult": mult},
                    profit, ar["server_seed"], ar["nonce"])
    await clear_active_round(p["id"])
    return {"ok": True, "level": st["level"], "mult": mult, "payout": payout, "profit": profit,
            "mine_positions": st["mine_positions"]}

# ================== MINES ==================
@app.post("/api/games/mines/start")
async def mines_start(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("mines")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    bet = float(body.get("bet", 0)); mines = int(body.get("mines", 3))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    if not (1 <= mines <= 24): raise HTTPException(400, "mines")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "mines")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    if await get_active_round(p["id"]): raise HTTPException(400, "active")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    positions = mine_positions(ss, p["client_seed"], nonce, mines)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "mines", "bet_amount": bet,
        "state": {"mines": mines, "positions": positions, "revealed": []},
        "server_seed": ss, "nonce": nonce}))
    return {"ok": True, "mines": mines, "mult": mines_mult(mines, 0)}

@app.post("/api/games/mines/reveal")
async def mines_reveal(body: dict, user: dict = Depends(get_current_user)):
    idx = int(body.get("cell", -1))
    if not (0 <= idx < 25): raise HTTPException(400, "cell")
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "mines": raise HTTPException(400, "no game")
    st = ar["state"]
    if idx in st["revealed"]: raise HTTPException(400, "already")
    positions = set(st["positions"]); bet = float(ar["bet_amount"])
    if idx in positions:
        await log_round(p["id"], "mines", bet, {"mine": idx}, -bet, ar["server_seed"], ar["nonce"])
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        await clear_active_round(p["id"])
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
        return {"ok": True, "lost": True, "mine_hit": idx, "positions": st["positions"]}
    st["revealed"].append(idx)
    await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))
    return {"ok": True, "lost": False, "revealed": st["revealed"],
            "mult": mines_mult(st["mines"], len(st["revealed"]))}

@app.post("/api/games/mines/cashout")
async def mines_cashout(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "mines": raise HTTPException(400, "no game")
    st = ar["state"]; k = len(st["revealed"])
    if k == 0: raise HTTPException(400, "reveal")
    bet = float(ar["bet_amount"]); mult = mines_mult(st["mines"], k)
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await log_round(p["id"], "mines", bet, {"revealed": k, "mult": mult},
                    profit, ar["server_seed"], ar["nonce"])
    await clear_active_round(p["id"])
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit, "positions": st["positions"]}

# ================== ROULETTE ==================
RED = {1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36}
BLACK = {2,4,6,8,10,11,13,15,17,20,22,24,26,28,29,31,33,35}

@app.post("/api/games/roulette/bet")
async def roulette_bet(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("roulette")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    bet = float(body.get("bet", 0)); bt = body.get("type"); bv = body.get("value")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "roulette")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    n = roulette_number(ss, p["client_seed"], nonce)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    win = False; pm = 0.0
    if bt == "red" and n in RED: win, pm = True, ROUL_RB_PAYOUT
    elif bt == "black" and n in BLACK: win, pm = True, ROUL_RB_PAYOUT
    elif bt == "even" and n != 0 and n % 2 == 0: win, pm = True, ROUL_RB_PAYOUT
    elif bt == "odd" and n % 2 == 1: win, pm = True, ROUL_RB_PAYOUT
    elif bt in ("dozen1","dozen2","dozen3"):
        d = {"dozen1": range(1,13), "dozen2": range(13,25), "dozen3": range(25,37)}[bt]
        if n in d: win, pm = True, ROUL_DOZEN_PAYOUT
    elif bt == "number" and int(bv) == n: win, pm = True, ROUL_NUM_PAYOUT
    profit = -bet
    if win:
        payout = round(bet * pm, 8); profit = round(payout - bet, 8)
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    await log_round(p["id"], "roulette", bet, {"n": n, "bet": bt, "win": win}, profit, ss, nonce)
    color = "green" if n == 0 else ("red" if n in RED else "black")
    return {"ok": True, "number": n, "color": color, "win": win,
            "payout": round(bet * pm, 8) if win else 0, "profit": profit}

# ================== KENO ==================
@app.post("/api/games/keno/play")
async def keno_play(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("keno")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    bet = float(body.get("bet", 0))
    picks = body.get("picks") or []
    if not isinstance(picks, list): raise HTTPException(400, "picks")
    try: picks = sorted(set(int(x) for x in picks))
    except: raise HTTPException(400, "picks nums")
    if not (1 <= len(picks) <= 10): raise HTTPException(400, "1-10 picks")
    if not all(1 <= x <= 80 for x in picks): raise HTTPException(400, "1-80")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "keno")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    drawn = keno_draw(ss, p["client_seed"], nonce, 20)
    hits = len(set(picks) & set(drawn))
    mult_table = KENO_PAYOUTS.get(len(picks), {})
    mult = float(mult_table.get(hits, 0))
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    if profit > 0:
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    elif profit < 0:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    await log_round(p["id"], "keno", bet,
                    {"picks": picks, "drawn": drawn, "hits": hits, "mult": mult},
                    profit, ss, nonce)
    return {"ok": True, "drawn": drawn, "hits": hits, "mult": mult,
            "payout": payout, "profit": profit}

# ================== HI-LO API ==================
@app.get("/api/games/hilo/state")
async def hilo_state(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "hilo": return {"active": False}
    st = ar["state"]
    current = int(st["current"])
    ph, mh = hilo_prob_mult(current, "higher")
    pl, ml = hilo_prob_mult(current, "lower")
    return {"active": True, "current": current, "level": int(st["level"]),
            "mult": float(st["mult"]), "bet": float(ar["bet_amount"]),
            "probs": {"higher": ph, "lower": pl},
            "mults": {"higher": mh, "lower": ml},
            "card_names": HILO_NAMES}

@app.post("/api/games/hilo/start")
async def hilo_start(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("hilo")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    bet = float(body.get("bet", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "hilo")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    if await get_active_round(p["id"]): raise HTTPException(400, "active")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    card = hilo_draw_card(ss, p["client_seed"], nonce, 0)
    state = {"current": card, "level": 0, "mult": 1.0, "bet": bet}
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "hilo", "bet_amount": bet,
        "state": state, "server_seed": ss, "nonce": nonce}))
    ph, mh = hilo_prob_mult(card, "higher")
    pl, ml = hilo_prob_mult(card, "lower")
    return {"ok": True, "current": card, "level": 0, "mult": 1.0,
            "probs": {"higher": ph, "lower": pl},
            "mults": {"higher": mh, "lower": ml},
            "card_names": HILO_NAMES}

@app.post("/api/games/hilo/guess")
async def hilo_guess(body: dict, user: dict = Depends(get_current_user)):
    direction = (body.get("direction") or "").lower()
    if direction not in ("higher", "lower"): raise HTTPException(400, "dir")
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "hilo": raise HTTPException(400, "no game")
    st = ar["state"]
    current = int(st["current"])
    bet = float(st["bet"])
    step = int(st["level"]) + 1
    next_card = hilo_draw_card(ar["server_seed"], p["client_seed"], ar["nonce"], step)
    win = (next_card >= current) if direction == "higher" else (next_card <= current)
    if not win:
        await log_round(p["id"], "hilo", bet,
                        {"lost": True, "prev": current, "next": next_card,
                         "dir": direction, "level": st["level"]},
                        -bet, ar["server_seed"], ar["nonce"])
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        await clear_active_round(p["id"])
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
        return {"ok": True, "lost": True, "current": next_card,
                "profit": -bet, "mult": 0, "card_names": HILO_NAMES}
    _, m = hilo_prob_mult(current, direction)
    new_mult = round(float(st["mult"]) * m, 6)
    st.update({"current": next_card, "level": st["level"] + 1, "mult": new_mult})
    await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))
    ph, mh = hilo_prob_mult(next_card, "higher")
    pl, ml = hilo_prob_mult(next_card, "lower")
    return {"ok": True, "lost": False, "current": next_card,
            "level": st["level"], "mult": new_mult,
            "probs": {"higher": ph, "lower": pl},
            "mults": {"higher": mh, "lower": ml},
            "card_names": HILO_NAMES}

@app.post("/api/games/hilo/cashout")
async def hilo_cashout(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "hilo": raise HTTPException(400, "no game")
    st = ar["state"]
    if st["level"] <= 0: raise HTTPException(400, "no level")
    bet = float(st["bet"]); mult = float(st["mult"])
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await log_round(p["id"], "hilo", bet, {"level": st["level"], "mult": mult},
                    profit, ar["server_seed"], ar["nonce"])
    await clear_active_round(p["id"])
    return {"ok": True, "level": st["level"], "mult": mult,
            "payout": payout, "profit": profit}

# ================== SCRATCH ==================
@app.post("/api/games/scratch/play")
async def scratch_play(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("scratch")
    if MAINTENANCE: raise HTTPException(503, "maintenance")
    ticket_id = (body.get("ticket") or "").strip()
    tier = SCRATCH_TIER_MAP.get(ticket_id)
    if not tier: raise HTTPException(400, "неизвестный билет")
    bet = float(tier["bet"])
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, "bet")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "scratch")
    if float(p["balance"]) < bet: raise HTTPException(400, "balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    cells, mult = scratch_draw(ss, p["client_seed"], nonce, tier)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(add_wager(p["id"], bet))
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    if profit > 0:
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    elif profit < 0:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    await log_round(p["id"], "scratch", bet,
                    {"ticket": ticket_id, "cells": cells, "mult": mult},
                    profit, ss, nonce)
    return {"ok": True, "cells": cells, "mult": mult,
            "payout": payout, "profit": profit,
            "bet": bet, "ticket": ticket_id}
