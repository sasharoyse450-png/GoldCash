import os, json, hmac, hashlib, logging, asyncio, time, math
from urllib.parse import parse_qsl
from contextlib import asynccontextmanager
from math import comb
from datetime import datetime, timezone, timedelta

import httpx
from fastapi import FastAPI, Header, HTTPException, Depends, Request
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
    "basket": True, "dart": True, "football": True,
}

def ensure_game_enabled(game: str):
    if not GAMES_ENABLED.get(game, True):
        raise HTTPException(503, f"игра {game} временно отключена")

# ================== PREDICTION GAMES ==================
DICE_GAMES = {
    "dice":     {"emoji": "🎲", "min": 1, "max": 6, "name": "Кубик"},
    "basket":   {"emoji": "🏀", "min": 1, "max": 5, "name": "Баскетбол"},
    "dart":     {"emoji": "🎯", "min": 1, "max": 6, "name": "Дартс"},
    "football": {"emoji": "⚽", "min": 1, "max": 5, "name": "Футбол"},
}

DICE_PREDICTIONS = {
    "dice": {
        "even":   {"label": "Чёт",         "mult": 1.92},
        "odd":    {"label": "Нечёт",       "mult": 1.92},
        "low":    {"label": "1-3",         "mult": 1.92},
        "high":   {"label": "4-6",         "mult": 1.92},
        "num":    {"label": "Точное число","mult": 5.76},
    },
    "basket": {
        "low":    {"label": "1-2",         "mult": 1.6},
        "high":   {"label": "3-5",         "mult": 1.6},
        "num":    {"label": "Точное число","mult": 4.8},
    },
    "dart": {
        "red":    {"label": "Красное 1-2", "mult": 2.88},
        "white":  {"label": "Белое 3-5",   "mult": 1.92},
        "center": {"label": "Центр 6",     "mult": 5.76},
        "num":    {"label": "Точное число","mult": 5.76},
    },
    "football": {
        "goal":   {"label": "Гол 4-5",     "mult": 2.4},
        "miss":   {"label": "Мимо 1-3",    "mult": 1.6},
        "num":    {"label": "Точное число","mult": 4.8},
    },
}

def eval_prediction(game, result, ptype, pvalue=None):
    if game == "dice":
        if ptype == "num":  return result == int(pvalue)
        if ptype == "even": return result % 2 == 0
        if ptype == "odd":  return result % 2 == 1
        if ptype == "low":  return 1 <= result <= 3
        if ptype == "high": return 4 <= result <= 6
    if game == "basket":
        if ptype == "num":  return result == int(pvalue)
        if ptype == "low":  return result <= 2
        if ptype == "high": return result >= 3
    if game == "dart":
        if ptype == "num":    return result == int(pvalue)
        if ptype == "red":    return 1 <= result <= 2
        if ptype == "white":  return 3 <= result <= 5
        if ptype == "center": return result == 6
    if game == "football":
        if ptype == "num":  return result == int(pvalue)
        if ptype == "goal": return result >= 4
        if ptype == "miss": return result <= 3
    return False

def zone_label(game, val):
    if game == "dart":
        if val in (1, 2):    return "🔴 красное"
        if val in (3, 4, 5): return "⚪ белое"
        if val == 6:         return "🎯 центр"
    if game == "dice":
        return "чёт" if val % 2 == 0 else "нечёт"
    if game == "basket":
        return "промах" if val <= 2 else "забил"
    if game == "football":
        return "мимо" if val <= 3 else "гол"
    return ""

PLINKO_MULTS = {
    8:  [5.6, 2.1, 1.1, 1.0, 0.5, 1.0, 1.1, 2.1, 5.6],
    12: [10, 3, 1.6, 1.4, 1.1, 1.0, 0.5, 1.0, 1.1, 1.4, 1.6, 3, 10],
    16: [16, 9, 2, 1.4, 1.4, 1.2, 1.1, 1.0, 0.5, 1.0, 1.1, 1.2, 1.4, 1.4, 2, 9, 16],
}

supabase: Client = create_client(SUPABASE_URL, SUPABASE_SERVICE_KEY)
BOT_USERNAME: str | None = None

crash_state = {
    "round_id": None, "status": "idle", "server_seed": None,
    "crash_point": None, "started_at": None, "betting_ends_at": None,
    "auto_task": None,
}

class AmountInput(StatesGroup):
    deposit = State()
    withdraw = State()

class AdminInput(StatesGroup):
    broadcast = State()

class PredictionInput(StatesGroup):
    custom_bet = State()

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
        reason = profile.get("ban_reason") or "нарушение правил"
        raise HTTPException(403, f"аккаунт заблокирован: {reason}")

# ================== SUBSCRIPTION ==================
async def is_subscribed(user_id: int) -> bool:
    if is_admin(user_id): return True
    if not CHANNEL_ID: return True
    try:
        member = await bot.get_chat_member(chat_id=CHANNEL_ID, user_id=user_id)
        return member.status in ("member", "administrator", "creator")
    except Exception as e:
        log.warning("is_subscribed failed for %s: %s", user_id, e)
        return True

def sub_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📢 Подписаться", url=CHANNEL_URL)],
        [InlineKeyboardButton(text="✅ Я подписался", callback_data="check_sub")]])

async def send_sub_prompt(message: Message):
    if not CHANNEL_URL: return
    await message.answer(
        "🔒 <b>Доступ только для подписчиков</b>\n\n"
        f"Подпишись на канал:\n👉 <a href=\"{CHANNEL_URL}\">{CHANNEL_URL.replace('https://t.me/', '@')}</a>\n\n"
        "После подписки нажми <b>«Я подписался»</b>.",
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

# ================== XROCKET (ИСПРАВЛЕНО) ==================
async def xrocket_request(method: str, path: str, body: dict | None = None) -> dict:
    """Универсальный запрос к xRocket Pay API."""
    url = f"{XROCKET_API_BASE}{path}"
    headers = {
        "Authorization": f"Bearer {XROCKET_API_KEY}",
        "Content-Type": "application/json",
    }
    async with httpx.AsyncClient(timeout=30) as http:
        r = await http.request(method, url, json=body or {}, headers=headers)
        try:
            data = r.json()
        except Exception:
            data = {"raw": r.text}

        log.info("xRocket %s %s -> %s\n  req=%s\n  resp=%s",
                 method, path, r.status_code, body, data)

        if r.status_code not in (200, 201):
            msg = (data.get("detail") or data.get("message")
                   or data.get("error") or f"HTTP {r.status_code}")
            if isinstance(msg, dict):
                msg = json.dumps(msg, ensure_ascii=False)
            raise Exception(msg)

        return data


async def xrocket_create_invoice(amount: float, description: str,
                                  client_id: str, currency: str = "USDT") -> dict:
    """Создаёт инвойс на оплату. Возвращает {'id': ..., 'link': ..., 'raw': ...}"""
    payload = {
        "currency": currency.upper(),
        "amount": float(amount),
        "description": description,
        "clientInvoiceId": client_id,
    }
    data = await xrocket_request("POST", "/api/v1/invoices", payload)

    links = data.get("links") or {}
    link = (links.get("telegramBotLink")
            or links.get("telegramMiniAppLink")
            or links.get("webLink"))

    if not link:
        raise Exception(f"xRocket не вернул ссылку: {data}")

    return {"id": data.get("id"), "link": link, "raw": data}


async def xrocket_create_payout(user_id: int, amount: float, comment: str,
                                 client_id: str, currency: str = "USDT") -> dict:
    """Отправляет выплату пользователю Telegram."""
    payload = {
        "clientPayoutId": client_id,
        "target": str(user_id),
        "targetType": "telegram_user_id",
        "asset": currency.upper(),
        "amount": str(amount),
        "description": comment or "Withdraw",
    }
    data = await xrocket_request("POST", "/api/v1/payouts", payload)
    return {"id": data.get("payoutId"), "raw": data}


# ================== MATH / PF ==================
def pf_rand(ss, cs, n):
    h = hmac.new(ss.encode(), f"{cs}:{n}".encode(), hashlib.sha256).hexdigest()
    return int(h[:13], 16) / float(0xFFFFFFFFFFFFF)

def crash_point(ss, cs, n):
    r = pf_rand(ss, cs, n)
    if r < HOUSE_EDGE: return 1.00
    return round(min(1000.0, (1 - HOUSE_EDGE) / (1 - r)), 2)

def crash_mult(elapsed):
    return round(max(1.0, 1.07 ** elapsed), 2)

def roulette_number(ss, cs, n):
    return int(pf_rand(ss, cs, n) * 37)

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

def dice_result(ss, cs, n):
    return int(pf_rand(ss, cs, n) * 6) + 1

def plinko_path(ss, cs, n, rows):
    idx = 0; path = []
    for i in range(rows):
        r = pf_rand(ss, cs, n * 1000 + i)
        step = 1 if r >= 0.5 else 0
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
    while total > 21 and aces > 0:
        total -= 10; aces -= 1
    return total

# ================== AUTH ==================
def validate_init_data(init_data, bot_token):
    try:
        parsed = dict(parse_qsl(init_data, keep_blank_values=True))
        rh = parsed.pop("hash", None)
        if not rh:
            log.error("validate: no hash in initData")
            return None

        auth_date_str = parsed.get("auth_date")
        if auth_date_str:
            try:
                auth_date = int(auth_date_str)
                age = time.time() - auth_date
                if age > 7200:
                    log.warning("validate: initData expired, age=%ss", int(age))
                    return None
            except (ValueError, TypeError):
                log.error("validate: bad auth_date=%s", auth_date_str)

        dcs = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
        sk = hmac.new(b"WebAppData", bot_token.encode(), hashlib.sha256).digest()
        calc = hmac.new(sk, dcs.encode(), hashlib.sha256).hexdigest()

        if not hmac.compare_digest(calc, rh):
            log.error("validate: HASH MISMATCH\n  data_check_string=%r\n  calc=%s\n  recv=%s",
                      dcs, calc, rh)
            return None

        u = json.loads(parsed.get("user", "{}"))
        if not u.get("id"):
            log.error("validate: no user.id")
            return None
        return u
    except Exception:
        log.exception("validate_init_data failed")
        return None

async def get_current_user(x_telegram_init_data: str = Header(None, alias="X-Telegram-Init-Data")):
    if not x_telegram_init_data:
        log.warning("API: missing X-Telegram-Init-Data header")
        raise HTTPException(401, "missing init data")
    u = validate_init_data(x_telegram_init_data, BOT_TOKEN)
    if not u:
        raise HTTPException(401, "invalid init data")
    if not await is_subscribed(int(u["id"])):
        raise HTTPException(403, "subscription_required")
    return u

# ================== DB ==================
async def get_or_create_profile(tg_user):
    tg_id = int(tg_user["id"])
    r = await sb(supabase.table("profiles").select("*").eq("telegram_id", tg_id))
    if r.data: return r.data[0]
    ins = await sb(supabase.table("profiles").insert({
        "telegram_id": tg_id, "username": tg_user.get("username"),
        "first_name": tg_user.get("first_name"), "preferred_currency": "USDT"}))
    return ins.data[0]

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
    rounds = (await sb(supabase.table("game_rounds").select("id").eq("user_id", uid))).data or []
    dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    wins = sum(float(t["amount"]) for t in tx if t["type"] == "win")
    bets = sum(float(t["amount"]) for t in tx if t["type"] == "bet")
    return {"games": len(rounds), "deposits": round(dep, 2), "withdrawals": round(wd, 2),
            "bets": round(bets, 2), "wins": round(wins, 2), "net": round(wins - bets, 2)}

async def credit_referrer_on_loss(uid: str, bet_amount: float):
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
        if done: log.info("wager complete uid=%s req=%s", uid, req)
    except Exception:
        log.exception("apply_wager_progress failed")

async def check_and_reset_wager_if_broke(uid):
    try:
        r = await sb(supabase.table("profiles").select(
            "balance, bonus_active").eq("id", uid))
        if not r.data: return False
        p = r.data[0]
        if not p.get("bonus_active"): return False
        bal = float(p.get("balance") or 0)
        if bal >= WAGER_RESET_THRESHOLD:
            return False
        await sb(supabase.table("profiles").update({
            "bonus_active": False, "wager_required": 0, "wager_progress": 0,
            "bonus_amount": 0, "bonus_code": None, "bonus_max_bet": None,
            "bonus_allowed_games": None}).eq("id", uid))
        log.info("wager auto-reset (broke) uid=%s bal=%s", uid, bal)
        return True
    except Exception:
        log.exception("check_and_reset_wager_if_broke failed")
        return False

async def check_wager_lock(profile):
    if not profile.get("bonus_active"): return
    req = float(profile.get("wager_required") or 0)
    prog = float(profile.get("wager_progress") or 0)
    if prog < req:
        left = round(req - prog, 2)
        raise HTTPException(400, f"🎰 Бонус активен. Отыграй ещё {left} ₮ (прогресс {prog:.2f}/{req:.2f})")

async def check_bonus_max_bet(profile, bet: float):
    if not profile.get("bonus_active"): return
    mb = profile.get("bonus_max_bet")
    if mb and float(bet) > float(mb):
        raise HTTPException(400, f"🎰 Пока бонус активен, макс. ставка {float(mb):.2f} ₮")

async def check_bonus_game(profile, game: str):
    if not profile.get("bonus_active"): return
    allowed = profile.get("bonus_allowed_games")
    if allowed is None: return
    if not isinstance(allowed, list): return
    if game not in allowed:
        if not allowed:
            raise HTTPException(400, "🎰 Бонус можно только отыграть выводом. Игры заблокированы.")
        raise HTTPException(400, f"🎰 С бонусом доступны только: {', '.join(allowed)}")

def _bonus_info(p: dict) -> dict:
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
    if currency not in SUPPORTED_CURRENCIES:
        raise HTTPException(400, "неподдерживаемая валюта")

    cid = f"dep_{profile['id'][:8]}_{int(time.time())}"
    inv = await xrocket_create_invoice(
        amount=amount,
        description="GoldCash deposit",
        client_id=cid,
        currency=currency,
    )

    await sb(supabase.table("transactions").insert({
        "user_id": profile["id"], "type": "deposit", "amount": amount,
        "currency": currency, "external_id": cid, "status": "pending",
        "meta": {"invoice_id": inv.get("id")}}))

    return {"link": inv["link"], "invoice_id": inv.get("id"), "cid": cid}

async def daily_withdrawn(uid):
    since = (datetime.now(timezone.utc) - timedelta(hours=24)).isoformat()
    r = await sb(supabase.table("transactions").select("amount")
                 .eq("user_id", uid).eq("type", "withdraw").eq("status", "completed")
                 .gte("created_at", since))
    return sum(float(x["amount"]) for x in r.data or [])

async def do_withdraw(profile, tg_id, amount, currency="USDT"):
    if currency not in SUPPORTED_CURRENCIES:
        raise HTTPException(400, "неподдерживаемая валюта")

    # кулдаун после депозита
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
        except Exception: log.exception("cooldown check failed")

    # дневной лимит
    spent = await daily_withdrawn(profile["id"])
    if spent + amount > MAX_WITHDRAW_DAILY:
        left = MAX_WITHDRAW_DAILY - spent
        raise HTTPException(400, f"дневной лимит вывода. Осталось {max(0, left):.2f}")

    # выплата
    cid = f"wd_{profile['id'][:8]}_{int(time.time())}"
    payout = await xrocket_create_payout(
        user_id=int(tg_id),
        amount=amount,
        comment="GoldCash withdraw",
        client_id=cid,
        currency=currency,
    )

    # списываем баланс
    await sb_rpc("change_balance", {"p_user_id": profile["id"], "p_delta": -amount})
    await sb(supabase.table("transactions").insert({
        "user_id": profile["id"], "type": "withdraw", "amount": amount,
        "currency": currency, "external_id": cid, "status": "completed",
        "meta": {"payout_id": payout.get("id")}}))
    return payout

# ================== CRASH LOOP ==================
async def crash_auto_cashout_watcher(round_id: str, started_at: float, crash_point_val: float):
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
            except Exception:
                active = []
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
                            "meta": {"game": "crash_auto", "mult": mult, "round": round_id}}))
                        await log_round(b["user_id"], "crash", amount,
                                        {"global": True, "mult": mult, "auto": True, "round": round_id},
                                        profit, crash_state["server_seed"] or "", 0)
                    except Exception: log.exception("auto cashout failed")
            await asyncio.sleep(0.15)
    except asyncio.CancelledError: pass
    except Exception: log.exception("auto cashout watcher error")

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
            round_id = res.data[0]["id"]
            crash_state.update({"round_id": round_id, "status": "betting",
                                "server_seed": ss, "crash_point": cp,
                                "started_at": None, "betting_ends_at": now + CRASH_BETTING_SEC})
            await asyncio.sleep(CRASH_BETTING_SEC)
            started = time.time()
            await sb(supabase.table("crash_rounds").update({
                "status": "running", "started_at": datetime.now(timezone.utc).isoformat()}).eq("id", round_id))
            crash_state["status"] = "running"; crash_state["started_at"] = started
            auto_task = asyncio.create_task(crash_auto_cashout_watcher(round_id, started, cp))
            crash_state["auto_task"] = auto_task
            duration = max(0.4, math.log(cp) / math.log(1.07)) if cp > 1.0 else 0.4
            await asyncio.sleep(duration)
            if not auto_task.done(): auto_task.cancel()
            await sb(supabase.table("crash_rounds").update({
                "status": "crashed", "ended_at": datetime.now(timezone.utc).isoformat()}).eq("id", round_id))
            crash_state["status"] = "crashed"
            lost = (await sb(supabase.table("crash_bets").select("*")
                             .eq("round_id", round_id).eq("status", "active"))).data or []
            for b in lost:
                await sb(supabase.table("crash_bets").update({"status": "lost"}).eq("id", b["id"]))
                await log_round(b["user_id"], "crash", float(b["amount"]),
                                {"global": True, "crashed_at": cp}, -float(b["amount"]), ss, 0)
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
        [InlineKeyboardButton(text="🎲 Предсказания", callback_data="pg:home")],
        [InlineKeyboardButton(text="💰 Пополнить", callback_data="menu:deposit"),
         InlineKeyboardButton(text="💸 Вывести", callback_data="menu:withdraw")],
        [InlineKeyboardButton(text="👥 Друзья (5%)", callback_data="menu:ref"),
         InlineKeyboardButton(text="📊 Статистика", callback_data="menu:stats")],
        [InlineKeyboardButton(text="📖 Помощь", callback_data="menu:help")],
        [InlineKeyboardButton(text="🌐 Открыть казино", web_app=WebAppInfo(url=WEBAPP_URL))]])

def back_kb():
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])

def fmt_stats(s, balance, first_name):
    return (f"👤 <b>{first_name or 'игрок'}</b>\n\n"
            f"💎 <b>Баланс:</b> {balance:.2f}\n━━━━━━━━━━━━━━━\n"
            f"📥 Пополнено: <b>{s['deposits']:.2f}</b>\n📤 Выведено: <b>{s['withdrawals']:.2f}</b>\n"
            f"🎯 Ставок: <b>{s['bets']:.2f}</b>\n🏆 Выигрышей: <b>{s['wins']:.2f}</b>\n"
            f"🎮 Игр: <b>{s['games']}</b>\n📊 Профит: <b>{s['net']:+.2f}</b>")

# ================== PREDICTION KEYBOARDS ==================
def pred_home_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎲 Кубик", callback_data="pgm:dice")],
        [InlineKeyboardButton(text="🏀 Баскетбол", callback_data="pgm:basket")],
        [InlineKeyboardButton(text="🎯 Дартс", callback_data="pgm:dart")],
        [InlineKeyboardButton(text="⚽ Футбол", callback_data="pgm:football")],
        [InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])

def pred_bet_kb(game):
    amounts = [0.5, 1, 5, 10, 25, 50]
    rows = []
    for i in range(0, len(amounts), 3):
        rows.append([InlineKeyboardButton(text=f"{a} ₮", callback_data=f"pgb:{game}:{a}") for a in amounts[i:i+3]])
    rows.append([InlineKeyboardButton(text="✏️ Своя сумма", callback_data=f"pgcb:{game}")])
    rows.append([InlineKeyboardButton(text="⬅️ Назад", callback_data="pg:home"),
                 InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def pred_type_kb(game, bet):
    back_row = [InlineKeyboardButton(text="⬅️ Ставка", callback_data=f"pgm:{game}"),
                InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]
    if game == "dice":
        return InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Чёт", callback_data=f"pgr:{game}:{bet}:even"),
             InlineKeyboardButton(text="Нечёт", callback_data=f"pgr:{game}:{bet}:odd")],
            [InlineKeyboardButton(text="1-3", callback_data=f"pgr:{game}:{bet}:low"),
             InlineKeyboardButton(text="4-6", callback_data=f"pgr:{game}:{bet}:high")],
            [InlineKeyboardButton(text="🔢 Точное число", callback_data=f"pgn:{game}:{bet}")],
            back_row])
    if game == "basket":
        return InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Забил 3-5", callback_data=f"pgr:{game}:{bet}:high"),
             InlineKeyboardButton(text="Промазал 1-2", callback_data=f"pgr:{game}:{bet}:low")],
            [InlineKeyboardButton(text="🔢 Точное число", callback_data=f"pgn:{game}:{bet}")],
            back_row])
    if game == "dart":
        return InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔴 Красное 1-2", callback_data=f"pgr:{game}:{bet}:red")],
            [InlineKeyboardButton(text="⚪ Белое 3-5",   callback_data=f"pgr:{game}:{bet}:white")],
            [InlineKeyboardButton(text="🎯 Центр 6",     callback_data=f"pgr:{game}:{bet}:center")],
            [InlineKeyboardButton(text="🔢 Точное число", callback_data=f"pgn:{game}:{bet}")],
            back_row])
    if game == "football":
        return InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="⚽ Гол 4-5", callback_data=f"pgr:{game}:{bet}:goal"),
             InlineKeyboardButton(text="❌ Мимо 1-3", callback_data=f"pgr:{game}:{bet}:miss")],
            [InlineKeyboardButton(text="🔢 Точное число", callback_data=f"pgn:{game}:{bet}")],
            back_row])
    return InlineKeyboardMarkup(inline_keyboard=[back_row])

def pred_number_kb(game, bet):
    max_n = DICE_GAMES[game]["max"]
    rows = []; row = []
    for n in range(1, max_n + 1):
        row.append(InlineKeyboardButton(text=str(n), callback_data=f"pgr:{game}:{bet}:num:{n}"))
        if len(row) == 3: rows.append(row); row = []
    if row: rows.append(row)
    rows.append([InlineKeyboardButton(text="⬅️ Назад", callback_data=f"pgb:{game}:{bet}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

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
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>🎮 Управление играми</b>\n"
        "/astatus · /aon GAME · /aoff GAME · /aonall · /aoffall\n"
        "Игры: crash, mines, roulette, dice, plinko, blackjack, tower, basket, dart, football\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>🎮 Активные игры</b>\n"
        "/aendgame ID [lose] · /aendgameall · /aactive ID · /aactivelist · /acleargames\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>👤 Юзеры</b>\n"
        "/auser ID · /afind @username · /awhois ID\n"
        "/agive · /atake · /asetbal\n"
        "/aban · /aunban · /abanlist · /apause · /aunpause\n"
        "/anote · /anotes · /aresetnonce · /aresetserver\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>📊 Статистика</b>\n"
        "/astats · /aggr · /abalances · /aonline · /arich\n"
        "/adaily · /aweekly · /agames · /atop · /atopdep · /atopwd · /arp\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>💸 Транзакции</b>\n"
        "/atx ID · /atxlast N · /arefund TX_ID\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>🎟 Промо</b>\n"
        "/anewpromo CODE SUM [WAGER] [USES] [MAX_BET] [GAMES]\n"
        "/alistpromos · /adelpromo CODE · /adelallpromos · /apromoinfo CODE\n"
        "/awager ID · /aresetwager ID · /apromogames CODE all|none|dice,mines\n"
        "/asetbonusgames ID all|none|dice,mines\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>📢 Сообщения</b>\n"
        "/abroadcast TXT · /apush ID TXT\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>⚙️ Настройки</b>\n"
        "/asettings · /asetrtp 0.96 · /asetminbet · /asetmaxbet\n"
        "/asetmindep · /asetminwd · /asetmaxwd\n"
        "/asetref 0.05 · /asetcooldown 15 · /amaintenance on|off\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>🩺 Система</b>\n"
        "/ahealth · /alogs N · /aclearlogs N · /aadmins",
        parse_mode="HTML")

@dp.message(Command("admin"))
async def cmd_admin(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"🏦 <b>Админ-панель</b>\n"
        f"RTP {100-HOUSE_EDGE*100:.0f}% · HE {HOUSE_EDGE*100:.1f}%\n"
        f"Мин ставка {MIN_BET} · макс {MAX_BET}\n"
        f"Мин деп {MIN_DEPOSIT} · мин вывод {MIN_WITHDRAW}\n"
        f"Лимит/сутки {MAX_WITHDRAW_DAILY}\nКулдаун {WITHDRAW_COOLDOWN_MIN} мин\n"
        f"Рефералка {REFERRAL_SHARE*100:.0f}%\n"
        f"Daily bonus: {DAILY_BONUS} ₮ / {BONUS_COOLDOWN_H}ч\n"
        f"Сброс вейджера если баланс < {WAGER_RESET_THRESHOLD} ₮\n"
        f"Maintenance: {'🚫 ON' if MAINTENANCE else '✅ OFF'}\n"
        f"Игры вкл: {sum(1 for v in GAMES_ENABLED.values() if v)}/{len(GAMES_ENABLED)}\n"
        f"Канал: {CHANNEL_ID or '— не задан —'}\n"
        "━━━━━━━━━━━━━━━━━━━\nВсе команды: /ahelp", parse_mode="HTML")

@dp.message(Command("astatus"))
async def cmd_astatus(message: Message):
    if not admin_only(message): return
    lines = [f"{'✅' if v else '⛔'} <code>{k}</code>" for k, v in GAMES_ENABLED.items()]
    await message.answer("<b>🎮 Статус игр</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("aon"))
async def cmd_aon(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer(f"/aon <game>\n{', '.join(GAMES_ENABLED.keys())}")
    g = command.args.strip().lower()
    if g not in GAMES_ENABLED: return await message.answer(f"❌ Нет игры {g}")
    GAMES_ENABLED[g] = True
    await message.answer(f"✅ <b>{g}</b> включена", parse_mode="HTML")

@dp.message(Command("aoff"))
async def cmd_aoff(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer(f"/aoff <game>\n{', '.join(GAMES_ENABLED.keys())}")
    g = command.args.strip().lower()
    if g not in GAMES_ENABLED: return await message.answer(f"❌ Нет игры {g}")
    GAMES_ENABLED[g] = False
    await message.answer(f"⛔ <b>{g}</b> выключена", parse_mode="HTML")

@dp.message(Command("aonall"))
async def cmd_aonall(message: Message):
    if not admin_only(message): return
    for g in GAMES_ENABLED: GAMES_ENABLED[g] = True
    await message.answer("✅ Все игры включены")

@dp.message(Command("aoffall"))
async def cmd_aoffall(message: Message):
    if not admin_only(message): return
    for g in GAMES_ENABLED: GAMES_ENABLED[g] = False
    await message.answer("⛔ Все игры выключены")

@dp.message(Command("aendgame"))
async def cmd_aendgame(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aendgame <id|@username> [lose]")
    parts = command.args.split()
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Юзер не найден")
    mode = parts[1].lower() if len(parts) > 1 else "refund"
    ar = await get_active_round(p["id"])
    if not ar: return await message.answer(f"Нет активной игры у <code>{p['telegram_id']}</code>", parse_mode="HTML")
    game = ar["game_type"]; bet = float(ar["bet_amount"])
    if mode != "lose":
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": bet})
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "admin", "amount": bet, "currency": "USDT",
            "status": "completed",
            "meta": {"by": message.from_user.id, "action": "endgame_refund", "game": game}}))
    await clear_active_round(p["id"])
    await log_round(p["id"], game, bet, {"admin_end": True, "mode": mode},
                    0 if mode != "lose" else -bet, "", 0)
    await message.answer(f"✅ <b>{game}</b> завершена. Режим: {'возврат' if mode != 'lose' else 'без возврата'}\nСтавка: {bet:.2f}", parse_mode="HTML")

@dp.message(Command("aendgameall"))
async def cmd_aendgameall(message: Message):
    if not admin_only(message): return
    rounds = (await sb(supabase.table("active_rounds").select("*"))).data or []
    if not rounds: return await message.answer("Активных игр нет")
    ok = 0; total = 0.0
    for ar in rounds:
        bet = float(ar["bet_amount"]); uid = ar["user_id"]
        try:
            await sb_rpc("change_balance", {"p_user_id": uid, "p_delta": bet})
            await sb(supabase.table("transactions").insert({
                "user_id": uid, "type": "admin", "amount": bet, "currency": "USDT",
                "status": "completed", "meta": {"by": message.from_user.id, "action": "endgame_refund_all"}}))
            await sb(supabase.table("active_rounds").delete().eq("user_id", uid))
            total += bet; ok += 1
        except Exception as e: log.exception("aendgameall fail: %s", e)
    await message.answer(f"✅ Завершено <b>{ok}</b>, возвращено <b>{total:.2f}</b>", parse_mode="HTML")

@dp.message(Command("aactive"))
async def cmd_aactive(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aactive <id>")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Юзер не найден")
    ar = await get_active_round(p["id"])
    if not ar: return await message.answer("Нет активной игры")
    await message.answer(
        f"<b>🎮 {ar['game_type']}</b>\nЮзер: <code>{p['telegram_id']}</code>\n"
        f"Ставка: {float(ar['bet_amount']):.2f}\nState: <code>{json.dumps(ar.get('state', {}))[:400]}</code>",
        parse_mode="HTML")

@dp.message(Command("aactivelist"))
async def cmd_aactivelist(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("active_rounds").select("*").order("started_at", desc=True).limit(30))
    if not r.data: return await message.answer("Активных игр нет")
    uids = list(set(x["user_id"] for x in r.data))
    prof = await sb(supabase.table("profiles").select("id, telegram_id, first_name").in_("id", uids))
    nm = {p["id"]: (p.get("first_name") or str(p.get("telegram_id"))) for p in prof.data or []}
    lines = [f"• <b>{nm.get(x['user_id'], '?')}</b> · {x['game_type']} · {float(x['bet_amount']):.2f}" for x in r.data]
    await message.answer("<b>🎮 Активные:</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("acleargames"))
async def cmd_acleargames(message: Message):
    if not admin_only(message): return
    await sb(supabase.table("active_rounds").delete().neq("user_id", "00000000-0000-0000-0000-000000000000"))
    await message.answer("✅ Все активные игры удалены")

@dp.message(Command("auser"))
async def cmd_auser(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("Использование: /auser <id|@username>")
    p = await admin_get_user(message, command.args.strip())
    if not p: return await message.answer("Юзер не найден")
    s = await get_user_stats(p["id"])
    ban = "🚫 ЗАБАНЕН" if p.get("is_banned") else "✅ активен"
    ar = await get_active_round(p["id"])
    active_line = f"\n🎮 активная: <b>{ar['game_type']}</b> ({float(ar['bet_amount']):.2f})" if ar else ""
    bonus_line = ""
    if p.get("bonus_active"):
        bonus_line = (f"\n🎰 Бонус: {float(p.get('wager_progress') or 0):.2f}"
                      f"/{float(p.get('wager_required') or 0):.2f}")
    await message.answer(
        f"👤 <b>{p.get('first_name') or '—'}</b> @{p.get('username') or '—'}\n"
        f"🆔 <code>{p['telegram_id']}</code>\n💎 <b>{float(p['balance']):.2f}</b>\nСтатус: {ban}{active_line}{bonus_line}\n"
        f"📥 {s['deposits']:.2f} · 📤 {s['withdrawals']:.2f}\n"
        f"🎯 {s['bets']:.2f} · 🏆 {s['wins']:.2f}\n🎮 {s['games']} · 📊 {s['net']:+.2f}",
        parse_mode="HTML")

@dp.message(Command("afind"))
async def cmd_afind(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/afind @username")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Не найден")
    s = await get_user_stats(p["id"])
    ban = "🚫 ЗАБАНЕН" if p.get("is_banned") else "✅"
    await message.answer(
        f"👤 <b>{p.get('first_name') or '—'}</b> @{p.get('username') or '—'}\n"
        f"🆔 <code>{p['telegram_id']}</code>\n💎 {float(p['balance']):.2f}\n{ban}\n"
        f"Игр: {s['games']} · профит: {s['net']:+.2f}", parse_mode="HTML")

@dp.message(Command("awhois"))
async def cmd_awhois(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/awhois <id>")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Юзер не найден")
    ar = await get_active_round(p["id"])
    extra = f"\n🎮 в игре: <b>{ar['game_type']}</b>" if ar else ""
    await message.answer(
        f"👤 {p.get('first_name') or '—'} @{p.get('username') or '—'}\n"
        f"🆔 <code>{p['telegram_id']}</code>\n💎 {float(p['balance']):.2f}{extra}", parse_mode="HTML")

@dp.message(Command("agive"))
async def cmd_agive(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) != 2: return await message.answer("/agive <id> <сумма>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Юзер не найден")
    try: amount = float(parts[1].replace(",", "."))
    except: return await message.answer("Некорректные аргументы")
    if amount <= 0: return await message.answer("Сумма > 0")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "admin", "amount": amount, "currency": "USDT",
        "status": "completed", "meta": {"by": message.from_user.id, "action": "give"}}))
    await message.answer(f"✅ +<b>{amount}</b> → <code>{p['telegram_id']}</code>", parse_mode="HTML")
    try: await bot.send_message(p["telegram_id"], f"💎 +<b>{amount}</b>", parse_mode="HTML")
    except: pass

@dp.message(Command("atake"))
async def cmd_atake(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) != 2: return await message.answer("/atake <id> <сумма>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Юзер не найден")
    try: amount = float(parts[1].replace(",", "."))
    except: return await message.answer("Некорректные аргументы")
    if amount <= 0: return await message.answer("Сумма > 0")
    if float(p["balance"]) < amount: return await message.answer(f"У юзера только {float(p['balance']):.2f}")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -amount})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "admin", "amount": amount, "currency": "USDT",
        "status": "completed", "meta": {"by": message.from_user.id, "action": "take"}}))
    await message.answer(f"✅ −<b>{amount}</b> у <code>{p['telegram_id']}</code>", parse_mode="HTML")

@dp.message(Command("asetbal"))
async def cmd_asetbal(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) != 2: return await message.answer("/asetbal <id> <сумма>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Юзер не найден")
    try: new_bal = float(parts[1].replace(",", "."))
    except: return await message.answer("Сумма числом")
    if new_bal < 0: return await message.answer("Сумма >= 0")
    diff = new_bal - float(p["balance"])
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": diff})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "admin", "amount": abs(diff), "currency": "USDT",
        "status": "completed",
        "meta": {"by": message.from_user.id, "action": "set_balance", "old": float(p["balance"]), "new": new_bal}}))
    await message.answer(f"✅ Баланс {p['telegram_id']} = <b>{new_bal:.2f}</b>", parse_mode="HTML")

@dp.message(Command("aban"))
async def cmd_aban(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aban <id> [причина]")
    parts = command.args.split(maxsplit=1)
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Юзер не найден")
    reason = parts[1] if len(parts) > 1 else "нарушение правил"
    await sb(supabase.table("profiles").update({"is_banned": True, "ban_reason": reason}).eq("id", p["id"]))
    await message.answer(f"🚫 <code>{p['telegram_id']}</code> забанен: {reason}", parse_mode="HTML")

@dp.message(Command("aunban"))
async def cmd_aunban(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aunban <id>")
    p = await admin_get_user(message, command.args.strip())
    if not p: return await message.answer("Юзер не найден")
    await sb(supabase.table("profiles").update({"is_banned": False, "ban_reason": None}).eq("id", p["id"]))
    await message.answer(f"✅ <code>{p['telegram_id']}</code> разбанен", parse_mode="HTML")

@dp.message(Command("abanlist"))
async def cmd_abanlist(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("profiles").select("telegram_id, first_name, username, ban_reason")
                 .eq("is_banned", True).limit(50))
    if not r.data: return await message.answer("Забаненных нет")
    lines = [f"• <code>{p['telegram_id']}</code> {p.get('first_name') or ''} — {p.get('ban_reason') or '—'}" for p in r.data]
    await message.answer("<b>🚫 Забаненные:</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("apause"))
async def cmd_apause(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/apause <id>")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Юзер не найден")
    await sb(supabase.table("profiles").update({"is_banned": True, "ban_reason": "paused by admin"}).eq("id", p["id"]))
    await message.answer(f"⏸ <code>{p['telegram_id']}</code> на паузе", parse_mode="HTML")

@dp.message(Command("aunpause"))
async def cmd_aunpause(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aunpause <id>")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Юзер не найден")
    await sb(supabase.table("profiles").update({"is_banned": False, "ban_reason": None}).eq("id", p["id"]))
    await message.answer(f"▶️ <code>{p['telegram_id']}</code> снят с паузы", parse_mode="HTML")

@dp.message(Command("anote"))
async def cmd_anote(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2: return await message.answer("/anote <id> <текст>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Юзер не найден")
    meta = p.get("admin_notes") or []
    if not isinstance(meta, list): meta = []
    meta.append({"by": message.from_user.id, "text": parts[1], "at": datetime.now(timezone.utc).isoformat()})
    try:
        await sb(supabase.table("profiles").update({"admin_notes": meta}).eq("id", p["id"]))
    except Exception as e:
        return await message.answer(f"⚠️ Нужна колонка admin_notes jsonb. {e}")
    await message.answer(f"✅ Заметка добавлена для {p['telegram_id']}")

@dp.message(Command("anotes"))
async def cmd_anotes(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/anotes <id>")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Юзер не найден")
    meta = p.get("admin_notes") or []
    if not meta: return await message.answer("Заметок нет")
    lines = [f"• {n.get('text')} — {n.get('by')} @ {n.get('at','')[:16]}" for n in meta]
    await message.answer(f"<b>📝 Заметки:</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("aresetnonce"))
async def cmd_aresetnonce(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aresetnonce <id>")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Юзер не найден")
    await sb(supabase.table("profiles").update({"nonce": 0}).eq("id", p["id"]))
    await message.answer(f"✅ nonce сброшен для {p['telegram_id']}")

@dp.message(Command("aresetserver"))
async def cmd_aresetserver(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aresetserver <id>")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Юзер не найден")
    new_seed = os.urandom(16).hex()
    await sb(supabase.table("profiles").update({"client_seed": new_seed}).eq("id", p["id"]))
    await message.answer(f"✅ Новый client_seed:\n<code>{new_seed}</code>", parse_mode="HTML")

@dp.message(Command("astats"))
async def cmd_astats(message: Message):
    if not admin_only(message): return
    try:
        users = (await sb(supabase.table("profiles").select("id, balance"))).data or []
        tx = (await sb(supabase.table("transactions").select("type, amount, status"))).data or []
        rounds = (await sb(supabase.table("game_rounds").select("bet_amount, profit, game_type"))).data or []
        dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
        wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
        total_bets = sum(float(r["bet_amount"]) for r in rounds)
        ggr = -sum(float(r["profit"]) for r in rounds)
        await message.answer(
            f"👥 Юзеров: <b>{len(users)}</b>\n💰 Балансов: <b>{sum(float(u['balance']) for u in users):.2f}</b>\n"
            f"📥 Депозиты: <b>{dep:.2f}</b>\n📤 Выводы: <b>{wd:.2f}</b>\n"
            f"🎯 Оборот: <b>{total_bets:.2f}</b>\n📈 GGR: <b>{ggr:+.2f}</b>\n🎮 Игр: {len(rounds)}",
            parse_mode="HTML")
    except Exception as e: await message.answer(f"❌ {e}")

@dp.message(Command("aggr"))
async def cmd_aggr(message: Message):
    if not admin_only(message): return
    rounds = (await sb(supabase.table("game_rounds").select("bet_amount, profit"))).data or []
    turnover = sum(float(r["bet_amount"]) for r in rounds)
    user_profit = sum(float(r["profit"]) for r in rounds)
    ggr = -user_profit
    rtp_real = (turnover - ggr) / turnover if turnover else 0
    await message.answer(
        f"<b>📈 GGR</b>\nОборот: <b>{turnover:.2f}</b>\nGGR: <b>{ggr:+.2f}</b>\n"
        f"Реальный RTP: <b>{rtp_real*100:.2f}%</b>\nИгр: {len(rounds)}", parse_mode="HTML")

@dp.message(Command("abalances"))
async def cmd_abalances(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("profiles").select("balance"))
    total = sum(float(x["balance"]) for x in r.data or [])
    await message.answer(f"💰 Суммарно: <b>{total:.2f}</b>\nЮзеров: {len(r.data or [])}", parse_mode="HTML")

@dp.message(Command("aonline"))
async def cmd_aonline(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(minutes=5)).isoformat()
    r = await sb(supabase.table("action_log").select("user_id").gte("created_at", since))
    uids = list(set(x["user_id"] for x in r.data or []))
    await message.answer(f"👥 Активны за 5 мин: <b>{len(uids)}</b>", parse_mode="HTML")

@dp.message(Command("arich"))
async def cmd_arich(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("profiles").select("telegram_id, first_name, username, balance")
                 .order("balance", desc=True).limit(15))
    if not r.data: return await message.answer("Пусто")
    lines = [f"{i+1}. <b>{p.get('first_name') or p.get('username') or p['telegram_id']}</b> — {float(p['balance']):.2f}"
             for i, p in enumerate(r.data)]
    await message.answer("<b>💰 Топ по балансу</b>\n" + "\n".join(lines), parse_mode="HTML")

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
    users = (await sb(supabase.table("profiles").select("id").gte("created_at", since))).data or []
    await message.answer(
        f"<b>📅 За 24 часа</b>\nНовых: <b>{len(users)}</b>\n"
        f"Депозиты: <b>{dep:.2f}</b>\nВыводы: <b>{wd:.2f}</b>\n"
        f"Оборот: <b>{bets:.2f}</b>\nGGR: <b>{ggr:+.2f}</b>\nИгр: {len(rounds)}", parse_mode="HTML")

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
    users = (await sb(supabase.table("profiles").select("id").gte("created_at", since))).data or []
    await message.answer(
        f"<b>📅 За 7 дней</b>\nНовых: <b>{len(users)}</b>\n"
        f"Депозиты: <b>{dep:.2f}</b>\nВыводы: <b>{wd:.2f}</b>\n"
        f"Оборот: <b>{bets:.2f}</b>\nGGR: <b>{ggr:+.2f}</b>\nИгр: {len(rounds)}", parse_mode="HTML")

@dp.message(Command("agames"))
async def cmd_agames(message: Message):
    if not admin_only(message): return
    rounds = (await sb(supabase.table("game_rounds").select("game_type, bet_amount, profit"))).data or []
    agg = {}
    for r in rounds:
        g = r["game_type"]
        a = agg.setdefault(g, {"count": 0, "bets": 0.0, "ggr": 0.0})
        a["count"] += 1; a["bets"] += float(r["bet_amount"]); a["ggr"] -= float(r["profit"])
    lines = []
    for g, a in sorted(agg.items(), key=lambda x: -x[1]["ggr"]):
        rtp = (a["bets"] - a["ggr"]) / a["bets"] * 100 if a["bets"] else 0
        lines.append(f"<b>{g}</b>: {a['count']} · оборот {a['bets']:.2f} · GGR {a['ggr']:+.2f} · RTP {rtp:.1f}%")
    await message.answer("<b>🎲 По играм</b>\n" + ("\n".join(lines) if lines else "Нет данных"), parse_mode="HTML")

@dp.message(Command("atop"))
async def cmd_atop(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(days=30)).isoformat()
    r = await sb(supabase.table("game_rounds").select("user_id, profit, profiles(telegram_id, first_name)")
                 .gte("created_at", since))
    agg = {}
    for row in r.data or []:
        uid = row["user_id"]; pr = row.get("profiles") or {}
        a = agg.setdefault(uid, {"name": pr.get("first_name") or str(pr.get("telegram_id")), "profit": 0.0, "games": 0})
        a["profit"] += float(row["profit"]); a["games"] += 1
    items = sorted(agg.items(), key=lambda x: -x[1]["profit"])[:15]
    lines = [f"{i+1}. <b>{a['name']}</b> — {a['profit']:+.2f} ({a['games']} игр)" for i, (uid, a) in enumerate(items)]
    await message.answer("<b>🏆 Топ профит (30д)</b>\n" + ("\n".join(lines) if lines else "Нет"), parse_mode="HTML")

@dp.message(Command("atopdep"))
async def cmd_atopdep(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(days=30)).isoformat()
    r = await sb(supabase.table("transactions").select("user_id, amount, profiles(telegram_id, first_name)")
                 .eq("type", "deposit").eq("status", "completed").gte("created_at", since))
    agg = {}
    for row in r.data or []:
        uid = row["user_id"]; pr = row.get("profiles") or {}
        a = agg.setdefault(uid, {"name": pr.get("first_name") or str(pr.get("telegram_id")), "sum": 0.0})
        a["sum"] += float(row["amount"])
    items = sorted(agg.items(), key=lambda x: -x[1]["sum"])[:15]
    lines = [f"{i+1}. <b>{a['name']}</b> — {a['sum']:.2f}" for i, (uid, a) in enumerate(items)]
    await message.answer("<b>💎 Топ депозитов (30д)</b>\n" + ("\n".join(lines) if lines else "Нет"), parse_mode="HTML")

@dp.message(Command("atopwd"))
async def cmd_atopwd(message: Message):
    if not admin_only(message): return
    since = (datetime.now(timezone.utc) - timedelta(days=30)).isoformat()
    r = await sb(supabase.table("transactions").select("user_id, amount, profiles(telegram_id, first_name)")
                 .eq("type", "withdraw").eq("status", "completed").gte("created_at", since))
    agg = {}
    for row in r.data or []:
        uid = row["user_id"]; pr = row.get("profiles") or {}
        a = agg.setdefault(uid, {"name": pr.get("first_name") or str(pr.get("telegram_id")), "sum": 0.0})
        a["sum"] += float(row["amount"])
    items = sorted(agg.items(), key=lambda x: -x[1]["sum"])[:15]
    lines = [f"{i+1}. <b>{a['name']}</b> — {a['sum']:.2f}" for i, (uid, a) in enumerate(items)]
    await message.answer("<b>📤 Топ выводов (30д)</b>\n" + ("\n".join(lines) if lines else "Нет"), parse_mode="HTML")

@dp.message(Command("arp"))
async def cmd_arp(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"📊 RTP: <b>{100-HOUSE_EDGE*100:.2f}%</b>\n\n"
        f"🎲 Кубик (число) ×5.76 · (чёт/нечет, 1-3/4-6) ×1.92\n"
        f"🏀 Баскет — число ×4.8 · 3-5/1-2 ×1.6\n"
        f"🎯 Дартс — красное 1-2 ×2.88 · белое 3-5 ×1.92 · центр 6 ×5.76\n"
        f"⚽ Футбол — гол 4-5 ×2.4 · мимо 1-3 ×1.6 · число ×4.8\n"
        f"💥 Crash · 💎 Mines · 🎡 Рулетка · 🃏 BJ · 🎰 Plinko · 🗼 Tower\n"
        f"Всё в диапазоне ~{(1-HOUSE_EDGE)*100:.2f}%",
        parse_mode="HTML")

@dp.message(Command("atx"))
async def cmd_atx(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/atx <id>")
    p = await admin_get_user(message, command.args)
    if not p: return await message.answer("Юзер не найден")
    r = await sb(supabase.table("transactions").select("*").eq("user_id", p["id"])
                 .order("created_at", desc=True).limit(20))
    if not r.data: return await message.answer("Транзакций нет")
    lines = []
    for x in r.data:
        dt = datetime.fromisoformat(x["created_at"].replace("Z", "+00:00")).strftime("%d.%m %H:%M")
        lines.append(f"• {dt} · {x['type']} · {float(x['amount']):.2f} · {x['status']}")
    await message.answer(f"<b>💸 Транзы {p['telegram_id']}</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("atxlast"))
async def cmd_atxlast(message: Message, command: CommandObject):
    if not admin_only(message): return
    n = 20
    if command.args:
        try: n = min(50, int(command.args))
        except: pass
    r = await sb(supabase.table("transactions").select("*").order("created_at", desc=True).limit(n))
    if not r.data: return await message.answer("Транзакций нет")
    uids = list(set(x["user_id"] for x in r.data))
    prof = await sb(supabase.table("profiles").select("id, telegram_id, first_name").in_("id", uids))
    nm = {p["id"]: (p.get("first_name") or str(p.get("telegram_id"))) for p in prof.data or []}
    lines = []
    for x in r.data:
        dt = datetime.fromisoformat(x["created_at"].replace("Z", "+00:00")).strftime("%d.%m %H:%M")
        lines.append(f"• {dt} <b>{nm.get(x['user_id'], '?')}</b> · {x['type']} · {float(x['amount']):.2f}")
    await message.answer("<b>💸 Последние</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("arefund"))
async def cmd_arefund(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/arefund <tx_id>")
    tx_id = command.args.strip()
    r = await sb(supabase.table("transactions").select("*").eq("id", tx_id))
    if not r.data: return await message.answer("Не найдена")
    tx = r.data[0]
    if tx["status"] != "completed": return await message.answer(f"Статус {tx['status']}, нельзя")
    amt = float(tx["amount"])
    refund = -amt if tx["type"] in ("deposit", "win", "bonus", "ref_reward") else amt
    await sb_rpc("change_balance", {"p_user_id": tx["user_id"], "p_delta": refund})
    await sb(supabase.table("transactions").insert({
        "user_id": tx["user_id"], "type": "admin", "amount": abs(refund),
        "currency": "USDT", "status": "completed",
        "meta": {"by": message.from_user.id, "action": "refund", "orig_tx": tx_id}}))
    await message.answer(f"✅ Возврат {abs(refund):.2f}")

# ================== PROMO ADMIN ==================
@dp.message(Command("anewpromo"))
async def cmd_anewpromo(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split()
    if len(parts) < 2:
        return await message.answer(
            "📖 <b>Формат</b>:\n"
            "<code>/anewpromo CODE AMOUNT [WAGER] [USES] [MAX_BET] [GAMES]</code>\n\n"
            "<b>GAMES:</b> all | none | dice,mines,roulette,basket,dart,football,…",
            parse_mode="HTML")
    code = parts[0].upper().strip()
    try: amount = float(parts[1].replace(",", "."))
    except: return await message.answer("Сумма числом")
    if amount <= 0: return await message.answer("Сумма > 0")

    wager = 0.0
    if len(parts) >= 3:
        try: wager = float(parts[2].replace(",", ".").rstrip("xX"))
        except: return await message.answer("Вейджер числом (например 40)")
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
        g = parts[5].strip().lower()
        if g == "all": allowed_games = None
        elif g == "none": allowed_games = []
        else:
            allowed_games = [x.strip() for x in g.split(",") if x.strip()]
            invalid = [x for x in allowed_games if x not in GAMES_ENABLED]
            if invalid:
                return await message.answer(f"❌ Неизвестные игры: {', '.join(invalid)}")

    try:
        await sb(supabase.table("promo_codes").insert({
            "code": code, "amount": amount,
            "wager_mult": wager, "max_uses": max_uses,
            "max_bet": max_bet, "allowed_games": allowed_games,
            "created_by": message.from_user.id,
        }))
        txt = f"✅ <b>Промокод создан</b>\nКод: <code>{code}</code>\nБонус: <b>{amount} ₮</b>\n"
        if wager > 0:
            txt += f"Вейджер: <b>×{wager}</b> (= {amount*wager:.2f} ₮)\n"
            if max_bet: txt += f"Макс. ставка: <b>{max_bet} ₮</b>\n"
        else:
            txt += "Без вейджера 🎉\n"
        if allowed_games is None: txt += "Игры: <b>все</b>\n"
        elif allowed_games == []: txt += "Игры: <b>только вывод</b>\n"
        else: txt += f"Игры: <b>{', '.join(allowed_games)}</b>\n"
        txt += f"Активаций: {'∞' if not max_uses else max_uses}"
        await message.answer(txt, parse_mode="HTML")
    except Exception as e:
        await message.answer(f"❌ {e}")

@dp.message(Command("alistpromos"))
async def cmd_alistpromos(message: Message):
    if not admin_only(message): return
    r = await sb(supabase.table("promo_codes").select("*").order("created_at", desc=True).limit(20))
    if not r.data: return await message.answer("Промокодов нет")
    lines = []
    for p in r.data:
        uses = f"{p['uses']}/{p['max_uses']}" if p['max_uses'] else f"{p['uses']}/∞"
        w = p.get("wager_mult") or 0
        w_txt = f"×{w:.0f}" if w > 0 else "—"
        ag = p.get("allowed_games")
        g_txt = "все" if ag is None else ("нет" if ag == [] else ",".join(ag))
        lines.append(f"• <code>{p['code']}</code> · {float(p['amount']):.2f} ₮ · вейджер {w_txt} · игры: {g_txt} · {uses}")
    await message.answer("<b>🎟 Промокоды:</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("adelpromo"))
async def cmd_adelpromo(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/adelpromo CODE")
    code = command.args.strip().upper()
    try:
        await sb(supabase.table("promo_codes").delete().eq("code", code))
        await message.answer(f"✅ <code>{code}</code> удалён", parse_mode="HTML")
    except Exception as e: await message.answer(f"❌ {e}")

@dp.message(Command("adelallpromos"))
async def cmd_adelallpromos(message: Message):
    if not admin_only(message): return
    await sb(supabase.table("promo_codes").delete().neq("code", "__none__"))
    await message.answer("✅ Все промокоды удалены")

@dp.message(Command("apromoinfo"))
async def cmd_apromoinfo(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/apromoinfo CODE")
    code = command.args.strip().upper()
    r = await sb(supabase.table("promo_codes").select("*").eq("code", code))
    if not r.data: return await message.answer("Не найден")
    p = r.data[0]
    uses = await sb(supabase.table("promo_uses").select("user_id, amount").eq("code", code))
    lines = [f"• user {str(u['user_id'])[:8]} — {float(u['amount']):.2f}" for u in uses.data or []]
    w = float(p.get("wager_mult") or 0)
    ag = p.get("allowed_games")
    games_txt = "все" if ag is None else ("нет (только вывод)" if ag == [] else ", ".join(ag))
    await message.answer(
        f"<b>🎟 {code}</b>\nБонус: <b>{float(p['amount']):.2f} ₮</b>\n"
        f"Вейджер: <b>×{w:.0f}</b>" + (f" (= {float(p['amount'])*w:.2f} ₮)" if w > 0 else " (нет)") + "\n"
        f"Макс. ставка: <b>{float(p['max_bet']) if p.get('max_bet') else '—'}</b>\n"
        f"Игры: <b>{games_txt}</b>\n"
        f"Активаций: {p['uses']}/{p['max_uses'] or '∞'}\n\n"
        f"<b>Активировали:</b>\n" + ("\n".join(lines) if lines else "—"),
        parse_mode="HTML")

@dp.message(Command("apromogames"))
async def cmd_apromogames(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2:
        return await message.answer(
            "/apromogames CODE all|none|dice,mines\n"
            f"Доступные: {', '.join(GAMES_ENABLED.keys())}", parse_mode="HTML")
    code = parts[0].upper().strip()
    val = parts[1].strip().lower()
    r = await sb(supabase.table("promo_codes").select("code").eq("code", code))
    if not r.data: return await message.answer(f"❌ Промокод <code>{code}</code> не найден", parse_mode="HTML")
    if val == "all": new_val, label = None, "все игры"
    elif val == "none": new_val, label = [], "только вывод"
    else:
        games = [g.strip().lower() for g in val.replace(" ", "").split(",") if g.strip()]
        invalid = [g for g in games if g not in GAMES_ENABLED]
        if invalid: return await message.answer(f"❌ Неизвестные игры: {', '.join(invalid)}")
        if not games: return await message.answer("Пустой список")
        new_val, label = games, ", ".join(games)
    await sb(supabase.table("promo_codes").update({"allowed_games": new_val}).eq("code", code))
    await message.answer(f"✅ <code>{code}</code> → <b>{label}</b>", parse_mode="HTML")

@dp.message(Command("asetbonusgames"))
async def cmd_asetbonusgames(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2:
        return await message.answer("/asetbonusgames <id> all|none|dice,mines")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Юзер не найден")
    val = parts[1].strip().lower()
    if val == "all": new_val, label = None, "все игры"
    elif val == "none": new_val, label = [], "только вывод"
    else:
        games = [g.strip().lower() for g in val.replace(" ", "").split(",") if g.strip()]
        invalid = [g for g in games if g not in GAMES_ENABLED]
        if invalid: return await message.answer(f"❌ Неизвестные: {', '.join(invalid)}")
        new_val, label = games, ", ".join(games)
    await sb(supabase.table("profiles").update({"bonus_allowed_games": new_val}).eq("id", p["id"]))
    await message.answer(f"✅ {p['telegram_id']} → <b>{label}</b>", parse_mode="HTML")

@dp.message(Command("awager"))
async def cmd_awager(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/awager <id>")
    p = await admin_get_user(message, command.args.strip())
    if not p: return await message.answer("Юзер не найден")
    if not p.get("bonus_active"):
        return await message.answer(f"У {p['telegram_id']} нет активного бонуса")
    req = float(p.get("wager_required") or 0)
    prog = float(p.get("wager_progress") or 0)
    pct = (prog / req * 100) if req > 0 else 0
    ag = p.get("bonus_allowed_games")
    games_txt = "все" if ag is None else ("нет (только вывод)" if ag == [] else ", ".join(ag))
    await message.answer(
        f"🎰 <b>Вейджер {p['telegram_id']}</b>\n"
        f"Код: <code>{p.get('bonus_code') or '—'}</code>\n"
        f"Бонус: {float(p.get('bonus_amount') or 0):.2f} ₮\n"
        f"Отыграно: <b>{prog:.2f} / {req:.2f}</b> ({pct:.1f}%)\n"
        f"Осталось: {max(0, req - prog):.2f} ₮\n"
        f"Игры: <b>{games_txt}</b>",
        parse_mode="HTML")

@dp.message(Command("aresetwager"))
async def cmd_aresetwager(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aresetwager <id>")
    p = await admin_get_user(message, command.args.strip())
    if not p: return await message.answer("Юзер не найден")
    await sb(supabase.table("profiles").update({
        "bonus_active": False, "wager_required": 0,
        "wager_progress": 0, "bonus_amount": 0,
        "bonus_code": None, "bonus_max_bet": None,
        "bonus_allowed_games": None}).eq("id", p["id"]))
    await message.answer(f"✅ Вейджер сброшен для {p['telegram_id']}")

# ================== BROADCAST ==================
@dp.message(Command("abroadcast"))
async def cmd_abroadcast(message: Message, command: CommandObject, state: FSMContext):
    if not admin_only(message): return
    if not command.args:
        await state.set_state(AdminInput.broadcast)
        return await message.answer("✍️ Отправь текст (или /cancel)")
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
    if not text: return await message.answer("Пустой текст")
    users = (await sb(supabase.table("profiles").select("telegram_id"))).data or []
    await message.answer(f"📢 Рассылка на {len(users)}…")
    ok = fail = 0
    for u in users:
        try: await bot.send_message(int(u["telegram_id"]), text); ok += 1
        except: fail += 1
        await asyncio.sleep(0.05)
    await message.answer(f"✅ {ok} доставлено, {fail} ошибок")

@dp.message(Command("apush"))
async def cmd_apush(message: Message, command: CommandObject):
    if not admin_only(message): return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2: return await message.answer("/apush <id> <текст>")
    p = await admin_get_user(message, parts[0])
    if not p: return await message.answer("Не найден")
    try:
        await bot.send_message(p["telegram_id"], f"📢 {parts[1]}")
        await message.answer(f"✅ Отправлено {p['telegram_id']}")
    except Exception as e: await message.answer(f"❌ {e}")

# ================== SETTINGS ==================
@dp.message(Command("asettings"))
async def cmd_asettings(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"<b>⚙️ Настройки</b>\nMIN_BET: {MIN_BET}\nMAX_BET: {MAX_BET}\n"
        f"MIN_DEPOSIT: {MIN_DEPOSIT}\nMIN_WITHDRAW: {MIN_WITHDRAW}\n"
        f"MAX_WITHDRAW_DAILY: {MAX_WITHDRAW_DAILY}\nWITHDRAW_COOLDOWN_MIN: {WITHDRAW_COOLDOWN_MIN}\n"
        f"HOUSE_EDGE: {HOUSE_EDGE}\nRTP: {(1-HOUSE_EDGE)*100:.1f}%\nREFERRAL_SHARE: {REFERRAL_SHARE}\n"
        f"DAILY_BONUS: {DAILY_BONUS}\nBONUS_COOLDOWN_H: {BONUS_COOLDOWN_H}\n"
        f"WAGER_RESET_THRESHOLD: {WAGER_RESET_THRESHOLD}\n"
        f"Maintenance: {'🚫 ON' if MAINTENANCE else '✅ OFF'}\nКанал: {CHANNEL_ID or '— не задан —'}",
        parse_mode="HTML")

@dp.message(Command("asetminbet"))
async def cmd_asetminbet(message: Message, command: CommandObject):
    global MIN_BET
    if not admin_only(message): return
    try: v = float(command.args)
    except: return await message.answer("/asetminbet 0.1")
    if v < 0: return await message.answer(">= 0")
    MIN_BET = v; await message.answer(f"✅ MIN_BET = {v}")

@dp.message(Command("asetmaxbet"))
async def cmd_asetmaxbet(message: Message, command: CommandObject):
    global MAX_BET
    if not admin_only(message): return
    try: v = float(command.args)
    except: return await message.answer("/asetmaxbet 1000")
    MAX_BET = v; await message.answer(f"✅ MAX_BET = {v}")

@dp.message(Command("asetmindep"))
async def cmd_asetmindep(message: Message, command: CommandObject):
    global MIN_DEPOSIT
    if not admin_only(message): return
    try: v = float(command.args)
    except: return await message.answer("/asetmindep 0.1")
    MIN_DEPOSIT = v; await message.answer(f"✅ MIN_DEPOSIT = {v}")

@dp.message(Command("asetminwd"))
async def cmd_asetminwd(message: Message, command: CommandObject):
    global MIN_WITHDRAW
    if not admin_only(message): return
    try: v = float(command.args)
    except: return await message.answer("/asetminwd 0.5")
    MIN_WITHDRAW = v; await message.answer(f"✅ MIN_WITHDRAW = {v}")

@dp.message(Command("asetmaxwd"))
async def cmd_asetmaxwd(message: Message, command: CommandObject):
    global MAX_WITHDRAW_DAILY
    if not admin_only(message): return
    try: v = float(command.args)
    except: return await message.answer("/asetmaxwd 500")
    MAX_WITHDRAW_DAILY = v; await message.answer(f"✅ MAX_WITHDRAW_DAILY = {v}")

@dp.message(Command("asetrtp"))
async def cmd_asetrtp(message: Message, command: CommandObject):
    global HOUSE_EDGE, DICE_PAYOUT, ROUL_RB_PAYOUT, ROUL_DOZEN_PAYOUT, ROUL_NUM_PAYOUT
    if not admin_only(message): return
    if not command.args: return await message.answer("/asetrtp 0.96 (RTP)")
    try: rtp = float(command.args)
    except: return await message.answer("Числом, 0.90–0.99")
    if not (0.90 <= rtp <= 0.99): return await message.answer("RTP от 0.90 до 0.99")
    HOUSE_EDGE = round(1 - rtp, 4)
    DICE_PAYOUT = round(6 * (1 - HOUSE_EDGE), 4)
    ROUL_RB_PAYOUT = round(2 * (1 - HOUSE_EDGE), 4)
    ROUL_DOZEN_PAYOUT = round(3 * (1 - HOUSE_EDGE), 4)
    ROUL_NUM_PAYOUT = round(36 * (1 - HOUSE_EDGE), 4)
    await message.answer(f"✅ RTP = {rtp*100:.1f}%")

@dp.message(Command("asetref"))
async def cmd_asetref(message: Message, command: CommandObject):
    global REFERRAL_SHARE
    if not admin_only(message): return
    try: v = float(command.args)
    except: return await message.answer("/asetref 0.05")
    if not (0 <= v <= 0.5): return await message.answer("0..0.5")
    REFERRAL_SHARE = v
    await message.answer(f"✅ Рефералка = {v*100:.1f}%")

@dp.message(Command("asetcooldown"))
async def cmd_asetcooldown(message: Message, command: CommandObject):
    global WITHDRAW_COOLDOWN_MIN
    if not admin_only(message): return
    try: v = int(command.args)
    except: return await message.answer("/asetcooldown 15")
    if v < 0: return await message.answer(">= 0")
    WITHDRAW_COOLDOWN_MIN = v
    await message.answer(f"✅ Кулдаун = {v} мин")

@dp.message(Command("amaintenance"))
async def cmd_amaintenance(message: Message, command: CommandObject):
    global MAINTENANCE
    if not admin_only(message): return
    if not command.args:
        return await message.answer(f"Maintenance: {'ON' if MAINTENANCE else 'OFF'}\n/amaintenance on|off")
    v = command.args.strip().lower()
    if v in ("on", "1", "true", "yes"): MAINTENANCE = True
    elif v in ("off", "0", "false", "no"): MAINTENANCE = False
    else: return await message.answer("on или off")
    await message.answer(f"✅ Maintenance = {'ON' if MAINTENANCE else 'OFF'}")

@dp.message(Command("ahealth"))
async def cmd_ahealth(message: Message):
    if not admin_only(message): return
    try:
        await sb(supabase.table("profiles").select("id").limit(1))
        sb_status = "✅ OK"
    except Exception as e: sb_status = f"❌ {type(e).__name__}"
    try:
        async with httpx.AsyncClient(timeout=8) as http:
            rr = await http.get(f"{XROCKET_API_BASE}/api/v1/me",
                                headers={"Authorization": f"Bearer {XROCKET_API_KEY}"})
            xr_status = f"✅ {rr.status_code}" if rr.status_code < 500 else f"⚠️ {rr.status_code}"
    except Exception as e: xr_status = f"❌ {type(e).__name__}"
    active_count = len((await sb(supabase.table("active_rounds").select("user_id"))).data or [])
    enabled = sum(1 for v in GAMES_ENABLED.values() if v)
    await message.answer(
        f"<b>🩺 Health</b>\nSupabase: {sb_status}\nXroket: {xr_status}\n"
        f"Crash: <b>{crash_state['status']}</b>\nАктивных игр: <b>{active_count}</b>\n"
        f"Игр вкл: <b>{enabled}/{len(GAMES_ENABLED)}</b>\n"
        f"Канал: {CHANNEL_ID or '— не задан —'}\n"
        f"Maintenance: {'🚫 ON' if MAINTENANCE else '✅ OFF'}\n"
        f"Uptime: {int(time.time() - START_TIME)}s", parse_mode="HTML")

@dp.message(Command("alogs"))
async def cmd_alogs(message: Message, command: CommandObject):
    if not admin_only(message): return
    n = 20
    if command.args:
        try: n = min(100, int(command.args))
        except: pass
    r = await sb(supabase.table("action_log").select("*").order("created_at", desc=True).limit(n))
    if not r.data: return await message.answer("Логов нет")
    uids = list(set(x["user_id"] for x in r.data))
    prof = await sb(supabase.table("profiles").select("id, telegram_id, first_name").in_("id", uids))
    nm = {p["id"]: (p.get("first_name") or str(p.get("telegram_id"))) for p in prof.data or []}
    lines = []
    for x in r.data:
        dt = datetime.fromisoformat(x["created_at"].replace("Z", "+00:00")).strftime("%d.%m %H:%M")
        lines.append(f"• {dt} <b>{nm.get(x['user_id'], '?')}</b> — {x['action']}")
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
    await message.answer(f"✅ Логи старше {days}д удалены")

@dp.message(Command("aadmins"))
async def cmd_aadmins(message: Message):
    if not admin_only(message): return
    lines = [f"• <code>{aid}</code>" for aid in sorted(ADMIN_IDS)]
    await message.answer("<b>🛡 Админы:</b>\n" + "\n".join(lines), parse_mode="HTML")

# ================== USER COMMANDS ==================
@dp.message(Command("start"))
async def cmd_start(message: Message, command: CommandObject, state: FSMContext):
    if not await is_subscribed(message.from_user.id):
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
    extra = "\n\n🔐 <i>У тебя доступ к /admin</i>" if is_admin(message.from_user.id) else ""
    bonus_line = f"\n🎁 Ежедневный бонус: <b>{DAILY_BONUS} ₮</b>" if DAILY_BONUS > 0 else ""
    cur = p.get("preferred_currency") or "USDT"
    await message.answer(
        f"👋 <b>Добро пожаловать в GoldCash!</b>\n\n"
        f"💎 Баланс: <b>{float(p['balance']):.2f} {cur}</b>{bonus_line}\n\n"
        f"<b>Что можно делать:</b>\n"
        f"🎲 Предсказания: 🎲 кубик · 🏀 баскет · 🎯 дартс · ⚽ футбол\n"
        f"🌐 Mini App — Mines, Roulette, Plinko, Blackjack, Tower, Crash\n"
        f"💰 Пополнение и вывод через @xRocket\n"
        f"👥 Друзья: {REFERRAL_SHARE*100:.0f}% от их проигрыша\n\n"
        f"Команды: /help{extra}",
        reply_markup=main_menu(), parse_mode="HTML")

@dp.callback_query(F.data == "check_sub")
async def cb_check_sub(cb: CallbackQuery, state: FSMContext):
    if not await is_subscribed(cb.from_user.id):
        return await cb.answer("❌ Ты ещё не подписан на канал", show_alert=True)
    await cb.answer("✅ Подписка подтверждена", show_alert=False)
    try: await cb.message.delete()
    except: pass
    await state.clear()
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    await cb.message.answer(
        f"👋 <b>Добро пожаловать в GoldCash!</b>\n\n💎 Баланс: <b>{float(p['balance']):.2f} {cur}</b>\n\n"
        f"Команды: /help",
        reply_markup=main_menu(), parse_mode="HTML")

@dp.message(Command("help"))
async def cmd_help(message: Message):
    await message.answer(
        "📖 <b>GoldCash — справка</b>\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>🎲 Предсказания (в чате)</b>\n"
        "• 🎲 Кубик — 1-6: чёт/нечет, 1-3 / 4-6, точное число\n"
        "• 🏀 Баскетбол — 1-5: забил/промазал, точное\n"
        "• 🎯 Дартс — 1-6: красное 1-2, белое 3-5, центр 6\n"
        "• ⚽ Футбол — 1-5: гол/мимо, точное\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>🌐 Mini App</b>\nMines, Roulette, Plinko, Blackjack, Tower, Crash\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>💰 Платежи</b>\n"
        "• Пополнение/вывод через @xRocket\n"
        f"• После депозита вывод через {WITHDRAW_COOLDOWN_MIN} мин\n"
        f"• Лимит вывода: {MAX_WITHDRAW_DAILY} ₮ / сутки\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        f"<b>👥 Рефералка</b> — {REFERRAL_SHARE*100:.0f}% от проигрыша друзей\n"
        "━━━━━━━━━━━━━━━━━━━\n"
        "<b>Команды</b>\n/balance · /stats · /currency · /promo КОД · /bonus\n\n"
        "<i>RTP 96% · Provably Fair</i>",
        parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("balance"))
async def cmd_balance(message: Message):
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    bonus = ""
    if p.get("bonus_active"):
        bonus = (f"\n🎰 Бонус: {float(p.get('wager_progress') or 0):.2f}"
                 f"/{float(p.get('wager_required') or 0):.2f}")
    await message.answer(f"💎 Баланс: <b>{float(p['balance']):.2f} {cur}</b>{bonus}",
                         parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("stats"))
async def cmd_stats(message: Message):
    p = await get_or_create_profile(message.from_user.model_dump())
    s = await get_user_stats(p["id"])
    await message.answer(fmt_stats(s, float(p["balance"]), message.from_user.first_name),
                         parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("promo"))
async def cmd_promo(message: Message, command: CommandObject):
    if not command.args: return await message.answer("Использование: /promo КОД")
    await try_redeem_promo(message, command.args.strip().upper())

@dp.message(Command("currency"))
async def cmd_currency(message: Message, command: CommandObject):
    if not command.args:
        return await message.answer(f"Валюты: {', '.join(SUPPORTED_CURRENCIES)}\n/currency TON")
    cur = command.args.strip().upper()
    if cur not in SUPPORTED_CURRENCIES: return await message.answer("❌ Неподдерживаемая валюта")
    p = await get_or_create_profile(message.from_user.model_dump())
    await sb(supabase.table("profiles").update({"preferred_currency": cur}).eq("id", p["id"]))
    await message.answer(f"✅ Валюта: <b>{cur}</b>", parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("bonus"))
async def cmd_bonus(message: Message):
    if DAILY_BONUS <= 0:
        return await message.answer("🎁 Бонус отключён")
    p = await get_or_create_profile(message.from_user.model_dump())
    await ensure_not_banned(p)
    last = p.get("last_bonus_at")
    if last:
        try:
            dt = datetime.fromisoformat(str(last).replace("Z", "+00:00"))
            left = BONUS_COOLDOWN_H * 3600 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0:
                m = int(left // 60)
                return await message.answer(f"⏳ Следующий бонус через {m} мин.")
        except: pass
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": DAILY_BONUS})
    await sb(supabase.table("profiles").update(
        {"last_bonus_at": datetime.now(timezone.utc).isoformat()}).eq("id", p["id"]))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": DAILY_BONUS,
        "currency": "USDT", "status": "completed", "meta": {"source": "daily"}}))
    await message.answer(f"🎁 +<b>{DAILY_BONUS}</b> ₮", parse_mode="HTML",
                         reply_markup=back_kb())

async def try_redeem_promo(message: Message, code: str):
    p = await get_or_create_profile(message.from_user.model_dump())
    if p.get("bonus_active"):
        return await message.answer("🎰 Сначала отыграй текущий бонус")
    r = await sb(supabase.table("promo_codes").select("*").eq("code", code))
    if not r.data: return await message.answer("❌ Промокод не найден")
    promo = r.data[0]
    if promo.get("max_uses") and promo["uses"] >= promo["max_uses"]:
        return await message.answer("❌ Промокод исчерпан")
    used = await sb(supabase.table("promo_uses").select("id").eq("code", code).eq("user_id", p["id"]))
    if used.data: return await message.answer("❌ Ты уже использовал")
    amount = float(promo["amount"])
    if promo.get("max_bonus"):
        amount = min(amount, float(promo["max_bonus"]))
    wager_mult = float(promo.get("wager_mult") or 0)
    wager_required = round(amount * wager_mult, 8) if wager_mult > 0 else 0
    max_bet = promo.get("max_bet")
    allowed = promo.get("allowed_games")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    await sb(supabase.table("profiles").update({
        "bonus_active": wager_required > 0,
        "bonus_amount": amount, "wager_required": wager_required, "wager_progress": 0,
        "bonus_code": code, "bonus_max_bet": float(max_bet) if max_bet else None,
        "bonus_allowed_games": allowed,
    }).eq("id", p["id"]))
    await sb(supabase.table("promo_uses").insert({"code": code, "user_id": p["id"], "amount": amount}))
    await sb(supabase.table("promo_codes").update({"uses": promo["uses"] + 1}).eq("code", code))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": amount,
        "currency": "USDT", "status": "completed",
        "meta": {"source": "promo", "code": code, "wager": wager_mult}}))
    txt = f"✅ +<b>{amount}</b> ₮\n"
    if wager_required > 0:
        txt += f"🎰 Вейджер: <b>×{wager_mult}</b> (= {wager_required:.2f} ₮)\n"
        if max_bet: txt += f"⚠️ Макс. ставка: {float(max_bet)} ₮\n"
    if allowed is None: txt += "🎮 Все игры доступны"
    elif allowed == []: txt += "🚫 Игры заблокированы (только вывод)"
    else: txt += f"🎮 Только: {', '.join(allowed)}"
    await message.answer(txt, parse_mode="HTML")

# ================== PREDICTION GAME FLOW ==================
@dp.callback_query(F.data == "pg:home")
async def cb_pg_home(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await cb.message.edit_text(
        "🎲 <b>Предсказания</b>\n\nВыбери игру:",
        parse_mode="HTML", reply_markup=pred_home_kb())

@dp.callback_query(F.data.startswith("pgm:"))
async def cb_pg_game(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    game = cb.data.split(":")[1]
    if game not in DICE_GAMES: return await cb.answer("Ошибка")
    if not GAMES_ENABLED.get(game, True):
        return await cb.answer(f"⛔ {DICE_GAMES[game]['name']} выключена", show_alert=True)
    g = DICE_GAMES[game]
    await cb.message.edit_text(
        f"{g['emoji']} <b>{g['name']}</b>\nВыбери ставку:",
        parse_mode="HTML", reply_markup=pred_bet_kb(game))

@dp.callback_query(F.data.startswith("pgcb:"))
async def cb_pg_custom_bet(cb: CallbackQuery, state: FSMContext):
    game = cb.data.split(":")[1]
    if game not in DICE_GAMES: return await cb.answer("Ошибка")
    await state.set_state(PredictionInput.custom_bet)
    await state.update_data(game=game)
    await cb.message.edit_text(
        f"✏️ Введи сумму ставки в ₮ (мин. {MIN_BET}, макс. {MAX_BET}):\n"
        f"Или /cancel для отмены.",
        reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="⬅️ Назад", callback_data=f"pgm:{game}")]]))

@dp.message(PredictionInput.custom_bet)
async def fsm_pg_custom_bet(message: Message, state: FSMContext):
    data = await state.get_data()
    game = data.get("game")
    try:
        bet = float((message.text or "").replace(",", ".").strip())
    except:
        return await message.answer("❌ Не число")
    if not (MIN_BET <= bet <= MAX_BET):
        return await message.answer(f"❌ Ставка {MIN_BET}..{MAX_BET}")
    await state.clear()
    g = DICE_GAMES[game]
    await message.answer(
        f"{g['emoji']} <b>{g['name']}</b> · ставка <b>{bet} ₮</b>\nВыбери предсказание:",
        parse_mode="HTML", reply_markup=pred_type_kb(game, bet))

@dp.callback_query(F.data.startswith("pgb:"))
async def cb_pg_bet(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    _, game, bet_s = cb.data.split(":")
    if game not in DICE_GAMES: return await cb.answer("Ошибка")
    bet = float(bet_s)
    g = DICE_GAMES[game]
    await cb.message.edit_text(
        f"{g['emoji']} <b>{g['name']}</b> · ставка <b>{bet} ₮</b>\nВыбери предсказание:",
        parse_mode="HTML", reply_markup=pred_type_kb(game, bet))

@dp.callback_query(F.data.startswith("pgn:"))
async def cb_pg_numbers(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    _, game, bet_s = cb.data.split(":")
    if game not in DICE_GAMES: return await cb.answer("Ошибка")
    bet = float(bet_s)
    g = DICE_GAMES[game]
    await cb.message.edit_text(
        f"{g['emoji']} <b>{g['name']}</b> · ставка <b>{bet} ₮</b>\n"
        f"Выбери точное число ({g['min']}–{g['max']}):",
        parse_mode="HTML", reply_markup=pred_number_kb(game, bet))

@dp.callback_query(F.data.startswith("pgr:"))
async def cb_pg_run(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    parts = cb.data.split(":")
    game = parts[1]; bet = float(parts[2]); ptype = parts[3]
    pvalue = int(parts[4]) if len(parts) > 4 else None
    if game not in DICE_GAMES: return await cb.answer("Ошибка")
    if not GAMES_ENABLED.get(game, True):
        return await cb.answer(f"⛔ Игра выключена", show_alert=True)

    p = await get_or_create_profile(cb.from_user.model_dump())
    try:
        await ensure_not_banned(p)
        await check_bonus_max_bet(p, bet)
        await check_bonus_game(p, game)
        await check_rate_limit(p["id"], "bet")
    except HTTPException as e:
        return await cb.answer(e.detail, show_alert=True)

    if float(p["balance"]) < bet:
        return await cb.answer("❌ Недостаточно средств", show_alert=True)

    try:
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
        asyncio.create_task(apply_wager_progress(p["id"], bet))
    except Exception as e:
        return await cb.answer(f"Ошибка: {e}", show_alert=True)

    g = DICE_GAMES[game]
    pred_meta = DICE_PREDICTIONS[game][ptype]
    label = pred_meta["label"]
    if ptype == "num": label = f"Число {pvalue}"

    await cb.message.edit_text(
        f"{g['emoji']} <b>{g['name']}</b> · ставка <b>{bet} ₮</b>\n"
        f"Твоё предсказание: <b>{label}</b>\n\n{g['emoji']} Бросаем…",
        parse_mode="HTML")

    try:
        dice_msg = await bot.send_dice(chat_id=cb.message.chat.id, emoji=g["emoji"])
        result = dice_msg.dice.value
        await asyncio.sleep(3.5)
    except Exception as e:
        log.exception("send_dice failed")
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": bet})
        return await cb.message.edit_text(f"❌ Ошибка броска: {e}", reply_markup=back_kb())

    win = eval_prediction(game, result, ptype, pvalue)
    profit = -bet
    payout = 0.0
    if win:
        payout = round(bet * pred_meta["mult"], 8)
        profit = round(payout - bet, 8)
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
            "status": "completed", "meta": {"game": game, "result": result}}))
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))

    await log_round(p["id"], game, bet,
                    {"result": result, "pred": ptype, "value": pvalue, "win": win,
                     "label": label, "mult": pred_meta["mult"]},
                    profit, f"telegram_{game}", 0)

    p2 = await get_or_create_profile(cb.from_user.model_dump())
    balance = float(p2["balance"])

    wager_reset = False
    if not win and balance < WAGER_RESET_THRESHOLD:
        wager_reset = await check_and_reset_wager_if_broke(p2["id"])

    z = zone_label(game, result)
    z_txt = f" ({z})" if z else ""

    if win:
        text = (f"{g['emoji']} <b>Выпало {result}{z_txt}</b>\n"
                f"Твоё: {label}\n"
                f"✅ <b>+{profit:.2f}</b> ₮ (×{pred_meta['mult']})\n\n"
                f"💎 Баланс: <b>{balance:.2f}</b>")
    else:
        text = (f"{g['emoji']} <b>Выпало {result}{z_txt}</b>\n"
                f"Твоё: {label}\n"
                f"❌ <b>−{bet:.2f}</b> ₮\n\n"
                f"💎 Баланс: <b>{balance:.2f}</b>")

    if wager_reset:
        text += "\n\n♻️ <i>Бонус сброшен — не хватило баланса на отыгрыш</i>"

    again_kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔁 Ещё раз", callback_data=f"pgb:{game}:{bet}")],
        [InlineKeyboardButton(text="🎲 Другая игра", callback_data="pg:home"),
         InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])

    try:
        await cb.message.edit_text(text, parse_mode="HTML", reply_markup=again_kb)
    except Exception:
        await bot.send_message(cb.message.chat.id, text, parse_mode="HTML", reply_markup=again_kb)

# ================== MAIN MENU CALLBACKS ==================
@dp.callback_query(F.data == "menu:main")
async def cb_menu(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await cb.message.edit_text("🏠 Главное меню:", reply_markup=main_menu())

@dp.callback_query(F.data == "menu:help")
async def cb_help(cb: CallbackQuery):
    await cb.message.edit_text(
        "📖 <b>Справка</b>\n"
        "🎲 Предсказания — /start → «Предсказания»\n"
        "🌐 Mini App — кнопка в меню\n"
        f"💰 Мин. вывод: {MIN_WITHDRAW} ₮\n"
        f"👥 Рефералка: {REFERRAL_SHARE*100:.0f}%",
        parse_mode="HTML", reply_markup=back_kb())

@dp.callback_query(F.data == "menu:stats")
async def cb_stats(cb: CallbackQuery):
    p = await get_or_create_profile(cb.from_user.model_dump())
    s = await get_user_stats(p["id"])
    await cb.message.edit_text(fmt_stats(s, float(p["balance"]), cb.from_user.first_name),
                               parse_mode="HTML", reply_markup=back_kb())

@dp.callback_query(F.data == "menu:deposit")
async def cb_deposit(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    await cb.message.edit_text(f"💰 <b>Пополнение</b>\nВалюта: <b>{cur}</b> (/currency)\nМин: {MIN_DEPOSIT}",
                               parse_mode="HTML", reply_markup=deposit_kb())

@dp.callback_query(F.data.startswith("dep:"))
async def cb_dep_amount(cb: CallbackQuery, state: FSMContext):
    val = cb.data.split(":")[1]
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if val == "custom":
        await state.set_state(AmountInput.deposit)
        await cb.message.edit_text(f"💰 Введи сумму в {cur} (мин. {MIN_DEPOSIT}).",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="⬅️ Назад", callback_data="menu:deposit")]]))
        return
    amount = float(val)
    try: inv = await create_deposit_invoice(p, amount, cur)
    except Exception as e: return await cb.answer(f"❌ {e}", show_alert=True)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💳 Оплатить", url=inv["link"])],
        [InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])
    await cb.message.edit_text(f"💰 Счёт на <b>{amount} {cur}</b>.", parse_mode="HTML", reply_markup=kb)

@dp.callback_query(F.data == "menu:withdraw")
async def cb_withdraw(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    p = await get_or_create_profile(cb.from_user.model_dump())
    bal = float(p["balance"]); cur = p.get("preferred_currency") or "USDT"
    spent = await daily_withdrawn(p["id"]); left = MAX_WITHDRAW_DAILY - spent
    warn = ""
    if p.get("bonus_active"):
        req = float(p.get("wager_required") or 0)
        prog = float(p.get("wager_progress") or 0)
        if prog < req:
            warn = f"\n🎰 ⚠️ Бонус: отыграй ещё {req-prog:.2f} ₮"
    hint = f"\n\n⚠️ Баланс {bal:.2f}, минимум {MIN_WITHDRAW}." if bal < MIN_WITHDRAW else ""
    await cb.message.edit_text(
        f"💸 <b>Вывод в {cur}</b>\nБаланс: <b>{bal:.2f}</b>\n"
        f"Лимит/сутки: <b>{max(0,left):.2f}</b> из {MAX_WITHDRAW_DAILY:.0f}\n"
        f"Минимум: {MIN_WITHDRAW}{hint}{warn}\n\n"
        f"<b>⚠️ Средства приходят на @xRocket.</b>\nВыбери сумму:",
        parse_mode="HTML", reply_markup=withdraw_kb(bal))

@dp.callback_query(F.data.startswith("wd:"))
async def cb_wd_amount(cb: CallbackQuery, state: FSMContext):
    val = cb.data.split(":")[1]
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if val == "custom":
        await state.set_state(AmountInput.withdraw)
        await cb.message.edit_text(f"💸 Введи сумму в {cur} (мин. {MIN_WITHDRAW}).",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="⬅️ Назад", callback_data="menu:withdraw")]]))
        return
    amount = float(val)
    if amount < MIN_WITHDRAW: return await cb.answer(f"Минимум {MIN_WITHDRAW}", show_alert=True)
    if float(p["balance"]) < amount: return await cb.answer("Недостаточно", show_alert=True)
    await check_and_reset_wager_if_broke(p["id"])
    p = await get_or_create_profile(cb.from_user.model_dump())
    try:
        await check_wager_lock(p)
    except HTTPException as e:
        return await cb.answer(e.detail, show_alert=True)
    await cb.message.edit_text("⏳ Обработка…", reply_markup=back_kb())
    try: await do_withdraw(p, cb.from_user.id, amount, cur)
    except HTTPException as e: return await cb.message.edit_text(f"❌ {e.detail}", reply_markup=back_kb())
    except Exception as e:
        log.exception("payout failed"); return await cb.message.edit_text(f"❌ {e}", reply_markup=back_kb())
    await cb.message.edit_text(f"✅ Выплата <b>{amount} {cur}</b>.", parse_mode="HTML", reply_markup=back_kb())

@dp.message(AmountInput.deposit)
async def fsm_deposit_amount(message: Message, state: FSMContext):
    try: amount = float(message.text.replace(",", ".").strip())
    except: return await message.answer("❌ Не число.")
    if amount < MIN_DEPOSIT: return await message.answer(f"❌ Минимум {MIN_DEPOSIT}")
    if amount > MAX_DEPOSIT: return await message.answer(f"❌ Макс {MAX_DEPOSIT}")
    await state.clear()
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    try: inv = await create_deposit_invoice(p, amount, cur)
    except Exception as e: return await message.answer(f"❌ {e}", reply_markup=back_kb())
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💳 Оплатить", url=inv["link"])],
        [InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])
    await message.answer(f"💰 Счёт на <b>{amount} {cur}</b>.", parse_mode="HTML", reply_markup=kb)

@dp.message(AmountInput.withdraw)
async def fsm_withdraw_amount(message: Message, state: FSMContext):
    try: amount = float(message.text.replace(",", ".").strip())
    except: return await message.answer("❌ Не число.")
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if amount < MIN_WITHDRAW: return await message.answer(f"❌ Минимум {MIN_WITHDRAW}")
    if float(p["balance"]) < amount:
        return await message.answer(f"❌ Баланс: <b>{float(p['balance']):.2f}</b>", parse_mode="HTML")
    await check_and_reset_wager_if_broke(p["id"])
    p = await get_or_create_profile(message.from_user.model_dump())
    try:
        await check_wager_lock(p)
    except HTTPException as e:
        return await message.answer(f"❌ {e.detail}")
    await state.clear()
    msg = await message.answer("⏳ Обработка…")
    try: await do_withdraw(p, message.from_user.id, amount, cur)
    except HTTPException as e: return await msg.edit_text(f"❌ {e.detail}", reply_markup=back_kb())
    except Exception as e: return await msg.edit_text(f"❌ {e}", reply_markup=back_kb())
    await msg.edit_text(f"✅ Выплата <b>{amount} {cur}</b>.", parse_mode="HTML", reply_markup=back_kb())

def deposit_kb():
    amounts = [1, 5, 10, 25, 50, 100]
    rows = [[InlineKeyboardButton(text=f"{a} ₮", callback_data=f"dep:{a}") for a in amounts[i:i+3]]
            for i in range(0, len(amounts), 3)]
    rows.append([InlineKeyboardButton(text="✏️ Своя сумма", callback_data="dep:custom")])
    rows.append([InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def withdraw_kb(balance):
    candidates = [1, 5, 10, 25, 50, 100, 250, 500]
    amounts = [a for a in candidates if a <= balance and a >= MIN_WITHDRAW]
    rows = []
    if amounts:
        for i in range(0, len(amounts), 3):
            rows.append([InlineKeyboardButton(text=f"{a} ₮", callback_data=f"wd:{a}") for a in amounts[i:i+3]])
    rows.append([InlineKeyboardButton(text="✏️ Своя сумма", callback_data="wd:custom")])
    rows.append([InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

@dp.callback_query(F.data == "menu:ref")
async def cb_ref_menu(cb: CallbackQuery):
    p = await get_or_create_profile(cb.from_user.model_dump())
    info = referral_info_sync(p)
    share_url = f"https://t.me/share/url?url={info['link']}&text=Играю в GoldCash!"
    invited = (await sb(supabase.table("profiles").select("first_name, username, created_at")
                        .eq("referrer_id", p["id"]).order("created_at", desc=True).limit(50))).data or []
    text = (f"👥 <b>Приглашай друзей</b>\n\n<b>{REFERRAL_SHARE*100:.0f}%</b> от проигрыша!\n\n"
            f"👤 Приглашено: <b>{len(invited)}</b>\n💰 Заработано: <b>{float(p.get('ref_earnings') or 0):.2f}</b>\n\n"
            f"Ссылка:\n<code>{info['link']}</code>")
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📤 Поделиться", url=share_url)],
        [InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])
    await cb.message.edit_text(text, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)

# ================== MIDDLEWARE ==================
dp.message.middleware(SubscriptionMiddleware())
dp.callback_query.middleware(SubscriptionMiddleware())

# ================== FASTAPI ==================
@asynccontextmanager
async def lifespan(app):
    global BOT_USERNAME
    me = await bot.get_me(); BOT_USERNAME = me.username
    log.info("start · house_edge=%.3f · admins=%s · bot=@%s · channel=%s · daily_bonus=%s · wager_reset<%.2f",
             HOUSE_EDGE, ADMIN_IDS, BOT_USERNAME, CHANNEL_ID or "—", DAILY_BONUS, WAGER_RESET_THRESHOLD)
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
        "payouts": {"dice": DICE_PAYOUT, "roulette_rb": ROUL_RB_PAYOUT,
                    "roulette_dozen": ROUL_DOZEN_PAYOUT, "roulette_number": ROUL_NUM_PAYOUT,
                    "plinko": PLINKO_MULTS},
        "dice_predictions": DICE_PREDICTIONS,
    }

@app.post("/api/auth")
async def auth(user: dict = Depends(get_current_user)):
    return await get_or_create_profile(user)

def _profile_sync(user):
    tg_id = int(user["id"])
    r = supabase.table("profiles").select("*").eq("telegram_id", tg_id).execute()
    p = r.data[0] if r.data else supabase.table("profiles").insert({
        "telegram_id": tg_id, "username": user.get("username"),
        "first_name": user.get("first_name"), "preferred_currency": "USDT"}).execute().data[0]
    try:
        tx = supabase.table("transactions").select("type, amount, status").eq("user_id", p["id"]).execute().data or []
        rounds = supabase.table("game_rounds").select("id").eq("user_id", p["id"]).execute().data or []
    except Exception: tx, rounds = [], []
    dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    wins = sum(float(t["amount"]) for t in tx if t["type"] == "win")
    bets = sum(float(t["amount"]) for t in tx if t["type"] == "bet")
    return {"id": p["id"], "telegram_id": p["telegram_id"], "username": p.get("username"),
            "first_name": p.get("first_name"), "balance": float(p["balance"]),
            "client_seed": p.get("client_seed") or "", "nonce": int(p.get("nonce") or 0),
            "ref_earnings": float(p.get("ref_earnings") or 0),
            "preferred_currency": p.get("preferred_currency") or "USDT",
            "is_banned": bool(p.get("is_banned")),
            "bonus": _bonus_info(p),
            "stats": {"total_games": len(rounds), "total_wagered": round(bets, 2),
                      "total_profit": round(wins - bets, 2), "best_mult": 1.0,
                      "deposits": round(dep, 2), "withdrawals": round(wd, 2), "wins": round(wins, 2)}}

@app.get("/api/profile")
async def profile(user: dict = Depends(get_current_user)):
    try: return await asyncio.to_thread(_profile_sync, user)
    except Exception:
        log.exception("profile endpoint failed"); raise HTTPException(500, "profile error")

@app.post("/api/profile/currency")
async def set_currency(body: dict, user: dict = Depends(get_current_user)):
    currency = (body.get("currency") or "").upper()
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "неподдерживаемая валюта")
    p = await get_or_create_profile(user)
    await sb(supabase.table("profiles").update({"preferred_currency": currency}).eq("id", p["id"]))
    return {"ok": True, "currency": currency}

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
                        .eq("referrer_id", p["id"]).order("created_at", desc=True).limit(50))).data or []
    info["earnings"] = float(p.get("ref_earnings") or 0)
    info["invited_count"] = len(invited)
    info["invited"] = [{"name": u.get("first_name") or u.get("username") or "anon",
                        "joined": u.get("created_at")} for u in invited]
    return info

@app.post("/api/promo/redeem")
async def api_promo_redeem(body: dict, user: dict = Depends(get_current_user)):
    code = (body.get("code") or "").strip().upper()
    if not code: raise HTTPException(400, "пустой код")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    if p.get("bonus_active"):
        raise HTTPException(400, "Сначала отыграй текущий бонус")
    r = await sb(supabase.table("promo_codes").select("*").eq("code", code))
    if not r.data: raise HTTPException(404, "промокод не найден")
    promo = r.data[0]
    exp = promo.get("expires_at")
    if exp:
        try:
            exp_dt = datetime.fromisoformat(str(exp).replace("Z", "+00:00"))
            if datetime.now(timezone.utc) > exp_dt: raise HTTPException(400, "промокод истёк")
        except HTTPException: raise
        except Exception: pass
    if promo.get("max_uses") and promo["uses"] >= promo["max_uses"]:
        raise HTTPException(400, "промокод исчерпан")
    used = await sb(supabase.table("promo_uses").select("id").eq("code", code).eq("user_id", p["id"]))
    if used.data: raise HTTPException(400, "уже использовал")
    amount = float(promo["amount"])
    if promo.get("max_bonus"): amount = min(amount, float(promo["max_bonus"]))
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
        "meta": {"source": "promo", "code": code, "wager": wager_mult}}))
    return {"ok": True, "amount": amount, "wager_required": wager_required,
            "wager_mult": wager_mult, "max_bet": float(max_bet) if max_bet else None,
            "allowed_games": allowed}

@app.get("/api/bonus/daily")
async def bonus_status(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    if DAILY_BONUS <= 0:
        return {"available": False, "amount": 0, "next_in_sec": 0}
    last = p.get("last_bonus_at")
    if last:
        try:
            dt = datetime.fromisoformat(str(last).replace("Z", "+00:00"))
            left = BONUS_COOLDOWN_H * 3600 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0:
                return {"available": False, "amount": DAILY_BONUS, "next_in_sec": int(left)}
        except Exception: log.exception("bonus cooldown parse")
    return {"available": True, "amount": DAILY_BONUS, "next_in_sec": 0}

@app.post("/api/bonus/daily")
async def bonus_claim(user: dict = Depends(get_current_user)):
    if DAILY_BONUS <= 0: raise HTTPException(400, "бонус отключён")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    last = p.get("last_bonus_at")
    if last:
        try:
            dt = datetime.fromisoformat(str(last).replace("Z", "+00:00"))
            left = BONUS_COOLDOWN_H * 3600 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0:
                m = int(left // 60); raise HTTPException(400, f"бонус будет через {m} мин.")
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
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "валюта не поддерживается")
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
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "валюта не поддерживается")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "withdraw")
    await check_and_reset_wager_if_broke(p["id"])
    p = await get_or_create_profile(user)
    await check_wager_lock(p)
    if float(p["balance"]) < amount: raise HTTPException(400, "insufficient balance")
    try: payout = await do_withdraw(p, user["id"], amount, currency)
    except HTTPException: raise
    except Exception as e:
        log.exception("payout failed"); raise HTTPException(400, str(e))
    return {"ok": True, "payout_id": payout.get("id")}

@app.post("/api/webhook/xrocket")
async def xrocket_webhook(request: Request):
    raw = await request.body()
    sig = request.headers.get("Signature")
    ver = request.headers.get("Signature-Version")
    ts  = request.headers.get("Signature-Timestamp")

    if not all([sig, ver, ts]):
        raise HTTPException(401, "missing sig")
    if ver != "v1":
        raise HTTPException(401, "unsupported version")
    if abs(int(time.time() * 1000) - int(ts)) > 300_000:
        raise HTTPException(401, "timestamp too old")

    expected = hmac.new(
        XROCKET_WEBHOOK_SECRET.encode(),
        f"{ts}.{raw.decode()}".encode(),
        hashlib.sha256,
    ).hexdigest()
    if not hmac.compare_digest(expected, sig):
        raise HTTPException(401, "bad signature")

    event = json.loads(raw)
    log.info("xRocket webhook: %s", event)

    if event.get("type") == "invoice" and event.get("status") == "paid":
        cid = (event.get("clientInvoiceId")
               or (event.get("invoice") or {}).get("clientInvoiceId")
               or (event.get("payload") or {}).get("clientInvoiceId"))
        if cid:
            tx = (await sb(supabase.table("transactions").select("*")
                           .eq("external_id", str(cid))
                           .eq("status", "pending"))).data
            if tx:
                row = tx[0]
                await sb_rpc("change_balance",
                             {"p_user_id": row["user_id"], "p_delta": float(row["amount"])})
                await sb(supabase.table("transactions")
                         .update({"status": "completed"}).eq("id", row["id"]))
                log.info("deposit credited: %s", cid)

    return {"ok": True}

# ================== CRASH API ==================
def _crash_state_sync(p):
    status = crash_state["status"]; mult = 1.0
    if status == "running" and crash_state["started_at"]:
        mult = crash_mult(time.time() - crash_state["started_at"])
    elif status == "crashed":
        mult = crash_state["crash_point"] or 1.0
    bets = []; my_bet = None
    rid = crash_state["round_id"]
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
    try: return await asyncio.to_thread(_crash_state_sync, p)
    except Exception:
        log.exception("crash_state failed"); raise HTTPException(500, "crash state error")

@app.post("/api/crash/bet")
async def crash_bet(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("crash")
    if MAINTENANCE: raise HTTPException(503, "технические работы")
    if crash_state["status"] != "betting": raise HTTPException(400, "ставки закрыты")
    bet = float(body.get("bet", 0)); auto = body.get("auto_cashout_mult")
    auto = float(auto) if auto else None
    if auto is not None and (auto < 1.01 or auto > 100): raise HTTPException(400, "auto 1.01..100")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet)
    await check_bonus_game(p, "crash")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    rid = crash_state["round_id"]
    ex = await sb(supabase.table("crash_bets").select("id").eq("round_id", rid).eq("user_id", p["id"]))
    if ex.data: raise HTTPException(400, "уже поставил в этом раунде")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    row = {"round_id": rid, "user_id": p["id"],
           "username": p.get("first_name") or p.get("username") or "anon",
           "amount": bet, "status": "active"}
    if auto is not None: row["auto_cashout_mult"] = auto
    await sb(supabase.table("crash_bets").insert(row))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet, "currency": "USDT",
        "status": "completed", "meta": {"game": "crash_global", "auto": auto}}))
    return {"ok": True}

@app.post("/api/crash/cashout")
async def crash_cashout_global(user: dict = Depends(get_current_user)):
    if crash_state["status"] != "running": raise HTTPException(400, "раунд не идёт")
    elapsed = time.time() - crash_state["started_at"]
    mult = crash_mult(elapsed)
    if mult >= crash_state["crash_point"]: raise HTTPException(400, "слишком поздно")
    p = await get_or_create_profile(user); await ensure_not_banned(p)
    rid = crash_state["round_id"]
    b = await sb(supabase.table("crash_bets").select("*").eq("round_id", rid).eq("user_id", p["id"]).eq("status", "active"))
    if not b.data: raise HTTPException(400, "нет активной ставки")
    bet = b.data[0]; amount = float(bet["amount"])
    payout = round(amount * mult, 8); profit = round(payout - amount, 8)
    await sb(supabase.table("crash_bets").update({
        "status": "cashed", "cashout_mult": mult, "payout": payout,
        "auto_cashout_mult": None}).eq("id", bet["id"]))
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
        "status": "completed", "meta": {"game": "crash_global"}}))
    await log_round(p["id"], "crash", amount, {"global": True, "mult": mult, "round": rid},
                    profit, crash_state["server_seed"] or "", 0)
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit}

# ================== GAME API ==================
@app.post("/api/games/dice/bet")
async def dice_webapp(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("dice")
    if MAINTENANCE: raise HTTPException(503, "технические работы")
    bet = float(body.get("bet", 0)); chosen = int(body.get("chosen", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    if not (1 <= chosen <= 6): raise HTTPException(400, "chosen 1..6")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "dice")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    result = dice_result(ss, p["client_seed"], nonce)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    win = (result == chosen); profit = -bet; payout = 0
    if win:
        payout = round(bet * DICE_PAYOUT, 8); profit = round(payout - bet, 8)
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
            "status": "completed", "meta": {"game": "dice"}}))
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
    await log_round(p["id"], "dice", bet, {"result": result, "chosen": chosen, "win": win},
                    profit, ss, nonce)
    if not win:
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    return {"ok": True, "result": result, "win": win, "profit": profit, "payout": payout}

@app.post("/api/games/plinko/drop")
async def plinko_drop(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("plinko")
    if MAINTENANCE: raise HTTPException(503, "технические работы")
    bet = float(body.get("bet", 0)); rows = int(body.get("rows", 8))
    if rows not in (8, 12, 16): raise HTTPException(400, "rows 8/12/16")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "plinko")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    idx, path = plinko_path(ss, p["client_seed"], nonce, rows)
    mult = PLINKO_MULTS[rows][idx]
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    if profit > 0:
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
            "status": "completed", "meta": {"game": "plinko", "mult": mult}}))
    elif profit < 0:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await log_round(p["id"], "plinko", bet, {"rows": rows, "slot": idx, "mult": mult},
                    profit, ss, nonce)
    if profit < 0:
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    return {"ok": True, "slot": idx, "mult": mult, "payout": payout, "profit": profit,
            "rows": rows, "path": path}

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
    if MAINTENANCE: raise HTTPException(503, "технические работы")
    bet = float(body.get("bet", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "blackjack")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    ar = await get_active_round(p["id"])
    if ar:
        if ar["game_type"] == "blackjack":
            st = ar["state"]
            return {"ok": True, "resumed": True, "player": st["player"],
                    "dealer": [st["dealer"][0], "??"],
                    "player_value": bj_value(st["player"]),
                    "dealer_value": bj_value([st["dealer"][0]]), "finished": False}
        raise HTTPException(400, f"активная игра: {ar['game_type']}")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    deck = bj_deck(ss, p["client_seed"], nonce)
    player = [deck[0], deck[2]]; dealer = [deck[1], deck[3]]; rest = deck[4:]
    player_v = bj_value(player)
    state = {"player": player, "dealer": dealer, "rest": rest, "bet": bet, "status": "player_turn"}
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "blackjack", "bet_amount": bet,
        "state": state, "server_seed": ss, "nonce": nonce}))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet, "currency": "USDT",
        "status": "completed", "meta": {"game": "blackjack"}}))
    if player_v == 21:
        dealer_full = bj_value(dealer)
        if dealer_full == 21:
            payout = bet; profit = 0
            await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": bet})
        else:
            payout = round(bet * 2.5, 8); profit = round(payout - bet, 8)
            await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
            "status": "completed", "meta": {"game": "blackjack", "bj": True}}))
        await log_round(p["id"], "blackjack", bet,
                        {"player": player, "dealer": dealer, "bj": True}, profit, ss, nonce)
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
    if not ar or ar["game_type"] != "blackjack": raise HTTPException(400, "нет активной игры")
    st = ar["state"]
    if st["status"] != "player_turn": raise HTTPException(400, "не твой ход")
    rest = st["rest"]
    if not rest: raise HTTPException(400, "колода кончилась")
    card = rest.pop(0); st["player"].append(card); st["rest"] = rest
    pv = bj_value(st["player"])
    if pv > 21:
        await log_round(p["id"], "blackjack", float(st["bet"]),
                        {"player": st["player"], "dealer": st["dealer"], "bust": True},
                        -float(st["bet"]), ar["server_seed"], ar["nonce"])
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
    if not ar or ar["game_type"] != "blackjack": raise HTTPException(400, "нет активной игры")
    st = ar["state"]
    if st["status"] != "player_turn": raise HTTPException(400, "уже завершено")
    rest = st["rest"]
    while bj_value(st["dealer"]) < 17 and rest:
        st["dealer"].append(rest.pop(0))
    st["rest"] = rest
    pv = bj_value(st["player"]); dv = bj_value(st["dealer"])
    bet = float(st["bet"]); profit = -bet; payout = 0; push = False; win = False
    if dv > 21 or pv > dv:
        win = True; payout = round(bet * 2, 8); profit = round(payout - bet, 8)
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
            "status": "completed", "meta": {"game": "blackjack"}}))
    elif pv == dv:
        push = True; profit = 0; payout = bet
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": bet})
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
    await log_round(p["id"], "blackjack", bet,
                    {"player": st["player"], "dealer": st["dealer"], "win": win, "push": push},
                    profit, ar["server_seed"], ar["nonce"])
    await clear_active_round(p["id"])
    if not win and not push:
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    return {"ok": True, "player": st["player"], "dealer": st["dealer"],
            "player_value": pv, "dealer_value": dv,
            "finished": True, "win": win, "push": push,
            "profit": profit, "payout": payout}

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
    if MAINTENANCE: raise HTTPException(503, "технические работы")
    bet = float(body.get("bet", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "tower")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    ar = await get_active_round(p["id"])
    if ar:
        if ar["game_type"] == "tower":
            st = ar["state"]
            return {"ok": True, "resumed": True, "level": st["level"],
                    "mult": tower_mult(st["level"]),
                    "next_mult": tower_mult(st["level"] + 1)}
        raise HTTPException(400, f"активная игра: {ar['game_type']}")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    positions = tower_step_positions(ss, p["client_seed"], nonce, levels=6)
    state = {"level": 0, "mine_positions": positions, "bet": bet, "revealed": []}
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "tower", "bet_amount": bet,
        "state": state, "server_seed": ss, "nonce": nonce}))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet, "currency": "USDT",
        "status": "completed", "meta": {"game": "tower"}}))
    return {"ok": True, "level": 0, "mult": 1.0, "next_mult": tower_mult(1)}

@app.post("/api/games/tower/step")
async def tower_step(body: dict, user: dict = Depends(get_current_user)):
    door = int(body.get("door", -1))
    if not (0 <= door <= 2): raise HTTPException(400, "door 0..2")
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "tower": raise HTTPException(400, "нет активной игры")
    st = ar["state"]
    level = st["level"]
    if level >= len(st["mine_positions"]): raise HTTPException(400, "макс уровень")
    mine = st["mine_positions"][level]
    bet = float(st["bet"])
    if door == mine:
        await log_round(p["id"], "tower", bet,
                        {"level": level, "door": door, "mine": mine, "lost": True},
                        -bet, ar["server_seed"], ar["nonce"])
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        await clear_active_round(p["id"])
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
        return {"ok": True, "lost": True, "mine": mine, "level": level}
    st["level"] = level + 1
    st["revealed"].append({"level": level, "door": door, "mine": mine})
    new_level = st["level"]
    await sb(supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]))
    return {"ok": True, "lost": False, "level": new_level,
            "mult": tower_mult(new_level), "next_mult": tower_mult(new_level + 1),
            "mine": mine, "all_levels": st["mine_positions"]}

@app.post("/api/games/tower/cashout")
async def tower_cashout(user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "tower": raise HTTPException(400, "нет активной игры")
    st = ar["state"]
    level = st["level"]
    if level <= 0: raise HTTPException(400, "пройди хотя бы 1 уровень")
    bet = float(st["bet"]); mult = tower_mult(level)
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
        "status": "completed", "meta": {"game": "tower", "mult": mult}}))
    await log_round(p["id"], "tower", bet,
                    {"level": level, "mult": mult, "revealed": st["revealed"]},
                    profit, ar["server_seed"], ar["nonce"])
    await clear_active_round(p["id"])
    return {"ok": True, "level": level, "mult": mult, "payout": payout, "profit": profit,
            "mine_positions": st["mine_positions"]}

@app.post("/api/games/mines/start")
async def mines_start(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("mines")
    if MAINTENANCE: raise HTTPException(503, "технические работы")
    bet = float(body.get("bet", 0)); mines = int(body.get("mines", 3))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    if not (1 <= mines <= 24): raise HTTPException(400, "mines 1..24")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "mines")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    if await get_active_round(p["id"]): raise HTTPException(400, "active round exists")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    positions = mine_positions(ss, p["client_seed"], nonce, mines)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    asyncio.create_task(apply_wager_progress(p["id"], bet))
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "mines", "bet_amount": bet,
        "state": {"mines": mines, "positions": positions, "revealed": []},
        "server_seed": ss, "nonce": nonce}))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet, "currency": "USDT",
        "status": "completed", "meta": {"game": "mines"}}))
    return {"ok": True, "mines": mines, "mult": mines_mult(mines, 0)}

@app.post("/api/games/mines/reveal")
async def mines_reveal(body: dict, user: dict = Depends(get_current_user)):
    idx = int(body.get("cell", -1))
    if not (0 <= idx < 25): raise HTTPException(400, "bad cell")
    p = await get_or_create_profile(user)
    ar = await get_active_round(p["id"])
    if not ar or ar["game_type"] != "mines": raise HTTPException(400, "no active mines round")
    st = ar["state"]
    if idx in st["revealed"]: raise HTTPException(400, "already revealed")
    positions = set(st["positions"]); bet = float(ar["bet_amount"])
    if idx in positions:
        await log_round(p["id"], "mines", bet,
                        {"mine_hit": idx, "revealed": st["revealed"], "mines": st["mines"], "positions": st["positions"]},
                        -bet, ar["server_seed"], ar["nonce"])
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
    if not ar or ar["game_type"] != "mines": raise HTTPException(400, "no active mines round")
    st = ar["state"]; k = len(st["revealed"])
    if k == 0: raise HTTPException(400, "reveal at least one cell")
    bet = float(ar["bet_amount"]); mult = mines_mult(st["mines"], k)
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await log_round(p["id"], "mines", bet,
                    {"revealed": st["revealed"], "mult": mult, "mines": st["mines"], "positions": st["positions"]},
                    profit, ar["server_seed"], ar["nonce"])
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
        "status": "completed", "meta": {"game": "mines"}}))
    await clear_active_round(p["id"])
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit, "positions": st["positions"]}

RED = {1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36}
BLACK = {2,4,6,8,10,11,13,15,17,20,22,24,26,28,29,31,33,35}

@app.post("/api/games/roulette/bet")
async def roulette_bet(body: dict, user: dict = Depends(get_current_user)):
    ensure_game_enabled("roulette")
    if MAINTENANCE: raise HTTPException(503, "технические работы")
    bet = float(body.get("bet", 0)); bt = body.get("type"); bv = body.get("value")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p); await check_rate_limit(p["id"], "bet")
    await check_bonus_max_bet(p, bet); await check_bonus_game(p, "roulette")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    n = roulette_number(ss, p["client_seed"], nonce)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
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
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit, "currency": "USDT",
            "status": "completed", "meta": {"game": "roulette"}}))
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
    await log_round(p["id"], "roulette", bet, {"n": n, "bet_type": bt, "win": win}, profit, ss, nonce)
    if not win:
        asyncio.create_task(check_and_reset_wager_if_broke(p["id"]))
    color = "green" if n == 0 else ("red" if n in RED else "black")
    return {"ok": True, "number": n, "color": color, "win": win,
            "payout": round(bet * pm, 8) if win else 0, "profit": profit}
