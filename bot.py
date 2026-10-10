import os, json, hmac, hashlib, logging, asyncio, time, math, uuid
from urllib.parse import parse_qsl
from contextlib import asynccontextmanager
from math import comb
from datetime import datetime, timezone, timedelta

import httpx
from fastapi import FastAPI, Header, HTTPException, Depends, Request
from fastapi.middleware.cors import CORSMiddleware
from aiogram import Bot, Dispatcher, F
from aiogram.types import (Message, CallbackQuery, InlineKeyboardMarkup,
                           InlineKeyboardButton, WebAppInfo)
from aiogram.filters import Command, CommandObject
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.context import FSMContext
from supabase import create_client, Client

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("casino")

BOT_TOKEN = os.environ["BOT_TOKEN"]
WEBAPP_URL = os.environ["WEBAPP_URL"]
SUPABASE_URL = os.environ["SUPABASE_URL"]
SUPABASE_SERVICE_KEY = os.environ["SUPABASE_SERVICE_KEY"]
XROCKET_API_KEY = os.environ["XROCKET_API_KEY"]
XROCKET_WEBHOOK_SECRET = os.environ["XROCKET_WEBHOOK_SECRET"]
XROCKET_API_BASE = os.environ.get("XROCKET_API_BASE", "https://pay.api.xrocket.exchange")

HOUSE_EDGE = float(os.environ.get("HOUSE_EDGE", "0.04"))
MIN_BET = float(os.environ.get("MIN_BET", "0.1"))
MAX_BET = float(os.environ.get("MAX_BET", "1000"))
MIN_DEPOSIT = float(os.environ.get("MIN_DEPOSIT", "0.1"))
MIN_WITHDRAW = float(os.environ.get("MIN_WITHDRAW", "0.5"))
MAX_DEPOSIT = float(os.environ.get("MAX_DEPOSIT", "100000"))
WITHDRAW_COOLDOWN_MIN = int(os.environ.get("WITHDRAW_COOLDOWN_MIN", "15"))
MAX_WITHDRAW_DAILY = float(os.environ.get("MAX_WITHDRAW_DAILY", "500"))
REFERRAL_SHARE = float(os.environ.get("REFERRAL_SHARE", "0.05"))

ADMIN_IDS = set(int(x) for x in os.environ.get("ADMIN_IDS", "8130244626").split(",") if x.strip().isdigit())

DICE_PAYOUT = round(6 * (1 - HOUSE_EDGE), 4)
ROUL_RB_PAYOUT = round(2 * (1 - HOUSE_EDGE), 4)
ROUL_DOZEN_PAYOUT = round(3 * (1 - HOUSE_EDGE), 4)
ROUL_NUM_PAYOUT = round(36 * (1 - HOUSE_EDGE), 4)

RATE_LIMITS = {
    "bet":      (5, 10),   # 5 ставок за 10 сек
    "withdraw": (1, 30),   # 1 вывод за 30 сек
    "deposit":  (1, 5),    # 1 депозит за 5 сек
}
SUPPORTED_CURRENCIES = ["USDT", "TON", "BTC", "ETH", "TRX"]

CRASH_BETTING_SEC = 10
CRASH_COOLDOWN_SEC = 4

supabase: Client = create_client(SUPABASE_URL, SUPABASE_SERVICE_KEY)
BOT_USERNAME: str | None = None

crash_state = {
    "round_id": None, "status": "idle", "server_seed": None,
    "crash_point": None, "started_at": None, "betting_ends_at": None,
}


class AmountInput(StatesGroup):
    deposit = State()
    withdraw = State()

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
                 .eq("user_id", uid).eq("action", action)
                 .gte("created_at", since))
    if len(r.data or []) >= max_calls:
        raise HTTPException(429, f"слишком часто. Подожди {window} сек.")
    await sb(supabase.table("action_log").insert({"user_id": uid, "action": action}))


async def ensure_not_banned(profile):
    if profile.get("is_banned"):
        reason = profile.get("ban_reason") or "нарушение правил"
        raise HTTPException(403, f"аккаунт заблокирован: {reason}")


# =================== xRocket Pay API ===================
async def xrocket_request(method: str, path: str, body: dict | None = None) -> dict:
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
        if r.status_code not in (200, 201):
            log.error("xRocket %s %s -> %s %s", method, path, r.status_code, data)
            msg = data.get("message") or data.get("detail") or data.get("error") or f"HTTP {r.status_code}"
            if isinstance(msg, dict):
                msg = json.dumps(msg, ensure_ascii=False)
            raise Exception(f"{msg}")
        return data


async def xrocket_create_invoice(amount: float, description: str, req_id: str,
                                  currency: str = "USDT") -> dict:
    payload = {
        "amount": float(amount),
        "asset": currency,
        "description": description,
        "clientInvoiceId": req_id,
    }
    data = await xrocket_request("POST", "/api/v1/invoices", payload)
    link = data.get("link") or data.get("url") or data.get("invoiceUrl")
    inv_id = data.get("id") or data.get("invoiceId")
    if not link:
        raise Exception(f"xRocket не вернул ссылку: {data}")
    return {"id": inv_id, "link": link, "raw": data}


async def xrocket_create_payout(user_id: int, amount: float, comment: str, req_id: str,
                                 currency: str = "USDT") -> dict:
    payload = {
        "clientPayoutId": req_id,
        "target": str(user_id),
        "targetType": "telegram_user_id",
        "asset": currency,
        "amount": str(amount),
        "description": comment,
    }
    data = await xrocket_request("POST", "/api/v1/payouts", payload)
    payout_id = data.get("payoutId") or data.get("id")
    return {"id": payout_id, "raw": data}


# =================== math / PF ===================
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


# =================== auth ===================
def validate_init_data(init_data, bot_token):
    try:
        parsed = dict(parse_qsl(init_data, keep_blank_values=True))
        rh = parsed.pop("hash", None)
        if not rh: return None
        dcs = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
        sk = hmac.new(b"WebAppData", bot_token.encode(), hashlib.sha256).digest()
        if not hmac.compare_digest(hmac.new(sk, dcs.encode(), hashlib.sha256).hexdigest(), rh): return None
        u = json.loads(parsed.get("user", "{}"))
        return u if u.get("id") else None
    except Exception:
        log.exception("validate_init_data failed")
        return None

async def get_current_user(x_telegram_init_data: str = Header(None, alias="X-Telegram-Init-Data")):
    if not x_telegram_init_data: raise HTTPException(401, "missing init data")
    u = validate_init_data(x_telegram_init_data, BOT_TOKEN)
    if not u: raise HTTPException(401, "invalid init data")
    return u


# =================== DB helpers ===================
async def get_or_create_profile(tg_user):
    tg_id = int(tg_user["id"])
    r = await sb(supabase.table("profiles").select("*").eq("telegram_id", tg_id))
    if r.data: return r.data[0]
    ins = await sb(supabase.table("profiles").insert({
        "telegram_id": tg_id,
        "username": tg_user.get("username"),
        "first_name": tg_user.get("first_name"),
        "preferred_currency": "USDT",
    }))
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
            "result": result, "profit": profit, "server_seed": ss, "nonce": nonce,
        }))
    except Exception:
        log.exception("log_round failed")

async def get_user_stats(uid):
    tx = (await sb(supabase.table("transactions").select("type, amount, status").eq("user_id", uid))).data or []
    rounds = (await sb(supabase.table("game_rounds").select("id").eq("user_id", uid))).data or []
    deposits = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    withdrawals = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    wins = sum(float(t["amount"]) for t in tx if t["type"] == "win")
    bets = sum(float(t["amount"]) for t in tx if t["type"] == "bet")
    return {
        "games": len(rounds), "deposits": round(deposits, 2),
        "withdrawals": round(withdrawals, 2), "bets": round(bets, 2),
        "wins": round(wins, 2), "net": round(wins - bets, 2),
    }

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
            "meta": {"from_user": uid, "bet": bet_amount},
        }))
    except Exception:
        log.exception("credit_referrer_on_loss failed")


def referral_info_sync(profile):
    ref_link = f"https://t.me/{BOT_USERNAME}?start=ref_{profile['telegram_id']}" if BOT_USERNAME else ""
    return {"link": ref_link, "share": REFERRAL_SHARE}


# =================== payments ===================
async def create_deposit_invoice(profile, amount, currency="USDT"):
    if currency not in SUPPORTED_CURRENCIES:
        raise HTTPException(400, "неподдерживаемая валюта")
    cid = f"dep_{profile['id'][:8]}_{int(time.time())}"
    inv = await xrocket_create_invoice(amount, "GoldCash deposit", cid, currency)
    await sb(supabase.table("transactions").insert({
        "user_id": profile["id"], "type": "deposit", "amount": amount,
        "currency": currency, "external_id": cid, "status": "pending",
        "meta": {"invoice_id": inv.get("id")},
    }))
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

    spent = await daily_withdrawn(profile["id"])
    if spent + amount > MAX_WITHDRAW_DAILY:
        left = MAX_WITHDRAW_DAILY - spent
        raise HTTPException(400, f"дневной лимит вывода. Осталось {max(0, left):.2f}")

    cid = f"wd_{profile['id'][:8]}_{int(time.time())}"
    payout = await xrocket_create_payout(tg_id, amount, "GoldCash withdraw", cid, currency)
    await sb_rpc("change_balance", {"p_user_id": profile["id"], "p_delta": -amount})
    await sb(supabase.table("transactions").insert({
        "user_id": profile["id"], "type": "withdraw", "amount": amount,
        "currency": currency, "external_id": cid, "status": "completed",
        "meta": {"payout_id": payout.get("id")},
    }))
    return payout


# =================== CRASH LOOP ===================
async def crash_loop():
    global crash_state
    await asyncio.sleep(3)
    while True:
        try:
            ss = os.urandom(16).hex()
            cp = crash_point(ss, "global", 0)
            now = time.time()
            res = await sb(supabase.table("crash_rounds").insert({
                "status": "betting", "server_seed": ss, "crash_point": cp,
            }))
            round_id = res.data[0]["id"]
            crash_state.update({
                "round_id": round_id, "status": "betting",
                "server_seed": ss, "crash_point": cp,
                "started_at": None, "betting_ends_at": now + CRASH_BETTING_SEC,
            })
            await asyncio.sleep(CRASH_BETTING_SEC)
            started = time.time()
            await sb(supabase.table("crash_rounds").update({
                "status": "running",
                "started_at": datetime.now(timezone.utc).isoformat(),
            }).eq("id", round_id))
            crash_state["status"] = "running"
            crash_state["started_at"] = started
            duration = max(0.4, math.log(cp) / math.log(1.07)) if cp > 1.0 else 0.4
            await asyncio.sleep(duration)
            await sb(supabase.table("crash_rounds").update({
                "status": "crashed",
                "ended_at": datetime.now(timezone.utc).isoformat(),
            }).eq("id", round_id))
            crash_state["status"] = "crashed"
            lost = (await sb(supabase.table("crash_bets").select("*")
                             .eq("round_id", round_id).eq("status", "active"))).data or []
            for b in lost:
                await sb(supabase.table("crash_bets").update({"status": "lost"}).eq("id", b["id"]))
                await log_round(b["user_id"], "crash", float(b["amount"]),
                                {"global": True, "crashed_at": cp}, -float(b["amount"]), ss, 0)
                await credit_referrer_on_loss(b["user_id"], float(b["amount"]))
            await asyncio.sleep(CRASH_COOLDOWN_SEC)
            crash_state["status"] = "idle"
            crash_state["round_id"] = None
        except Exception as e:
            log.exception("crash loop error: %s", e)
            await asyncio.sleep(5)


# =================== aiogram ===================
bot = Bot(token=BOT_TOKEN)
dp = Dispatcher()

def main_menu():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎲 Играть в кубы", callback_data="menu:dice")],
        [InlineKeyboardButton(text="💰 Пополнить", callback_data="menu:deposit"),
         InlineKeyboardButton(text="💸 Вывести", callback_data="menu:withdraw")],
        [InlineKeyboardButton(text="👥 Друзья (5%)", callback_data="menu:ref"),
         InlineKeyboardButton(text="📊 Статистика", callback_data="menu:stats")],
        [InlineKeyboardButton(text="🌐 Открыть казино", web_app=WebAppInfo(url=WEBAPP_URL))],
    ])

def back_kb():
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])

def fmt_stats(s, balance, first_name):
    return (
        f"👤 <b>{first_name or 'игрок'}</b>\n\n"
        f"💎 <b>Баланс:</b> {balance:.2f}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"📥 Пополнено: <b>{s['deposits']:.2f}</b>\n"
        f"📤 Выведено: <b>{s['withdrawals']:.2f}</b>\n"
        f"🎯 Ставок: <b>{s['bets']:.2f}</b>\n"
        f"🏆 Выигрышей: <b>{s['wins']:.2f}</b>\n"
        f"🎮 Игр: <b>{s['games']}</b>\n"
        f"📊 Профит: <b>{s['net']:+.2f}</b>"
    )


# =================== ADMIN ===================
def admin_only(message: Message) -> bool:
    return message.from_user and is_admin(message.from_user.id)

@dp.message(Command("admin"))
async def cmd_admin(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"🏦 <b>Админ-панель</b>\n"
        f"RTP {100-HOUSE_EDGE*100:.0f}% · HE {HOUSE_EDGE*100:.1f}%\n"
        f"Мин ставка {MIN_BET} · макс {MAX_BET}\n"
        f"Мин деп {MIN_DEPOSIT} · мин вывод {MIN_WITHDRAW}\n"
        f"Лимит вывода/сутки {MAX_WITHDRAW_DAILY}\n"
        f"Кулдаун {WITHDRAW_COOLDOWN_MIN} мин\n"
        f"Рефералка {REFERRAL_SHARE*100:.0f}%\n"
        f"━━━━━━━━━━━━━━━\n"
        f"/astats · /arp · /auser &lt;id&gt;\n"
        f"/agive &lt;id&gt; &lt;sum&gt; · /atake &lt;id&gt; &lt;sum&gt;\n"
        f"/aban &lt;id&gt; [reason] · /aunban &lt;id&gt;\n"
        f"/abroadcast &lt;text&gt;\n"
        f"/anewpromo &lt;code&gt; &lt;amount&gt; [max]\n"
        f"/alistpromos · /adelpromo &lt;code&gt;",
        parse_mode="HTML")

@dp.message(Command("aban"))
async def cmd_aban(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aban <tg_id> [причина]")
    parts = command.args.split(maxsplit=1)
    try: tg_id = int(parts[0])
    except: return await message.answer("tg_id числом")
    reason = parts[1] if len(parts) > 1 else "нарушение правил"
    p = await get_profile_by_tg(tg_id)
    if not p: return await message.answer("Юзер не найден")
    await sb(supabase.table("profiles").update({
        "is_banned": True, "ban_reason": reason}).eq("id", p["id"]))
    await message.answer(f"🚫 <code>{tg_id}</code> забанен: {reason}", parse_mode="HTML")
    try: await bot.send_message(tg_id, f"🚫 Твой аккаунт заблокирован: {reason}")
    except: pass

@dp.message(Command("aunban"))
async def cmd_aunban(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/aunban <tg_id>")
    try: tg_id = int(command.args.strip())
    except: return await message.answer("tg_id числом")
    p = await get_profile_by_tg(tg_id)
    if not p: return await message.answer("Юзер не найден")
    await sb(supabase.table("profiles").update({
        "is_banned": False, "ban_reason": None}).eq("id", p["id"]))
    await message.answer(f"✅ <code>{tg_id}</code> разбанен", parse_mode="HTML")

@dp.message(Command("arp"))
async def cmd_arp(message: Message):
    if not admin_only(message): return
    await message.answer(
        f"📊 RTP: <b>{100-HOUSE_EDGE*100:.2f}%</b>\n\n"
        f"🎲 Кубик ×{DICE_PAYOUT} — {DICE_PAYOUT/6*100:.2f}%\n"
        f"💥 Crash — {(1-HOUSE_EDGE)*100:.2f}%\n"
        f"💎 Mines — {(1-HOUSE_EDGE)*100:.2f}%\n"
        f"🎡 Рулетка RB ×{ROUL_RB_PAYOUT} — {ROUL_RB_PAYOUT*18/37*100:.2f}%\n"
        f"   Дюжина ×{ROUL_DOZEN_PAYOUT} — {ROUL_DOZEN_PAYOUT*12/37*100:.2f}%\n"
        f"   Число ×{ROUL_NUM_PAYOUT} — {ROUL_NUM_PAYOUT/37*100:.2f}%",
        parse_mode="HTML")

@dp.message(Command("astats"))
async def cmd_astats(message: Message):
    if not admin_only(message): return
    try:
        users = (await sb(supabase.table("profiles").select("id, balance, created_at"))).data or []
        tx = (await sb(supabase.table("transactions").select("type, amount, status"))).data or []
        rounds = (await sb(supabase.table("game_rounds").select("bet_amount, profit, game_type"))).data or []
        dep = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
        wd = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
        total_bets = sum(float(r["bet_amount"]) for r in rounds)
        ggr = -sum(float(r["profit"]) for r in rounds)
        by_game = {}
        for r in rounds:
            g = r["game_type"]
            by_game.setdefault(g, {"bets": 0, "count": 0})
            by_game[g]["bets"] += float(r["bet_amount"])
            by_game[g]["count"] += 1
        games_text = "\n".join(f"   • {g}: {v['count']} игр, оборот {v['bets']:.2f}"
                              for g, v in by_game.items()) or "   нет"
        await message.answer(
            f"👥 Юзеров: <b>{len(users)}</b>\n"
            f"💰 Балансов: <b>{sum(float(u['balance']) for u in users):.2f}</b>\n"
            f"📥 Депозиты: <b>{dep:.2f}</b>\n"
            f"📤 Выводы: <b>{wd:.2f}</b>\n"
            f"🎯 Оборот: <b>{total_bets:.2f}</b>\n"
            f"📈 GGR: <b>{ggr:+.2f}</b>\n"
            f"━━━━━━━━━━━━━━━\n{games_text}",
            parse_mode="HTML")
    except Exception as e:
        await message.answer(f"❌ {e}")

@dp.message(Command("auser"))
async def cmd_auser(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("Использование: /auser <tg_id>")
    try: tg_id = int(command.args.strip())
    except: return await message.answer("tg_id числом")
    p = await get_profile_by_tg(tg_id)
    if not p: return await message.answer("Юзер не найден")
    s = await get_user_stats(p["id"])
    ban = "🚫 ЗАБАНЕН" if p.get("is_banned") else "✅ активен"
    await message.answer(
        f"👤 <b>{p.get('first_name') or '—'}</b> @{p.get('username') or '—'}\n"
        f"🆔 <code>{p['telegram_id']}</code>\n"
        f"💎 <b>{float(p['balance']):.2f}</b>\n"
        f"Статус: {ban}\n"
        f"📥 {s['deposits']:.2f} · 📤 {s['withdrawals']:.2f}\n"
        f"🎯 {s['bets']:.2f} · 🏆 {s['wins']:.2f}\n"
        f"🎮 {s['games']} · 📊 {s['net']:+.2f}\n"
        f"👥 реф: {float(p.get('ref_earnings') or 0):.2f}",
        parse_mode="HTML")

@dp.message(Command("agive"))
async def cmd_agive(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/agive <tg_id> <сумма>")
    parts = command.args.split()
    if len(parts) != 2: return await message.answer("/agive <tg_id> <сумма>")
    try: tg_id, amount = int(parts[0]), float(parts[1].replace(",", "."))
    except: return await message.answer("Некорректные аргументы")
    if amount <= 0: return await message.answer("Сумма > 0")
    p = await get_profile_by_tg(tg_id)
    if not p: return await message.answer("Юзер не найден")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "admin", "amount": amount,
        "currency": "USDT", "status": "completed",
        "meta": {"by": message.from_user.id, "action": "give"}}))
    await message.answer(f"✅ +<b>{amount}</b> → <code>{tg_id}</code>", parse_mode="HTML")
    try: await bot.send_message(tg_id, f"💎 +<b>{amount}</b>", parse_mode="HTML")
    except: pass

@dp.message(Command("atake"))
async def cmd_atake(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/atake <tg_id> <сумма>")
    parts = command.args.split()
    if len(parts) != 2: return await message.answer("/atake <tg_id> <сумма>")
    try: tg_id, amount = int(parts[0]), float(parts[1].replace(",", "."))
    except: return await message.answer("Некорректные аргументы")
    if amount <= 0: return await message.answer("Сумма > 0")
    p = await get_profile_by_tg(tg_id)
    if not p: return await message.answer("Юзер не найден")
    if float(p["balance"]) < amount:
        return await message.answer(f"У юзера только {float(p['balance']):.2f}")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -amount})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "admin", "amount": amount,
        "currency": "USDT", "status": "completed",
        "meta": {"by": message.from_user.id, "action": "take"}}))
    await message.answer(f"✅ −<b>{amount}</b> у <code>{tg_id}</code>", parse_mode="HTML")

@dp.message(Command("abroadcast"))
async def cmd_abroadcast(message: Message, command: CommandObject, state: FSMContext):
    if not admin_only(message): return
    if not command.args:
        await state.set_state(AdminInput.broadcast)
        return await message.answer("✍️ Отправь текст (или /cancel)")
    await do_broadcast(message, command.args)

@dp.message(Command("cancel"))
async def cmd_cancel(message: Message, state: FSMContext):
    await state.clear()
    await message.answer("Отменено")

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
        try:
            await bot.send_message(int(u["telegram_id"]), text)
            ok += 1
        except: fail += 1
        await asyncio.sleep(0.05)
    await message.answer(f"✅ {ok} доставлено, {fail} ошибок")

@dp.message(Command("anewpromo"))
async def cmd_anewpromo(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/anewpromo CODE AMOUNT [MAX]")
    parts = command.args.split()
    if len(parts) < 2: return await message.answer("/anewpromo CODE AMOUNT [MAX]")
    code = parts[0].upper().strip()
    try: amount = float(parts[1].replace(",", "."))
    except: return await message.answer("Сумма числом")
    max_uses = None
    if len(parts) >= 3:
        try: max_uses = int(parts[2])
        except: pass
    if amount <= 0: return await message.answer("Сумма > 0")
    try:
        await sb(supabase.table("promo_codes").insert({
            "code": code, "amount": amount, "max_uses": max_uses,
            "created_by": message.from_user.id}))
        await message.answer(f"✅ <code>{code}</code> · {amount} · {'∞' if not max_uses else max_uses}", parse_mode="HTML")
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
        lines.append(f"• <code>{p['code']}</code> — {float(p['amount']):.2f} · {uses}")
    await message.answer("<b>Промокоды:</b>\n" + "\n".join(lines), parse_mode="HTML")

@dp.message(Command("adelpromo"))
async def cmd_adelpromo(message: Message, command: CommandObject):
    if not admin_only(message): return
    if not command.args: return await message.answer("/adelpromo CODE")
    code = command.args.strip().upper()
    try:
        await sb(supabase.table("promo_codes").delete().eq("code", code))
        await message.answer(f"✅ <code>{code}</code> удалён", parse_mode="HTML")
    except Exception as e:
        await message.answer(f"❌ {e}")


# =================== USER COMMANDS ===================
@dp.message(Command("start"))
async def cmd_start(message: Message, command: CommandObject, state: FSMContext):
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
    extra = "\n\n🔐 <i>У тебя есть /admin</i>" if is_admin(message.from_user.id) else ""
    cur = p.get("preferred_currency") or "USDT"
    await message.answer(
        f"Привет, {message.from_user.first_name}! 👋\n\n"
        f"💎 Баланс: <b>{float(p['balance']):.2f} {cur}</b>{extra}",
        reply_markup=main_menu(), parse_mode="HTML")

@dp.message(Command("balance"))
async def cmd_balance(message: Message):
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    await message.answer(f"💎 Баланс: <b>{float(p['balance']):.2f} {cur}</b>",
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

@dp.message(Command("dice"))
async def cmd_dice(message: Message):
    await message.answer("🎲 Выбери ставку:", reply_markup=dice_bet_kb())

@dp.message(Command("deposit"))
async def cmd_deposit(message: Message, command: CommandObject):
    try: amount = float(command.args)
    except: return await message.answer(f"Использование: /deposit 1 (мин {MIN_DEPOSIT})")
    if amount < MIN_DEPOSIT: return await message.answer(f"Минимум {MIN_DEPOSIT}")
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    try: inv = await create_deposit_invoice(p, amount, cur)
    except Exception as e: return await message.answer(f"❌ {e}")
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="💳 Оплатить", url=inv["link"])]])
    await message.answer(f"💰 Счёт на <b>{amount} {cur}</b>.", parse_mode="HTML", reply_markup=kb)

@dp.message(Command("withdraw"))
async def cmd_withdraw(message: Message, command: CommandObject):
    p = await get_or_create_profile(message.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if not command.args:
        return await message.answer(
            f"💸 <b>Вывод</b>\n"
            f"Баланс: <b>{float(p['balance']):.2f} {cur}</b>\n"
            f"Минимум: {MIN_WITHDRAW}\n\n"
            f"<b>⚠️ Средства придут на @xRocket.</b>\n\n"
            f"Использование: /withdraw 5",
            parse_mode="HTML", reply_markup=back_kb())
    try: amount = float(command.args.replace(",", ".").strip())
    except: return await message.answer("Использование: /withdraw 5")
    if amount < MIN_WITHDRAW:
        return await message.answer(f"❌ Минимум {MIN_WITHDRAW}")
    if float(p["balance"]) < amount:
        return await message.answer(f"❌ Недостаточно. Баланс: <b>{float(p['balance']):.2f}</b>", parse_mode="HTML")
    msg = await message.answer("⏳ Обработка…")
    try: await do_withdraw(p, message.from_user.id, amount, cur)
    except HTTPException as e: return await msg.edit_text(f"❌ {e.detail}")
    except Exception as e:
        log.exception("payout failed")
        return await msg.edit_text(f"❌ {e}")
    await msg.edit_text(f"✅ Выплата <b>{amount} {cur}</b> отправлена.", parse_mode="HTML")

@dp.message(Command("currency"))
async def cmd_currency(message: Message, command: CommandObject):
    if not command.args:
        return await message.answer(
            f"Доступные валюты: {', '.join(SUPPORTED_CURRENCIES)}\n"
            f"Использование: /currency TON")
    cur = command.args.strip().upper()
    if cur not in SUPPORTED_CURRENCIES:
        return await message.answer("❌ Неподдерживаемая валюта")
    p = await get_or_create_profile(message.from_user.model_dump())
    await sb(supabase.table("profiles").update({"preferred_currency": cur}).eq("id", p["id"]))
    await message.answer(f"✅ Валюта: <b>{cur}</b>", parse_mode="HTML", reply_markup=back_kb())


async def try_redeem_promo(message: Message, code: str):
    p = await get_or_create_profile(message.from_user.model_dump())
    r = await sb(supabase.table("promo_codes").select("*").eq("code", code))
    if not r.data: return await message.answer("❌ Промокод не найден")
    promo = r.data[0]
    if promo.get("max_uses") and promo["uses"] >= promo["max_uses"]:
        return await message.answer("❌ Промокод исчерпан")
    used = await sb(supabase.table("promo_uses").select("id").eq("code", code).eq("user_id", p["id"]))
    if used.data: return await message.answer("❌ Ты уже использовал")
    amount = float(promo["amount"])
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    await sb(supabase.table("promo_uses").insert({"code": code, "user_id": p["id"], "amount": amount}))
    await sb(supabase.table("promo_codes").update({"uses": promo["uses"] + 1}).eq("code", code))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": amount,
        "currency": "USDT", "status": "completed",
        "meta": {"source": "promo", "code": code}}))
    await message.answer(f"✅ +<b>{amount}</b>", parse_mode="HTML")


# =================== MENUS ===================
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


@dp.callback_query(F.data == "menu:main")
async def cb_menu(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await cb.message.edit_text("🏠 Главное меню:", reply_markup=main_menu())

@dp.callback_query(F.data == "menu:balance")
async def cb_balance(cb: CallbackQuery):
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    await cb.message.edit_text(f"💎 <b>{float(p['balance']):.2f} {cur}</b>", parse_mode="HTML", reply_markup=back_kb())

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
    await cb.message.edit_text(
        f"💰 <b>Пополнение</b>\nВалюта: <b>{cur}</b> (смени через /currency)\nВыбери сумму (мин. {MIN_DEPOSIT}):",
        parse_mode="HTML", reply_markup=deposit_kb())

@dp.callback_query(F.data.startswith("dep:"))
async def cb_dep_amount(cb: CallbackQuery, state: FSMContext):
    val = cb.data.split(":")[1]
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if val == "custom":
        await state.set_state(AmountInput.deposit)
        await cb.message.edit_text(
            f"💰 Введи сумму в {cur} (мин. {MIN_DEPOSIT}).\nОтмена — /start",
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
    await cb_withdraw_dispatch(cb, p)

async def cb_withdraw_dispatch(cb, p):
    bal = float(p["balance"])
    cur = p.get("preferred_currency") or "USDT"
    spent = await daily_withdrawn(p["id"])
    left = MAX_WITHDRAW_DAILY - spent
    hint = ""
    if bal < MIN_WITHDRAW:
        hint = f"\n\n⚠️ Баланс {bal:.2f}, минимум {MIN_WITHDRAW}."
    await cb.message.edit_text(
        f"💸 <b>Вывод в {cur}</b>\n"
        f"Баланс: <b>{bal:.2f}</b>\n"
        f"Лимит/сутки: <b>{max(0,left):.2f}</b> из {MAX_WITHDRAW_DAILY:.0f}\n"
        f"Минимум: {MIN_WITHDRAW}{hint}\n\n"
        f"<b>⚠️ Средства приходят на твой аккаунт @xRocket.</b>\n\n"
        f"Выбери сумму или «Своя сумма»:",
        parse_mode="HTML", reply_markup=withdraw_kb(bal))

@dp.callback_query(F.data.startswith("wd:"))
async def cb_wd_amount(cb: CallbackQuery, state: FSMContext):
    val = cb.data.split(":")[1]
    p = await get_or_create_profile(cb.from_user.model_dump())
    cur = p.get("preferred_currency") or "USDT"
    if val == "custom":
        await state.set_state(AmountInput.withdraw)
        await cb.message.edit_text(
            f"💸 Введи сумму вывода в {cur} (мин. {MIN_WITHDRAW}).\n"
            f"Баланс: <b>{float(p['balance']):.2f}</b>\n\n"
            f"<b>⚠️ Средства придут на @xRocket.</b>\nОтмена — /start",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="⬅️ Назад", callback_data="menu:withdraw")]]))
        return
    amount = float(val)
    if amount < MIN_WITHDRAW:
        return await cb.answer(f"Минимум {MIN_WITHDRAW}", show_alert=True)
    if float(p["balance"]) < amount:
        return await cb.answer("Недостаточно средств", show_alert=True)
    await cb.message.edit_text("⏳ Обработка…", reply_markup=back_kb())
    try: await do_withdraw(p, cb.from_user.id, amount, cur)
    except HTTPException as e: return await cb.message.edit_text(f"❌ {e.detail}", reply_markup=back_kb())
    except Exception as e:
        log.exception("payout failed")
        return await cb.message.edit_text(f"❌ {e}", reply_markup=back_kb())
    await cb.message.edit_text(f"✅ Выплата <b>{amount} {cur}</b> отправлена.", parse_mode="HTML", reply_markup=back_kb())


# =================== FSM ===================
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
    except Exception as e:
        log.exception("create_invoice failed")
        return await message.answer(f"❌ {e}", reply_markup=back_kb())
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
        return await message.answer(f"❌ Недостаточно. Баланс: <b>{float(p['balance']):.2f}</b>", parse_mode="HTML")
    await state.clear()
    msg = await message.answer("⏳ Обработка…")
    try: await do_withdraw(p, message.from_user.id, amount, cur)
    except HTTPException as e: return await msg.edit_text(f"❌ {e.detail}", reply_markup=back_kb())
    except Exception as e:
        log.exception("payout failed")
        return await msg.edit_text(f"❌ {e}", reply_markup=back_kb())
    await msg.edit_text(f"✅ Выплата <b>{amount} {cur}</b> отправлена.", parse_mode="HTML", reply_markup=back_kb())


# =================== DICE ===================
def dice_bet_kb():
    amounts = [0.5, 1, 5, 10, 25, 50]
    rows = [[InlineKeyboardButton(text=f"{a} ₮", callback_data=f"dice_bet:{a}") for a in amounts[i:i+3]]
            for i in range(0, len(amounts), 3)]
    rows.append([InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def dice_num_kb(bet):
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=str(n), callback_data=f"dnum:{n}:{bet}") for n in (1,2,3)],
        [InlineKeyboardButton(text=str(n), callback_data=f"dnum:{n}:{bet}") for n in (4,5,6)],
        [InlineKeyboardButton(text="⬅️ Назад", callback_data="menu:dice"),
         InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])

@dp.callback_query(F.data == "menu:dice")
async def cb_dice(cb: CallbackQuery):
    await cb.message.edit_text(
        f"🎲 <b>Кубы</b>\nВыбери число 1–6. Если выпадет — ×<b>{DICE_PAYOUT}</b>.\nСначала ставка:",
        parse_mode="HTML", reply_markup=dice_bet_kb())

@dp.callback_query(F.data.startswith("dice_bet:"))
async def cb_dice_bet(cb: CallbackQuery):
    bet = float(cb.data.split(":")[1])
    p = await get_or_create_profile(cb.from_user.model_dump())
    if float(p["balance"]) < bet:
        return await cb.answer("Недостаточно средств", show_alert=True)
    await cb.message.edit_text(f"🎲 Ставка <b>{bet}</b>. Выбери число:",
                               parse_mode="HTML", reply_markup=dice_num_kb(bet))

@dp.callback_query(F.data.startswith("dnum:"))
async def cb_dice_num(cb: CallbackQuery):
    _, num_s, bet_s = cb.data.split(":")
    num, bet = int(num_s), float(bet_s)
    p = await get_or_create_profile(cb.from_user.model_dump())
    if float(p["balance"]) < bet:
        return await cb.answer("Недостаточно средств", show_alert=True)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet,
        "currency": "USDT", "status": "completed", "meta": {"game": "dice", "chosen": num}}))
    await cb.message.edit_text(f"🎲 Бросаем…", parse_mode="HTML")
    dice_msg = await bot.send_dice(chat_id=cb.message.chat.id, emoji="🎲")
    result = dice_msg.dice.value
    await asyncio.sleep(3.5)
    win = (result == num)
    profit = -bet
    if win:
        payout = round(bet * DICE_PAYOUT, 8); profit = round(payout - bet, 8)
        await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
        await sb(supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit,
            "currency": "USDT", "status": "completed", "meta": {"game": "dice"}}))
        text = f"🎲 <b>{result}</b> · твоё {num}\n✅ +{profit:.2f} (×{DICE_PAYOUT})"
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
        text = f"🎲 <b>{result}</b> · твоё {num}\n❌ −{bet:.2f}"
    await log_round(p["id"], "dice", bet, {"result": result, "chosen": num, "win": win},
                    profit, "telegram_dice", 0)
    p2 = await get_or_create_profile(cb.from_user.model_dump())
    text += f"\n\n💎 <b>{float(p2['balance']):.2f}</b>"
    again_kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎲 Ещё раз", callback_data=f"dice_bet:{bet}")],
        [InlineKeyboardButton(text="💰 Пополнить", callback_data="menu:deposit"),
         InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])
    await bot.send_message(cb.message.chat.id, text, parse_mode="HTML", reply_markup=again_kb)


# =================== MENU REF ===================
@dp.callback_query(F.data == "menu:ref")
async def cb_ref_menu(cb: CallbackQuery):
    p = await get_or_create_profile(cb.from_user.model_dump())
    info = referral_info_sync(p)
    share_url = f"https://t.me/share/url?url={info['link']}&text=Играю в GoldCash!"
    invited = (await sb(supabase.table("profiles").select("first_name, username, created_at")
                        .eq("referrer_id", p["id"]).order("created_at", desc=True).limit(50))).data or []
    text = (
        f"👥 <b>Приглашай друзей</b>\n\n"
        f"<b>{REFERRAL_SHARE*100:.0f}%</b> от проигрыша каждого!\n\n"
        f"👤 Приглашено: <b>{len(invited)}</b>\n"
        f"💰 Заработано: <b>{float(p.get('ref_earnings') or 0):.2f}</b>\n\n"
        f"Ссылка:\n<code>{info['link']}</code>"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📤 Поделиться", url=share_url)],
        [InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])
    await cb.message.edit_text(text, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)


# =================== FastAPI ===================
@asynccontextmanager
async def lifespan(app):
    global BOT_USERNAME
    me = await bot.get_me()
    BOT_USERNAME = me.username
    log.info("start · house_edge=%.3f · admins=%s · bot=@%s",
             HOUSE_EDGE, ADMIN_IDS, BOT_USERNAME)
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
        "withdraw_cooldown_min": WITHDRAW_COOLDOWN_MIN,
        "max_withdraw_daily": MAX_WITHDRAW_DAILY,
        "referral_share": REFERRAL_SHARE,
        "currencies": SUPPORTED_CURRENCIES,
        "rtp": round(1 - HOUSE_EDGE, 4),
        "payouts": {
            "dice": DICE_PAYOUT, "roulette_rb": ROUL_RB_PAYOUT,
            "roulette_dozen": ROUL_DOZEN_PAYOUT, "roulette_number": ROUL_NUM_PAYOUT,
        },
    }

@app.post("/api/auth")
async def auth(user: dict = Depends(get_current_user)):
    return await get_or_create_profile(user)


def _profile_sync(user):
    tg_id = int(user["id"])
    r = supabase.table("profiles").select("*").eq("telegram_id", tg_id).execute()
    p = r.data[0] if r.data else supabase.table("profiles").insert({
        "telegram_id": tg_id, "username": user.get("username"),
        "first_name": user.get("first_name"), "preferred_currency": "USDT",
    }).execute().data[0]
    try:
        tx = supabase.table("transactions").select("type, amount, status").eq("user_id", p["id"]).execute().data or []
        rounds = supabase.table("game_rounds").select("id").eq("user_id", p["id"]).execute().data or []
    except Exception:
        tx, rounds = [], []
    deposits = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    withdrawals = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    wins = sum(float(t["amount"]) for t in tx if t["type"] == "win")
    bets = sum(float(t["amount"]) for t in tx if t["type"] == "bet")
    return {
        "id": p["id"], "telegram_id": p["telegram_id"],
        "username": p.get("username"), "first_name": p.get("first_name"),
        "balance": float(p["balance"]),
        "client_seed": p.get("client_seed") or "",
        "nonce": int(p.get("nonce") or 0),
        "ref_earnings": float(p.get("ref_earnings") or 0),
        "preferred_currency": p.get("preferred_currency") or "USDT",
        "is_banned": bool(p.get("is_banned")),
        "stats": {
            "total_games": len(rounds), "total_wagered": round(bets, 2),
            "total_profit": round(wins - bets, 2), "best_mult": 1.0,
            "deposits": round(deposits, 2), "withdrawals": round(withdrawals, 2),
            "wins": round(wins, 2),
        },
    }

@app.get("/api/profile")
async def profile(user: dict = Depends(get_current_user)):
    try:
        return await asyncio.to_thread(_profile_sync, user)
    except Exception:
        log.exception("profile endpoint failed")
        raise HTTPException(500, "profile error")

@app.post("/api/profile/currency")
async def set_currency(body: dict, user: dict = Depends(get_current_user)):
    currency = (body.get("currency") or "").upper()
    if currency not in SUPPORTED_CURRENCIES:
        raise HTTPException(400, "неподдерживаемая валюта")
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
            uid = row["user_id"]
            pr = row.get("profiles") or {}
            a = agg.setdefault(uid, {"name": pr.get("first_name") or pr.get("username") or "anon",
                                     "profit": 0.0, "bets": 0.0, "games": 0})
            a["profit"] += float(row["profit"])
            a["bets"] += float(row["bet_amount"])
            a["games"] += 1
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
    r = await sb(supabase.table("promo_codes").select("*").eq("code", code))
    if not r.data: raise HTTPException(404, "промокод не найден")
    promo = r.data[0]
    if promo.get("max_uses") and promo["uses"] >= promo["max_uses"]:
        raise HTTPException(400, "исчерпан")
    used = await sb(supabase.table("promo_uses").select("id").eq("code", code).eq("user_id", p["id"]))
    if used.data: raise HTTPException(400, "уже использовал")
    amount = float(promo["amount"])
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": amount})
    await sb(supabase.table("promo_uses").insert({"code": code, "user_id": p["id"], "amount": amount}))
    await sb(supabase.table("promo_codes").update({"uses": promo["uses"] + 1}).eq("code", code))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bonus", "amount": amount,
        "currency": "USDT", "status": "completed", "meta": {"source": "promo", "code": code}}))
    return {"ok": True, "amount": amount}

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

@app.get("/api/fairness/verify/{round_id}")
async def fairness_verify(round_id: str, user: dict = Depends(get_current_user)):
    p = await get_or_create_profile(user)
    r = await sb(supabase.table("game_rounds").select("*").eq("id", round_id).eq("user_id", p["id"]))
    if not r.data: raise HTTPException(404, "раунд не найден")
    row = r.data[0]
    ss = row.get("server_seed") or ""
    nonce = row.get("nonce") or 0
    cs = p["client_seed"]
    recomputed = None
    if row["game_type"] == "crash":
        recomputed = {"crash_point": crash_point(ss, cs, nonce)}
    elif row["game_type"] == "mines":
        mines = int((row["result"] or {}).get("mines") or len((row["result"] or {}).get("positions") or []))
        recomputed = {"positions": mine_positions(ss, cs, nonce, mines)}
    elif row["game_type"] == "roulette":
        recomputed = {"number": roulette_number(ss, cs, nonce)}
    return {"round_id": round_id, "game": row["game_type"], "server_seed": ss,
            "server_seed_hash": hashlib.sha256(ss.encode()).hexdigest() if ss else "",
            "client_seed": cs, "nonce": nonce,
            "stored_result": row["result"], "recomputed": recomputed}

@app.post("/api/payments/deposit")
async def api_deposit(body: dict, user: dict = Depends(get_current_user)):
    amount = float(body.get("amount", 0))
    currency = (body.get("currency") or "USDT").upper()
    if amount < MIN_DEPOSIT: raise HTTPException(400, f"min {MIN_DEPOSIT}")
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "валюта не поддерживается")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    await check_rate_limit(p["id"], "deposit")
    try: inv = await create_deposit_invoice(p, amount, currency)
    except Exception as e:
        log.exception("create_invoice failed")
        raise HTTPException(400, str(e))
    return {"link": inv["link"], "invoice_id": inv.get("invoice_id")}

@app.post("/api/payments/withdraw")
async def api_withdraw(body: dict, user: dict = Depends(get_current_user)):
    amount = float(body.get("amount", 0))
    currency = (body.get("currency") or "USDT").upper()
    if amount < MIN_WITHDRAW: raise HTTPException(400, f"min {MIN_WITHDRAW}")
    if currency not in SUPPORTED_CURRENCIES: raise HTTPException(400, "валюта не поддерживается")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    await check_rate_limit(p["id"], "withdraw")
    if float(p["balance"]) < amount: raise HTTPException(400, "insufficient balance")
    try: payout = await do_withdraw(p, user["id"], amount, currency)
    except HTTPException: raise
    except Exception as e:
        log.exception("payout failed")
        raise HTTPException(400, str(e))
    return {"ok": True, "payout_id": payout.get("id")}

@app.post("/api/webhook/xrocket")
async def xrocket_webhook(request: Request):
    raw = await request.body()
    sig = request.headers.get("Signature"); ver = request.headers.get("Signature-Version")
    ts = request.headers.get("Signature-Timestamp")
    if not all([sig, ver, ts]): raise HTTPException(401, "missing sig")
    if ver != "v1": raise HTTPException(401, "unsupported")
    if abs(int(time.time() * 1000) - int(ts)) > 300_000: raise HTTPException(401, "too old")
    expected = hmac.new(XROCKET_WEBHOOK_SECRET.encode(),
                        f"{ts}.{raw.decode()}".encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, sig): raise HTTPException(401, "bad sig")
    event = json.loads(raw)
    if event.get("type") == "invoice" and event.get("status") == "paid":
        cid = event.get("clientInvoiceId") or event.get("payload") or event.get("invoiceId")
        if cid:
            tx = (await sb(supabase.table("transactions").select("*")
                           .eq("external_id", str(cid)).eq("status", "pending"))).data
            if not tx:
                tx = (await sb(supabase.table("transactions").select("*")
                               .eq("meta->>invoice_id", str(cid)).eq("status", "pending"))).data
            if tx:
                row = tx[0]
                await sb_rpc("change_balance", {"p_user_id": row["user_id"], "p_delta": float(row["amount"])})
                await sb(supabase.table("transactions").update({"status": "completed"}).eq("id", row["id"]))
                log.info("deposit credited: %s", cid)
    return {"ok": True}


# =================== CRASH API ===================
def _crash_state_sync(p):
    status = crash_state["status"]
    mult = 1.0
    if status == "running" and crash_state["started_at"]:
        mult = crash_mult(time.time() - crash_state["started_at"])
    elif status == "crashed":
        mult = crash_state["crash_point"] or 1.0
    bets = []; my_bet = None
    rid = crash_state["round_id"]
    if rid:
        r = supabase.table("crash_bets").select("user_id, username, amount, cashout_mult, payout, status") \
            .eq("round_id", rid).order("created_at", desc=True).execute()
        for b in r.data or []:
            item = {"user_id": b["user_id"], "username": b.get("username") or "anon",
                    "amount": float(b["amount"]),
                    "cashout_mult": float(b["cashout_mult"]) if b["cashout_mult"] else None,
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
        log.exception("crash_state failed")
        raise HTTPException(500, "crash state error")

@app.post("/api/crash/bet")
async def crash_bet(body: dict, user: dict = Depends(get_current_user)):
    if crash_state["status"] != "betting": raise HTTPException(400, "ставки закрыты")
    bet = float(body.get("bet", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    await check_rate_limit(p["id"], "bet")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    rid = crash_state["round_id"]
    ex = await sb(supabase.table("crash_bets").select("id").eq("round_id", rid).eq("user_id", p["id"]))
    if ex.data: raise HTTPException(400, "уже поставил в этом раунде")
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    await sb(supabase.table("crash_bets").insert({
        "round_id": rid, "user_id": p["id"],
        "username": p.get("first_name") or p.get("username") or "anon",
        "amount": bet, "status": "active"}))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet,
        "currency": "USDT", "status": "completed", "meta": {"game": "crash_global"}}))
    return {"ok": True}

@app.post("/api/crash/cashout")
async def crash_cashout_global(user: dict = Depends(get_current_user)):
    if crash_state["status"] != "running": raise HTTPException(400, "раунд не идёт")
    elapsed = time.time() - crash_state["started_at"]
    mult = crash_mult(elapsed)
    if mult >= crash_state["crash_point"]:
        raise HTTPException(400, "слишком поздно")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    rid = crash_state["round_id"]
    b = await sb(supabase.table("crash_bets").select("*").eq("round_id", rid).eq("user_id", p["id"]).eq("status", "active"))
    if not b.data: raise HTTPException(400, "нет активной ставки")
    bet = b.data[0]
    amount = float(bet["amount"])
    payout = round(amount * mult, 8); profit = round(payout - amount, 8)
    await sb(supabase.table("crash_bets").update({
        "status": "cashed", "cashout_mult": mult, "payout": payout}).eq("id", bet["id"]))
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout})
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit,
        "currency": "USDT", "status": "completed", "meta": {"game": "crash_global"}}))
    await log_round(p["id"], "crash", amount, {"global": True, "mult": mult, "round": rid},
                    profit, crash_state["server_seed"] or "", 0)
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit}


def _roulette_bets_sync():
    r = supabase.table("game_rounds").select("result, bet_amount, profit, profiles(username, first_name)") \
        .eq("game_type", "roulette").order("created_at", desc=True).limit(25).execute()
    out = []
    for row in r.data or []:
        pr = row.get("profiles") or {}
        name = pr.get("first_name") or pr.get("username") or "anon"
        res = row.get("result") or {}
        out.append({"name": name, "number": res.get("n"), "bet_type": res.get("bet_type"),
                    "win": bool(res.get("win", False)), "amount": float(row["bet_amount"]),
                    "profit": float(row["profit"])})
    return out

@app.get("/api/roulette/bets")
async def roulette_bets():
    try: return await asyncio.to_thread(_roulette_bets_sync)
    except Exception: return []


# =================== MINES ===================
@app.post("/api/games/mines/start")
async def mines_start(body: dict, user: dict = Depends(get_current_user)):
    bet = float(body.get("bet", 0)); mines = int(body.get("mines", 3))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    if not (1 <= mines <= 24): raise HTTPException(400, "mines 1..24")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    await check_rate_limit(p["id"], "bet")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    if await get_active_round(p["id"]): raise HTTPException(400, "active round exists")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    positions = mine_positions(ss, p["client_seed"], nonce, mines)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
    await sb(supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]))
    await sb(supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "mines", "bet_amount": bet,
        "state": {"mines": mines, "positions": positions, "revealed": []},
        "server_seed": ss, "nonce": nonce}))
    await sb(supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet,
        "currency": "USDT", "status": "completed", "meta": {"game": "mines"}}))
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
        "user_id": p["id"], "type": "win", "amount": profit,
        "currency": "USDT", "status": "completed", "meta": {"game": "mines"}}))
    await clear_active_round(p["id"])
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit, "positions": st["positions"]}

RED = {1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36}
BLACK = {2,4,6,8,10,11,13,15,17,20,22,24,26,28,29,31,33,35}

@app.post("/api/games/roulette/bet")
async def roulette_bet(body: dict, user: dict = Depends(get_current_user)):
    bet = float(body.get("bet", 0)); bt = body.get("type"); bv = body.get("value")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = await get_or_create_profile(user)
    await ensure_not_banned(p)
    await check_rate_limit(p["id"], "bet")
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    n = roulette_number(ss, p["client_seed"], nonce)
    await sb_rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet})
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
            "user_id": p["id"], "type": "win", "amount": profit,
            "currency": "USDT", "status": "completed", "meta": {"game": "roulette"}}))
    else:
        asyncio.create_task(credit_referrer_on_loss(p["id"], bet))
    await log_round(p["id"], "roulette", bet, {"n": n, "bet_type": bt, "win": win}, profit, ss, nonce)
    color = "green" if n == 0 else ("red" if n in RED else "black")
    return {"ok": True, "number": n, "color": color, "win": win,
            "payout": round(bet * pm, 8) if win else 0, "profit": profit}
