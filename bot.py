import os, json, hmac, hashlib, logging, asyncio, time, math
from urllib.parse import parse_qsl
from contextlib import asynccontextmanager
from math import comb
from datetime import datetime, timezone

from fastapi import FastAPI, Header, HTTPException, Depends, Request
from fastapi.middleware.cors import CORSMiddleware
from aiogram import Bot, Dispatcher, F
from aiogram.types import (Message, CallbackQuery, InlineKeyboardMarkup,
                           InlineKeyboardButton, WebAppInfo)
from aiogram.filters import Command, CommandObject
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.context import FSMContext
from supabase import create_client, Client
from aiorocket2 import xRocketClient

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("casino")

BOT_TOKEN = os.environ["BOT_TOKEN"]
WEBAPP_URL = os.environ["WEBAPP_URL"]
SUPABASE_URL = os.environ["SUPABASE_URL"]
SUPABASE_SERVICE_KEY = os.environ["SUPABASE_SERVICE_KEY"]
XROCKET_API_KEY = os.environ["XROCKET_API_KEY"]
XROCKET_WEBHOOK_SECRET = os.environ["XROCKET_WEBHOOK_SECRET"]
HOUSE_EDGE = float(os.environ.get("HOUSE_EDGE", "0.05"))
MIN_BET = float(os.environ.get("MIN_BET", "0.1"))
MAX_BET = float(os.environ.get("MAX_BET", "1000"))
MIN_DEPOSIT = float(os.environ.get("MIN_DEPOSIT", "0.1"))
MIN_WITHDRAW = float(os.environ.get("MIN_WITHDRAW", "0.5"))
MAX_DEPOSIT = float(os.environ.get("MAX_DEPOSIT", "100000"))
WITHDRAW_COOLDOWN_MIN = int(os.environ.get("WITHDRAW_COOLDOWN_MIN", "15"))
DICE_PAYOUT = 5.5

CRASH_BETTING_SEC = 10
CRASH_COOLDOWN_SEC = 4

supabase: Client = create_client(SUPABASE_URL, SUPABASE_SERVICE_KEY)
xrocket: xRocketClient | None = None

crash_state = {
    "round_id": None, "status": "idle", "server_seed": None,
    "crash_point": None, "started_at": None, "betting_ends_at": None,
}


class AmountInput(StatesGroup):
    deposit = State()
    withdraw = State()


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

def get_or_create_profile(tg_user):
    tg_id = int(tg_user["id"])
    r = supabase.table("profiles").select("*").eq("telegram_id", tg_id).execute()
    if r.data: return r.data[0]
    return supabase.table("profiles").insert({
        "telegram_id": tg_id,
        "username": tg_user.get("username"),
        "first_name": tg_user.get("first_name"),
    }).execute().data[0]

def get_active_round(uid):
    r = supabase.table("active_rounds").select("*").eq("user_id", uid).execute()
    return r.data[0] if r.data else None

def clear_active_round(uid):
    supabase.table("active_rounds").delete().eq("user_id", uid).execute()

def log_round(uid, game, bet, result, profit, ss, nonce):
    try:
        supabase.table("game_rounds").insert({
            "user_id": uid, "game_type": game, "bet_amount": bet,
            "result": result, "profit": profit, "server_seed": ss, "nonce": nonce,
        }).execute()
    except Exception:
        log.exception("log_round failed")

def get_user_stats(uid):
    tx = supabase.table("transactions").select("type, amount, status").eq("user_id", uid).execute().data or []
    rounds = supabase.table("game_rounds").select("id").eq("user_id", uid).execute().data or []
    deposits = sum(float(t["amount"]) for t in tx if t["type"] == "deposit" and t["status"] == "completed")
    withdrawals = sum(float(t["amount"]) for t in tx if t["type"] == "withdraw" and t["status"] == "completed")
    wins = sum(float(t["amount"]) for t in tx if t["type"] == "win")
    bets = sum(float(t["amount"]) for t in tx if t["type"] == "bet")
    return {
        "games": len(rounds), "deposits": round(deposits, 2),
        "withdrawals": round(withdrawals, 2), "bets": round(bets, 2),
        "wins": round(wins, 2), "net": round(wins - bets, 2),
    }


# =================== payments ===================
async def create_deposit_invoice(profile, amount):
    cid = f"dep_{profile['id'][:8]}_{int(time.time())}"
    inv = await xrocket.create_invoice(
        amount=amount, currency="USDT", description="GoldCash deposit",
        min_payment=0, num_payments=1, client_invoice_id=cid,
    )
    supabase.table("transactions").insert({
        "user_id": profile["id"], "type": "deposit", "amount": amount,
        "currency": "USDT", "external_id": cid, "status": "pending",
        "meta": {"invoice_id": inv.get("id")},
    }).execute()
    return inv

async def do_withdraw(profile, tg_id, amount):
    last = supabase.table("transactions").select("created_at") \
        .eq("user_id", profile["id"]).eq("type", "deposit").eq("status", "completed") \
        .order("created_at", desc=True).limit(1).execute()
    if last.data:
        try:
            dt = datetime.fromisoformat(last.data[0]["created_at"].replace("Z", "+00:00"))
            left = WITHDRAW_COOLDOWN_MIN * 60 - (datetime.now(timezone.utc) - dt).total_seconds()
            if left > 0:
                m, s = divmod(int(left), 60)
                raise HTTPException(400, f"после депозита подожди {m}м {s}с")
        except HTTPException: raise
        except Exception: log.exception("cooldown check failed")
    cid = f"wd_{profile['id'][:8]}_{int(time.time())}"
    payout = await xrocket.create_payout(
        target=str(tg_id), target_type="telegram_user_id",
        asset="USDT", amount=amount, description="GoldCash withdraw",
        client_payout_id=cid,
    )
    supabase.rpc("change_balance", {"p_user_id": profile["id"], "p_delta": -amount}).execute()
    supabase.table("transactions").insert({
        "user_id": profile["id"], "type": "withdraw", "amount": amount,
        "currency": "USDT", "external_id": cid, "status": "completed",
        "meta": {"payout_id": payout.get("payoutId")},
    }).execute()
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
            res = supabase.table("crash_rounds").insert({
                "status": "betting", "server_seed": ss, "crash_point": cp,
            }).execute()
            round_id = res.data[0]["id"]
            crash_state.update({
                "round_id": round_id, "status": "betting",
                "server_seed": ss, "crash_point": cp,
                "started_at": None, "betting_ends_at": now + CRASH_BETTING_SEC,
            })
            await asyncio.sleep(CRASH_BETTING_SEC)

            started = time.time()
            supabase.table("crash_rounds").update({
                "status": "running",
                "started_at": datetime.now(timezone.utc).isoformat(),
            }).eq("id", round_id).execute()
            crash_state["status"] = "running"
            crash_state["started_at"] = started

            duration = max(0.4, math.log(cp) / math.log(1.07)) if cp > 1.0 else 0.4
            await asyncio.sleep(duration)

            supabase.table("crash_rounds").update({
                "status": "crashed",
                "ended_at": datetime.now(timezone.utc).isoformat(),
            }).eq("id", round_id).execute()
            crash_state["status"] = "crashed"

            lost = supabase.table("crash_bets").select("*") \
                .eq("round_id", round_id).eq("status", "active").execute().data or []
            for b in lost:
                supabase.table("crash_bets").update({"status": "lost"}).eq("id", b["id"]).execute()
                log_round(b["user_id"], "crash", float(b["amount"]),
                          {"global": True, "crashed_at": cp}, -float(b["amount"]), ss, 0)

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
        [InlineKeyboardButton(text="📊 Статистика", callback_data="menu:stats"),
         InlineKeyboardButton(text="👤 Баланс", callback_data="menu:balance")],
        [InlineKeyboardButton(text="🌐 Открыть казино", web_app=WebAppInfo(url=WEBAPP_URL))],
    ])

def back_kb():
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")]])

def fmt_stats(s, balance, first_name):
    return (
        f"👤 <b>{first_name or 'игрок'}</b>\n\n"
        f"💎 <b>Баланс:</b> {balance:.2f} ₮\n"
        f"━━━━━━━━━━━━━━━\n"
        f"📥 Пополнено: <b>{s['deposits']:.2f} ₮</b>\n"
        f"📤 Выведено: <b>{s['withdrawals']:.2f} ₮</b>\n"
        f"🎯 Ставок: <b>{s['bets']:.2f} ₮</b>\n"
        f"🏆 Выигрышей: <b>{s['wins']:.2f} ₮</b>\n"
        f"🎮 Игр: <b>{s['games']}</b>\n"
        f"📊 Профит: <b>{s['net']:+.2f} ₮</b>"
    )

@dp.message(Command("start"))
async def cmd_start(message: Message, state: FSMContext):
    await state.clear()
    p = get_or_create_profile(message.from_user.model_dump())
    await message.answer(
        f"Привет, {message.from_user.first_name}! 👋\n\n"
        f"💎 Твой баланс: <b>{float(p['balance']):.2f} ₮</b>\n\n"
        f"Играй в кубы, пополняй и выводи прямо здесь.",
        reply_markup=main_menu(), parse_mode="HTML",
    )

@dp.message(Command("balance"))
async def cmd_balance(message: Message):
    p = get_or_create_profile(message.from_user.model_dump())
    await message.answer(f"💎 Баланс: <b>{float(p['balance']):.2f} ₮</b>",
                         parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("stats"))
async def cmd_stats(message: Message):
    p = get_or_create_profile(message.from_user.model_dump())
    s = get_user_stats(p["id"])
    await message.answer(fmt_stats(s, float(p["balance"]), message.from_user.first_name),
                         parse_mode="HTML", reply_markup=back_kb())

@dp.message(Command("dice"))
async def cmd_dice(message: Message):
    await message.answer("🎲 Выбери ставку:", reply_markup=dice_bet_kb())

@dp.message(Command("deposit"))
async def cmd_deposit(message: Message, command: CommandObject):
    try: amount = float(command.args)
    except Exception: return await message.answer(f"Использование: /deposit 1 (мин {MIN_DEPOSIT})")
    if amount < MIN_DEPOSIT: return await message.answer(f"Минимум {MIN_DEPOSIT} USDT")
    p = get_or_create_profile(message.from_user.model_dump())
    try: inv = await create_deposit_invoice(p, amount)
    except Exception as e:
        return await message.answer(f"Ошибка: {e}")
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="💳 Оплатить", url=inv["link"])]])
    await message.answer(f"💰 Счёт на <b>{amount} USDT</b> создан.", parse_mode="HTML", reply_markup=kb)


# =================== DEPOSIT / WITHDRAW MENUS ===================
def deposit_kb():
    amounts = [1, 5, 10, 25, 50, 100]
    rows = [[InlineKeyboardButton(text=f"{a} ₮", callback_data=f"dep:{a}") for a in amounts[i:i+3]]
            for i in range(0, len(amounts), 3)]
    rows.append([InlineKeyboardButton(text="✏️ Своя сумма", callback_data="dep:custom")])
    rows.append([InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def withdraw_kb(balance):
    amounts = [a for a in [1, 5, 10, 25, 50, 100] if a <= balance and a >= MIN_WITHDRAW]
    rows = []
    if amounts:
        rows = [[InlineKeyboardButton(text=f"{a} ₮", callback_data=f"wd:{a}") for a in amounts[i:i+3]]
                for i in range(0, len(amounts), 3)]
    rows.append([InlineKeyboardButton(text="✏️ Своя сумма", callback_data="wd:custom")])
    rows.append([InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


@dp.callback_query(F.data == "menu:main")
async def cb_menu(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await cb.message.edit_text("🏠 Главное меню:", reply_markup=main_menu())

@dp.callback_query(F.data == "menu:balance")
async def cb_balance(cb: CallbackQuery):
    p = get_or_create_profile(cb.from_user.model_dump())
    await cb.message.edit_text(f"💎 Баланс: <b>{float(p['balance']):.2f} ₮</b>",
                               parse_mode="HTML", reply_markup=back_kb())

@dp.callback_query(F.data == "menu:stats")
async def cb_stats(cb: CallbackQuery):
    p = get_or_create_profile(cb.from_user.model_dump())
    s = get_user_stats(p["id"])
    await cb.message.edit_text(fmt_stats(s, float(p["balance"]), cb.from_user.first_name),
                               parse_mode="HTML", reply_markup=back_kb())

@dp.callback_query(F.data == "menu:deposit")
async def cb_deposit(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await cb.message.edit_text(
        f"💰 <b>Пополнение</b>\n\nВыбери сумму или «Своя сумма» (мин. {MIN_DEPOSIT}):",
        parse_mode="HTML", reply_markup=deposit_kb())

@dp.callback_query(F.data.startswith("dep:"))
async def cb_dep_amount(cb: CallbackQuery, state: FSMContext):
    val = cb.data.split(":")[1]
    if val == "custom":
        await state.set_state(AmountInput.deposit)
        await cb.message.edit_text(
            f"💰 Введи сумму пополнения в USDT (например, <code>0.5</code>).\n\n"
            f"Минимум: {MIN_DEPOSIT}.\nОтмена — /start",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="⬅️ Назад", callback_data="menu:deposit")]
            ]))
        return
    amount = float(val)
    p = get_or_create_profile(cb.from_user.model_dump())
    try: inv = await create_deposit_invoice(p, amount)
    except Exception as e:
        return await cb.answer(f"Ошибка: {e}", show_alert=True)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💳 Оплатить", url=inv["link"])],
        [InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")],
    ])
    await cb.message.edit_text(f"💰 Счёт на <b>{amount} USDT</b> создан.",
                               parse_mode="HTML", reply_markup=kb)

@dp.callback_query(F.data == "menu:withdraw")
async def cb_withdraw(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    p = get_or_create_profile(cb.from_user.model_dump())
    bal = float(p["balance"])
    if bal < MIN_WITHDRAW:
        return await cb.answer(f"Минимум для вывода — {MIN_WITHDRAW} USDT", show_alert=True)
    await cb.message.edit_text(
        f"💸 <b>Баланс:</b> {bal:.2f} ₮\n\nВыбери сумму или «Своя сумма» (мин. {MIN_WITHDRAW}):",
        parse_mode="HTML", reply_markup=withdraw_kb(bal))

@dp.callback_query(F.data.startswith("wd:"))
async def cb_wd_amount(cb: CallbackQuery, state: FSMContext):
    val = cb.data.split(":")[1]
    p = get_or_create_profile(cb.from_user.model_dump())
    if val == "custom":
        await state.set_state(AmountInput.withdraw)
        await cb.message.edit_text(
            f"💸 Введи сумму вывода в USDT (например, <code>0.5</code>).\n\n"
            f"Твой баланс: <b>{float(p['balance']):.2f} ₮</b>.\nМинимум: {MIN_WITHDRAW}.\nОтмена — /start",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="⬅️ Назад", callback_data="menu:withdraw")]
            ]))
        return
    amount = float(val)
    if amount < MIN_WITHDRAW:
        return await cb.answer(f"Минимум {MIN_WITHDRAW} USDT", show_alert=True)
    if float(p["balance"]) < amount:
        return await cb.answer("Недостаточно средств", show_alert=True)
    try:
        await do_withdraw(p, cb.from_user.id, amount)
    except HTTPException as e: return await cb.answer(str(e.detail), show_alert=True)
    except Exception as e:
        log.exception("payout failed")
        return await cb.answer(f"Ошибка: {e}", show_alert=True)
    await cb.message.edit_text(f"✅ Выплата <b>{amount} ₮</b> отправлена.",
                               parse_mode="HTML", reply_markup=back_kb())


# =================== FSM handlers ===================
@dp.message(AmountInput.deposit)
async def fsm_deposit_amount(message: Message, state: FSMContext):
    try:
        amount = float(message.text.replace(",", ".").strip())
    except Exception:
        return await message.answer("❌ Не число. Введи сумму, например <code>0.5</code>", parse_mode="HTML")
    if amount < MIN_DEPOSIT:
        return await message.answer(f"❌ Минимум {MIN_DEPOSIT} USDT")
    if amount > MAX_DEPOSIT:
        return await message.answer(f"❌ Слишком много (макс {MAX_DEPOSIT})")
    await state.clear()
    p = get_or_create_profile(message.from_user.model_dump())
    try:
        inv = await create_deposit_invoice(p, amount)
    except Exception as e:
        log.exception("create_invoice failed")
        return await message.answer(f"Ошибка: {e}", reply_markup=back_kb())
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💳 Оплатить", url=inv["link"])],
        [InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")],
    ])
    await message.answer(
        f"💰 Счёт на <b>{amount} USDT</b> создан.\n\nНажми «Оплатить», оплати в xRocket.",
        parse_mode="HTML", reply_markup=kb)

@dp.message(AmountInput.withdraw)
async def fsm_withdraw_amount(message: Message, state: FSMContext):
    try:
        amount = float(message.text.replace(",", ".").strip())
    except Exception:
        return await message.answer("❌ Не число. Введи сумму, например <code>0.5</code>", parse_mode="HTML")
    p = get_or_create_profile(message.from_user.model_dump())
    if amount < MIN_WITHDRAW:
        return await message.answer(f"❌ Минимум {MIN_WITHDRAW} USDT")
    if float(p["balance"]) < amount:
        return await message.answer(
            f"❌ Недостаточно средств. Баланс: <b>{float(p['balance']):.2f} ₮</b>",
            parse_mode="HTML")
    await state.clear()
    try:
        await do_withdraw(p, message.from_user.id, amount)
    except HTTPException as e:
        return await message.answer(f"❌ {e.detail}", reply_markup=back_kb())
    except Exception as e:
        log.exception("payout failed")
        return await message.answer(f"Ошибка: {e}", reply_markup=back_kb())
    await message.answer(
        f"✅ Выплата <b>{amount} ₮</b> отправлена на твой аккаунт xRocket.",
        parse_mode="HTML", reply_markup=back_kb())


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
         InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")],
    ])

@dp.callback_query(F.data == "menu:dice")
async def cb_dice(cb: CallbackQuery):
    await cb.message.edit_text(
        f"🎲 <b>Игра в кубы</b>\n\nВыбери число 1–6. Если выпадет — ×<b>{DICE_PAYOUT}</b>.\n\nСначала ставка:",
        parse_mode="HTML", reply_markup=dice_bet_kb())

@dp.callback_query(F.data.startswith("dice_bet:"))
async def cb_dice_bet(cb: CallbackQuery):
    bet = float(cb.data.split(":")[1])
    p = get_or_create_profile(cb.from_user.model_dump())
    if float(p["balance"]) < bet:
        return await cb.answer("Недостаточно средств", show_alert=True)
    await cb.message.edit_text(f"🎲 Ставка: <b>{bet} ₮</b>\nВыбери число (1–6):",
                               parse_mode="HTML", reply_markup=dice_num_kb(bet))

@dp.callback_query(F.data.startswith("dnum:"))
async def cb_dice_num(cb: CallbackQuery):
    _, num_s, bet_s = cb.data.split(":")
    num, bet = int(num_s), float(bet_s)
    p = get_or_create_profile(cb.from_user.model_dump())
    if float(p["balance"]) < bet:
        return await cb.answer("Недостаточно средств", show_alert=True)
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet}).execute()
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet,
        "currency": "USDT", "status": "completed", "meta": {"game": "dice", "chosen": num},
    }).execute()
    await cb.message.edit_text(f"🎲 Бросаем...\n\nСтавка: <b>{bet} ₮</b> · Твоё число: <b>{num}</b>", parse_mode="HTML")
    dice_msg = await bot.send_dice(chat_id=cb.message.chat.id, emoji="🎲")
    result = dice_msg.dice.value
    await asyncio.sleep(3.5)
    win = (result == num)
    profit = 0.0
    if win:
        payout = round(bet * DICE_PAYOUT, 8); profit = round(payout - bet, 8)
        supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout}).execute()
        supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit,
            "currency": "USDT", "status": "completed", "meta": {"game": "dice"},
        }).execute()
        text = f"🎲 Выпало: <b>{result}</b>\n🎯 Твоё: <b>{num}</b>\n\n✅ <b>ПОБЕДА!</b> +{profit:.2f} ₮ (×{DICE_PAYOUT})"
    else:
        profit = -bet
        text = f"🎲 Выпало: <b>{result}</b>\n🎯 Твоё: <b>{num}</b>\n\n❌ Проигрыш −{bet:.2f} ₮"
    log_round(p["id"], "dice", bet, {"result": result, "chosen": num, "win": win},
              profit, "telegram_dice", 0)
    p2 = get_or_create_profile(cb.from_user.model_dump())
    text += f"\n\n💎 Баланс: <b>{float(p2['balance']):.2f} ₮</b>"
    again_kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎲 Ещё раз", callback_data=f"dice_bet:{bet}")],
        [InlineKeyboardButton(text="💰 Пополнить", callback_data="menu:deposit"),
         InlineKeyboardButton(text="🏠 Меню", callback_data="menu:main")],
    ])
    await bot.send_message(cb.message.chat.id, text, parse_mode="HTML", reply_markup=again_kb)


# =================== FastAPI ===================
@asynccontextmanager
async def lifespan(app):
    global xrocket
    xrocket = xRocketClient(api_key=XROCKET_API_KEY)
    log.info("xrocket initialized")
    task_bot = asyncio.create_task(dp.start_polling(bot))
    task_crash = asyncio.create_task(crash_loop())
    yield
    task_bot.cancel(); task_crash.cancel()
    try: await task_bot
    except asyncio.CancelledError: pass
    try: await task_crash
    except asyncio.CancelledError: pass
    await bot.session.close()

app = FastAPI(lifespan=lifespan)
app.add_middleware(CORSMiddleware, allow_origins=["*"], allow_credentials=False,
                   allow_methods=["*"], allow_headers=["*"])


@app.get("/")
async def root(): return {"status": "ok"}

@app.get("/api/config")
async def config():
    return {"min_bet": MIN_BET, "max_bet": MAX_BET, "house_edge": HOUSE_EDGE,
            "min_deposit": MIN_DEPOSIT, "min_withdraw": MIN_WITHDRAW,
            "withdraw_cooldown_min": WITHDRAW_COOLDOWN_MIN}

@app.post("/api/auth")
async def auth(user: dict = Depends(get_current_user)):
    return get_or_create_profile(user)

@app.get("/api/profile")
async def profile(user: dict = Depends(get_current_user)):
    try:
        p = get_or_create_profile(user)
        try: s = get_user_stats(p["id"])
        except Exception:
            log.exception("get_user_stats failed")
            s = {"games":0,"deposits":0,"withdrawals":0,"bets":0,"wins":0,"net":0}
        return {
            "id": p["id"], "telegram_id": p["telegram_id"],
            "username": p.get("username"), "first_name": p.get("first_name"),
            "balance": float(p["balance"]),
            "client_seed": p.get("client_seed") or "",
            "nonce": int(p.get("nonce") or 0),
            "stats": {
                "total_games": s["games"], "total_wagered": s["bets"],
                "total_profit": s["net"], "best_mult": 1.0,
                "deposits": s["deposits"], "withdrawals": s["withdrawals"], "wins": s["wins"],
            },
        }
    except Exception:
        log.exception("profile endpoint failed")
        raise HTTPException(500, "profile error")

@app.get("/api/live")
async def live():
    try:
        r = supabase.table("game_rounds").select("game_type, profit, bet_amount, profiles(username, first_name)") \
            .gt("profit", 0).order("created_at", desc=True).limit(20).execute()
        out = []
        for row in r.data or []:
            pr = row.get("profiles") or {}
            name = pr.get("first_name") or pr.get("username") or "anon"
            mult = round((float(row["profit"]) + float(row["bet_amount"])) / float(row["bet_amount"]), 2) \
                   if float(row["bet_amount"]) else 1.0
            out.append({"game": row["game_type"], "name": name,
                        "profit": round(float(row["profit"]), 2), "mult": mult})
        return out
    except Exception:
        log.exception("live failed")
        return []

@app.get("/api/history/games")
async def history_games(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    return supabase.table("game_rounds").select("*").eq("user_id", p["id"]) \
        .order("created_at", desc=True).limit(30).execute().data or []

@app.get("/api/history/transactions")
async def history_tx(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    return supabase.table("transactions").select("*").eq("user_id", p["id"]) \
        .order("created_at", desc=True).limit(30).execute().data or []

@app.get("/api/fairness")
async def fairness(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    r = supabase.table("game_rounds").select("*").eq("user_id", p["id"]) \
        .order("created_at", desc=True).limit(10).execute()
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
    amount = float(body.get("amount", 0))
    if amount < MIN_DEPOSIT: raise HTTPException(400, f"minimum deposit is {MIN_DEPOSIT} USDT")
    p = get_or_create_profile(user)
    try: inv = await create_deposit_invoice(p, amount)
    except Exception as e:
        log.exception("create_invoice failed")
        raise HTTPException(400, f"invoice failed: {e}")
    return {"link": inv["link"], "invoice_id": inv.get("id")}

@app.post("/api/payments/withdraw")
async def api_withdraw(body: dict, user: dict = Depends(get_current_user)):
    amount = float(body.get("amount", 0))
    if amount < MIN_WITHDRAW: raise HTTPException(400, f"minimum withdrawal is {MIN_WITHDRAW} USDT")
    p = get_or_create_profile(user)
    if float(p["balance"]) < amount: raise HTTPException(400, "insufficient balance")
    try: payout = await do_withdraw(p, user["id"], amount)
    except HTTPException: raise
    except Exception as e:
        log.exception("payout failed")
        raise HTTPException(400, f"payout failed: {e}")
    return {"ok": True, "payout_id": payout.get("payoutId")}

@app.post("/api/webhook/xrocket")
async def xrocket_webhook(request: Request):
    raw = await request.body()
    sig = request.headers.get("Signature"); ver = request.headers.get("Signature-Version")
    ts = request.headers.get("Signature-Timestamp")
    if not all([sig, ver, ts]): raise HTTPException(401, "missing signature headers")
    if ver != "v1": raise HTTPException(401, "unsupported version")
    if abs(int(time.time() * 1000) - int(ts)) > 300_000: raise HTTPException(401, "timestamp too old")
    expected = hmac.new(XROCKET_WEBHOOK_SECRET.encode(),
                        f"{ts}.{raw.decode()}".encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, sig): raise HTTPException(401, "invalid signature")
    event = json.loads(raw)
    if event.get("type") == "invoice" and event.get("status") == "paid":
        cid = event.get("clientInvoiceId")
        if cid:
            tx = supabase.table("transactions").select("*").eq("external_id", cid).eq("status", "pending").execute()
            if tx.data:
                row = tx.data[0]
                supabase.rpc("change_balance",
                             {"p_user_id": row["user_id"], "p_delta": float(row["amount"])}).execute()
                supabase.table("transactions").update({"status": "completed"}).eq("id", row["id"]).execute()
                log.info("deposit credited: %s", cid)
    return {"ok": True}


# =================== CRASH API ===================
@app.get("/api/crash/state")
async def crash_state_endpoint(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
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
            item = {
                "user_id": b["user_id"], "username": b.get("username") or "anon",
                "amount": float(b["amount"]),
                "cashout_mult": float(b["cashout_mult"]) if b["cashout_mult"] else None,
                "payout": float(b["payout"] or 0), "status": b["status"],
                "is_me": b["user_id"] == p["id"],
            }
            bets.append(item)
            if item["is_me"]: my_bet = item
    recent = supabase.table("crash_rounds").select("crash_point, created_at") \
        .eq("status", "crashed").order("created_at", desc=True).limit(10).execute()
    return {
        "status": status, "mult": mult,
        "crash_point": crash_state["crash_point"] if status == "crashed" else None,
        "started_at": crash_state["started_at"],
        "betting_ends_in": max(0, (crash_state.get("betting_ends_at") or 0) - time.time()) if status == "betting" else 0,
        "bets": bets, "my_bet": my_bet,
        "recent": [{"crash_point": float(x["crash_point"])} for x in recent.data or []],
        "balance": float(p["balance"]), "round_id": rid,
    }

@app.post("/api/crash/bet")
async def crash_bet(body: dict, user: dict = Depends(get_current_user)):
    if crash_state["status"] != "betting":
        raise HTTPException(400, "ставки закрыты")
    bet = float(body.get("bet", 0))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = get_or_create_profile(user)
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    rid = crash_state["round_id"]
    ex = supabase.table("crash_bets").select("id").eq("round_id", rid).eq("user_id", p["id"]).execute()
    if ex.data: raise HTTPException(400, "ты уже сделал ставку в этом раунде")
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet}).execute()
    supabase.table("crash_bets").insert({
        "round_id": rid, "user_id": p["id"],
        "username": p.get("first_name") or p.get("username") or "anon",
        "amount": bet, "status": "active",
    }).execute()
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet,
        "currency": "USDT", "status": "completed", "meta": {"game": "crash_global"},
    }).execute()
    return {"ok": True}

@app.post("/api/crash/cashout")
async def crash_cashout_global(user: dict = Depends(get_current_user)):
    if crash_state["status"] != "running":
        raise HTTPException(400, "раунд не идёт")
    elapsed = time.time() - crash_state["started_at"]
    mult = crash_mult(elapsed)
    if mult >= crash_state["crash_point"]:
        raise HTTPException(400, "слишком поздно — краш уже случился")
    p = get_or_create_profile(user)
    rid = crash_state["round_id"]
    b = supabase.table("crash_bets").select("*").eq("round_id", rid).eq("user_id", p["id"]) \
        .eq("status", "active").execute()
    if not b.data: raise HTTPException(400, "нет активной ставки")
    bet = b.data[0]
    amount = float(bet["amount"])
    payout = round(amount * mult, 8); profit = round(payout - amount, 8)
    supabase.table("crash_bets").update({
        "status": "cashed", "cashout_mult": mult, "payout": payout,
    }).eq("id", bet["id"]).execute()
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout}).execute()
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit,
        "currency": "USDT", "status": "completed", "meta": {"game": "crash_global"},
    }).execute()
    log_round(p["id"], "crash", amount, {"global": True, "mult": mult, "round": rid},
              profit, crash_state["server_seed"] or "", 0)
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit}


# =================== ROULETTE SHARED ===================
@app.get("/api/roulette/bets")
async def roulette_bets():
    r = supabase.table("game_rounds") \
        .select("result, bet_amount, profit, profiles(username, first_name)") \
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


# =================== MINES / ROULETTE ===================
@app.post("/api/games/mines/start")
async def mines_start(body: dict, user: dict = Depends(get_current_user)):
    bet = float(body.get("bet", 0)); mines = int(body.get("mines", 3))
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    if not (1 <= mines <= 24): raise HTTPException(400, "mines 1..24")
    p = get_or_create_profile(user)
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    if get_active_round(p["id"]): raise HTTPException(400, "active round exists")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    positions = mine_positions(ss, p["client_seed"], nonce, mines)
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet}).execute()
    supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]).execute()
    supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "mines", "bet_amount": bet,
        "state": {"mines": mines, "positions": positions, "revealed": []},
        "server_seed": ss, "nonce": nonce,
    }).execute()
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet,
        "currency": "USDT", "status": "completed", "meta": {"game": "mines"},
    }).execute()
    return {"ok": True, "mines": mines, "mult": mines_mult(mines, 0)}

@app.post("/api/games/mines/reveal")
async def mines_reveal(body: dict, user: dict = Depends(get_current_user)):
    idx = int(body.get("cell", -1))
    if not (0 <= idx < 25): raise HTTPException(400, "bad cell")
    p = get_or_create_profile(user)
    ar = get_active_round(p["id"])
    if not ar or ar["game_type"] != "mines": raise HTTPException(400, "no active mines round")
    st = ar["state"]
    if idx in st["revealed"]: raise HTTPException(400, "already revealed")
    positions = set(st["positions"]); bet = float(ar["bet_amount"])
    if idx in positions:
        log_round(p["id"], "mines", bet,
                  {"mine_hit": idx, "revealed": st["revealed"], "mines": st["mines"], "positions": st["positions"]},
                  -bet, ar["server_seed"], ar["nonce"])
        clear_active_round(p["id"])
        return {"ok": True, "lost": True, "mine_hit": idx, "positions": st["positions"]}
    st["revealed"].append(idx)
    supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]).execute()
    return {"ok": True, "lost": False, "revealed": st["revealed"],
            "mult": mines_mult(st["mines"], len(st["revealed"]))}

@app.post("/api/games/mines/cashout")
async def mines_cashout(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    ar = get_active_round(p["id"])
    if not ar or ar["game_type"] != "mines": raise HTTPException(400, "no active mines round")
    st = ar["state"]; k = len(st["revealed"])
    if k == 0: raise HTTPException(400, "reveal at least one cell")
    bet = float(ar["bet_amount"]); mult = mines_mult(st["mines"], k)
    payout = round(bet * mult, 8); profit = round(payout - bet, 8)
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout}).execute()
    log_round(p["id"], "mines", bet,
              {"revealed": st["revealed"], "mult": mult, "mines": st["mines"], "positions": st["positions"]},
              profit, ar["server_seed"], ar["nonce"])
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit,
        "currency": "USDT", "status": "completed", "meta": {"game": "mines"},
    }).execute()
    clear_active_round(p["id"])
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit, "positions": st["positions"]}

RED = {1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36}
BLACK = {2,4,6,8,10,11,13,15,17,20,22,24,26,28,29,31,33,35}

@app.post("/api/games/roulette/bet")
async def roulette_bet(body: dict, user: dict = Depends(get_current_user)):
    bet = float(body.get("bet", 0)); bt = body.get("type"); bv = body.get("value")
    if not (MIN_BET <= bet <= MAX_BET): raise HTTPException(400, f"bet {MIN_BET}..{MAX_BET}")
    p = get_or_create_profile(user)
    if float(p["balance"]) < bet: raise HTTPException(400, "insufficient balance")
    ss = os.urandom(16).hex(); nonce = p["nonce"] + 1
    n = roulette_number(ss, p["client_seed"], nonce)
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet}).execute()
    supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]).execute()
    win = False; pm = 0.0
    if bt == "red" and n in RED: win, pm = True, 2.0
    elif bt == "black" and n in BLACK: win, pm = True, 2.0
    elif bt == "even" and n != 0 and n % 2 == 0: win, pm = True, 2.0
    elif bt == "odd" and n % 2 == 1: win, pm = True, 2.0
    elif bt in ("dozen1","dozen2","dozen3"):
        d = {"dozen1": range(1,13), "dozen2": range(13,25), "dozen3": range(25,37)}[bt]
        if n in d: win, pm = True, 3.0
    elif bt == "number" and int(bv) == n: win, pm = True, 36.0
    profit = -bet
    if win:
        payout = round(bet * pm, 8); profit = round(payout - bet, 8)
        supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout}).execute()
        supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit,
            "currency": "USDT", "status": "completed", "meta": {"game": "roulette"},
        }).execute()
    log_round(p["id"], "roulette", bet, {"n": n, "bet_type": bt, "win": win}, profit, ss, nonce)
    color = "green" if n == 0 else ("red" if n in RED else "black")
    return {"ok": True, "number": n, "color": color, "win": win,
            "payout": round(bet * pm, 8) if win else 0, "profit": profit}
