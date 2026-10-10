import os, json, hmac, hashlib, logging, asyncio, time
from urllib.parse import parse_qsl
from contextlib import asynccontextmanager
from math import comb

from fastapi import FastAPI, Header, HTTPException, Depends, Request
from fastapi.middleware.cors import CORSMiddleware
from aiogram import Bot, Dispatcher
from aiogram.types import Message, InlineKeyboardMarkup, InlineKeyboardButton, WebAppInfo
from aiogram.filters import Command
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
MIN_BET = float(os.environ.get("MIN_BET", "1"))
MAX_BET = float(os.environ.get("MAX_BET", "1000"))

supabase: Client = create_client(SUPABASE_URL, SUPABASE_SERVICE_KEY)
xrocket: xRocketClient | None = None


# ---------------- PF / math ----------------
def pf_rand(server_seed: str, client_seed: str, nonce: int) -> float:
    msg = f"{client_seed}:{nonce}".encode()
    h = hmac.new(server_seed.encode(), msg, hashlib.sha256).hexdigest()
    return int(h[:13], 16) / float(0xFFFFFFFFFFFFF)

def crash_point(server_seed: str, client_seed: str, nonce: int) -> float:
    r = pf_rand(server_seed, client_seed, nonce)
    if r < HOUSE_EDGE:
        return 1.00
    return round(min(1000.0, (1 - HOUSE_EDGE) / (1 - r)), 2)

def crash_mult(elapsed: float) -> float:
    return round(max(1.0, 1.0 * (1.07 ** elapsed)), 2)

def roulette_number(server_seed: str, client_seed: str, nonce: int) -> int:
    return int(pf_rand(server_seed, client_seed, nonce) * 37)

def mine_positions(server_seed: str, client_seed: str, nonce: int, mines: int) -> list[int]:
    seed = f"{server_seed}:{client_seed}:{nonce}".encode()
    state = int.from_bytes(hashlib.sha256(seed).digest()[:8], "big")
    pos = list(range(25))
    for i in range(24, 0, -1):
        state = (state * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
        j = state % (i + 1)
        pos[i], pos[j] = pos[j], pos[i]
    return pos[:mines]

def mines_mult(mines: int, revealed: int) -> float:
    if revealed <= 0:
        return 1.0
    safe = 25 - mines
    if revealed > safe:
        return 0.0
    p = comb(safe, revealed) / comb(25, revealed)
    return round((1 - HOUSE_EDGE) / p, 4)


# ---------------- auth ----------------
def validate_init_data(init_data: str, bot_token: str) -> dict | None:
    try:
        parsed = dict(parse_qsl(init_data, keep_blank_values=True))
        received_hash = parsed.pop("hash", None)
        if not received_hash:
            return None
        dcs = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
        secret = hmac.new(b"WebAppData", bot_token.encode(), hashlib.sha256).digest()
        computed = hmac.new(secret, dcs.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(computed, received_hash):
            return None
        user = json.loads(parsed.get("user", "{}"))
        return user if user.get("id") else None
    except Exception:
        log.exception("validate_init_data failed")
        return None

async def get_current_user(x_telegram_init_data: str = Header(None, alias="X-Telegram-Init-Data")) -> dict:
    if not x_telegram_init_data:
        raise HTTPException(401, "missing init data")
    user = validate_init_data(x_telegram_init_data, BOT_TOKEN)
    if not user:
        raise HTTPException(401, "invalid init data")
    return user

def get_or_create_profile(tg_user: dict) -> dict:
    tg_id = int(tg_user["id"])
    res = supabase.table("profiles").select("*").eq("telegram_id", tg_id).execute()
    if res.data:
        return res.data[0]
    ins = supabase.table("profiles").insert({
        "telegram_id": tg_id,
        "username": tg_user.get("username"),
        "first_name": tg_user.get("first_name"),
    }).execute()
    return ins.data[0]

def get_active_round(user_id: str) -> dict | None:
    r = supabase.table("active_rounds").select("*").eq("user_id", user_id).execute()
    return r.data[0] if r.data else None

def clear_active_round(user_id: str):
    supabase.table("active_rounds").delete().eq("user_id", user_id).execute()

def log_round(user_id: str, game: str, bet: float, result: dict, profit: float, server_seed: str):
    supabase.table("game_rounds").insert({
        "user_id": user_id,
        "game_type": game,
        "bet_amount": bet,
        "result": result,
        "profit": profit,
        "server_seed": server_seed,
    }).execute()


# ---------------- aiogram ----------------
bot = Bot(token=BOT_TOKEN)
dp = Dispatcher()

@dp.message(Command("start"))
async def cmd_start(message: Message):
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎰 Открыть GoldCash", web_app=WebAppInfo(url=WEBAPP_URL))]
    ])
    await message.answer(
        f"Привет, {message.from_user.first_name}!\nЖми кнопку, чтобы играть:",
        reply_markup=kb,
    )


# ---------------- app ----------------
@asynccontextmanager
async def lifespan(app: FastAPI):
    global xrocket
    xrocket = xRocketClient(api_key=XROCKET_API_KEY)
    log.info("xrocket initialized")
    task = asyncio.create_task(dp.start_polling(bot))
    yield
    task.cancel()
    try:
        await task
    except asyncio.CancelledError:
        pass
    await bot.session.close()

app = FastAPI(lifespan=lifespan)
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)

@app.get("/")
async def root():
    return {"status": "ok"}


# ---------------- profile ----------------
@app.post("/api/auth")
async def auth(user: dict = Depends(get_current_user)):
    return get_or_create_profile(user)

@app.get("/api/profile")
async def profile(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    rounds = supabase.table("game_rounds").select("profit, game_type, bet_amount") \
        .eq("user_id", p["id"]).order("created_at", desc=True).limit(100).execute().data or []
    total_games = len(rounds)
    total_wagered = sum(float(r["bet_amount"]) for r in rounds)
    total_profit = sum(float(r["profit"]) for r in rounds)
    best_mult = max([(float(r["profit"]) + float(r["bet_amount"])) / float(r["bet_amount"])
                     for r in rounds if float(r["bet_amount"]) > 0] or [1.0])
    return {
        "id": p["id"],
        "telegram_id": p["telegram_id"],
        "username": p.get("username"),
        "first_name": p.get("first_name"),
        "balance": float(p["balance"]),
        "client_seed": p["client_seed"],
        "nonce": p["nonce"],
        "stats": {
            "total_games": total_games,
            "total_wagered": round(total_wagered, 2),
            "total_profit": round(total_profit, 2),
            "best_mult": round(best_mult, 2),
        },
    }

@app.get("/api/live")
async def live():
    r = supabase.table("game_rounds") \
        .select("game_type, profit, bet_amount, profiles(username, first_name)") \
        .gt("profit", 0).order("created_at", desc=True).limit(20).execute()
    out = []
    for row in r.data or []:
        prof = row.get("profiles") or {}
        name = prof.get("first_name") or prof.get("username") or "anon"
        out.append({
            "game": row["game_type"],
            "name": name,
            "profit": round(float(row["profit"]), 2),
            "mult": round((float(row["profit"]) + float(row["bet_amount"])) / float(row["bet_amount"]), 2)
                    if float(row["bet_amount"]) else 1.0,
        })
    return out

@app.get("/api/history/games")
async def history_games(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    r = supabase.table("game_rounds").select("*").eq("user_id", p["id"]) \
        .order("created_at", desc=True).limit(30).execute()
    return r.data or []

@app.get("/api/history/transactions")
async def history_tx(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    r = supabase.table("transactions").select("*").eq("user_id", p["id"]) \
        .order("created_at", desc=True).limit(30).execute()
    return r.data or []


# ---------------- deposits / withdrawals ----------------
@app.post("/api/payments/deposit")
async def create_deposit(body: dict, user: dict = Depends(get_current_user)):
    amount = float(body.get("amount", 0))
    if amount < 1:
        raise HTTPException(400, "minimum deposit is 1 USDT")
    p = get_or_create_profile(user)
    cid = f"dep_{p['id'][:8]}_{int(time.time())}"
    try:
        inv = await xrocket.create_invoice(
            amount=amount, currency="USDT", description="GoldCash deposit",
            min_payment=0, num_payments=1, client_invoice_id=cid,
        )
    except Exception as e:
        log.exception("create_invoice failed")
        raise HTTPException(400, f"invoice failed: {e}")
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "deposit", "amount": amount,
        "currency": "USDT", "external_id": cid, "status": "pending",
        "meta": {"invoice_id": inv.get("id")},
    }).execute()
    return {"link": inv["link"], "invoice_id": inv.get("id")}

@app.post("/api/payments/withdraw")
async def withdraw(body: dict, user: dict = Depends(get_current_user)):
    amount = float(body.get("amount", 0))
    if amount < 1:
        raise HTTPException(400, "minimum withdrawal is 1 USDT")
    p = get_or_create_profile(user)
    if float(p["balance"]) < amount:
        raise HTTPException(400, "insufficient balance")
    cid = f"wd_{p['id'][:8]}_{int(time.time())}"
    try:
        payout = await xrocket.create_payout(
            target=str(user["id"]), target_type="telegram_user_id",
            asset="USDT", amount=amount, description="GoldCash withdraw",
            client_payout_id=cid,
        )
    except Exception as e:
        log.exception("payout failed")
        raise HTTPException(400, f"payout failed: {e}")
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": -amount}).execute()
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "withdraw", "amount": amount,
        "currency": "USDT", "external_id": cid, "status": "completed",
        "meta": {"payout_id": payout.get("payoutId")},
    }).execute()
    return {"ok": True, "payout_id": payout.get("payoutId")}

@app.post("/api/webhook/xrocket")
async def xrocket_webhook(request: Request):
    raw = await request.body()
    sig = request.headers.get("Signature")
    ver = request.headers.get("Signature-Version")
    ts = request.headers.get("Signature-Timestamp")
    if not all([sig, ver, ts]):
        raise HTTPException(401, "missing signature headers")
    if ver != "v1":
        raise HTTPException(401, "unsupported version")
    if abs(int(time.time() * 1000) - int(ts)) > 300_000:
        raise HTTPException(401, "timestamp too old")
    expected = hmac.new(XROCKET_WEBHOOK_SECRET.encode(),
                        f"{ts}.{raw.decode()}".encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, sig):
        raise HTTPException(401, "invalid signature")
    event = json.loads(raw)
    if event.get("type") == "invoice" and event.get("status") == "paid":
        cid = event.get("clientInvoiceId")
        if cid:
            tx = supabase.table("transactions").select("*").eq("external_id", cid) \
                .eq("status", "pending").execute()
            if tx.data:
                row = tx.data[0]
                supabase.rpc("change_balance",
                             {"p_user_id": row["user_id"], "p_delta": float(row["amount"])}).execute()
                supabase.table("transactions").update({"status": "completed"}).eq("id", row["id"]).execute()
                log.info("deposit credited: %s", cid)
    return {"ok": True}


# ============================================================
# CRASH
# ============================================================
@app.post("/api/games/crash/start")
async def crash_start(body: dict, user: dict = Depends(get_current_user)):
    bet = float(body.get("bet", 0))
    if not (MIN_BET <= bet <= MAX_BET):
        raise HTTPException(400, f"bet must be {MIN_BET}..{MAX_BET}")
    p = get_or_create_profile(user)
    if float(p["balance"]) < bet:
        raise HTTPException(400, "insufficient balance")
    if get_active_round(p["id"]):
        raise HTTPException(400, "active round exists")

    server_seed = os.urandom(16).hex()
    nonce = p["nonce"] + 1
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet}).execute()
    supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]).execute()
    supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "crash", "bet_amount": bet,
        "state": {"started_at": time.time()},
        "server_seed": server_seed, "nonce": nonce,
    }).execute()
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet,
        "currency": "USDT", "status": "completed", "meta": {"game": "crash"},
    }).execute()
    return {"ok": True, "started_at": time.time()}

@app.post("/api/games/crash/cashout")
async def crash_cashout(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    ar = get_active_round(p["id"])
    if not ar or ar["game_type"] != "crash":
        raise HTTPException(400, "no active crash round")
    started = float(ar["state"]["started_at"])
    elapsed = time.time() - started
    current_mult = crash_mult(elapsed)
    cp = crash_point(ar["server_seed"], p["client_seed"], ar["nonce"])
    bet = float(ar["bet_amount"])

    if current_mult >= cp:
        # краш
        log_round(p["id"], "crash", bet,
                  {"crashed_at": cp, "elapsed": round(elapsed, 2)}, -bet, ar["server_seed"])
        clear_active_round(p["id"])
        return {"ok": True, "lost": True, "crash_point": cp}

    payout = round(bet * current_mult, 8)
    profit = round(payout - bet, 8)
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout}).execute()
    log_round(p["id"], "crash", bet,
              {"mult": current_mult, "elapsed": round(elapsed, 2)}, profit, ar["server_seed"])
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit,
        "currency": "USDT", "status": "completed", "meta": {"game": "crash"},
    }).execute()
    clear_active_round(p["id"])
    return {"ok": True, "lost": False, "mult": current_mult,
            "payout": payout, "profit": profit, "server_seed": ar["server_seed"]}


# ============================================================
# MINES
# ============================================================
@app.post("/api/games/mines/start")
async def mines_start(body: dict, user: dict = Depends(get_current_user)):
    bet = float(body.get("bet", 0))
    mines = int(body.get("mines", 3))
    if not (MIN_BET <= bet <= MAX_BET):
        raise HTTPException(400, f"bet must be {MIN_BET}..{MAX_BET}")
    if not (1 <= mines <= 24):
        raise HTTPException(400, "mines must be 1..24")
    p = get_or_create_profile(user)
    if float(p["balance"]) < bet:
        raise HTTPException(400, "insufficient balance")
    if get_active_round(p["id"]):
        raise HTTPException(400, "active round exists")

    server_seed = os.urandom(16).hex()
    nonce = p["nonce"] + 1
    positions = mine_positions(server_seed, p["client_seed"], nonce, mines)
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet}).execute()
    supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]).execute()
    supabase.table("active_rounds").insert({
        "user_id": p["id"], "game_type": "mines", "bet_amount": bet,
        "state": {"mines": mines, "positions": positions, "revealed": []},
        "server_seed": server_seed, "nonce": nonce,
    }).execute()
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "bet", "amount": bet,
        "currency": "USDT", "status": "completed", "meta": {"game": "mines"},
    }).execute()
    return {"ok": True, "mines": mines, "mult": mines_mult(mines, 0)}

@app.post("/api/games/mines/reveal")
async def mines_reveal(body: dict, user: dict = Depends(get_current_user)):
    idx = int(body.get("cell", -1))
    if not (0 <= idx < 25):
        raise HTTPException(400, "bad cell")
    p = get_or_create_profile(user)
    ar = get_active_round(p["id"])
    if not ar or ar["game_type"] != "mines":
        raise HTTPException(400, "no active mines round")
    st = ar["state"]
    if idx in st["revealed"]:
        raise HTTPException(400, "already revealed")
    mines = st["mines"]
    positions = set(st["positions"])
    bet = float(ar["bet_amount"])

    if idx in positions:
        # проигрыш
        log_round(p["id"], "mines", bet,
                  {"mine_hit": idx, "revealed": st["revealed"]}, -bet, ar["server_seed"])
        clear_active_round(p["id"])
        return {"ok": True, "lost": True, "mine_hit": idx, "positions": st["positions"]}

    st["revealed"].append(idx)
    new_mult = mines_mult(mines, len(st["revealed"]))
    supabase.table("active_rounds").update({"state": st}).eq("user_id", p["id"]).execute()
    return {"ok": True, "lost": False, "revealed": st["revealed"],
            "mult": new_mult, "next_mult": mines_mult(mines, len(st["revealed"]) + 1)}

@app.post("/api/games/mines/cashout")
async def mines_cashout(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    ar = get_active_round(p["id"])
    if not ar or ar["game_type"] != "mines":
        raise HTTPException(400, "no active mines round")
    st = ar["state"]
    k = len(st["revealed"])
    if k == 0:
        raise HTTPException(400, "reveal at least one cell")
    bet = float(ar["bet_amount"])
    mult = mines_mult(st["mines"], k)
    payout = round(bet * mult, 8)
    profit = round(payout - bet, 8)
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout}).execute()
    log_round(p["id"], "mines", bet,
              {"revealed": st["revealed"], "mult": mult}, profit, ar["server_seed"])
    supabase.table("transactions").insert({
        "user_id": p["id"], "type": "win", "amount": profit,
        "currency": "USDT", "status": "completed", "meta": {"game": "mines"},
    }).execute()
    clear_active_round(p["id"])
    return {"ok": True, "mult": mult, "payout": payout, "profit": profit,
            "positions": st["positions"]}


# ============================================================
# ROULETTE
# ============================================================
RED = {1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36}
BLACK = {2,4,6,8,10,11,13,15,17,20,22,24,26,28,29,31,33,35}

@app.post("/api/games/roulette/bet")
async def roulette_bet(body: dict, user: dict = Depends(get_current_user)):
    bet = float(body.get("bet", 0))
    bet_type = body.get("type")  # red|black|even|odd|dozen1|dozen2|dozen3|number
    bet_value = body.get("value")
    if not (MIN_BET <= bet <= MAX_BET):
        raise HTTPException(400, f"bet must be {MIN_BET}..{MAX_BET}")
    p = get_or_create_profile(user)
    if float(p["balance"]) < bet:
        raise HTTPException(400, "insufficient balance")
    if get_active_round(p["id"]):
        raise HTTPException(400, "active round exists")

    server_seed = os.urandom(16).hex()
    nonce = p["nonce"] + 1
    n = roulette_number(server_seed, p["client_seed"], nonce)
    supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": -bet}).execute()
    supabase.table("profiles").update({"nonce": nonce}).eq("id", p["id"]).execute()

    win = False
    payout_mult = 0.0
    if bet_type == "red" and n in RED:
        win, payout_mult = True, 2.0
    elif bet_type == "black" and n in BLACK:
        win, payout_mult = True, 2.0
    elif bet_type == "even" and n != 0 and n % 2 == 0:
        win, payout_mult = True, 2.0
    elif bet_type == "odd" and n % 2 == 1:
        win, payout_mult = True, 2.0
    elif bet_type in ("dozen1", "dozen2", "dozen3"):
        d = {"dozen1": range(1, 13), "dozen2": range(13, 25), "dozen3": range(25, 37)}[bet_type]
        if n in d:
            win, payout_mult = True, 3.0
    elif bet_type == "number" and int(bet_value) == n:
        win, payout_mult = True, 36.0

    if win:
        payout = round(bet * payout_mult, 8)
        profit = round(payout - bet, 8)
        supabase.rpc("change_balance", {"p_user_id": p["id"], "p_delta": payout}).execute()
        supabase.table("transactions").insert({
            "user_id": p["id"], "type": "win", "amount": profit,
            "currency": "USDT", "status": "completed", "meta": {"game": "roulette"},
        }).execute()
    else:
        profit = -bet

    log_round(p["id"], "roulette", bet,
              {"n": n, "bet_type": bet_type, "win": win}, profit, server_seed)
    color = "green" if n == 0 else ("red" if n in RED else "black")
    return {"ok": True, "number": n, "color": color, "win": win,
            "payout": round(bet * payout_mult, 8) if win else 0,
            "profit": profit, "server_seed": server_seed}
