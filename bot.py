import os
import json
import hmac
import hashlib
import logging
import asyncio
import time
from urllib.parse import parse_qsl
from contextlib import asynccontextmanager

from fastapi import FastAPI, Header, HTTPException, Depends, Request
from fastapi.middleware.cors import CORSMiddleware
from aiogram import Bot, Dispatcher
from aiogram.types import Message, InlineKeyboardMarkup, InlineKeyboardButton, WebAppInfo
from aiogram.filters import Command
from supabase import create_client, Client
from aiorocket2 import xRocketClient

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("casino")

# ---------- config ----------
BOT_TOKEN = os.environ["BOT_TOKEN"]
WEBAPP_URL = os.environ["WEBAPP_URL"]
SUPABASE_URL = os.environ["SUPABASE_URL"]
SUPABASE_SERVICE_KEY = os.environ["SUPABASE_SERVICE_KEY"]
XROCKET_API_KEY = os.environ["XROCKET_API_KEY"]
XROCKET_WEBHOOK_SECRET = os.environ["XROCKET_WEBHOOK_SECRET"]

# ---------- clients ----------
supabase: Client = create_client(SUPABASE_URL, SUPABASE_SERVICE_KEY)
xrocket = xRocketClient(api_key=XROCKET_API_KEY)


# ---------- initData validation ----------
def validate_init_data(init_data: str, bot_token: str) -> dict | None:
    try:
        parsed = dict(parse_qsl(init_data, keep_blank_values=True))
        received_hash = parsed.pop("hash", None)
        if not received_hash:
            return None

        data_check_string = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
        secret_key = hmac.new(b"WebAppData", bot_token.encode(), hashlib.sha256).digest()
        computed = hmac.new(secret_key, data_check_string.encode(), hashlib.sha256).hexdigest()

        if not hmac.compare_digest(computed, received_hash):
            log.warning("initData hash mismatch")
            return None

        user = json.loads(parsed.get("user", "{}"))
        if not user.get("id"):
            return None
        return user
    except Exception as e:
        log.exception("validate_init_data failed: %s", e)
        return None


async def get_current_user(
    x_telegram_init_data: str = Header(None, alias="X-Telegram-Init-Data"),
) -> dict:
    if not x_telegram_init_data:
        raise HTTPException(status_code=401, detail="missing init data")
    user = validate_init_data(x_telegram_init_data, BOT_TOKEN)
    if not user:
        raise HTTPException(status_code=401, detail="invalid init data")
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


# ---------- aiogram ----------
bot = Bot(token=BOT_TOKEN)
dp = Dispatcher()


@dp.message(Command("start"))
async def cmd_start(message: Message):
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎰 Открыть казино", web_app=WebAppInfo(url=WEBAPP_URL))]
    ])
    await message.answer(
        f"Привет, {message.from_user.first_name}!\nОткрой приложение:",
        reply_markup=kb,
    )


# ---------- fastapi ----------
@asynccontextmanager
async def lifespan(app: FastAPI):
    log.info("starting aiogram polling")
    task = asyncio.create_task(dp.start_polling(bot))
    yield
    log.info("stopping aiogram polling")
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


@app.post("/api/auth")
async def auth(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    return {
        "id": p["id"],
        "telegram_id": p["telegram_id"],
        "username": p.get("username"),
        "first_name": p.get("first_name"),
        "balance": float(p["balance"]),
        "client_seed": p["client_seed"],
    }


@app.get("/api/profile")
async def profile(user: dict = Depends(get_current_user)):
    p = get_or_create_profile(user)
    return {
        "id": p["id"],
        "telegram_id": p["telegram_id"],
        "username": p.get("username"),
        "first_name": p.get("first_name"),
        "balance": float(p["balance"]),
        "client_seed": p["client_seed"],
        "nonce": p["nonce"],
    }


# ---------- deposits ----------
@app.post("/api/payments/deposit")
async def create_deposit(
    body: dict,
    user: dict = Depends(get_current_user),
):
    amount = float(body.get("amount", 0))
    if amount < 1:
        raise HTTPException(400, "minimum deposit is 1 USDT")

    p = get_or_create_profile(user)
    client_invoice_id = f"dep_{p['id'][:8]}_{int(time.time())}"

    invoice = await xrocket.create_invoice(
        amount=amount,
        currency="USDT",
        description="Deposit to casino",
        min_payment=0,
        num_payments=1,
        client_invoice_id=client_invoice_id,
    )

    supabase.table("transactions").insert({
        "user_id": p["id"],
        "type": "deposit",
        "amount": amount,
        "currency": "USDT",
        "external_id": client_invoice_id,
        "status": "pending",
        "meta": {"invoice_id": invoice.get("id")},
    }).execute()

    return {"link": invoice["link"], "invoice_id": invoice.get("id")}


# ---------- withdrawals ----------
@app.post("/api/payments/withdraw")
async def withdraw(
    body: dict,
    user: dict = Depends(get_current_user),
):
    amount = float(body.get("amount", 0))
    if amount < 1:
        raise HTTPException(400, "minimum withdrawal is 1 USDT")

    p = get_or_create_profile(user)
    if float(p["balance"]) < amount:
        raise HTTPException(400, "insufficient balance")

    client_payout_id = f"wd_{p['id'][:8]}_{int(time.time())}"

    try:
        payout = await xrocket.create_payout(
            target=str(user["id"]),
            target_type="telegram_user_id",
            asset="USDT",
            amount=amount,
            description="Withdrawal from casino",
            client_payout_id=client_payout_id,
        )
    except Exception as e:
        log.exception("payout failed: %s", e)
        raise HTTPException(400, f"payout failed: {e}")

    supabase.rpc("change_balance", {
        "p_user_id": p["id"],
        "p_delta": -amount,
    }).execute()

    supabase.table("transactions").insert({
        "user_id": p["id"],
        "type": "withdraw",
        "amount": amount,
        "currency": "USDT",
        "external_id": client_payout_id,
        "status": "completed",
        "meta": {"payout_id": payout.get("payoutId")},
    }).execute()

    return {"ok": True, "payout_id": payout.get("payoutId")}


# ---------- xrocket webhook ----------
@app.post("/api/webhook/xrocket")
async def xrocket_webhook(request: Request):
    raw_body = await request.body()
    signature = request.headers.get("Signature")
    sig_version = request.headers.get("Signature-Version")
    sig_timestamp = request.headers.get("Signature-Timestamp")

    if not all([signature, sig_version, sig_timestamp]):
        raise HTTPException(401, "missing signature headers")
    if sig_version != "v1":
        raise HTTPException(401, "unsupported signature version")

    now_ms = int(time.time() * 1000)
    if abs(now_ms - int(sig_timestamp)) > 300_000:
        raise HTTPException(401, "timestamp too old")

    signed_string = f"{sig_timestamp}.{raw_body.decode()}"
    expected = hmac.new(
        XROCKET_WEBHOOK_SECRET.encode(),
        signed_string.encode(),
        hashlib.sha256,
    ).hexdigest()

    if not hmac.compare_digest(expected, signature):
        raise HTTPException(401, "invalid signature")

    event = json.loads(raw_body)
    log.info("xrocket webhook: %s", event.get("type"))

    if event.get("type") == "invoice" and event.get("status") == "paid":
        client_invoice_id = event.get("clientInvoiceId")
        if client_invoice_id:
            tx = supabase.table("transactions") \
                .select("*") \
                .eq("external_id", client_invoice_id) \
                .eq("status", "pending") \
                .execute()

            if tx.data:
                tx_row = tx.data[0]
                supabase.rpc("change_balance", {
                    "p_user_id": tx_row["user_id"],
                    "p_delta": float(tx_row["amount"]),
                }).execute()

                supabase.table("transactions") \
                    .update({"status": "completed"}) \
                    .eq("id", tx_row["id"]) \
                    .execute()

                log.info("deposit credited: %s", client_invoice_id)

    return {"ok": True}
