import os
import json
import hmac
import hashlib
import logging
import asyncio
from urllib.parse import parse_qsl
from contextlib import asynccontextmanager

from fastapi import FastAPI, Header, HTTPException, Depends
from fastapi.middleware.cors import CORSMiddleware
from aiogram import Bot, Dispatcher
from aiogram.types import Message, InlineKeyboardMarkup, InlineKeyboardButton, WebAppInfo
from aiogram.filters import Command
from supabase import create_client, Client

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("casino")

# ---------- config ----------
BOT_TOKEN = os.environ["BOT_TOKEN"]
WEBAPP_URL = os.environ["WEBAPP_URL"]
SUPABASE_URL = os.environ["SUPABASE_URL"]
SUPABASE_SERVICE_KEY = os.environ["SUPABASE_SERVICE_KEY"]

# ---------- supabase ----------
supabase: Client = create_client(SUPABASE_URL, SUPABASE_SERVICE_KEY)


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
