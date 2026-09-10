import asyncio
import hashlib
import hmac
import json
import logging
import os
import re
import tempfile
import time
from pathlib import Path
from typing import Any, Optional
from urllib.parse import parse_qsl, quote

from dotenv import load_dotenv
from telethon import TelegramClient
from telethon.errors import (
    AuthKeyUnregisteredError,
    FloodWaitError,
    SessionPasswordNeededError,
    PhoneNumberInvalidError,
    PhoneNumberBannedError,
    PhoneCodeInvalidError,
    PhoneCodeExpiredError,
    PasswordHashInvalidError,
    SendCodeUnavailableError,
)
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputFile, Update, WebAppInfo
from telegram.error import BadRequest, RetryAfter
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes, MessageHandler, TypeHandler, filters

load_dotenv()


def _required_env(name: str) -> str:
    value = os.getenv(name, "").strip()
    if not value:
        raise RuntimeError(
            f"متغير البيئة {name} مفقود أو فارغ. أضفه في إعدادات الاستضافة أو ملف .env ثم أعد تشغيل التطبيق."
        )
    return value


def _required_int_env(name: str) -> int:
    raw = _required_env(name)
    try:
        value = int(raw)
    except ValueError as exc:
        raise RuntimeError(
            f"متغير البيئة {name} يجب أن يكون رقماً صحيحاً فقط، لكن القيمة الحالية غير صالحة."
        ) from exc
    if value <= 0:
        raise RuntimeError(f"متغير البيئة {name} يجب أن يكون أكبر من صفر.")
    return value


logging.basicConfig(
    format="%(asctime)s [%(name)s] %(levelname)s: %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger("telegram_archiver")

API_ID = _required_int_env("TELEGRAM_API_ID")
API_HASH = _required_env("TELEGRAM_API_HASH")
BOT_TOKEN = _required_env("BOT_TOKEN")
OWNER_ID = _required_int_env("OWNER_ID")
SECOND_RECIPIENT = os.getenv("SECOND_RECIPIENT", "").strip()
DELETE_AFTER_SECONDS = int(os.getenv("DELETE_AFTER_SECONDS", "30"))
DELETE_SENT_MESSAGES = os.getenv("DELETE_SENT_MESSAGES", "true").lower() == "true"
MAX_FILE_SIZE_MB = int(os.getenv("MAX_FILE_SIZE_MB", "1024"))
MAX_FILE_SIZE_BYTES = MAX_FILE_SIZE_MB * 1024 * 1024
DAILY_QUOTA = 5
REFERRAL_BONUS = 5
TRANSFER_REFERRAL_REQUIREMENT = 5
DOWNLOAD_TIMEOUT_SECONDS = int(os.getenv("DOWNLOAD_TIMEOUT_SECONDS", "1800"))
# مهلة نقل ملفات القنوات، بالثواني؛ الافتراضي ساعتان للملفات الكبيرة.
TRANSFER_MEDIA_TIMEOUT_SECONDS = int(os.getenv("TRANSFER_MEDIA_TIMEOUT_SECONDS", "7200"))

# حدود التزامن: تمنع انهيار الأداء عندما يصل عدد المستخدمين/المهام إلى عشرات أو مئات.
# يمكن تعديلها من متغيرات البيئة حسب موارد الخادم.
MEDIA_CONCURRENCY = max(1, int(os.getenv("MEDIA_CONCURRENCY", "8")))
TRANSFER_CONCURRENCY = max(1, int(os.getenv("TRANSFER_CONCURRENCY", "3")))

SESSION_DIR = Path(os.getenv("SESSION_DIR", "sessions"))
SESSION_DIR.mkdir(parents=True, exist_ok=True)
TRANSFER_STATE_PATH = SESSION_DIR / "channel_transfers.json"
ADMIN_STATE_PATH = SESSION_DIR / "admin_state.json"

admins: set[int] = {OWNER_ID}
user_registry: dict[str, dict[str, Any]] = {}


LANGUAGE_LABELS = {"ar": "العربية", "en": "English"}


def user_language(user_id: int) -> str:
    language = str(user_registry.get(str(user_id), {}).get("language", "ar")).lower()
    return language if language in {"ar", "en"} else "ar"


def localized(user_id: int, arabic: str, english: str) -> str:
    return english if user_language(user_id) == "en" else arabic


def set_user_language(user_id: int, language: str) -> None:
    entry = user_registry.setdefault(str(user_id), {"id": int(user_id)})
    entry["language"] = language if language in {"ar", "en"} else "ar"
    save_admin_state()


def load_admin_state() -> None:
    global admins, user_registry
    if not ADMIN_STATE_PATH.exists():
        return
    try:
        data = json.loads(ADMIN_STATE_PATH.read_text(encoding="utf-8"))
        admins = {OWNER_ID, *(int(value) for value in data.get("admins", []))}
        user_registry = {str(key): value for key, value in data.get("users", {}).items()}
    except Exception:
        logger.exception("تعذر تحميل حالة المشرفين والمستخدمين")


def save_admin_state() -> None:
    temp_path = ADMIN_STATE_PATH.with_suffix(".tmp")
    temp_path.write_text(
        json.dumps({"admins": sorted(admins), "users": user_registry}, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    temp_path.replace(ADMIN_STATE_PATH)


def today_key() -> str:
    return time.strftime("%Y-%m-%d", time.gmtime())


def referral_id_from_args(args: list[str] | None) -> int | None:
    if not args:
        return None
    raw = str(args[0]).strip()
    if raw.startswith("ref_"):
        raw = raw[4:]
    try:
        value = int(raw)
    except ValueError:
        return None
    return value if value > 0 else None


def register_user(user, referral_id: int | None = None) -> None:
    if not user:
        return
    user_id = str(user.id)
    is_new = user_id not in user_registry
    entry = user_registry.setdefault(user_id, {})
    entry.setdefault("daily_date", today_key())
    entry.setdefault("daily_used", 0)
    entry.setdefault("bonus_credits", 0)
    entry.setdefault("referral_count", 0)
    entry.setdefault("referred_by", None)
    # صلاحية مستقلة يمكن للمالك منحها دون تحويل المستخدم إلى مشرف.
    entry.setdefault("channel_transfer_access", False)
    entry.setdefault("language", "ar")
    entry.update({
        "id": int(user.id),
        "name": getattr(user, "full_name", "") or "",
        "username": getattr(user, "username", "") or "",
        "last_seen": int(time.time()),
    })
    if is_new and referral_id and referral_id != int(user.id) and str(referral_id) in user_registry:
        referrer = user_registry[str(referral_id)]
        entry["referred_by"] = int(referral_id)
        referrer["referral_count"] = int(referrer.get("referral_count", 0)) + 1
        referrer["bonus_credits"] = int(referrer.get("bonus_credits", 0)) + REFERRAL_BONUS
    save_admin_state()


def quota_snapshot(user_id: int) -> dict[str, int]:
    entry = user_registry.setdefault(str(user_id), {"id": int(user_id)})
    if entry.get("daily_date") != today_key():
        entry["daily_date"] = today_key()
        entry["daily_used"] = 0
        save_admin_state()
    used = int(entry.get("daily_used", 0))
    bonus = int(entry.get("bonus_credits", 0))
    return {
        "daily_remaining": max(0, DAILY_QUOTA - used),
        "bonus_credits": max(0, bonus),
        "total_remaining": max(0, DAILY_QUOTA - used) + max(0, bonus),
        "referral_count": int(entry.get("referral_count", 0)),
    }


def consume_quota(user_id: int) -> bool:
    entry = user_registry.setdefault(str(user_id), {"id": int(user_id)})
    quota_snapshot(user_id)
    if int(entry.get("daily_used", 0)) < DAILY_QUOTA:
        entry["daily_used"] = int(entry.get("daily_used", 0)) + 1
    elif int(entry.get("bonus_credits", 0)) > 0:
        entry["bonus_credits"] = int(entry.get("bonus_credits", 0)) - 1
    else:
        return False
    save_admin_state()
    return True


def admin_only(update: Update) -> bool:
    return bool(update.effective_user and update.effective_user.id in admins)


load_admin_state()

LINK_PATTERN = re.compile(
    r"https?://t\.me/(?:(?P<private>c)/(?P<private_id>\d+)/|(?P<username>[A-Za-z0-9_]+)/)(?P<message_id>\d+)"
)

# حالة كل مستخدم داخل الذاكرة: الهاتف، رمز الجلسة، والعميل الخاص به.
clients: dict[int, TelegramClient] = {}
public_client: TelegramClient | None = None
public_client_lock = asyncio.Lock()
states: dict[int, dict[str, Any]] = {}

# =========================
# Telegram Mini App Web UI
# =========================
FASTAPI_WEB_ENABLED = True
WEB_HOST = "0.0.0.0"
# JustRunMy يحدد المنفذ عبر PORT؛ نستخدم 8080 كقيمة احتياطية.
WEB_PORT = int(os.getenv("PORT", "8080"))
# الرابط العام الذي يفتحه زر Telegram Mini App. يمكن تغييره من البيئة.
WEB_PUBLIC_BASE_URL = os.getenv("WEB_PUBLIC_BASE_URL", "https://telegrampanel.xs1.onjrnm.link").rstrip("/")

# Telegram يوصي برفض initData القديمة. نسمح بحد أقصى 24 ساعة.
TELEGRAM_WEBAPP_INIT_DATA_MAX_AGE = 86400

# Web dependencies must be installed by the hosting platform from requirements.txt.
# Never run pip during application startup: it can consume the container memory and
# cause the process to be killed before the bot starts.
try:
    from fastapi import FastAPI, HTTPException, Query
    from fastapi.responses import HTMLResponse, StreamingResponse, JSONResponse
    from pydantic import BaseModel
    import uvicorn
except ImportError:
    logger.exception(
        "FastAPI/Uvicorn غير مثبتين. ثبتهما أثناء Build من requirements.txt "
        "ثم أعد تشغيل التطبيق. لن يتم تثبيتهما أثناء التشغيل."
    )
    FastAPI = None

WEB_HTML = r"""<!doctype html>
<html lang="ar" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>Telegram Mini App</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
*{box-sizing:border-box}body{margin:0;font-family:system-ui,-apple-system,Segoe UI,sans-serif;background:#10151d;color:#e8edf4}
.app{display:flex;height:100vh}.side{width:330px;border-left:1px solid #29313d;background:#151b24;display:flex;flex-direction:column}
.main{flex:1;display:flex;flex-direction:column;min-width:0}.top{height:62px;border-bottom:1px solid #29313d;display:flex;align-items:center;padding:0 18px;gap:10px}
h2,h3{margin:0}.search{margin:12px}.search input,.composer input{width:100%;background:#0d1219;border:1px solid #303b49;color:#fff;border-radius:10px;padding:11px}
.sessions,.dialogs{overflow:auto;flex:1}.item{padding:12px 14px;border-bottom:1px solid #242c37;cursor:pointer}.item:hover,.item.active{background:#202a37}
.badge{font-size:11px;padding:3px 7px;border-radius:8px;background:#26374b}.green{color:#65e59b}.muted{color:#8e9aaa;font-size:12px}
.messages{flex:1;overflow:auto;padding:18px;display:flex;flex-direction:column;gap:10px}
.msg{max-width:min(720px,85%);background:#1c2632;border-radius:13px;padding:10px 12px;align-self:flex-start}.msg.out{align-self:flex-end;background:#24435a}.meta{font-size:11px;color:#8fa0b3;margin-top:5px}
.media{margin-top:8px}.media img,.media video{max-width:100%;border-radius:10px;max-height:430px}.file{display:inline-block;padding:9px;background:#111820;border-radius:9px;color:#fff;text-decoration:none}
.composer{display:flex;gap:8px;padding:12px;border-top:1px solid #29313d}.composer input{flex:1}.btn{border:0;background:#2b83f6;color:white;border-radius:9px;padding:10px 15px;cursor:pointer}.btn.alt{background:#283341}
.empty{padding:30px;text-align:center;color:#8996a6}.row{display:flex;gap:8px;align-items:center}.title{font-weight:700}.small{font-size:13px}
.auth-error{padding:28px;text-align:center}.auth-error h3{margin-bottom:10px}
@media(max-width:800px){.side{width:260px}.main{min-width:0}.msg{max-width:92%}}
@media(max-width:600px){.app{display:block}.side{width:100%;height:38vh}.main{height:62vh}.top{height:54px}}
</style>
</head>
<body>
<div class="app">
  <aside class="side">
    <div class="top"><h3>📱 حساب Telegram</h3></div>
    <div class="search"><input id="sessionSearch" placeholder="بحث في الجلسة..." oninput="filterSessions()"></div>
    <div id="sessions" class="sessions"><div class="empty">جاري التحقق من Telegram...</div></div>
  </aside>
  <main class="main">
    <div class="top">
      <div style="flex:1"><div id="chatTitle" class="title">اختر محادثة</div><div id="chatSub" class="muted"></div></div>
      <button class="btn alt" onclick="loadDialogs()">🔄 تحديث</button>
    </div>
    <div class="search"><input id="chatSearch" placeholder="🔎 بحث داخل المحادثات أو الرسائل..." onkeydown="if(event.key==='Enter') searchMessages()"></div>
    <div id="dialogs" class="dialogs"></div>
    <div id="messages" class="messages"><div class="empty">اختر محادثة لعرض الرسائل والصور والفيديو والملفات.</div></div>
    <div class="composer">
      <input id="message" placeholder="اكتب رسالة..." onkeydown="if(event.key==='Enter') sendMessage()">
      <button class="btn" onclick="sendMessage()">إرسال</button>
    </div>
  </main>
</div>
<script>
const tg = window.Telegram && window.Telegram.WebApp ? window.Telegram.WebApp : null;
const initData = tg ? (tg.initData || "") : "";
let sessions=[], currentSession=null, currentChat=null, sessionFilter='';
const $=id=>document.getElementById(id);

if(tg){
  tg.ready();
  tg.expand();
  if(tg.setHeaderColor) tg.setHeaderColor('#10151d');
  if(tg.setBackgroundColor) tg.setBackgroundColor('#10151d');
}

function authUrl(path){
  const join = path.includes('?') ? '&' : '?';
  return path + join + 'init_data=' + encodeURIComponent(initData);
}

async function api(path, opts={}) {
  if(!initData) throw new Error('يجب فتح هذه الصفحة من داخل Telegram Mini App.');
  const url = authUrl(path);
  const r=await fetch(url,opts);
  if(!r.ok) throw new Error(await r.text());
  return r.json();
}

async function init(){
  if(!tg || !initData){
    $('sessions').innerHTML='<div class="auth-error"><h3>⚠️ يجب فتح Mini App من Telegram</h3><div class="muted">افتح الواجهة من زر Telegram Mini App داخل البوت.</div></div>';
    return;
  }
  try{
    sessions=await api('/api/sessions');
    renderSessions();
    if(sessions.length){
      currentSession=sessions[0].id;
      renderSessions();
      try{ await loadDialogs(); }
      catch(e){ $('dialogs').innerHTML='<div class="auth-error"><div class="muted">تعذر تحميل محادثات هذه الجلسة: '+esc(e.message)+'</div></div>'; }
    } else {
      $('dialogs').innerHTML='<div class="empty">لا توجد جلسات Telegram مسجلة وصالحة.</div>';
    }
  }catch(e){
    $('sessions').innerHTML='<div class="auth-error"><h3>⚠️ تعذر المصادقة</h3><div class="muted">'+esc(e.message)+'</div></div>';
    $('dialogs').innerHTML=''; $('messages').innerHTML='';
  }
}
function renderSessions(){
  $('sessions').innerHTML='';
  sessions.filter(s=>(s.name+' '+s.username).toLowerCase().includes(sessionFilter.toLowerCase())).forEach(s=>{
    const d=document.createElement('div'); d.className='item '+(s.id===currentSession?'active':'');
    d.innerHTML=`<div class="row"><b>${esc(s.name||'حساب')}</b><span class="badge">${s.connected?'🟢 متصل':'🔴 غير متصل'}</span></div><div class="muted">@${esc(s.username||'')} · ${s.id}</div>`;
    d.onclick=()=>selectSession(s.id,d); $('sessions').appendChild(d);
  });
}
function filterSessions(){sessionFilter=$('sessionSearch').value;renderSessions()}
async function selectSession(id,el){
  currentSession=id;
  currentChat=null; document.querySelectorAll('.item').forEach(x=>x.classList.remove('active'));el.classList.add('active');
  $('chatTitle').textContent='محادثات الحساب'; $('chatSub').textContent='الجلسة #'+id; $('messages').innerHTML='<div class="empty">اختر محادثة.</div>';
  try{ await loadDialogs(); }
  catch(e){ $('dialogs').innerHTML='<div class="auth-error"><div class="muted">تعذر تحميل محادثات هذه الجلسة: '+esc(e.message)+'</div></div>'; }
}
async function loadDialogs(){
 if(!currentSession)return;
 const q=$('chatSearch').value||'';
 const ds=await api('/api/sessions/'+currentSession+'/dialogs?search='+encodeURIComponent(q));
 $('dialogs').innerHTML='';
 ds.forEach(d=>{
   const x=document.createElement('div');x.className='item';
   x.innerHTML=`<div class="title">💬 ${esc(d.title)}</div><div class="muted">${esc(d.type)} · ${d.unread||0} غير مقروء</div>`;
   x.onclick=()=>openChat(d.id,d.title);$('dialogs').appendChild(x);
 });
}
async function openChat(id,title){
 currentChat=id;$('chatTitle').textContent=title;$('chatSub').textContent='تحميل الرسائل...';
 const ms=await api(`/api/sessions/${currentSession}/chats/${id}/messages?limit=60`); renderMessages(ms);
 $('chatSub').textContent=ms.length+' رسالة معروضة';
}
async function searchMessages(){
 if(!currentSession)return;
 if(currentChat){ const q=$('chatSearch').value||''; const ms=await api(`/api/sessions/${currentSession}/chats/${currentChat}/search?q=`+encodeURIComponent(q));renderMessages(ms); }
 else await loadDialogs();
}
function renderMessages(ms){
 $('messages').innerHTML='';
 ms.slice().reverse().forEach(m=>{
   const x=document.createElement('div');x.className='msg '+(m.out?'out':'');
   let media='';
   if(m.media){
     const u=authUrl(m.media.url);
     if(m.media.kind==='image') media=`<div class="media"><img src="${esc(u)}" loading="lazy"></div>`;
     else if(m.media.kind==='video') media=`<div class="media"><video src="${esc(u)}" controls preload="metadata"></video></div>`;
     else media=`<div class="media"><a class="file" href="${esc(u)}" target="_blank" rel="noopener">📎 ${esc(m.media.name||'ملف')}</a></div>`;
   }
   x.innerHTML=`<div>${esc(m.text||'')}</div>${media}<div class="meta">${esc(m.date||'')} ${m.sender? '· '+esc(m.sender):''}</div>`;
   $('messages').appendChild(x);
 });
 $('messages').scrollTop=$('messages').scrollHeight;
}
async function sendMessage(){
 if(!currentSession||!currentChat)return;
 const inp=$('message'), text=inp.value.trim();if(!text)return;
 await api(`/api/sessions/${currentSession}/chats/${currentChat}/send`,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({text})});
 inp.value='';await openChat(currentChat,$('chatTitle').textContent);
}
function esc(s){return String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
init();
</script>
</body></html>"""

if FastAPI:
    web_app = FastAPI(title="Telegram Mini App")

    class SendBody(BaseModel):
        text: str

    async def _authorized_user(init_data: str = Query("")) -> int:
        """تحقق رسمي من Telegram WebApp initData وتعيد Telegram user_id."""
        if not init_data or not init_data.strip():
            raise HTTPException(401, "initData مطلوب. افتح الواجهة من داخل Telegram Mini App.")

        try:
            pairs = dict(parse_qsl(init_data, keep_blank_values=True, strict_parsing=True))
        except ValueError as exc:
            raise HTTPException(401, "initData غير صالح") from exc

        received_hash = pairs.pop("hash", "")
        if not received_hash:
            raise HTTPException(401, "hash غير موجود في initData")

        try:
            auth_date = int(pairs.get("auth_date", "0"))
        except (TypeError, ValueError) as exc:
            raise HTTPException(401, "auth_date غير صالح") from exc

        now = int(time.time())
        if auth_date <= 0 or auth_date > now + 60:
            raise HTTPException(401, "auth_date غير صالح")
        if now - auth_date > TELEGRAM_WEBAPP_INIT_DATA_MAX_AGE:
            raise HTTPException(401, "انتهت صلاحية initData، أعد فتح Mini App من Telegram")

        data_check_string = "\n".join(
            f"{key}={value}" for key, value in sorted(pairs.items())
        )
        secret_key = hmac.new(
            key=b"WebAppData",
            msg=BOT_TOKEN.encode("utf-8"),
            digestmod=hashlib.sha256,
        ).digest()
        calculated_hash = hmac.new(
            key=secret_key,
            msg=data_check_string.encode("utf-8"),
            digestmod=hashlib.sha256,
        ).hexdigest()

        if not hmac.compare_digest(calculated_hash, received_hash):
            raise HTTPException(403, "فشل التحقق من هوية Telegram Mini App")

        user_raw = pairs.get("user", "")
        if not user_raw:
            raise HTTPException(401, "بيانات مستخدم Telegram غير موجودة")
        try:
            user_obj = json.loads(user_raw)
            user_id = int(user_obj["id"])
        except (json.JSONDecodeError, KeyError, TypeError, ValueError) as exc:
            raise HTTPException(401, "بيانات مستخدم Telegram غير صالحة") from exc

        if user_id <= 0:
            raise HTTPException(401, "معرّف مستخدم Telegram غير صالح")
        # Mini App مخصصة للمالك فقط. أي مستخدم آخر يُرفض قبل الوصول إلى أي جلسة أو API.
        if user_id != OWNER_ID:
            raise HTTPException(403, "هذه الميني آب مخصصة للمالك فقط")
        return user_id

    def _available_session_ids() -> list[int]:
        """Return every locally stored session id without exposing other users."""
        ids: set[int] = set(clients)
        for path in SESSION_DIR.glob("user_*.session"):
            try:
                ids.add(int(path.stem.removeprefix("user_")))
            except ValueError:
                continue
        return sorted(value for value in ids if value > 0)

    async def _web_client(sid: int, init_data: str = Query("")):
        """Authenticate the owner, then open any locally stored Telegram session."""
        await _authorized_user(init_data)
        if sid not in _available_session_ids():
            raise HTTPException(404, "جلسة Telegram غير موجودة")

        try:
            c = await get_or_create_client(sid)
            if not c.is_connected():
                await c.connect()
            if not await c.is_user_authorized():
                raise HTTPException(403, "جلسة Telegram الخاصة بك غير مسجل الدخول فيها")
            me = await c.get_me()
        except HTTPException:
            raise
        except AuthKeyUnregisteredError as exc:
            raise HTTPException(403, "جلسة Telegram غير صالحة، أعد تسجيل الدخول من البوت") from exc
        except Exception as e:
            raise HTTPException(503, f"تعذر الاتصال بجلسة Telegram: {e}") from e
        return c

    @web_app.get("/", response_class=HTMLResponse)
    async def web_index():
        return HTMLResponse(WEB_HTML)

    @web_app.get("/healthz")
    async def web_healthz():
        return {"ok": True, "web": True, "mini_app": True, "host": WEB_HOST, "port": WEB_PORT,
                "sessions": len(clients)}

    @web_app.get("/api/sessions")
    async def web_sessions(init_data: str = Query("")):
        await _authorized_user(init_data)
        result = []
        for sid in _available_session_ids():
            try:
                c = await _web_client(sid, init_data)
                me = await c.get_me()
                name = f"{getattr(me,'first_name','') or ''} {getattr(me,'last_name','') or ''}".strip()
                result.append({"id": sid, "name": name or "حساب", "username": getattr(me,'username','') or "",
                               "account_id": int(getattr(me, 'id', 0) or 0), "connected": c.is_connected()})
            except Exception as e:
                logger.warning("تعذر فتح جلسة Mini App %s: %s", sid, e)
                # تجاهل الجلسة غير المسجلة أو التالفة حتى لا تختارها الواجهة
                # تلقائياً ثم تستبدل قائمة الجلسات برسالة مصادقة خاطئة.
                continue
        return result

    @web_app.get("/api/sessions/{sid}/dialogs")
    async def web_dialogs(sid:int, search:str="", init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        out=[]
        # لا نضع حداً منخفضاً؛ الواجهة يجب أن تعرض كل حوارات الجلسة.
        async for d in c.iter_dialogs(limit=None):
            title=d.name or str(d.id)
            if search and search.lower() not in title.lower(): continue
            ent=d.entity
            typ="مجموعة" if getattr(ent,"megagroup",False) else ("قناة" if getattr(ent,"broadcast",False) else "محادثة")
            out.append({"id":d.id,"title":title,"type":typ,"unread":d.unread_count})
        return out

    async def _message_json(c, chat_id, m):
        media=None
        if m.media:
            name=getattr(m.file,"name",None) or "ملف"
            mime=getattr(m.file,"mime_type",None) or ""
            kind="image" if mime.startswith("image/") else ("video" if mime.startswith("video/") else "file")
            media={"kind":kind,"name":name,"url":f"/api/sessions/{getattr(c,'_web_sid',0)}/media/{chat_id}/{m.id}"}
        return {"id":m.id,"text":m.text or "","out":bool(m.out),"date":m.date.isoformat() if m.date else "",
                "sender":getattr(getattr(m,"sender",None),"first_name",None),"media":media}

    @web_app.get("/api/sessions/{sid}/chats/{chat_id}/messages")
    async def web_messages(sid:int, chat_id:int, limit:int=60, init_data:str=Query("")):
        c=await _web_client(sid, init_data); c._web_sid=sid
        msgs=[m async for m in c.iter_messages(chat_id,limit=min(max(limit,1),100))]
        return [await _message_json(c,chat_id,m) for m in msgs]

    @web_app.get("/api/sessions/{sid}/chats/{chat_id}/search")
    async def web_search_messages(sid:int, chat_id:int, q:str=Query(""), init_data:str=Query("")):
        c=await _web_client(sid, init_data); c._web_sid=sid
        msgs=[m async for m in c.iter_messages(chat_id,limit=100,search=q)]
        return [await _message_json(c,chat_id,m) for m in msgs]

    @web_app.get("/api/sessions/{sid}/media/{chat_id}/{msg_id}")
    async def web_media(sid:int, chat_id:int, msg_id:int, init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        m=await c.get_messages(chat_id,ids=msg_id)
        if not m or not m.media: raise HTTPException(404,"الوسائط غير موجودة")
        async def gen():
            import io
            bio=io.BytesIO()
            await c.download_media(m.media,file=bio)
            bio.seek(0)
            while True:
                chunk=bio.read(1024*1024)
                if not chunk: break
                yield chunk
        mime=getattr(getattr(m,"file",None),"mime_type",None) or "application/octet-stream"
        filename=getattr(getattr(m,"file",None),"name",None) or "media"
        headers={"Content-Disposition": f"inline; filename*=UTF-8''{quote(filename)}"}
        return StreamingResponse(gen(),media_type=mime,headers=headers)

    @web_app.post("/api/sessions/{sid}/chats/{chat_id}/send")
    async def web_send(sid:int, chat_id:int, body:SendBody, init_data:str=Query("")):
        c=await _web_client(sid, init_data)
        text_msg=body.text.strip()
        if not text_msg: raise HTTPException(400,"الرسالة فارغة")
        m=await c.send_message(chat_id,text_msg)
        return {"ok":True,"id":m.id}


# Runtime dashboard counters
runtime_stats = {
    "started_at": time.time(),
    "downloads_started": 0,
    "downloads_done": 0,
    "downloads_failed": 0,
    "transfers_started": 0,
    "transfers_done": 0,
    "transfers_failed": 0,
    "messages_processed": 0,
    "bytes_downloaded": 0,
    "bytes_uploaded": 0,
}

locks: dict[int, asyncio.Lock] = {}
active_link_tasks: dict[int, asyncio.Task] = {}
channel_transfer_tasks: dict[int, asyncio.Task] = {}
channel_transfers: dict[str, dict[str, Any]] = {}

# Semaphores مستقلة حتى لا يؤدي ضغط المستخدمين إلى فتح عشرات عمليات نقل/رفع
# في نفس اللحظة وإسقاط الخدمة أو الوصول السريع إلى حدود Telegram.
media_semaphore = asyncio.Semaphore(MEDIA_CONCURRENCY)
transfer_semaphore = asyncio.Semaphore(TRANSFER_CONCURRENCY)


def load_channel_transfers() -> None:
    global channel_transfers
    if not TRANSFER_STATE_PATH.exists():
        return
    try:
        data = json.loads(TRANSFER_STATE_PATH.read_text(encoding="utf-8"))
        channel_transfers = {str(k): v for k, v in data.items()}
        changed = False
        for job in channel_transfers.values():
            if "session_user_id" not in job:
                job["session_user_id"] = OWNER_ID
                changed = True
            # المهام القديمة أنشأها المالك قبل إضافة صلاحية النقل للمستخدمين.
            if "created_by" not in job:
                job["created_by"] = OWNER_ID
                changed = True
        if changed:
            save_channel_transfers()
    except Exception:
        logger.exception("تعذر تحميل قائمة نقل القنوات")
        channel_transfers = {}


def save_channel_transfers() -> None:
    temp_path = TRANSFER_STATE_PATH.with_suffix(".tmp")
    temp_path.write_text(json.dumps(channel_transfers, ensure_ascii=False, indent=2), encoding="utf-8")
    temp_path.replace(TRANSFER_STATE_PATH)


def transfer_message_signature(message) -> str | None:
    """بصمة محافظة للبحث عن نسخة موجودة في الهدف دون تنزيل الوسائط."""
    text = (getattr(message, "message", None) or "").strip()
    media = getattr(message, "media", None)
    if not media:
        # النصوص العادية المتكررة قد تكون منشورات مختلفة؛ نقارن النص فقط إذا احتوى رابطاً.
        return f"text|{text}" if "http://" in text or "https://" in text else None
    document = getattr(message, "document", None)
    photo = getattr(message, "photo", None)
    if document is not None:
        size = int(getattr(document, "size", 0) or 0)
        mime = getattr(document, "mime_type", "") or ""
        name = ""
        width = height = duration = 0
        for attribute in getattr(document, "attributes", []) or []:
            filename = getattr(attribute, "file_name", None)
            if filename:
                name = filename
            width = int(getattr(attribute, "w", width) or width)
            height = int(getattr(attribute, "h", height) or height)
            duration = int(getattr(attribute, "duration", duration) or duration)
        # لا ندخل الوصف في بصمة الملف؛ قد يختلف الوصف عند إعادة النشر.
        return f"document|{mime}|{size}|{name}|{width}x{height}|{duration}"
    if photo is not None:
        photo_sizes = getattr(photo, "sizes", None) or []
        largest_photo_size = photo_sizes[-1] if photo_sizes else None
        photo_size = int(getattr(largest_photo_size, "size", 0) or 0)
        photo_width = int(getattr(photo, "w", 0) or 0)
        photo_height = int(getattr(photo, "h", 0) or 0)
        return f"photo|{photo_width}|{photo_height}|{photo_size}"
    return f"media|{type(media).__name__}|{text}"


async def build_target_signature_index(client: TelegramClient, target) -> set[str]:
    """يبني فهرساً خفيفاً من رسائل الهدف؛ لا ينزّل الملفات.
    TARGET_INDEX_LIMIT=0 يعني فهرسة كاملة؛ القيمة الافتراضية تحدّ من زمن البدء
    في القنوات الضخمة مع بقاء delivered_source_message_ids لمنع التكرار في المهام المستمرة.
    """
    signatures: set[str] = set()
    limit = max(0, int(os.getenv("TARGET_INDEX_LIMIT", "20000")))
    async for target_message in client.iter_messages(target, limit=limit or None):
        signature = transfer_message_signature(target_message)
        if signature:
            signatures.add(signature)
    return signatures


async def verify_target_message(client: TelegramClient, target, sent_message) -> bool:
    """يتأكد أن Telegram أنشأ الرسالة فعلاً في الهدف قبل اعتمادها."""
    if isinstance(sent_message, (list, tuple)):
        sent_message = sent_message[-1] if sent_message else None
    message_id = getattr(sent_message, "id", None)
    if not message_id:
        return False
    try:
        confirmed = await client.get_messages(target, ids=int(message_id))
        return confirmed is not None and getattr(confirmed, "id", None) == int(message_id)
    except Exception:
        logger.exception("تعذر التحقق من رسالة الهدف ذات المعرّف %s", message_id)
        return False


async def find_target_message_by_signature(client: TelegramClient, target, signature: str | None):
    """يبحث بعد فشل/مهلة الرفع عن نسخة قُبلت رغم عدم عودة الاستجابة."""
    if not signature:
        return None
    async for target_message in client.iter_messages(target):
        if transfer_message_signature(target_message) == signature:
            return target_message
    return None


load_channel_transfers()


def get_lock(user_id: int) -> asyncio.Lock:
    if user_id not in locks:
        locks[user_id] = asyncio.Lock()
    return locks[user_id]


def session_path(user_id: int) -> str:
    return str(SESSION_DIR / f"user_{user_id}")


def normalize_otp(value: str) -> str:
    arabic_digits = str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")
    return re.sub(r"\s+", "", value).translate(arabic_digits)


def format_size(size_bytes: int) -> str:
    size_gb = size_bytes / (1024 ** 3)
    if size_gb >= 1:
        return f"{size_gb:.2f} غيغابايت"
    return f"{size_bytes / (1024 ** 2):.0f} ميغابايت"


def normalize_channel_ref(value: str | int):
    """يقبل @username أو username أو معرّف القناة أو رابط Telegram."""
    raw = str(value).strip()
    public_match = re.fullmatch(r"https?://t\.me/(?P<username>[A-Za-z0-9_]+)(?:/\d+)?/?", raw)
    if public_match:
        return "@" + public_match.group("username")
    private_match = re.fullmatch(r"https?://t\.me/c/(?P<channel_id>\d+)(?:/\d+)?/?", raw)
    if private_match:
        return int("-100" + private_match.group("channel_id"))
    if re.fullmatch(r"-100\d+", raw):
        return int(raw)
    if re.fullmatch(r"\d+", raw):
        return int("-100" + raw)
    if raw.startswith("@") and re.fullmatch(r"@[A-Za-z0-9_]{3,}", raw):
        return raw
    if re.fullmatch(r"[A-Za-z0-9_]{3,}", raw):
        return "@" + raw
    raise ValueError(
        "صيغة القناة غير صحيحة. أرسل @username أو رابط https://t.me/... أو المعرّف الرقمي مثل -1001234567890."
    )


async def resolve_channel_entity(client: TelegramClient, reference):
    """حل قناة بالاسم أو الرابط أو المعرّف، مع البحث في حوارات الحساب عند الحاجة."""
    try:
        return await client.get_entity(reference)
    except (ValueError, TypeError) as first_error:
        if not isinstance(reference, int) and not str(reference).lstrip("-").isdigit():
            raise first_error
        numeric = int(reference)
        channel_id = int(str(abs(numeric))[3:]) if str(abs(numeric)).startswith("100") else abs(numeric)
        async for dialog in client.iter_dialogs():
            entity = dialog.entity
            if getattr(entity, "id", None) == channel_id:
                return entity
        raise ValueError(
            f"لم يجد الحساب القناة ذات المعرّف {reference} في حواراته. "
            "افتح القناة بالحساب أولاً، ثم أعد المحاولة."
        ) from first_error


def parse_message_link(link: str):
    match = LINK_PATTERN.search(link.strip())
    if not match:
        return None
    if match.group("private"):
        entity = int(f"-100{match.group('private_id')}")
    else:
        # مرّر الاسم بصيغة @username حتى لا يُفسَّر كنص أو قيمة غير مكتملة.
        entity = "@" + match.group("username")
    return entity, int(match.group("message_id"))


def is_public_message_link(link: str) -> bool:
    parsed = parse_message_link(link)
    return bool(parsed and isinstance(parsed[0], str))


async def discard_client_session(user_id: int, remove_file: bool = True) -> None:
    """إسقاط عميل Telethon وملف الجلسة التالف بأمان."""
    client = clients.pop(user_id, None)
    if client is not None:
        try:
            if client.is_connected():
                await client.disconnect()
        except Exception:
            logger.exception("تعذر فصل عميل المستخدم %s", user_id)
    if not remove_file:
        return
    base = Path(session_path(user_id))
    candidates = [
        Path(str(base) + ".session"),
        Path(str(base) + "-journal"),
        Path(str(base) + ".session-journal"),
    ]
    for path in candidates:
        try:
            if path.exists():
                path.unlink()
                logger.warning("تم حذف ملف جلسة المستخدم %s: %s", user_id, path.name)
        except Exception:
            logger.exception("تعذر حذف ملف جلسة المستخدم %s: %s", user_id, path)


async def get_or_create_client(user_id: int) -> TelegramClient:
    """إرجاع عميل الجلسة دون حذف ملفها تلقائياً عند أخطاء التفويض.

    مهم جداً: user_id هنا هو آيدي مستخدم البوت الذي يملك ملف الجلسة،
    وليس بالضرورة آيدي حساب Telegram المسجّل داخل الجلسة. لذلك لا يجوز
    حذف ملف جلسة بناءً على AuthKeyUnregisteredError دون تأكيد صريح.
    """
    client = clients.get(user_id)
    if client is None:
        client = TelegramClient(session_path(user_id), API_ID, API_HASH)
        clients[user_id] = client
    if not client.is_connected():
        try:
            await client.connect()
        except AuthKeyUnregisteredError:
            # حماية من حذف جلسة أخرى بالخطأ. الملف يبقى كما هو حتى يقرر
            # المالك حذفه صراحة من زر تسجيل الخروج/الحذف.
            logger.warning(
                "مفتاح جلسة المستخدم %s غير مسجل؛ لن يتم حذف ملف الجلسة تلقائياً",
                user_id,
            )
            clients.pop(user_id, None)
            raise
        except ValueError as exc:
            if "cannot be reused after logging out" not in str(exc).lower():
                raise
            # لا نحذف ملف الجلسة هنا أيضاً؛ نترك قرار الحذف/إعادة التسجيل
            # لمسار تسجيل الدخول الصريح.
            logger.warning(
                "جلسة المستخدم %s لا يمكن إعادة استخدامها بعد تسجيل الخروج؛ "
                "يجب إعادة تسجيل الدخول صراحةً دون حذف جلسات أخرى",
                user_id,
            )
            clients.pop(user_id, None)
            raise
    return client


async def inspect_session_identity(user_id: int, client: TelegramClient | None = None):
    """يتحقق من الحساب الحقيقي داخل ملف الجلسة دون حذف أي ملف.

    يعيد كائن الحساب إذا كانت الجلسة صالحة، ويرفع الخطأ الأصلي إذا كانت
    جلسة Telegram غير مسجلة. لا يوجد في هذه الدالة أي حذف تلقائي.
    """
    client = client or await get_or_create_client(user_id)
    if not await client.is_user_authorized():
        raise ValueError("الجلسة غير مسجلة الدخول")
    me = await client.get_me()
    if not me or not getattr(me, "id", None):
        raise ValueError("تعذر التحقق من هوية حساب Telegram داخل الجلسة")
    return me


async def resolve_second_recipient(client: TelegramClient):
    raw = SECOND_RECIPIENT.strip()
    if raw.startswith("@"):
        return await client.get_entity(raw)

    if raw.lstrip("-").isdigit():
        recipient_id = int(raw)
        try:
            return await client.get_entity(recipient_id)
        except ValueError:
            # أرقام المستخدمين لا يمكن حلها دائماً من الذاكرة المحلية.
            # نبحث في الحوارات التي حمّلها حساب المستخدم أولاً.
            async for dialog in client.iter_dialogs():
                entity = dialog.entity
                if getattr(entity, "id", None) == recipient_id:
                    return entity
            raise ValueError(
                f"لا يمكن لحساب المستخدم العثور على المستلم {raw}. "
                "اجعل الحساب يفتح محادثة معه أولاً، أو استخدم اسم المستخدم بصيغة @username."
            )

    raise ValueError(
        "قيمة SECOND_RECIPIENT غير صحيحة. استخدم @username أو المعرّف الرقمي مع وجود محادثة سابقة."
    )


async def reset_public_client() -> None:
    """إسقاط العميل العام التالف فقط، دون لمس جلسات المستخدمين."""
    global public_client
    async with public_client_lock:
        old_client = public_client
        public_client = None
        if old_client is not None:
            try:
                if old_client.is_connected():
                    await old_client.disconnect()
            except Exception:
                logger.exception("تعذر فصل العميل العام التالف")


async def get_public_client() -> TelegramClient:
    """إنشاء عميل غير مسجل جديد لكل عملية عامة مستقلة."""
    # لا نشارك عميلاً مؤقتاً بين المستخدمين؛ مشاركة العميل قد تؤدي إلى
    # AuthKeyUnregisteredError عند تزامن عمليات متعددة أو إبطال مفتاح مؤقت.
    client = TelegramClient(None, API_ID, API_HASH)
    await client.connect()
    return client


async def is_ready(user_id: int) -> bool:
    client = clients.get(user_id)
    if client is None:
        session_file = Path(f"{session_path(user_id)}.session")
        if not session_file.exists():
            return False
        try:
            client = await get_or_create_client(user_id)
        except AuthKeyUnregisteredError:
            logger.warning(
                "جلسة المستخدم %s غير صالحة أثناء فحص التفويض؛ تم الحفاظ على الملف",
                user_id,
            )
            return False
    try:
        return await client.is_user_authorized()
    except AuthKeyUnregisteredError:
        logger.warning(
            "جلسة المستخدم %s غير صالحة أثناء فحص التفويض؛ لن يتم حذفها تلقائياً",
            user_id,
        )
        clients.pop(user_id, None)
        return False


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return
    user_id = update.effective_user.id
    logger.info("استلام /start من المستخدم %s", user_id)
    try:
        register_user(update.effective_user, referral_id_from_args(context.args))
    except Exception:
        logger.exception("تعذر حفظ بيانات المستخدم %s؛ يستمر /start دون الحفظ", user_id)
    if user_id in admins:
        await update.message.reply_text(
            "🛠️ *لوحة الإدارة*\n\nاختر القسم المطلوب من الأزرار أدناه.",
            parse_mode="Markdown",
            reply_markup=owner_keyboard() if user_id == OWNER_ID else admin_keyboard(),
        )
        return
    try:
        ready = await asyncio.wait_for(is_ready(user_id), timeout=20)
    except asyncio.TimeoutError:
        logger.warning("انتهت مهلة فحص جلسة المستخدم %s أثناء /start", user_id)
        ready = False
    except Exception:
        logger.exception("فشل فحص جلسة المستخدم %s أثناء /start", user_id)
        ready = False
    if ready:
        if user_id in admins:
            await update.message.reply_text(
                "🛠️ *لوحة الإدارة*\n\nاختر القسم المطلوب من الأزرار أدناه.",
                parse_mode="Markdown",
                reply_markup=admin_keyboard(),
            )
        else:
            await update.message.reply_text(
                "✅ *حسابك متصل*\n\nأرسل رابط منشور Telegram الذي تريد أرشفته، وسأتعامل معه في الخلفية.\n\n"
                "استخدم زر المساعدة لمعرفة طريقة الاستخدام.",
                parse_mode="Markdown",
                reply_markup=user_keyboard(user_id),
            )
        return
    states[user_id] = {"step": "phone"}
    await update.message.reply_text(
        "🔐 *تسجيل الدخول إلى Telegram*\n\n"
        "الخطوة ١ من ٣: أرسل رقم هاتف الحساب بالصيغة الدولية.\n"
        "مثال: `+249XXXXXXXXX`\n\n"
        "📌 سيُرسل Telegram رمز تحقق إلى تطبيق Telegram أو SMS.\n"
        "🔒 لا ترسل كلمة المرور أو الرمز لأي شخص؛ أرسله هنا فقط للبوت.\n"
        "↩️ يمكنك الإلغاء في أي وقت عبر /cancel.",
        parse_mode="Markdown",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ إلغاء", callback_data="user:cancel")]]),
    )


async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user:
        states.pop(update.effective_user.id, None)
    if update.message:
        await update.message.reply_text("تم إلغاء العملية الحالية.")


async def handle_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return

    user_id = update.effective_user.id
    register_user(update.effective_user)
    text = (update.message.text or "").strip()
    state = states.get(user_id, {})

    async with get_lock(user_id):
        if state.get("step") == "phone":
            await begin_login(update, user_id, text)
            return
        if state.get("step") == "code":
            await finish_code(update, user_id, text)
            return
        if state.get("step") == "password":
            await finish_password(update, user_id, text)
            return
        if (user_id in admins or can_use_channel_transfer(user_id)) and state.get("step") in {
            "transfer_source", "transfer_target", "transfer_delete", "admin_add", "admin_broadcast", "transfer_access_grant", "transfer_access_revoke"
        }:
            if state.get("step") == "admin_add" and user_id != OWNER_ID:
                states.pop(user_id, None)
                await update.message.reply_text("⛔ إضافة المشرفين مخصصة للمالك فقط.")
                return
            if state.get("step", "").startswith("transfer_"):
                await handle_transfer_input(update, text, state)
            else:
                await handle_admin_input(update, context, text, state)
            return

    try:
        ready = await asyncio.wait_for(is_ready(user_id), timeout=20)
    except Exception:
        logger.exception("فشل فحص الجلسة قبل معالجة رسالة المستخدم %s", user_id)
        ready = False
    if ready:
        if user_id not in admins:
            quota = quota_snapshot(user_id)
            if quota["total_remaining"] <= 0:
                await update.message.reply_text(
                    "🚫 انتهت حصتك الحالية.\n\n"
                    "الحصة اليومية: 5 مقاطع. ادعُ مستخدماً جديداً عبر رابطك لتحصل على 5 مقاطع إضافية لكل إحالة.\n\n"
                    f"👥 إحالاتك المقبولة: {quota['referral_count']}\n"
                    "🔗 رابط الدعوة موجود في زر حالة الحساب."
                )
                return
        current_task = active_link_tasks.get(user_id)
        if current_task and not current_task.done():
            await update.message.reply_text(
                "⏳ لديك عملية تنزيل قيد التنفيذ. أرسل رابطاً جديداً بعد انتهائها."
            )
            return

        active_link_tasks[user_id] = asyncio.create_task(
            run_link_task(update, context, user_id, text)
        )
        await update.message.reply_text(
            "✅ تم استلام الرابط وبدأ التنزيل."
        )
    else:
        # القنوات العامة يمكن تجربتها دون تسجيل دخول؛ المحتوى الخاص أو المقيد
        # سيستمر في طلب جلسة Telegram مسجلة.
        if is_public_message_link(text):
            quota = quota_snapshot(user_id)
            if quota["total_remaining"] <= 0 and user_id not in admins:
                await update.message.reply_text(
                    localized(user_id,
                        "🚫 انتهت حصتك الحالية. ادعُ مستخدماً جديداً من حالة الحساب للحصول على رصيد إضافي.",
                        "🚫 Your quota is exhausted. Invite a new user from Account status to get bonus credits."
                    )
                )
                return
            current_task = active_link_tasks.get(user_id)
            if current_task and not current_task.done():
                await update.message.reply_text(localized(user_id, "⏳ لديك عملية تنزيل قيد التنفيذ.", "⏳ A download is already in progress."))
                return
            active_link_tasks[user_id] = asyncio.create_task(run_link_task(update, context, user_id, text))
            await update.message.reply_text(localized(user_id, "✅ تم استلام الرابط وبدأ التنزيل.", "✅ Link received. Download started."))
        else:
            await update.message.reply_text(localized(user_id, "أرسل /start لتسجيل الدخول أو أرسل رابط قناة عامة.", "Send /start to log in, or send a public channel link."))


async def run_link_task(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    user_id: int,
    text: str,
) -> None:
    try:
        succeeded = await process_link(update, context, user_id, text)
        if succeeded and user_id not in admins:
            consume_quota(user_id)
            quota = quota_snapshot(user_id)
            try:
                await update.message.reply_text(
                    f"📊 المتبقي: {quota['total_remaining']} مقطع "
                    f"(اليومي: {quota['daily_remaining']}، الإضافي: {quota['bonus_credits']})."
                )
            except Exception:
                logger.exception("تعذر إرسال رصيد المستخدم %s", user_id)
    except asyncio.CancelledError:
        logger.info("تم إلغاء مهمة الرابط للمستخدم %s", user_id)
        raise
    except Exception:
        logger.exception("خطأ غير معالج في مهمة الرابط للمستخدم %s", user_id)
    finally:
        current = asyncio.current_task()
        if active_link_tasks.get(user_id) is current:
            active_link_tasks.pop(user_id, None)


async def begin_login(update: Update, user_id: int, phone: str) -> None:
    if not re.fullmatch(r"\+[1-9]\d{7,14}", phone):
        await update.message.reply_text(
            "⚠️ رقم الهاتف غير صحيح.\n\nأرسله بالصيغة الدولية، مثل: `+249XXXXXXXXX`.",
            parse_mode="Markdown",
        )
        return

    try:
        client = await asyncio.wait_for(get_or_create_client(user_id), timeout=30)
        sent = await asyncio.wait_for(client.send_code_request(phone), timeout=60)
    except AuthKeyUnregisteredError:
        # المستخدم بدأ تسجيل دخول صريحاً؛ هنا فقط نزيل الجلسة القديمة
        # الخاصة بهذا المستخدم في البوت، ثم ننشئ جلسة نظيفة.
        clients.pop(user_id, None)
        await discard_client_session(user_id, remove_file=True)
        try:
            client = await asyncio.wait_for(get_or_create_client(user_id), timeout=30)
            sent = await asyncio.wait_for(client.send_code_request(phone), timeout=60)
        except Exception as exc:
            states.pop(user_id, None)
            logger.exception("فشل إنشاء جلسة جديدة للمستخدم %s بعد جلسة تالفة", user_id)
            await update.message.reply_text(
                f"❌ تعذر إنشاء جلسة Telegram جديدة ({type(exc).__name__}). أرسل /start وحاول مرة أخرى."
            )
            return
    except ValueError as exc:
        if "cannot be reused after logging out" not in str(exc).lower():
            states.pop(user_id, None)
            logger.exception("فشل تجهيز جلسة المستخدم %s", user_id)
            await update.message.reply_text(f"❌ تعذر تجهيز تسجيل الدخول ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
            return
        # تسجيل الدخول الصريح يسمح باستبدال جلسة هذا المستخدم فقط.
        clients.pop(user_id, None)
        await discard_client_session(user_id, remove_file=True)
        try:
            client = await asyncio.wait_for(get_or_create_client(user_id), timeout=30)
            sent = await asyncio.wait_for(client.send_code_request(phone), timeout=60)
        except Exception as retry_exc:
            states.pop(user_id, None)
            logger.exception("فشل إعادة إنشاء جلسة المستخدم %s", user_id)
            await update.message.reply_text(
                f"❌ تعذر إنشاء جلسة Telegram جديدة ({type(retry_exc).__name__}). أرسل /start وحاول مرة أخرى."
            )
            return
    except FloodWaitError as exc:
        states.pop(user_id, None)
        wait_seconds = int(exc.seconds)
        wait_minutes = (wait_seconds + 59) // 60
        await update.message.reply_text(
            f"Telegram فرض فترة انتظار بسبب كثرة طلبات الرموز. حاول مرة أخرى بعد نحو {wait_minutes} دقيقة."
        )
        logger.warning("FloodWait عند طلب رمز للمستخدم %s: %s ثانية", user_id, wait_seconds)
        return
    except (PhoneNumberInvalidError, PhoneNumberBannedError) as exc:
        states.pop(user_id, None)
        reason = "رقم الهاتف غير صحيح." if isinstance(exc, PhoneNumberInvalidError) else "هذا الرقم محظور من Telegram."
        await update.message.reply_text(f"❌ تعذر إرسال الرمز.\n\n{reason}\nتحقق من الرقم الدولي ثم أرسل /start وحاول مرة أخرى.")
        return
    except SendCodeUnavailableError:
        states.pop(user_id, None)
        await update.message.reply_text("❌ Telegram لا يسمح بإرسال رمز جديد لهذا الرقم حالياً. انتظر قليلاً ثم أرسل /start وحاول مرة أخرى.")
        return
    except asyncio.TimeoutError:
        states.pop(user_id, None)
        logger.warning("انتهت مهلة طلب رمز الدخول للمستخدم %s", user_id)
        await update.message.reply_text("⏱️ لم يصل رد Telegram في الوقت المحدد. لم تُحفظ محاولة ناقصة؛ أرسل /start وحاول مرة أخرى.")
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("فشل طلب رمز الدخول للمستخدم %s", user_id)
        await update.message.reply_text(
            "❌ تعذر إرسال رمز Telegram.\n\n"
            f"السبب التقني: `{type(exc).__name__}`\n\n"
            "لم يتم الانتقال إلى خطوة الرمز. تحقق من الرقم وأرسل /start وحاول مرة أخرى.",
            parse_mode="Markdown",
        )
        return

    states[user_id] = {
        "step": "code",
        "phone": phone,
        "phone_code_hash": sent.phone_code_hash,
    }
    await update.message.reply_text(
        "📩 تم إرسال رمز Telegram.\n\n"
        "الخطوة ٢ من ٣: أرسل الرمز *مفرقاً إجبارياً* بهذا الشكل:\n"
        "`1 2 3 4 5`\n\n"
        "لا ترسله هكذا: `12345`.\n"
        "للإلغاء استخدم /cancel.",
    )


async def finish_code(update: Update, user_id: int, code: str) -> None:
    state = states.get(user_id, {})
    spaced_code_pattern = r"^\s*[0-9٠-٩](?:\s+[0-9٠-٩]){3,7}\s*$"
    if not re.fullmatch(spaced_code_pattern, code):
        await update.message.reply_text(
            "⚠️ أرسل رمز التحقق مفرقاً بين كل رقم، مثل:\n\n"
            "`1 2 3 4 5`\n\n"
            "لا ترسله متجمعاً مثل `12345`.",
            parse_mode="Markdown",
        )
        return
    normalized_code = normalize_otp(code)

    try:
        client = await get_or_create_client(user_id)
    except AuthKeyUnregisteredError:
        states.pop(user_id, None)
        clients.pop(user_id, None)
        await update.message.reply_text(
            "⚠️ جلسة Telegram القديمة غير مسجلة لدى Telegram. لم أحذف ملفها تلقائياً حمايةً من حذف جلسة أخرى. أرسل /start وابدأ تسجيل الدخول من جديد."
        )
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("تعذر تجهيز جلسة التحقق للمستخدم %s", user_id)
        await update.message.reply_text(f"❌ تعذر تجهيز تسجيل الدخول ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
        return

    try:
        await client.sign_in(
            phone=state["phone"],
            code=normalized_code,
            phone_code_hash=state["phone_code_hash"],
        )
    except SessionPasswordNeededError:
        states[user_id] = {"step": "password", "phone": state.get("phone")}

        await update.message.reply_text(
            "الحساب محمي بالتحقق بخطوتين. أرسل كلمة المرور مرة واحدة لإكمال الدخول."
        )
        return
    except PhoneCodeInvalidError:
        await update.message.reply_text("⚠️ الرمز غير صحيح. أرسله مرة أخرى مفرقاً، مثل: 1 2 3 4 5.")
        return
    except PhoneCodeExpiredError:
        states.pop(user_id, None)
        await update.message.reply_text("⚠️ انتهت صلاحية الرمز. أرسل /start واطلب رمزاً جديداً.")
        return
    except AuthKeyUnregisteredError:
        states.pop(user_id, None)
        clients.pop(user_id, None)
        await update.message.reply_text(
            "⚠️ جلسة Telegram القديمة غير مسجلة لدى Telegram. لم أحذف ملفها تلقائياً حمايةً من حذف جلسة أخرى. أرسل /start وابدأ تسجيل الدخول من جديد."
        )
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("فشل التحقق من رمز المستخدم %s", user_id)
        await update.message.reply_text(f"❌ تعذر التحقق من الرمز ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
        return

    states.pop(user_id, None)
    await update.message.reply_text(
        "✅ تم تسجيل الدخول بنجاح.\n\nأرسل الآن رابط منشور الفيديو المصرح بأرشفته.",
    )


async def finish_password(update: Update, user_id: int, password: str) -> None:
    try:
        client = await get_or_create_client(user_id)
    except AuthKeyUnregisteredError:
        states.pop(user_id, None)
        clients.pop(user_id, None)
        await update.message.reply_text(
            "⚠️ جلسة Telegram القديمة غير مسجلة لدى Telegram. لم أحذف ملفها تلقائياً حمايةً من حذف جلسة أخرى. أرسل /start وابدأ تسجيل الدخول من جديد."
        )
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("تعذر تجهيز جلسة كلمة المرور للمستخدم %s", user_id)
        await update.message.reply_text(f"❌ تعذر تجهيز تسجيل الدخول ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
        return
    try:
        await client.sign_in(password=password)
    except PasswordHashInvalidError:
        await update.message.reply_text("⚠️ كلمة مرور التحقق بخطوتين غير صحيحة. حاول مرة أخرى أو استخدم /cancel.")
        return
    except AuthKeyUnregisteredError:
        states.pop(user_id, None)
        clients.pop(user_id, None)
        await update.message.reply_text(
            "⚠️ جلسة Telegram القديمة غير مسجلة لدى Telegram. لم أحذف ملفها تلقائياً حمايةً من حذف جلسة أخرى. أرسل /start وابدأ تسجيل الدخول من جديد."
        )
        return
    except Exception as exc:
        states.pop(user_id, None)
        logger.exception("فشل التحقق من كلمة مرور المستخدم %s", user_id)
        await update.message.reply_text(f"❌ تعذر التحقق من كلمة المرور ({type(exc).__name__}). أرسل /start وحاول مرة أخرى.")
        return

    states.pop(user_id, None)
    await update.message.reply_text(
        "✅ تم تسجيل الدخول بنجاح.\n\nأرسل الآن رابط منشور الفيديو المصرح بأرشفته.",
    )


def owner_only(update: Update) -> bool:
    return bool(update.effective_user and update.effective_user.id == OWNER_ID)


def message_kind_label(message) -> str:
    if getattr(message, "photo", None):
        return "🖼️ صورة"
    if getattr(message, "video", None):
        return "🎬 فيديو"
    if getattr(message, "voice", None):
        return "🎙️ رسالة صوتية"
    if getattr(message, "audio", None):
        return "🎵 ملف صوتي"
    if getattr(message, "document", None):
        return "📄 ملف"
    if getattr(message, "sticker", None):
        return "🏷️ ملصق"
    if getattr(message, "media", None):
        return "📎 وسائط"
    return "💬 نص"


def message_open_url(entity, message_id: int) -> str | None:
    username = getattr(entity, "username", None)
    if username:
        return f"https://t.me/{username}/{message_id}"
    entity_id = int(getattr(entity, "id", 0) or 0)
    if entity_id < 0:
        return f"https://t.me/c/{abs(entity_id)}/{message_id}"
    return None


def account_display_name(user_id: int, user_obj=None) -> str:
    """اسم الحساب مع اليوزر، مع استخدام الآيدي كمرجع عند غياب الاسم."""
    entry = user_registry.get(str(user_id), {})
    name = getattr(user_obj, "full_name", "") if user_obj is not None else ""
    username = getattr(user_obj, "username", "") if user_obj is not None else ""
    name = name or entry.get("name") or ""
    username = username or entry.get("username") or ""
    if name and username:
        return f"{name} (@{username})"
    if name:
        return str(name)
    if username:
        return f"@{username}"
    return f"حساب Telegram {user_id}"


def admin_only(update: Update) -> bool:
    return bool(update.effective_user and update.effective_user.id in admins)


def has_channel_transfer_access(user_id: int) -> bool:
    """صلاحية نقل القنوات: المالك/المشرف، أو منح يدوي، أو خمسة إحالات."""
    if user_id == OWNER_ID or user_id in admins:
        return True
    entry = user_registry.get(str(user_id), {})
    return bool(entry.get("channel_transfer_access", False)) or int(entry.get("referral_count", 0) or 0) >= TRANSFER_REFERRAL_REQUIREMENT


def can_use_channel_transfer(user_id: int) -> bool:
    return has_channel_transfer_access(user_id)


def transfer_job_visible_to(user_id: int, job: dict[str, Any]) -> bool:
    """المالك يرى كل المهام؛ بقية المستخدمين يرون مهامهم فقط."""
    if user_id == OWNER_ID:
        return True
    return int(job.get("created_by", 0) or 0) == int(user_id)


def transfer_session_for_user(user_id: int, selected_session_id: int | None = None) -> int:
    """تحديد جلسة النقل. المستخدم العادي يستخدم جلسته؛ المالك يستطيع اختيار جلسة أخرى."""
    if selected_session_id is None:
        return int(user_id)
    selected = int(selected_session_id)
    if user_id != OWNER_ID and selected != user_id:
        raise PermissionError("لا يمكن لهذا المستخدم استخدام جلسة حساب آخر.")
    return selected


async def prepare_transfer_session(requesting_user_id: int, selected_session_id: int | None = None):
    """فتح جلسة النقل والتحقق من الحساب الحقيقي داخل ملف الجلسة."""
    session_user_id = transfer_session_for_user(requesting_user_id, selected_session_id)
    session_file = Path(f"{session_path(session_user_id)}.session")
    if not session_file.exists():
        raise ValueError(
            f"لا يوجد ملف جلسة للحساب {session_user_id}. سجّل دخول هذا الحساب أولاً من البوت ثم أعد المحاولة."
        )
    try:
        client = await get_or_create_client(session_user_id)
        authorized = await client.is_user_authorized()
    except AuthKeyUnregisteredError as exc:
        clients.pop(session_user_id, None)
        raise AuthKeyUnregisteredError() from exc
    if not authorized:
        raise ValueError(
            "الجلسة موجودة، لكن الحساب غير مسجل الدخول فيها. API ID وAPI HASH لا يسجلان دخول حساب Telegram؛ "
            "يجب أن تحتوي الجلسة على تسجيل دخول فعلي للحساب."
        )
    me = await client.get_me()
    actual_id = int(getattr(me, "id", 0) or 0)
    if not actual_id:
        raise ValueError("تعذر قراءة هوية حساب Telegram من الجلسة.")
    if actual_id != session_user_id:
        raise ValueError(
            f"عدم تطابق خطير: ملف الجلسة user_{session_user_id}.session مرتبط بالحساب {actual_id}. "
            "لن أستخدم الجلسة ولن أحذف أي ملف."
        )
    return client, me, session_user_id


def transfer_back_callback(user_id: int) -> str:
    return "admin:transfers" if user_id in admins else "user:transfers"


def user_keyboard(user_id: int | None = None) -> InlineKeyboardMarkup:
    uid = int(user_id or 0)
    is_en = user_language(uid) == "en" if uid else False
    rows = [
        [InlineKeyboardButton("🔑 Log in" if is_en else "🔑 تسجيل الدخول", callback_data="user:login")],
        [InlineKeyboardButton("📖 Help" if is_en else "📖 طريقة الاستخدام", callback_data="user:help")],
        [InlineKeyboardButton("🔐 Account status" if is_en else "🔐 حالة الحساب", callback_data="user:account")],
        [InlineKeyboardButton("🔁 Channel transfer" if is_en else "🔁 نقل القنوات", callback_data="user:transfers")],
        [InlineKeyboardButton("🔌 Disconnect temporarily" if is_en else "🔌 فصل مؤقت", callback_data="user:disconnect")],
        [InlineKeyboardButton("🗑️ Log out and delete session" if is_en else "🗑️ حذف الجلسة وتسجيل الخروج", callback_data="user:logout")],
        [InlineKeyboardButton("🌐 العربية" if is_en else "🌐 English", callback_data="user:language")],
    ]
    return InlineKeyboardMarkup(rows)


def transfer_keyboard(back_callback: str = "admin:transfers") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ إضافة قناة مصدر وهدف", callback_data="transfer:add")],
        [InlineKeyboardButton("📋 قائمة القنوات", callback_data="transfer:list")],
        [InlineKeyboardButton("▶️ بدء الكل", callback_data="transfer:start_all"), InlineKeyboardButton("⏹️ إيقاف الكل", callback_data="transfer:stop_all")],
        [InlineKeyboardButton("🗑️ حذف مهمة", callback_data="transfer:delete")],
        [InlineKeyboardButton("⬅️ رجوع", callback_data=back_callback)],
    ])


def admin_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("👥 المستخدمون والجلسات", callback_data="admin:users")],
        [InlineKeyboardButton("🔁 نقل القنوات", callback_data="admin:transfers")],
        [InlineKeyboardButton("📢 إذاعة رسالة", callback_data="admin:broadcast")],
        [InlineKeyboardButton("🔄 تحديث اللوحة", callback_data="admin:home")],
    ])



def _fmt_bytes(n: int) -> str:
    n = max(0, int(n or 0))
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.1f} {unit}"
        n /= 1024

def owner_dashboard_text() -> str:
    active_tasks = sum(1 for t in asyncio.all_tasks() if not t.done())
    active_transfers = sum(1 for t in channel_transfer_tasks.values() if t and not t.done())
    sessions_total = len(clients)
    sessions_connected = sum(1 for c in clients.values() if c and c.is_connected())
    uptime = int(max(0, time.time() - runtime_stats["started_at"]))
    h, rem = divmod(uptime, 3600)
    m, s = divmod(rem, 60)
    return (
        "📊 لوحة تحكم المالك\n\n"
        f"👥 المستخدمون: {len(users)}\n"
        f"🔑 الجلسات: {sessions_total}\n"
        f"🟢 المتصلة: {sessions_connected}\n"
        f"🔄 عمليات النقل النشطة: {active_transfers}\n"
        f"⚙️ المهام النشطة: {active_tasks}\n\n"
        f"📥 التحميلات: {runtime_stats['downloads_started']} بدأ / "
        f"{runtime_stats['downloads_done']} مكتمل / {runtime_stats['downloads_failed']} فشل\n"
        f"🔄 النقل: {runtime_stats['transfers_started']} بدأ / "
        f"{runtime_stats['transfers_done']} مكتمل / {runtime_stats['transfers_failed']} فشل\n"
        f"💬 الرسائل المعالجة: {runtime_stats['messages_processed']}\n"
        f"⬇️ البيانات: {_fmt_bytes(runtime_stats['bytes_downloaded'])}\n"
        f"⬆️ البيانات: {_fmt_bytes(runtime_stats['bytes_uploaded'])}\n"
        f"⏱️ التشغيل: {h:02d}:{m:02d}:{s:02d}"
    )

def owner_dashboard_keyboard():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🔄 تحديث الإحصائيات", callback_data="owner:dashboard")],
        [InlineKeyboardButton("👥 الجلسات", callback_data="owner:sessions")],
        [InlineKeyboardButton("🔄 عمليات النقل", callback_data="transfer:list")],
    ])

def owner_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🌐 فتح Telegram Mini App", web_app=WebAppInfo(url=WEB_PUBLIC_BASE_URL))],
        [InlineKeyboardButton("🔑 تسجيل الدخول / تبديل الحساب", callback_data="user:login")],
        [InlineKeyboardButton("👥 المستخدمون والجلسات", callback_data="admin:users")],
        [InlineKeyboardButton("🔁 نقل القنوات", callback_data="admin:transfers")],
        [InlineKeyboardButton("💬 استعراض جلساتي", callback_data="owner:sessions")],
        [InlineKeyboardButton("📢 إذاعة رسالة", callback_data="admin:broadcast")],
        [InlineKeyboardButton("🛡️ إضافة مشرف", callback_data="admin:add")],
        [InlineKeyboardButton("✅ منح نقل القنوات", callback_data="admin:grant_transfer"), InlineKeyboardButton("🚫 سحب نقل القنوات", callback_data="admin:revoke_transfer")],
        [InlineKeyboardButton("🔄 تحديث اللوحة", callback_data="admin:home")],
    ])


async def channels_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_only(update) or not update.message:
        return
    if not channel_transfers:
        text = "📋 قائمة القنوات فارغة.\nأضف قناة بصيغة:\n/addchannel @source @target"
    else:
        rows = []
        for job_id, job in channel_transfers.items():
            rows.append(
                f"{job_id}. {job['source']} ➜ {job['target']} | "
                f"جلسة: {job.get('session_user_id', OWNER_ID)} | "
                f"{job.get('status', 'متوقف')} | آخر رسالة: {job.get('last_message_id', 0)}"
            )
        text = "📋 قائمة نقل القنوات:\n\n" + "\n".join(rows)
    await update.message.reply_text(text, reply_markup=admin_keyboard())


async def add_channel_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_only(update) or not update.message:
        return
    if len(context.args) != 2:
        await update.message.reply_text("الاستخدام: /addchannel @قناة_المصدر @قناة_الهدف")
        return
    source, target = context.args
    try:
        source = normalize_channel_ref(source)
        target = normalize_channel_ref(target)
    except ValueError as exc:
        await update.message.reply_text(f"⚠️ {exc}")
        return
    try:
        client = await get_or_create_client(OWNER_ID)
    except AuthKeyUnregisteredError:
        clients.pop(OWNER_ID, None)
        await update.message.reply_text(
            "⚠️ جلسة المالك غير صالحة لدى Telegram. لم يتم حذف ملفها. أعد تسجيل الدخول ثم حاول مرة أخرى."
        )
        return
    try:
        me = await inspect_session_identity(OWNER_ID, client)
    except AuthKeyUnregisteredError:
        clients.pop(OWNER_ID, None)
        await update.message.reply_text("⚠️ جلسة المالك غير صالحة لدى Telegram. لم يتم حذف ملفها. أعد تسجيل الدخول ثم حاول مرة أخرى.")
        return
    except Exception:
        await update.message.reply_text("سجّل دخول حساب النقل أولاً عبر /start.")
        return
    try:
        await resolve_channel_entity(client, source)
        await resolve_channel_entity(client, target)
    except Exception as exc:
        logger.exception("تعذر التحقق من القنوات")
        await update.message.reply_text(
            "تعذر الوصول إلى إحدى القناتين. تأكد أن حساب النقل عضو في المصدر ومشرف في الهدف.\n"
            f"التفصيل: {exc}"
        )
        return
    job_id = str(max([int(k) for k in channel_transfers if str(k).isdigit()] or [0]) + 1)
    channel_transfers[job_id] = {
        "source": source,
        "target": target,
        "created_by": OWNER_ID,
        "session_user_id": OWNER_ID,
        "session_account_id": int(getattr(me, "id", 0) or 0),
        "session_account_username": getattr(me, "username", "") or "",
        "status": "متوقف",
        "last_message_id": 0,
        "sent_count": 0,
        "skipped_count": 0,
        "skipped_message_ids": [],
    }
    save_channel_transfers()
    await update.message.reply_text(f"✅ تمت إضافة النقل رقم {job_id}: {source} ➜ {target}")


async def handle_transfer_input(update: Update, text: str, state: dict[str, Any]) -> None:
    if not update.message:
        return
    user_id = update.effective_user.id
    step = state.get("step")
    if step == "transfer_source":
        if not text:
            await update.message.reply_text("أرسل قناة المصدر بصيغة @username أو رابط القناة أو المعرّف الرقمي.")
            return
        try:
            state["source"] = normalize_channel_ref(text)
        except ValueError as exc:
            await update.message.reply_text(f"⚠️ {exc}")
            return
        state["step"] = "transfer_target"
        await update.message.reply_text(
            "أرسل الآن قناة الهدف بصيغة @username أو رابط القناة أو المعرّف الرقمي."
        )
        return
    if step == "transfer_target":
        source = state.get("source")
        target = text
        try:
            source = normalize_channel_ref(source or "")
            target = normalize_channel_ref(target)
        except ValueError as exc:
            await update.message.reply_text(f"⚠️ {exc}\nأرسل قيمة القناة من جديد، أو اضغط /cancel.")
            state["step"] = "transfer_source"
            return
        if not source or not target:
            states.pop(user_id, None)
            await update.message.reply_text("تعذر حفظ القنوات. اضغط إضافة وحاول من جديد.", reply_markup=transfer_keyboard(transfer_back_callback(user_id)))
            return
        # الجلسة تُحفظ صراحة داخل الحالة. للمستخدم الممنوح له النقل تكون جلسته هو،
        # وللمالك يمكن أن تكون جلسة اختارها من «استعراض جلساتي».
        requested_session_id = state.get("transfer_session_id")
        try:
            client, session_me, transfer_session_id = await prepare_transfer_session(
                user_id, int(requested_session_id) if requested_session_id is not None else None
            )
        except AuthKeyUnregisteredError:
            await update.message.reply_text(
                "⚠️ مفتاح جلسة الحساب غير مسجل لدى Telegram. لم يتم حذف الملف.\n"
                "أعد تسجيل الدخول للحساب من البوت ثم حاول النقل مرة أخرى."
            )
            return
        except Exception as identity_error:
            await update.message.reply_text(
                f"⚠️ تعذر التحقق من جلسة النقل.\n\n{identity_error}\n\n"
                "ملاحظة: API ID وAPI HASH هما بيانات تطبيق وليسا تسجيل دخول للحساب."
            )
            return
        try:
            source_entity = await resolve_channel_entity(client, source)
            target_entity = await resolve_channel_entity(client, target)
            if getattr(source_entity, "id", None) == getattr(target_entity, "id", None):
                raise ValueError("قناة المصدر وقناة الهدف متطابقتان. اختر قناتين مختلفتين.")
        except Exception as exc:
            logger.exception("تعذر التحقق من القنوات من الواجهة")
            await update.message.reply_text(
                "تعذر الوصول إلى إحدى القناتين. تأكد من عضوية الحساب وصلاحية الإرسال في الهدف.\n"
                f"التفصيل: {exc}\n\nأرسل اسم المصدر من جديد، أو اضغط /cancel."
            )
            state["step"] = "transfer_source"
            return
        job_id = str(max([int(k) for k in channel_transfers if str(k).isdigit()] or [0]) + 1)
        channel_transfers[job_id] = {
            "source": source,
            "target": target,
            "created_by": int(user_id),
            "session_user_id": transfer_session_id,
            "session_account_id": int(getattr(session_me, "id", 0) or 0),
            "session_account_username": getattr(session_me, "username", "") or "",
            "status": "متوقف",
            "last_message_id": 0,
            "sent_count": 0,
            "skipped_count": 0,
        }
        save_channel_transfers()
        states.pop(user_id, None)
        await update.message.reply_text(
            f"✅ تمت الإضافة رقم {job_id}.\n{source} ➜ {target}",
            reply_markup=transfer_keyboard(transfer_back_callback(user_id)),
        )
        return
    if step == "transfer_delete":
        if text not in channel_transfers or not transfer_job_visible_to(user_id, channel_transfers[text]):
            await update.message.reply_text("رقم المهمة غير موجود أو لا تملك صلاحية حذفها.")
            return
        task = channel_transfer_tasks.get(int(text))
        if task and not task.done():
            task.cancel()
        channel_transfers.pop(text, None)
        save_channel_transfers()
        states.pop(user_id, None)
        await update.message.reply_text("🗑️ حُذفت مهمة النقل.", reply_markup=transfer_keyboard(transfer_back_callback(user_id)))


def format_transfer_status(job_id: str, job: dict[str, Any]) -> str:
    status = job.get("status", "متوقف")
    sent = int(job.get("sent_count", 0))
    skipped = int(job.get("skipped_count", 0))
    last_id = int(job.get("last_message_id", 0))
    total = int(job.get("total_messages", 0))
    processed = sent + skipped
    if total > 0:
        percent = min(100, int(processed * 100 / total))
        progress = f"📊 التقدم: {processed} من {total} ({percent}٪)"
    else:
        progress = f"📊 تمت معالجة: {processed} رسالة"
    return (
        f"🔄 مهمة نقل رقم {job_id}\n\n"
        f"📥 المصدر: {job.get('source')}\n"
        f"📤 الهدف: {job.get('target')}\n"
        f"👤 جلسة النقل: {job.get('session_user_id', OWNER_ID)}"
        + (f" (@{job.get('session_account_username')})" if job.get('session_account_username') else "")
        + "\n"
        f"📌 الحالة: {status}\n"
        + (f"🛑 الخطأ: {job.get('error')}\n" if job.get('error') else "")
        + f"✅ تم الإرسال: {sent}\n"
        f"⚠️ تم التخطي: {skipped}\n"
        f"🆔 آخر رسالة: {last_id}\n"
        f"{progress}"
    )


async def update_transfer_status_message(job_id: str, context: ContextTypes.DEFAULT_TYPE) -> None:
    job = channel_transfers.get(job_id)
    if not job:
        return
    last_text = format_transfer_status(job_id, job)
    status_recipient = int(job.get("created_by") or OWNER_ID)
    message = await context.bot.send_message(
        chat_id=status_recipient,
        text=last_text,
    )
    try:
        while True:
            # تحديث كل 30 ثانية لتجنب Flood control؛ تقدم الملف التفصيلي
            # يبقى محفوظاً في الحالة ويظهر عند كل تحديث ناجح.
            await asyncio.sleep(30)
            job = channel_transfers.get(job_id)
            if not job:
                return
            new_text = format_transfer_status(job_id, job)
            if new_text != last_text:
                try:
                    await message.edit_text(new_text)
                    last_text = new_text
                except RetryAfter as exc:
                    wait_seconds = int(getattr(exc, "retry_after", 60))
                    logger.warning(
                        "Flood control أثناء تحديث المهمة %s؛ إيقاف تحديث الواجهة لمدة %s ثانية مع استمرار النقل",
                        job_id,
                        wait_seconds,
                    )
                    # لا نكرر editMessageText أثناء الحظر؛ عامل النقل مستقل ويستمر
                    # في حفظ status و last_message_id داخل ملف الحالة.
                    return
                except BadRequest as exc:
                    if "Message is not modified" not in str(exc):
                        logger.exception("تعذر تحديث رسالة تقدم المهمة %s", job_id)
                except Exception:
                    logger.exception("تعذر تحديث رسالة تقدم المهمة %s", job_id)
            if job.get("status") in {"مكتمل", "متوقف", "فشل"}:
                return
    except asyncio.CancelledError:
        job = channel_transfers.get(job_id)
        if job:
            final_text = format_transfer_status(job_id, job)
            if final_text != last_text:
                try:
                    await message.edit_text(final_text)
                except BadRequest as exc:
                    if "Message is not modified" not in str(exc):
                        logger.exception("تعذر تحديث الحالة النهائية للمهمة %s", job_id)
                except Exception:
                    logger.exception("تعذر تحديث الحالة النهائية للمهمة %s", job_id)
        raise


async def start_transfer_job(job_id: str, context: ContextTypes.DEFAULT_TYPE) -> None:
    async with transfer_semaphore:
        return await _start_transfer_job_inner(job_id, context)


async def _start_transfer_job_inner(job_id: str, context: ContextTypes.DEFAULT_TYPE) -> None:
    job = channel_transfers[job_id]
    progress_task = None
    job["status"] = "جارٍ تشغيل المهمة"
    job.pop("error", None)
    save_channel_transfers()
    progress_task = asyncio.create_task(update_transfer_status_message(job_id, context))
    try:
        logger.info("بدأ عامل نقل القنوات للمهمة %s", job_id)
        created_by = int(job.get("created_by") or OWNER_ID)
        transfer_session_id = int(job.get("session_user_id") or created_by)
        job["session_user_id"] = transfer_session_id
        job["status"] = f"جارٍ الاتصال بجلسة النقل {transfer_session_id}"
        try:
            client, session_me, transfer_session_id = await prepare_transfer_session(
                created_by, transfer_session_id
            )
        except AuthKeyUnregisteredError:
            job["status"] = "فشل؛ جلسة النقل غير صالحة"
            job["error"] = (
                f"جلسة النقل المرتبطة بالمعرّف {transfer_session_id} غير مسجلة لدى Telegram. "
                "لم يتم حذف ملف الجلسة تلقائياً."
            )
            save_channel_transfers()
            return
        except Exception as exc:
            job["status"] = "فشل؛ تعذر التحقق من جلسة النقل"
            job["error"] = str(exc)
            save_channel_transfers()
            return
        job["session_account_id"] = int(getattr(session_me, "id", 0) or 0)
        job["session_account_username"] = getattr(session_me, "username", "") or ""
        job["session_account_name"] = getattr(session_me, "first_name", "") or ""
        job["status"] = "جارٍ التحقق من القنوات"
        job.pop("error", None)
        save_channel_transfers()
        source = await resolve_channel_entity(client, job["source"])
        target = await resolve_channel_entity(client, job["target"])
        source_id = getattr(source, "id", None)
        target_id = getattr(target, "id", None)
        logger.info(
            "تم حل القنوات للمهمة %s: source_id=%s target_id=%s",
            job_id,
            source_id,
            target_id,
        )
        job["status"] = "جارٍ فهرسة محتوى الهدف للمقارنة"
        save_channel_transfers()
        target_signatures = await build_target_signature_index(client, target)
        job["target_indexed_count"] = len(target_signatures)
        logger.info("تمت فهرسة %s بصمة في الهدف للمهمة %s", len(target_signatures), job_id)
        if source_id is not None and source_id == target_id:
            raise ValueError(
                "قناة المصدر والهدف متطابقتان فعلياً؛ احذف المهمة وأضف قناة هدف مختلفة."
            )
        job["status"] = "جارٍ قراءة عدد الرسائل"
        try:
            job["total_messages"] = await client.get_messages(source, limit=0)
            job["total_messages"] = int(getattr(job["total_messages"], "total", 0) or 0)
        except Exception:
            job["total_messages"] = 0
        job["status"] = "يعمل"
        job.pop("last_skip_reason", None)
        save_channel_transfers()
        found_messages = 0
        async for message in client.iter_messages(
            source,
            min_id=int(job.get("last_message_id", 0)),
            reverse=True,
        ):
            if message.id <= int(job.get("last_message_id", 0)):
                continue
            found_messages += 1
            job["current_message_id"] = int(message.id)
            job["status"] = f"يعمل؛ معالجة الرسالة {message.id}"
            logger.info("معالجة الرسالة %s في المهمة %s", message.id, job_id)
            signature = transfer_message_signature(message)
            if signature and signature in target_signatures:
                job["duplicate_count"] = int(job.get("duplicate_count", 0)) + 1
                job["last_duplicate_message_id"] = int(message.id)
                job["status"] = f"تم تجاوز الرسالة {message.id}؛ موجودة مسبقاً في الهدف"
                job["last_message_id"] = int(message.id)
                save_channel_transfers()
                continue
            delivered = False
            sent_this_message = False
            transfer_attempts = 0
            delivered_source_ids = job.setdefault("delivered_source_message_ids", {})
            if str(message.id) in delivered_source_ids:
                job["duplicate_count"] = int(job.get("duplicate_count", 0)) + 1
                job["last_duplicate_message_id"] = int(message.id)
                job["status"] = f"تم تجاوز الرسالة {message.id}؛ نجاحها محفوظ مسبقاً"
                job["last_message_id"] = int(message.id)
                save_channel_transfers()
                continue
            while not delivered:
                try:
                    # لا نستخدم التحويل المباشر هنا؛ فقد يقبل Telegram الطلب
                    # ثم يعرض الرسالة في الهدف كقناة غير قابلة للعرض.
                    # المسار الوحيد هو تنزيل المحتوى ثم إعادة رفعه كنسخة مستقلة.
                    direct_forwarded = False
                    if not direct_forwarded:
                        if message.media:
                            with tempfile.TemporaryDirectory(prefix=f"transfer_{job_id}_") as temp_dir:
                                progress_clock = {"last": 0.0}

                                def download_progress(current: int, total: int) -> None:
                                    now = time.monotonic()
                                    if total <= 0:
                                        return
                                    if (now - progress_clock["last"] >= 5.0) or current >= total:
                                        progress_clock["last"] = now
                                        percent = min(100, int(current * 100 / total))
                                        job["download_current"] = int(current)
                                        job["download_total"] = int(total)
                                        job["status"] = (
                                            f"يعمل؛ تنزيل الرسالة {message.id}: "
                                            f"{format_size(current)} من {format_size(total)} ({percent}٪)"
                                        )

                                job["status"] = f"يعمل؛ تنزيل الرسالة {message.id}: 0 من الحجم الكلي (0٪)"
                                job["download_current"] = 0
                                job["download_total"] = 0
                                save_channel_transfers()
                                downloaded = await asyncio.wait_for(
                                    client.download_media(
                                        message,
                                        file=temp_dir,
                                        progress_callback=download_progress,
                                    ),
                                    timeout=TRANSFER_MEDIA_TIMEOUT_SECONDS,
                                )
                                if downloaded:
                                    downloaded_size = os.path.getsize(downloaded) if os.path.exists(downloaded) else 0
                                    job["status"] = (
                                        f"يعمل؛ جارٍ رفع الرسالة {message.id}: "
                                        f"0 من {format_size(downloaded_size)} (0٪)"
                                    )
                                    upload_clock = {"last": 0.0}

                                    def upload_progress(current: int, total: int) -> None:
                                        now = time.monotonic()
                                        if total <= 0:
                                            return
                                        if (now - upload_clock["last"] >= 5.0) or current >= total:
                                            upload_clock["last"] = now
                                            percent = min(100, int(current * 100 / total))
                                            job["upload_current"] = int(current)
                                            job["upload_total"] = int(total)
                                            job["status"] = (
                                                f"يعمل؛ رفع الرسالة {message.id}: "
                                                f"{format_size(current)} من {format_size(total)} ({percent}٪)"
                                            )

                                    save_channel_transfers()
                                    sent_result = await asyncio.wait_for(
                                        client.send_file(
                                            target,
                                            downloaded,
                                            caption=message.message or "",
                                            force_document=False,
                                            progress_callback=upload_progress,
                                        ),
                                        timeout=TRANSFER_MEDIA_TIMEOUT_SECONDS,
                                    )
                                    if not await verify_target_message(client, target, sent_result):
                                        raise RuntimeError("تمت محاولة الرفع لكن لم يتم تأكيد ظهور الرسالة في الهدف")
                                    sent_target_id = getattr(sent_result, "id", None)
                                    if isinstance(sent_result, (list, tuple)) and sent_result:
                                        sent_target_id = getattr(sent_result[-1], "id", None)
                                    delivered_source_ids[str(message.id)] = int(sent_target_id or 0)
                                    sent_this_message = True
                                else:
                                    raise ValueError("تعذر تنزيل الوسائط")
                        elif message.message:
                            job["status"] = f"يعمل؛ جارٍ إرسال النص {message.id}"
                            save_channel_transfers()
                            sent_result = await asyncio.wait_for(
                                client.send_message(target, message.message),
                                timeout=120,
                            )
                            if not await verify_target_message(client, target, sent_result):
                                raise RuntimeError("تمت محاولة إرسال النص لكن لم يتم تأكيد ظهوره في الهدف")
                            delivered_source_ids[str(message.id)] = int(getattr(sent_result, "id", 0) or 0)
                            sent_this_message = True
                        else:
                            job["skipped_count"] = int(job.get("skipped_count", 0)) + 1
                            skipped_ids = job.setdefault("skipped_message_ids", [])
                            if int(message.id) not in skipped_ids:
                                skipped_ids.append(int(message.id))
                            job["last_skip_reason"] = "منشور بلا نص أو وسائط قابلة للنقل"
                    delivered = True
                    if sent_this_message:
                        job["sent_count"] = int(job.get("sent_count", 0)) + 1
                        if signature:
                            target_signatures.add(signature)
                        save_channel_transfers()
                except FloodWaitError as exc:
                    wait_seconds = int(exc.seconds)
                    job["status"] = f"انتظار Telegram {wait_seconds} ثانية"
                    save_channel_transfers()
                    await asyncio.sleep(wait_seconds + 2)
                    job["status"] = "يعمل"
                except asyncio.TimeoutError:
                    confirmed_after_timeout = await find_target_message_by_signature(client, target, signature)
                    if confirmed_after_timeout is not None:
                        delivered_source_ids[str(message.id)] = int(getattr(confirmed_after_timeout, "id", 0) or 0)
                        if signature:
                            target_signatures.add(signature)
                        sent_this_message = True
                        delivered = True
                        job["sent_count"] = int(job.get("sent_count", 0)) + 1
                        job["status"] = f"تم تأكيد الرسالة {message.id} بعد انتهاء المهلة؛ لن تتكرر"
                        save_channel_transfers()
                        continue
                    transfer_attempts += 1
                    logger.exception("انتهت مهلة نقل الرسالة %s في المهمة %s", message.id, job_id)
                    if transfer_attempts < 5:
                        job["status"] = (
                            f"إعادة محاولة الرسالة {message.id} "
                            f"({transfer_attempts} من 4) بعد انتهاء المهلة"
                        )
                        job["last_error"] = "انتهت مهلة التنزيل أو الرفع؛ لم تُحسب الرسالة كتخطي"
                        save_channel_transfers()
                        await asyncio.sleep(min(60, transfer_attempts * 10))
                    else:
                        job["status"] = f"فشل نقل الرسالة {message.id} بعد 4 محاولات"
                        job["error"] = "الملف الكبير لم يكتمل؛ أعد تشغيل المهمة للاستئناف من هذه الرسالة"
                        save_channel_transfers()
                        raise RuntimeError(job["error"])
                except Exception as exc:
                    confirmed_after_error = await find_target_message_by_signature(client, target, signature)
                    if confirmed_after_error is not None:
                        delivered_source_ids[str(message.id)] = int(getattr(confirmed_after_error, "id", 0) or 0)
                        if signature:
                            target_signatures.add(signature)
                        sent_this_message = True
                        delivered = True
                        job["sent_count"] = int(job.get("sent_count", 0)) + 1
                        job["status"] = f"تم تأكيد الرسالة {message.id} بعد خطأ مؤقت؛ لن تتكرر"
                        save_channel_transfers()
                        continue
                    transfer_attempts += 1
                    logger.exception("فشل نقل الرسالة %s في المهمة %s", message.id, job_id)
                    if transfer_attempts < 4:
                        job["status"] = (
                            f"إعادة محاولة الرسالة {message.id} "
                            f"({transfer_attempts} من 3): {type(exc).__name__}"
                        )
                        job["last_error"] = f"{type(exc).__name__}: {exc}"
                        save_channel_transfers()
                        await asyncio.sleep(min(60, transfer_attempts * 10))
                    else:
                        job["status"] = f"فشل نقل الرسالة {message.id} بعد 3 محاولات"
                        job["error"] = f"{type(exc).__name__}: {exc}؛ لم تُحسب الرسالة كتخطي"
                        save_channel_transfers()
                        raise
            job["last_message_id"] = int(message.id)
            job.pop("current_message_id", None)
            save_channel_transfers()
        if found_messages == 0:
            job["status"] = "مكتمل؛ لا توجد رسائل جديدة"
            logger.info(
                "اكتملت المهمة %s دون رسائل جديدة؛ last_message_id=%s total=%s",
                job_id,
                job.get("last_message_id", 0),
                job.get("total_messages", 0),
            )
        else:
            job["status"] = "مكتمل"
            logger.info(
                "اكتملت المهمة %s: عُولجت=%s أُرسلت=%s تم تخطيها=%s",
                job_id,
                found_messages,
                job.get("sent_count", 0),
                job.get("skipped_count", 0),
            )
    except asyncio.CancelledError:
        job["status"] = "متوقف"
        raise
    except Exception as exc:
        logger.exception("فشل عامل نقل القنوات للمهمة %s", job_id)
        job["status"] = "فشل"
        job["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        if progress_task and not progress_task.done():
            progress_task.cancel()
            try:
                await progress_task
            except asyncio.CancelledError:
                pass
        save_channel_transfers()
        channel_transfer_tasks.pop(int(job_id), None)


async def start_transfer_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_only(update) or not update.message:
        return
    job_ids = context.args or list(channel_transfers.keys())
    started = []
    for job_id in job_ids:
        if job_id not in channel_transfers:
            continue
        if int(job_id) in channel_transfer_tasks and not channel_transfer_tasks[int(job_id)].done():
            continue
        channel_transfer_tasks[int(job_id)] = asyncio.create_task(start_transfer_job(job_id, context))
        started.append(job_id)
    await update.message.reply_text("▶️ بدأ النقل: " + (", ".join(started) if started else "لا توجد مهمة جديدة."))


async def stop_transfer_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_only(update) or not update.message:
        return
    job_ids = context.args or list(channel_transfers.keys())
    stopped = []
    for job_id in job_ids:
        task = channel_transfer_tasks.get(int(job_id)) if str(job_id).isdigit() else None
        if task and not task.done():
            task.cancel()
            stopped.append(job_id)
    await update.message.reply_text("⏹️ تم طلب إيقاف: " + (", ".join(stopped) if stopped else "لا توجد مهمة تعمل."))


async def transfer_status_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await channels_command(update, context)


async def handle_admin_input(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str, state: dict[str, Any]) -> None:
    if not update.message:
        return
    step = state.get("step")
    if step in {"transfer_access_grant", "transfer_access_revoke"}:
        try:
            target_id = int(text.strip())
            if target_id <= 0:
                raise ValueError
        except ValueError:
            await update.message.reply_text("⚠️ أرسل آيدي Telegram الرقمي فقط، مثل: 123456789")
            return
        target = user_registry.setdefault(str(target_id), {"id": target_id})
        granted = step == "transfer_access_grant"
        target["channel_transfer_access"] = granted
        save_admin_state()
        states.pop(update.effective_user.id, None)
        action = "منح" if granted else "سحب"
        await update.message.reply_text(
            f"✅ تم {action} صلاحية نقل القنوات للمستخدم {target_id}.\n"
            "هذه الصلاحية لا تضيفه كمشرف ولا تمنحه استعراض الجلسات.",
            reply_markup=owner_keyboard(),
        )
    elif step == "admin_add":
        try:
            new_admin = int(text.strip())
            if new_admin <= 0:
                raise ValueError
        except ValueError:
            await update.message.reply_text("⚠️ أرسل آيدي Telegram الرقمي فقط، مثل: 123456789")
            return
        admins.add(new_admin)
        save_admin_state()
        states.pop(update.effective_user.id, None)
        await update.message.reply_text(f"✅ تمت إضافة المشرف {new_admin} بنجاح.", reply_markup=admin_keyboard())
    elif step == "admin_broadcast":
        if not text:
            await update.message.reply_text("⚠️ لا يمكن إرسال إذاعة فارغة. أرسل النص أو /cancel.")
            return
        sent = failed = 0
        broadcast_sem = asyncio.Semaphore(max(1, int(os.getenv("BROADCAST_CONCURRENCY", "8"))))

        async def send_one(user_id: str) -> bool:
            async with broadcast_sem:
                try:
                    await context.bot.send_message(
                        chat_id=int(user_id),
                        text=f"📢 رسالة من الإدارة\n\n{text}",
                    )
                    return True
                except Exception:
                    logger.exception("فشلت الإذاعة إلى المستخدم %s", user_id)
                    return False

        results = await asyncio.gather(
            *(send_one(user_id) for user_id in list(user_registry)),
            return_exceptions=False,
        )
        sent = sum(results)
        failed = len(results) - sent
        states.pop(update.effective_user.id, None)
        await update.message.reply_text(f"✅ اكتملت الإذاعة.\nتم الإرسال: {sent}\nفشل الإرسال: {failed}", reply_markup=admin_keyboard())


def admin_users_text() -> str:
    active_sessions = sum(1 for uid in user_registry if Path(f"{session_path(int(uid))}.session").exists())
    active_clients = sum(1 for client in clients.values() if client.is_connected())
    lines = [
        "👥 *المستخدمون والجلسات*", "",
        f"👤 المستخدمون المسجلون: {len(user_registry)}",
        f"💾 ملفات الجلسات: {active_sessions}",
        f"🔌 الجلسات المتصلة الآن: {active_clients}",
        f"🛡️ عدد المشرفين: {len(admins)}", "",
    ]
    for entry in list(user_registry.values())[-20:]:
        name = entry.get("name") or "بدون اسم"
        username = f"@{entry['username']}" if entry.get("username") else "بدون معرف"
        referral_count = int(entry.get("referral_count", 0) or 0)
        transfer_status = "متاح ✅" if has_channel_transfer_access(int(entry.get("id", 0) or 0)) else "مغلق 🔒"
        if entry.get("channel_transfer_access"):
            transfer_status = "متاح بمنح المالك ✅"
        lines.append(f"• {name} — {username} — {entry.get('id')} | إحالات: {referral_count} | نقل: {transfer_status}")
    return "\n".join(lines)


async def transfer_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query:
        return
    data = query.data or ""
    logger.info("معالجة زر callback: user_id=%s data=%r", update.effective_user.id if update.effective_user else None, data)
    if data.startswith("admin:"):
        if not admin_only(update):
            await query.answer("هذه اللوحة مخصصة للمشرفين فقط.", show_alert=True)
            return
    if data.startswith("transfer:"):
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
    await query.answer()
    if data == "admin:home":
        await query.edit_message_text("🛠️ *لوحة الإدارة*\n\nاختر القسم المطلوب:", parse_mode="Markdown", reply_markup=owner_keyboard() if owner_only(update) else admin_keyboard())
    elif data == "admin:users":
        try:
            await query.edit_message_text(
                admin_users_text(),
                reply_markup=owner_keyboard() if owner_only(update) else admin_keyboard(),
            )
        except BadRequest as exc:
            if "Message is not modified" not in str(exc):
                raise
    elif data in {"admin:grant_transfer", "admin:revoke_transfer"}:
        if not owner_only(update):
            await query.answer("هذه العملية مخصصة للمالك فقط.", show_alert=True)
            return
        granting = data == "admin:grant_transfer"
        states[update.effective_user.id] = {"step": "transfer_access_grant" if granting else "transfer_access_revoke"}
        action = "منح" if granting else "سحب"
        await query.edit_message_text(
            f"🛡️ {action} صلاحية نقل القنوات\n\n"
            "أرسل آيدي Telegram الرقمي للمستخدم.\n"
            "لن تتم إضافته كمشرف، ولن يحصل على استعراض جلساتك.\n\n"
            "للإلغاء استخدم /cancel."
        )
    elif data == "admin:add":
        if not owner_only(update):
            await query.answer("إضافة المشرفين مخصصة للمالك فقط.", show_alert=True)
            return
        states[update.effective_user.id] = {"step": "admin_add"}
        await query.edit_message_text("🛡️ أرسل آيدي Telegram الرقمي للمشرف الجديد.\n\nللإلغاء استخدم /cancel.")
    elif data == "admin:broadcast":
        states[update.effective_user.id] = {"step": "admin_broadcast"}
        await query.edit_message_text("📢 أرسل الآن نص الإذاعة، وسيصل إلى المستخدمين المسجلين فقط.\n\nللإلغاء استخدم /cancel.")
    elif data == "user:transfers":
        uid = update.effective_user.id
        if not can_use_channel_transfer(uid):
            await query.edit_message_text(
                "🔒 قسم نقل القنوات غير متاح حالياً.\n\n"
                "يفتح القسم بعد تسجيل دعوة خمسة أصدقاء جدد، ثم أرسل /start أو افتح حالة الحساب لتحديث القائمة.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data="user:account")]]),
            )
            return
        await query.edit_message_text(
            "🔁 نقل القنوات\n\n"
            "أضف قناة مصدر وقناة هدف، ثم ابدأ المهمة.\n"
            "💡 من «استعراض جلساتي» افتح أي جلسة ثم اضغط «🔁 نقل القنوات من هذه الجلسة» لاستخدامها هي تحديداً.\n"
            "يلزم أن يكون حساب الجلسة عضواً في المصدر ومشرفاً في الهدف.",
            reply_markup=transfer_keyboard("user:account"),
        )
    elif data == "admin:transfers":
        await query.edit_message_text(
            "🔁 *نقل القنوات*\n\n"
            "أضف قناة مصدر وقناة هدف، ثم ابدأ المهمة.\n"
            "يمكن اختيار جلسة محددة من «استعراض جلساتي»، وتُحفظ الجلسة داخل المهمة.\n"
            "يتم النقل بالتسلسل، مع فحص التكرار والتوقف عند فشل الرسالة.",
            parse_mode="Markdown",
            reply_markup=transfer_keyboard("admin:home"),
        )
    elif data == "owner:sessions" or data.startswith("owner:sessions:"):
        if not owner_only(update):
            await query.answer("استعراض الجلسات مخصص للمالك فقط.", show_alert=True)
            return
        try:
            logger.info("فتح استعراض الجلسات للمالك %s، المسار=%s", update.effective_user.id, SESSION_DIR)
            session_ids = []
            for path in SESSION_DIR.glob("user_*.session"):
                suffix = path.stem[len("user_"):]
                if suffix.isdigit():
                    session_ids.append(int(suffix))
            session_ids = sorted(set(session_ids))
            logger.info("عدد ملفات الجلسات المكتشفة: %s", len(session_ids))
            if not session_ids:
                await query.edit_message_text("💬 لا توجد ملفات جلسات محفوظة.", reply_markup=owner_keyboard())
                return
            rows = []
            try:
                sessions_page = max(1, int(data.rsplit(":", 1)[1])) if data != "owner:sessions" else 1
            except (TypeError, ValueError):
                sessions_page = 1
            sessions_page_size = 10
            sessions_pages = max(1, (len(session_ids) + sessions_page_size - 1) // sessions_page_size)
            sessions_page = min(sessions_page, sessions_pages)
            session_start = (sessions_page - 1) * sessions_page_size
            for uid in session_ids[session_start:session_start + sessions_page_size]:
                entry = user_registry.get(str(uid), {})
                label = account_display_name(uid)
                status = "⚪"
                try:
                    session_client = await get_or_create_client(uid)
                    me = await inspect_session_identity(uid, session_client)
                    label = account_display_name(uid, me)
                    status = "🟢"
                except AuthKeyUnregisteredError:
                    status = "🔴"
                    label = f"{label} — جلسة غير صالحة"
                except Exception:
                    status = "🟡"
                if entry.get("username") and status == "⚪":
                    label = f"{entry.get('name') or '@' + entry['username']} (@{entry['username']})"
                rows.append([InlineKeyboardButton(f"{status} 📱 {label[:42]}", callback_data=f"owner:dialogs:{uid}")])
            session_nav = []
            if sessions_page > 1:
                session_nav.append(InlineKeyboardButton("⬅️ السابق", callback_data=f"owner:sessions:{sessions_page - 1}"))
            if sessions_page < sessions_pages:
                session_nav.append(InlineKeyboardButton("التالي ➡️", callback_data=f"owner:sessions:{sessions_page + 1}"))
            if session_nav:
                rows.append(session_nav)
            rows.append([InlineKeyboardButton("⬅️ رجوع إلى لوحة الإدارة", callback_data="admin:home")])
            await query.edit_message_text(
                f"💬 جلسات الحسابات المحفوظة\n📄 الصفحة: {sessions_page} من {sessions_pages}\n\n"
                "اختر جلسة لعرض القنوات والمحادثات، وستجد داخل كل جلسة زر «🔁 نقل القنوات من هذه الجلسة»:",
                reply_markup=InlineKeyboardMarkup(rows),
            )
            logger.info("تم عرض قائمة الجلسات للمالك %s", update.effective_user.id)
        except BadRequest as exc:
            if "Message is not modified" not in str(exc):
                logger.exception("فشل تعديل رسالة قائمة الجلسات")
                raise
        except Exception as exc:
            logger.exception("فشل استعراض الجلسات للمالك %s", update.effective_user.id)
            await query.edit_message_text(
                f"⚠️ تعذر عرض الجلسات.\nالسبب: {type(exc).__name__}: {exc}",
                reply_markup=owner_keyboard(),
            )
    elif data.startswith("owner:dialogs:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            session_user_id = int(data.rsplit(":", 1)[1])
            client = await get_or_create_client(session_user_id)
            if not await client.is_user_authorized():
                raise ValueError("الجلسة غير مسجلة الدخول")
            session_me = await client.get_me()
            session_name = account_display_name(session_user_id, session_me)
            rows = [
                [InlineKeyboardButton("🔁 نقل القنوات من هذه الجلسة", callback_data=f"owner:transfer:{session_user_id}")],
                [InlineKeyboardButton("🌐 فتح Telegram Mini App", web_app=WebAppInfo(url=WEB_PUBLIC_BASE_URL))],
                [InlineKeyboardButton("🔄 فحص حالة الجلسة", callback_data=f"owner:session_check:{session_user_id}")],
                [InlineKeyboardButton("🔌 فصل الجلسة", callback_data=f"owner:session_disconnect:{session_user_id}")],
                [InlineKeyboardButton("🗑️ حذف الجلسة", callback_data=f"owner:session_delete:{session_user_id}")],
            ]
            count = 0
            async for dialog in client.iter_dialogs(limit=200):
                entity = dialog.entity
                title = (dialog.name or "بدون اسم")[:35]
                kind = "📣" if getattr(entity, "broadcast", False) else ("👥" if getattr(entity, "megagroup", False) else "💬")
                rows.append([InlineKeyboardButton(f"{kind} {title}", callback_data=f"owner:chat:{session_user_id}:{getattr(entity, 'id', 0)}")])
                count += 1
            rows.append([InlineKeyboardButton("⬅️ رجوع إلى الجلسات", callback_data="owner:sessions")])
            await query.edit_message_text(
                f"💬 حساب: {session_name}\n"
                f"🆔 معرّف ملف الجلسة في البوت: {session_user_id}\n"
                f"🆔 معرّف حساب Telegram الفعلي: {getattr(session_me, 'id', 'غير معروف')}\n\n"
                f"عدد الحوارات المعروضة: {count}",
                reply_markup=InlineKeyboardMarkup(rows),
            )
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text(
                "⚠️ هذه الجلسة غير صالحة لدى Telegram. لم يتم حذف ملفها تلقائياً حمايةً من حذف جلسة أخرى.\n"
                "أعد تسجيل الحساب من جديد أو احذف الجلسة يدوياً من حسابها.",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("⬅️ رجوع إلى الجلسات", callback_data="owner:sessions")],
                    [InlineKeyboardButton("⬅️ لوحة الإدارة", callback_data="admin:home")],
                ]),
            )
        except Exception as exc:
            logger.exception("تعذر عرض حوارات الجلسة %s", data)
            await query.edit_message_text(f"⚠️ تعذر فتح الجلسة.\nالسبب: {type(exc).__name__}: {exc}", reply_markup=owner_keyboard())
    elif data.startswith("owner:transfer:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            session_user_id = int(data.rsplit(":", 1)[1])
            client, me, session_user_id = await prepare_transfer_session(
                update.effective_user.id, session_user_id
            )
            # نحفظ جلسة النقل داخل حالة المحادثة حتى لا يعود النقل تلقائياً إلى OWNER_ID.
            states[update.effective_user.id] = {
                "step": "transfer_source",
                "transfer_session_id": session_user_id,
                "transfer_account_id": int(getattr(me, "id", 0) or 0),
            }
            await query.edit_message_text(
                "🔁 نقل القنوات من جلسة محددة\n\n"
                f"👤 الحساب: {account_display_name(session_user_id, me)}\n"
                f"🆔 آيدي حساب Telegram: {getattr(me, 'id', 'غير معروف')}\n\n"
                "هذه العملية ستستخدم هذه الجلسة تحديداً، وليس جلسة المالك الافتراضية.\n\n"
                "أرسل الآن قناة المصدر بصيغة @username أو رابط القناة أو المعرّف الرقمي.\n"
                "للإلغاء استخدم /cancel.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع إلى الجلسة", callback_data=f"owner:dialogs:{session_user_id}")]]),
            )
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text(
                "⚠️ الجلسة المختارة غير صالحة لدى Telegram. لم يتم حذف ملفها. أعد تسجيل الدخول للحساب ثم حاول مرة أخرى.",
                reply_markup=owner_keyboard(),
            )
        except Exception as exc:
            await query.edit_message_text(
                f"⚠️ تعذر تجهيز جلسة النقل.\nالسبب: {type(exc).__name__}: {exc}",
                reply_markup=owner_keyboard(),
            )
    elif data.startswith("owner:session_check:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        session_user_id = int(data.rsplit(":", 1)[1])
        try:
            client = await get_or_create_client(session_user_id)
            connected = client.is_connected()
            authorized = await client.is_user_authorized() if connected else False
            me = await client.get_me() if authorized else None
            active_jobs = [
                jid for jid, job in channel_transfers.items()
                if int(job.get("session_user_id", 0) or 0) == session_user_id
                and int(jid) in channel_transfer_tasks
                and not channel_transfer_tasks[int(jid)].done()
            ]
            status = "🟢 متصلة ومسجلة" if connected and authorized else ("🟡 متصلة لكن غير مسجلة" if connected else "⚪ مفصولة")
            await query.edit_message_text(
                "🔐 *تفاصيل الجلسة*\n\n"
                f"👤 الحساب: {account_display_name(session_user_id, me)}\n"
                f"🆔 آيدي Telegram: {getattr(me, 'id', 'غير معروف') if me else 'غير متاح'}\n"
                f"📡 الحالة: {status}\n"
                f"🔄 مهام النقل النشطة بهذه الجلسة: {len(active_jobs)}\n"
                f"💾 ملف الجلسة: user_{session_user_id}.session",
                parse_mode="Markdown",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔄 تحديث", callback_data=f"owner:session_check:{session_user_id}")],
                    [InlineKeyboardButton("🔌 فصل الجلسة", callback_data=f"owner:session_disconnect:{session_user_id}")],
                    [InlineKeyboardButton("🗑️ حذف الجلسة", callback_data=f"owner:session_delete:{session_user_id}")],
                    [InlineKeyboardButton("⬅️ رجوع", callback_data=f"owner:dialogs:{session_user_id}")],
                ]),
            )
        except Exception as exc:
            await query.edit_message_text(
                f"⚠️ تعذر فحص الجلسة.\nالسبب: {type(exc).__name__}: {exc}",
                reply_markup=owner_keyboard(),
            )
    elif data.startswith("owner:session_disconnect:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        session_user_id = int(data.rsplit(":", 1)[1])
        # الفصل هنا لا يحذف ملف الجلسة ولا يسجل خروج حساب Telegram.
        client = clients.get(session_user_id)
        try:
            if client and client.is_connected():
                await client.disconnect()
            await query.answer("تم فصل الاتصال.", show_alert=False)
            await query.edit_message_text(
                "🔌 تم فصل الجلسة مؤقتاً.\n\n"
                "ملف الجلسة محفوظ، ويمكن إعادة الاتصال عند الحاجة.",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🔄 فحص الحالة", callback_data=f"owner:session_check:{session_user_id}")],
                    [InlineKeyboardButton("⬅️ رجوع", callback_data=f"owner:dialogs:{session_user_id}")],
                ]),
            )
        except Exception as exc:
            await query.edit_message_text(f"⚠️ تعذر فصل الجلسة: {type(exc).__name__}: {exc}", reply_markup=owner_keyboard())
    elif data.startswith("owner:session_delete:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        session_user_id = int(data.rsplit(":", 1)[1])
        if session_user_id == OWNER_ID:
            await query.answer("لا تحذف جلسة المالك من هذا الزر. استخدم تسجيل الخروج الصريح.", show_alert=True)
            return
        # أوقف مهام النقل المرتبطة بالجلسة قبل حذفها.
        for jid, job in list(channel_transfers.items()):
            if int(job.get("session_user_id", 0) or 0) == session_user_id:
                task = channel_transfer_tasks.get(int(jid))
                if task and not task.done():
                    task.cancel()
        await discard_client_session(session_user_id, remove_file=True)
        await query.edit_message_text(
            f"🗑️ تم حذف جلسة المستخدم {session_user_id} وملفها من الخادم، وإيقاف مهام النقل المرتبطة بها.",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("💬 استعراض الجلسات", callback_data="owner:sessions")],
                [InlineKeyboardButton("⬅️ لوحة الإدارة", callback_data="admin:home")],
            ]),
        )
    elif data.startswith("owner:text:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            _, _, session_raw, chat_raw, page_raw, message_raw = data.split(":", 5)
            session_user_id = int(session_raw)
            chat_id = int(chat_raw)
            page = int(page_raw)
            message_id = int(message_raw)
            client = await get_or_create_client(session_user_id)
            msg = await client.get_messages(chat_id, ids=message_id)
            if not msg:
                raise ValueError("لم يتم العثور على الرسالة")
            text = (msg.message or msg.text or "").replace("\\r", "").replace("\\n", "\n").strip()
            if not text:
                text = "لا يوجد نص في هذه الرسالة."
            await query.edit_message_text(
                f"📝 الرسالة #{message_id}\n\n{text[:3800]}",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("⬅️ رجوع إلى الصفحة", callback_data=f"owner:chat:{session_user_id}:{chat_id}:{page}")],
                ]),
            )
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text("⚠️ الجلسة غير صالحة لدى Telegram. لم يتم حذفها تلقائياً. أعد تسجيل الحساب من جديد أو احذفها يدوياً.", reply_markup=owner_keyboard())
        except Exception as exc:
            logger.exception("تعذر عرض نص الرسالة %s", data)
            await query.answer("تعذر عرض الرسالة", show_alert=True)
            await query.edit_message_text(
                f"⚠️ تعذر عرض الرسالة.\nالسبب: {type(exc).__name__}: {exc}",
                reply_markup=owner_keyboard(),
            )
    elif data.startswith("owner:media:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            _, _, session_raw, chat_raw, page_raw, message_raw = data.split(":", 5)
            session_user_id = int(session_raw)
            chat_id = int(chat_raw)
            page = int(page_raw)
            message_id = int(message_raw)
            client = await get_or_create_client(session_user_id)
            selected = None
            async for dialog in client.iter_dialogs(limit=200):
                if int(getattr(dialog.entity, "id", 0)) == chat_id:
                    selected = dialog.entity
                    break
            if selected is None:
                raise ValueError("لم يتم العثور على الحوار")
            msg = await client.get_messages(selected, ids=message_id)
            if not msg or not getattr(msg, "media", None):
                raise ValueError("الرسالة لا تحتوي على وسائط قابلة للإرسال")
            await query.answer("⏳ جارٍ إرسال الوسائط إلى محادثتك...", show_alert=False)
            file_obj = getattr(msg, "file", None)
            file_name = getattr(file_obj, "name", None) or "بدون اسم محفوظ"
            file_size = getattr(file_obj, "size", None)
            size_label = format_size(int(file_size)) if file_size else "الحجم غير متاح"
            caption = (
                f"📎 من الرسالة #{message_id}\n"
                f"🗂️ النوع: {message_kind_label(msg)}\n"
                f"📄 الاسم: {file_name}\n"
                f"📦 الحجم: {size_label}"
            )
            with tempfile.TemporaryDirectory(prefix=f"session_browser_{session_user_id}_") as temp_dir:
                downloaded_path = await asyncio.wait_for(
                    client.download_media(msg, file=temp_dir),
                    timeout=DOWNLOAD_TIMEOUT_SECONDS,
                )
                if not downloaded_path or not Path(str(downloaded_path)).exists():
                    raise RuntimeError("تعذر تنزيل الوسائط إلى الخادم")
                downloaded_path = str(downloaded_path)
                # الإرسال يتم عبر Bot API، وليس عبر حساب Telegram المسجّل.
                # نمرر ملفاً مفتوحاً إلى InputFile لتفادي RuntimeError في بعض إصدارات PTB.
                with open(downloaded_path, "rb") as upload_file:
                    upload = InputFile(upload_file, filename=Path(downloaded_path).name)
                    if getattr(msg, "photo", None):
                        await context.bot.send_photo(chat_id=OWNER_ID, photo=upload, caption=caption)
                    elif getattr(msg, "video", None):
                        await context.bot.send_video(chat_id=OWNER_ID, video=upload, caption=caption, supports_streaming=True)
                    elif getattr(msg, "animation", None):
                        await context.bot.send_animation(chat_id=OWNER_ID, animation=upload, caption=caption)
                    elif getattr(msg, "audio", None):
                        await context.bot.send_audio(chat_id=OWNER_ID, audio=upload, caption=caption)
                    elif getattr(msg, "voice", None):
                        await context.bot.send_voice(chat_id=OWNER_ID, voice=upload, caption=caption)
                    elif getattr(msg, "video_note", None):
                        await context.bot.send_video_note(chat_id=OWNER_ID, video_note=upload)
                    else:
                        await context.bot.send_document(chat_id=OWNER_ID, document=upload, caption=caption)
            await query.edit_message_text(
                "✅ تم تنزيل الوسائط على الخادم وإرسالها بواسطة البوت إلى محادثتك.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع إلى الحوار", callback_data=f"owner:chat:{session_user_id}:{chat_id}:{page}")]]),
            )
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text("⚠️ الجلسة غير صالحة لدى Telegram. لم يتم حذفها تلقائياً. أعد تسجيل الحساب من جديد أو احذفها يدوياً.", reply_markup=owner_keyboard())
        except Exception as exc:
            logger.exception("تعذر إرسال الوسائط %s", data)
            await query.answer("تعذر إرسال الوسائط", show_alert=True)
            await query.edit_message_text(f"⚠️ تعذر إرسال الوسائط.\nالسبب: {type(exc).__name__}: {exc}", reply_markup=owner_keyboard())
    elif data.startswith("owner:chat:"):
        if not owner_only(update):
            await query.answer("هذا القسم مخصص للمالك فقط.", show_alert=True)
            return
        try:
            parts = data.split(":")
            session_user_id = int(parts[2])
            chat_id = int(parts[3])
            page = max(1, int(parts[4])) if len(parts) > 4 else 1
            page_size = 8
            client = await get_or_create_client(session_user_id)
            selected = None
            async for dialog in client.iter_dialogs(limit=200):
                if int(getattr(dialog.entity, "id", 0)) == chat_id:
                    selected = dialog.entity
                    title = dialog.name or "بدون اسم"
                    break
            if selected is None:
                raise ValueError("لم يتم العثور على الحوار في الجلسة")
            total_probe = await client.get_messages(selected, limit=0)
            total = int(getattr(total_probe, "total", 0) or 0)
            pages = max(1, (total + page_size - 1) // page_size)
            page = min(page, pages)
            messages = await client.get_messages(selected, limit=page_size, add_offset=(page - 1) * page_size)
            session_me = await client.get_me()
            session_name = account_display_name(session_user_id, session_me)
            lines = [
                f"💬 الحوار: {title}",
                f"👤 الحساب: {session_name}",
                f"📄 الصفحة: {page} من {pages}  |  إجمالي الرسائل: {total}",
                "────────────────",
            ]
            rows = []
            for msg in reversed(messages):
                kind = message_kind_label(msg)
                raw_body = msg.text or ""
                body = " ".join(raw_body.replace("\\r", "").replace("\\n", " ").split())[:140]
                file_obj = getattr(msg, "file", None)
                file_name = getattr(file_obj, "name", None) if file_obj else None
                file_size = getattr(file_obj, "size", None) if file_obj else None
                if getattr(msg, "media", None):
                    body = (
                        f"📄 {file_name or 'بدون اسم محفوظ'}\n"
                        f"📦 {format_size(int(file_size)) if file_size else 'الحجم غير متاح'}"
                    )
                elif not body:
                    body = "رسالة بدون نص"
                lines.append(f"#{msg.id} • {kind}\n{body}")
                if getattr(msg, "media", None):
                    rows.append([InlineKeyboardButton(
                        f"📥 تنزيل #{msg.id} ({kind})",
                        callback_data=f"owner:media:{session_user_id}:{chat_id}:{page}:{msg.id}",
                    )])
                elif raw_body.strip():
                    rows.append([InlineKeyboardButton(
                        f"📝 عرض نص #{msg.id}",
                        callback_data=f"owner:text:{session_user_id}:{chat_id}:{page}:{msg.id}",
                    )])
            navigation = []
            if page > 1:
                navigation.append(InlineKeyboardButton("⬅️ السابق", callback_data=f"owner:chat:{session_user_id}:{chat_id}:{page - 1}"))
            if page < pages:
                navigation.append(InlineKeyboardButton("التالي ➡️", callback_data=f"owner:chat:{session_user_id}:{chat_id}:{page + 1}"))
            if navigation:
                rows.append(navigation)
            rows.append([InlineKeyboardButton("⬅️ رجوع إلى الحوارات", callback_data=f"owner:dialogs:{session_user_id}")])
            await query.edit_message_text("\n".join(lines)[:3900], reply_markup=InlineKeyboardMarkup(rows))
        except AuthKeyUnregisteredError:
            clients.pop(session_user_id, None)
            await query.edit_message_text("⚠️ الجلسة غير صالحة لدى Telegram. لم يتم حذفها تلقائياً. أعد تسجيل الحساب من جديد أو احذفها يدوياً.", reply_markup=owner_keyboard())
        except Exception as exc:
            logger.exception("تعذر عرض صفحة الحوار %s", data)
            await query.edit_message_text(f"⚠️ تعذر عرض الحوار.\nالسبب: {type(exc).__name__}: {exc}", reply_markup=owner_keyboard())
    elif data == "user:language":
        uid = update.effective_user.id
        current = user_language(uid)
        new_language = "en" if current == "ar" else "ar"
        set_user_language(uid, new_language)
        await query.edit_message_text(
            localized(uid,
                "✅ تم تغيير اللغة إلى العربية.",
                "✅ Language changed to English."
            ),
            reply_markup=user_keyboard(uid),
        )
    elif data == "user:login":
        uid = update.effective_user.id
        # السماح للمالك والمستخدم بإظهار مسار تسجيل الدخول مباشرة من الزر،
        # بدلاً من الاعتماد على /start فقط.
        states[uid] = {"step": "phone"}
        await query.edit_message_text(
            "🔐 *تسجيل الدخول إلى Telegram*\n\n"
            "الخطوة ١ من ٣: أرسل رقم هاتف الحساب بالصيغة الدولية.\n"
            "مثال: `+249XXXXXXXXX`\n\n"
            "📌 سيُرسل Telegram رمز التحقق إلى تطبيق Telegram أو SMS.\n"
            "🔒 لا ترسل كلمة المرور أو الرمز لأي شخص؛ أرسله هنا فقط للبوت.\n"
            "↩️ يمكنك الإلغاء في أي وقت عبر /cancel.",
            parse_mode="Markdown",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("❌ إلغاء", callback_data="user:cancel")]
            ]),
        )
    elif data == "user:help":
        uid = update.effective_user.id
        help_ar = (
            "📖 طريقة الاستخدام\n\n"
            "1️⃣ القنوات العامة: انسخ رابط المنشور العام مثل:\n"
            "https://t.me/channel_name/123\n"
            "ثم أرسله هنا. سيحاول البوت تنزيله بدون تسجيل دخول.\n\n"
            "2️⃣ القنوات الخاصة أو المحتوى المقيد: سجّل حساب Telegram أولاً من زر «تسجيل الدخول»، ثم أرسل الرابط.\n\n"
            "3️⃣ عند التسجيل، اكتب رقم الهاتف بالصيغة الدولية، ثم أرسل رمز التحقق مع مسافات بين الأرقام، مثل: 1 2 3 4 5.\n\n"
            "4️⃣ إذا كان التحقق بخطوتين مفعلاً، أرسل كلمة مرور Telegram.\n\n"
            "5️⃣ بعد نجاح التنزيل، يرسل البوت الملف داخل هذه المحادثة.\n\n"
            "🎁 الحصة اليومية: 5 تنزيلات. كل إحالة ناجحة لمستخدم جديد تضيف 5 تنزيلات.\n"
            "⚠️ إذا كان الرابط غير صالح أو المنشور محمياً من Telegram، سيخبرك البوت بسبب الفشل.\n"
            "🔒 لا ترسل رمز التحقق أو كلمة المرور لأي شخص."
        )
        help_en = (
            "📖 How to use the bot\n\n"
            "1️⃣ Public channels: copy a public post link, for example:\n"
            "https://t.me/channel_name/123\n"
            "and send it here. The bot will try to download it without login.\n\n"
            "2️⃣ Private channels or restricted content: log in to your Telegram account using «Log in», then send the post link.\n\n"
            "3️⃣ During login, enter your phone number in international format, then send the verification code with spaces, for example: 1 2 3 4 5.\n\n"
            "4️⃣ If two-step verification is enabled, send your Telegram password.\n\n"
            "5️⃣ After a successful download, the bot sends the file in this chat.\n\n"
            "🎁 Daily quota: 5 downloads. Each successful referral of a new user adds 5 downloads.\n"
            "⚠️ If the link is invalid or Telegram protects the post, the bot will explain the failure.\n"
            "🔒 Never share your verification code or password."
        )
        await query.edit_message_text(
            localized(uid, help_ar, help_en),
            reply_markup=user_keyboard(uid),
        )
    elif data == "user:account":
        uid = update.effective_user.id
        connected = await is_ready(uid)
        quota = quota_snapshot(uid)
        invite_link = f"https://t.me/{(await context.bot.get_me()).username}?start=ref_{uid}"
        await query.edit_message_text(
            f"🔐 حالة الحساب: {'متصل ✅' if connected else 'غير متصل ❌'}\n\n"
            f"📊 المتبقي الآن: {quota['total_remaining']} مقطع\n"
            f"🗓️ المتبقي من الحصة اليومية: {quota['daily_remaining']}\n"
            f"🎁 الرصيد الإضافي: {quota['bonus_credits']}\n"
            f"👥 الإحالات المقبولة: {quota['referral_count']}\n\n"
            f"🔗 رابط دعوتك:\n{invite_link}\n\n"
            "كل مستخدم جديد يبدأ من هذا الرابط يمنحك ٥ مقاطع إضافية.",
            reply_markup=user_keyboard(uid),
        )
    elif data == "user:cancel":
        states.pop(update.effective_user.id, None)
        await query.edit_message_text("❌ أُلغيت العملية.", reply_markup=user_keyboard(update.effective_user.id))
    elif data == "user:disconnect":
        uid = update.effective_user.id
        client = clients.get(uid)
        try:
            if client and client.is_connected():
                await client.disconnect()
        except Exception:
            logger.exception("تعذر فصل اتصال المستخدم %s", uid)
        states.pop(uid, None)
        await query.edit_message_text(
            "🔌 تم فصل الاتصال مؤقتاً.\n\n"
            "بقيت جلسة Telegram محفوظة، ويمكنك العودة دون إدخال الرقم من جديد.",
            reply_markup=user_keyboard(uid),
        )
    elif data == "user:logout":
        uid = update.effective_user.id
        client = clients.get(uid)
        try:
            if client and await client.is_user_authorized():
                await client.log_out()
        except Exception:
            logger.exception("تعذر تسجيل خروج المستخدم %s", uid)
        states.pop(uid, None)
        await discard_client_session(uid, remove_file=True)
        await query.edit_message_text("✅ تم حذف جلسة الحساب وتسجيل الخروج نهائياً. عند الاستخدام القادم سيُطلب الرقم من جديد.")
    elif data == "transfer:add":
        uid = update.effective_user.id
        if not can_use_channel_transfer(uid):
            await query.answer("ليس لديك صلاحية نقل القنوات.", show_alert=True)
            return
        # أي مستخدم ممنوح له النقل يستخدم حساب Telegram الخاص به تلقائياً.
        # المالك أيضاً يبدأ من جلسته الخاصة؛ اختيار جلسة أخرى يتم من استعراض الجلسات.
        try:
            client, me, transfer_session_id = await prepare_transfer_session(uid)
        except AuthKeyUnregisteredError:
            await query.edit_message_text(
                "⚠️ جلسة حساب النقل غير صالحة لدى Telegram.\n\n"
                "لم يتم حذف ملف الجلسة. أعد تسجيل دخول الحساب من زر تسجيل الدخول ثم حاول مرة أخرى.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data=transfer_back_callback(uid))]]),
            )
            return
        except Exception as exc:
            await query.edit_message_text(
                f"⚠️ لا يمكن بدء نقل القنوات من هذه الجلسة.\n\n{exc}",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data=transfer_back_callback(uid))]]),
            )
            return
        states[uid] = {
            "step": "transfer_source",
            "transfer_session_id": transfer_session_id,
            "transfer_account_id": int(getattr(me, "id", 0) or 0),
        }
        await query.edit_message_text(
            "➕ إضافة نقل قنوات\n\n"
            f"👤 حساب النقل: {account_display_name(transfer_session_id, me)}\n"
            f"🆔 آيدي الحساب: {getattr(me, 'id', 'غير معروف')}\n\n"
            "أرسل قناة المصدر بصيغة @username أو رابط القناة أو المعرّف الرقمي.\n"
            "للإلغاء استخدم /cancel.",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data=transfer_back_callback(uid))]]),
        )
    elif data == "transfer:delete":
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
        if not channel_transfers:
            await query.edit_message_text("لا توجد مهام لحذفها.", reply_markup=transfer_keyboard(transfer_back_callback(update.effective_user.id)))
        else:
            states[update.effective_user.id] = {"step": "transfer_delete"}
            await query.edit_message_text("🗑️ أرسل رقم المهمة التي تريد حذفها.\nللإلغاء استخدم /cancel.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ رجوع", callback_data=transfer_back_callback(update.effective_user.id))]]))
    elif data == "transfer:list":
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
        visible_jobs = {k: v for k, v in channel_transfers.items() if transfer_job_visible_to(update.effective_user.id, v)}
        text = "📋 القائمة فارغة." if not visible_jobs else "📋 قائمة نقل القنوات:\n\n" + "\n".join(
            f"{k}. {v['source']} ➜ {v['target']} | جلسة: {v.get('session_user_id', OWNER_ID)} | "
            f"{v.get('status')} | آخر رسالة: {v.get('last_message_id', 0)}"
            for k, v in visible_jobs.items()
        )
        await query.edit_message_text(text, reply_markup=transfer_keyboard(transfer_back_callback(update.effective_user.id)))
    elif data == "transfer:start_all":
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
        started = []
        for job_id, job in channel_transfers.items():
            if not transfer_job_visible_to(update.effective_user.id, job):
                continue
            if int(job_id) not in channel_transfer_tasks or channel_transfer_tasks[int(job_id)].done():
                channel_transfer_tasks[int(job_id)] = asyncio.create_task(start_transfer_job(job_id, context))
                started.append(str(job_id))
        await query.edit_message_text("▶️ بدأ النقل: " + (", ".join(started) if started else "لا توجد مهمة جديدة"), reply_markup=transfer_keyboard(transfer_back_callback(update.effective_user.id)))
    elif data == "transfer:stop_all":
        if not can_use_channel_transfer(update.effective_user.id):
            await query.answer("هذا القسم يفتح بعد دعوة خمسة أصدقاء جدد.", show_alert=True)
            return
        for task in list(channel_transfer_tasks.values()):
            if not task.done():
                task.cancel()
        await query.edit_message_text("⏹️ تم طلب إيقاف عمليات النقل.", reply_markup=transfer_keyboard(transfer_back_callback(update.effective_user.id)))


async def process_link(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int, text: str) -> None:
    async with media_semaphore:
        return await _process_link_inner(update, context, user_id, text)


async def _process_link_inner(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int, text: str) -> None:
    parsed = parse_message_link(text)
    if not parsed:
        await update.message.reply_text("أرسل رابط منشور Telegram صالحاً.")
        return False

    entity, message_id = parsed
    status = await update.message.reply_text(localized(user_id, "⏳ بدأ التنزيل\n[□□□□□□□□□□] 0%\n📦 تم تحميل: 0 ميغابايت", "⏳ Download started\n[□□□□□□□□□□] 0%\n📦 Downloaded: 0 MB"))
    bot_sent_message = None
    public_mode = isinstance(entity, str)

    # المسار الجذري للرابط العام: جرّب Bot API أولاً. هذا لا يحتاج
    # جلسة Telethon، لكنه ينجح فقط إذا كان البوت يملك وصولاً فعلياً للمنشور.
    if public_mode:
        try:
            bot_sent_message = await context.bot.copy_message(
                chat_id=user_id,
                from_chat_id=entity,
                message_id=message_id,
            )
            await status.edit_text(localized(
                user_id,
                "✅ تم إرسال المنشور العام مباشرة عبر Telegram.",
                "✅ The public post was copied directly through Telegram.",
            ))
            await asyncio.sleep(DELETE_AFTER_SECONDS)
            if status is not None:
                await context.bot.delete_message(chat_id=user_id, message_id=status.message_id)
            return True
        except Exception:
            logger.info(
                "Bot API لا يستطيع الوصول إلى المنشور العام %s/%s؛ سيتم التحقق من جلسة المستخدم",
                entity,
                message_id,
                exc_info=True,
            )

    # إذا لم يملك Bot API وصولاً مباشراً، فلا يوجد عميل مجهول مضمون.
    # نستخدم فقط جلسة المستخدم المصادق عليها، وإلا نرفض بوضوح.
    if public_mode:
        if not await is_ready(user_id):
            await status.edit_text(localized(
                user_id,
                "⚠️ القناة عامة، لكن Telegram لم يمنح البوت وصولاً مباشراً لهذا المنشور. سجّل الدخول بحساب مصرح له ثم أرسل الرابط مرة أخرى.",
                "⚠️ The channel is public, but Telegram did not grant the bot direct access to this post. Log in with an authorized account and send the link again.",
            ))
            return False
        client = await get_or_create_client(user_id)
    else:
        client = await get_or_create_client(user_id)

    async def delete_message_by_id(message_id: int, label: str) -> None:
        # الحذف مطلوب في هذا البوت دائماً؛ لا نعتمد على قيمة بيئية قديمة
        # عطّلت الحذف في نسخة الاستضافة.
        if not DELETE_SENT_MESSAGES:
            logger.warning(
                "DELETE_SENT_MESSAGES=%s، لكن سيستمر الحذف لأن التنظيف إلزامي للمستخدم %s",
                DELETE_SENT_MESSAGES,
                user_id,
            )
        try:
            await context.bot.delete_message(chat_id=user_id, message_id=message_id)
            logger.info("تم حذف %s للمستخدم %s، message_id=%s", label, user_id, message_id)
        except Exception:
            logger.exception("تعذر حذف %s للمستخدم %s، message_id=%s", label, user_id, message_id)

    async def cleanup_messages() -> None:
        # نحذف رسالة الفيديو ورسالة الحالة في شات المستخدم فقط.
        # لا نستخدم أي معرّف لرسالة المستلم الثاني.
        if bot_sent_message is not None:
            await delete_message_by_id(bot_sent_message.message_id, "نسخة الفيديو")
        if status is not None:
            await delete_message_by_id(status.message_id, "رسالة الحالة")

    try:
        try:
            source = await client.get_messages(entity, ids=message_id)
        except AuthKeyUnregisteredError:
            if not public_mode:
                raise
            logger.warning("مفتاح العميل العام غير مسجل؛ إعادة إنشائه وإعادة محاولة الرابط")
            await reset_public_client()
            client = await get_public_client()
            source = await client.get_messages(entity, ids=message_id)
        if not source or not source.media:
            raise ValueError("المنشور غير موجود أو لا يحتوي على وسائط قابلة للتنزيل.")

        with tempfile.TemporaryDirectory(prefix=f"telegram_{user_id}_") as temp_dir:
            operation_started = time.monotonic()
            progress_state = {"last_update": 0.0, "last_percent": -1}

            def download_progress(current: int, total: int) -> None:
                now = time.monotonic()
                if total <= 0:
                    return
                percent_float = min(100.0, current * 100.0 / total)
                percent = int(percent_float)
                # تحديث دوري، مع تحديث فوري عند اكتمال كل نسبة جديدة.
                if percent < 100 and now - progress_state["last_update"] < 2 and percent == progress_state["last_percent"]:
                    return
                progress_state["last_update"] = now
                progress_state["last_percent"] = percent
                bar_length = 20
                exact_filled = min(bar_length, percent_float * bar_length / 100.0)
                full_blocks = int(exact_filled)
                remainder = exact_filled - full_blocks
                partial_blocks = "▏▎▍▌▋▊▉"
                partial = partial_blocks[min(len(partial_blocks) - 1, int(remainder * len(partial_blocks)))] if full_blocks < bar_length and remainder > 0 else ""
                bar = "█" * full_blocks + partial + "░" * max(0, bar_length - full_blocks - (1 if partial else 0))
                downloaded_mb = current / (1024 ** 2)
                total_mb = total / (1024 ** 2)
                progress_text = (
                    f"⏳ جارٍ تنزيل الوسائط\n[{bar}] {percent_float:5.1f}%\n"
                    f"📦 تم تحميل: {downloaded_mb:,.2f} من {total_mb:,.2f} ميغابايت"
                )

                async def update_progress_message() -> None:
                    try:
                        await status.edit_text(progress_text)
                    except Exception:
                        # قد تتزامن عدة تحديثات أو يفرض Telegram حد التعديل؛ لا نوقف التنزيل.
                        logger.debug("تعذر تحديث رسالة تقدم التنزيل", exc_info=True)

                asyncio.create_task(update_progress_message())

            downloaded = await asyncio.wait_for(
                client.download_media(
                    source,
                    file=temp_dir,
                    progress_callback=download_progress,
                ),
                timeout=DOWNLOAD_TIMEOUT_SECONDS,
            )
            if not downloaded:
                raise ValueError("تعذر تنزيل الفيديو.")
            file_path = Path(downloaded)
            actual_size = file_path.stat().st_size
            if actual_size > MAX_FILE_SIZE_BYTES:
                raise ValueError(
                    f"حجم الفيديو {format_size(actual_size)} يتجاوز الحد المسموح {MAX_FILE_SIZE_MB} ميغابايت."
                )
            caption = source.message or ""
            logger.info(
                "اكتمل تنزيل %s للمستخدم %s خلال %.1f ثانية؛ يبدأ إرسال نسخة البوت",
                format_size(actual_size),
                user_id,
                time.monotonic() - operation_started,
            )
            await status.edit_text(localized(user_id, "📤 اكتمل التنزيل. جارٍ إرسال الوسائط إلى شاتك...", "📤 Download complete. Sending the media to your chat..."))

            # رفع واحد فقط عبر Bot API إلى شات صاحب الرابط.
            with file_path.open("rb") as media_for_bot:
                # اختيار طريقة Bot API المناسبة لكل أنواع الوسائط الشائعة.
                if source.photo:
                    send_method = context.bot.send_photo
                    send_kwargs = {"photo": media_for_bot}
                elif source.video:
                    send_method = context.bot.send_video
                    send_kwargs = {"video": media_for_bot, "supports_streaming": True}
                elif source.animation:
                    send_method = context.bot.send_animation
                    send_kwargs = {"animation": media_for_bot}
                elif source.audio:
                    send_method = context.bot.send_audio
                    send_kwargs = {"audio": media_for_bot}
                elif source.voice:
                    send_method = context.bot.send_voice
                    send_kwargs = {"voice": media_for_bot}
                elif source.video_note:
                    send_method = context.bot.send_video_note
                    send_kwargs = {"video_note": media_for_bot}
                elif source.sticker:
                    send_method = context.bot.send_sticker
                    send_kwargs = {"sticker": media_for_bot}
                else:
                    send_method = context.bot.send_document
                    send_kwargs = {"document": media_for_bot}
                send_parameters = {"chat_id": user_id, **send_kwargs}
                # الملصق والفيديو الدائري لا يقبلان caption في Bot API.
                if not source.sticker and not source.video_note:
                    send_parameters["caption"] = caption
                bot_sent_message = await asyncio.wait_for(
                    send_method(**send_parameters),
                    timeout=DOWNLOAD_TIMEOUT_SECONDS,
                )

            if public_mode:
                await status.edit_text(localized(user_id, "✅ تم تنزيل الوسائط العامة بدون تسجيل دخول وإرسالها من البوت إلى شاتك.", "✅ The public media was downloaded without login and sent by the bot to your chat."))
                await asyncio.sleep(DELETE_AFTER_SECONDS)
                await cleanup_messages()
                return True

            await status.edit_text("🔁 تم الإرسال إلى شاتك. جارٍ تحويل الرسالة إلى المستلم الثاني...")
            delivery_mode = "direct"

            # تحويل رسالة البوت عبر جلسة المستخدم، دون رفع الفيديو مرة ثانية.
            bot_info = await context.bot.get_me()
            bot_entity = await client.get_entity(bot_info.id)
            recipient_entity = await resolve_second_recipient(client)

            try:
                bot_message = await client.get_messages(
                    bot_entity,
                    ids=bot_sent_message.message_id,
                )
                if not bot_message:
                    raise ValueError("لم يتم العثور على رسالة الفيديو في شات البوت.")
                await asyncio.wait_for(
                    client.forward_messages(
                        entity=recipient_entity,
                        messages=bot_message,
                        from_peer=bot_entity,
                    ),
                    timeout=DOWNLOAD_TIMEOUT_SECONDS,
                )
                logger.info("تم التحويل المباشر للمستخدم %s إلى %s", user_id, SECOND_RECIPIENT)
            except Exception:
                logger.exception(
                    "فشل التحويل المباشر للمستخدم %s؛ ستتم تجربة رفع احتياطي واحد إلى المستلم %s",
                    user_id,
                    SECOND_RECIPIENT,
                )
                delivery_mode = "fallback"
                await status.edit_text("⏳ جارٍ إرسال النسخة الاحتياطية إلى المستلم الثاني...")
                with file_path.open("rb") as video_for_recipient:
                    await asyncio.wait_for(
                        client.send_file(
                            recipient_entity,
                            video_for_recipient,
                            caption=caption,
                            supports_streaming=True,
                        ),
                        timeout=DOWNLOAD_TIMEOUT_SECONDS,
                    )
                logger.info("اكتمل الرفع الاحتياطي للمستخدم %s إلى %s", user_id, SECOND_RECIPIENT)

            logger.info(
                "اكتمل الإرسال والتحويل للمستخدم %s خلال %.1f ثانية إجمالاً",
                user_id,
                time.monotonic() - operation_started,
            )
            if delivery_mode == "direct":
                final_text = (
                    "✅ تم الإرسال والتحويل المباشر بنجاح.\n\n"
                    "أُرسلت نسخة إلى شاتك، وحُوّلت الرسالة نفسها إلى المستلم الثاني دون رفع ثانٍ.\n"
                )
            else:
                final_text = (
                    "✅ تم الإرسال بنجاح عبر الرفع الاحتياطي.\n\n"
                    "تعذر التحويل المباشر، لذلك رُفعت نسخة واحدة إلى المستلم الثاني.\n"
                )
            await status.edit_text(
                final_text
                + "ستبقى نسخة المستلم الثاني، وتُحذف رسالة الفيديو ورسالة الحالة والملف المؤقت بعد "
                f"{DELETE_AFTER_SECONDS} ثانية."
            )
            await asyncio.sleep(DELETE_AFTER_SECONDS)
            await cleanup_messages()

        # التنظيف يتم داخل cleanup_messages حتى لا تبقى رسالة الحالة أو الفيديو.
        return True

    except AuthKeyUnregisteredError:
        logger.exception("مفتاح العميل العام غير مسجل أثناء معالجة الرابط للمستخدم %s", user_id)
        if public_mode:
            await reset_public_client()
            # بديل Bot API مشروع: ينجح فقط إذا كان البوت قادراً فعلياً
            # على الوصول إلى القناة العامة. لا يتجاوز الخصوصية أو الحماية.
            try:
                bot_sent_message = await context.bot.copy_message(
                    chat_id=user_id,
                    from_chat_id=entity,
                    message_id=message_id,
                )
                await status.edit_text(localized(
                    user_id,
                    "✅ تم إرسال المنشور العام مباشرة عبر Telegram.",
                    "✅ The public post was copied directly through Telegram.",
                ))
                await asyncio.sleep(DELETE_AFTER_SECONDS)
                await cleanup_messages()
                return True
            except Exception:
                logger.warning(
                    "تعذر استخدام Bot API للوصول إلى المنشور العام %s/%s",
                    entity,
                    message_id,
                    exc_info=True,
                )
        try:
            await status.edit_text(localized(
                user_id,
                "⚠️ لا يملك البوت وصولاً إلى هذا المنشور العام عبر Telegram. أضف البوت إلى القناة أو سجّل الدخول بحساب مصرح له ثم أرسل الرابط مرة أخرى.",
                "⚠️ Telegram did not grant the bot access to this public post. Add the bot to the channel or log in with an authorized account, then send the link again.",
            ))
        finally:
            await cleanup_messages()
        return False
    except asyncio.TimeoutError:
        logger.exception("انتهت مهلة معالجة الرابط للمستخدم %s", user_id)
        try:
            await status.edit_text(
                "⏱️ استغرقت العملية وقتاً أطول من المسموح وتم إيقافها.\n"
                "لم يتم الاحتفاظ بالملف المؤقت. جرّب فيديو أصغر."
            )
        finally:
            await cleanup_messages()
        return False
    except ValueError as exc:
        try:
            await status.edit_text(f"⚠️ {exc}")
        finally:
            await cleanup_messages()
        return False
    except Exception:
        logger.exception("فشلت معالجة رابط للمستخدم %s", user_id)
        try:
            await status.edit_text(
                "❌ تعذر تنفيذ العملية. تأكد من صلاحية الرابط وحجم الفيديو ثم حاول مرة أخرى."
            )
        finally:
            await cleanup_messages()
        return False
    finally:
        if public_mode and client is not None:
            try:
                if client.is_connected():
                    await client.disconnect()
            except Exception:
                logger.debug("تعذر فصل عميل الرابط العام بعد انتهاء العملية", exc_info=True)



# حالة خادم الويب على مستوى الملف حتى يمكن لـ post_init تشغيله فعلياً.
web_server = None
web_server_task = None

async def post_init(application: Application) -> None:
    try:
        bot_info = await application.bot.get_me()
        logger.info("البوت المتصل فعلياً: @%s (id=%s)، المالك: %s", bot_info.username, bot_info.id, OWNER_ID)
    except Exception:
        logger.exception("تعذر قراءة هوية البوت عند بدء التشغيل")
    logger.info("البوت يعمل، المالك: %s", OWNER_ID)
    # مهام asyncio لا تبقى بعد إعادة تشغيل الخدمة، لكن حالة المهمة محفوظة في JSON.
    # نزيل الحالات المؤقتة القديمة فقط، ونحافظ على last_message_id للاستئناف.
    changed = False
    for job_id, job in channel_transfers.items():
        status = str(job.get("status", ""))
        if status.startswith(("يعمل", "جارٍ", "انتظار Telegram", "إعادة محاولة")):
            job["status"] = (
                "متوقف بعد إعادة التشغيل؛ اضغط بدء النقل للاستئناف من الرسالة "
                f"{int(job.get('last_message_id', 0)) + 1}"
            )
            job.pop("current_message_id", None)
            changed = True
    if changed:
        save_channel_transfers()

    # تشغيل واجهة الويب فعلياً عند بدء البوت.
    # مهم: لا نعتمد على دالة متداخلة داخل كتلة FastAPI، بل نشغّل Uvicorn
    # من post_init مباشرة حتى لا يحدث NameError.
    global web_server, web_server_task
    try:
        if FastAPI is None:
            raise RuntimeError("FastAPI/uvicorn غير مثبتين في بيئة التشغيل")
        config = uvicorn.Config(
            web_app,
            host=WEB_HOST,
            port=WEB_PORT,
            log_level="info",
            access_log=True,
        )
        web_server = uvicorn.Server(config)
        web_server_task = asyncio.create_task(web_server.serve())

        for _ in range(50):
            if web_server.started:
                logger.info("WEB_READY: http://%s:%s", WEB_HOST, WEB_PORT)
                logger.info("WEB_PUBLIC_URL: %s", WEB_PUBLIC_BASE_URL)
                break
            if web_server_task.done():
                exc = web_server_task.exception()
                if exc:
                    raise exc
                raise RuntimeError("Uvicorn توقف قبل بدء الاستماع")
            await asyncio.sleep(0.1)
        else:
            logger.warning("WEB_START_TIMEOUT: لم يؤكد Uvicorn بدء الاستماع خلال 5 ثوانٍ")
    except Exception:
        logger.exception("تعذر تشغيل واجهة الويب على 0.0.0.0:8080")


async def post_shutdown(application: Application) -> None:
    global web_server, web_server_task
    if web_server is not None:
        try:
            web_server.should_exit = True
        except Exception:
            pass
    for client in clients.values():
        if client.is_connected():
            await client.disconnect()


async def trace_update(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    message = getattr(update, "message", None)
    if message:
        logger.info(
            "تحديث وارد: update_id=%s user_id=%s chat_id=%s text=%r",
            getattr(update, "update_id", None),
            getattr(getattr(message, "from_user", None), "id", None),
            getattr(getattr(message, "chat", None), "id", None),
            getattr(message, "text", None),
        )
    else:
        logger.info("تحديث وارد غير نصي: update_id=%s", getattr(update, "update_id", None))


async def application_error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.exception("خطأ غير معالج في تحديث Telegram", exc_info=context.error)
    if isinstance(update, Update) and update.effective_chat:
        try:
            await context.bot.send_message(
                chat_id=update.effective_chat.id,
                text="⚠️ حدث خطأ مؤقت. تم تسجيل التفاصيل، حاول الضغط على الزر مرة أخرى.",
            )
        except Exception:
            logger.exception("تعذر إرسال رسالة الخطأ للمستخدم")


def main() -> None:
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .concurrent_updates(max(4, int(os.getenv("BOT_CONCURRENT_UPDATES", "32"))))
        .build()
    )
    # مجموعة تشخيصية قبل المعالجات العادية: لا تغيّر السلوك، وتؤكد وصول /start لهذه النسخة.
    app.add_handler(TypeHandler(Update, trace_update), group=-1)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("cancel", cancel))
    app.add_handler(CommandHandler("channels", channels_command))
    app.add_handler(CommandHandler("addchannel", add_channel_command))
    app.add_handler(CommandHandler("starttransfer", start_transfer_command))
    app.add_handler(CommandHandler("stoptransfer", stop_transfer_command))
    app.add_handler(CommandHandler("transferstatus", transfer_status_command))
    app.add_handler(CallbackQueryHandler(transfer_callback, pattern=r"^(?:transfer|admin|user|owner):"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))
    app.add_error_handler(application_error_handler)
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
async def owner_open_session_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_owner(uid):
        return
    try:
        sid = int(q.data.split(":")[-1])
    except Exception:
        return
    client = clients.get(sid)
    if not client:
        await q.edit_message_text("❌ الجلسة غير موجودة.")
        return
    try:
        me = await client.get_me()
        await q.edit_message_text(
            f"📱 جلسة الحساب\n\n"
            f"الاسم: {getattr(me, 'first_name', '') or ''} {getattr(me, 'last_name', '') or ''}\n"
            f"المعرف: @{getattr(me, 'username', '') or 'بدون'}\n"
            f"ID: {me.id}\n\n"
            "اختر ما تريد فتحه:",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("💬 المحادثات", callback_data=f"owner:chats:{sid}:0")],
                [InlineKeyboardButton("🔙 الجلسات", callback_data="owner:sessions")],
            ])
        )
    except Exception as e:
        await q.edit_message_text(f"❌ تعذر فتح الجلسة: {e}")

async def owner_chats_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_owner(uid):
        return
    parts = q.data.split(":")
    sid, page = int(parts[2]), int(parts[3])
    client = clients.get(sid)
    if not client:
        await q.edit_message_text("❌ الجلسة غير متاحة.")
        return
    try:
        dialogs = [d async for d in client.iter_dialogs(limit=12)]
        start = page * 6
        chunk = dialogs[start:start+6]
        if not chunk:
            await q.edit_message_text("لا توجد محادثات في هذه الصفحة.",
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 رجوع", callback_data=f"owner:open_session:{sid}")]]))
            return
        rows = []
        for d in chunk:
            title = (d.name or "بدون اسم")[:28]
            rows.append([InlineKeyboardButton(f"💬 {title}", callback_data=f"owner:chat:{sid}:{d.id}")])
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅️ السابق", callback_data=f"owner:chats:{sid}:{page-1}"))
        nav.append(InlineKeyboardButton("➡️ التالي", callback_data=f"owner:chats:{sid}:{page+1}"))
        rows.append(nav)
        rows.append([InlineKeyboardButton("🔙 الجلسة", callback_data=f"owner:open_session:{sid}")])
        await q.edit_message_text("💬 محادثات الحساب:", reply_markup=InlineKeyboardMarkup(rows))
    except Exception as e:
        await q.edit_message_text(f"❌ تعذر جلب المحادثات: {e}")

async def owner_chat_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    if not is_owner(uid):
        return
    parts = q.data.split(":")
    sid, chat_id = int(parts[2]), int(parts[3])
    client = clients.get(sid)
    if not client:
        await q.edit_message_text("❌ الجلسة غير متاحة.")
        return
    try:
        msgs = [m async for m in client.iter_messages(chat_id, limit=8)]
        lines = ["🗨️ آخر الرسائل:\n"]
        media_count = 0
        for msg in reversed(msgs):
            text_msg = (msg.text or "").replace("\n", " ")[:90]
            if msg.media:
                media_count += 1
                text_msg = ("🖼️/📎 " + text_msg).strip()
            if not text_msg:
                text_msg = "📎 وسائط"
            lines.append(f"• {text_msg}")
        lines.append(f"\n📎 وسائط في المعاينة: {media_count}")
        await q.edit_message_text(
            "\n".join(lines),
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔙 المحادثات", callback_data=f"owner:chats:{sid}:0")],
                [InlineKeyboardButton("📱 الجلسة", callback_data=f"owner:open_session:{sid}")],
            ])
        )
    except Exception as e:
        await q.edit_message_text(f"❌ تعذر فتح المحادثة: {e}")
