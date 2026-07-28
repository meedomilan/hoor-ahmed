import asyncio
import json
import logging
import os
import signal
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from urllib.parse import quote

import aiohttp
from aiohttp import web
from zoneinfo import ZoneInfo

BINANCE_REST = "https://fapi.binance.com"
BINANCE_WS = "wss://fstream.binance.com/stream?streams="
SAUDI_TZ = ZoneInfo("Asia/Riyadh")

TIMEFRAMES = tuple(
    tf.strip() for tf in os.getenv("TIMEFRAMES", "15m,1h,4h").split(",") if tf.strip()
)
HISTORY_LIMIT = int(os.getenv("HISTORY_LIMIT", "220"))
STREAMS_PER_SOCKET = int(os.getenv("STREAMS_PER_SOCKET", "160"))
REST_CONCURRENCY = int(os.getenv("REST_CONCURRENCY", "20"))
MIN_QUOTE_VOLUME = float(os.getenv("MIN_QUOTE_VOLUME", "0"))
SEND_STARTUP_TEST = os.getenv("SEND_STARTUP_TEST", "true").lower() == "true"
SEND_REAL_TEST_SIGNAL = os.getenv("SEND_REAL_TEST_SIGNAL", "true").lower() == "true"
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()

TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()
PORT = int(os.getenv("PORT", "8080"))

logging.basicConfig(
    level=getattr(logging, LOG_LEVEL, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(message)s",
)
log = logging.getLogger("AGP")

@dataclass
class Candle:
    open_time: int
    open: float
    high: float
    low: float
    close: float
    volume: float
    close_time: int
    closed: bool = False

@dataclass
class SignalResult:
    name: str
    side: str
    score: int
    reasons: List[str]

candles: Dict[Tuple[str, str], List[Candle]] = defaultdict(list)
dedup: set[Tuple[str, str, str, int]] = set()
session: Optional[aiohttp.ClientSession] = None
stop_event = asyncio.Event()
stats = {
    "symbols": 0,
    "streams": 0,
    "messages": 0,
    "ws_reconnects": 0,
    "last_event": None,
    "signals_detected": 0,
    "signals_skipped": 0,
}

def ema(values: List[float], period: int) -> List[float]:
    if not values:
        return []
    alpha = 2.0 / (period + 1.0)
    out = [values[0]]
    for value in values[1:]:
        out.append(alpha * value + (1.0 - alpha) * out[-1])
    return out

def sma(values: List[float], period: int) -> float:
    if len(values) < period:
        return sum(values) / max(len(values), 1)
    return sum(values[-period:]) / period

def rsi(values: List[float], period: int = 14) -> float:
    if len(values) <= period:
        return 50.0
    gains = []
    losses = []
    for i in range(len(values) - period, len(values)):
        delta = values[i] - values[i - 1]
        gains.append(max(delta, 0.0))
        losses.append(max(-delta, 0.0))
    avg_gain = sum(gains) / period
    avg_loss = sum(losses) / period
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return 100.0 - (100.0 / (1.0 + rs))

def atr(items: List[Candle], period: int = 14) -> float:
    if len(items) < 2:
        return 0.0
    trs = []
    start = max(1, len(items) - period)
    for i in range(start, len(items)):
        prev_close = items[i - 1].close
        c = items[i]
        trs.append(max(c.high - c.low, abs(c.high - prev_close), abs(c.low - prev_close)))
    return sum(trs) / max(len(trs), 1)

def macd_hist(values: List[float]) -> Tuple[float, float, float]:
    fast = ema(values, 12)
    slow = ema(values, 26)
    line = [a - b for a, b in zip(fast[-len(slow):], slow)]
    sig = ema(line, 9)
    hist = line[-1] - sig[-1]
    prev_hist = line[-2] - sig[-2] if len(line) > 1 else hist
    prev2_hist = line[-3] - sig[-3] if len(line) > 2 else prev_hist
    return hist, prev_hist, prev2_hist

def recent_fvg(items: List[Candle], bullish: bool, lookback: int = 20) -> bool:
    if len(items) < 3:
        return False
    start = max(2, len(items) - lookback)
    for i in range(start, len(items)):
        if bullish and items[i].low > items[i - 2].high:
            return True
        if not bullish and items[i].high < items[i - 2].low:
            return True
    return False

def recent_liquidity_sweep(items: List[Candle], bullish: bool, lookback: int = 12) -> bool:
    if len(items) < lookback + 2:
        return False
    c = items[-1]
    previous = items[-(lookback + 1):-1]
    if bullish:
        level = min(x.low for x in previous)
        return c.low < level and c.close > level
    level = max(x.high for x in previous)
    return c.high > level and c.close < level

def calculate_signal(items: List[Candle]) -> Optional[SignalResult]:
    if len(items) < 205:
        return None

    closes = [x.close for x in items]
    current = items[-1]
    previous = items[-2]
    current_atr = atr(items, 14)
    if current_atr <= 0:
        return None

    ma7 = ema(closes, 7)[-1]
    ma10 = ema(closes, 10)[-1]
    ma25 = ema(closes, 25)[-1]
    ma50 = ema(closes, 50)[-1]
    ma200 = ema(closes, 200)[-1]

    hist, prev_hist, prev2_hist = macd_hist(closes)
    current_rsi = rsi(closes, 14)
    avg_vol = sma([x.volume for x in items[:-1]], 20)
    vol_ratio = current.volume / avg_vol if avg_vol > 0 else 1.0

    candle_range = max(current.high - current.low, 1e-12)
    close_pos = max(0.0, min(1.0, (current.close - current.low) / candle_range))
    buy_pct = close_pos * 100.0
    sell_pct = 100.0 - buy_pct
    body_ratio = abs(current.close - current.open) / current_atr

    lookback = items[-11:-1]
    prev_high = max(x.high for x in lookback)
    prev_low = min(x.low for x in lookback)
    bull_break = current.close > prev_high and current.close > current.open
    bear_break = current.close < prev_low and current.close < current.open

    bull = 0.0
    bear = 0.0
    bull_reasons: List[str] = []
    bear_reasons: List[str] = []

    if current.close > current.open:
        bull += 8; bull_reasons.append("شمعة صاعدة")
    else:
        bear += 8; bear_reasons.append("شمعة هابطة")

    if close_pos >= 0.75:
        bull += 7; bull_reasons.append("إغلاق قوي قرب القمة")
    elif close_pos >= 0.60:
        bull += 4
    if close_pos <= 0.25:
        bear += 7; bear_reasons.append("إغلاق قوي قرب القاع")
    elif close_pos <= 0.40:
        bear += 4

    vol_points = 13 if vol_ratio >= 2.0 else 10 if vol_ratio >= 1.5 else 5 if vol_ratio >= 1.2 else 0
    if vol_points:
        bull += vol_points
        bear += vol_points
        bull_reasons.append("حجم تداول مرتفع")
        bear_reasons.append("حجم تداول مرتفع")

    body_points = 10 if body_ratio >= 1.0 else 7 if body_ratio >= 0.6 else 0
    if body_points:
        bull += body_points
        bear += body_points
        bull_reasons.append("جسم شمعة قوي")
        bear_reasons.append("جسم شمعة قوي")

    macd_line_up = hist > 0
    if macd_line_up:
        bull += 15; bull_reasons.append("MACD إيجابي")
    else:
        bear += 15; bear_reasons.append("MACD سلبي")
    if hist > prev_hist:
        bull += 5; bull_reasons.append("زخم MACD يتصاعد")
    if hist < prev_hist:
        bear += 5; bear_reasons.append("زخم MACD يهبط")

    for condition, points, reason in [
        (current.close > ma25, 5, "فوق EMA25"),
        (current.close > ma50, 6, "فوق EMA50"),
        (current.close > ma200, 7, "فوق EMA200"),
        (ma25 > ma50, 4, "ترتيب المتوسطات صاعد"),
        (ma50 > ma200, 5, "الاتجاه العام صاعد"),
    ]:
        if condition:
            bull += points
            if points >= 6: bull_reasons.append(reason)

    for condition, points, reason in [
        (current.close < ma25, 5, "تحت EMA25"),
        (current.close < ma50, 6, "تحت EMA50"),
        (current.close < ma200, 7, "تحت EMA200"),
        (ma25 < ma50, 4, "ترتيب المتوسطات هابط"),
        (ma50 < ma200, 5, "الاتجاه العام هابط"),
    ]:
        if condition:
            bear += points
            if points >= 6: bear_reasons.append(reason)

    if buy_pct >= 70:
        bull += 8; bull_reasons.append("ضغط شراء مرتفع")
    elif buy_pct >= 60:
        bull += 5
    elif buy_pct >= 55:
        bull += 3

    if sell_pct >= 70:
        bear += 8; bear_reasons.append("ضغط بيع مرتفع")
    elif sell_pct >= 60:
        bear += 5
    elif sell_pct >= 55:
        bear += 3

    if bull_break:
        bull += 7; bull_reasons.append("اختراق قمة قصيرة")
    if bear_break:
        bear += 7; bear_reasons.append("كسر قاع قصير")

    bull_pre = (
        current_rsi >= 32 and current_rsi <= 58 and current_rsi > rsi(closes[:-1], 14)
        and hist > prev_hist and prev_hist >= prev2_hist
        and current.close > ma7 and ma7 >= ma10
    )
    bear_pre = (
        current_rsi <= 68 and current_rsi >= 42 and current_rsi < rsi(closes[:-1], 14)
        and hist < prev_hist and prev_hist <= prev2_hist
        and current.close < ma7 and ma7 <= ma10
    )
    if bull_pre:
        bull += 10; bull_reasons.append("تجهيز مبكر RSI وMACD")
    if bear_pre:
        bear += 10; bear_reasons.append("تجهيز مبكر RSI وMACD")

    if recent_fvg(items, True):
        bull += 4; bull_reasons.append("Bullish FVG")
    if recent_fvg(items, False):
        bear += 4; bear_reasons.append("Bearish FVG")
    if recent_liquidity_sweep(items, True):
        bull += 6; bull_reasons.append("سحب سيولة بيعية")
    if recent_liquidity_sweep(items, False):
        bear += 6; bear_reasons.append("سحب سيولة شرائية")

    bull = min(100.0, bull)
    bear = min(100.0, bear)

    side = "BUY" if bull > bear else "SELL"
    raw_score = max(bull, bear)
    gap = abs(bull - bear)

    if raw_score < 42 or gap < 5:
        stats["signals_skipped"] += 1
        return None

    if gap >= 24 and raw_score >= 68:
        stage = "GOLD"
        score = min(100, 85 + int((gap - 24) * 0.35 + (raw_score - 68) * 0.25))
    elif gap >= 12 and raw_score >= 55:
        stage = "EARLY"
        score = min(84, 70 + int((gap - 12) * 0.45 + (raw_score - 55) * 0.20))
    else:
        stage = "PRE"
        score = min(69, 61 + int((gap - 5) * 0.55 + max(0.0, raw_score - 42) * 0.12))

    reasons = bull_reasons if side == "BUY" else bear_reasons
    reasons = list(dict.fromkeys(reasons))[:6]
    return SignalResult(f"{stage} {side}", side, score, reasons)

def tradingview_link(symbol: str) -> str:
    return f"https://www.tradingview.com/chart/?symbol=BINANCE:{quote(symbol)}.P"

def binance_link(symbol: str) -> str:
    return f"https://www.binance.com/en/futures/{quote(symbol)}"

def format_message(symbol: str, tf: str, candle: Candle, result: SignalResult) -> str:
    stage, side = result.name.split()
    if stage == "PRE":
        icon = "🔵" if side == "BUY" else "🔴"
        note = "📍 مرحلة الاستعداد"
    elif stage == "EARLY":
        icon = "🟢" if side == "BUY" else "🟠"
        note = "⚡ دخول مبكر"
    else:
        icon = "🟡" if side == "BUY" else "🔻"
        note = "🔥 تأكيد قوي"

    dt = datetime.now(SAUDI_TZ)
    reasons = "\n".join(f"• {r}" for r in result.reasons) or "• توافق شروط AGP"
    price = f"{candle.close:.10f}".rstrip("0").rstrip(".")
    return (
        f"{icon} <b>AGP PRIVATE — {result.name}</b>\n"
        f"💎 إشارة خاصة من محرك Ahmed Gold Pro\n\n"
        f"💰 العملة: <b>#{symbol}.P</b>\n"
        f"⏰ الفريم: <b>{tf}</b>\n"
        f"💵 السعر: <b>{price} USDT</b>\n"
        f"📊 القوة: <b>{result.score}%</b>\n\n"
        f"{note}\n\n"
        f"<b>أسباب الإشارة:</b>\n{reasons}\n\n"
        f"🕒 {dt:%d-%m-%Y %H:%M:%S} (السعودية)\n\n"
        f'🔗 <a href="{binance_link(symbol)}">Binance</a> | '
        f'<a href="{tradingview_link(symbol)}">TradingView</a>'
    )

async def telegram_send(text: str) -> None:
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        raise RuntimeError("TELEGRAM_BOT_TOKEN و TELEGRAM_CHAT_ID مطلوبان")
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
    }
    for attempt in range(4):
        try:
            assert session is not None
            async with session.post(url, json=payload, timeout=20) as resp:
                body = await resp.text()
                if resp.status == 200:
                    stats["messages"] += 1
                    return
                if resp.status == 429:
                    data = json.loads(body)
                    wait = int(data.get("parameters", {}).get("retry_after", 2))
                    await asyncio.sleep(wait)
                    continue
                raise RuntimeError(f"Telegram {resp.status}: {body[:300]}")
        except Exception:
            if attempt == 3:
                raise
            await asyncio.sleep(2 ** attempt)

async def fetch_symbols() -> List[str]:
    assert session is not None
    async with session.get(f"{BINANCE_REST}/fapi/v1/exchangeInfo", timeout=30) as resp:
        resp.raise_for_status()
        info = await resp.json()

    allowed = []
    for item in info["symbols"]:
        if (
            item.get("status") == "TRADING"
            and item.get("quoteAsset") == "USDT"
            and item.get("contractType") == "PERPETUAL"
        ):
            allowed.append(item["symbol"])

    if MIN_QUOTE_VOLUME > 0:
        async with session.get(f"{BINANCE_REST}/fapi/v1/ticker/24hr", timeout=30) as resp:
            resp.raise_for_status()
            tickers = await resp.json()
        volume_map = {x["symbol"]: float(x.get("quoteVolume", 0)) for x in tickers}
        allowed = [s for s in allowed if volume_map.get(s, 0) >= MIN_QUOTE_VOLUME]

    return sorted(allowed)

async def fetch_history(symbol: str, tf: str, sem: asyncio.Semaphore) -> None:
    params = {"symbol": symbol, "interval": tf, "limit": HISTORY_LIMIT}
    async with sem:
        for attempt in range(5):
            try:
                assert session is not None
                async with session.get(f"{BINANCE_REST}/fapi/v1/klines", params=params, timeout=30) as resp:
                    if resp.status == 429:
                        await asyncio.sleep(5 + attempt * 2)
                        continue
                    resp.raise_for_status()
                    rows = await resp.json()
                candles[(symbol, tf)] = [
                    Candle(
                        open_time=int(x[0]), open=float(x[1]), high=float(x[2]),
                        low=float(x[3]), close=float(x[4]), volume=float(x[5]),
                        close_time=int(x[6]), closed=True,
                    )
                    for x in rows
                ]
                return
            except Exception as exc:
                if attempt == 4:
                    log.error("فشل تحميل %s %s: %s", symbol, tf, exc)
                    return
                await asyncio.sleep(1 + attempt)

async def preload(symbols: List[str]) -> None:
    sem = asyncio.Semaphore(REST_CONCURRENCY)
    jobs = [fetch_history(s, tf, sem) for s in symbols for tf in TIMEFRAMES]
    total = len(jobs)
    log.info("تحميل التاريخ لـ %s مسار...", total)
    completed = 0
    for batch_start in range(0, total, 200):
        batch = jobs[batch_start:batch_start + 200]
        await asyncio.gather(*batch)
        completed += len(batch)
        log.info("تم تحميل %s/%s", completed, total)
        await asyncio.sleep(0.2)

def update_candle(symbol: str, tf: str, c: Candle) -> None:
    key = (symbol, tf)
    items = candles[key]
    if items and items[-1].open_time == c.open_time:
        items[-1] = c
    else:
        items.append(c)
    if len(items) > HISTORY_LIMIT:
        del items[:-HISTORY_LIMIT]

async def process_kline(data: dict) -> None:
    k = data["k"]
    symbol = data["s"]
    tf = k["i"]
    c = Candle(
        open_time=int(k["t"]),
        open=float(k["o"]),
        high=float(k["h"]),
        low=float(k["l"]),
        close=float(k["c"]),
        volume=float(k["v"]),
        close_time=int(k["T"]),
        closed=bool(k["x"]),
    )
    update_candle(symbol, tf, c)
    stats["last_event"] = datetime.now(SAUDI_TZ).isoformat()

    result = calculate_signal(candles[(symbol, tf)])
    if not result:
        return

    stats["signals_detected"] += 1
    key = (symbol, tf, result.name, c.open_time)
    if key in dedup:
        return
    dedup.add(key)

    if len(dedup) > 100_000:
        cutoff = c.open_time - 8 * 24 * 3600 * 1000
        old = [x for x in dedup if x[3] < cutoff]
        for x in old:
            dedup.discard(x)

    text = format_message(symbol, tf, c, result)
    try:
        await telegram_send(text)
        log.info("%s | %s | %s | %s%%", symbol, tf, result.name, result.score)
    except Exception as exc:
        log.exception("فشل إرسال Telegram: %s", exc)

async def initial_real_scan(symbols: List[str]) -> None:
    found = []
    for symbol in symbols:
        for tf in TIMEFRAMES:
            items = candles.get((symbol, tf), [])
            result = calculate_signal(items)
            if result and items:
                found.append((result.score, symbol, tf, items[-1], result))

    found.sort(key=lambda x: x[0], reverse=True)
    log.info("الفحص الأولي وجد %s إشارة حقيقية", len(found))

    for _, symbol, tf, candle, result in found[:20]:
        key = (symbol, tf, result.name, candle.open_time)
        if key in dedup:
            continue
        dedup.add(key)
        try:
            await telegram_send(format_message(symbol, tf, candle, result))
            stats["signals_detected"] += 1
            log.info("INITIAL | %s | %s | %s | %s%%", symbol, tf, result.name, result.score)
            await asyncio.sleep(0.35)
        except Exception as exc:
            log.exception("فشل إرسال إشارة الفحص الأولي: %s", exc)

async def websocket_worker(streams: List[str], worker_id: int) -> None:
    url = BINANCE_WS + "/".join(streams)
    while not stop_event.is_set():
        try:
            assert session is not None
            async with session.ws_connect(url, heartbeat=30, receive_timeout=90) as ws:
                log.info("WebSocket %s متصل (%s stream)", worker_id, len(streams))
                async for msg in ws:
                    if stop_event.is_set():
                        break
                    if msg.type == aiohttp.WSMsgType.TEXT:
                        payload = json.loads(msg.data)
                        data = payload.get("data", {})
                        if data.get("e") == "kline":
                            await process_kline(data)
                    elif msg.type in (aiohttp.WSMsgType.ERROR, aiohttp.WSMsgType.CLOSED):
                        break
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            stats["ws_reconnects"] += 1
            log.warning("WebSocket %s انقطع: %s — إعادة اتصال خلال 5 ثوان", worker_id, exc)
            await asyncio.sleep(5)

async def stats_logger() -> None:
    while not stop_event.is_set():
        await asyncio.sleep(300)
        log.info(
            "الحالة | إشارات مكتشفة: %s | مرسلة: %s | متجاهلة: %s | آخر حدث: %s",
            stats["signals_detected"], stats["messages"],
            stats["signals_skipped"], stats["last_event"]
        )

async def health(_: web.Request) -> web.Response:
    return web.json_response({"ok": True, **stats, "timeframes": TIMEFRAMES})

async def start_health_server() -> web.AppRunner:
    app = web.Application()
    app.router.add_get("/", health)
    app.router.add_get("/health", health)
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", PORT)
    await site.start()
    return runner

async def main() -> None:
    global session
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        raise SystemExit("ضع TELEGRAM_BOT_TOKEN و TELEGRAM_CHAT_ID في Variables")

    timeout = aiohttp.ClientTimeout(total=60)
    connector = aiohttp.TCPConnector(limit=100, ttl_dns_cache=300)
    session = aiohttp.ClientSession(timeout=timeout, connector=connector)
    health_runner = await start_health_server()

    try:
        symbols = await fetch_symbols()
        stats["symbols"] = len(symbols)
        log.info("عدد عقود USDT Perpetual: %s", len(symbols))

        if SEND_STARTUP_TEST:
            await telegram_send(
                "✅ <b>AGP Telegram Alerts يعمل الآن</b>\n\n"
                f"📊 العقود: <b>{len(symbols)}</b>\n"
                f"⏰ الفريمات: <b>{' — '.join(TIMEFRAMES)}</b>\n"
                "🔔 التنبيهات: PRE / EARLY / GOLD\n"
                "🕒 التوقيت: السعودية"
            )

        await preload(symbols)

        if SEND_REAL_TEST_SIGNAL and ("BTCUSDT", "15m") in candles and candles[("BTCUSDT", "15m")]:
            test_candle = candles[("BTCUSDT", "15m")][-1]
            test_result = SignalResult(
                name="PRE BUY",
                side="BUY",
                score=66,
                reasons=["اختبار اتصال المحرك", "بيانات Binance وصلت بنجاح"]
            )
            await telegram_send(
                "🧪 <b>اختبار إشارة حقيقية</b>\n\n" +
                format_message("BTCUSDT", "15m", test_candle, test_result)
            )

        await initial_real_scan(symbols)

        streams = [f"{s.lower()}@kline_{tf}" for s in symbols for tf in TIMEFRAMES]
        stats["streams"] = len(streams)
        shards = [
            streams[i:i + STREAMS_PER_SOCKET]
            for i in range(0, len(streams), STREAMS_PER_SOCKET)
        ]
        log.info("تشغيل %s WebSocket لعدد %s stream", len(shards), len(streams))
        tasks = [
            asyncio.create_task(websocket_worker(shard, i + 1))
            for i, shard in enumerate(shards)
        ]
        tasks.append(asyncio.create_task(stats_logger()))
        await stop_event.wait()
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
    finally:
        await health_runner.cleanup()
        if session:
            await session.close()

def request_stop() -> None:
    stop_event.set()

if __name__ == "__main__":
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(sig, request_stop)
        except NotImplementedError:
            pass
    try:
        loop.run_until_complete(main())
    finally:
        loop.close()
