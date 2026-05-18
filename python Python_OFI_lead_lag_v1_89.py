# Python_OFI_lead_lag_v1.89 TrailSL方向ガード追加・TRAIL_START=35/DIST=20に変更・エントリーブラックアウト0.5秒追加で多重エントリー根絶
import sys
import time
import math
import asyncio
import threading
import collections
import orjson
import MetaTrader5 as mt5
import websockets
import logging
from datetime import datetime, timezone

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')
if hasattr(sys.stderr, 'reconfigure'):
    sys.stderr.reconfigure(encoding='utf-8')

SYMBOL_MT5 = "XAUUSD"
SYMBOL_BINANCE = "xauusdt"
MAGIC_NUMBER = 100189
FIXED_LOT = 0.01

BASE_DEVIATION = 30
EXIT_DEVIATION = 50

SPREAD_FILTER_PT = 50
MAX_TICK_AGE_MS = 150
MAX_BINANCE_LATENCY_MS = 120
COOLDOWN = 1.0

CLOSE_RETRY_INTERVAL = 0.05
CLOSE_MAX_RETRIES = 20
CLOSE_TIMEOUT_SEC = 10.0

GAP_EMA_ALPHA = 0.08
MIN_DELTA_GAP_PT = 45.0

OFI_WINDOW_SIZE = 200
OFI_ACCUM_WINDOW = 20
Z_SCORE_THR = 2.0

SL_PT = 50.0
BE_TRIGGER_PT = 25.0
BE_PROFIT_PT = 5.0
TRAIL_START_PT = 35.0
TRAIL_DIST_PT = 20.0
SL_UPDATE_MIN_PT = 5.0

SLIP_FILTER_PT = 50.0
ENTRY_TICKET_RETRY = 10
ENTRY_TICKET_WAIT = 0.05

ENTRY_BLACKOUT_SEC = 0.5

WS_RECV_TIMEOUT = 20.0
WS_RECONNECT_DELAY = 2.0

MARKET_SESSIONS = {
    0: (110, 2355), 1: (110, 2355), 2: (110, 2355),
    3: (110, 2355), 4: (110, 2350), 5: None, 6: None,
}

logger = logging.getLogger("HFT_OFI")
logger.setLevel(logging.INFO)
logger.propagate = False
_formatter = logging.Formatter('%(asctime)s.%(msecs)03d[%(levelname)s] %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
_file_handler = logging.FileHandler('hft_ofi.log', encoding='utf-8')
_file_handler.setFormatter(_formatter)
_console_handler = logging.StreamHandler(sys.stdout)
_console_handler.setFormatter(_formatter)
logger.addHandler(_file_handler)
logger.addHandler(_console_handler)

def _is_market_open(server_timestamp: int) -> bool:
    dt = datetime.fromtimestamp(server_timestamp, tz=timezone.utc)
    session = MARKET_SESSIONS.get(dt.weekday())
    if not session:
        return False
    return session[0] <= (dt.hour * 100 + dt.minute) <= session[1]

def _build_entry_req(symbol, side, price, sl_price, filling, digits):
    return {
        "action": mt5.TRADE_ACTION_DEAL,
        "symbol": symbol,
        "volume": float(FIXED_LOT),
        "type": side,
        "price": round(price, digits),
        "sl": round(sl_price, digits),
        "deviation": BASE_DEVIATION,
        "magic": MAGIC_NUMBER,
        "type_filling": filling,
    }

def _build_close_req(symbol, ticket, volume, side, price, filling, digits, dev):
    return {
        "action": mt5.TRADE_ACTION_DEAL,
        "position": ticket,
        "symbol": symbol,
        "volume": float(volume),
        "type": side,
        "price": round(price, digits),
        "deviation": dev,
        "magic": MAGIC_NUMBER,
        "type_filling": filling,
    }

class MT5TickFeed:
    def __init__(self, symbol):
        self.symbol = symbol
        self.latest_tick = None
        self.recv_perf = 0.0
        self.lock = threading.Lock()
        self.running = False

    def start(self):
        self.running = True
        threading.Thread(target=self._update_loop, daemon=True).start()

    def get(self):
        with self.lock:
            return self.latest_tick, self.recv_perf

    def _update_loop(self):
        p_t, p_b = 0, 0.0
        while self.running:
            t = mt5.symbol_info_tick(self.symbol)
            if t and (t.time_msc != p_t or t.bid != p_b):
                now = time.perf_counter()
                with self.lock:
                    self.latest_tick, self.recv_perf = t, now
                p_t, p_b = t.time_msc, t.bid
            time.sleep(0.0001)

class TradeState:
    def __init__(self):
        self.lock = threading.Lock()
        self.is_ordering = False
        self.is_closing = False
        self.gap_ema = None
        self.last_b_etime = 0.0
        self.peak_price = 0.0
        self.peak_unrealized_pt = 0.0
        self.last_close_perf = -COOLDOWN
        self.last_entry_perf = -ENTRY_BLACKOUT_SEC
        self.entry_perf = 0.0
        self.trail_active = False
        self.be_active = False
        self.last_sl_price = 0.0
        self.entry_count = 0
        self.explicitly_closed_tickets = set()

class MarketMicrostructureState:
    def __init__(self):
        self.prev_bb = (0.0, 0.0)
        self.prev_ba = (0.0, 0.0)
        self.event_time = 0.0
        self.micro_price = 0.0
        self.raw_ofi_buf = collections.deque(maxlen=OFI_ACCUM_WINDOW)
        self.ofi_history = collections.deque(maxlen=OFI_WINDOW_SIZE)
        self.initialized = False
        self.lock = threading.Lock()

    def update_depth(self, bids, asks, etime):
        with self.lock:
            if not bids or not asks:
                return
            bb_p, bb_v = float(bids[0][0]), float(bids[0][1])
            ba_p, ba_v = float(asks[0][0]), float(asks[0][1])
            self.micro_price = ((bb_p * ba_v + ba_p * bb_v) / (bb_v + ba_v)) if (bb_v + ba_v) > 0 else (bb_p + ba_p) / 2.0

            if not self.initialized:
                self.prev_bb, self.prev_ba = (bb_p, bb_v), (ba_p, ba_v)
                self.event_time, self.initialized = etime, True
                return

            p_bb_p, p_bb_v = self.prev_bb
            p_ba_p, p_ba_v = self.prev_ba
            ofi = 0.0

            if bb_p > p_bb_p:
                ofi += bb_v
            elif bb_p == p_bb_p:
                ofi += (bb_v - p_bb_v)

            if ba_p < p_ba_p:
                ofi -= ba_v
            elif ba_p == p_ba_p:
                ofi -= (ba_v - p_ba_v)

            self.raw_ofi_buf.append(ofi)

            if len(self.raw_ofi_buf) == OFI_ACCUM_WINDOW:
                self.ofi_history.append(sum(self.raw_ofi_buf))

            self.prev_bb, self.prev_ba = (bb_p, bb_v), (ba_p, ba_v)
            self.event_time = etime

    def get_signals(self):
        with self.lock:
            if len(self.ofi_history) < 2:
                return 0.0, self.micro_price, self.event_time
            avg = sum(self.ofi_history) / len(self.ofi_history)
            std = math.sqrt(sum((x - avg)**2 for x in self.ofi_history) / len(self.ofi_history))
            z = (self.ofi_history[-1] - avg) / std if std > 1e-9 else 0.0
            return z, self.micro_price, self.event_time

class BinanceFeed:
    def __init__(self, symbol):
        self.symbol = symbol.lower()
        self.ms = MarketMicrostructureState()

    def start(self):
        threading.Thread(target=lambda: asyncio.run(self._ws_loop()), daemon=True).start()

    async def _ws_loop(self):
        url = f"wss://fstream.binance.com/stream?streams={self.symbol}@depth5@100ms"
        while True:
            try:
                async with websockets.connect(url, ping_interval=None) as ws:
                    while True:
                        raw = await asyncio.wait_for(ws.recv(), timeout=WS_RECV_TIMEOUT)
                        data = orjson.loads(raw).get("data", {})
                        self.ms.update_depth(data.get("b", []), data.get("a", []), data.get("E", 0) / 1000.0)
            except Exception:
                await asyncio.sleep(WS_RECONNECT_DELAY)

def _get_exec_price(res, fallback_price):
    if not res:
        return fallback_price
    if res.price != 0.0:
        return res.price
    if res.deal > 0:
        deals = mt5.history_deals_get(ticket=res.deal)
        if deals:
            return deals[0].price
    return fallback_price

def _reset_state(state):
    state.is_closing = False
    state.peak_price = 0.0
    state.peak_unrealized_pt = 0.0
    state.entry_perf = 0.0
    state.trail_active = False
    state.be_active = False
    state.last_sl_price = 0.0

def _sl_hit_label(be_active, trail_active):
    if trail_active:
        return "SL_HIT(TRAIL)"
    if be_active:
        return "SL_HIT(BE)"
    return "SL_HIT(RAW)"

def update_sl(ticket, new_sl, pt, digits, state, pos_type, reason="SL", unrealized_pt=None):
    with state.lock:
        last_sl = state.last_sl_price
        # 方向ガード: SLが既存より不利な方向への更新を禁止
        if pos_type == mt5.ORDER_TYPE_BUY and new_sl <= last_sl:
            return
        if pos_type == mt5.ORDER_TYPE_SELL and new_sl >= last_sl:
            return
        if abs(new_sl - last_sl) / pt < SL_UPDATE_MIN_PT:
            return
        state.last_sl_price = new_sl

    req = {
        "action": mt5.TRADE_ACTION_SLTP,
        "position": ticket,
        "sl": round(new_sl, digits),
        "tp": 0.0,
    }
    res = mt5.order_send(req)
    if res and res.retcode == mt5.TRADE_RETCODE_DONE:
        u_str = f" Unrealized:{unrealized_pt:.1f}pt" if unrealized_pt is not None else ""
        logger.info(f"{reason} updated: NewSL:{new_sl:.2f}{u_str}")
    else:
        logger.warning(f"{reason} update failed: retcode:{res.retcode if res else -1} NewSL:{new_sl:.2f}")
        with state.lock:
            state.last_sl_price = last_sl

def _slip_filter_close(symbol, ticket, pos_type, exec_price, filling, digits, slip_pt, state):
    close_side = mt5.ORDER_TYPE_SELL if pos_type == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY
    pt = mt5.symbol_info(symbol).point

    for attempt in range(CLOSE_MAX_RETRIES):
        if not mt5.positions_get(ticket=ticket):
            with state.lock:
                _reset_state(state)
            return

        tick = mt5.symbol_info_tick(symbol)
        if not tick:
            time.sleep(CLOSE_RETRY_INTERVAL)
            continue

        price = tick.bid if close_side == mt5.ORDER_TYPE_SELL else tick.ask
        req = _build_close_req(symbol, ticket, FIXED_LOT, close_side, price, filling, digits, EXIT_DEVIATION)
        res = mt5.order_send(req)

        if res and res.retcode in [mt5.TRADE_RETCODE_DONE, mt5.TRADE_RETCODE_DONE_PARTIAL]:
            exec_p = _get_exec_price(res, price)
            pft = (exec_p - exec_price) / pt if pos_type == mt5.ORDER_TYPE_BUY else (exec_price - exec_p) / pt
            logger.info(f"Exit[SlipFilter] Slip:{slip_pt:.1f}pt Pft:{pft:.1f}pt ExecP:{exec_p:.2f}")
            with state.lock:
                _reset_state(state)
            return

        time.sleep(CLOSE_RETRY_INTERVAL)

    if mt5.positions_get(ticket=ticket):
        logger.warning(f"Exit[SlipFilter] close failed after {CLOSE_MAX_RETRIES} retries, ticket:{ticket} - keeping is_closing=True")
    else:
        with state.lock:
            _reset_state(state)

def execute_entry(symbol, side, filling, digits, z_score, curr_gap_entry, spread_pt, b_lat_ms, m_age_ms, state):
    tick = mt5.symbol_info_tick(symbol)
    if not tick:
        with state.lock:
            state.is_ordering = False
        return

    pt = mt5.symbol_info(symbol).point
    order_price = tick.ask if side == mt5.ORDER_TYPE_BUY else tick.bid
    sl_price = order_price - (SL_PT * pt) if side == mt5.ORDER_TYPE_BUY else order_price + (SL_PT * pt)

    req = _build_entry_req(symbol, side, order_price, sl_price, filling, digits)
    t0 = time.perf_counter()

    try:
        res = mt5.order_send(req)
        send_ms = (time.perf_counter() - t0) * 1000.0
        if res and res.retcode == mt5.TRADE_RETCODE_DONE:
            exec_price = _get_exec_price(res, order_price)
            slip_pt = (order_price - exec_price) / pt if side == mt5.ORDER_TYPE_BUY else (exec_price - order_price) / pt

            with state.lock:
                state.entry_count += 1
                entry_no = state.entry_count
                state.last_entry_perf = time.perf_counter()

            logger.info(f"Entry[#{entry_no}]:{'BUY' if side == mt5.ORDER_TYPE_BUY else 'SELL'} Z:{z_score:.2f} D_Gap:{curr_gap_entry:.1f}pt ExecP:{exec_price:.2f} Slip:{slip_pt:.1f}pt Lat:{b_lat_ms:.1f}ms Age:{m_age_ms:.1f}ms Send:{send_ms:.1f}ms")

            if slip_pt > SLIP_FILTER_PT:
                ticket = None
                for _ in range(ENTRY_TICKET_RETRY):
                    positions = mt5.positions_get(symbol=symbol)
                    matched = [p for p in positions if p.magic == MAGIC_NUMBER and p.type == side] if positions else []
                    if matched:
                        ticket = matched[0].ticket
                        break
                    time.sleep(ENTRY_TICKET_WAIT)

                if ticket is not None:
                    with state.lock:
                        state.is_closing = True
                        state.last_close_perf = time.perf_counter()
                    _slip_filter_close(symbol, ticket, side, exec_price, filling, digits, slip_pt, state)
                else:
                    logger.warning(f"SlipFilter: could not find position ticket after {ENTRY_TICKET_RETRY} retries, resetting state")
                    with state.lock:
                        _reset_state(state)
                return

            with state.lock:
                state.peak_price = exec_price
                state.peak_unrealized_pt = 0.0
                state.entry_perf = time.perf_counter()
                state.trail_active = False
                state.be_active = False
                state.last_sl_price = sl_price
        else:
            logger.warning(f"Entry Failed: Retcode:{res.retcode if res else -1}")
    finally:
        with state.lock:
            state.is_ordering = False

def execute_close(symbol, ticket, pos_type, open_price, filling, digits, reason, state):
    if not mt5.positions_get(ticket=ticket):
        logger.info(f"Exit[{reason}] Ticket:{ticket} already closed, skipping")
        with state.lock:
            state.last_close_perf = time.perf_counter()
            _reset_state(state)
        return

    close_side = mt5.ORDER_TYPE_SELL if pos_type == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY
    pt = mt5.symbol_info(symbol).point
    closed = False

    with state.lock:
        hold_sec = time.perf_counter() - state.entry_perf
        peak_unrealized_pt = state.peak_unrealized_pt
        entry_no = state.entry_count

    try:
        for attempt in range(CLOSE_MAX_RETRIES):
            pos_info = mt5.positions_get(ticket=ticket)
            if not pos_info:
                closed = True
                break

            rem_vol = pos_info[0].volume
            t = mt5.symbol_info_tick(symbol)
            if not t:
                time.sleep(CLOSE_RETRY_INTERVAL)
                continue

            price = t.bid if close_side == mt5.ORDER_TYPE_SELL else t.ask
            req = _build_close_req(symbol, ticket, rem_vol, close_side, price, filling, digits, EXIT_DEVIATION)

            t0 = time.perf_counter()
            res = mt5.order_send(req)
            ms = (time.perf_counter() - t0) * 1000.0

            if res and res.retcode in [mt5.TRADE_RETCODE_DONE, mt5.TRADE_RETCODE_DONE_PARTIAL]:
                exec_p = _get_exec_price(res, price)
                filled = res.volume if res.volume > 0 else rem_vol
                pft = (exec_p - open_price) / pt if pos_type == mt5.ORDER_TYPE_BUY else (open_price - exec_p) / pt
                logger.info(f"Exit[#{entry_no}][{reason}] Pft:{pft:.1f}pt Peak:{peak_unrealized_pt:.1f}pt ExecP:{exec_p:.2f} Send:{ms:.1f}ms Vol:{filled:.2f} Hold:{hold_sec:.1f}s")
                closed = True
                break

            time.sleep(CLOSE_RETRY_INTERVAL)

        if not closed:
            if mt5.positions_get(ticket=ticket):
                logger.warning(f"Exit[#{entry_no}][{reason}] Position {ticket} still open after {CLOSE_MAX_RETRIES} retries - keeping is_closing=True")
                with state.lock:
                    state.last_close_perf = time.perf_counter()
                return
            else:
                logger.warning(f"Exit[#{entry_no}][{reason}] Ticket:{ticket} not found after retries - assuming closed by SL")
                closed = True

    finally:
        if closed:
            with state.lock:
                state.explicitly_closed_tickets.add(ticket)
                state.last_close_perf = time.perf_counter()
                _reset_state(state)

def _force_close_all(filling, digits):
    for attempt in range(10):
        positions = mt5.positions_get(magic=MAGIC_NUMBER)
        if not positions:
            return
        for pos in positions:
            side = mt5.ORDER_TYPE_SELL if pos.type == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY
            tick = mt5.symbol_info_tick(pos.symbol)
            if not tick:
                continue
            price = tick.bid if side == mt5.ORDER_TYPE_SELL else tick.ask
            req = _build_close_req(pos.symbol, pos.ticket, pos.volume, side, price, filling, digits, 200)
            res = mt5.order_send(req)
            if res and res.retcode in [mt5.TRADE_RETCODE_DONE, mt5.TRADE_RETCODE_DONE_PARTIAL]:
                logger.info(f"ForceClose ticket:{pos.ticket} retcode:{res.retcode}")
            else:
                logger.warning(f"ForceClose failed ticket:{pos.ticket} retcode:{res.retcode if res else -1}")
        time.sleep(0.2)
    remaining = mt5.positions_get(magic=MAGIC_NUMBER)
    if remaining:
        logger.error(f"ForceClose: {len(remaining)} position(s) still open after all retries")

def main():
    if not mt5.initialize():
        return
    info = mt5.symbol_info(SYMBOL_MT5)
    if not info:
        return

    POINT = info.point
    DIGITS = max(0, round(-math.log10(POINT)))
    FILLING = mt5.ORDER_FILLING_FOK if info.filling_mode & 1 else mt5.ORDER_FILLING_RETURN

    mt5_feed = MT5TickFeed(SYMBOL_MT5)
    mt5_feed.start()
    feed, state = BinanceFeed(SYMBOL_BINANCE), TradeState()
    feed.start()

    logger.info(f"Bot v1.89: SL_PT={SL_PT}, BE={BE_TRIGGER_PT}/{BE_PROFIT_PT}, TRAIL={TRAIL_START_PT}/{TRAIL_DIST_PT}, SL_UPDATE_MIN={SL_UPDATE_MIN_PT}, BLACKOUT={ENTRY_BLACKOUT_SEC}s")

    prev_tickets = set()
    prev_state_snapshot = {}

    try:
        while True:
            now_perf, now_wall = time.perf_counter(), time.time()
            tick, mt5_recv_p = mt5_feed.get()
            z_score, micro_p, b_etime = feed.ms.get_signals()

            if not tick:
                time.sleep(0.0001)
                continue

            b_lat_ms = (now_wall - b_etime) * 1000.0
            m_age_ms = (now_perf - mt5_recv_p) * 1000.0
            curr_mid = (tick.bid + tick.ask) / 2.0
            raw_gap = (micro_p - curr_mid) / POINT
            spread_pt = (tick.ask - tick.bid) / POINT

            with state.lock:
                if b_etime != state.last_b_etime:
                    g_ema = state.gap_ema
                    g_ema = raw_gap if g_ema is None else g_ema * (1.0 - GAP_EMA_ALPHA) + raw_gap * GAP_EMA_ALPHA
                    state.gap_ema = g_ema
                    state.last_b_etime = b_etime
                g_ema = state.gap_ema if state.gap_ema is not None else raw_gap
                is_ord, is_cls, l_close = state.is_ordering, state.is_closing, state.last_close_perf
                l_entry = state.last_entry_perf

            positions = mt5.positions_get(symbol=SYMBOL_MT5, magic=MAGIC_NUMBER)
            curr_tickets = {p.ticket for p in positions} if positions else set()

            if is_cls and (now_perf - l_close) > CLOSE_TIMEOUT_SEC:
                if not curr_tickets:
                    with state.lock:
                        _reset_state(state)
                    is_cls = False
                else:
                    logger.warning("CloseTimeout: position still open, triggering force close")
                    _force_close_all(FILLING, DIGITS)

            vanished = prev_tickets - curr_tickets
            for ticket in vanished:
                with state.lock:
                    if ticket in state.explicitly_closed_tickets:
                        state.explicitly_closed_tickets.discard(ticket)
                        prev_state_snapshot.pop(ticket, None)
                        continue

                snap = prev_state_snapshot.get(ticket, {})
                snap_be = snap.get("be_active", False)
                snap_trail = snap.get("trail_active", False)
                snap_peak_pt = snap.get("peak_unrealized_pt", 0.0)
                snap_entry_no = snap.get("entry_count", 0)
                sl_label = _sl_hit_label(snap_be, snap_trail)

                deals = mt5.history_deals_get(position=ticket)
                if deals:
                    entry_deal = next((d for d in deals if d.entry == mt5.DEAL_ENTRY_IN), None)
                    exit_deal = next((d for d in deals if d.entry == mt5.DEAL_ENTRY_OUT), None)
                    if entry_deal and exit_deal:
                        pft_pt = (exit_deal.price - entry_deal.price) / POINT if entry_deal.type == mt5.ORDER_TYPE_BUY else (entry_deal.price - exit_deal.price) / POINT
                        hold = exit_deal.time - entry_deal.time
                        direction = "BUY" if entry_deal.type == mt5.ORDER_TYPE_BUY else "SELL"
                        logger.info(f"Exit[#{snap_entry_no}][{sl_label}] Ticket:{ticket} Dir:{direction} Pft:{pft_pt:.1f}pt Peak:{snap_peak_pt:.1f}pt ExecP:{exit_deal.price:.2f} Hold:{hold:.1f}s")

                with state.lock:
                    state.last_close_perf = time.perf_counter()
                    if not state.is_closing:
                        _reset_state(state)
                prev_state_snapshot.pop(ticket, None)
            prev_tickets = curr_tickets

            if positions and not is_cls:
                pos = positions[0]
                curr_p = tick.bid if pos.type == mt5.ORDER_TYPE_BUY else tick.ask

                is_exit, reason, peak_moved = False, "", False

                with state.lock:
                    trail_active = state.trail_active
                    be_active = state.be_active
                    unrealized_pt = (curr_p - pos.price_open) / POINT if pos.type == mt5.ORDER_TYPE_BUY else (pos.price_open - curr_p) / POINT

                    if not trail_active and not be_active and unrealized_pt >= BE_TRIGGER_PT:
                        state.be_active = True
                        be_active = True
                        be_price = pos.price_open + BE_PROFIT_PT * POINT if pos.type == mt5.ORDER_TYPE_BUY else pos.price_open - BE_PROFIT_PT * POINT
                        threading.Thread(target=update_sl, args=(pos.ticket, be_price, POINT, DIGITS, state, pos.type, "BreakEven", unrealized_pt), daemon=True).start()

                    if not trail_active and unrealized_pt >= TRAIL_START_PT:
                        state.trail_active = True
                        state.peak_price = curr_p
                        state.peak_unrealized_pt = unrealized_pt
                        trail_active = True

                    if trail_active and not state.is_closing:
                        if (pos.type == mt5.ORDER_TYPE_BUY and curr_p > state.peak_price) or \
                           (pos.type == mt5.ORDER_TYPE_SELL and curr_p < state.peak_price):
                            state.peak_price = curr_p
                            state.peak_unrealized_pt = unrealized_pt
                            peak_moved = True

                    if not _is_market_open(tick.time):
                        is_exit, reason = True, "MKT_CLOSE"

                    if is_exit:
                        peak_moved = False
                        if not state.is_closing:
                            state.is_closing = True
                            state.last_close_perf = now_perf

                    prev_state_snapshot[pos.ticket] = {
                        "be_active": state.be_active,
                        "trail_active": state.trail_active,
                        "peak_unrealized_pt": state.peak_unrealized_pt,
                        "entry_count": state.entry_count,
                    }

                if peak_moved:
                    new_sl = state.peak_price - TRAIL_DIST_PT * POINT if pos.type == mt5.ORDER_TYPE_BUY else state.peak_price + TRAIL_DIST_PT * POINT
                    threading.Thread(target=update_sl, args=(pos.ticket, new_sl, POINT, DIGITS, state, pos.type, "TrailSL", unrealized_pt), daemon=True).start()

                if is_exit:
                    threading.Thread(target=execute_close, args=(SYMBOL_MT5, pos.ticket, pos.type, pos.price_open, FILLING, DIGITS, reason, state), daemon=True).start()

            elif not positions and not is_ord and not is_cls:
                curr_gap_entry = raw_gap - g_ema

                if (now_perf - l_close) > COOLDOWN and (now_perf - l_entry) > ENTRY_BLACKOUT_SEC and _is_market_open(tick.time):
                    if b_lat_ms < MAX_BINANCE_LATENCY_MS and m_age_ms < MAX_TICK_AGE_MS and spread_pt <= SPREAD_FILTER_PT:
                        sig = 1 if (z_score > Z_SCORE_THR and curr_gap_entry > MIN_DELTA_GAP_PT) else \
                             -1 if (z_score < -Z_SCORE_THR and curr_gap_entry < -MIN_DELTA_GAP_PT) else 0

                        if sig != 0:
                            with state.lock:
                                if state.is_ordering or state.is_closing:
                                    sig = 0
                                else:
                                    state.is_ordering = True

                            if sig != 0:
                                threading.Thread(target=execute_entry, args=(SYMBOL_MT5, mt5.ORDER_TYPE_BUY if sig > 0 else mt5.ORDER_TYPE_SELL, FILLING, DIGITS, z_score, curr_gap_entry, spread_pt, b_lat_ms, m_age_ms, state), daemon=True).start()

            time.sleep(0.0001)

    except KeyboardInterrupt:
        pass
    finally:
        mt5_feed.running = False
        _force_close_all(FILLING, DIGITS)
        mt5.shutdown()
        logger.info("Bot shutdown complete")

if __name__ == "__main__":
    main()