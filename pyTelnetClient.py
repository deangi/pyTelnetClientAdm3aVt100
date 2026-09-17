"""
pyTelnetClient — tkinter telnet client with 80x24 display
emulating VT-100 or ADM-3A escape sequences.

Run:  python pyTelnetClient.py

The escape-code semantics mirror the vZ80 console parser so the same
mode switch ("vt100" | "adm3a") behaves identically on either end.

Version 2.4, September 5, 2026
Dean Gienger, May 13, 2026, with Claude
"""

import socket
import threading
import queue
import json
import os
import tkinter as tk
from pathlib import Path
from tkinter import ttk, font, messagebox

try:
    import serial
except ImportError:
    serial = None

APP_VERSION = "2.4"
APP_RELEASE_DATE = "September 5, 2026"
APP_CONFIG_DIR = Path(os.environ.get("APPDATA", Path.home())) / "pyTelnetClient"
CONNECTIONS_FILE = APP_CONFIG_DIR / "connections.json"

EMULATION_TYPES = ("VT-100", "ADM-3A")


class ConnectionStore:
    def __init__(self, path):
        self.path = path

    def load(self):
        try:
            with self.path.open("r", encoding="utf-8") as f:
                raw = json.load(f)
        except FileNotFoundError:
            return []
        except (OSError, json.JSONDecodeError):
            return []

        if not isinstance(raw, list):
            return []

        connections = []
        for item in raw:
            normalized = self._normalize(item)
            if normalized is not None:
                connections.append(normalized)
        return connections

    def save(self, connections):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.path.open("w", encoding="utf-8") as f:
            json.dump(connections, f, indent=2)
            f.write("\n")

    def _normalize(self, item):
        if not isinstance(item, dict):
            return None

        name = str(item.get("name", "")).strip()
        connection_type = str(item.get("type", "tcp")).strip().lower()
        if connection_type not in ("tcp", "serial"):
            connection_type = "tcp"
        host = str(item.get("host", "")).strip()
        serial_port = str(item.get("serial_port", item.get("device", ""))).strip()
        mode = str(item.get("emulation", "VT-100")).strip().upper()
        try:
            port = int(item.get("port", 23))
        except (TypeError, ValueError):
            port = 23
        try:
            baudrate = int(item.get("baudrate", item.get("baud", 9600)))
        except (TypeError, ValueError):
            baudrate = 9600

        if not name or (connection_type == "tcp" and not host) or (
                connection_type == "serial" and not serial_port):
            return None

        if mode in ("ADM3A", "ADM-3A"):
            emulation = "ADM-3A"
        else:
            emulation = "VT-100"

        return {
            "name": name,
            "type": connection_type,
            "host": host,
            "port": port,
            "serial_port": serial_port,
            "baudrate": baudrate,
            "emulation": emulation,
        }


# ---------------------------------------------------------------------------
# Terminal emulator (parser + 80x24 buffer + scrollback)
# ---------------------------------------------------------------------------

class TerminalEmulator:
    COLS = 80
    ROWS = 24
    SCROLLBACK_MAX = 1000

    MODE_VT100 = 0
    MODE_ADM3A = 1

    PS_GROUND      = 0
    PS_ESC         = 1
    PS_CSI         = 2
    PS_ADM_CUP_ROW = 3   # saw ESC '='; next byte = row + 0x20
    PS_ADM_CUP_COL = 4   # saw row byte; next byte = col + 0x20
    PS_CHARSET_DESIGNATE = 5  # saw ESC '(' or ESC ')'; next byte names set

    CHARSET_ASCII = "B"
    CHARSET_SPECIAL_GRAPHICS = "0"

    VT100_SPECIAL_GRAPHICS = {
        0x5F: ' ',
        0x60: '◆',
        0x61: '▒',
        0x62: '␉',
        0x63: '␌',
        0x64: '␍',
        0x65: '␊',
        0x66: '°',
        0x67: '±',
        0x68: '␤',
        0x69: '␋',
        0x6A: '┘',
        0x6B: '┐',
        0x6C: '┌',
        0x6D: '└',
        0x6E: '┼',
        0x6F: '⎺',
        0x70: '⎻',
        0x71: '─',
        0x72: '⎼',
        0x73: '⎽',
        0x74: '├',
        0x75: '┤',
        0x76: '┴',
        0x77: '┬',
        0x78: '│',
        0x79: '≤',
        0x7A: '≥',
        0x7B: 'π',
        0x7C: '≠',
        0x7D: '£',
        0x7E: '·',
    }

    def __init__(self):
        self.buf = [[' '] * self.COLS for _ in range(self.ROWS)]
        self.inverse = [[False] * self.COLS for _ in range(self.ROWS)]
        # Lines scrolled off the top of the screen (oldest first).
        self.history = []  # list of (chars_row, inverse_row)
        self.history_trimmed = 0  # rows dropped from front since last check
        self.cx = 0
        self.cy = 0
        self.saved_cx = 0
        self.saved_cy = 0
        self.mode = self.MODE_VT100
        self.pstate = self.PS_GROUND
        self.params = []
        self.cur_param = ''
        self.csi_private = False
        self.adm_cup_row = 0
        self.charset_designate_target = 0
        self.g0_charset = self.CHARSET_ASCII
        self.g1_charset = self.CHARSET_ASCII
        self.active_charset = 0
        self.vt100_application_keypad = False
        self.vt100_cursor_key_application = False
        self.vt100_auto_wrap = True
        self.vt100_origin_mode = False
        self.vt100_pending_wrap = False
        self.scroll_top = 0
        self.scroll_bottom = self.ROWS - 1
        self.current_inverse = False
        self.dirty = True
        self.answerback = self.default_answerback

    # ---- mode --------------------------------------------------------------
    def set_mode(self, mode):
        self.mode = mode
        self.pstate = self.PS_GROUND
        if mode == self.MODE_VT100:
            self.vt100_application_keypad = False
            self.active_charset = 0
            self.vt100_auto_wrap = True
            self.vt100_origin_mode = False
            self.vt100_pending_wrap = False
            self.scroll_top = 0
            self.scroll_bottom = self.ROWS - 1

    def reset_stream_state(self):
        """Discard an incomplete escape sequence after its input stream ends."""
        self.pstate = self.PS_GROUND
        self.params = []
        self.cur_param = ''
        self.csi_private = False
        self.adm_cup_row = 0
        self.charset_designate_target = 0

    # ---- low-level buffer ops ---------------------------------------------
    def clear(self):
        for r in range(self.ROWS):
            for c in range(self.COLS):
                self.buf[r][c] = ' '
                self.inverse[r][c] = False
        self.cx = 0
        self.cy = 0
        self.vt100_pending_wrap = False
        self.dirty = True

    def clear_scrollback(self):
        """Drop all lines that have scrolled off the live 80x24 screen."""
        self.history.clear()
        self.history_trimmed = 0
        self.dirty = True

    def _push_scrollback(self, chars, inv):
        """Save a line scrolled off the absolute top of the screen."""
        self.history.append((chars[:], inv[:]))
        while len(self.history) > self.SCROLLBACK_MAX:
            self.history.pop(0)
            self.history_trimmed += 1

    def take_history_trimmed(self):
        n = self.history_trimmed
        self.history_trimmed = 0
        return n

    def line_at(self, abs_row):
        """Return (chars, inverse) for absolute row (0 = oldest scrollback)."""
        hist = len(self.history)
        if abs_row < 0:
            return [' '] * self.COLS, [False] * self.COLS
        if abs_row < hist:
            return self.history[abs_row]
        live = abs_row - hist
        if 0 <= live < self.ROWS:
            return self.buf[live], self.inverse[live]
        return [' '] * self.COLS, [False] * self.COLS

    def total_rows(self):
        return len(self.history) + self.ROWS

    def scroll_up(self, top=None, bottom=None):
        if top is None:
            top = 0
        if bottom is None:
            bottom = self.ROWS - 1
        top = max(0, min(self.ROWS - 1, top))
        bottom = max(0, min(self.ROWS - 1, bottom))
        if bottom <= top:
            return

        # Lines leaving the absolute top of the screen enter scrollback.
        if top == 0:
            self._push_scrollback(self.buf[0], self.inverse[0])

        for r in range(top, bottom):
            self.buf[r] = self.buf[r + 1][:]
            self.inverse[r] = self.inverse[r + 1][:]
        self.buf[bottom] = [' '] * self.COLS
        self.inverse[bottom] = [False] * self.COLS
        self.dirty = True

    def scroll_down(self, top=None, bottom=None):
        if top is None:
            top = 0
        if bottom is None:
            bottom = self.ROWS - 1
        top = max(0, min(self.ROWS - 1, top))
        bottom = max(0, min(self.ROWS - 1, bottom))
        if bottom <= top:
            return

        for r in range(bottom, top, -1):
            self.buf[r] = self.buf[r - 1][:]
            self.inverse[r] = self.inverse[r - 1][:]
        self.buf[top] = [' '] * self.COLS
        self.inverse[top] = [False] * self.COLS
        self.dirty = True

    def newline(self):
        self.cx = 0
        self.vt100_pending_wrap = False
        if self.mode == self.MODE_VT100 and self.cy == self.scroll_bottom:
            self.scroll_up(self.scroll_top, self.scroll_bottom)
        elif self.cy >= self.ROWS - 1:
            self.scroll_up(0, self.ROWS - 1)
        else:
            self.cy += 1

    def cursor_to(self, row, col):
        if self.mode == self.MODE_VT100 and self.vt100_origin_mode:
            row += self.scroll_top
            row = max(self.scroll_top, min(self.scroll_bottom, row))
        else:
            row = max(0, min(self.ROWS - 1, row))
        col = max(0, min(self.COLS - 1, col))
        self.cy = row
        self.cx = col
        self.vt100_pending_wrap = False

    def erase_in_line(self, mode):
        # 0 = cursor..EOL, 1 = BOL..cursor, 2 = entire line
        if mode == 0:
            for c in range(self.cx, self.COLS):
                self.buf[self.cy][c] = ' '
                self.inverse[self.cy][c] = False
        elif mode == 1:
            for c in range(0, self.cx + 1):
                self.buf[self.cy][c] = ' '
                self.inverse[self.cy][c] = False
        elif mode == 2:
            for c in range(self.COLS):
                self.buf[self.cy][c] = ' '
                self.inverse[self.cy][c] = False
        self.dirty = True

    def erase_in_display(self, mode):
        # 0 = cursor..end, 1 = start..cursor, 2 = whole screen
        if mode == 0:
            for c in range(self.cx, self.COLS):
                self.buf[self.cy][c] = ' '
                self.inverse[self.cy][c] = False
            for r in range(self.cy + 1, self.ROWS):
                for c in range(self.COLS):
                    self.buf[r][c] = ' '
                    self.inverse[r][c] = False
        elif mode == 1:
            for r in range(0, self.cy):
                for c in range(self.COLS):
                    self.buf[r][c] = ' '
                    self.inverse[r][c] = False
            for c in range(0, self.cx + 1):
                self.buf[self.cy][c] = ' '
                self.inverse[self.cy][c] = False
        elif mode == 2:
            for r in range(self.ROWS):
                for c in range(self.COLS):
                    self.buf[r][c] = ' '
                    self.inverse[r][c] = False
        self.dirty = True

    # ---- byte stream entrypoint -------------------------------------------
    def write(self, data):
        for b in data:
            self.putc(b)

    def putc(self, b):
        # CAN unconditionally cancels any pending escape
        if b == 0x18:
            self.pstate = self.PS_GROUND
            return

        # SUB — ADM-3A clear; VT-100 cancel
        if b == 0x1A:
            if self.mode == self.MODE_ADM3A:
                self.clear()
            self.pstate = self.PS_GROUND
            return

        # ADM-3A binary cursor address — route raw bytes before the
        # C0 filter so 0x20 (space) reaches the col handler.
        if self.pstate == self.PS_ADM_CUP_ROW:
            self.adm_cup_row = b - 0x20
            self.pstate = self.PS_ADM_CUP_COL
            return
        if self.pstate == self.PS_ADM_CUP_COL:
            col = b - 0x20
            self.cursor_to(self.adm_cup_row, col)
            self.pstate = self.PS_GROUND
            return
        if self.pstate == self.PS_CHARSET_DESIGNATE:
            self.designate_charset(b)
            self.pstate = self.PS_GROUND
            return

        # ESC always restarts escape parsing
        if b == 0x1B:
            self.pstate = self.PS_ESC
            return

        if self.pstate == self.PS_ESC:
            self.parse_esc(b)
            return
        if self.pstate == self.PS_CSI:
            self.parse_csi(b)
            return

        self.putc_ground(b)

    def putc_ground(self, b):
        # C0 controls
        if b == 0x07:                                   # BEL
            self.root_bell()
            return
        if b == 0x08:                                   # BS
            self.vt100_pending_wrap = False
            if self.cx > 0:
                self.cx -= 1
            return
        if b == 0x09:                                   # HT
            self.vt100_pending_wrap = False
            self.cx = (self.cx + 8) & ~7
            if self.cx > self.COLS - 1:
                self.cx = self.COLS - 1
            return
        if b == 0x0A:                                   # LF
            self.newline()
            return
        if b == 0x0D:                                   # CR
            self.cx = 0
            self.vt100_pending_wrap = False
            return
        if b == 0x0E:                                   # SO — invoke G1
            if self.mode == self.MODE_VT100:
                self.active_charset = 1
            return
        if b == 0x0F:                                   # SI — invoke G0
            if self.mode == self.MODE_VT100:
                self.active_charset = 0
            return
        if b == 0x0B:                                   # VT — ADM cursor up; VT-100 ignores
            if self.mode == self.MODE_ADM3A and self.cy > 0:
                self.cy -= 1
            return
        if b == 0x0C:                                   # FF — VT-100 clear+home; ADM cursor right
            if self.mode == self.MODE_ADM3A:
                if self.cx < self.COLS - 1:
                    self.cx += 1
            else:
                self.clear()
            return
        if b == 0x1E:                                   # RS — home (no clear)
            self.cx = 0
            self.cy = 0
            self.vt100_pending_wrap = False
            return

        # Printable
        if 0x20 <= b < 0x7F:
            if self.mode == self.MODE_VT100 and self.vt100_pending_wrap:
                self.cx = 0
                if self.cy == self.scroll_bottom:
                    self.scroll_up(self.scroll_top, self.scroll_bottom)
                elif self.cy >= self.ROWS - 1:
                    self.scroll_up(0, self.ROWS - 1)
                else:
                    self.cy += 1
                self.vt100_pending_wrap = False

            self.buf[self.cy][self.cx] = self.translate_printable(b)
            self.inverse[self.cy][self.cx] = self.current_inverse
            self.dirty = True
            if self.cx < self.COLS - 1:
                self.cx += 1
            elif self.mode == self.MODE_VT100 and self.vt100_auto_wrap:
                self.vt100_pending_wrap = True
            # else: stay clamped at COLS-1, matching CP/M-friendly behavior

    # ---- escape parsing ---------------------------------------------------
    def parse_esc(self, b):
        # ESC '=' is ADM-3A cursor addressing in ADM-3A mode, and VT100
        # application keypad mode in VT100 mode.
        if b == ord('='):
            if self.mode == self.MODE_ADM3A:
                self.pstate = self.PS_ADM_CUP_ROW
            else:
                self.vt100_application_keypad = True
                self.pstate = self.PS_GROUND
            return

        if self.mode == self.MODE_VT100 and b == ord('>'):
            self.vt100_application_keypad = False
            self.pstate = self.PS_GROUND
            return

        # ADM-3A screen controls are available regardless of mode
        if b == ord('T'):
            self.erase_in_line(0)
            self.pstate = self.PS_GROUND
            return
        if b == ord('Y'):
            self.erase_in_display(0)
            self.pstate = self.PS_GROUND
            return
        if b == ord('*'):
            self.clear()
            self.pstate = self.PS_GROUND
            return

        # VT-100
        if b == ord('['):
            self.pstate = self.PS_CSI
            self.params = []
            self.cur_param = ''
            self.csi_private = False
            return
        if self.mode == self.MODE_VT100 and b == ord('Z'):  # DECID
            self.answerback(b'\x1B[?1;2c')
            self.pstate = self.PS_GROUND
            return
        if b in (ord('('), ord(')')):
            self.charset_designate_target = 0 if b == ord('(') else 1
            self.pstate = self.PS_CHARSET_DESIGNATE
            return
        if b == ord('E'):                                # NEL
            self.newline()
            self.pstate = self.PS_GROUND
            return
        if b == ord('D'):                                # IND
            if self.mode == self.MODE_VT100 and self.cy == self.scroll_bottom:
                self.scroll_up(self.scroll_top, self.scroll_bottom)
            elif self.cy >= self.ROWS - 1:
                self.scroll_up(0, self.ROWS - 1)
            else:
                self.cy += 1
            self.pstate = self.PS_GROUND
            return
        if b == ord('M'):                                # RI (reverse index)
            if self.mode == self.MODE_VT100 and self.cy == self.scroll_top:
                self.scroll_down(self.scroll_top, self.scroll_bottom)
            elif self.cy > 0:
                self.cy -= 1
            self.pstate = self.PS_GROUND
            return
        if b == ord('7'):                                # DECSC
            self.saved_cx = self.cx
            self.saved_cy = self.cy
            self.pstate = self.PS_GROUND
            return
        if b == ord('8'):                                # DECRC
            self.cx = self.saved_cx
            self.cy = self.saved_cy
            self.pstate = self.PS_GROUND
            return

        # Unknown — drop and resume
        self.pstate = self.PS_GROUND

    def designate_charset(self, b):
        charset = chr(b)
        if charset not in (self.CHARSET_ASCII, self.CHARSET_SPECIAL_GRAPHICS):
            charset = self.CHARSET_ASCII

        if self.charset_designate_target == 0:
            self.g0_charset = charset
        else:
            self.g1_charset = charset

    def translate_printable(self, b):
        if self.mode != self.MODE_VT100:
            return chr(b)

        charset = self.g1_charset if self.active_charset else self.g0_charset
        if charset == self.CHARSET_SPECIAL_GRAPHICS:
            return self.VT100_SPECIAL_GRAPHICS.get(b, chr(b))
        return chr(b)

    def parse_csi(self, b):
        if b == ord('?') and not self.params and self.cur_param == '':
            self.csi_private = True
            return
        if 0x30 <= b <= 0x39:                            # digit
            self.cur_param += chr(b)
            return
        if b == ord(';'):
            self.params.append(int(self.cur_param) if self.cur_param else 0)
            self.cur_param = ''
            return
        if 0x20 <= b <= 0x2F:                            # intermediate — ignore
            return
        if 0x40 <= b <= 0x7E:                            # final byte
            if self.cur_param != '':
                self.params.append(int(self.cur_param))
                self.cur_param = ''
            if self.csi_private:
                self.dispatch_private_csi(b)
            else:
                self.dispatch_csi(b)
            self.pstate = self.PS_GROUND
            self.csi_private = False
            return
        # Anything else — abandon
        self.pstate = self.PS_GROUND
        self.csi_private = False

    def csi_param(self, i, default_val):
        if i < len(self.params):
            v = self.params[i]
            return v if v != 0 else default_val
        return default_val

    def dispatch_csi(self, final):
        if final == ord('H') or final == ord('f'):       # CUP / HVP
            row = self.csi_param(0, 1) - 1
            col = self.csi_param(1, 1) - 1
            self.cursor_to(row, col)
        elif final == ord('J'):                          # ED
            mode = self.params[0] if self.params else 0
            self.erase_in_display(mode)
        elif final == ord('K'):                          # EL
            mode = self.params[0] if self.params else 0
            self.erase_in_line(mode)
        elif final == ord('A'):                          # CUU
            n = self.csi_param(0, 1)
            self.cy = max(0, self.cy - n)
        elif final == ord('B'):                          # CUD
            n = self.csi_param(0, 1)
            self.cy = min(self.ROWS - 1, self.cy + n)
        elif final == ord('C'):                          # CUF
            n = self.csi_param(0, 1)
            self.cx = min(self.COLS - 1, self.cx + n)
        elif final == ord('D'):                          # CUB
            n = self.csi_param(0, 1)
            self.cx = max(0, self.cx - n)
        elif final == ord('G'):                          # CHA — column abs
            col = self.csi_param(0, 1) - 1
            self.cx = max(0, min(self.COLS - 1, col))
        elif final == ord('d'):                          # VPA — row abs
            row = self.csi_param(0, 1) - 1
            self.cy = max(0, min(self.ROWS - 1, row))
        elif final == ord('s'):                          # save cursor
            self.saved_cx = self.cx
            self.saved_cy = self.cy
        elif final == ord('u'):                          # restore cursor
            self.cx = self.saved_cx
            self.cy = self.saved_cy
        elif final == ord('m'):                          # SGR
            self.dispatch_sgr()
        elif final == ord('r'):                          # DECSTBM
            self.set_scroll_region()
        elif final == ord('c'):                          # DA
            if not self.params or self.params == [0]:
                self.answerback(b'\x1B[?1;2c')
        # Other CSI (DSR, etc.) silently ignored.

    def set_scroll_region(self):
        top = self.params[0] if len(self.params) >= 1 and self.params[0] else 1
        bottom = self.params[1] if len(self.params) >= 2 and self.params[1] else self.ROWS

        top -= 1
        bottom -= 1
        if top < 0:
            top = 0
        if bottom >= self.ROWS:
            bottom = self.ROWS - 1
        if bottom <= top:
            self.scroll_top = 0
            self.scroll_bottom = self.ROWS - 1
        else:
            self.scroll_top = top
            self.scroll_bottom = bottom
        self.cursor_to(0, 0)

    def dispatch_sgr(self):
        params = self.params if self.params else [0]
        for param in params:
            if param == 0:
                self.current_inverse = False
            elif param == 7:
                self.current_inverse = True
            elif param == 27:
                self.current_inverse = False

    def dispatch_private_csi(self, final):
        if final not in (ord('h'), ord('l')):
            return

        enabled = final == ord('h')
        for mode in self.params:
            if mode == 1:                                # DECCKM
                self.vt100_cursor_key_application = enabled
            elif mode == 7:                              # DECAWM
                self.vt100_auto_wrap = enabled
            elif mode == 8:                              # DECARM
                # Repeat-key mode is owned by the local keyboard/OS.
                pass
            elif mode == 6:                              # DECOM
                self.vt100_origin_mode = enabled
                self.cursor_to(0, 0)
            elif mode == 25:                             # DECTCEM
                # Cursor visibility is ignored; cursor stays visible.
                pass
            # Other DEC private modes are safely ignored.

    # ---- hooks (overridable) ----------------------------------------------
    def root_bell(self):
        pass

    def default_answerback(self, data):
        pass


# ---------------------------------------------------------------------------
# Telnet client (background-thread socket)
# ---------------------------------------------------------------------------

class TelnetClient:
    IAC  = 0xFF
    DONT = 0xFE
    DO   = 0xFD
    WONT = 0xFC
    WILL = 0xFB
    SB   = 0xFA
    SE   = 0xF0

    OPT_BINARY = 0
    OPT_ECHO   = 1
    OPT_SGA    = 3

    def __init__(self, rx_callback, status_callback,
                 unexpected_disconnect_callback=None):
        self.sock = None
        self.serial_conn = None
        self.transport = None
        self.rx_callback = rx_callback
        self.status_callback = status_callback
        self.unexpected_disconnect_callback = unexpected_disconnect_callback
        self.rx_thread = None
        self.running = False

    def _close_serial(self):
        """Close a serial device defensively; USB devices may vanish at any time."""
        connection = self.serial_conn
        self.serial_conn = None
        if connection is not None:
            try:
                connection.close()
            except Exception:
                pass

    def connect(self, host, port):
        if self.running:
            return False
        try:
            self.sock = socket.create_connection((host, port), timeout=10)
            self.sock.settimeout(None)
            self.transport = "tcp"
            self.running = True
            self.rx_thread = threading.Thread(target=self._rx_loop, daemon=True)
            self.rx_thread.start()
            self.status_callback(f"Connected to {host}:{port}")
            return True
        except Exception as e:
            self.status_callback(f"Connect failed: {e}")
            self.sock = None
            self.transport = None
            return False

    def connect_serial(self, serial_port, baudrate):
        if self.running:
            return False
        if serial is None:
            self.status_callback("Serial support requires pyserial (pip install pyserial)")
            return False
        try:
            # Opening may fail because the device has de-enumerated.
            self.serial_conn = serial.Serial(serial_port, baudrate, timeout=1)
            self.transport = "serial"
            self.running = True
            self.rx_thread = threading.Thread(target=self._rx_loop, daemon=True)
            self.rx_thread.start()
            self.status_callback(f"Connected to {serial_port} at {baudrate} baud")
            return True
        except Exception as e:
            # Also close a port successfully opened before a later setup error.
            self._close_serial()
            self.running = False
            self.transport = None
            self.status_callback(f"Serial connect failed: {e}")
            return False

    def disconnect(self, unexpected=False):
        was_running = self.running
        self.running = False
        if self.sock is not None:
            try:
                self.sock.shutdown(socket.SHUT_RDWR)
            except Exception:
                pass
            try:
                self.sock.close()
            except Exception:
                pass
            self.sock = None
        self._close_serial()
        self.transport = None
        if was_running:
            self.status_callback("Disconnected")
        if unexpected and self.unexpected_disconnect_callback is not None:
            self.unexpected_disconnect_callback()

    def send(self, data):
        if not self.running or (self.sock is None and self.serial_conn is None):
            return
        if isinstance(data, str):
            data = data.encode('latin-1', errors='replace')
        try:
            if self.transport == "serial":
                # A USB serial device can disappear between the state check
                # above and this write; this is deliberately inside try/except.
                connection = self.serial_conn
                if connection is None:
                    raise OSError("serial device is unavailable")
                connection.write(data)
            else:
                self.sock.sendall(data)
        except Exception as e:
            self.status_callback(f"Send error: {e}")
            self.disconnect(unexpected=True)

    def _rx_loop(self):
        iac_state = None
        while self.running and (self.sock is not None or self.serial_conn is not None):
            try:
                if self.transport == "serial":
                    # Keep this call exception-contained: unplugging a device
                    # while blocked in read is a normal reconnect condition.
                    connection = self.serial_conn
                    if connection is None:
                        raise OSError("serial device is unavailable")
                    data = connection.read(4096)
                    if not data:
                        continue
                else:
                    data = self.sock.recv(4096)
                    if not data:
                        break
            except Exception as e:
                if self.running:
                    self.status_callback(f"Recv error: {e}")
                break

            if self.transport == "serial":
                self.rx_callback(data)
                continue

            out = bytearray()
            for b in data:
                if iac_state is None:
                    if b == self.IAC:
                        iac_state = 'cmd'
                    else:
                        out.append(b)
                elif iac_state == 'cmd':
                    if b == self.IAC:                    # escaped 0xFF data
                        out.append(self.IAC)
                        iac_state = None
                    elif b in (self.DO, self.DONT, self.WILL, self.WONT):
                        iac_state = ('opt', b)
                    elif b == self.SB:
                        iac_state = 'sb'
                    else:
                        iac_state = None
                elif isinstance(iac_state, tuple) and iac_state[0] == 'opt':
                    cmd = iac_state[1]
                    self._respond_iac(cmd, b)
                    iac_state = None
                elif iac_state == 'sb':
                    if b == self.IAC:
                        iac_state = 'sb_iac'
                elif iac_state == 'sb_iac':
                    if b == self.SE:
                        iac_state = None
                    else:
                        iac_state = 'sb'

            if out:
                self.rx_callback(bytes(out))

        unexpected = self.running
        self.running = False
        if self.sock is not None:
            try:
                self.sock.close()
            except Exception:
                pass
            self.sock = None
        self._close_serial()
        transport = self.transport
        self.transport = None
        if unexpected:
            self.status_callback("Serial disconnected" if transport == "serial" else "TCP disconnected")
            if self.unexpected_disconnect_callback is not None:
                self.unexpected_disconnect_callback()

    def _respond_iac(self, cmd, opt):
        if self.sock is None:
            return
        try:
            if cmd == self.DO:
                resp_will = opt in (self.OPT_SGA, self.OPT_BINARY)
                resp = bytes([self.IAC,
                              self.WILL if resp_will else self.WONT,
                              opt])
                self.sock.sendall(resp)
            elif cmd == self.WILL:
                resp_do = opt in (self.OPT_SGA, self.OPT_ECHO, self.OPT_BINARY)
                resp = bytes([self.IAC,
                              self.DO if resp_do else self.DONT,
                              opt])
                self.sock.sendall(resp)
            # DONT/WONT — no response required
        except Exception:
            pass


# ---------------------------------------------------------------------------
# Tkinter UI
# ---------------------------------------------------------------------------

class TerminalApp:
    REFRESH_MS = 33  # ~30 fps

    def __init__(self, root):
        self.root = root
        self.root.title(f"pyTelnetClient v{APP_VERSION} - VT-100 / ADM-3A")

        self.term = TerminalEmulator()
        self.term.root_bell = self._bell
        self.term.answerback = self._terminal_answerback
        self.rx_queue = queue.Queue()
        self.telnet = TelnetClient(self._on_rx_bytes, self._on_status,
                                   self._on_unexpected_disconnect)
        self.connection_store = ConnectionStore(CONNECTIONS_FILE)
        self.connections = self.connection_store.load()
        self.reconnect_after_id = None
        self.reconnect_active = False
        self.reconnect_host = ""
        self.reconnect_port = 23
        self.reconnect_type = "tcp"
        self.reconnect_serial_port = ""
        self.reconnect_baudrate = 9600
        self.selection_start = None
        self.selection_end = None
        self.selection_dragging = False
        # 0 = live screen; positive = lines scrolled up into history.
        self.view_offset = 0
        self.capture_active = False
        self.capture_chunks = []
        self.status_escape_buffer = bytearray()

        self._build_ui()
        self._schedule_refresh()
        self._cursor_blink_on = True
        self._schedule_blink()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---- UI construction --------------------------------------------------
    def _build_ui(self):
        top = ttk.Frame(self.root, padding=4)
        top.pack(side=tk.TOP, fill=tk.X)

        ttk.Label(top, text="Connection:").pack(side=tk.LEFT)
        self.connection_var = tk.StringVar()
        self.connection_combo = ttk.Combobox(top, textvariable=self.connection_var,
                                             width=18, state="readonly")
        self.connection_combo.pack(side=tk.LEFT, padx=2)
        self.connection_combo.bind("<<ComboboxSelected>>",
                                   self._on_connection_selected)

        ttk.Button(top, text="Manage", command=self._open_connection_manager)\
            .pack(side=tk.LEFT, padx=(2, 8))

        self.connect_btn = ttk.Button(top, text="Connect",
                                      command=self._on_connect)
        self.connect_btn.pack(side=tk.LEFT, padx=4)

        self.connection_state_var = tk.StringVar(value="Disconnected")
        self.connection_state_label = tk.Label(
            top, textvariable=self.connection_state_var,
            bg="#7A1E1E", fg="#FFFFFF", padx=8, pady=2)
        self.connection_state_label.pack(side=tk.LEFT, padx=(8, 0))

        self._refresh_connection_combo()

        # Pick a monospace font that exists
        available = set(font.families())
        for fam in ("Consolas", "Courier New", "Courier", "DejaVu Sans Mono",
                    "Monaco", "TkFixedFont"):
            if fam in available or fam == "TkFixedFont":
                self.mono = font.Font(family=fam, size=12)
                break
        else:
            self.mono = font.Font(family="Courier", size=12)

        self.cell_w = self.mono.measure("M")
        self.cell_h = self.mono.metrics("linespace")

        cw_total = self.cell_w * TerminalEmulator.COLS
        ch_total = self.cell_h * TerminalEmulator.ROWS

        self.fg = "#E6E6E6"
        self.bg = "#000000"
        self.cursor_color = "#33FF33"
        self.selection_fg = "#FFFFFF"
        self.selection_bg = "#2A62D5"

        terminal_area = ttk.Frame(self.root)
        terminal_area.pack(anchor=tk.W, padx=4, pady=4)

        self.canvas = tk.Canvas(terminal_area, width=cw_total, height=ch_total,
                                bg=self.bg, highlightthickness=0,
                                takefocus=True)
        self.canvas.pack(side=tk.LEFT)

        self.scrollbar = ttk.Scrollbar(terminal_area, orient=tk.VERTICAL,
                                       command=self._on_scrollbar)
        self.scrollbar.pack(side=tk.LEFT, fill=tk.Y)

        side = ttk.Frame(terminal_area, padding=(8, 0, 0, 0))
        side.pack(side=tk.LEFT, fill=tk.Y)

        ttk.Label(side, text="Type:").pack(anchor=tk.W)
        self.connection_type_var = tk.StringVar(value="tcp")
        ttk.Combobox(side, textvariable=self.connection_type_var,
                     values=["tcp", "serial"], width=16,
                     state="readonly").pack(fill=tk.X, pady=(0, 4))

        ttk.Label(side, text="Host:").pack(anchor=tk.W)
        self.host_var = tk.StringVar(value="127.0.0.1")
        ttk.Entry(side, textvariable=self.host_var, width=18)\
            .pack(fill=tk.X, pady=(0, 4))

        ttk.Label(side, text="TCP port:").pack(anchor=tk.W)
        self.port_var = tk.StringVar(value="23")
        ttk.Entry(side, textvariable=self.port_var, width=18)\
            .pack(fill=tk.X, pady=(0, 4))

        ttk.Label(side, text="COM port:").pack(anchor=tk.W)
        self.serial_port_var = tk.StringVar()
        ttk.Entry(side, textvariable=self.serial_port_var, width=18)\
            .pack(fill=tk.X, pady=(0, 4))

        ttk.Label(side, text="Baud rate:").pack(anchor=tk.W)
        self.baudrate_var = tk.StringVar(value="9600")
        ttk.Entry(side, textvariable=self.baudrate_var, width=18)\
            .pack(fill=tk.X, pady=(0, 4))

        ttk.Label(side, text="Emulation:").pack(anchor=tk.W)
        self.mode_var = tk.StringVar(value="VT-100")
        mode_combo = ttk.Combobox(side, textvariable=self.mode_var,
                                  values=["VT-100", "ADM-3A"],
                                  width=16, state="readonly")
        mode_combo.pack(fill=tk.X, pady=(0, 8))
        mode_combo.bind("<<ComboboxSelected>>", self._on_mode_change)

        ttk.Button(side, text="Clear", command=self._on_clear)\
            .pack(fill=tk.X, pady=(0, 4))
        ttk.Button(side, text="Copy",
                   command=lambda: self._copy_selection(show_empty=True))\
            .pack(fill=tk.X, pady=4)
        ttk.Button(side, text="Paste", command=self._paste_clipboard)\
            .pack(fill=tk.X, pady=4)
        ttk.Button(side, text="Start Capture", command=self._start_capture)\
            .pack(fill=tk.X, pady=4)
        ttk.Button(side, text="Load Capture", command=self._load_capture)\
            .pack(fill=tk.X, pady=4)

        # Pre-build cell background and text items — updating items is far
        # cheaper than redrawing the whole canvas each frame.
        self.cell_bg_items = [[None] * TerminalEmulator.COLS
                              for _ in range(TerminalEmulator.ROWS)]
        self.cell_items = [[None] * TerminalEmulator.COLS
                           for _ in range(TerminalEmulator.ROWS)]
        for r in range(TerminalEmulator.ROWS):
            for c in range(TerminalEmulator.COLS):
                x0 = c * self.cell_w
                y0 = r * self.cell_h
                x = c * self.cell_w + self.cell_w // 2
                y = r * self.cell_h + self.cell_h // 2
                self.cell_bg_items[r][c] = self.canvas.create_rectangle(
                    x0, y0, x0 + self.cell_w, y0 + self.cell_h,
                    fill=self.bg, outline=self.bg)
                self.cell_items[r][c] = self.canvas.create_text(
                    x, y, text=' ', font=self.mono, fill=self.fg,
                    anchor='center')

        self.cursor_item = self.canvas.create_rectangle(
            0, 0, self.cell_w, self.cell_h,
            outline=self.cursor_color, width=1)

        # The status panel is a borderless 80-column area aligned with the
        # main terminal canvas; it does not extend beneath the right controls.
        self.status_panel = tk.Text(self.root, height=4, width=TerminalEmulator.COLS,
                                    font=self.mono, bg=self.bg, fg=self.fg,
                                    insertbackground=self.fg, wrap=tk.NONE,
                                    borderwidth=0, highlightthickness=0,
                                    padx=0, pady=0, state=tk.DISABLED,
                                    takefocus=False)
        self.status_panel.pack(anchor=tk.W, padx=4, pady=(0, 4))
        self.status_bg = self.bg
        self.status_chars = [[' '] * TerminalEmulator.COLS for _ in range(4)]
        self.status_fg = [[self.fg] * TerminalEmulator.COLS for _ in range(4)]
        self.status_cell_bg = [[self.bg] * TerminalEmulator.COLS for _ in range(4)]
        self.status_tags = {}
        self._redraw_status_panel()

        # Status bar
        self.status_var = tk.StringVar(value="Not connected")
        ttk.Label(self.root, textvariable=self.status_var, anchor=tk.W,
                  relief=tk.SUNKEN).pack(side=tk.BOTTOM, fill=tk.X)

        # Keyboard and mouse input.
        # Ctrl+C / Ctrl+V are NOT intercepted — ASCII controls (0..127),
        # including ^C, are sent to the host via <Key>. Use the Copy/Paste
        # buttons or Shift+Insert (paste) for clipboard.
        self.canvas.bind("<Key>", self._on_key)
        self.canvas.bind("<Shift-Insert>", self._on_paste_key)
        self.canvas.bind("<Button-1>", self._on_select_start)
        self.canvas.bind("<B1-Motion>", self._on_select_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_select_end)
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.canvas.bind("<Button-4>", self._on_mousewheel_linux)
        self.canvas.bind("<Button-5>", self._on_mousewheel_linux)
        self.canvas.focus_set()
        self._sync_scrollbar()

    # ---- callbacks --------------------------------------------------------
    def _bell(self):
        try:
            self.root.bell()
        except Exception:
            pass

    def _terminal_answerback(self, data):
        if self.telnet.running:
            self.telnet.send(data)

    def _on_mode_change(self, event=None):
        if self.mode_var.get() == "ADM-3A":
            self.term.set_mode(TerminalEmulator.MODE_ADM3A)
        else:
            self.term.set_mode(TerminalEmulator.MODE_VT100)

    def _refresh_connection_combo(self):
        names = [conn["name"] for conn in self.connections]
        current = self.connection_var.get()
        self.connection_combo.configure(values=names)
        if current not in names:
            self.connection_var.set("")

    def _on_connection_selected(self, event=None):
        selected = self.connection_var.get()
        conn = self._find_connection(selected)
        if conn is None:
            return

        self.connection_type_var.set(conn["type"])
        self.host_var.set(conn["host"])
        self.port_var.set(str(conn["port"]))
        self.serial_port_var.set(conn["serial_port"])
        self.baudrate_var.set(str(conn["baudrate"]))
        self.mode_var.set(conn["emulation"])
        self._on_mode_change()

    def _find_connection(self, name):
        for conn in self.connections:
            if conn["name"] == name:
                return conn
        return None

    def _open_connection_manager(self):
        win = tk.Toplevel(self.root)
        win.title("Manage Connections")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)

        outer = ttk.Frame(win, padding=8)
        outer.pack(fill=tk.BOTH, expand=True)

        tree = ttk.Treeview(outer, columns=("type", "host", "port", "emulation"),
                            show="tree headings", height=8)
        tree.heading("#0", text="Name")
        tree.heading("type", text="Type")
        tree.heading("host", text="Endpoint")
        tree.heading("port", text="Port")
        tree.heading("emulation", text="Emulation")
        tree.column("#0", width=130, stretch=False)
        tree.column("type", width=60, anchor=tk.CENTER, stretch=False)
        tree.column("host", width=150, stretch=False)
        tree.column("port", width=60, anchor=tk.CENTER, stretch=False)
        tree.column("emulation", width=80, anchor=tk.CENTER, stretch=False)
        tree.grid(row=0, column=0, columnspan=4, sticky="nsew")

        form = ttk.Frame(outer)
        form.grid(row=1, column=0, columnspan=4, sticky="ew", pady=(8, 0))

        ttk.Label(form, text="Name:").grid(row=0, column=0, sticky=tk.W)
        name_var = tk.StringVar()
        ttk.Entry(form, textvariable=name_var, width=22)\
            .grid(row=0, column=1, padx=(2, 10), sticky=tk.W)

        ttk.Label(form, text="Type:").grid(row=0, column=2, sticky=tk.W)
        type_var = tk.StringVar(value="tcp")
        ttk.Combobox(form, textvariable=type_var, values=["tcp", "serial"],
                     width=10, state="readonly").grid(row=0, column=3, padx=(2, 0), sticky=tk.W)

        ttk.Label(form, text="IP / Host:").grid(row=1, column=0, sticky=tk.W, pady=(6, 0))
        host_var = tk.StringVar()
        ttk.Entry(form, textvariable=host_var, width=24)\
            .grid(row=1, column=1, padx=(2, 10), pady=(6, 0), sticky=tk.W)

        ttk.Label(form, text="Port:").grid(row=1, column=2, sticky=tk.W,
                                           pady=(6, 0))
        port_var = tk.StringVar(value="23")
        ttk.Entry(form, textvariable=port_var, width=8)\
            .grid(row=1, column=3, padx=(2, 0), pady=(6, 0), sticky=tk.W)

        ttk.Label(form, text="COM port:").grid(row=2, column=0, sticky=tk.W, pady=(6, 0))
        serial_port_var = tk.StringVar()
        ttk.Entry(form, textvariable=serial_port_var, width=12).grid(row=2, column=1, padx=(2, 10), pady=(6, 0), sticky=tk.W)
        ttk.Label(form, text="Baud:").grid(row=2, column=2, sticky=tk.W, pady=(6, 0))
        baudrate_var = tk.StringVar(value="9600")
        ttk.Entry(form, textvariable=baudrate_var, width=10).grid(row=2, column=3, padx=(2, 0), pady=(6, 0), sticky=tk.W)

        ttk.Label(form, text="Emulation:").grid(row=3, column=0, sticky=tk.W, pady=(6, 0))
        emulation_var = tk.StringVar(value="VT-100")
        ttk.Combobox(form, textvariable=emulation_var, values=EMULATION_TYPES,
                     width=10, state="readonly")\
            .grid(row=3, column=1, padx=(2, 0), pady=(6, 0), sticky=tk.W)

        buttons = ttk.Frame(outer)
        buttons.grid(row=2, column=0, columnspan=4, sticky="ew", pady=(8, 0))

        def refresh_tree(select_name=None):
            for item_id in tree.get_children():
                tree.delete(item_id)
            selected_id = None
            for index, conn in enumerate(self.connections):
                item_id = str(index)
                endpoint = conn["serial_port"] if conn["type"] == "serial" else conn["host"]
                detail = conn["baudrate"] if conn["type"] == "serial" else conn["port"]
                tree.insert("", tk.END, iid=item_id, text=conn["name"],
                            values=(conn["type"], endpoint, detail, conn["emulation"]))
                if conn["name"] == select_name:
                    selected_id = item_id
            if selected_id is not None:
                tree.selection_set(selected_id)
                tree.focus(selected_id)

        def selected_index():
            selection = tree.selection()
            if not selection:
                return None
            try:
                return int(selection[0])
            except ValueError:
                return None

        def load_selected(event=None):
            index = selected_index()
            if index is None or index >= len(self.connections):
                return
            conn = self.connections[index]
            name_var.set(conn["name"])
            type_var.set(conn["type"])
            host_var.set(conn["host"])
            port_var.set(str(conn["port"]))
            serial_port_var.set(conn["serial_port"])
            baudrate_var.set(str(conn["baudrate"]))
            emulation_var.set(conn["emulation"])

        def read_form(existing_index=None):
            name = name_var.get().strip()
            connection_type = type_var.get()
            host = host_var.get().strip()
            serial_port = serial_port_var.get().strip()
            emulation = emulation_var.get()

            if not name:
                messagebox.showerror("Connection", "Enter a connection name.", parent=win)
                return None
            if connection_type == "tcp" and not host:
                messagebox.showerror("Connection", "Enter an IP or host.", parent=win)
                return None
            if connection_type == "serial" and not serial_port:
                messagebox.showerror("Connection", "Enter a COM port.", parent=win)
                return None
            try:
                port = int(port_var.get())
                baudrate = int(baudrate_var.get())
            except ValueError:
                messagebox.showerror("Connection", "Port and baud rate must be numeric.", parent=win)
                return None
            if port < 1 or port > 65535 or baudrate < 1:
                messagebox.showerror("Connection", "Enter valid port and baud-rate values.", parent=win)
                return None
            if emulation not in EMULATION_TYPES:
                emulation = "VT-100"

            for index, conn in enumerate(self.connections):
                if index != existing_index and conn["name"] == name:
                    messagebox.showerror("Connection",
                                         "That connection name already exists.",
                                         parent=win)
                    return None

            return {
                "name": name,
                "type": connection_type,
                "host": host,
                "port": port,
                "serial_port": serial_port,
                "baudrate": baudrate,
                "emulation": emulation,
            }

        def save_connections(select_name=None):
            self.connection_store.save(self.connections)
            self._refresh_connection_combo()
            refresh_tree(select_name)

        def add_connection():
            conn = read_form()
            if conn is None:
                return
            self.connections.append(conn)
            save_connections(conn["name"])

        def update_connection():
            index = selected_index()
            if index is None or index >= len(self.connections):
                messagebox.showerror("Connection",
                                     "Select a connection to update.",
                                     parent=win)
                return
            conn = read_form(index)
            if conn is None:
                return
            self.connections[index] = conn
            save_connections(conn["name"])

        def delete_connection():
            index = selected_index()
            if index is None or index >= len(self.connections):
                messagebox.showerror("Connection",
                                     "Select a connection to delete.",
                                     parent=win)
                return
            name = self.connections[index]["name"]
            if not messagebox.askyesno("Delete Connection",
                                       f"Delete connection '{name}'?",
                                       parent=win):
                return
            del self.connections[index]
            save_connections()

        def use_selected():
            load_selected()
            selected = selected_index()
            if selected is None or selected >= len(self.connections):
                return
            conn = self.connections[selected]
            self.connection_var.set(conn["name"])
            self._on_connection_selected()
            win.destroy()

        ttk.Button(buttons, text="Add", command=add_connection)\
            .pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(buttons, text="Update", command=update_connection)\
            .pack(side=tk.LEFT, padx=4)
        ttk.Button(buttons, text="Delete", command=delete_connection)\
            .pack(side=tk.LEFT, padx=4)
        ttk.Button(buttons, text="Use Selected", command=use_selected)\
            .pack(side=tk.RIGHT, padx=(4, 0))
        ttk.Button(buttons, text="Close", command=win.destroy)\
            .pack(side=tk.RIGHT, padx=4)

        tree.bind("<<TreeviewSelect>>", load_selected)
        refresh_tree()

    def _on_connect(self):
        if self.telnet.running:
            self._cancel_reconnect()
            self.telnet.disconnect()
            self.connect_btn.config(text="Connect")
            self._set_connection_state("Disconnected", "#7A1E1E")
            return
        connection_type = self.connection_type_var.get()
        try:
            port = int(self.port_var.get())
            baudrate = int(self.baudrate_var.get())
        except ValueError:
            self.status_var.set("Invalid port or baud rate")
            return
        self._on_mode_change()
        host = self.host_var.get().strip()
        serial_port = self.serial_port_var.get().strip()
        if connection_type == "tcp" and not host:
            self.status_var.set("Enter a host")
            return
        if connection_type == "serial" and not serial_port:
            self.status_var.set("Enter a COM port")
            return
        self._cancel_reconnect()
        self.reconnect_type = connection_type
        self.reconnect_host = host
        self.reconnect_port = port
        self.reconnect_serial_port = serial_port
        self.reconnect_baudrate = baudrate
        self._set_connection_state("Connecting", "#7A5A1E")
        connected = (self.telnet.connect_serial(serial_port, baudrate)
                     if connection_type == "serial" else self.telnet.connect(host, port))
        if connected:
            self.connect_btn.config(text="Disconnect")
            self._set_connection_state("Connected", "#1E6B35")
            self.canvas.focus_set()
        else:
            self._set_connection_state("Disconnected", "#7A1E1E")

    def _on_clear(self):
        self._clear_selection()
        self.view_offset = 0
        self.term.clear()
        self.term.clear_scrollback()
        self._reset_status_panel()
        self._sync_scrollbar()
        self._redraw()
        self._update_cursor()

    def _view_top(self):
        """Absolute row index of the first visible screen row."""
        return len(self.term.history) - self.view_offset

    def _clamp_view_offset(self):
        hist = len(self.term.history)
        if self.view_offset > hist:
            self.view_offset = hist
        if self.view_offset < 0:
            self.view_offset = 0

    def _scroll_view(self, delta_lines):
        """Move the viewport by delta_lines (positive = older / up)."""
        if delta_lines == 0 and len(self.term.history) == 0:
            return
        self.view_offset += delta_lines
        self._clamp_view_offset()
        self._sync_scrollbar()
        self._redraw()
        self._update_cursor()

    def _snap_to_live(self):
        if self.view_offset != 0:
            self.view_offset = 0
            self._sync_scrollbar()
            self._redraw()
            self._update_cursor()

    def _sync_scrollbar(self):
        hist = len(self.term.history)
        total = hist + TerminalEmulator.ROWS
        if hist <= 0:
            self.scrollbar.set(0.0, 1.0)
            return
        top = float(hist - self.view_offset) / float(total)
        bottom = float(hist - self.view_offset + TerminalEmulator.ROWS) / float(total)
        self.scrollbar.set(max(0.0, top), min(1.0, bottom))

    def _on_scrollbar(self, action, value=None, units=None):
        hist = len(self.term.history)
        if hist <= 0:
            self.view_offset = 0
            self._sync_scrollbar()
            return

        if action == "moveto":
            # value is fraction for the top of the thumb in the trough.
            top_line = int(round(float(value) * hist))
            top_line = max(0, min(hist, top_line))
            self.view_offset = hist - top_line
        elif action == "scroll":
            amount = int(float(value))
            if units == "pages":
                amount *= TerminalEmulator.ROWS
            self.view_offset -= amount  # scrollbar scroll down → newer
            self._clamp_view_offset()
        self._sync_scrollbar()
        self._redraw()
        self._update_cursor()

    def _on_mousewheel(self, event):
        # Windows/macOS: event.delta is multiples of 120.
        if event.delta > 0:
            self._scroll_view(3)
        elif event.delta < 0:
            self._scroll_view(-3)
        return "break"

    def _on_mousewheel_linux(self, event):
        if event.num == 4:
            self._scroll_view(3)
        elif event.num == 5:
            self._scroll_view(-3)
        return "break"

    def _adjust_selection_after_trim(self, dropped):
        if dropped <= 0:
            return
        if self.selection_start is not None:
            row, col = self.selection_start
            row -= dropped
            if row < 0:
                self.selection_start = None
                self.selection_end = None
                self.selection_dragging = False
                return
            self.selection_start = (row, col)
        if self.selection_end is not None:
            row, col = self.selection_end
            row -= dropped
            if row < 0:
                self.selection_start = None
                self.selection_end = None
                self.selection_dragging = False
                return
            self.selection_end = (row, col)

    def _on_rx_bytes(self, data):
        # Called from telnet rx thread — push to queue, drained on UI thread
        self.rx_queue.put(data)

    def _capture_bytes(self, data):
        if self.capture_active and data:
            self.capture_chunks.append(data.decode('latin-1',
                                                   errors='replace'))

    @staticmethod
    def _rgb_to_tk(value):
        """Convert RGB nibbles to #R0G0B0 (for example, F12 -> #F01020)."""
        value = value.upper()
        return "#" + "".join(ch + "0" for ch in value)

    def _reset_status_panel(self):
        """Blank the four-line status panel and restore default colours."""
        self.status_bg = self.bg
        for row in range(4):
            for col in range(TerminalEmulator.COLS):
                self.status_chars[row][col] = ' '
                self.status_fg[row][col] = self.fg
                self.status_cell_bg[row][col] = self.status_bg
        self.status_panel.config(bg=self.status_bg)
        self._redraw_status_panel()

    def _set_status_background(self, rgb):
        if len(rgb) != 3 or any(ch not in "0123456789abcdefABCDEF" for ch in rgb):
            return False
        self.status_bg = self._rgb_to_tk(rgb)
        self.status_panel.config(bg=self.status_bg)
        # A new panel background starts a fresh status display.
        for row in range(4):
            for col in range(TerminalEmulator.COLS):
                self.status_chars[row][col] = ' '
                self.status_fg[row][col] = self.fg
                self.status_cell_bg[row][col] = self.status_bg
        self._redraw_status_panel()
        return True

    def _write_status_text(self, fg_rgb, bg_rgb, row_text, col_text, text):
        try:
            row = int(row_text)
            col = int(col_text)
        except ValueError:
            return False
        if (len(fg_rgb) != 3 or len(bg_rgb) != 3 or row not in range(4)
                or col not in range(TerminalEmulator.COLS)
                or any(ch not in "0123456789abcdefABCDEF" for ch in fg_rgb + bg_rgb)):
            return False
        fg = self._rgb_to_tk(fg_rgb)
        bg = self._rgb_to_tk(bg_rgb)
        for ch in text:
            if col >= TerminalEmulator.COLS:
                break
            self.status_chars[row][col] = ch
            self.status_fg[row][col] = fg
            self.status_cell_bg[row][col] = bg
            col += 1
        self._redraw_status_panel()
        return True

    def _redraw_status_panel(self):
        self.status_panel.config(state=tk.NORMAL, bg=self.status_bg)
        self.status_panel.delete("1.0", tk.END)
        for row in range(4):
            for col in range(TerminalEmulator.COLS):
                fg = self.status_fg[row][col]
                bg = self.status_cell_bg[row][col]
                tag = self.status_tags.get((fg, bg))
                if tag is None:
                    tag = f"status_{len(self.status_tags)}"
                    self.status_tags[(fg, bg)] = tag
                    self.status_panel.tag_configure(tag, foreground=fg, background=bg)
                self.status_panel.insert(tk.END, self.status_chars[row][col], tag)
            if row < 3:
                self.status_panel.insert(tk.END, "\n")
        self.status_panel.config(state=tk.DISABLED)

    def _filter_status_escapes(self, data):
        """Apply complete ESC ** status commands and return terminal bytes."""
        self.status_escape_buffer.extend(data)
        output = bytearray()
        while self.status_escape_buffer:
            marker = self.status_escape_buffer.find(b"\x1b**")
            if marker < 0:
                # Keep a possible partial prefix for the next receive chunk.
                keep = 0
                for suffix in (b"\x1b**", b"\x1b*", b"\x1b"):
                    if self.status_escape_buffer.endswith(suffix):
                        keep = len(suffix)
                        break
                if keep:
                    output.extend(self.status_escape_buffer[:-keep])
                    self.status_escape_buffer = self.status_escape_buffer[-keep:]
                else:
                    output.extend(self.status_escape_buffer)
                    self.status_escape_buffer.clear()
                break
            output.extend(self.status_escape_buffer[:marker])
            command = self.status_escape_buffer[marker:]
            if command.startswith(b"\x1b**BG"):
                if len(command) < 8:
                    self.status_escape_buffer = bytearray(command)
                    break
                code = command[5:8].decode("ascii", errors="ignore")
                self._set_status_background(code)
                self.status_escape_buffer = bytearray(command[8:])
            elif command.startswith(b"\x1b**TX"):
                eot = command.find(b"\x04", 5)
                if eot < 0:
                    self.status_escape_buffer = bytearray(command)
                    break
                fields = command[5:eot].decode("latin-1", errors="replace").split(",", 4)
                if len(fields) == 5:
                    self._write_status_text(*fields)
                self.status_escape_buffer = bytearray(command[eot + 1:])
            else:
                # Not a status command: preserve the original terminal input.
                output.append(self.status_escape_buffer[0])
                self.status_escape_buffer = self.status_escape_buffer[1:]
        return bytes(output)

    def _start_capture(self):
        self.capture_chunks = []
        self.capture_active = True
        self.status_var.set("Serial capture started")

    def _captured_text(self):
        return ''.join(self.capture_chunks)

    def _load_capture(self):
        self.capture_active = False
        text = self._captured_text()
        if not text:
            self.status_var.set("No captured data")
            return False

        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self.root.update()
        self.status_var.set(f"Loaded {len(text)} captured characters")
        self.canvas.focus_set()
        return True

    def _on_status(self, text):
        # Marshal to UI thread
        def apply():
            self.status_var.set(text)
            if not self.telnet.running:
                self.connect_btn.config(text="Connect")
        self.root.after(0, apply)

    def _set_connection_state(self, text, bg):
        self.connection_state_var.set(text)
        self.connection_state_label.config(bg=bg)

    def _event_to_cell(self, event):
        """Map a canvas click to absolute (row, col) including scrollback."""
        col = event.x // self.cell_w
        row = event.y // self.cell_h
        col = max(0, min(TerminalEmulator.COLS - 1, col))
        row = max(0, min(TerminalEmulator.ROWS - 1, row))
        abs_row = self._view_top() + row
        abs_row = max(0, min(self.term.total_rows() - 1, abs_row))
        return abs_row, col

    def _selection_bounds(self):
        if self.selection_start is None or self.selection_end is None:
            return None

        start = self.selection_start
        end = self.selection_end
        start_pos = start[0] * TerminalEmulator.COLS + start[1]
        end_pos = end[0] * TerminalEmulator.COLS + end[1]
        if start_pos <= end_pos:
            return start, end
        return end, start

    def _cell_is_selected(self, abs_row, col):
        bounds = self._selection_bounds()
        if bounds is None:
            return False

        start, end = bounds
        pos = abs_row * TerminalEmulator.COLS + col
        start_pos = start[0] * TerminalEmulator.COLS + start[1]
        end_pos = end[0] * TerminalEmulator.COLS + end[1]
        return start_pos <= pos <= end_pos

    def _clear_selection(self):
        if self.selection_start is None and self.selection_end is None:
            return
        self.selection_start = None
        self.selection_end = None
        self.selection_dragging = False
        self._redraw()

    def _on_select_start(self, event):
        self.canvas.focus_set()
        cell = self._event_to_cell(event)
        self.selection_start = cell
        self.selection_end = cell
        self.selection_dragging = True
        self._redraw()
        return "break"

    def _on_select_drag(self, event):
        if not self.selection_dragging:
            return "break"
        self.selection_end = self._event_to_cell(event)
        self._redraw()
        return "break"

    def _on_select_end(self, event):
        if self.selection_dragging:
            self.selection_end = self._event_to_cell(event)
            self.selection_dragging = False
            self._redraw()
        return "break"

    def _selected_text(self):
        bounds = self._selection_bounds()
        if bounds is None:
            return ""

        start, end = bounds
        lines = []
        for row in range(start[0], end[0] + 1):
            if row == start[0]:
                col_start = start[1]
            else:
                col_start = 0

            if row == end[0]:
                col_end = end[1]
            else:
                col_end = TerminalEmulator.COLS - 1

            chars, _inv = self.term.line_at(row)
            text = ''.join(chars[col_start:col_end + 1])
            lines.append(text.rstrip())
        return "\r".join(lines)

    def _copy_selection(self, show_empty=False):
        text = self._selected_text()
        if not text:
            if show_empty:
                self.status_var.set("No text selected")
            return False

        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self.root.update()
        self.status_var.set(f"Copied {len(text)} characters")
        return True

    def _on_copy_key(self, event):
        if self._copy_selection():
            return "break"
        return None

    def _clipboard_text_for_terminal(self, text):
        text = text.replace("\r\n", "\n")
        text = text.replace("\r", "\n")
        return text.replace("\n", "\r")

    def _paste_clipboard(self):
        if not self.telnet.running:
            self.status_var.set("Not connected")
            return False
        try:
            text = self.root.clipboard_get()
        except tk.TclError:
            self.status_var.set("Clipboard is empty")
            return False

        data = self._clipboard_text_for_terminal(text)
        if not data:
            self.status_var.set("Clipboard is empty")
            return False

        self.telnet.send(data)
        self.status_var.set(f"Pasted {len(data)} characters")
        self.canvas.focus_set()
        return True

    def _on_paste_key(self, event):
        self._paste_clipboard()
        return "break"

    def _on_unexpected_disconnect(self):
        self.root.after(0, self._handle_unexpected_disconnect)

    def _reset_stream_parsers(self):
        # A lost TCP or serial stream can leave either parser mid-command.
        self.status_escape_buffer.clear()
        self.term.reset_stream_state()

    def _handle_unexpected_disconnect(self):
        self._reset_stream_parsers()
        self.connect_btn.config(text="Connect")
        self._set_connection_state("Disconnected - retrying", "#7A1E1E")
        self.reconnect_active = True
        self._schedule_reconnect()

    def _schedule_reconnect(self):
        if self.reconnect_after_id is not None:
            return
        if not self.reconnect_active or self.telnet.running:
            return
        self.reconnect_after_id = self.root.after(4000, self._try_reconnect)

    def _try_reconnect(self):
        self.reconnect_after_id = None
        if not self.reconnect_active or self.telnet.running:
            return
        if (self.reconnect_type == "tcp" and not self.reconnect_host) or (self.reconnect_type == "serial" and not self.reconnect_serial_port):
            self._set_connection_state("Disconnected", "#7A1E1E")
            self.reconnect_active = False
            return

        self._set_connection_state("Reconnecting", "#7A5A1E")
        endpoint = (f"{self.reconnect_serial_port} at {self.reconnect_baudrate} baud"
                    if self.reconnect_type == "serial"
                    else f"{self.reconnect_host}:{self.reconnect_port}")
        self.status_var.set(f"Reconnecting to {endpoint}")
        self._on_mode_change()
        connected = (self.telnet.connect_serial(self.reconnect_serial_port, self.reconnect_baudrate)
                     if self.reconnect_type == "serial"
                     else self.telnet.connect(self.reconnect_host, self.reconnect_port))
        if connected:
            self.reconnect_active = False
            self.connect_btn.config(text="Disconnect")
            self._set_connection_state("Connected", "#1E6B35")
            self.canvas.focus_set()
        else:
            self._set_connection_state("Disconnected - retrying", "#7A1E1E")
            self._schedule_reconnect()

    def _cancel_reconnect(self):
        self.reconnect_active = False
        if self.reconnect_after_id is not None:
            self.root.after_cancel(self.reconnect_after_id)
            self.reconnect_after_id = None

    def _on_close(self):
        self._cancel_reconnect()
        self.telnet.disconnect()
        self.root.destroy()

    # ---- refresh loop -----------------------------------------------------
    def _schedule_refresh(self):
        # Drain bytes received from the telnet thread
        drained = False
        try:
            while True:
                data = self.rx_queue.get_nowait()
                self._capture_bytes(data)
                terminal_data = self._filter_status_escapes(data)
                if terminal_data:
                    self.term.write(terminal_data)
                drained = True
        except queue.Empty:
            pass

        trimmed = self.term.take_history_trimmed()
        if trimmed:
            self._adjust_selection_after_trim(trimmed)
            self._clamp_view_offset()

        if self.term.dirty or drained or trimmed:
            self._sync_scrollbar()
            self._redraw()
            self.term.dirty = False

        self._update_cursor()
        self.root.after(self.REFRESH_MS, self._schedule_refresh)

    def _redraw(self):
        cfg = self.canvas.itemconfig
        items = self.cell_items
        bg_items = self.cell_bg_items
        view_top = self._view_top()
        for r in range(TerminalEmulator.ROWS):
            abs_row = view_top + r
            row, inverse_row = self.term.line_at(abs_row)
            row_items = items[r]
            row_bg_items = bg_items[r]
            for c in range(TerminalEmulator.COLS):
                if self._cell_is_selected(abs_row, c):
                    text_fill = self.selection_fg
                    bg_fill = self.selection_bg
                elif inverse_row[c]:
                    text_fill = self.bg
                    bg_fill = self.fg
                else:
                    text_fill = self.fg
                    bg_fill = self.bg
                cfg(row_bg_items[c], fill=bg_fill, outline=bg_fill)
                cfg(row_items[c], text=row[c], fill=text_fill)

    def _update_cursor(self):
        # Cursor tracks the live screen; hide it while viewing scrollback.
        live_top = len(self.term.history)
        view_top = self._view_top()
        abs_cy = live_top + self.term.cy
        if abs_cy < view_top or abs_cy >= view_top + TerminalEmulator.ROWS:
            self.canvas.itemconfig(self.cursor_item, state="hidden")
            return
        self.canvas.itemconfig(self.cursor_item, state="normal")
        x = self.term.cx * self.cell_w
        y = (abs_cy - view_top) * self.cell_h
        self.canvas.coords(self.cursor_item,
                           x, y, x + self.cell_w, y + self.cell_h)

    def _schedule_blink(self):
        self._cursor_blink_on = not self._cursor_blink_on
        color = self.cursor_color if self._cursor_blink_on else ""
        self.canvas.itemconfig(self.cursor_item, outline=color)
        self.root.after(500, self._schedule_blink)

    # ---- keyboard ---------------------------------------------------------
    def _on_key(self, event):
        if not self.telnet.running:
            return

        # Typing returns the viewport to the live screen.
        self._snap_to_live()

        ks = event.keysym
        ch = event.char

        if self.term.mode == TerminalEmulator.MODE_ADM3A:
            key_map = {
                'Left':      b'\x08',
                'Down':      b'\x0A',
                'Up':        b'\x0B',
                'Right':     b'\x0C',
                'Home':      b'\x1E',
                'BackSpace': b'\x08',
                'Delete':    b'\x7F',
                'Return':    b'\x0D',
                'Tab':       b'\x09',
                'Escape':    b'\x1B',
            }
        else:
            if self.term.vt100_cursor_key_application:
                arrow_up = b'\x1BOA'
                arrow_down = b'\x1BOB'
                arrow_right = b'\x1BOC'
                arrow_left = b'\x1BOD'
            else:
                arrow_up = b'\x1B[A'
                arrow_down = b'\x1B[B'
                arrow_right = b'\x1B[C'
                arrow_left = b'\x1B[D'

            key_map = {
                'Left':      arrow_left,
                'Down':      arrow_down,
                'Up':        arrow_up,
                'Right':     arrow_right,
                'Home':      b'\x1B[H',
                'End':       b'\x1B[F',
                'Prior':     b'\x1B[5~',   # PgUp
                'Next':      b'\x1B[6~',   # PgDn
                'BackSpace': b'\x7F',
                'Delete':    b'\x1B[3~',
                'Return':    b'\x0D',
                'Tab':       b'\x09',
                'Escape':    b'\x1B',
                'F1':        b'\x1BOP',
                'F2':        b'\x1BOQ',
                'F3':        b'\x1BOR',
                'F4':        b'\x1BOS',
            }

            keypad_normal = {
                'KP_0':        b'0',
                'KP_1':        b'1',
                'KP_2':        b'2',
                'KP_3':        b'3',
                'KP_4':        b'4',
                'KP_5':        b'5',
                'KP_6':        b'6',
                'KP_7':        b'7',
                'KP_8':        b'8',
                'KP_9':        b'9',
                'KP_Decimal':  b'.',
                'KP_Subtract': b'-',
                'KP_Enter':    b'\x0D',
                'KP_Add':      b'+',
                'KP_Multiply': b'*',
                'KP_Divide':   b'/',
            }

            keypad_application = {
                'KP_0':        b'\x1BOp',
                'KP_1':        b'\x1BOq',
                'KP_2':        b'\x1BOr',
                'KP_3':        b'\x1BOs',
                'KP_4':        b'\x1BOt',
                'KP_5':        b'\x1BOu',
                'KP_6':        b'\x1BOv',
                'KP_7':        b'\x1BOw',
                'KP_8':        b'\x1BOx',
                'KP_9':        b'\x1BOy',
                'KP_Decimal':  b'\x1BOn',
                'KP_Subtract': b'\x1BOm',
                'KP_Enter':    b'\x1BOM',
                'KP_Add':      b'+',
                'KP_Multiply': b'*',
                'KP_Divide':   b'/',
            }

            if self.term.vt100_application_keypad:
                key_map.update(keypad_application)
            else:
                key_map.update(keypad_normal)

        if ks in key_map:
            self.telnet.send(key_map[ks])
            return

        # Pass through ASCII including C0 controls (e.g. Ctrl+C -> 0x03).
        if ch and len(ch) == 1:
            code = ord(ch)
            if 0 <= code <= 127:
                self.telnet.send(bytes([code]))
                return
            try:
                self.telnet.send(ch.encode('latin-1'))
            except UnicodeEncodeError:
                pass


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    root = tk.Tk()
    TerminalApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
