# The model-picker repro -- the API-loaded model list, pinned in a
# pty against the compiled `target-monad/release/weaver`. The mock wire
# answers its catalogue (`["mock"]`) offline, so the whole command (fetch,
# cache, render, picker) runs without a socket or a key.
#
# Checks: /model with no argument opens the picker with the current name
# marked, Enter
# selects and closes it -- the start model is deliberately not in the
# list, so the echo AND the banner prove the selection was applied --
# /model with no argument opens it too, and Esc closes it without a
# change.

import os, pty, time, select, fcntl, termios, struct, re, shutil

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = REPO + "/target-monad/release/weaver"
TMP = os.environ.get("WV_REPRO_TMP", "/tmp/wv_models_repro")
os.makedirs(TMP, exist_ok=True)


class Grid:
    """Cursor moves, ESC[2J, printable UTF-8; SGR ignored."""

    def __init__(self, rows, cols):
        self.rows, self.cols = rows, cols
        self.cells = [[" "] * cols for _ in range(rows)]
        self.row = self.col = 0
        self.state, self.seq, self.utf8 = "text", "", b""

    def put(self, ch):
        if 0 <= self.row < self.rows and 0 <= self.col < self.cols:
            self.cells[self.row][self.col] = ch
        self.col += 1

    def feed(self, data):
        for b in data:
            if self.state == "csi":
                ch = bytes([b]).decode("latin-1")
                if "@" <= ch <= "~":
                    if ch == "H":
                        p = self.seq.split(";") if self.seq else []
                        self.row = int(p[0]) - 1 if p and p[0] else 0
                        self.col = int(p[1]) - 1 if len(p) > 1 and p[1] else 0
                    elif ch == "J" and self.seq in ("", "2"):
                        self.cells = [[" "] * self.cols for _ in range(self.rows)]
                    self.state, self.seq = "text", ""
                else:
                    self.seq += ch
                continue
            if self.state == "esc":
                ch = bytes([b]).decode("latin-1")
                self.state = "csi" if ch == "[" else ("osc" if ch == "]" else "text")
                self.seq = ""
                continue
            if self.state == "osc":
                if b == 7:
                    self.state = "text"
                continue
            if b == 0x1B:
                self.state = "esc"
            elif b == 10:
                self.row += 1; self.col = 0
            elif b == 13:
                self.col = 0
            elif b < 0x20:
                pass
            elif b < 0x80:
                self.utf8 = b""
                self.put(chr(b))
            else:
                self.utf8 += bytes([b])
                try:
                    ch = self.utf8.decode("utf-8")
                except UnicodeDecodeError:
                    if len(self.utf8) >= 4:
                        self.utf8 = b""
                    continue
                self.utf8 = b""
                self.put(ch)

    def find(self, needle):
        for r in range(self.rows):
            row = "".join(self.cells[r])
            c = row.find(needle)
            if c >= 0:
                return r, c
        return None


ROWS = int(os.environ.get("WV_REPRO_ROWS", "20"))
COLS = int(os.environ.get("WV_REPRO_COLS", "80"))
GRID = Grid(ROWS, COLS)


def spawn():
    turns = os.path.join(TMP, "turns_slow.json")
    shutil.copyfile(os.path.join(REPO, "scripts", "weaver-tui-repro", "turns_slow.json"), turns)
    master, slave = pty.openpty()
    os.set_blocking(master, False)
    pid = os.fork()
    if pid == 0:
        os.setsid()
        fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", ROWS, COLS, 0, 0))
        os.dup2(slave, 0); os.dup2(slave, 1); os.dup2(slave, 2)
        os.close(master)
        os.chdir(REPO)
        # The CURRENT model deliberately differs from the only listed
        # one: a correct Enter changes the config, so the echo and the
        # banner prove the selection was applied rather than merely
        # re-printed from the catalogue header.
        os.execve(BIN, [BIN, "--provider", "mock", "--model", "wv-not-mock"],
                  dict(os.environ, SHUTTLE_MOCK_TURNS=turns))
    return master, pid


def pump(master, sec, buf):
    end = time.time() + sec
    while time.time() < end:
        r, _, _ = select.select([master], [], [], 0.1)
        if r:
            try:
                d = os.read(master, 65536)
            except OSError:
                return
            if not d:
                return
            buf.extend(d)
            GRID.feed(d)


def snap(master, sec, buf):
    pump(master, sec, buf)
    return bytes(buf)


def finish(master, pid, buf):
    os.write(master, b"\x03"); time.sleep(0.3); pump(master, 0.4, buf)
    os.write(master, b"\x03"); time.sleep(0.5); pump(master, 0.8, buf)
    restored = "?1049l" in bytes(buf).decode(errors="replace")
    try:
        os.kill(pid, 9)
    except ProcessLookupError:
        pass
    os.close(master)
    return restored


checks = []

master, pid = spawn()
buf = bytearray()
pump(master, 2.0, buf)                 # startup frame
checks.append(("S0 the start model is the one asked for", GRID.find("mock/wv-not-mock") is not None))
os.write(master, b"/model\n")          # fetch + render + picker
snap(master, 1.5, buf)
checks.append(("S1 /model opens the picker", GRID.find("Select a model") is not None))
checks.append(("S1 the picker marks the current name", GRID.find("current: wv-not-mock") is not None))
if ROWS >= 10:
    checks.append(("S1 the API list is shown", GRID.find("   mock") is not None))
else:
    # WV_REPRO_ROWS=7: the panel has one content row, so header-only is
    # correct -- and the row under it must still be the border.
    head = GRID.find("Select a model")
    border = GRID.find("╰")
    checks.append(("S1 a short panel clips the picker to the header",
                   head is not None and GRID.find("Esc cancel") is None))
    checks.append(("S1 a short panel keeps its border",
                   head is not None and border is not None and border[0] == head[0] + 1))
checks.append(("S1 nothing was selected yet", GRID.find("model: mock") is None))

os.write(master, b"\r")                # Enter selects
snap(master, 1.0, buf)
checks.append(("S2 Enter closes the picker", GRID.find("Select a model") is None))
checks.append(("S2 the choice is echoed", GRID.find("model: mock") is not None))
checks.append(("S2 the banner shows the new model", GRID.find("mock/mock") is not None))

os.write(master, b"/model\n")          # no argument -> the same picker
snap(master, 1.5, buf)
checks.append(("S3 /model opens the picker", GRID.find("Select a model") is not None))
os.write(master, b"\x1b")              # Esc cancels
snap(master, 0.8, buf)
checks.append(("S3 Esc closes the picker", GRID.find("Select a model") is None))

checks.append(("S4 quit restores the terminal", finish(master, pid, buf)))

failed = False
for name, ok in checks:
    print(("PASS  " if ok else "FAIL  ") + name)
    failed = failed or not ok
if failed:
    raise SystemExit(1)
