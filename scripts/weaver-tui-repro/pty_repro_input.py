# Input-box repro: the caret is visible on the first frame (over the
# placeholder) and after a submit, a click places the caret, and a drag
# selects input text and copies it through OSC 52.
import base64, fcntl, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TMP = tempfile.mkdtemp(prefix="wv_input_repro_")
HOME = TMP + "/home"
FIXTURE = os.path.join(REPO, "scripts/weaver-tui-repro/turns_select.json")
INPUT_ROW = 21  # 0-based; SGR reports are 1-based


class Grid:
    """Cursor moves, ESC[2J, printable UTF-8; SGR ignored. Wide glyphs are
    one key at their left cell and an empty continuation cell."""
    def __init__(self, rows, cols):
        self.rows, self.cols = rows, cols
        self.cells = [[" "] * cols for _ in range(rows)]
        self.row = self.col = 0
        self.state, self.seq, self.utf8 = "text", "", b""

    @staticmethod
    def wide(ch):
        o = ord(ch)
        return (0x1100 <= o <= 0x115F or 0x2E80 <= o <= 0xA4CF
                or 0xAC00 <= o <= 0xD7A3 or 0xF900 <= o <= 0xFAFF
                or 0xFF00 <= o <= 0xFF60 or 0x1F300 <= o <= 0x1FAFF)

    def put(self, ch):
        if 0 <= self.row < self.rows and 0 <= self.col < self.cols:
            self.cells[self.row][self.col] = ch
            if self.wide(ch) and self.col + 1 < self.cols:
                self.cells[self.row][self.col + 1] = ""
                self.col += 1
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
            if b == 0x1b:
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


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    return ok


def main():
    if not (os.path.isfile(BIN) and os.access(BIN, os.X_OK)):
        raise SystemExit("missing weaver binary: %s (build with --release)" % BIN)
    os.makedirs(HOME, exist_ok=True)
    master, slave = pty.openpty()
    os.set_blocking(master, False)
    pid = os.fork()
    if pid == 0:
        try:
            os.setsid()
            fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 80, 0, 0))
            os.dup2(slave, 0); os.dup2(slave, 1); os.dup2(slave, 2)
            os.close(master)
            os.chdir(TMP)
            env = dict(os.environ)
            env.pop("NO_COLOR", None)
            env["HOME"] = HOME
            env["WEAVER_SESSION_ROOT"] = TMP + "/sessions"
            env["SHUTTLE_MOCK_TURNS"] = FIXTURE
            os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock"], env)
        except BaseException:
            os._exit(127)

    grid = Grid(24, 80)
    raw = bytearray()

    def pump(sec):
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
                raw.extend(d)
                grid.feed(d)

    def send(data, pause=0.12):
        os.write(master, data)
        time.sleep(pause)
        pump(0.3)

    ok = True
    pump(1.2)
    ok &= check("startup caret is visible without a key", b";7m" in raw or b"[7m" in raw)

    for ch in b"hello":
        send(bytes([ch]), 0.05)
    pump(0.3)
    found = grid.find("hello")
    ok &= check("typed text lands in the input box", found is not None)
    row, col = found if found else (INPUT_ROW, 1)
    ok &= check("typed text is on the input row", row == INPUT_ROW)

    # Click just before the 'e' and type X: the caret moved there.
    click = col + 1
    sgr = lambda b, x, y, final=b"M": b"\x1b[<%d;%d;%d%s" % (b, x + 1, y + 1, final)
    send(sgr(0, click, row))
    send(sgr(0, click, row, b"m"))
    send(b"X", 0.05)
    pump(0.3)
    ok &= check("a click places the caret", grid.find("hXello") is not None)

    # Drag from the 'h' over the next two cells and release: copy them.
    send(sgr(0, col, row))
    send(sgr(32, col + 2, row))
    raw.clear()
    send(sgr(0, col + 2, row, b"m"))
    pump(0.5)
    payload = b"\x1b]52;c;" + base64.b64encode(b"hXe") + b"\x1b\\"
    ok &= check("an input drag copies its text via OSC 52", payload in raw)

    # Submit: the box clears and the placeholder's caret comes back.
    raw.clear()
    send(b"\n")
    pump(1.5)
    ok &= check("the caret returns after a submit", b";7m" in raw or b"[7m" in raw)

    try:
        os.write(master, b"\x03\x03")
    except OSError:
        pass
    time.sleep(0.4)
    try:
        os.kill(pid, 9)
    except ProcessLookupError:
        pass
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass
    shutil.rmtree(TMP, ignore_errors=True)
    print("input repro: " + ("ok" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
