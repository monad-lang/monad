# Resize repro: a real pty grows and shrinks while weaver runs, and a tiny
# ANSI grid emulator reconstructs what the terminal would show. Pins:
#   * ESC[2J is written on every geometry change (the clear that removes
#     old borders/glyphs -- a blank-cell diff never can),
#   * the bottom border lands on the NEW last transcript row,
#   * a long wrapped reply re-wraps at the new content width.
#
# Uses an isolated HOME and WEAVER_SESSION_ROOT, and the mock wire.
import fcntl, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TMP = tempfile.mkdtemp(prefix="wv_resize_repro_")
HOME = TMP + "/home"
FIXTURE = os.path.join(REPO, "scripts/weaver-tui-repro/turns_resize.json")

class Grid:
    """A minimal terminal: cursor moves, ESC[2J, printable UTF-8, SGR
    ignored. Enough to read the app's frames back."""
    def __init__(self, rows, cols):
        self.rows, self.cols = rows, cols
        self.cells = [[" "] * cols for _ in range(rows)]
        self.row = self.col = 0
        self.state = "text"
        self.seq = ""
        self.utf8 = b""
        self.clears = 0

    def resize(self, rows, cols):
        self.rows, self.cols = rows, cols
        self.cells = [[" "] * cols for _ in range(rows)]
        self.row = self.col = 0

    def put(self, ch):
        if 0 <= self.row < self.rows and 0 <= self.col < self.cols:
            self.cells[self.row][self.col] = ch
        self.col += 1

    def csi(self, final):
        params = self.seq
        if final == "H":
            parts = params.split(";") if params else []
            r = int(parts[0]) - 1 if len(parts) > 0 and parts[0] else 0
            c = int(parts[1]) - 1 if len(parts) > 1 and parts[1] else 0
            self.row, self.col = r, c
        elif final == "J":
            if params in ("", "2"):
                self.cells = [[" "] * self.cols for _ in range(self.rows)]
                self.clears += 1
            if params == "":
                self.row, self.col = 0, 0
        elif final == "m" or final in "hl":
            pass
        self.seq = ""
        self.state = "text"

    def feed(self, data):
        for b in data:
            if self.state == "csi":
                ch = bytes([b]).decode("latin-1")
                if "@" <= ch <= "~":
                    self.csi(ch)
                else:
                    self.seq += ch
                continue
            if self.state == "osc":
                if b == 7:  # BEL
                    self.state = "text"
                continue
            if self.state == "esc":
                ch = bytes([b]).decode("latin-1")
                if ch == "[":
                    self.state, self.seq = "csi", ""
                elif ch == "]":
                    self.state = "osc"
                else:
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

    def text_row(self, r):
        return "".join(self.cells[r]) if 0 <= r < self.rows else ""

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
            fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 30, 80, 0, 0))
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

    grid = Grid(30, 80)
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

    ok = True
    pump(1.5)
    ok &= check("initial bottom border at row 26", "╰" in grid.text_row(25) and "╯" in grid.text_row(25))

    os.write(master, b"go\n")
    pump(2.0)
    ok &= check("reply rendered at the initial width", any("x" in grid.text_row(r) for r in range(1, 25)))

    before = len(raw)
    fcntl.ioctl(master, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 40, 0, 0))
    os.kill(pid, signal.SIGWINCH)
    grid.resize(24, 40)
    pump(1.5)
    post = bytes(raw[before:])
    ok &= check("shrink clears the screen (ESC[2J)", b"\x1b[2J" in post)
    ok &= check("shrunken bottom border at row 20", "╰" in grid.text_row(19) and "╯" in grid.text_row(19))
    rows_with_x = sum(1 for r in range(1, 19) if "x" in grid.text_row(r))
    ok &= check("reply re-wrapped to the 36-cell content width (%d rows)" % rows_with_x, rows_with_x >= 5)

    before = len(raw)
    fcntl.ioctl(master, termios.TIOCSWINSZ, struct.pack("HHHH", 32, 100, 0, 0))
    os.kill(pid, signal.SIGWINCH)
    grid.resize(32, 100)
    pump(1.5)
    post = bytes(raw[before:])
    ok &= check("grow clears the screen (ESC[2J)", b"\x1b[2J" in post)
    ok &= check("grown bottom border at row 28", "╰" in grid.text_row(27) and "╯" in grid.text_row(27))
    rows_with_x = sum(1 for r in range(1, 27) if "x" in grid.text_row(r))
    ok &= check("reply re-wrapped to the 96-cell content width (%d rows)" % rows_with_x, 2 <= rows_with_x <= 4)

    try:
        os.write(master, b"\x03\x03")
    except OSError:
        pass
    pump(0.6)
    try:
        os.kill(pid, 9)
    except ProcessLookupError:
        pass
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass
    shutil.rmtree(TMP, ignore_errors=True)
    print("resize repro: " + ("ok" if ok else "FAILED"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
