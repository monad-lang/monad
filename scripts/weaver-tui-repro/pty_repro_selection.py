# Mouse-selection repro: drag over transcript text, see the reverse-video
# highlight, and receive the copied text as an OSC 52 clipboard sequence.
# Uses an isolated HOME/WEAVER_SESSION_ROOT and the mock wire.
import base64, fcntl, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TMP = tempfile.mkdtemp(prefix="wv_select_repro_")
HOME = TMP + "/home"
FIXTURE = os.path.join(REPO, "scripts/weaver-tui-repro/turns_select.json")

class Grid:
    """Cursor moves, ESC[2J, printable UTF-8; SGR ignored. Wide glyphs are
    one dict key at their left cell and an empty cell at the right."""
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
                self.cells[self.row][self.col + 1] = ""  # continuation
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

    ok = True
    pump(1.2)
    ok &= check("mouse drag reporting enabled (?1002h)", b"\x1b[?1002h" in bytes(raw))

    os.write(master, b"go\n")
    pump(2.0)
    spot = grid.find("hello")
    ok &= check("reply rendered", spot is not None)
    if spot is None:
        cleanup(master, pid)
        return 1

    r, c = spot
    # SGR is 1-based (col; row). Press at 'h', drag over 5 cells, release.
    os.write(master, ("\x1b[<0;%d;%dM" % (c + 1, r + 1)).encode())
    pump(0.2)
    os.write(master, ("\x1b[<32;%d;%dM" % (c + 6, r + 1)).encode())
    pump(0.3)
    marked = len(raw)
    os.write(master, ("\x1b[<0;%d;%dm" % (c + 6, r + 1)).encode())
    pump(0.8)

    stream = bytes(raw)
    ok &= check("drag paints a reverse-video highlight",
                b"\x1b[7m" in stream[:marked] or b";7m" in stream[:marked])
    payload = b"\x1b]52;c;" + base64.b64encode("hello".encode()) + b"\x1b\\"
    ok &= check("release copies 'hello' via OSC 52", payload in stream[marked:])

    # Wide characters: pick 日本 on the same row (each occupies two cells).
    spot2 = grid.find("日本")
    ok &= check("wide reply rendered", spot2 is not None)
    if spot2 is not None:
        r2, c2 = spot2
        marked2 = len(raw)
        os.write(master, ("\x1b[<0;%d;%dM" % (c2 + 1, r2 + 1)).encode())
        pump(0.2)
        os.write(master, ("\x1b[<32;%d;%dM" % (c2 + 4, r2 + 1)).encode())
        pump(0.3)
        os.write(master, ("\x1b[<0;%d;%dm" % (c2 + 4, r2 + 1)).encode())
        pump(0.8)
        payload2 = b"\x1b]52;c;" + base64.b64encode("日本".encode()) + b"\x1b\\"
        ok &= check("release copies the wide glyphs via OSC 52", payload2 in bytes(raw)[marked2:])

    cleanup(master, pid)
    shutil.rmtree(TMP, ignore_errors=True)
    print("selection repro: " + ("ok" if ok else "FAILED"))
    return 0 if ok else 1

def cleanup(master, pid):
    try:
        os.write(master, b"\x03\x03")
    except OSError:
        pass
    time.sleep(0.3)
    try:
        os.kill(pid, 9)
    except ProcessLookupError:
        pass
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass

if __name__ == "__main__":
    sys.exit(main())
