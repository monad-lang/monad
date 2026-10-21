# The large-plan repro: a plan big enough that the old
# byte-by-byte split/glyph walk (quadratic on the compiled runtime) froze
# the TUI for tens of seconds. Asserts the plan paints promptly, the
# /plan dialog opens and closes promptly, and a large bracketed paste into
# the note does not wedge the modal loop.
import fcntl, json, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TMP = tempfile.mkdtemp(prefix="wv_bigplan_repro_")
HOME = TMP + "/home"
TURNS = TMP + "/turns_bigplan.json"

PLAN_LINES = 2000
LINE = "PLAN-LINE-%04d inspect the module and propose the next step in detail"


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
            c = "".join(self.cells[r]).find(needle)
            if c >= 0:
                return r, c
        return None


def strip(s):
    return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)


def spawn():
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
            env["SHUTTLE_MOCK_TURNS"] = TURNS
            os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock"], env)
        except BaseException:
            os._exit(127)
    return master, pid


grid = Grid(24, 80)

def pump(master, sec):
    buf = bytearray()
    end = time.time() + sec
    while time.time() < end:
        r, _, _ = select.select([master], [], [], 0.05)
        if r:
            try:
                d = os.read(master, 65536)
            except OSError:
                break
            if not d:
                break
            buf.extend(d)
            grid.feed(d)
    return buf.decode("utf-8", "replace")


def pump_until(master, needle, timeout):
    """Pump until `needle` (ANSI-stripped) appears; returns (found, seconds, text)."""
    start = time.time()
    buf = ""
    while time.time() - start < timeout:
        buf += pump(master, 0.1)
        if needle in strip(buf):
            return True, time.time() - start, buf
    return False, time.time() - start, buf


def send(master, data, pause=0.1):
    view = memoryview(data)
    for off in range(0, len(view), 1024):
        os.write(master, view[off:off + 1024])
        time.sleep(pause)


def finish(master, pid):
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


def check(name, ok, results, detail=""):
    print(("PASS " if ok else "FAIL ") + name + ((" (" + detail + ")") if detail else ""))
    results.append(ok)


def main():
    if not (os.path.isfile(BIN) and os.access(BIN, os.X_OK)):
        raise SystemExit("missing weaver binary: %s (build with --release)" % BIN)
    os.makedirs(HOME + "/.weaver", exist_ok=True)
    os.makedirs(TMP + "/sessions", exist_ok=True)
    with open(HOME + "/.weaver/config.toml", "w") as f:
        f.write('mode = "plan"\n')

    plan = "\n".join(LINE % i for i in range(PLAN_LINES))
    with open(TURNS, "w") as f:
        json.dump([
            {"message": {"role": "assistant", "content": [{"type": "text", "text": plan}]},
             "usage": {"input_tokens": 1, "output_tokens": 10, "cached_tokens": 0}, "stop": "end_turn"},
        ], f)

    results = []
    master, pid = spawn()
    pump(master, 1.2)
    send(master, b"go\n")
    # The viewport is pinned to the bottom, so the plan's LAST line is the
    # one that proves completion; Home then reaches its first line.
    found, secs, out = pump_until(master, "PLAN-LINE-1999", 10.0)
    check("a large plan paints promptly", found, results, "%.2fs" % secs)
    send(master, b"\x1b[H")
    start = time.time()
    found_head = False
    while time.time() - start < 8.0 and not found_head:
        pump(master, 0.1)
        found_head = grid.find("PLAN-LINE-0000") is not None
    secs_head = time.time() - start
    check("Home reaches the plan's first line", found_head, results, "%.2fs" % secs_head)
    send(master, b"\x1b[F")

    send(master, b"/plan\r")
    found, secs, out3 = pump_until(master, "Plan ready", 10.0)
    check("the plan dialog opens promptly", found, results, "%.2fs" % secs)
    out += out3

    # A large bracketed paste into the note: the dialog's reader must use
    # the linear paste accumulator, not re-decode pending ++ chunk per byte.
    send(master, b"e")
    time.sleep(0.2)
    send(master, b"\x1b[200~" + b"note-" * 2048 + b"\x1b[201~")
    pasted, secs, out4 = pump_until(master, "note-note-", 15.0)
    check("a large note paste completes", pasted, results, "%.2fs" % secs)
    out += out4
    send(master, b"\x1b")
    closed, secs, out5 = pump_until(master, "plan not approved", 8.0)
    check("Esc still closes the dialog after a paste", closed, results, "%.2fs" % secs)
    out += out5

    finish(master, pid)
    shutil.rmtree(TMP, ignore_errors=True)
    print("big-plan repro: " + ("ok" if all(results) else "FAILED"))
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
