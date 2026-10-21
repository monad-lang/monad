# The confirmation-dialog repro: a permission prompt with arrows + Enter,
# a note attached to a denial, and the plan-review dialog's revise note.
# Isolated HOME/WEAVER_SESSION_ROOT; mock wire; no /tmp/wv_repro paths.
#
# A Grid (copied from pty_repro_input.py) renders the byte stream, so the
# checks can assert on the SCREEN: after a confirm/cancel the dialog text
# must be gone, and the plan dialog's revise path must leave the app
# responsive (the input box accepts typing again).
import fcntl, json, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TMP = tempfile.mkdtemp(prefix="wv_dialog_repro_")
HOME = TMP + "/home"
NOTE = TMP + "/note.txt"
EDIT_TURNS = TMP + "/turns_edit.json"
PLAN_TURNS = TMP + "/turns_plan.json"

def strip(s):
    return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)

def tight(s):
    return re.sub(r"[ \r\n\t]", "", strip(s))


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


GRID = None

def spawn(env_extra, fixture):
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
            env["SHUTTLE_MOCK_TURNS"] = fixture
            env.update(env_extra)
            os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock"], env)
        except BaseException:
            os._exit(127)
    return master, pid

def pump(master, sec):
    buf = bytearray()
    end = time.time() + sec
    while time.time() < end:
        r, _, _ = select.select([master], [], [], 0.1)
        if r:
            try:
                d = os.read(master, 65536)
            except OSError:
                break
            if not d:
                break
            buf.extend(d)
            if GRID is not None:
                GRID.feed(d)
    return buf.decode("utf-8", "replace")

def run_keys(master, keys, sec=0.5):
    out = ""
    for k in keys:
        os.write(master, k)
        time.sleep(0.12)
        out += pump(master, sec)
    return out

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

def check(name, ok, results):
    print(("PASS " if ok else "FAIL ") + name)
    results.append(ok)

INPUT_ROW = 21  # 0-based; a 24x80 terminal's input content row

def main():
    global GRID
    if not (os.path.isfile(BIN) and os.access(BIN, os.X_OK)):
        raise SystemExit("missing weaver binary: %s (build with --release)" % BIN)
    os.makedirs(HOME, exist_ok=True)
    os.makedirs(TMP + "/sessions", exist_ok=True)
    results = []

    # A write pick -> a manual-mode permission dialog whose safe default is
    # Deny; the second mock turn is the final text.
    with open(NOTE, "w") as f:
        f.write("hi")
    with open(EDIT_TURNS, "w") as f:
        json.dump([
            {"message": {"role": "assistant", "content": [
                {"type": "tool_use", "id": "c1", "name": "edit",
                 "input": {"path": NOTE, "new_content": "hello world", "expected_content": "hi"}}]},
             "usage": {"input_tokens": 1, "output_tokens": 10, "cached_tokens": 0}, "stop": "tool_use_stop"},
            {"message": {"role": "assistant", "content": [{"type": "text", "text": "wrote it"}]},
             "usage": {"input_tokens": 2, "output_tokens": 10, "cached_tokens": 0}, "stop": "end_turn"},
        ], f)

    # 1. Deny with a note: e -> text -> Enter (leaves the field) -> n.
    master, pid = spawn({}, EDIT_TURNS)
    GRID = Grid(24, 80)
    pump(master, 1.2)
    out = pump(master, 0.2) + run_keys(master, [b"go\n"], 1.2)
    check("permission dialog appears with its options",
          "Permission required" in strip(out) and "Approve once" in strip(out)
          and "Deny" in strip(out), results)
    out += run_keys(master, [b"e", b"please keep it", b"\r", b"n"], 0.5)
    out += pump(master, 1.5)
    check("a denied pick carries the note to the model",
          "denied: please keep it" in strip(out), results)
    check("the denied edit did not run", open(NOTE).read() == "hi", results)
    check("the turn continues after a denial", "wrote it" in strip(out), results)
    check("the dialog is gone after the denial",
          GRID.find("Permission required") is None and GRID.find("Approve once") is None, results)
    finish(master, pid)

    # 2. Arrow selection: default Deny -> Always -> Approve once, Enter.
    with open(NOTE, "w") as f:
        f.write("hi")
    master, pid = spawn({}, EDIT_TURNS)
    GRID = Grid(24, 80)
    pump(master, 1.2)
    run_keys(master, [b"go\n"], 1.2)
    out = run_keys(master, [b"\x1b[A", b"\x1b[A", b"\r"], 0.6)
    out += pump(master, 1.8)
    check("arrow selection + Enter approves the edit",
          open(NOTE).read() == "hello world" and "wrote it" in strip(out), results)
    check("the dialog is gone after the approval",
          GRID.find("Permission required") is None and GRID.find("Approve once") is None, results)
    finish(master, pid)

    # 3. Plan review: plan mode + a plan turn, then /plan opens the dialog;
    #    a revise note fills the input box.
    os.makedirs(HOME + "/.weaver", exist_ok=True)
    with open(HOME + "/.weaver/config.toml", "w") as f:
        f.write('mode = "plan"\n')
    with open(PLAN_TURNS, "w") as f:
        json.dump([
            {"message": {"role": "assistant", "content": [{"type": "text", "text": "PLAN: do the thing"}]},
             "usage": {"input_tokens": 1, "output_tokens": 10, "cached_tokens": 0}, "stop": "end_turn"},
        ], f)
    master, pid = spawn({}, PLAN_TURNS)
    GRID = Grid(24, 80)
    pump(master, 1.2)
    run_keys(master, [b"go\n"], 1.2)
    out = run_keys(master, [b"/plan", b"\r"], 1.0)
    out += pump(master, 1.0)
    check("the plan dialog shows the plan",
          "Plan ready" in strip(out) and "PLAN: do the thing" in strip(out)
          and "Approve and execute" in strip(out), results)
    out = run_keys(master, [b"e", b"fix the tests too", b"\r", b"r"], 0.6)
    out += pump(master, 1.0)
    check("revise with a note fills the input box", "fix the tests too" in strip(out), results)
    check("the plan dialog is gone after revise", GRID.find("Plan ready") is None, results)
    located = GRID.find("fix the tests too")
    check("the note sits on the input row", located is not None and located[0] == INPUT_ROW, results)
    # The revise path used to leave turn_pending/modal stuck; a keypress
    # must still edit the box.
    run_keys(master, [b"!"], 0.3)
    check("the app is responsive after revise", GRID.find("fix the tests too!") is not None, results)
    finish(master, pid)

    shutil.rmtree(TMP, ignore_errors=True)
    print("dialog repro: " + ("ok" if all(results) else "FAILED"))
    return 0 if all(results) else 1

if __name__ == "__main__":
    sys.exit(main())
