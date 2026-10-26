# The /resume picker repro: a bare /resume opens a dialog of saved
# sessions with their names and descriptions, marks the current one,
# pages past the first screen, and loads the chosen session's transcript.
#
# Sessions are synthesized (meta.json + one transcript block each), so the
# run needs no provider and no model turns; HOME and WEAVER_SESSION_ROOT
# are isolated under the run's temp dir.
#
# A Grid (copied from pty_repro_dialogs.py) renders the byte stream, so the
# checks assert on the SCREEN: the dialog's text appears, the page rows
# change, and Esc leaves the app responsive.
import fcntl, json, os, pty, re, select, shutil, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TMP = os.environ.get("WV_REPRO_TMP") or tempfile.mkdtemp(prefix="wv_resume_repro_")
HOME = TMP + "/home"
SESSIONS = TMP + "/sessions"

INPUT_ROW = 21  # 0-based; a 24x80 terminal's input content row


def strip(s):
    return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)


def tight(s):
    return re.sub(r"[ \r\n\t]", "", strip(s))


class Grid:
    """Cursor moves, ESC[2J, printable UTF-8; SGR ignored."""

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
                self.row += 1
                self.col = 0
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
            if needle in "".join(self.cells[r]):
                return r, "".join(self.cells[r]).find(needle)
        return None


GRID = None


def synth(sid, name, description, updated, marker, with_titles=True):
    """Write one session directory: meta.json plus one transcript block."""
    d = os.path.join(SESSIONS, sid)
    os.makedirs(os.path.join(d, "transcript"), exist_ok=True)
    os.makedirs(os.path.join(d, "history"), exist_ok=True)
    lines = [{"text": marker, "user": False, "detail": False}]
    with open(os.path.join(d, "transcript", "000000000001.json"), "w") as f:
        json.dump({"version": 2, "seq": 1, "start": 0, "count": 1, "lines": lines}, f)
    with open(os.path.join(d, "transcript", "index.json"), "w") as f:
        json.dump({"version": 1, "total": 1, "next_seq": 2,
                   "blocks": [{"seq": 1, "start": 0, "count": 1}]}, f)
    meta = {"version": 1, "created": updated, "updated": updated, "history_next": 1,
            "session": {"config": {"base_url": "mock", "model": "mock",
                                   "api_key_env": "WEAVER_UNUSED_KEY", "max_tokens": 8,
                                   "wire": "mock"},
                        "system_prompt": "s", "tools": [], "history": [],
                        "turns": 1,
                        "spent": {"input_tokens": 0, "output_tokens": 0,
                                  "cached_tokens": 0}}}
    if with_titles:
        meta["name"] = name
        meta["description"] = description
    with open(os.path.join(d, "meta.json"), "w") as f:
        json.dump(meta, f)


def spawn(resume):
    master, slave = pty.openpty()
    os.set_blocking(master, False)
    pid = os.fork()
    if pid == 0:
        try:
            os.setsid()
            fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 80, 0, 0))
            os.dup2(slave, 0)
            os.dup2(slave, 1)
            os.dup2(slave, 2)
            os.close(master)
            os.chdir(TMP)
            env = dict(os.environ)
            env.pop("NO_COLOR", None)
            env["HOME"] = HOME
            env["WEAVER_SESSION_ROOT"] = SESSIONS
            os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock",
                            "--resume", resume], env)
        except BaseException:
            os._exit(127)
    return master, pid


def pump(master, sec):
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
            if GRID is not None:
                GRID.feed(d)


def run_keys(master, keys, sec=0.5):
    for k in keys:
        os.write(master, k)
        time.sleep(0.12)
        pump(master, sec)


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


def close_dialog(master):
    run_keys(master, [b"\x1b"], 0.6)
    pump(master, 0.6)


def main():
    global GRID
    if not (os.path.isfile(BIN) and os.access(BIN, os.X_OK)):
        raise SystemExit("missing weaver binary: %s (build with --release)" % BIN)
    os.makedirs(HOME, exist_ok=True)
    os.makedirs(SESSIONS, exist_ok=True)
    results = []

    synth("s-alpha", "Alpha work", "the first task", 1000, "ALPHA-TRANSCRIPT")
    synth("s-beta", "Beta work", "the second task", 2000, "BETA-TRANSCRIPT")

    # 1. The dialog lists both sessions, marks the current one, and shows
    #    each description; Esc leaves the app responsive.
    master, pid = spawn("s-beta")
    GRID = Grid(24, 80)
    pump(master, 2.0)
    run_keys(master, [b"/resume", b"\r"], 1.0)
    pump(master, 1.0)
    check("the picker dialog opens", GRID.find("Resume a session") is not None, results)
    check("the current session is listed", GRID.find("Beta work") is not None, results)
    check("the current session is marked", GRID.find("(current)") is not None, results)
    check("another session is listed", GRID.find("Alpha work") is not None, results)
    check("descriptions are shown",
          GRID.find("the first task") is not None and GRID.find("the second task") is not None,
          results)
    close_dialog(master)
    check("the dialog is gone after Esc", GRID.find("Resume a session") is None, results)
    run_keys(master, [b"!"], 0.4)
    check("the app is responsive after Esc",
          GRID.find("!") is not None and GRID.find("!")[0] == INPUT_ROW, results)
    finish(master, pid)

    # 2. Choosing a session loads it: the older session's transcript lands.
    master, pid = spawn("s-beta")
    GRID = Grid(24, 80)
    pump(master, 2.0)
    run_keys(master, [b"/resume", b"\r"], 1.0)
    pump(master, 1.0)
    run_keys(master, [b"\x1b[B", b"\r"], 0.6)
    pump(master, 2.0)
    check("the chosen session's transcript is restored",
          GRID.find("ALPHA-TRANSCRIPT") is not None, results)
    check("the picker closed after choosing", GRID.find("Resume a session") is None, results)
    finish(master, pid)

    # 3. Ten sessions page: the first screen has the 8 newest and an
    #    "Older sessions" row; the second screen has the two oldest.
    shutil.rmtree(SESSIONS, ignore_errors=True)
    os.makedirs(SESSIONS, exist_ok=True)
    for i in range(10):
        synth("s-%02d" % i, "session %02d" % i, "desc %02d" % i, 100 + i * 10, "MARK-%02d" % i)
    master, pid = spawn("s-09")
    GRID = Grid(24, 80)
    pump(master, 2.0)
    run_keys(master, [b"/resume", b"\r"], 1.0)
    pump(master, 1.0)
    check("the first page shows the newest sessions", GRID.find("session 02") is not None, results)
    check("the first page hides the oldest sessions",
          GRID.find("session 00") is None and GRID.find("session 01") is None, results)
    check("the first page offers an older page",
          GRID.find("Older sessions") is not None, results)
    run_keys(master, [b"\x1b[B"] * 8 + [b"\r"], 0.5)
    pump(master, 1.5)
    check("the older page shows the oldest sessions",
          GRID.find("session 00") is not None and GRID.find("session 01") is not None, results)
    check("the older page offers a newer page",
          GRID.find("Newer sessions") is not None, results)
    close_dialog(master)
    check("the paged dialog closes", GRID.find("Resume a session") is None, results)
    finish(master, pid)

    shutil.rmtree(TMP, ignore_errors=True)
    print("RESUME PICKER REPRO: " + ("ALL PASS" if all(results) else "FAILED"))
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
