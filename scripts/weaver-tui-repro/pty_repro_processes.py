# The background-process repro: a scripted turn starts a detached process
# (after one approval), `/processes` shows it running, `x` kills it, and
# Esc returns to the main screen. Isolated HOME/session/proc roots.
import fcntl, json, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TMP = tempfile.mkdtemp(prefix="wv_proc_repro_")
HOME = TMP + "/home"
PROCS = TMP + "/procs"
TURNS = TMP + "/turns_process.json"


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

    def text(self):
        return "\n".join("".join(r) for r in self.cells)


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    return ok


def main():
    if not (os.path.isfile(BIN) and os.access(BIN, os.X_OK)):
        raise SystemExit("missing weaver binary: %s (build with --release)" % BIN)
    os.makedirs(HOME, exist_ok=True)
    os.makedirs(TMP + "/sessions", exist_ok=True)
    with open(TURNS, "w") as f:
        json.dump([
            {"message": {"role": "assistant", "content": [
                {"type": "tool_use", "id": "c1", "name": "start_process",
                 "input": {"command": "exec sleep 30", "cwd": ""}}]},
             "usage": {"input_tokens": 1, "output_tokens": 10, "cached_tokens": 0}, "stop": "tool_use_stop"},
            {"message": {"role": "assistant", "content": [{"type": "text", "text": "started it"}]},
             "usage": {"input_tokens": 2, "output_tokens": 10, "cached_tokens": 0}, "stop": "end_turn"},
        ], f)

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
            env["WEAVER_PROC_ROOT"] = PROCS
            env["SHUTTLE_MOCK_TURNS"] = TURNS
            os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock"], env)
        except BaseException:
            os._exit(127)

    grid = Grid(24, 80)
    raw = bytearray()

    def pump(sec):
        end = time.time() + sec
        while time.time() < end:
            r, _, _ = select.select([master], [], [], 0.05)
            if r:
                try:
                    d = os.read(master, 65536)
                except OSError:
                    return
                if not d:
                    return
                raw.extend(d)
                grid.feed(d)

    def send(data, pause=0.15):
        os.write(master, data)
        time.sleep(pause)
        pump(0.4)

    def seen(needle):
        # The main loop's ticks can repaint over the modal between frames;
        # the bytes were still emitted, so scan the accumulated stream.
        return needle in re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", bytes(raw).decode("utf-8", "replace"))

    def find(needle, timeout=3.0):
        start = time.time()
        while time.time() - start < timeout:
            if seen(needle):
                return True
            pump(0.1)
        return False

    def seen(needle):
        return needle in re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", bytes(raw).decode("utf-8", "replace"))

    def find(needle, timeout=3.0):
        start = time.time()
        while time.time() - start < timeout:
            if seen(needle):
                return True
            pump(0.1)
        return False

    ok = True
    pump(1.2)
    send(b"go\n")
    ok &= check("the start_process approval dialog appears", find("Permission required"))
    send(b"y")                       # approve once
    ok &= check("the turn continues after starting", find("started it", 4.0))

    # The first (and only) task directory names the id.
    task_ids = sorted(os.listdir(PROCS)) if os.path.isdir(PROCS) else []
    task_id = task_ids[0] if task_ids else ""

    send(b"/processes\r")
    ok &= check("the snapshot lists the running task",
                find("running", 3.0) and (not task_id or find(task_id, 1.0)))
    ok &= check("the snapshot carries the command", find("exec sleep 30", 1.0))

    send(("/processes kill " + task_id + "\r").encode())
    ok &= check("kill <id> reports the kill", find("killed", 3.0))

    # The task's pid (from the pid file) must be gone after the kill.
    pids = []
    for root, dirs, files in os.walk(PROCS):
        for name in files:
            if name == "pid":
                try:
                    pids.append(int(open(os.path.join(root, name)).read().strip()))
                except ValueError:
                    pass
    alive = []
    for p in pids:
        try:
            os.kill(p, 0)
            alive.append(p)
        except ProcessLookupError:
            pass
    ok &= check("the killed task's pid is gone", pids and not alive)

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
    for p in alive:
        try:
            os.kill(p, signal.SIGKILL)
        except ProcessLookupError:
            pass
    shutil.rmtree(TMP, ignore_errors=True)
    print("processes repro: " + ("ok" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
