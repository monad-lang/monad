# The confirmation-dialog repro: a permission prompt with arrows + Enter,
# a note attached to a denial, and the plan-review dialog's revise note.
# Isolated HOME/WEAVER_SESSION_ROOT; mock wire; no /tmp/wv_repro paths.
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

def main():
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
    finish(master, pid)

    # 2. Arrow selection: default Deny -> Always -> Approve once, Enter.
    with open(NOTE, "w") as f:
        f.write("hi")
    master, pid = spawn({}, EDIT_TURNS)
    pump(master, 1.2)
    run_keys(master, [b"go\n"], 1.2)
    out = run_keys(master, [b"\x1b[A", b"\x1b[A", b"\r"], 0.6)
    out += pump(master, 1.8)
    check("arrow selection + Enter approves the edit",
          open(NOTE).read() == "hello world" and "wrote it" in strip(out), results)
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
    pump(master, 1.2)
    run_keys(master, [b"go\n"], 1.2)
    out = run_keys(master, [b"/plan", b"\r"], 1.0)
    out += pump(master, 1.0)
    check("the plan dialog shows the plan",
          "Plan ready" in strip(out) and "PLAN: do the thing" in strip(out)
          and "Approve and execute" in strip(out), results)
    out = run_keys(master, [b"e", b"fix the tests too", b"\r", b"r"], 0.6)
    out += pump(master, 0.8)
    check("revise with a note fills the input box", "fix the tests too" in strip(out), results)
    finish(master, pid)

    shutil.rmtree(TMP, ignore_errors=True)
    print("dialog repro: " + ("ok" if all(results) else "FAILED"))
    return 0 if all(results) else 1

if __name__ == "__main__":
    sys.exit(main())
