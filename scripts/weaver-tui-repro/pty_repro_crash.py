# Crash-log repro: run weaver, SIGKILL it, restart, and assert the second
# run reports the first as an unclean exit (and leaves process_exit on a
# clean exit). Isolated HOME/session/log roots.
import fcntl, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TMP = tempfile.mkdtemp(prefix="wv_crash_repro_")
HOME = TMP + "/home"
LOGDIR = TMP + "/debug"
FIXTURE = os.path.join(REPO, "scripts/weaver-tui-repro/turns_select.json")


def spawn(log_path):
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
            env["WEAVER_LOG_DIR"] = LOGDIR
            env["WEAVER_DEBUG_LOG"] = log_path
            env["SHUTTLE_MOCK_TURNS"] = FIXTURE
            os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock"], env)
        except BaseException:
            os._exit(127)
    return master, pid


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
    return buf.decode("utf-8", "replace")


def strip(s):
    return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)


def read(path):
    try:
        return open(path, "r", errors="replace").read()
    except OSError:
        return ""


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    return ok


def main():
    if not (os.path.isfile(BIN) and os.access(BIN, os.X_OK)):
        raise SystemExit("missing weaver binary: %s (build with --release)" % BIN)
    os.makedirs(HOME, exist_ok=True)
    os.makedirs(TMP + "/sessions", exist_ok=True)
    run1 = LOGDIR + "/run1.log"
    run2 = LOGDIR + "/run2.log"

    ok = True
    master, pid = spawn(run1)
    out1 = pump(master, 1.8)
    ok &= check("the first run starts and logs", "ev=process_start" in read(run1))

    os.kill(pid, signal.SIGKILL)
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass
    ok &= check("the killed run has no exit marker", "ev=process_exit" not in read(run1))

    master, pid = spawn(run2)
    out2 = pump(master, 2.0)
    warned = "previous session ended unexpectedly" in strip(out2)
    ok &= check("the restart warns about the previous crash", warned)
    if not warned:
        print("DEBUG out2:", strip(out2)[:900].replace("\n", "|"))
        print("DEBUG log2:", read(run2)[:500].replace("\n", "|"))
    ok &= check("the restart logs crash_detected", "ev=crash_detected" in read(run2))

    try:
        os.write(master, b"/quit\r")
    except OSError:
        pass
    pump(master, 1.5)
    try:
        os.kill(pid, 9)
    except ProcessLookupError:
        pass
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass
    ok &= check("a clean exit writes process_exit", "ev=process_exit" in read(run2))

    shutil.rmtree(TMP, ignore_errors=True)
    print("crash repro: " + ("ok" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
