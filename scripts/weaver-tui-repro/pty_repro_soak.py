# Long-run soak: the TUI event loop must not grow the native stack.
#
# Every frame of `motes/tui/src/tui.mo`'s loop runs through a chain of IO
# do-binds, and the compiled backend calls each continuation inside
# `monad_io_bind`'s C frame (the tail-call rewrite covers only pure
# self-recursion). Before the segmented loop, the stack grew per frame and a
# long session died with SIGSEGV; the 128 MB default only delayed it.
#
# This driver makes the failure fast and deterministic:
#   MONAD_STACK_BYTES=1048576     a 1 MiB stack instead of 128 MiB
#   MONAD_TUI_FRAME_BUDGET=200    unwind every 200 frames (the fix's knob)
# and then drives several thousand frames (one key each). The pre-fix binary
# dies within the burst; the fixed one survives, keeps answering keys, and
# still restores the terminal on exit.
#
# It also samples VmRSS after the burst and reports it (the async-turn RSS
# growth's baseline): a bound that is only advisory today, printed so a
# regression is visible in the CI log.
#
# Usage: python3 pty_repro_soak.py [--keys 3000] [--stack 1048576]
#        WV_BIN=/path/to/weaver python3 pty_repro_soak.py
import fcntl, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TURNS = os.path.join(REPO, "scripts", "weaver-tui-repro", "turns_select.json")

KEYS = 3000
STACK = "1048576"
BUDGET = "200"


def parse_args(argv):
    global KEYS, STACK, BUDGET
    i = 1
    while i < len(argv):
        a = argv[i]
        if a == "--keys" and i + 1 < len(argv):
            KEYS = int(argv[i + 1]); i += 2
        elif a == "--stack" and i + 1 < len(argv):
            STACK = argv[i + 1]; i += 2
        elif a == "--budget" and i + 1 < len(argv):
            BUDGET = argv[i + 1]; i += 2
        else:
            raise SystemExit("unknown argument: %s" % a)


def spawn(tmp):
    master, slave = pty.openpty()
    os.set_blocking(master, False)
    pid = os.fork()
    if pid == 0:
        try:
            os.setsid()
            fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 80, 0, 0))
            os.dup2(slave, 0); os.dup2(slave, 1); os.dup2(slave, 2)
            os.close(master)
            os.chdir(tmp)
            env = dict(os.environ)
            env.pop("NO_COLOR", None)
            env["HOME"] = tmp + "/home"
            env["WEAVER_SESSION_ROOT"] = tmp + "/sessions"
            env["WEAVER_LOG_DIR"] = tmp + "/debug"
            env["SHUTTLE_MOCK_TURNS"] = TURNS
            env["MONAD_STACK_BYTES"] = STACK
            env["MONAD_TUI_FRAME_BUDGET"] = BUDGET
            os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock"], env)
        except BaseException:
            os._exit(127)
    os.close(slave)
    return master, pid


def drain(master, buf, sec):
    end = time.time() + sec
    while time.time() < end:
        r, _, _ = select.select([master], [], [], 0.02)
        if r:
            try:
                d = os.read(master, 65536)
            except OSError:
                return False
            if not d:
                return False
            buf.extend(d)
    return True


def alive(pid):
    try:
        got, _ = os.waitpid(pid, os.WNOHANG)
        return got == 0
    except ChildProcessError:
        return False


def wait_exit(pid, timeout):
    """Reap the child, polling briefly. Under CI load it can take a moment
    past the last drain to leave; a single WNOHANG check is a race."""
    end = time.time() + timeout
    while time.time() < end:
        try:
            got, status = os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            return True, 0
        if got == pid:
            return True, status
        time.sleep(0.05)
    return False, 0


def rss_kb(pid):
    try:
        with open("/proc/%d/status" % pid) as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
    except OSError:
        pass
    return 0


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    return ok


def main():
    parse_args(sys.argv)
    if not (os.path.isfile(BIN) and os.access(BIN, os.X_OK)):
        raise SystemExit("missing weaver binary: %s (build with --release)" % BIN)
    tmp = tempfile.mkdtemp(prefix="wv_soak_")
    os.makedirs(tmp + "/home", exist_ok=True)
    os.makedirs(tmp + "/sessions", exist_ok=True)
    os.makedirs(tmp + "/debug", exist_ok=True)
    ok = True
    master, pid = spawn(tmp)
    buf = bytearray()
    try:
        ok &= check("the initial frame renders", drain(master, buf, 1.5) and len(buf) > 0)

        # One key per frame, paced so the reader does not coalesce them into a
        # single batch: the point is the NUMBER of loop iterations.
        sent = 0
        deadline = time.time() + 120
        while sent < KEYS and time.time() < deadline:
            try:
                os.write(master, b"x")
                sent += 1
            except OSError:
                break
            time.sleep(0.004)
            if sent % 100 == 0:
                if not drain(master, buf, 0.002):
                    break
                if not alive(pid):
                    break
            if sent % 1000 == 0:
                print("INFO frames=%d VmRSS=%d kB" % (sent, rss_kb(pid)))

        ok &= check("%d frames without a segfault (stack %s, budget %s)" % (sent, STACK, BUDGET),
                    sent == KEYS and alive(pid))

        # Still answering: Enter submits the typed line (an empty model call
        # is not made -- the mock wire would serve a turn; Ctrl+U clears it
        # instead), then the double Ctrl+C exits and restores.
        os.write(master, b"\x15")  # Ctrl+U: clear the long input (one frame)
        drain(master, buf, 0.3, )
        ok &= check("answers a key after the burst", alive(pid))
        rss = rss_kb(pid)
        print("INFO VmRSS after %d frames: %d kB" % (sent, rss))

        os.write(master, b"\x03")
        drain(master, buf, 0.4)
        os.write(master, b"\x03")
        drain(master, buf, 1.5)
        text = bytes(buf).decode("utf-8", "replace")
        ok &= check("the double Ctrl+C exits through the restore path", "\x1b[?1049l" in text)
        exited, status = wait_exit(pid, 6.0)
        ok &= check("the process exited", exited)
        ok &= check("exit status is 0", exited and os.WIFEXITED(status) and os.WEXITSTATUS(status) == 0)
    finally:
        if alive(pid):
            try:
                os.kill(pid, signal.SIGKILL)
                os.waitpid(pid, 0)
            except (ProcessLookupError, ChildProcessError):
                pass
        try:
            os.close(master)
        except OSError:
            pass
        shutil.rmtree(tmp, ignore_errors=True)
    print("SOAK " + ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
