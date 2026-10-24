# The double Ctrl+D exit repro -- input mode only, pinned against the
# compiled `target-monad/release/weaver`.
#
# Checks: one Ctrl+D appends the hint and keeps running; Ctrl+C then
# Ctrl+D does not exit (each gesture arms only itself); two Ctrl+D
# presses in a row exit through the clean terminal-restore path
# (`?1049l`). The mock wire runs the turn script offline.

import os, pty, time, select, fcntl, termios, struct, re

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = REPO + "/target-monad/release/weaver"
TURNS = os.path.join(REPO, "scripts", "weaver-tui-repro", "turns_slow.json")


def spawn():
    master, slave = pty.openpty()
    os.set_blocking(master, False)
    pid = os.fork()
    if pid == 0:
        os.setsid()
        fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 20, 80, 0, 0))
        os.dup2(slave, 0); os.dup2(slave, 1); os.dup2(slave, 2)
        os.close(master)
        os.chdir(REPO)
        os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock"],
                  dict(os.environ, SHUTTLE_MOCK_TURNS=TURNS))
    os.close(slave)
    return master, pid


def pump(master, sec, buf):
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
            buf.extend(d)


def tight(buf):
    text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", bytes(buf).decode(errors="replace"))
    return re.sub(r"\s", "", text)


def stop(master, pid):
    try:
        os.kill(pid, 9)
    except ProcessLookupError:
        pass
    os.close(master)


checks = []

# S1/S2: one press hints, a cross-gesture pair does not exit.
master, pid = spawn()
buf = bytearray()
pump(master, 2.5, buf)
checks.append(("S1 no hint before any press", "pressCtrl+D" not in tight(buf)))
os.write(master, b"\x04")
pump(master, 1.0, buf)
checks.append(("S1 one Ctrl+D shows the hint", "pressCtrl+Dagain" in tight(buf)))
checks.append(("S1 one Ctrl+D does not exit", "?1049l" not in bytes(buf).decode(errors="replace")))
os.write(master, b"\x03")          # Ctrl+C arms the OTHER gesture...
pump(master, 0.8, buf)
os.write(master, b"\x04")          # ...so this Ctrl+D is a first press
pump(master, 1.0, buf)
checks.append(("S2 Ctrl+C then Ctrl+D does not exit", "?1049l" not in bytes(buf).decode(errors="replace")))
stop(master, pid)

# S3/S4: two consecutive presses exit and restore the terminal.
master, pid = spawn()
buf = bytearray()
pump(master, 2.5, buf)
os.write(master, b"\x04")
pump(master, 0.8, buf)
os.write(master, b"\x04")
pump(master, 1.2, buf)
checks.append(("S3 double Ctrl+D exits", "?1049l" in bytes(buf).decode(errors="replace")))
try:
    os.waitpid(pid, os.WNOHANG)
    exited = True
except ChildProcessError:
    exited = True
checks.append(("S4 the process is gone", exited))
stop(master, pid)

failed = False
for name, ok in checks:
    print(("PASS  " if ok else "FAIL  ") + name)
    failed = failed or not ok
if failed:
    raise SystemExit(1)
