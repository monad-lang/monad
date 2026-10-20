import os, pty, sys, time, select, fcntl, termios, struct, re as _re

def strip(s):
    return _re.sub(r"\x1b\[[0-9;]*[A-Za-z]", " ", s)

def striptight(s):
    return _re.sub(r"\s", "", strip(s))

REPO = "/home/anderscs/src/monad-weaver"
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")

master, slave = pty.openpty()
os.set_blocking(master, False)
pid = os.fork()
if pid == 0:
    os.setsid()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 80, 0, 0))
    os.dup2(slave, 0); os.dup2(slave, 1); os.dup2(slave, 2)
    os.close(master)
    os.chdir(REPO)
    os.execve(BIN, [BIN, "--provider", "mock", "--model", "mock"],
              dict(os.environ, SHUTTLE_MOCK_TURNS="/tmp/wv_repro/turns.json", NO_COLOR="1"))

buf = bytearray()
def pump(sec):
    end = time.time() + sec
    while time.time() < end:
        r, _, _ = select.select([master], [], [], 0.2)
        if r:
            try:
                d = os.read(master, 65536)
            except OSError:
                return
            if not d: return
            buf.extend(d)

def txt():
    return bytes(buf).decode(errors="replace")

# 1. initial frame WITHOUT keys
pump(6)
t0 = txt()
print("PASS1 initial frame without key:", "manual" in striptight(t0) and "typeamessage" in striptight(t0) and "?1049h" in t0)

# 2. keys typed BEFORE go: junk 'x' — must be drained at the overlay
os.write(master, b"x")
time.sleep(0.4)
os.write(master, b"go\n")
pump(2)
t1 = txt()
s1 = striptight(t1) + striptight(t0); print("PASS2 overlay up after go:", "once" in s1 or "oncedeny" in s1)

# 3. one letter answers the dialog (the new dialog has no raw echo row;
# the turn continuing is the observable)
os.write(master, b"y")
time.sleep(0.6)
pump(2)
t2 = txt()
print("PASS3 answer accepted, turn continues:", "done" in striptight(t2))

# 4. turn finished with transcript rendered
pump(2)
t3 = txt()
print("PASS4 turn finished with transcript:", "done" in striptight(t3))

# 5. double ctrl+c clean exit (restore ?1049l)
os.write(master, b"\x03"); time.sleep(0.5); pump(0.5)
t4 = txt()
os.write(master, b"\x03"); time.sleep(0.8); pump(1)
t5 = txt()
print("PASS5 hint shown:", "pressCtrl+Cagain" in striptight(t4) + striptight(t5))
print("PASS6 clean restore (?1049l):", "?1049l" in t5)
try:
    os.kill(pid, 9)
except ProcessLookupError:
    pass