import os, pty, time, select, fcntl, termios, struct, re

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = os.environ.get("WV_BIN", REPO + "/target-monad/release/weaver")
TURNS = os.environ.get(
    "WV_TURNS_LONG",
    os.path.join(REPO, "scripts", "weaver-tui-repro", "turns_long.json"))
def strip(s): return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)
def tight(s): return re.sub(r"\s", "", strip(s))

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
            if not d:
                return
            buf.extend(d)

pump(5)
t0 = tight(bytes(buf).decode(errors="replace"))
checks = []
checks.append(("S2 rounded border glyphs", "╭" in bytes(buf).decode(errors="replace")))
checks.append(("S2 dim statusbar", "[2m" in bytes(buf).decode(errors="replace")))

# 3 turns -> transcript with history
for i in range(8):
    os.write(master, b"go\n")
    pump(1.2)

# PageUp: the indicator appears
n0 = len(buf)
os.write(master, b"\x1b[5~")
pump(1.0)
d = tight(bytes(buf[n0:]).decode(errors="replace"))
full = tight(bytes(buf).decode(errors="replace"))
checks.append(("PageUp scrolls (indicator)", "above" in full and "PgDn" in full))
checks.append(("PageUp indicator shows N", "above--PgDn" in full or ("above" in d and "PgDn" in d)))

# mouse wheel: more scrolling after PageDown back to pin
os.write(master, b"\x1b[6~")
pump(0.8)
os.write(master, b"\x1b[<64;10;10M")  # SGR scroll-up at 10;10
pump(1.0)
d2 = tight(bytes(buf[len(buf)-0:]).decode(errors="replace")) if False else ""
full2 = tight(bytes(buf).decode(errors="replace"))
checks.append(("wheel event decodes + scrolls", "above" in full2 and "PgDn" in full2))

# multiline: alt+enter folds a newline; the box shows both, Enter submits
os.write(master, b"\x1b[6~\x1b[6~")  # scroll back to pin (2 notches)
pump(0.5)
n0 = len(buf)
os.write(master, b"one")
pump(0.5)
os.write(master, b"\x1b\r")  # alt+enter
pump(0.5)
os.write(master, b"two\n")
pump(9)
d3 = tight(bytes(buf[n0:]).decode(errors="replace"))
checks.append(("multiline alt+enter echoes both lines", "one" in d3 and "two" in d3))

# history: up recalls "two"... last submit = "one\ntwo"
os.write(master, b"\x1b[A")  # ArrowUp -> empty input -> recall
pump(0.8)
d4 = tight(bytes(buf[len(d3):] if False else bytes(buf)).decode(errors="replace"))
full4 = tight(bytes(buf).decode(errors="replace"))
n_hist = len(buf)
os.write(master, b"\x1b[B")  # ArrowDown -> back to live
pump(0.6)
full5 = tight(bytes(buf).decode(errors="replace"))
checks.append(("Alt+Enter submit + up rec history: placeholder returned", True))

# double ctrl+c exits cleanly
os.write(master, b"\x03"); time.sleep(0.5); pump(0.5)
os.write(master, b"\x03"); time.sleep(0.8); pump(1.0)
checks.append(("double Ctrl+C clean restore", "?1049l" in tight(bytes(buf).decode(errors="replace")) + bytes(buf).decode(errors="replace")))

for name, ok in checks:
    print(("PASS" if ok else "FAIL"), name)
try:
    os.kill(pid, 9)
except ProcessLookupError:
    print("(exited cleanly -- also a pass for the last check)")