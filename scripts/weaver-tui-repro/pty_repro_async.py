# The async-turn repro -- weaver.md Phase 12's live behaviors, pinned in a
# pty against the compiled `target-monad/release/weaver` (mock wire via
# SHUTTLE_MOCK_TURNS, now with SHUTTLE_MOCK_DELAY_MS making the turn take
# real time -- without that knob the mock is instantaneous and nothing
# here is observably "mid-turn").
#
# What v1 of the async turn IS (tui.mo's header, weaver.md's changelog):
# the UI stays live during a turn (spinner frames, the streamed fragment
# on the transcript's last row), keys typed mid-turn BUFFER and land in
# the input box the moment the turn completes (the loop never reads stdin
# while a turn is pending), a Ctrl-C pressed mid-turn is delivered after
# the turn (double Ctrl-C still exits cleanly through restore_terminal),
# and the approval overlay is the turn's ONLY stdin reader -- a `y` typed
# while it waits is consumed by the overlay, never by the loop.

import os, pty, time, select, fcntl, termios, struct, re, shutil

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = REPO + "/target-monad/release/weaver"
TMP = os.environ.get("WV_REPRO_TMP", "/tmp/wv_async_repro")
os.makedirs(TMP, exist_ok=True)

def strip(s): return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)
def tight(s): return re.sub(r"\s", "", strip(s))

def spawn(turns_path):
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
                  dict(os.environ,
                       SHUTTLE_MOCK_TURNS=turns_path,
                       SHUTTLE_MOCK_DELAY_MS="2500"))
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

def snap(master, sec, buf):
    n0 = len(buf)
    pump(master, sec, buf)
    return bytes(buf[n0:])

def finish(master, pid, buf):
    os.write(master, b"\x03"); time.sleep(0.4); pump(master, 0.5, buf)
    os.write(master, b"\x03"); time.sleep(0.6); pump(master, 1.0, buf)
    restored = "?1049l" in bytes(buf).decode(errors="replace")
    try: os.kill(pid, 9)
    except ProcessLookupError: pass
    os.close(master)
    return restored

checks = []

# ── sessions over the slow single turn ──────────────────────────────────
slow = os.path.join(TMP, "turns_slow.json")
shutil.copyfile(os.path.join(REPO, "scripts", "weaver-tui-repro", "turns_slow.json"), slow)

master, pid = spawn(slow)
buf = bytearray()
pump(master, 2.0, buf)            # startup frame
os.write(master, b"hello\n")      # submit -> fork

# While the 2500 ms turn runs, the loop keeps REDRAWING (the spinner is
# model state; every changed frame writes a diff). Two windows inside
# the turn must both carry rewrite escapes -- a frozen loop would emit
# nothing after the initial frame. (The mock's fragment emits at its
# ~2.5 s mark; the windows bracket the idle-tick redraws before it.)
w1 = snap(master, 1.2, buf)
os.write(master, b"queued")       # typed mid-turn: buffers in the tty
w2 = snap(master, 1.8, buf)
checks.append(("S1 UI redraws while a turn runs", b"\x1b[" in w1 and b"\x1b[" in w2))

# The streamed fragment shows on the transcript's last row mid-turn.
mid = tight((w1 + w2).decode(errors="replace"))
checks.append(("S1 streamed fragment visible mid-turn", "[thinking]" in mid or "replyslow" in mid))

# The turn completes ~3.0 s after submit; this window catches the
# forced blank repaint (its largest single burst) and the transcript
# line landing.
tail = snap(master, 3.5, buf)
after = tight(bytes(buf).decode(errors="replace"))
checks.append(("S2 assistant text lands in transcript", "replyslow:the" in after))
checks.append(("S2 mid-turn keys buffered then drained", "queued" in after))
checks.append(("S3 completion forced a blank repaint", max(len(w2), len(tail)) > 3000))

# NOTHING re-appears after the completion frame: exactly-once means the
# app never re-emits the reply, and the fragment never resurfaces (the
# forced repaint cleaned it).
post = tight(snap(master, 1.5, buf).decode(errors="replace"))
checks.append(("S3 no re-emission after the completion", post.count("replyslow") == 0 and post.count("[thinking]") == 0))

checks.append(("S3 double Ctrl+C still exits cleanly", finish(master, pid, buf)))

# ── Ctrl-C mid-turn is queued, not interrupting ─────────────────────────
master, pid = spawn(slow)
buf = bytearray()
pump(master, 2.0, buf)
os.write(master, b"hi\n")
snap(master, 0.8, buf)            # into the turn
os.write(master, b"\x03\x03")     # two presses DURING the turn
snap(master, 3.8, buf)
after = tight(bytes(buf).decode(errors="replace"))
checks.append(("S4 turn completes despite mid-turn Ctrl-C", "replyslow:the" in after))
checks.append(("S4 queued Ctrl-C exits cleanly after", finish(master, pid, buf)))

# ── the overlay stays stdin's first reader ──────────────────────────────
two = os.path.join(TMP, "turns_two_reads.json")
shutil.copyfile(os.path.join(REPO, "scripts", "weaver-tui-repro", "turns_two_reads.json"), two)
master, pid = spawn(two)
buf = bytearray()
pump(master, 2.0, buf)
# Type garbage BEFORE submitting: it buffers, and the overlay's
# drain_stale_keys drops it rather than phantom-answering.
os.write(master, b"xxx")
os.write(master, b"hello\n")
# Wait INTO the overlay (the mock serves the tool_use turn after its
# delay), then answer for real: the echo is the overlay's, the loop
# never saw the `y`.
snap(master, 3.8, buf)
os.write(master, b"y")
snap(master, 3.4, buf)
after = tight(bytes(buf).decode(errors="replace"))
checks.append(("S5 the overlay consumed the y (the second prompt appears)", after.count("Permissionrequired") >= 2))
os.write(master, b"y")            # the second read's prompt
snap(master, 4.5, buf)
checks.append(("S5 clean exit after both prompts", finish(master, pid, buf)))

fails = [name for name, ok in checks if not ok]
for name, ok in checks:
    print(("PASS" if ok else "FAIL"), name)
print("ASYNC PTY REPRO:", "ALL PASS" if not fails else f"FAILED: {fails}")