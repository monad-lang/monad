# The session-store repro: durable transcripts/history, restart resume,
# disk-paged scrollback, bracketed paste, --no-color, and a memory probe.
# Everything runs against the compiled target-monad/release/weaver under a
# pty with WEAVER_SESSION_ROOT pointed at a temp directory, so the
# developer's real ~/.weaver/sessions is never touched.
import json, os, pty, re, select, shutil, signal, struct, termios, time, fcntl

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = REPO + "/target-monad/release/weaver"
TMP = os.environ.get("WV_SESSION_TMP", "/tmp/wv_sessions_repro")
SESSIONS = TMP + "/sessions"

def strip(s): return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)
def tight(s): return re.sub(r"[ \r\n\t]", "", strip(s))
def has_color(t): return any(c in t for c in ("\x1b[33;2m", "\x1b[36m", "\x1b[32;2m", "\x1b[31m"))

def spawn(args, env_extra=None):
    master, slave = pty.openpty()
    os.set_blocking(master, False)
    pid = os.fork()
    if pid == 0:
        os.setsid()
        fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 100, 0, 0))
        os.dup2(slave, 0); os.dup2(slave, 1); os.dup2(slave, 2)
        os.close(master)
        os.chdir(REPO)
        env = dict(os.environ, WEAVER_SESSION_ROOT=SESSIONS)
        if env_extra: env.update(env_extra)
        os.execve(BIN, [BIN] + args, env)
    return master, pid

def pump(master, sec, buf):
    end = time.time() + sec
    while time.time() < end:
        r, _, _ = select.select([master], [], [], 0.1)
        if r:
            try: d = os.read(master, 65536)
            except OSError: return
            if not d: return
            buf.extend(d)

def finish(master, pid):
    os.write(master, b"\x03\x03")
    pump(master, 0.8, bytearray())
    try: os.close(master)
    except OSError: pass
    try: os.waitpid(pid, 0)
    except ChildProcessError: pass

def mock_turns(path, texts):
    data = [{"message": {"role": "assistant", "content": [{"type": "text", "text": t}]},
             "usage": {"input_tokens": 1, "output_tokens": 1, "cached_tokens": 0},
             "stop": "end_turn"} for t in texts]
    with open(path, "w") as f: json.dump(data, f)

def session_ids():
    if not os.path.isdir(SESSIONS): return []
    return sorted(n for n in os.listdir(SESSIONS) if os.path.isdir(os.path.join(SESSIONS, n)))

def rss_kb(pid):
    try:
        with open("/proc/%d/status" % pid) as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
    except OSError:
        pass
    return -1

def write_meta(d, updated, turns=0):
    meta = {"version": 1, "created": 1, "updated": updated, "history_next": 1,
            "session": {"config": {"base_url": "mock", "model": "mock",
                                   "api_key_env": "WEAVER_UNUSED_KEY", "max_tokens": 8,
                                   "wire": "mock"},
                        "system_prompt": "s", "tools": [], "history": [],
                        "turns": turns,
                        "spent": {"input_tokens": 0, "output_tokens": 0, "cached_tokens": 0}}}
    with open(os.path.join(d, "meta.json"), "w") as f: json.dump(meta, f)

def synth_session(sid, lines):
    d = os.path.join(SESSIONS, sid)
    os.makedirs(os.path.join(d, "transcript"), exist_ok=True)
    os.makedirs(os.path.join(d, "history"), exist_ok=True)
    blocks, seq, start = [], 1, 0
    for i in range(0, len(lines), 256):
        chunk = lines[i:i + 256]
        with open(os.path.join(d, "transcript", "%012d.json" % seq), "w") as f:
            json.dump({"version": 1, "seq": seq, "start": start,
                       "count": len(chunk), "lines": chunk}, f)
        blocks.append({"seq": seq, "start": start, "count": len(chunk)})
        seq += 1; start += len(chunk)
    with open(os.path.join(d, "transcript", "index.json"), "w") as f:
        json.dump({"version": 1, "total": start, "next_seq": seq, "blocks": blocks}, f)
    write_meta(d, int(time.time() * 1000))
    return d

def check(cond, label):
    print(("PASS " if cond else "FAIL ") + label)
    return bool(cond)

results = []

def main():
    shutil.rmtree(TMP, ignore_errors=True)
    os.makedirs(TMP)
    turns1 = TMP + "/turns1.json"
    mock_turns(turns1, ["persisted-reply"])
    common = ["--provider", "mock", "--model", "mock"]
    env = {"SHUTTLE_MOCK_TURNS": turns1}

    # S1: one turn, then exit; the session is on disk.
    master, pid = spawn(common, env)
    buf = bytearray(); pump(master, 1.0, buf)
    os.write(master, b"hi\r"); pump(master, 1.2, buf)
    frames1 = strip(buf.decode("utf-8", "replace"))
    finish(master, pid)
    ids = session_ids()
    ok = bool(ids)
    if ok:
        d = os.path.join(SESSIONS, ids[-1])
        idx = json.load(open(os.path.join(d, "transcript", "index.json")))
        ok = ok and idx["total"] >= 2 and os.path.isfile(os.path.join(d, "history", "000000000001.json"))
    results.append(check(ok and "persisted-reply" in frames1, "S1 turn persisted to a session directory"))

    # S2: restart with --resume <id>; the old transcript fills the first frame.
    resumed = session_ids()[-1] if session_ids() else ""
    master, pid = spawn(common + ["--resume", resumed], env)
    buf = bytearray(); pump(master, 1.2, buf)
    frames2 = strip(buf.decode("utf-8", "replace"))
    finish(master, pid)
    results.append(check("persisted-reply" in frames2, "S2 --resume restores the transcript"))

    # S3: a synthetic session larger than the 512-line tail; Home pages to line 1.
    lines = ["EARLIEST-LINE-%04d" % i for i in range(1200)]
    d = synth_session("s-manual", lines)
    master, pid = spawn(common + ["--resume", d], env)
    buf = bytearray(); pump(master, 1.2, buf)
    os.write(master, b"\x1b[H")  # Home
    pump(master, 1.0, buf)
    frames3 = strip(buf.decode("utf-8", "replace"))
    finish(master, pid)
    results.append(check("EARLIEST-LINE-0000" in frames3, "S3 Home pages older lines from disk"))

    # S4: a bracketed paste stays literal (two lines, one submit).
    master, pid = spawn(common, env)
    buf = bytearray(); pump(master, 1.0, buf)
    os.write(master, b"\x1b[200~alpha\nbeta\x1b[201~"); pump(master, 0.5, buf)
    os.write(master, b"\r"); pump(master, 1.2, buf)
    frames4 = strip(buf.decode("utf-8", "replace"))
    finish(master, pid)
    results.append(check("you: alpha" in frames4 and "beta" in frames4, "S4 bracketed paste lands verbatim"))

    # S5: --no-color silences the palette.
    master, pid = spawn(common + ["--no-color"], env)
    buf = bytearray(); pump(master, 1.0, buf)
    raw5 = buf.decode("utf-8", "replace")
    finish(master, pid)
    results.append(check(not has_color(raw5), "S5 --no-color emits no palette codes"))

    # S6: memory probe -- a ~18 MB transcript on disk must not be loaded:
    # startup reads the index and the last 512 lines only, and idle RSS
    # stays flat. (Per-frame renderer churn is a separate tui concern and
    # is deliberately not what this asserts.)
    huge = ["z" * 900 + "-%05d" % i for i in range(20000)]
    d = synth_session("s-huge", huge)
    master, pid = spawn(common + ["--resume", d], env)
    buf = bytearray(); pump(master, 1.8, buf)
    r1 = rss_kb(pid)
    pump(master, 3.0, buf)
    r2 = rss_kb(pid)
    frames6 = strip(buf.decode("utf-8", "replace"))
    finish(master, pid)
    print("  rss after startup=%dKB after idle=%dKB (transcript ~18MB on disk)" % (r1, r2))
    results.append(check(0 < r1 < 120000 and (r2 - r1) < 20000 and "z" in frames6,
                         "S6 an 18MB session stays on disk (startup RSS bounded, idle flat)"))

    print("SESSION REPRO: " + ("ALL PASS" if all(results) else "FAILURES"))
    return 0 if all(results) else 1

if __name__ == "__main__":
    raise SystemExit(main())
