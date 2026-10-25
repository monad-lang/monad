# The session-store repro: durable transcripts/history, restart resume,
# disk-paged scrollback, bracketed paste, --no-color, and a memory probe.
# Everything runs against the compiled target-monad/release/weaver under a
# pty with an isolated HOME and WEAVER_SESSION_ROOT, so neither the
# developer's real ~/.weaver nor their ./weaver config is touched.
import json, os, pty, re, select, shutil, signal, struct, sys, tempfile, termios, time, fcntl

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BIN = REPO + "/target-monad/release/weaver"
BASE_TMP = os.environ.get("WV_SESSION_TMP")
TMP = (os.path.join(BASE_TMP, "wv_sessions_repro_%d" % os.getpid())
       if BASE_TMP else tempfile.mkdtemp(prefix="wv_sessions_repro_"))
SESSIONS = TMP + "/sessions"
HOME = TMP + "/home"

def strip(s): return re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", s)
def tight(s): return re.sub(r"[ \r\n\t]", "", strip(s))

# Any SGR colour parameter: 30-37 / 90-97 (fg), 40-47 / 100-107 (bg).
COLOR_RE = re.compile(r"\x1b\[[0-9;]*\b(?:3[0-7]|9[0-7]|4[0-7]|10[0-7])\b[0-9;]*m")
def has_color(t): return COLOR_RE.search(t) is not None

def spawn(args, env_extra=None):
    if not (os.path.isfile(BIN) and os.access(BIN, os.X_OK)):
        raise SystemExit("missing weaver binary: %s (build with --release)" % BIN)
    master, slave = pty.openpty()
    os.set_blocking(master, False)
    pid = os.fork()
    if pid == 0:
        try:
            os.setsid()
            fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 24, 100, 0, 0))
            os.dup2(slave, 0); os.dup2(slave, 1); os.dup2(slave, 2)
            os.close(master)
            os.chdir(TMP)  # no ./.weaver/config.toml from the checkout
            env = dict(os.environ)
            env.pop("NO_COLOR", None)
            env["HOME"] = HOME
            env["WEAVER_SESSION_ROOT"] = SESSIONS
            if env_extra: env.update(env_extra)
            os.execve(BIN, [BIN] + args, env)
        except BaseException:
            os._exit(127)
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

def painted(master, needle, sec, buf):
    """Pump until `needle` is in the raw output, or `sec` elapses.

    S6's huge session wraps 512 lines of 900 characters on the compiled
    backend; that outruns a fixed window on a loaded runner. The RSS probe
    is about memory, so it must not race the renderer.
    """
    want = needle.encode()
    end = time.time() + sec
    while time.time() < end:
        pump(master, 0.2, buf)
        if want in buf:
            return True
    return False

def wait_nohang(pid):
    """True once `pid` is reaped (or was already)."""
    try:
        return os.waitpid(pid, os.WNOHANG)[0] == pid
    except ChildProcessError:
        return True

def finish(master, pid):
    # A crashed child makes the write fail; the reap must never hang.
    try:
        os.write(master, b"\x03\x03")
    except OSError:
        pass
    pump(master, 0.8, bytearray())
    try: os.close(master)
    except OSError: pass
    deadline = time.time() + 5.0
    while time.time() < deadline:
        if wait_nohang(pid):
            return
        time.sleep(0.05)
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try: os.kill(pid, sig)
        except ProcessLookupError:
            reap(pid)
            return
        time.sleep(0.2)
        if wait_nohang(pid):
            return
    reap(pid)

def reap(pid):
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

def transcript_entries(d):
    out, tdir = [], os.path.join(d, "transcript")
    if os.path.isdir(tdir):
        for n in sorted(os.listdir(tdir)):
            if n.endswith(".json") and n != "index.json":
                try:
                    with open(os.path.join(tdir, n)) as f:
                        out.extend(json.load(f).get("lines", []))
                except (OSError, ValueError):
                    pass
    return out

def entry_text(e):
    return e.get("text", "") if isinstance(e, dict) else e

def entry_user(e):
    return bool(e.get("user", False)) if isinstance(e, dict) else False

def transcript_lines(d):
    return [entry_text(e) for e in transcript_entries(d)]

def history_messages(d):
    out, hdir = [], os.path.join(d, "history")
    if os.path.isdir(hdir):
        for n in sorted(os.listdir(hdir)):
            if n.endswith(".json"):
                try:
                    with open(os.path.join(hdir, n)) as f:
                        out.extend(json.load(f))
                except (OSError, ValueError):
                    pass
    return out

def message_text(m):
    return "".join(c.get("text", "") for c in m.get("content", [])
                   if isinstance(c, dict) and c.get("type") == "text")

def check(cond, label):
    print(("PASS " if cond else "FAIL ") + label)
    return bool(cond)

def new_session_since(before):
    """The directory a run created, even when synthetic sessions sort last."""
    new = [n for n in session_ids() if n not in before]
    return new[-1] if new else ""

def run(args, env_extra, before=1.0, keys_before=b"", after=1.2):
    master, pid = spawn(args, env_extra)
    buf = bytearray(); pump(master, before, buf)
    if keys_before: os.write(master, keys_before); pump(master, after, buf)
    frames = strip(buf.decode("utf-8", "replace"))
    return master, pid, frames, buf

def main():
    shutil.rmtree(TMP, ignore_errors=True)
    os.makedirs(SESSIONS)
    os.makedirs(HOME)
    turns1 = TMP + "/turns1.json"
    mock_turns(turns1, ["persisted-reply"])
    common = ["--provider", "mock", "--model", "mock"]
    env = {"SHUTTLE_MOCK_TURNS": turns1}

    # S1: one turn, then exit; the session is on disk WITH the turn's text.
    master, pid = spawn(common, env)
    buf = bytearray(); pump(master, 1.0, buf)
    os.write(master, b"hi\r"); pump(master, 1.2, buf)
    frames1 = strip(buf.decode("utf-8", "replace"))
    finish(master, pid)
    ids = session_ids()
    ok = bool(ids)
    lines = []
    if ok:
        d = os.path.join(SESSIONS, ids[-1])
        idx = json.load(open(os.path.join(d, "transcript", "index.json")))
        lines = transcript_lines(d)
        hist = history_messages(d)
        ok = (idx["total"] >= 3
              and any("persisted-reply" in l for l in lines)
              and any(entry_text(e) == "hi" and entry_user(e) for e in transcript_entries(d))
              and any(message_text(m) == "hi" for m in hist)
              and os.path.isfile(os.path.join(d, "history", "000000000001.json")))
    results.append(check(ok and "persisted-reply" in frames1, "S1 turn persisted to a session directory"))

    # S2: restart with --resume <id>; the old transcript fills the first frame.
    resumed = ids[-1] if ids else ""
    master, pid, frames2, _ = run(common + ["--resume", resumed], env, 1.2)
    finish(master, pid)
    results.append(check("persisted-reply" in frames2, "S2 --resume restores the transcript"))

    # S3: a synthetic session larger than the 512-line tail; Home pages to line 1.
    lines = ["EARLIEST-LINE-%04d" % i for i in range(1200)]
    d = synth_session("s-manual", lines)
    master, pid, frames3, _ = run(common + ["--resume", d], env, 1.2, b"\x1b[H", 1.0)
    finish(master, pid)
    results.append(check("EARLIEST-LINE-0000" in frames3, "S3 Home pages older lines from disk"))

    # S4: a bracketed paste stays literal: one submit, one two-line user
    # block (a second block would mean the newline submitted).
    before4 = set(session_ids())
    master, pid = spawn(common, env)
    buf = bytearray(); pump(master, 1.0, buf)
    os.write(master, b"\x1b[200~alpha\nbeta\x1b[201~"); pump(master, 0.5, buf)
    os.write(master, b"\r"); pump(master, 1.2, buf)
    frames4 = strip(buf.decode("utf-8", "replace"))
    finish(master, pid)
    sid4 = new_session_since(before4)
    hist4 = history_messages(os.path.join(SESSIONS, sid4)) if sid4 else []
    users4 = [message_text(m) for m in hist4 if m.get("role") == "user"]
    sid4_entries = transcript_entries(os.path.join(SESSIONS, sid4)) if sid4 else []
    user4 = [entry_text(e) for e in sid4_entries if entry_user(e)]
    results.append(check("alpha" in frames4 and "beta" in frames4
                         and "you:" not in frames4 and "assistant:" not in frames4
                         and users4 == ["alpha\nbeta"]
                         and user4 == ["alpha", "beta"],
                         "S4 bracketed paste lands verbatim, one user block"))

    # S5: the palette is on by default and --no-color silences it.
    colored_env = TMP + "/turns_color.json"
    mock_turns(colored_env, ["colored"])
    master, pid, frames5a, buf5a = run(common, dict(env, SHUTTLE_MOCK_TURNS=colored_env), 1.0)
    raw5a = bytes(buf5a).decode("utf-8", "replace")
    finish(master, pid)
    master, pid, frames5b, buf5b = run(common + ["--no-color"], dict(env, SHUTTLE_MOCK_TURNS=colored_env), 1.0)
    raw5b = bytes(buf5b).decode("utf-8", "replace")
    finish(master, pid)
    results.append(check(has_color(raw5a) and not has_color(raw5b),
                         "S5 --no-color emits no palette codes"))

    # S6: a ~18 MB transcript on disk must not be loaded. The control is a
    # tiny session: the huge one may cost no more than 10 MB over it, and
    # idle RSS must stay flat.
    small = synth_session("s-small", ["hello"])
    master, pid = spawn(common + ["--resume", small], env)
    buf = bytearray(); pump(master, 1.8, buf)
    base_rss = rss_kb(pid)
    finish(master, pid)

    huge = ["z" * 900 + "-%05d" % i for i in range(20000)]
    d = synth_session("s-huge", huge)
    master, pid = spawn(common + ["--resume", d], env)
    buf = bytearray(); pump(master, 1.8, buf)
    r1 = rss_kb(pid)
    # Wrapping the 512-line tail (900-char lines) is the first frame's cost
    # on the compiled backend and varies with runner load; wait for the
    # paint on a deadline rather than assuming it fits a fixed window.
    painted(master, "z", 30.0, buf)
    r2 = rss_kb(pid)
    frames6 = strip(buf.decode("utf-8", "replace"))
    finish(master, pid)
    print("  rss base=%dKB huge=%dKB idle=%dKB (transcript ~18MB on disk)" % (base_rss, r1, r2))
    results.append(check(0 < r1 < base_rss + 10240 and (r2 - r1) < 20000 and "z" in frames6,
                         "S6 an 18MB session stays on disk (startup RSS bounded, idle flat)"))

    print("SESSION REPRO: " + ("ALL PASS" if all(results) else "FAILURES"))
    return 0 if all(results) else 1

results = []
try:
    code = main()
finally:
    if not os.environ.get("WV_SESSION_KEEP"):
        shutil.rmtree(TMP, ignore_errors=True)
sys.exit(code)
