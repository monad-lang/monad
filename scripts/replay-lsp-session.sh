#!/usr/bin/env bash
# usage: replay-lsp-session.sh <fixture.jsonl> <command...>
#
# Replays an LSP session against a compiler's `lsp` subcommand and asserts the
# milestone's criteria on the wire. The fixture is a line-per-message script
# (fixtures/lsp/README.md defines the format); the command is the server, and the
# remainder of the command line is its arguments:
#
#   scripts/replay-lsp-session.sh fixtures/lsp/session.jsonl ./out/monad lsp
#   scripts/replay-lsp-session.sh fixtures/lsp/session.jsonl \
#     ./target/release/monad-rs run cli/src/main.mo lsp
#
# The second form is how this was developed -- the Rust host interpreting the
# self-hosted server -- and it is not the gate. The gate is the compiled binary:
# the whole point of the LSP being written in Monad is that it ships in the
# compiler, and the interpreted run says nothing about codegen.
#
# THE SESSION IS RUN ONCE PER ENCODING, because `initialize` may offer one
# encoding per connection. Which one the server picks is the CLIENT's list to
# narrow and the server's to choose from, so a session that needs both runs twice
# with `positionEncodings` a single element. That is also why the encoding is a
# fixture placeholder (`@ENCODINGS@`) rather than a constant: the point of the
# sweep is that every asserted range is a different pair of numbers.
#
# WHAT IS ASSERTED, in the order the fixture asks for it:
#
#   1. `initialize` advertises the five implemented features and echoes the
#      negotiated `positionEncoding` -- and nothing else, since a capability that
#      is advertised and not answered is worse than one never offered.
#   2. The parse-error vector publishes exactly one diagnostic, severity error,
#      source `monad`, and its range matches fixtures/lsp/README.md's hand-computed
#      columns -- which DIFFER between the two encodings. This is the assertion the
#      Rust server this replaces fails.
#   3. A clean file publishes nothing.
#   4. `documentSymbol` answers one symbol per declaration, with the kind the
#      picker's vocabulary gives it and a range that starts at the declaration.
#   5. `hover` on a def and `definition` on a def's use resolve, in the file.
#   6. `definition` and `hover` on a local that shadows a top-level def answer the
#      LOCAL's binder, not the def (`motes/toolkit/src/navigation.mo`'s cursor-to-binding walk).
#      `definition` on a type, constructor and class the prelude declares opens
#      prelude.mo at the declaration (`farref.mo`).
#   7. `workspace/symbol` finds a declaration in an open buffer.
#   8. A message that is not JSON gets a -32700 error with a null id and the session
#      SURVIVES it -- the next request is still answered.
#   9. A frame truncated by end of input exits cleanly, with no panic.
#  10. No stray bytes on stdout, ever: the protocol stream is the only thing that
#      may be written there, and a diagnostic printed by the check path would look
#      exactly like a client bug.
set -euo pipefail

usage() {
  sed -n '2,3p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//' >&2
  exit 2
}

[ $# -ge 2 ] || usage
fixture="$1"; shift
[ -f "$fixture" ] || { echo "replay-lsp-session: no such fixture: $fixture" >&2; exit 2; }
[ -n "${1:-}" ] || usage

# The command as the caller spelled it, resolved to an absolute path for its first
# word so a relative `./out/monad` keeps working after the client has changed
# directory -- which it does not, but a future edit that does should not silently
# run a different binary.
bin="$1"
case "$bin" in
  /*) ;;
  */*) bin="$PWD/$bin" ;;
  *) bin="$(command -v -- "$bin" || true)" ;;
esac
[ -n "$bin" ] && [ -x "$bin" ] || { echo "replay-lsp-session: not executable: $1" >&2; exit 2; }
shift
cmd=("$bin" "$@")

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

exec python3 - "$fixture" "$root" "${cmd[@]}" <<'PY'
import json, os, re, subprocess, sys

fixture, root = sys.argv[1], sys.argv[2]
cmd = sys.argv[3:]
fixture_dir = os.path.dirname(os.path.abspath(fixture))

# --- The hand-computed table, and the arithmetic behind it -------------------
#
# fixtures/lsp/nonascii.mo's offending byte is U+00AB on line 17 (0-based). 44 bytes
# precede it on that line:
#
#   "def zz_replay_broken : String := "a"   35   (32 + the opening quote + the `a`)
#   the em dash U+2014                       3   -> 38
#   "b" ++ "                                 6   -> 44
#
# U+2014 is THREE bytes in utf-8 and ONE code unit in utf-16, so the utf-16 column is
# 44 - 2 = 42. The range's end is one past the byte: +2 bytes in utf-8 (U+00AB is two
# bytes there) and +1 unit in utf-16. Both numbers are asserted literally, and the
# oracle below recomputes them from the file's bytes, so a fixture edit that moves the
# vector fails loudly rather than silently re-deriving an expectation.
NONASCII_AT_END = {
    "utf-8": ((17, 44), (17, 46)),
    "utf-16": ((17, 42), (17, 43)),
}

SHAPES_SYMBOLS = [
    # (name, kind, start line): the picker's kind codes are
    # def 12, struct 23, class 5, type 10, instance 11.
    #
    # THE INSTANCE'S NAME IS `_`, which is the language's own marker for an unnamed
    # instance -- `instance_try_named` (lang/src/parser.mo:3394) defaults the name to
    # `Identifier.id "_"`. So it is not an LSP-side accident, but it is a wart in the
    # picker: every anonymous instance lists as `_`. Reported, not fixed here: naming
    # it after its class is a change to `lang/src/module.mo`'s outline vocabulary,
    # shared with other plans, and `lang/src/tests/decl_range_tests.mo` pins the names.
    ("ZzReplayShape", 23, 16),
    ("ZzReplayColor", 10, 21),
    ("ZzReplayName", 5, 26),
    ("_", 11, 30),
    ("zz_replay_width", 12, 38),
    ("zz_replay_area", 12, 40),
    ("zz_replay_shadowed", 12, 42),
    ("zz_replay_shadow_use", 12, 44),
]

# THE MESSAGE CARRIES THE SAME POSITION IN A THIRD CONVENTION, and the three disagree.
# For the offending byte, which is on line 17 (0-based):
#
#   wire range, utf-8    start character 44   (bytes, 0-based)
#   wire range, utf-16   start character 42   (code units, 0-based)
#   this message         "expected '(' at 18:43"
#
# `18` is a 1-based LINE and `43` is a 1-based CHARACTER column -- 0-based characters
# gives 42, which is exactly the utf-16 start, so the message counts characters and not
# bytes. It is computed from the source alone and is therefore IDENTICAL under both
# encodings, which is why it is asserted once and not per-encoding.
#
# Three numbers for one position is a wart. The message exists for `monad check`'s
# terminal, where a human wants 1-based characters; the wire range exists for an editor,
# which wants 0-based units in the negotiated encoding. They are pinned separately so
# that unifying them is a deliberate change rather than an accident.
NONASCII_MESSAGE = "expected '(' at 18:43"

# Every declaration's range ends one past its last token: a struct's at its closing
# brace, a def's at the end of its own last line (`motes/toolkit/src/decl_text.mo` trims what the
# def's parse swallowed after it). So the struct's range is (16,0)..(19,1) --
# `struct ZzReplayShape {` on line 16 through the `}` on line 19.
SHAPES_STRUCT_RANGE = (16, 0, 19, 1)

# A declaration's NAME, which is where `definition` lands and what documentSymbol's
# `selectionRange` covers: `struct ZzReplayShape` and `def zz_replay_width`.
SHAPES_STRUCT_NAME = (16, 7, 16, 20)
SHAPES_WIDTH_NAME = (38, 4, 38, 19)


def prelude_line(needle):
    """The 0-based line of `needle` in the checkout's prelude, so the cross-file pins
    (`farref.mo`) follow a prelude edit instead of hard-coding its line numbers."""
    with open(os.path.join(root, "init", "src", "prelude.mo"), encoding="utf-8") as fh:
        text = fh.read()
    return text[:text.index(needle)].count("\n")

failures = []


def check(label, ok, detail=""):
    print(f"  {'PASS' if ok else 'FAIL'}  {label}" + (f"  -- {detail}" if detail else ""))
    if not ok:
        failures.append(label)


# --- The fixture format ------------------------------------------------------


def unescape(s):
    out, i = bytearray(), 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            n = s[i + 1]
            if n == "r":
                out += b"\r"
            elif n == "n":
                out += b"\n"
            elif n == "t":
                out += b"\t"
            elif n == "\\":
                out.append(92)
            elif n == '"':
                out.append(34)
            elif n == "x" and i + 3 < len(s):
                out.append(int(s[i + 2:i + 4], 16))
                i += 2
            else:
                out += c.encode()
                i += 1
                continue
            i += 2
        else:
            out += c.encode()
            i += 1
    return bytes(out)


def inline_buffers(node):
    """`"@name.mo"` as a `didOpen` text means that file's bytes."""
    if isinstance(node, dict):
        for k, v in node.items():
            if k == "text" and isinstance(v, str) and v.startswith("@") and v.endswith(".mo"):
                path = os.path.join(fixture_dir, v[1:])
                with open(path, encoding="utf-8") as fh:
                    node[k] = fh.read()
            else:
                inline_buffers(v)
    elif isinstance(node, list):
        for v in node:
            inline_buffers(v)


def messages(path, encoding):
    """The fixture as `(kind, bytes)` pairs: `("frame", body)` or `("raw", bytes)`."""
    out = []
    with open(path, encoding="utf-8") as fh:
        for raw in fh.read().split("\n"):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("!raw "):
                out.append(("raw", unescape(line[len("!raw "):])))
                continue
            text = line.replace("@ROOT@", root).replace("@ENCODINGS@", encoding)
            try:
                msg = json.loads(text)
            except json.JSONDecodeError:
                # Deliberately malformed: the client frames the LINE, whatever it is,
                # so the server sees a well-formed frame carrying invalid JSON.
                out.append(("frame", line.encode()))
                continue
            inline_buffers(msg)
            body = json.dumps(msg, ensure_ascii=False).encode()
            out.append(("frame", body))
    return out


def wire(msgs):
    chunks = []
    for kind, body in msgs:
        if kind == "raw":
            chunks.append(body)
        else:
            chunks.append(b"Content-Length: %d\r\n\r\n" % len(body) + body)
    return b"".join(chunks)


def unframe(raw):
    """Every complete body, plus the number of trailing bytes that are not one."""
    bodies, i, consumed = [], 0, 0
    pat = re.compile(rb"Content-Length: (\d+)\r\n\r\n")
    while True:
        m = pat.search(raw, i)
        if not m:
            break
        n = int(m.group(1))
        start = m.end()
        if start + n > len(raw):
            break
        bodies.append(raw[start:start + n].decode("utf-8", "replace"))
        i = consumed = start + n
    return bodies, len(raw) - consumed


def run(msgs, timeout):
    p = subprocess.run(cmd, input=wire(msgs), capture_output=True, cwd=root, timeout=timeout)
    bodies, stray = unframe(p.stdout)
    return p, [json.loads(b) for b in bodies] if bodies else [], stray


def by_id(replies, rid):
    for r in replies:
        if r.get("id") == rid:
            return r
    return None


def rng(node):
    """`(start_line, start_char, end_line, end_char)` of a wire range."""
    r = node["range"] if "range" in node else node
    return (r["start"]["line"], r["start"]["character"], r["end"]["line"], r["end"]["character"])


def locs(result):
    """`[(file, range)]` from either result shape.

    `textDocument/definition` answers `Location` -- a bare `{uri, range}` -- but
    `workspace/symbol` answers `SymbolInformation`, which nests the same pair one level
    down under `location` and adds `name`/`kind`. Both are legal, and the two features
    disagree, so the reader has to take both or it fails on whichever it meets second.
    """
    if not result:
        return []
    out = []
    for l in result:
        loc = l.get("location", l)
        out.append((os.path.basename(loc["uri"].replace("file://", "")), rng(loc)))
    return out


# --- The oracle for the hand-computed columns --------------------------------

def oracle(path, needle):
    with open(path, encoding="utf-8") as fh:
        text = fh.read()
    i = text.index(needle)
    line = text[:i].count("\n")
    pre = text[:i].rsplit("\n", 1)[-1]
    post = text[:i + len(needle)].rsplit("\n", 1)[-1]
    return (line, len(pre.encode("utf-8")), len(post.encode("utf-8")),
            len(pre.encode("utf-16-le")) // 2, len(post.encode("utf-16-le")) // 2)


# --- One session per encoding ------------------------------------------------


def session(encoding):
    print(f"\n=== {encoding}: {os.path.basename(fixture)}")
    p, replies, stray = run(messages(fixture, encoding), timeout=int(os.environ.get("LSP_TIMEOUT", "1800")))

    # 10. The protocol stream, and only it.
    check(f"{encoding} no stray stdout bytes", stray == 0, f"{stray} byte(s) not in a frame")
    check(f"{encoding} exit status 0", p.returncode == 0, f"exit={p.returncode}")

    # 1. The handshake.
    init = by_id(replies, 1) or {}
    caps = (init.get("result") or {}).get("capabilities") or {}
    want = {"positionEncoding", "textDocumentSync", "hoverProvider",
            "definitionProvider", "documentSymbolProvider", "workspaceSymbolProvider"}
    check(f"{encoding} capabilities: exactly the implemented five", set(caps) == want,
          f"offered {sorted(caps)}")
    check(f"{encoding} capabilities: positionEncoding echoed", caps.get("positionEncoding") == encoding,
          f"{caps.get('positionEncoding')!r}")
    check(f"{encoding} capabilities: full sync", caps.get("textDocumentSync") == 1,
          f"{caps.get('textDocumentSync')!r}")

    # 2. The parse-error vector, against the hand-computed table.
    pubs = [r for r in replies if r.get("method") == "textDocument/publishDiagnostics"]
    nonascii = [r for r in pubs if r["params"]["uri"].endswith("nonascii.mo")]
    ds = nonascii[0]["params"]["diagnostics"] if nonascii else []
    expected = NONASCII_AT_END[encoding]
    check(f"{encoding} nonascii.mo: exactly one diagnostic", len(ds) == 1, f"{len(ds)} published")
    if ds:
        d = ds[0]
        check(f"{encoding} nonascii.mo: range == hand-computed {expected}", rng(d) == expected[0] + expected[1],
              f"got {rng(d)}")
        check(f"{encoding} nonascii.mo: severity is error", d.get("severity") == 1, f"{d.get('severity')!r}")
        check(f"{encoding} nonascii.mo: source is monad", d.get("source") == "monad", f"{d.get('source')!r}")
        check(f"{encoding} nonascii.mo: message is 1-based line and character column",
              d.get("message") == NONASCII_MESSAGE, f"{d.get('message')!r}")

    # 3. A clean file.
    shapes = [r for r in pubs if r["params"]["uri"].endswith("shapes.mo")]
    ds = shapes[0]["params"]["diagnostics"] if shapes else []
    check(f"{encoding} shapes.mo: no diagnostics", len(ds) == 0, f"{len(ds)} published")

    # 4. The outline.
    syms = by_id(replies, 10)
    got = [s["name"] for s in (syms or {}).get("result") or []]
    check(f"{encoding} documentSymbol: the declarations in the file", got == [n for n, _k, _l in SHAPES_SYMBOLS],
          f"got {got}")
    got = [(s["name"], s["kind"], s["range"]["start"]["line"]) for s in (syms or {}).get("result") or []]
    check(f"{encoding} documentSymbol: kinds and ranges", got == SHAPES_SYMBOLS, f"got {got}")
    by_name = {s["name"]: s for s in (syms or {}).get("result") or []}
    sel = [(n, rng(s["selectionRange"])) for n, s in by_name.items()
           if n in ("ZzReplayShape", "zz_replay_width")]
    check(f"{encoding} documentSymbol: selectionRange is the name",
          sorted(sel) == [("ZzReplayShape", SHAPES_STRUCT_NAME), ("zz_replay_width", SHAPES_WIDTH_NAME)],
          f"got {sel}")
    # A def's range ends at its own last token, not at the next line's start.
    width = rng(by_name.get("zz_replay_width", {}).get("range", {"start": {"line": -1, "character": -1},
                                                                  "end": {"line": -1, "character": -1}}))
    check(f"{encoding} documentSymbol: a def's range ends on its own line",
          width == (38, 0, 38, 56), f"got {width}")
    inside = all(rng(s["range"])[:2] <= rng(s["selectionRange"])[:2]
                 and rng(s["selectionRange"])[2:] <= rng(s["range"])[2:] for s in by_name.values())
    check(f"{encoding} documentSymbol: every selectionRange is inside its range", inside)

    # 5. Navigation, in the file.
    hover = by_id(replies, 11)
    detail = ((hover or {}).get("result") or {}).get("contents", {}).get("value", "")
    # Hover on a `struct` declaration renders the struct as written (`show_struct`, read
    # from the buffer's own declarations): the scope holds only the synthetic inductive a
    # struct is registered as. Asserted exactly, so the old bare-name fallback fails.
    check(f"{encoding} hover on the struct declaration renders the struct",
          detail == "```monad\nstruct ZzReplayShape {\n  width : I64,\n  height : I64\n}\n```",
          f"{detail!r}")
    check(f"{encoding} definition on the struct declaration",
          locs((by_id(replies, 12) or {}).get("result")) == [("shapes.mo", SHAPES_STRUCT_NAME)],
          f"{locs((by_id(replies, 12) or {}).get('result'))}")
    hover = by_id(replies, 13)
    detail = ((hover or {}).get("result") or {}).get("contents", {}).get("value", "")
    check(f"{encoding} hover on a def's use", "def zz_replay_width" in detail, f"{detail[:80]!r}")
    check(f"{encoding} definition on a def's use",
          locs((by_id(replies, 14) or {}).get("result")) == [("shapes.mo", SHAPES_WIDTH_NAME)],
          f"{locs((by_id(replies, 14) or {}).get('result'))}")

    # 6. The shadowing case. Cursor is on the local's USE inside
    # `\zz_replay_shadowed => zz_replay_shadowed` (line 45); both features answer the
    # lambda binder -- its name, columns 5..23 -- and not `def zz_replay_shadowed` on
    # line 42, which it hides. The lambda is unannotated, so the hover is the bare name.
    check(f"{encoding} definition on a shadowing local answers its binder",
          locs((by_id(replies, 15) or {}).get("result")) == [("shapes.mo", (45, 5, 45, 23))],
          f"{locs((by_id(replies, 15) or {}).get('result'))}")
    hover = by_id(replies, 16)
    detail = ((hover or {}).get("result") or {}).get("contents", {}).get("value", "")
    check(f"{encoding} hover on a shadowing local answers its binder",
          detail == "```monad\nzz_replay_shadowed\n```", f"{detail!r}")

    # 6b. Across files. Each name in `farref.mo` is declared in the prelude, another
    # module, so its definition is that file at the declaration -- a constructor at its
    # type's. Only the file's basename and the start line are pinned: the declaration's
    # extent is the prelude's business.
    farref = [r for r in pubs if r["params"]["uri"].endswith("farref.mo")]
    ds = farref[0]["params"]["diagnostics"] if farref else ["(none published)"]
    check(f"{encoding} farref.mo: no diagnostics", len(ds) == 0, f"{ds[:1]}")
    for rid, what, needle in ((19, "type", "pub type Option A"),
                              (20, "class", "pub class Add A"),
                              (21, "constructor", "pub type Option A")):
        got = [(f, r[0]) for f, r in locs((by_id(replies, rid) or {}).get("result"))]
        check(f"{encoding} definition on a prelude {what} opens its declaration",
              got == [("prelude.mo", prelude_line(needle))], f"{got}")
    hover = by_id(replies, 22)
    detail = ((hover or {}).get("result") or {}).get("contents", {}).get("value", "")
    check(f"{encoding} hover on a prelude class renders the class",
          detail.startswith("```monad\npub class Add (A : Type) {"), f"{detail[:80]!r}")

    # 7. The workspace scan. `SymbolInformation`, so `locs()` takes the nested shape --
    # and the range is the same byte-exact decl span the definition feature answers.
    hits = locs((by_id(replies, 17) or {}).get("result"))
    check(f"{encoding} workspace/symbol finds the open buffer's declaration",
          hits == [("shapes.mo", SHAPES_STRUCT_RANGE)], f"{hits}")

    # 8. An unparseable message is answered, not fatal.
    bad = [r for r in replies if r.get("id") is None and "error" in r]
    check(f"{encoding} unparseable message: a -32700 error with a null id",
          any(r["error"].get("code") == -32700 for r in bad), f"{bad[:1]}")
    check(f"{encoding} session survived it", by_id(replies, 18) is not None)

    # Every request that was sent got an answer.
    sent = {json.loads(b)["id"] for k, b in messages(fixture, encoding)
            if k == "frame" and b.startswith(b"{") and b'"id"' in b}
    missing = sorted(i for i in (sent - {None}) if by_id(replies, i) is None)
    check(f"{encoding} every request answered", not missing, f"unanswered ids: {missing}")
    return p


# --- The truncated frame -----------------------------------------------------


def truncated():
    eof_fixture = os.path.join(fixture_dir, "eof-mid-message.jsonl")
    print(f"\n=== eof-mid-message: {os.path.basename(eof_fixture)}")
    if not os.path.exists(eof_fixture):
        check("eof fixture present", False, eof_fixture)
        return
    p, replies, _stray = run(messages(eof_fixture, "utf-8"), timeout=int(os.environ.get("LSP_TIMEOUT", "1800")))
    check("truncated frame: initialize was answered", by_id(replies, 1) is not None)
    check("truncated frame: clean exit", p.returncode == 0, f"exit={p.returncode}")
    err = p.stderr.decode("utf-8", "replace")
    check("truncated frame: no panic", "panic" not in err and "overflowed its stack" not in err,
          err.strip().splitlines()[-1] if err.strip() else "")


# --- Go ----------------------------------------------------------------------

# The table above is the expectation; this is the arithmetic behind it. A fixture
# edit that moves the offending byte fails HERE, with the numbers, rather than
# producing a mysterious range mismatch later.
non = os.path.join(fixture_dir, "nonascii.mo")
o = oracle(non, "«")
check("oracle: the fixture's offending byte is where the table says",
      NONASCII_AT_END["utf-8"] == ((o[0], o[1]), (o[0], o[2]))
      and NONASCII_AT_END["utf-16"] == ((o[0], o[3]), (o[0], o[4])),
      f"bytes {o[1]}..{o[2]}, units {o[3]}..{o[4]} on line {o[0]}")

for enc in ("utf-8", "utf-16"):
    session(enc)
truncated()

print()
if failures:
    print(f"FAILED {len(failures)} assertion(s):")
    for f in failures:
        print(f"  - {f}")
    sys.exit(1)
print("all assertions passed")
PY
