# LSP fixtures

Input for `scripts/replay-lsp-session.sh`, which replays one LSP session per position
encoding against a server and asserts the milestone's criteria on the wire. Run it as

```sh
# The host interpreting the self-hosted server -- how these were developed, NOT the gate.
scripts/replay-lsp-session.sh fixtures/lsp/session.jsonl \
  ./target/release/monad-rs run cli/src/main.mo lsp

# The gate: the compiled binary's own `lsp` subcommand.
scripts/replay-lsp-session.sh fixtures/lsp/session.jsonl ./out/monad lsp
```

The distinction matters. The whole point of the LSP being written in Monad is that it
ships *inside the compiler*, so the interpreted run says nothing about codegen, and a
green interpreted run is evidence about the protocol layer only.

## The session format

One message per line. Three line kinds:

| Line | Meaning |
|---|---|
| JSON | A message. Framed as `Content-Length: N\r\n\r\n` + body and written to stdin. |
| `!raw …` | Literal bytes, written to stdin verbatim. `\r`, `\n`, `\t`, `\\`, `\"` and `\xNN` are unescaped. |
| anything else | A deliberately malformed frame: the line is still *framed*, so the server reads a complete body, but the body is not JSON. |
| blank, or starting `#` | Skipped. |

Two placeholders are substituted per run, which is why a session can be replayed twice:
`@ROOT@` is the repository root, and `@ENCODINGS@` is the single position encoding the
client offers that run. One encoding per connection is the point — `initialize` lets the
client *narrow* the list and the server choose from it, so a session that must exercise
both ranges is run twice with `positionEncodings` a single element.

Inside a `didOpen`, a `"text"` value of `"@name.mo"` is replaced by that file's bytes, so
the buffer the server sees is the same file on disk that the assertions talk about.

## The hand-computed table

`nonascii.mo`'s only non-ASCII code line ends in `«` (U+00AB), which the parser does not
accept anywhere, so the parse stops there and the one diagnostic's range is that byte's
own extent. The comment block at the top of the file is deliberately ASCII, so the
offending byte's offset is unambiguous and this table can be checked by eye.

The bytes before it on line 17 (0-based):

| Run | Bytes |
|---|---|
| `def zz_replay_broken : String := "a` | 35 |
| `—` (U+2014, three bytes in utf-8, one code unit in utf-16) | 3 → 38 |
| `b" ++ ` | 6 → **44** |
| `«` (two bytes in utf-8, one unit in utf-16) | → 46 / 45 |

So the diagnostic's range is

| Encoding | Start | End |
|---|---|---|
| `utf-8` | (17, 44) | (17, 46) |
| `utf-16` | (17, 42) | (17, 43) |

Both are asserted literally **and** recomputed from the file's bytes by the script's
oracle before any session runs, so a fixture edit that moves the offending byte fails
loudly with the numbers rather than silently re-deriving an expectation that then agrees
with a buggy server.

A type error would not do here: its range is a declaration's whole-line span, which lands
on a line boundary, and a column that lands on a line boundary is zero under every
encoding and tests nothing. The difference is only observable mid-line.

### The same position, spelled three ways

The wire range is not the only place that position appears, and the spellings disagree:

| Where | Line | Column | Counts |
|---|---|---|---|
| wire range, `utf-8` | 17 | 44 | bytes, 0-based |
| wire range, `utf-16` | 17 | 42 | code units, 0-based |
| the diagnostic's `message` | 18 | 43 | **characters, 1-based** |

The message is computed from the source alone, so it is identical under both encodings —
which is why the script asserts it once and not per-encoding. The message exists for
`monad check`'s terminal, where a human wants 1-based characters; the range exists for an
editor, which wants 0-based units in the encoding it negotiated. All three numbers are
pinned so that unifying them later is a deliberate change rather than an accident.

## The files

| File | What it pins |
|---|---|
| `session.jsonl` | The whole milestone: handshake, one diagnostic with a correctly-ranged non-ASCII position, a clean file, the outline, hover and definition in-file, a shadowing local, the workspace scan, an unparseable message, and a clean exit. |
| `eof-mid-message.jsonl` | A frame truncated by end of input: the answer to the last complete request still arrives and the server exits cleanly. |
| `nonascii.mo` | The parse-error vector, and the only fixture whose offsets differ between encodings. |
| `shapes.mo` | One declaration of every kind the picker has a word for, plus a local that shadows a def. Pure ASCII, so every position in it is the same number in bytes and in code units. |

### What `session.jsonl` pinned *as a gap*

No assertion pins a known defect any more; the two that did have flipped. The shadowing
pin flipped with the cursor-to-binding walk: `definition` and `hover` on the local's use
inside `\zz_replay_shadowed => zz_replay_shadowed` answer the lambda's binder, line 45
columns 5..23. The struct pin flipped with struct hover: hover on `ZzReplayShape`'s
declaration renders the struct (`show_struct`) instead of its bare name.

Two more measured oddities are pinned rather than fixed, both in `lang/` and both shared
with other work:

- **An unnamed instance lists in the picker as `_`.** That is the parser's own sentinel —
  `instance_try_named` (`lang/src/parser.mo:3394`) defaults the name to
  `Identifier.id "_"` — not an LSP accident.
- **`def` ranges are whole lines; `struct`/`type`/`class`/`instance` ranges are byte-exact
  to one past the closing brace.** So `struct ZzReplayShape {` at line 16 through `}` at
  line 19 is `(16,0)..(19,1)`, not `(16,0)..(21,0)`. Both come from the same table by
  different mechanisms.
