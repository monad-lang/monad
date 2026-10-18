# The weaver TUI pty repro

Every UI-repair-pass finding was pinned with this driver BEFORE fixing,
against the compiled `target-monad/release/weaver` binary under a
python-driven pty (no interactive terminal needed):

```bash
python3 scripts/weaver-tui-repro/pty_repro.py
# or, against another binary / turn script:
WV_BIN=target-monad/release/weaver python3 scripts/weaver-tui-repro/pty_repro.py
```

The driver:

1. spawns the binary under a pty (24x80) with the `mock` provider and
   `SHUTTLE_MOCK_TURNS=…` pointing at a scripted JSON array of turns
   (a `tool_use` turn drives a `read` pick, so the approval overlay
   fires offline);
2. asserts the INITIAL FRAME renders with no keypress (the blank-on-
   start bug);
3. feeds a junk key before the trigger line, then `go\n` -- the overlay
   must come up and the junk must be drained;
4. presses `y` and asserts the immediate answer echo (`y -- approved`);
5. presses Ctrl+C once (hint line) and again (`ESC[?1049l` restore).

Note the assertions strip ANSI and whitespace before matching: cell
deltas interleave per-cell cursor/SGR codes, so a rendered phrase is
never contiguous in the raw byte stream.

## The scripted turns

Turn JSON is the same codec a session file uses: an array of serialized
`Turn`s (`message`/`usage`/`stop`), the served turn indexed by the
assistant count (`motes/shuttle/src/wire/mock.mo`). Two variants are
kept:

- `turns_two_reads.json` -- two `tool_use` turns (read, grep): drives
  the second-overlay path; answering `a` on the first must auto-run
  the second (the always-cache).
- `turns_edit.json` -- an `edit` pick: drives the diff overlay.

## Parser probes (`probes/`)

Ten-line repros for the three compiler findings recorded in the
UI-repair changelog; `monad check <probe>` shows each:

- `comment_after_assign.mo` -- a `--` comment line directly after
  `:=` breaks the parse (the def's body does not parse; the error
  reports misleading "remaining text" positions).
- `expr_project_bind_looser.mo` -- `(expr).field == rhs` parses as
  `(. expr) (field == rhs)`: the projection binds looser than `==`.
  Bind the expression to a `let` first.
- `over_application.mo` -- a two-arg def called with three arguments
  checks clean on both hosts and crashes at runtime.