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
## Round 2 (`pty_repro_round2.py`)

With `turns_long.json` (8 reply turns), on a 20-row pty: rounded border
glyphs render, the statusbar carries the dim manual-mode SGR, PageUp shows
the `N lines above` indicator, an SGR mouse wheel report scrolls,
Alt+Enter folds a newline and the multiline submit echoes on its own
lines (the pump after the submit must EXCEED the retry sleeps when the
mock script is exhausted -- 2s+4s of backoff before the turn fails).

## Async turns (`pty_repro_async.py`)

With `turns_slow.json`: the UI redraws while a turn runs, the streamed
fragment is visible mid-turn, mid-turn keys land in the input box, the
completion repaints from blank without re-emitting, one Ctrl+C mid-turn
only hints while two consecutive presses exit promptly, Esc shows the
`stopping…` row and ends the turn with `[stopped]` (the partial reply is
kept), and the approval overlay still owns stdin (a paste cannot answer
it) -- a rendered grid pins the stopping row because the cell diff
rewrites it non-contiguously.

## Resize (`pty_repro_resize.py`)

Spawns at 30x80, runs one mock turn with a 240-character reply, then
shrinks to 24x40 and grows to 32x100. A small ANSI grid emulator
reconstructs the screen and asserts that each geometry change emits a
real `ESC[2J` clear (blank cells emit no diff delta, so a clear is what
removes the old borders), that the bottom border lands on the new last
transcript row, and that the reply re-wraps to the new content width.

## Selection (`pty_repro_selection.py`)

Runs one mock turn with `hello 日本`, then sends SGR press/drag/release
reports over the text. Asserts the drag emits reverse-video SGR, and the
release writes an OSC 52 clipboard sequence carrying the base64 of
`hello` and (a second drag) `日本` -- wide glyphs selected whole.

## Dialogs (`pty_repro_dialogs.py`)

Drives the permission dialog with arrows + Enter (approving an `edit`
runs it), a note on a denial (`e`, text, Enter, `n`) reaching the model
as `denied: <note>`, and the plan-review dialog in plan mode (`/plan`),
including a revise note landing in the input box. A rendered grid also
asserts the dialog is GONE from the screen after confirm/deny, and that
the revise path leaves the app responsive (the stuck `modal`/
`turn_pending` bug). The mock fixture's
edit path is generated under the repro's temp root, not `/tmp/wv_repro`.

## Sessions (`pty_repro_sessions.py`)

Spawns with `WEAVER_SESSION_ROOT` and `HOME` pointed at a temp root, so
the developer's `~/.weaver` and config are untouched. S1 persists a
turn (checked in the block files and history, not just the frame), S2
resumes it, S3 pages a 1200-line synthetic session with Home, S4 keeps
a bracketed paste literal (exactly one `you:` prefix, one `alpha\nbeta`
user message), S5 runs a colored control and then `--no-color`, and S6
requires an 18 MB session to raise startup RSS no more than 10 MB over a
tiny-session baseline, flat while idle. The temp root is pid-qualified
and removed at exit unless `WV_SESSION_KEEP` is set; `WV_SESSION_TMP`
chooses its parent.

## Input (`pty_repro_input.py`)

Asserts the input caret is visible on the initial frame and after a
submit, a click before a character places the caret (typing `X` gives
`hXello`), and a drag across the input copies its text through OSC 52.

## Large plans (`pty_repro_bigplan.py`)

A generated 100 KB / 2000-line plan: the tail paints promptly, Home
reaches the first line, `/plan` opens promptly, an 8 KB bracketed paste
into the note completes, and Esc still closes the dialog. This is the
compiled-backend gate for the linear text pipeline (interpreted tests
cannot see the quadratic).

## Processes (`pty_repro_processes.py`)

A scripted turn calls `start_process` (an `exec sleep 30`), the approval
dialog is answered, `/processes` shows the task as running, and
`/processes kill <id>` reports killed; the pid is gone afterwards.

## Crash log (`pty_repro_crash.py`)

Spawns weaver with `WEAVER_LOG_DIR`/`WEAVER_DEBUG_LOG`, SIGKILLs the
first run, restarts, and asserts the restart prints the previous-session
warning and logs `ev=crash_detected`; a clean `/quit` writes
`ev=process_exit`.
