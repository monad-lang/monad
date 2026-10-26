# weaver

The interactive coding agent built on shuttle's harness: a slash-command
loop, a mode-based approval policy, settings persistence, and a terminal
UI over `motes/tui` -- auto-detected when stdin is a tty, with a
line-based fallback (`dumb.mo`) for everything else (piped input,
scripts, a non-tty CI run).

## Building and running

```bash
monad run motes/weaver/src/main.mo -- --provider ollama --model qwen3:latest
monad build motes/weaver/src/main.mo -o ./weaver
```

```
usage: weaver [--provider <name>] [--model <name>] [--max-turns <n>] [--mcp <exe>]...
              [--resume <id|file>] [--continue] [--no-color]
  --provider ollama|mistral|openrouter|anthropic|mock  (default ollama)
  --model <name>       (default: the provider's preferred model; /model
                        lists what the API actually serves)
  --max-turns <n>      (default 40, total across a save/resume)
  --mcp <exe>          (repeatable; bare executable, no arguments yet)
  --resume <id|file>   open a session directory/id or a /save checkpoint
  --continue           resume the newest session under ~/.weaver/sessions
  --no-color           disable the palette in both UIs (NO_COLOR works too)
```

Every flag overrides the settings files; see below. The session ends on
EOF, `/quit` or a crashed loop, and the mounted MCP servers are disposed
on every one of those paths.

## Architecture

```
policy.mo          Capability x Mode -> Decision (allow | ask | refuse),
                   pure, the whole safety story in one table
gate.mo            Gate.weaver: the mode + policy + approval prompt as
                   one Gate for shuttle's loop; approvals ride the SAME
                   read seam as the input (scriptable without a tty)
permissions.mo     session grants: {capability, repo|anywhere}, lexical
                   path containment, and the Ref the gate consults
settings.mo        ~/.weaver/config.toml under .weaver/config.toml,
                   merged field by field (project wins), caps unioned;
                   /settings saves the named keys back (unknown keys kept)
store.mo           the session store: transcript blocks, per-turn model
                   history, paged scrollback, ~/.weaver/sessions
commands.mo        the slash-command table (BTreeMap) and the
                   interactive State it advances
usage.mo           per-turn usage: last request (context) and turn delta
                   from shuttle's cumulative spend
monad_tools.mo     monad_check (compiler checker) and monad_eval (a
                   REPL-style scratch module on the self-hosted interpreter)
diff.mo            old -> new rendering for write/edit approvals,
                   picked out of the tool input
dumb.mo            the line loop: read -> command-or-model -> print,
                   turns charged against the budget; the non-tty fallback
model.mo           the TUI's pure half: TuiModel/WeaverMsg, on_event,
                   Model.view (transcript/status/input over motes/tui)
tui_app.mo         the TUI's IO half: TuiApp.update (closes over a
                   model turn or a slash command via Cmd.perform),
                   Gate.weaver_tui (the approval overlay), Tui.run
providers.mo       the provider presets (host, key env var, wire)
format.mo          token/elapsed display formatters (the thinking row)
overlay.mo         the dialog/stdin-ownership handshake and close sequence
stop.mo            the generation-guarded Esc stop signal
logs.mo            the debug log path/level/events and crash detector
procs.mo           detached background processes (pid/log/meta files)
process_tools.mo   start_process / read_process / kill_process / list_processes
subagent.mo        the read-only `task` subagent (child Loop.run_state)
main.mo            the entry: settings load, flag resolution, MCP
                   mount (proxy tools default exec-cap), Tui.run with
                   Dumb.run as its non-tty fallback
```

### The TUI

`monad run motes/weaver/src/main.mo` starts the TUI whenever stdin is a
tty (the same `Terminal.enter_raw_mode` degrade check `terminal.mo`
already uses for a non-tty stdin). The input box is 3 padded rows
with a visible reverse-block caret from the first frame (over the
placeholder, after every submit, and wherever a click lands); a left drag
selects input text and copies it through OSC 52, and typing or Backspace
replaces the selection. Alt+Enter folds a newline into it (Enter submits
the whole value, a multiline submission echoed on its own lines), and the
arrow keys pull prompt history -- ArrowUp recalls from an empty input, repeats walk
backward, ArrowDown steps forward back to the live edit. The mouse
wheel scrolls the transcript (3 rows a notch); a left DRAG selects
transcript text (reverse-video while dragging) and releasing copies it
through OSC 52 -- the terminal's own clipboard, also over SSH (tmux
needs `set-clipboard on`; Shift+drag usually keeps the terminal's
native selection). A fresh session opens with a colorful launch banner
(the shuttle sweeps once) that yields to the conversation on the first
submit. Tab cycles the
approval mode
(`manual -> plan -> allow_edit -> auto -> manual`), PageUp/PageDown
scroll a screen and Ctrl+U half a screen (End re-pins, Home jumps
to the top; new output auto-pins only when the window is already pinned
and the scrolled-up window shows a `N lines above -- PgDn for latest`
row instead). Scrolling is by wrapped DISPLAY ROW, so even a single
message taller than the panel is fully reachable. Enter submits a line;
the turn runs on a fiber while the UI keeps folding keys and 100 ms
ticks. A dim line under the last prompt shows the spinner, elapsed time
and THIS TURN's token delta (`| thinking 3.4s · ↑1.2k ↓345`),
which becomes `running <tool>` while a tool dispatches and `responding`
once text streams; the streamed text itself appears under the
transcript with a caret, dim, and is replaced by the real message when
the turn lands. The row refreshes at 1 Hz from the turn's usage file
and disappears when the result lands. The status bar separately shows
the CONTEXT (`ctx 12.3k/128k (10%)`, from the last request's real
prompt size) and cumulative `spent` — they are different quantities:
cumulative input sums the whole prompt of every model call. Keys typed mid-turn
land in the input box. Esc asks the
turn to stop: the row says `stopping…`, the in-flight model call or
foreground tool finishes, and the turn ends at the next boundary with a
`[stopped]` line -- the partial session is kept. Background processes
keep running and retry backoffs are not interrupted, so stop waits for
the current call; a stalled provider read is bounded by moose's request
timeouts instead. While a
dialog owns stdin the loop stops reading and drawing, and the dialog's
close forces a clear+repaint, so a confirmed prompt never lingers. An approval prompt (`manual`/`allow_edit`'s `ask`
cells) opens a centered dialog: the diff for a `write`/`edit` pick,
then `Approve once` / `Always allow all <cap>s in this repo` /
`Always allow all <cap>s this session (anywhere)` / `Deny` with the safe
option highlighted. Arrows (or j/k) select, Enter confirms, `y`/`r`/`a`/
`n` are shortcuts, `e` opens an optional note, Esc cancels, and a
bracketed paste edits only the note -- it can never answer the prompt. A
note on `Deny` becomes the denial reason the model reads; a note on an
approval is appended to the tool result. `r` grants the capability for
path-bearing picks INSIDE the workspace root (lexical containment, not a
sandbox); `a` grants it anywhere for the rest of the session. The grants
live in weaver (not shuttle's per-capability cache), are cleared on
`/clear` and `/resume`, and `/permissions` lists or revokes them; plan
mode's refusal is re-checked before every pick, even a granted one. In plan mode `/plan` opens a `Plan ready`
dialog over the last assistant message: approve to `allow_edit` or to
`manual`, revise with a note (the note lands in the input box), or
cancel. Two Ctrl+C presses in a row, or two Ctrl+D presses in a row
(no other key between), exit cleanly through the restore path -- cbreak
has ISIG off, so Ctrl+C arrives as a key rather than SIGINT; a single
press just prints a hint. Each gesture arms only itself: Ctrl+C
followed by Ctrl+D does not exit. Ctrl+D is the exit gesture and no
longer scrolls (PageUp/PageDown and Ctrl+U remain); while the model
picker is open it is swallowed. Both presses work while a turn runs
(Esc is the stop gesture there); while a dialog is open, Ctrl+C cancels
that dialog instead. A piped or scripted run
(stdin not a tty) falls back to the line-based UI above automatically;
there a single Ctrl+D is EOF and exits.

Long transcript lines wrap (word-wrap at the last fitting space) by
terminal CELLS, not bytes: UTF-8 text (`æøå`, CJK, emoji, combining
marks) is measured and painted at its real width. Scrolling moves by
wrapped ROW, so every row of a message taller than the panel is
reachable. A resize clears and repaints at the new geometry instead of
leaving old borders behind. A bracketed paste lands as literal text in
the input box, newlines included -- Enter submits it, so a pasted
multi-line snippet is one prompt. `--no-color` (or `NO_COLOR`) turns the
palette off in both UIs.

The `mock` provider is shuttle's scripted wire: a JSON array of turns at
`/tmp/shuttle_mock_turns_<pid>.json` (or `SHUTTLE_MOCK_TURNS`), indexed
by assistant count. The e2e tests (`src/tests/`) drive the whole loop --
approvals, plan-mode refusals, a real edit with its diff -- through it,
offline.

## Modes

| Mode | Read | Write | Exec/Net |
|---|---|---|---|
| `manual` | ask | ask | ask |
| `plan` | allow | refuse | refuse |
| `allow_edit` | allow | allow | ask |
| `auto` | allow | allow | allow |

`plan` mode is read-only: the model inspects and proposes, then `/plan`
opens the review dialog (or, in the line-based UI, `/plan approve
manual|allow_edit` is the ONE constrained way out; a one-word escalation
to `auto` is refused by design). `auto` is a trust
setting, not a sandbox -- the gate is advisory; it also flips the
warning flag shuttle's loop prints.

## Commands

```
/mode [manual|plan|allow_edit|auto]  show or set the approval mode
/budget [n]                          show or raise the model-call budget
/model [name]                        show/pick (TUI) or set the model
/compact [instructions]              summarize the context, keep a recent tail
/thinking [on|off]                   show or set the provider's reasoning channel
/provider [ollama|mistral|openrouter|anthropic|mock] [model]  show or set the provider
/plan [approve manual|allow_edit]    show the current plan; approve leaves plan mode
/permissions [allow|revoke ...]      list or manage session approval grants
/settings [<key> <value>|save project|global]  change or save settings
/tools                               list tools with their capability tags
/processes [kill <id>]               list background tasks (a snapshot)
/log                                 the debug log path, tail and crash note
/mcp                                 list mounted MCP servers
/save <file>                         checkpoint the session
/resume [<id>]                       pick a saved session (TUI dialog) or load one by id
/name [<text>|-]                     show, set or clear this session's name
/describe [<text>|-]                 show, set or clear this session's description
/clear                               drop the transcript and reset the budget
/help (or /h)                        this table
/quit (or /q)                        exit (MCP servers are disposed)
```

Two Monad-aware tools are registered for the model: `monad_check`
type-checks a file (`path`) or an in-memory buffer (`source`) with the
compiler's own checker, and `monad_eval` runs a REPL-style scratch
module on the self-hosted interpreter -- `def` snippets accumulate for
the session, bare expressions get a typed `main`, and a snippet with
`def main` runs whole. Eval is pure (I64/String natives, no IO) and
tagged `exec`, so `allow_edit`/`manual` ask before it runs.

The provider decides which models exist: `/model` with no argument
fetches its `/v1/models` list (the mock wire answers `mock` offline),
caches it for the session, and opens a picker in the TUI (the line UI
prints the list); dismissing the picker leaves the transcript untouched.
`/model <name>` sets a name as given
-- when a fetched list does not contain it, the output says so but the
name is still selectable (an API list can be partial). The settings
`model` is used as-is; no built-in family table rewrites or refuses it.
Without a list, `/provider mistral` starts from its preferred name
(`mistral-large-latest`); a fetched list picks the preferred name when
listed, else the first model returned. OpenRouter has no preferred name,
so `/provider openrouter` fetches its list (or takes an explicit model).

Every provider request has a timeout: one 30 s deadline covering
connect, write and response for one-shot calls, a 120 s per-read idle
bound while streaming, so a blackholed host, a peer that stops reading,
or a silent connection fails instead of hanging.

MCP servers mount with `--mcp <executable>`; their proxy tools default
to `exec` capability (a server's catalogue is arbitrary code) and are
listed by `/mcp`.

## Background processes

`start_process {command, cwd}` launches a detached `sh -c` with merged
stdout/stderr under `<sessions root>/procs/p-<pid>/` (`WEAVER_PROC_ROOT`
overrides); `read_process {id}` returns status, elapsed time and the last
40 output lines, `list_processes` lists them, and `kill_process {id}`
sends TERM then KILL. `/processes` prints the same snapshot and accepts
`kill <id>`. Tasks are killed when weaver exits (`WEAVER_PROC_KEEP` opts
out). Limitations: no process group (a detached grandchild can survive a
kill), the log file is not size-capped, and a task can outlive a weaver
crash (its files remain under the proc root).

## Logging and crash reports

Each run appends an `ev=` event log under `<sessions root>/debug/`:
startup/session, submits, turn outcomes and usage, settings warnings,
retries, subagent events and `process_exit`. `WEAVER_LOG` sets the level
(`trace|debug|info|warn|error|off`, default info), `WEAVER_LOG_DIR`
the directory, `WEAVER_DEBUG_LOG` one exact file, and
`WEAVER_LOG_FORMAT=json` switches every line to one JSON object
(`{"fields":{...},"level":"INFO","msg":"...","ts":...}`) for machine
consumption. API keys, prompts and file contents are never logged. A run that dies without `process_exit`
is reported by the next launch (`warning: previous session ended
unexpectedly (log: …)`) and logged as `crash_detected`; `/log` prints the
newest log's path, last 20 lines and any crash note. The runtime has no
signal handler/backtrace, so the last logged event is the crash-location
evidence.

## Subagents (design)

`task {prompt, max_turns}` runs one read-only child loop (read/grep/glob,
`Gate.read_only`, depth 1) and returns its plan plus a usage footer. The
fuller roadmap (execute phase, `/agents`, background/parallel children,
approval forwarding) is in [SUBAGENTS.md](SUBAGENTS.md).

## Settings

Two TOML files, in resolution order GLOBAL -> PROJECT -> RUNTIME:

```
~/.weaver/config.toml     the user's defaults
.weaver/config.toml       the project's (gitignored); wins per field
--provider/--model/--max-turns and /mode, /model, /provider at runtime
```

```toml
mode = "plan"          # manual | plan | allow_edit | auto
provider = "ollama"
model = "qwen3:8b"     # used as-is; /model lists the API's catalogue
max_turns = 100        # model calls per session (raise with /budget)
thinking = false       # ask for the provider's reasoning channel
max_tokens = 4096      # per-response output budget (weaver's default; 512 cuts off tool calls)
context_window = 128000  # the window autocompact measures against; when unset,
                       # the provider's own default is used (Ollama 32k,
                       # Mistral/OpenRouter 128k, Anthropic 200k)
compact_at = 80        # autocompact at this percentage of it (0 disables)

[mcp_caps]             # per-server capability override, keyed by the
my-server = "read"      # exact --mcp executable: read | write | exec | net

[api_keys]             # per-provider API keys, keyed by provider name:
mistral = "..."         # ollama | mistral | openrouter | anthropic
```

A missing or unparsable file contributes nothing; a bad value drops its
own entry, never the file. Unknown top-level keys are ignored but
reported in the startup warnings (the TUI's first transcript block, or
stderr in the line-based UI), with a near-miss hint -- `[api_key]`
instead of `[api_keys]` would otherwise be silently dead. The entries
inside `[mcp_caps]` and `[api_keys]` are free-form and never warn. The
built-in floor is ollama / the provider's default model / 100 turns /
the provider's window / manual mode.

`/settings` opens a dialog (TUI) or prints the rows (line UI): Enter
cycles a curated value, `/settings <key> <value>` sets one exactly, and
`save project` / `save global` write the current values back to the
named file. A save preserves unknown keys and other tables; it refuses
to overwrite a file that does not parse. API key values are never
displayed.

### Colors

The dumb UI follows the informal standard: colors are ON unless
`NO_COLOR` is set (the TUI honors the same rules: `NO_COLOR` or
`--no-color` turns its palette off too). A submitted prompt is one
cyan block carrying its role as data -- no `you:`/`assistant:` text
prefix -- separated from the reply by a blank line; the reply is plain.
The remaining lines classify by semantic prefix: `[running]` rows dim
cyan, `error:`/`denied:`/`refused:` lines and diff `-` rows red, diff
`+` rows green, the Ctrl+C/Ctrl+D hints dim. Old sessions that stored the v1
`you:`/`assistant:` prefixes migrate on read. The status bar is dim
terminal-default foreground in manual mode (the one place that reads as
chrome, not content), dim YELLOW
in `allow_edit`, GREEN in plan mode (the read-only trust state) and red
while `auto` mode is on (the trust warning). Borders are dim. Both UIs use
the same classification (`theme.mo`: one LineClass enum, rendered by
`class_style` in the TUI and `class_code` in dumb mode).

### Retries

A failed provider call gets 3 attempts by default (backoff sleeps of
2s then 4s before the second and third tries), each retry announced as
`retrying (n/3): <error>` through the same live sink the turn's text
streams through. The classification scans only the error's first bytes
(the status marker lives there): a 4xx status error is NOT retried --
a malformed request or an unknown key fails identically on every
resend -- except 429 (rate limiting). The headless default is one
attempt, byte-identical to the pre-retry loop.

## Sessions

A run that can open the store writes to `~/.weaver/sessions/<id>/`
(`id` is `s-<pid>`, with `-2`, `-3`, ... when that directory exists):
`meta.json` (session config, turn/spend totals), `transcript/` (rendered
lines in append-only blocks, with a small `index.json` cache), and
`history/` (each turn's model messages). `WEAVER_SESSION_ROOT` overrides
the root; when HOME is unset or the root is not writable the run
degrades to the pre-store in-memory behavior with one warning line. The
line-based (piped) UI persists the per-turn history only -- it has no
rendered transcript to store.

The TUI keeps only a window: the last 512 transcript lines plus at most
one older page. Scrolling above that reads the needed blocks back from
disk, so the full scrollback is reachable while memory stays bounded.
The model's conversation history (what a provider call needs) remains
in memory by design; the rendered copy no longer accumulates.

Bare `/resume` opens a picker of the saved sessions, newest first: each
row carries the session's **name** and a one-line **description**, the
current session is marked `(current)`, and a list longer than a screen
pages with `Older sessions…`/`Newer sessions…` rows. Choosing a row loads
that session, transcript and history both. In the line UI the same
command prints the list; `/resume <id>` loads a session id, `/resume
<dir>` a directory, and `/resume <file>` a `/save` checkpoint (imported
into a new session directory). `--resume <id>` and `--continue` do the
same at startup. `/clear` starts a NEW session directory and leaves the
old one resumable.

A session's name is its first user message (one line, byte-capped) and
its description is the first assistant text; both are captured at the
first turn's meta write, so a later compaction does not lose them.
`/name <text>` and `/describe <text>` override them (`-` clears the
override, so the next turn re-derives), and a rename never reorders the
picker. Older sessions with neither field fall back to their directory
id.

A streamed TUI turn's text is appended to `live.txt` as it arrives; a
turn that completes removes it, and one interrupted by a crash leaves
it as an `[interrupted turn output]` block on the next resume (never
fed to the model). Writes are process-crash safe, not power-loss safe
(there is no fsync native), and two processes must not resume the same
session directory at once.

### API keys

An `[api_keys]` entry wins over the provider's env var (`MISTRAL_API_KEY`
and friends stay the fallback when the file does not speak for a
provider); there is deliberately no `--api-key` flag -- a key on a
command line leaks into shell history and `ps`.

Keys are plaintext on disk. `~/.weaver/config.toml` is the recommended
home for them; the project file is gitignored but plaintext is
plaintext, and a key that came from there prints one startup warning
naming the providers. A saved session (`/save`) never contains key
material -- the checkpoint keeps only the env var name, and a resumed
session re-resolves its key from settings/env at startup.

## Context management

`/compact [instructions]` summarizes the conversation (one provider call through the same model) and replaces the MODEL history with that summary plus a recent tail; the visible transcript is untouched. Autocompact runs the same step automatically before a turn when the estimated context (`history + system prompt + tool schemas`) crosses `compact_at` percent of `context_window`; a zero `context_window` disables it. A failed summarization leaves the session intact and only notes it. The compacted history is persisted as a new history block and a resume replays only from there.

Ctrl+O shows the detail lines hidden by default: tool output beyond its first three lines, and completed thinking blocks.
