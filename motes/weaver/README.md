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
  --provider ollama|mistral|openrouter|anthropic|mock  (default ollama)
  --model <name>       (default: the provider's preset model)
  --max-turns <n>      (default 40, total across a save/resume)
  --mcp <exe>          (repeatable; bare executable, no arguments yet)
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
settings.mo        ~/.weaver/config.toml under .weaver/config.toml,
                   merged field by field (project wins), caps unioned
commands.mo        the slash-command table (BTreeMap) and the
                   interactive State it advances
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
main.mo            the entry: settings load, flag resolution, MCP
                   mount (proxy tools default exec-cap), Tui.run with
                   Dumb.run as its non-tty fallback
```

### The TUI

`monad run motes/weaver/src/main.mo` starts the TUI whenever stdin is a
tty (the same `Terminal.enter_raw_mode` degrade check `terminal.mo`
already uses for a non-tty stdin). Tab cycles the approval mode
(`manual -> plan -> allow_edit -> auto -> manual`), PageUp/PageDown
scroll a page and Ctrl+U/Ctrl+D half a page (End re-pins, Home jumps to
the top; new output auto-pins only when the window is already pinned
and the scrolled-up window shows a `N lines above -- PgDn for latest`
row instead). Enter submits a line and blocks the UI for that one turn
or slash command -- there is no non-blocking fiber-poll primitive in
`std/concurrent` to animate a spinner meanwhile, so the wait is what a
turn costs; what the model streams meanwhile shows on the status row
(`[thinking] ...`, overwritten in place, wiped when the turn's
transcript lands). An approval prompt (`manual`/`allow_edit`'s `ask`
cells) takes over the whole screen for one `y`/`n`/`a` keypress, diff
included for a `write`/`edit` pick; the answer echoes back immediately
and keystrokes typed while the model call was blocking are drained,
not fed to the answer read. `a` approves every pick of that capability
for the WHOLE session -- one `a` on a read is repo-wide read access
until `/clear` or exit. Two Ctrl+C presses in a row (no other key
between) exit cleanly through the restore path -- cbreak now has ISIG
off, so Ctrl+C arrives as a key rather than SIGINT; a single press just
prints a hint, and DURING a turn Ctrl+C is only queued (a truly hung
tool still needs `/quit` once the turn ends). A piped or scripted run
(stdin not a tty) falls back to the line-based UI above automatically.

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

`plan` mode is read-only: the model inspects and proposes, then
`/plan approve manual|allow_edit` is the ONE constrained way out (a
one-word escalation to `auto` is refused by design). `auto` is a trust
setting, not a sandbox -- the gate is advisory; it also flips the
warning flag shuttle's loop prints.

## Commands

```
/mode [manual|plan|allow_edit|auto]  show or set the approval mode
/model [name]                        show or set the model
/provider [ollama|mistral|openrouter|anthropic|mock]  show or set the provider
/plan [approve manual|allow_edit]    plan-mode status; approve drops plan mode
/tools                               list tools with their capability tags
/mcp                                 list mounted MCP servers
/save <file>                         checkpoint the session
/resume <file>                       continue a saved session (budget spans both halves)
/clear                               drop the transcript and reset the budget
/help                                this table
/quit                                exit (MCP servers are disposed)
```

MCP servers mount with `--mcp <executable>`; their proxy tools default
to `exec` capability (a server's catalogue is arbitrary code) and are
listed by `/mcp`.

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
model = "qwen3:8b"
max_turns = 20

[mcp_caps]             # per-server capability override, keyed by the
my-server = "read"      # exact --mcp executable: read | write | exec | net

[api_keys]             # per-provider API keys, keyed by provider name:
mistral = "..."         # ollama | mistral | openrouter | anthropic
```

A missing or unparsable file contributes nothing; a bad value drops its
own entry, never the file. The built-in floor is
ollama / the provider's default model / 40 turns / manual mode.

### Colors

The dumb UI follows the informal standard: colors are ON unless
`NO_COLOR` is set (the TUI always colors its own screen). Transcript
lines classify by prefix -- user lines and running rows dim (the
running row cyan), `error:`/`denied:` lines and diff `-` rows red, diff
`+` rows green, the status bar dim with the mode chip red (`auto`,
the trust warning) or cyan (`plan`). Both UIs use the same
classification (`theme.mo`).

### Retries

A failed provider call retries up to 3 times by default (2s, 4s, 6s
backoff), each attempt announced as `retrying (n/3): <error>`. A 4xx
status error is NOT retried -- a malformed request or an unknown key
fails identically on every resend -- except 429 (rate limiting). The
headless default is one attempt, byte-identical to the pre-retry loop.

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
