# weaver

The interactive coding agent built on shuttle's harness: a slash-command
loop, a mode-based approval policy, and settings persistence -- the
line-based UI (a terminal UI is planned, gated on terminal-ui's raw-mode
natives).

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
                   turns charged against the budget
providers.mo       the provider presets (host, key env var, wire)
main.mo            the entry: settings load, flag resolution, MCP
                   mount (proxy tools default exec-cap), the loop
```

The `mock` provider is shuttle's scripted wire: a JSON array of turns at
`/tmp/shuttle_mock_turns_<pid>.json`, indexed by assistant count. The
e2e tests (`src/tests/`) drive the whole loop -- approvals, plan-mode
refusals, a real edit with its diff -- through it, offline.

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
my-server = "read"     # exact --mcp executable: read | write | exec | net
```

A missing or unparsable file contributes nothing; a bad value drops its
own entry, never the file. The built-in floor is
ollama / the provider's default model / 40 turns / manual mode.
