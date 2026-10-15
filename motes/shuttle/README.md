# shuttle

The Monad AI agent harness: a typed tool-use loop over a normalized
transcript, providers on two wire protocols, and any MCP server's tools
mounted as first-class tools. Owns `plans/implementations/agent-skills.md`.

## Building and running

```bash
monad build motes/shuttle/src/main.mo -o ./shuttle   # self-hosted compiled backend
./shuttle run "list the files here" --provider ollama --model qwen3:latest
```

`monad run` does not forward program arguments on the current CLI, so
build the binary and run it directly. Anything networked is
compiled-path only: the `tcp_*` natives have no Rust-host interpreter,
so the Rust host (`monad-rs`) is not a verification surface for this
mote.

```
usage: shuttle run "<task>"
  --provider ollama|mistral|openrouter|anthropic  (default ollama)
  --model <name>    (defaults: ollama qwen2.5-coder, mistral mistral-large-latest,
                    anthropic claude-opus-5; openrouter requires it)
  --max-turns <n>   (default 10, total across a save/resume)
  --mcp <exe>       (repeatable; bare executable, no arguments yet)
  --resume <file>   (continue a saved session)
  --save <file>     (checkpoint the final session)
```

## Architecture

```
message.mo / message_types.mo   Message/Usage/Turn, Role/Content/StopReason:
                                the normalized transcript every wire maps to
provider.mo / wire/*.mo         one seam, two wires: Provider.send builds the
                                request, the wire owns the bytes (openai,
                                anthropic, mock -- a scripted provider for
                                offline e2e)
presets.mo                      named ProviderConfigs (host, env var, wire)
tool.mo / registry.mo           ToolSpec + ToolImpl, a BTreeMap registry
                                (Loom-free; the Phase 3 fallback that stuck)
tools/*.mo                      shell/read/grep/glob built-ins
agent.mo / loop.mo               the loop as an IndexedMonad program over
                                phantom phases (Idle/Answered/Executing/Done):
                                ask-then-dispatch is a type-level fact
session.mo                      checkpointable transcript (JSON in, JSON out)
context.mo                      token estimation, history trimming, prefix
                                caching helpers
main.mo                         the CLI: parse, mount, run, report
```

The loop is turn-by-turn, not streaming (`http.md` still owes chunked
transfer encoding): a long response is a long silence. A tool failure
becomes an `is_error := true` tool_result the model can see and adapt
to, not a short-circuit of the run.

## Providers

| Provider | Wire | Transport | Key |
|---|---|---|---|
| ollama | OpenAI-compatible | plaintext `http://localhost:11434` | none (optional `OLLAMA_API_KEY`) |
| mistral | OpenAI-compatible | TLS `https://api.mistral.ai` | `MISTRAL_API_KEY` |
| openrouter | OpenAI-compatible | TLS `https://openrouter.ai/api` | `OPENROUTER_API_KEY` |
| anthropic | Anthropic Messages | TLS `https://api.anthropic.com` | `ANTHROPIC_API_KEY` (required) |

TLS rides `motes/tls` through moose: any `https` base_url opens a TLS
stream, so the remote presets are reachable, not placeholders. A missing
key fails at the server (401) rather than locally, except Anthropic,
which names its key at send time.

```bash
./shuttle run "fix the failing test" --provider anthropic --model claude-opus-5
MISTRAL_API_KEY=... ./shuttle run "review this diff" --provider mistral
./shuttle run "anything" --provider openrouter --model mistralai/mistral-large
```

## Tool authoring

A tool is a `ToolSpec` (name, description, JSON schema) plus a
`ToolImpl` whose `run` takes the model's tool-call id and the input
JSON, and returns `ResultT String IO Content`. Returning `Result.err`
marks the result `is_error := true` for the model; it does not abort
the run. The `tools/*_tools.mo` files are the templates: a
`ToolImpl` value, a schema built from the decoder's own keys, and a
`*_args.mo` deserialization module split out to keep derive-macro
capture passes happy. Register by nesting `ToolRegistry.register`.

Two invariants the harness cannot enforce for you: the schema must
declare exactly the keys the decoder reads (with `schema := Json.null`
the model guesses key names), and `run` must echo the id it was given in
its `Content.tool_result`.

## MCP servers

Each `--mcp <exe>` spawns a subprocess, completes the MCP `initialize`
handshake (`mcp_client::server`), and mounts every tool from
`tools/list` as a proxy `ToolImpl`: the model calls it like a built-in,
the proxy forwards to `tools/call` and maps the result's first text
block to a `tool_result`. Repeat `--mcp` to mount several servers;
mounted servers are disposed on every exit path. `--mcp` takes a bare
executable only (no argument list yet -- `String.split` does not exist),
so wrap argumented servers in a script.

## Sessions

`--save <file>` checkpoints the final session as JSON (transcript,
config, tool list, turn count, accumulated usage); a session file is
the latest state of a run, not an append-only log. `--resume <file>`
continues one: the loaded transcript is the model's context, the turn
and token accounting keep counting from where the file left off, and
`--max-turns` is the budget for the WHOLE session across both halves
(resume with `--max-turns` above the turns already spent). The registry
is closures and never round-trips: a resumed run gets a fresh one, and
its mismatch with the transcript's recorded tools is the caller's signal
to remount what the transcript references (a tool_use naming a tool no
fresh registry mounts comes back as an `is_error` tool_result the model
can see).

## Tests

```bash
monad test motes/shuttle        # 63 tests: codecs, context, session, mock e2e
monad test motes/shuttle/src/tests/ollama_e2e_tests.mo   # live, env-gated
```

`wire/mock.mo` scripts a provider through a JSON file of serialized
turns (`SHUTTLE_MOCK_TURNS`, or a PID-default temp path), which drives
the full indexed loop offline. The live e2e tests are env-gated
(`MONAD_SHUTTLE_OLLAMA_TESTS=1` etc.) against a local Ollama.
