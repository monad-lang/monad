# Monad Tools — Claude Code plugin

Two servers, from two different binaries built out of this repo.

**A language server** — `lspServers.monad` in `plugin.json`, bound to `.mo`
files. This is the **self-hosted** `monad lsp` (`motes/lsp`, written in Monad),
which gives Claude Code diagnostics after edits, hover, go-to-definition, and
document/workspace symbols through its built-in LSP tool. `rust/rust-cli` also has
an `lsp` subcommand, and the plugin deliberately does **not** point at it: the
Rust servers are deprecated and the self-hosted one is the deliverable.

**An MCP tool set** — described below, and unaffected by the above. The two are
complementary rather than alternatives: LSP is what the editor-side tooling
speaks, while the MCP tools are callable operations with arguments the LSP
protocol has no equivalent for (`organize_imports`, `test`, and the
`workspace: true` scans).

Exposes the `monad-rs mcp` server (`rust/rust-cli/src/mcp.rs`) as an MCP tool set for
Claude Code, so Claude can call `check`/`symbols`/`hover`/`definition`/
`organize_imports`/`test` directly instead of shelling out to `monad-rs
check --json ...`. `check`, `symbols`, `organize_imports`, and `test` are
all workspace-aware: they accept a `workspace: true` argument to scan the
whole resolved mote graph (the project's own `src/` plus every dependency
mote's `src/`) instead of an explicit file list, and `hover`/`definition`
fall back to a workspace-wide search when the identifier isn't defined in
the queried file (e.g. something imported via `use OtherMote {name}`).

## Setup

The plugin runs a **prebuilt release binary**, not `cargo run` — build it
once before first use, and again after pulling changes that touch `rust/rust-cli/`
or `rust/core/`:

```sh
cargo build --manifest-path rust/Cargo.toml --release --package monad-cli
```

This produces `rust/target/release/monad-rs`, which `plugin.json`'s
`mcpServers.monad.command` points at via `${CLAUDE_PLUGIN_ROOT}` (the
plugin's own root — this repo's root, when loaded locally as below).

### The language server needs a different, much slower build

`lspServers.monad.command` points at
`target-monad/bootstrap-ci/monad` — the **self-hosted** compiler, which cargo
does not produce. It comes from the bootstrap ladder:

```sh
scripts/build-self-hosted.sh "$PWD/target-monad/bootstrap-ci" --release
```

That is the path `scripts/lib/bootstrap-dir.sh` defines (per-checkout by
design, so sibling worktrees do not share one scratch compiler), and it is what
CI's own ladder builds, so an ordinary `compiler-checks` run leaves it in
place. Two consequences worth knowing:

* **It is absent until you run that.** The ladder interprets the compiler with
  the Rust host and takes ~18–20 minutes cold. Until then the LSP entry points
  at a file that does not exist; Claude Code reports the server as failed and
  the MCP tools keep working regardless.
* **`monad clean --all` deletes it**, since it lives under the monad target
  directory. That is right for scratch, but it means a `clean` costs a full
  rebuild of the language server.

Verify the binary before trusting the entry — it must answer a frame, not just
exist:

```sh
printf 'Content-Length: 58\r\n\r\n{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' \
  | target-monad/bootstrap-ci/monad lsp
```

A working server replies with a `Content-Length` frame whose result carries
`capabilities` and `serverInfo.name: "monad-lsp"`.

## Install (local, no marketplace/GitHub remote needed)

This repo is both the plugin and a self-referencing local marketplace
(`.claude-plugin/marketplace.json`'s one entry has `"source": "./"`), so
it installs straight from a local clone:

```
/plugin marketplace add /path/to/monad-lsp
/plugin install monad-tools@monad-tools
```

Restart your Claude Code session after installing (or after `/plugin
update`) — like any newly added MCP server, the tools don't appear in an
already-running session. Verified end-to-end on 2026-08-08: `claude mcp
list` reports `plugin:monad-tools:monad: .../rust/target/release/monad-rs mcp
- ✔ Connected`, and because the marketplace source is this local
directory (not a copied/cached snapshot), `${CLAUDE_PLUGIN_ROOT}`
resolves to the live repo — a `cargo build --manifest-path rust/Cargo.toml --release` here takes effect
immediately, no reinstall needed.

## Scope

Bundling a prebuilt binary *inside* the plugin package (for distributing
to people who haven't cloned/built this repo) and a companion Skill/
slash-command wrapper are both out of scope for this first pass — see
`rust/rust-cli/src/mcp.rs`'s own module doc comment for what the MCP server itself
does and doesn't cover (e.g. `run` isn't a tool yet — executing a
program's `main` is a fundamentally different, still-unstructured
problem than running `#[test]` defs, which `test` now covers).
