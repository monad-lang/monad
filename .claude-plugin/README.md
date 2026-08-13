# Monad Tools — Claude Code plugin

Exposes the `monad-rs mcp` server (`cli/src/mcp.rs`) as an MCP tool set for
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
once before first use, and again after pulling changes that touch `cli/`
or `core/`:

```sh
cargo build --release --package monad-cli
```

This produces `target/release/monad-rs`, which `plugin.json`'s
`mcpServers.monad.command` points at via `${CLAUDE_PLUGIN_ROOT}` (the
plugin's own root — this repo's root, when loaded locally as below).

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
list` reports `plugin:monad-tools:monad: .../target/release/monad-rs mcp
- ✔ Connected`, and because the marketplace source is this local
directory (not a copied/cached snapshot), `${CLAUDE_PLUGIN_ROOT}`
resolves to the live repo — a `cargo build --release` here takes effect
immediately, no reinstall needed.

## Scope

Bundling a prebuilt binary *inside* the plugin package (for distributing
to people who haven't cloned/built this repo) and a companion Skill/
slash-command wrapper are both out of scope for this first pass — see
`cli/src/mcp.rs`'s own module doc comment for what the MCP server itself
does and doesn't cover (e.g. `run` isn't a tool yet — executing a
program's `main` is a fundamentally different, still-unstructured
problem than running `#[test]` defs, which `test` now covers).
