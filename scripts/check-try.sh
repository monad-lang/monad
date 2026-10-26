#!/usr/bin/env bash
# usage: check-try.sh [path/to/monad]
#
# Builds the /try modules through `scripts/build-try.sh` (so the deploy
# path itself is exercised) and drives them through the Node harnesses:
# the staging ABI, the engine's evaluation contract, and the Oak UI's
# run/poll/render/cancel loop over a fake Worker. Requires WASI_SDK_PATH
# (the dev shell sets it) and node.
set -euo pipefail

MONAD="${1:-${MONAD:-monad}}"
: "${WASI_SDK_PATH:?WASI_SDK_PATH must name a wasi-sdk installation}"

command -v node >/dev/null 2>&1 || {
    echo "error: node is required (the dev shell provides it)" >&2
    exit 1
}

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

tmp=$(mktemp -d "${TMPDIR:-/tmp}/monad-try-check.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

# `try_abi_smoke.mjs` imports the repo's generated loader; build-try.sh
# generates its own copy later, but this harness runs first.
MONAD="$MONAD" "$repo_root/scripts/gen-web-js.sh"

echo "== /try staging ABI =="
"$MONAD" build --target wasm32-unknown-unknown fixtures/wasm/try_abi.mo \
    -o "$tmp/try_abi.wasm" --no-cache
node wasm/web/try_abi_smoke.mjs "$tmp/try_abi.wasm"

echo "== /try build (scripts/build-try.sh) =="
MONAD="$MONAD" "$repo_root/scripts/build-try.sh" "$tmp"

echo "== /try worker protocol =="
node wasm/web/try_worker_smoke.mjs "$tmp"

echo "== /try engine =="
node wasm/web/try_engine_smoke.mjs "$tmp"

echo "== /try UI =="
node wasm/web/try_ui_smoke.mjs "$tmp/try_ui.wasm"

echo "ok: /try checks passed"
