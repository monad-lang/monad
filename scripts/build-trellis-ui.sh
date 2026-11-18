#!/usr/bin/env bash
# Build trellis's browser UI (motes/trellis_ui) into a servable directory.
#
# Run inside `nix develop` (web builds need WASI_SDK_PATH, llc, clang):
#   nix develop --no-pure-eval --accept-flake-config -c scripts/build-trellis-ui.sh [out]
#
# Writes (default target-monad/trellis-ui):
#   index.html, trellis_ui.wasm, web.js, web_runtime.js, float_format.js
#
# `trellis serve <mote>...` serves this directory and adds the two files the
# page fetches at run time: `graph.tsv` (the extracted graph) and
# `trellis.css` (the oak_ui sheet plus trellis's own rules).
# MONAD selects the compiler (default: `monad` on PATH).
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
out="${1:-$root/target-monad/trellis-ui}"
monad="${MONAD:-monad}"

mkdir -p "$out"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/monad-trellis-ui.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT

"$monad" build --target wasm32-unknown-unknown "$root/motes/trellis_ui" --bin trellis_ui \
    -o "$tmp/trellis_ui.wasm" --no-cache

# Never trust an exit code alone (see build-try.sh): require the exports.
if command -v node >/dev/null 2>&1; then
    node -e '
const fs = require("fs");
const mod = new WebAssembly.Module(fs.readFileSync(process.argv[1]));
const names = WebAssembly.Module.exports(mod).map((e) => e.name);
for (const want of ["oak_mount", "oak_dispatch_event", "oak_tick"]) {
  if (!names.includes(want)) { console.error("missing export " + want); process.exit(1); }
}' "$tmp/trellis_ui.wasm"
else
    echo "build-trellis-ui: warning: node is unavailable; exports not verified" >&2
fi

MONAD="$monad" "$root/scripts/gen-web-js.sh" "$tmp/web.js"

cp "$tmp/trellis_ui.wasm" "$tmp/web.js" "$out/"
cp "$root/wasm/web/web_runtime.js" "$root/wasm/web/float_format.js" "$out/"
cp "$root/motes/trellis_ui/web/index.html" "$out/index.html"

echo "build-trellis-ui: wrote $out"
