#!/usr/bin/env bash
# Build the oak_ui component explorer and its static gallery.
#
# Run inside `nix develop` (web builds need WASI_SDK_PATH, llc, clang):
#   nix develop --no-pure-eval --accept-flake-config -c scripts/build-oak-ui-book.sh [out]
#
# Writes a servable directory (default target-monad/oak-ui-book):
#   index.html, oak_ui_book.wasm, web.js, web_runtime.js, float_format.js
#                       the live explorer (motes/oak_ui_book, --bin book)
#   oak-ui.css          the shared stylesheet (written by book_static)
#   gallery/            every story rendered statically, no runtime needed
#
# Serve it with any static server, e.g. `python3 -m http.server -d <out>`.
# MONAD selects the compiler (default: `monad` on PATH).
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
out="${1:-$root/target-monad/oak-ui-book}"
monad="${MONAD:-monad}"

mkdir -p "$out"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/monad-oak-ui-book.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT

# The live explorer. `-o` leaves .ll/.o intermediates beside its output,
# so build into the temp dir and copy only the module.
"$monad" build --target wasm32-unknown-unknown "$root/motes/oak_ui_book" --bin book \
    -o "$tmp/oak_ui_book.wasm" --no-cache

# Never trust an exit code alone (see build-try.sh): require the exports.
if command -v node >/dev/null 2>&1; then
    node -e '
const fs = require("fs");
const mod = new WebAssembly.Module(fs.readFileSync(process.argv[1]));
const names = WebAssembly.Module.exports(mod).map((e) => e.name);
for (const want of ["oak_mount", "oak_dispatch_event", "oak_tick"]) {
  if (!names.includes(want)) { console.error("missing export " + want); process.exit(1); }
}' "$tmp/oak_ui_book.wasm"
else
    echo "build-oak-ui-book: warning: node is unavailable; exports not verified" >&2
fi

MONAD="$monad" "$root/scripts/gen-web-js.sh" "$tmp/web.js"

# The static gallery and the stylesheet both pages load. book_static writes
# oak-ui.css next to the gallery; the explorer loads it from the root.
OAK_UI_BOOK_OUT="$tmp/gallery" "$monad" run "$root/motes/oak_ui_book/src/static.mo"

rm -rf "$out/gallery"
cp -R "$tmp/gallery" "$out/gallery"
cp "$tmp/gallery/oak-ui.css" "$out/oak-ui.css"
cp "$tmp/oak_ui_book.wasm" "$tmp/web.js" "$out/"
cp "$root/wasm/web/web_runtime.js" "$root/wasm/web/float_format.js" "$out/"
cp "$root/motes/oak_ui_book/web/index.html" "$out/index.html"

echo "build-oak-ui-book: wrote $out (explorer: index.html, gallery: gallery/index.html)"
