#!/usr/bin/env bash
# Build the /try wasm artifacts and stage them beside the committed page.
#
# Run inside `nix develop` (web builds need WASI_SDK_PATH, llc, clang):
#   nix develop --no-pure-eval --accept-flake-config -c scripts/build-try.sh
#
# The output directory is BUILD OUTPUT: `index.html`, `style.css`,
# `worker.js` and `sources.js` are tracked, but `web.js`, `web_runtime.js`,
# `float_format.js`, both `.wasm` files, `sources.json` and the `sources/`
# tree are gitignored. `web.js` is generated here (`scripts/gen-web-js.sh`)
# rather than copied from a tracked file. This script stages ALL of them on
# every run -- one invocation always leaves a self-consistent, servable
# directory. Restart `zola serve` after a rebuild (it snapshots static/ at
# startup).
#
# The engine embeds no prelude: the page fetches the real `init/src/*.mo`
# files from `sources/` (indexed by `sources.json`) and hands their text to
# the wasm. That is why the source tree is staged here, in the same run as
# the engine that parses it.
#
# MONAD selects the compiler binary (the deploy workflow passes the nix
# build's `.#monad`); the first argument overrides the output directory.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
out="${1:-$root/docs/site/static/try}"

# Pick a compiler that can actually build THIS tree. The active nightly
# can lag the natives a branch adds, and a local bootstrap binary can be
# older still; both fail with a clean "unwired native" error. An explicit
# MONAD is honoured alone (the deploy passes the nix build); otherwise try
# the tree-built binaries first, then `monad`. `target-monad/release` is
# what `scripts/build-self-hosted.sh <dir>` writes, so a developer who
# built this tree gets it picked up by `docs-serve` too.
if [ -n "${MONAD:-}" ]; then
    candidates=("$MONAD")
else
    candidates=()
    for candidate in "$root/target-monad/release/monad" \
                     "$root/target-monad/bootstrap-ci/monad" \
                     "$root/target-monad/ci-self-compile/monad" \
                     "$(command -v monad 2>/dev/null || true)"; do
        if [ -n "$candidate" ] && [ -x "$candidate" ]; then
            candidates+=("$candidate")
        fi
    done
    if [ "${#candidates[@]}" -eq 0 ]; then
        echo "build-try: no compiler found; set MONAD or install one with 'monadup default'" >&2
        exit 1
    fi
fi

mkdir -p "$out"

# Build into a temp dir: `-o` also leaves the `.ll` and `.o` intermediates
# beside its output, and those must not land in the deployed static tree.
tmp="$(mktemp -d "${TMPDIR:-/tmp}/monad-build-try.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT

# The page shell comes along so a non-default output directory (the check
# script uses one) is servable too.
cp "$root/docs/site/static/try/index.html" \
   "$root/docs/site/static/try/style.css" \
   "$root/docs/site/static/try/worker.js" \
   "$root/docs/site/static/try/sources.js" "$tmp/"

# Stage the prelude the way the site serves it: every non-test module of
# `init/src`, mirrored under `sources/` at its repo-relative path (the
# engine derives module identity from that path), plus the index the worker
# reads. Test modules are excluded -- nothing the prelude reaches imports
# them, and they are not part of the language surface.
stage_sources() {
    local dest="$1" file name first=1
    mkdir -p "$dest/sources/init/src"
    printf '{"version":1,"modules":[' > "$dest/sources.json"
    for file in "$root"/init/src/*.mo; do
        name="$(basename "$file")"
        case "$name" in
            *_tests*.mo|test*.mo) continue ;;
        esac
        cp "$file" "$dest/sources/init/src/$name"
        if [ "$first" -eq 1 ]; then first=0; else printf ',' >> "$dest/sources.json"; fi
        printf '"%s"' "init/src/$name" >> "$dest/sources.json"
    done
    printf ']}\n' >> "$dest/sources.json"
    if [ "$first" -eq 1 ]; then
        echo "build-try: no init/src sources to serve" >&2
        return 1
    fi
}

stage_sources "$tmp"

# A stale compiler can accept the build and exit 0 with an EMPTY module:
# `target-monad/ci-self-compile/monad` (2026-10-23) did exactly that, and the
# resulting 4 KB stub (no `try_run`, no imports) is what made /try fail to
# load. Never trust an exit code alone -- require the export each module's
# worker/page calls.
verify_wasm() {
    local file="$1" export_name="$2"
    if ! command -v node >/dev/null 2>&1; then
        echo "build-try: warning: node is unavailable; cannot verify $file" >&2
        return 0
    fi
    node -e '
const fs = require("fs");
const mod = new WebAssembly.Module(fs.readFileSync(process.argv[1]));
const names = WebAssembly.Module.exports(mod).map((e) => e.name);
if (!names.includes(process.argv[2])) {
  console.error("missing export " + process.argv[2] + "; exports: " + names.join(","));
  process.exit(1);
}' "$file" "$export_name"
}

# The engine is DOM-free and runs in the worker; the UI is the Oak app.
built=""
last_log=""
i=0
for monad in "${candidates[@]}"; do
    i=$((i + 1))
    log="$tmp/build-$i.log"
    echo "build-try: trying compiler $monad"
    if "$monad" build --target wasm32-unknown-unknown \
            "$root/motes/try_engine" -o "$tmp/try_engine.wasm" --no-cache >"$log" 2>&1 \
        && "$monad" build --target wasm32-unknown-unknown \
            "$root/motes/try_ui" -o "$tmp/try_ui.wasm" --no-cache >>"$log" 2>&1 \
        && verify_wasm "$tmp/try_engine.wasm" try_run >>"$log" 2>&1 \
        && verify_wasm "$tmp/try_ui.wasm" oak_mount >>"$log" 2>&1; then
        built="$monad"
        break
    fi
    last_log="$log"
    echo "build-try: $monad cannot build this tree; trying the next compiler" >&2
done

if [ -z "$built" ]; then
    echo "build-try: no compiler could build the /try modules. Build one with" >&2
    echo "  devenv tasks run monad:bootstrap-compile   (or: monadup default)" >&2
    [ -n "$last_log" ] && cat "$last_log" >&2
    exit 1
fi
echo "build-try: compiler $built"

# The host is generated from WebAbi and shared by both modules. `web.js` is
# a build artifact (see scripts/gen-web-js.sh), generated here with the
# compiler that just built the modules, so the deploy never depends on a
# stale checkout copy.
MONAD="$built" "$root/scripts/gen-web-js.sh" "$tmp/web.js"
cp "$root/wasm/web/web_runtime.js" "$root/wasm/web/float_format.js" "$tmp/"

cp "$tmp/try_engine.wasm" "$tmp/try_ui.wasm" \
   "$tmp/web.js" "$tmp/web_runtime.js" "$tmp/float_format.js" \
   "$tmp/index.html" "$tmp/style.css" "$tmp/worker.js" "$tmp/sources.js" \
   "$tmp/sources.json" "$out/"

# Replace the served sources wholesale: a module dropped from init/src must
# not linger in an old build directory.
rm -rf "$out/sources"
cp -R "$tmp/sources" "$out/sources"

echo "build-try: wrote $out/try_engine.wasm and $out/try_ui.wasm"
echo "build-try: wrote $out/sources.json and $out/sources/ (the prelude the page serves)"
