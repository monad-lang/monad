#!/usr/bin/env bash
# Build the monad-lang.org site into docs/public with `acorn`, the Monad site
# generator (motes/acorn). Replaces the mdBook + Zola pipeline.
#
# Order matters: `acorn build` copies the static tree (docs/site/static) into
# the output, so the /try wasm and the /install script must be staged there
# FIRST. `scripts/build-try.sh` stages every /try file in one run, so the page
# never mixes a new host with stale wasm (worker protocol mismatch).
#
# MONAD selects the compiler that builds acorn; the first argument is passed
# to `scripts/build-try.sh`'s own compiler selection (see its header).
#
# Usage: scripts/build-docs.sh [--skip-try]
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

# Pick a compiler the way `scripts/build-try.sh` does (keep the list in step):
# an explicit MONAD alone, else a tree-built binary, else the nightly. A
# stale compiler fails the build loudly rather than publishing a site the
# tree's natives cannot build.
if [ -n "${MONAD:-}" ]; then
    monad="$MONAD"
else
    monad=""
    for candidate in "$root/target-monad/release/monad" \
                     "$root/target-monad/bootstrap-ci/monad" \
                     "$root/target-monad/ci-self-compile/monad" \
                     "$(command -v monad 2>/dev/null || true)"; do
        if [ -n "$candidate" ] && [ -x "$candidate" ]; then
            monad="$candidate"
            break
        fi
    done
    if [ -z "$monad" ]; then
        echo "build-docs: no compiler found; set MONAD or install one with 'monadup default'" >&2
        exit 1
    fi
fi

cd "$root"
export MONAD_STDLIB="$root/init/src"

"$root/scripts/sync-install.sh"
if [ "${1:-}" = "--skip-try" ]; then
    echo "build-docs: /try wasm not rebuilt (--skip-try)" >&2
else
    "$root/scripts/build-try.sh"
fi

# `-o` is the output BINARY (its `.ll` and `.o` land beside it).
mkdir -p "$root/target-docs"
"$monad" build "$root/motes/acorn" -o "$root/target-docs/acorn"
"$root/target-docs/acorn" build
