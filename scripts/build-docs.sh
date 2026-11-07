#!/usr/bin/env bash
# Build the monad-lang.org site into docs/public.
#
# Two binaries: `motes/acorn` is the generic generator (book pages, link
# gate), and `docs/site/monad_website` is this site (its chrome and landing
# page), which builds on acorn as a library and does the actual build.
#
# Order matters: `acorn build` copies the static tree (docs/site/static) into
# the output, so the /try wasm and the /install script must be staged there
# FIRST. `scripts/build-try.sh` stages every /try file in one run, so the page
# never mixes a new host with stale wasm (worker protocol mismatch).
#
# MONAD selects the compiler that builds acorn; the first argument is passed
# to `scripts/build-try.sh`'s own compiler selection (see its header).
#
# Usage: scripts/build-docs.sh [--skip-try] [--with-moon]
#
#   --skip-try   do not rebuild the /try wasm
#   --with-moon  also build the `moon` binary into target-docs/ (docs-serve
#                serves with `moon static`, CI compiles it here)
set -euo pipefail

skip_try=0
with_moon=0
for arg in "$@"; do
    case "$arg" in
        --skip-try) skip_try=1 ;;
        --with-moon) with_moon=1 ;;
        *)
            echo "build-docs: unknown argument '$arg' (--skip-try, --with-moon)" >&2
            exit 2
            ;;
    esac
done

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
if [ "$skip_try" -eq 1 ]; then
    echo "build-docs: /try wasm not rebuilt (--skip-try)" >&2
else
    "$root/scripts/build-try.sh"
fi

# `-o` is the output BINARY (its `.ll` and `.o` land beside it).
# acorn is built too: `monad test motes/acorn` never compiles its `main.mo`,
# so this is the only build of the generic CLI.
mkdir -p "$root/target-docs"
"$monad" build "$root/motes/acorn" -o "$root/target-docs/acorn"
"$monad" build "$root/docs/site/monad_website" -o "$root/target-docs/monad_website"
if [ "$with_moon" -eq 1 ]; then
    "$monad" build "$root/motes/moon" -o "$root/target-docs/moon"
fi
"$root/target-docs/monad_website" build
