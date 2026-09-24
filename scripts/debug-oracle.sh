#!/usr/bin/env bash
# The `Term.ctx` transparency oracle (tools/debug_transparency_oracle.sh).
#
# Source positions ride the AST as `Term.ctx` wrappers on every path, and
# ~180 sites match on term SHAPE. A wrapper interposed where one of those
# looks does not crash -- it silently stops matching, and a call quietly
# fails to resolve. This asserts the property that makes wrappers safe:
# `--debug` may add `!dbg` annotations and nothing else, so stripping them
# must reproduce the `--release` build byte for byte.
#
# It existed, unwired, while the bug it describes was live. Cheap: two
# compiles per example file, against the SELF-HOSTED BINARY rather than
# the Rust host interpreting cli/src/main.mo -- the binary is what ships,
# and it is ~40x faster per file besides.
#
# This is called by .github/workflows/ci.yml and .tangled/workflows/bootstrap.yml
# directly, inside one `nix develop -c`, rather than through
# `devenv tasks run monad:debug-oracle` (which is the local equivalent):
# devenv-tasks captures a task's stdout and shows it only when the task FAILS,
# which would swallow the oracle's per-file verdicts -- the evidence that says
# which file broke transparency. The task in devenv.nix runs this same script
# in this same dev shell, just quieter on success.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

out="${TMPDIR:-/tmp}/monad-bootstrap-ci"
# Reuse the binary `bootstrap-compile.sh` just built -- in CI that is the step
# immediately before this one, in the same job. Rebuild when it is missing or
# older than any source compiled INTO it: a stale binary reports failures that
# are really its own age (one here predated two examples' syntax and could not
# parse them at all), which would be indistinguishable from the transparency
# break this looks for. All four motes, not just lang/ -- cli/ holds the compile
# target itself, and llvm/ and runtime/ hold the backend.
if [ ! -x "$out/monad" ] || [ -n "$(find "$root"/lang "$root"/cli "$root"/llvm "$root"/runtime -name '*.mo' -newer "$out/monad" -print -quit)" ]; then
  mkdir -p "$out"
  cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$out/monad" --release
fi
MONAD_BIN="$out/monad" "$root"/tools/debug_transparency_oracle.sh "$root"/examples/*.mo
