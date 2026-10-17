#!/usr/bin/env bash
# Self-compile the compiler for CI: the latest monadup NIGHTLY hosts the
# build when it can, and the checkout's Rust host (monad-rs) is the FALLBACK.
#
# CI runs only the Rust test suite; this script is the pipeline's other
# compiler leg -- it proves THIS tree's sources still self-compile. The
# nightly-first order is the point of the transition: the nightly is cut
# from main, so a PR that changes the parser, the prelude or the sources
# the compiler is built FROM can outgrow it, and the failure mode is not
# always a clean parse error -- the derive-handler branch (PR #77) had a
# nightly whose decls parser silently truncated `std/derive.mo` at the
# first annotated defmacro. The FALLBACK catches the loud failures; a
# silently wrong nightly-hosted build is a risk this scheme accepts, and
# the Rust regression tests (core/tests/constrained_dict_regression_test.rs
# and the suite they joined) are the coverage that no longer depends on
# the self-hosted sweeps this replaces.
#
# The nightly is installed with `monadup default` (install latest, set it
# active), so the host is `$MONAD_HOME/bin/monad` -- the active shim, no
# output parsing. On a runner with no monadup, or a failed install, the
# script says so and takes the fallback directly.
#
# Both hosts build the SAME thing: `scripts/build-self-hosted.sh` compiles
# `cli/src/main.mo` from THIS checkout (MONAD_STDLIB pinned to the
# checkout's init/src by that script), one rung for a `monad` host
# (native speed, ~1 min), an interpreted two-rung build for a monad-rs
# host (~22 min). The fallback host comes from MONAD_HOST_BIN -- ci.yml
# sets it to the flake's packaged monad-rs; unset, `cargo run --release --`
# is the default build-self-hosted.sh already carries.
#
# Runnable by hand, which is how it was checked rather than assumed:
#
#   MONAD_HOST_BIN=target-rust/release/monad-rs scripts/ci-self-compile.sh
#
# with the same warning every other build carries: do not edit the tree
# while it runs.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

fallback_host="${MONAD_HOST_BIN:-"cargo run --release --"}"
out="${1:-$root/target-monad/ci-self-compile}"

nightly=""
monad_home="${MONAD_HOME:-"$HOME/.monad"}"
if ! command -v monadup >/dev/null 2>&1; then
  echo "ci-self-compile: no monadup on PATH -- taking the Rust host fallback" >&2
elif ! monadup default; then
  echo "ci-self-compile: monadup could not install the latest nightly -- taking the Rust host fallback" >&2
elif [ ! -x "$monad_home/bin/monad" ]; then
  echo "ci-self-compile: monadup reported success but $monad_home/bin/monad is not executable -- taking the Rust host fallback" >&2
else
  nightly="$monad_home/bin/monad"
fi

if [ -n "$nightly" ]; then
  # `|| 1` rather than `set -e`'s exit: a failed nightly-hosted build is
  # this script's EXPECTED middle case, not the end of the run. The build
  # either leaves no binary (the fallback rebuilds fresh) or fails before
  # writing one (build-self-hosted.sh's staleness scan only short-circuits
  # on an existing, newer binary, which a failed attempt never produces).
  nightly_rc=0
  MONAD_HOST_BIN="$nightly" scripts/build-self-hosted.sh "$out" || nightly_rc=$?
  if [ "$nightly_rc" -eq 0 ]; then
    echo "ci-self-compile: self-compile OK with the latest nightly host ($nightly)"
    exit 0
  fi
  echo "ci-self-compile: the nightly-hosted build exited $nightly_rc -- falling back to the Rust host" >&2
fi

MONAD_HOST_BIN="$fallback_host" scripts/build-self-hosted.sh "$out"
echo "ci-self-compile: self-compile OK with the Rust host fallback ($fallback_host)"
