#!/usr/bin/env bash
# Gate weaver's terminal tests in CI.
#
# The drivers live in motes/weaver/test and run under `monad test`, with the
# generic pty harness in motes/mty (compiled-only `#[extern "c"]` FFI). There
# is no Python driver left: the sessions S6 scenario (an 18 MB store with an
# RSS bound) is in sessions_tests.mo. See
# plans/implementations/2026-10-25-weaver-pty-monad-tests.md.
#
# ISOLATION. Every driver creates its own temp root and points the spawned
# weaver's HOME, session root and proc root at it, so nothing touches the
# developer's ~/.weaver. A failed driver keeps its root and prints its path.
#
# MONAD_BIN is the compiler to build the weaver under test with, the same name
# scripts/build-self-hosted.sh and scripts/check-monad-tests.sh take. CI passes
# the self-compiled binary from this commit; unset, the script uses the
# checkout's target-monad/release/monad, then target-monad/bootstrap-ci/monad.
#
# WEAVER_PTY_SKIP_BUILD=1 reuses an existing release weaver (local iteration).
#
# Runnable by hand:
#
#   MONAD_BIN=target-monad/release/monad scripts/ci-weaver-pty.sh
#
# with the same warning every build carries: do not edit the tree while it runs.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

die() {
  echo "ci-weaver-pty: $*" >&2
  exit 1
}

# --- the compiler and the binary under test ---------------------------------

monad="${MONAD_BIN:-}"
if [ -z "$monad" ]; then
  if [ -x "$root/target-monad/release/monad" ]; then
    monad="$root/target-monad/release/monad"
  elif [ -x "$root/target-monad/bootstrap-ci/monad" ]; then
    monad="$root/target-monad/bootstrap-ci/monad"
  elif command -v monad >/dev/null 2>&1; then
    monad="monad"
  else
    die "no compiler found -- set MONAD_BIN (or build target-monad/release/monad)"
  fi
fi
export MONAD_BIN="$monad"

bin="$root/target-monad/release/weaver"

if [ "${WEAVER_PTY_SKIP_BUILD:-0}" != 1 ]; then
  echo "ci-weaver-pty: building the release weaver with $monad"
  # An absolute -o wins outright, so MONAD_TARGET_DIR cannot move the output
  # the drivers and the rest of this script name.
  # shellcheck disable=SC2086  # MONAD_BIN may be `cargo run --release --`
  $monad build motes/weaver/src/main.mo --release -o "$bin" \
    || die "the release build failed"
fi
[ -x "$bin" ] || die "missing $bin after the build (run without WEAVER_PTY_SKIP_BUILD)"
echo "ci-weaver-pty: testing $bin"

# --- the Monad `mty` drivers ------------------------------------------------
#
# WEAVER_MTY gates the suite (unset skips it green in an ordinary sweep); CI
# sets it and requires the binary, so a missing or broken weaver is red.
echo "ci-weaver-pty: running the Monad mty drivers"
# shellcheck disable=SC2086  # MONAD_BIN may be `cargo run --release --`
MTY_ROOT="$root" WEAVER_MTY=1 WEAVER_MTY_REQUIRED=1 WV_BIN="$bin" \
  $monad test motes/weaver/test --jobs 1 \
  || die "the Monad mty drivers failed"
