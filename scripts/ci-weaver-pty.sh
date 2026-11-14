#!/usr/bin/env bash
# Gate weaver's terminal tests in CI.
#
# The drivers live in motes/weaver/src/pty and run under `monad test` through
# the one file motes/weaver/test/pty_tests.mo (one compile for the whole
# suite), with the generic pty harness in motes/pty (compiled-only
# `#[extern "c"]` FFI). The sessions S6 scenario (an 18 MB store with an RSS
# bound) is in weaver::pty::sessions. See
# plans/implementations/2026-10-25-weaver-pty-monad-tests.md.
#
# ISOLATION. Every driver creates its own temp root and points the spawned
# weaver's HOME, session root and proc root at it, so nothing touches the
# developer's ~/.weaver. A failed driver keeps its root and prints its path.
#
# MONAD_BIN is the compiler to build the weaver under test with, the same name
# scripts/build-self-hosted.sh and scripts/check-monad-tests.sh take. CI passes
# the tree compiler (`MONAD_CI_BIN`, realized by .github/actions/tree-compiler);
# unset, the script uses the checkout's target-monad/release/monad, then
# target-monad/bootstrap-ci/monad.
#
# WATCHDOG. Each phase runs under `run_phase`, a wall-clock `timeout` that puts
# the child in its own process group -- a hung `monad test` and every weaver it
# spawned die together -- and names the phase it killed. CI's step timeout is
# the backstop; this is what makes a stall say "build" or "pty-tests" instead
# of "the job exceeded its budget". The defaults (build 35 min, suite 30 min)
# sit ABOVE contention, not above the median: the record's contended build is
# 29m38s (run 43438794724) against 7-10 min quiet, and a guard that fires on a
# busy runner would be the bug it exists to catch. Raise them per phase with
# WEAVER_PTY_BUILD_WATCHDOG_MIN / WEAVER_PTY_SUITE_WATCHDOG_MIN if a loaded
# runner legitimately needs more; never remove the guard.
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

# --- phase watchdog ---------------------------------------------------------

build_watchdog_min="${WEAVER_PTY_BUILD_WATCHDOG_MIN:-35}"
suite_watchdog_min="${WEAVER_PTY_SUITE_WATCHDOG_MIN:-30}"

phase="preflight"
on_exit() {
  rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "ci-weaver-pty: failed in phase '$phase' (exit $rc)" >&2
  fi
}
trap on_exit EXIT

# Run one named phase under a wall-clock guard. Exit 124 (TERM) or 137
# (KILL, after --kill-after) is the watchdog; anything else is the phase's
# own failure. `$monad` may be `cargo run --release --`, so the call sites
# keep their unquoted expansion and their SC2086 disables.
run_phase() {
  name="$1"
  seconds="$2"
  shift 2
  phase="$name"
  echo "ci-weaver-pty: phase '$name' (watchdog ${seconds}s)"
  rc=0
  timeout --signal=TERM --kill-after=30s "${seconds}s" "$@" || rc=$?
  if [ "$rc" -eq 0 ]; then return 0; fi
  if [ "$rc" -eq 124 ] || [ "$rc" -eq 137 ]; then
    die "phase '$name' stalled: watchdog fired after ${seconds}s"
  fi
  die "phase '$name' failed (exit $rc)"
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
  # An absolute -o wins outright, so MONAD_TARGET_DIR cannot move the output
  # the drivers and the rest of this script name.
  # shellcheck disable=SC2086  # MONAD_BIN may be `cargo run --release --`
  run_phase build "$((build_watchdog_min * 60))" \
    $monad build motes/weaver/src/main.mo --release -o "$bin"
else
  echo "ci-weaver-pty: WEAVER_PTY_SKIP_BUILD=1: reusing $bin"
fi
[ -x "$bin" ] || die "missing $bin after the build (run without WEAVER_PTY_SKIP_BUILD)"
echo "ci-weaver-pty: testing $bin"

# --- the Monad `pty` drivers ------------------------------------------------
#
# WEAVER_PTY gates the suite (unset skips it green in an ordinary sweep); CI
# sets it and requires the binary, so a missing or broken weaver is red.
echo "ci-weaver-pty: running the Monad pty drivers"
# shellcheck disable=SC2086  # MONAD_BIN may be `cargo run --release --`
run_phase pty-tests "$((suite_watchdog_min * 60))" \
  env PTY_ROOT="$root" WEAVER_PTY=1 WEAVER_PTY_REQUIRED=1 WV_BIN="$bin" \
  $monad test motes/weaver/test/pty_tests.mo
