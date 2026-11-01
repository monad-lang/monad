#!/usr/bin/env bash
# Gate weaver's terminal tests in CI.
#
# Two suites run against the compiled `target-monad/release/weaver`: the
# `mty` drivers in motes/weaver/test (compiled-only, under `monad test`) and
# one Python oracle, scripts/weaver-tui-repro/pty_repro_sessions.py. Its S6
# scenario (an 18 MB session with an RSS bound) is not ported yet: resuming
# that session SIGSEGVs the compiled test driver in a runtime fiber thread
# (GC_inner_start_routine -> monad_get_tag), independent of where the session
# is synthesized. Everything else is in the Monad suite
# (plans/implementations/2026-10-25-weaver-pty-monad-tests.md).
#
# THE EXIT CODE IS NOT THE VERDICT. The Python driver is classified from its
# OUTPUT too: a FAIL line, a traceback, no PASS line, or the missing
# `SESSION REPRO: ALL PASS` marker is a failure even when `$?` is zero.
# The marker is in `marker_for` below.
#
# ISOLATION. The Python driver gets its own HOME, session root, proc root and
# WV_SESSION_TMP under one mktemp root; the Monad tests create their own roots.
# Nothing touches the developer's ~/.weaver. The run root is removed on success
# unless WEAVER_PTY_KEEP=1, and kept on failure so the logs survive.
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

# --- isolation --------------------------------------------------------------

run="$(mktemp -d "${TMPDIR:-/tmp}/weaver_pty_ci.XXXXXX")"
keep="${WEAVER_PTY_KEEP:-0}"
cleanup() {
  if [ "$keep" != 1 ]; then
    rm -rf "$run"
  fi
}
trap cleanup EXIT

mkdir -p "$run/home" "$run/sessions" "$run/procs" "$run/logs" \
  "$run/repro" "$run/session-tmp"

export HOME="$run/home"
export WEAVER_SESSION_ROOT="$run/sessions"
export WEAVER_PROC_ROOT="$run/procs"
export WV_SESSION_TMP="$run/session-tmp"
export WV_BIN="$bin"
export PYTHONUNBUFFERED=1
unset NO_COLOR

# --- the Monad `mty` drivers ------------------------------------------------
#
# The mty drivers (everything except the sessions S6 scenario) live in
# motes/weaver/test and run under `monad test`, with the generic pty harness in
# motes/mty. WEAVER_MTY gates the suite (unset skips it green in an ordinary
# sweep); CI sets it and requires the binary.
echo "ci-weaver-pty: running the Monad mty drivers"
# shellcheck disable=SC2086  # MONAD_BIN may be `cargo run --release --`
MTY_ROOT="$root" WEAVER_MTY=1 WEAVER_MTY_REQUIRED=1 WV_BIN="$bin" \
  $monad test motes/weaver/test --jobs 1 \
  || die "the Monad mty drivers failed"

# --- the driver table -------------------------------------------------------

drivers=(
  pty_repro_sessions.py
)

# The final success line a driver prints on a fully green run. An empty marker
# means the driver has none: the exit code, the no-FAIL scan, and the PASS-line
# requirement are its verdict.
marker_for() {
  case "$1" in
    pty_repro_sessions.py) echo "SESSION REPRO: ALL PASS" ;;
    *) echo "" ;;
  esac
}

# Sessions pages a 1200-line store and measures RSS over an 18 MB session.
timeout_for() {
  case "$1" in
    pty_repro_sessions.py) echo 420 ;;
    *) echo 180 ;;
  esac
}

# --- run --------------------------------------------------------------------

passed=0
failed=0
failed_names=()

for driver in "${drivers[@]}"; do
  stem="${driver%.py}"
  log="$run/logs/$stem.log"
  mkdir -p "$run/repro/$stem"
  limit="$(timeout_for "$driver")"

  rc=0
  WV_REPRO_TMP="$run/repro/$stem" \
    timeout --signal=TERM --kill-after=5 "$limit" \
    python3 -u "scripts/weaver-tui-repro/$driver" </dev/null >"$log" 2>&1 || rc=$?

  reason=""
  if [ "$rc" -ne 0 ]; then
    reason="exit $rc"
  fi
  if grep -qE '^[[:space:]]*FAIL([[:space:]]|$)' "$log"; then
    reason="${reason:+$reason; }FAIL line"
  fi
  if grep -q '^Traceback (most recent call last):' "$log"; then
    reason="${reason:+$reason; }traceback"
  fi
  if ! grep -q '^PASS' "$log"; then
    reason="${reason:+$reason; }no PASS line"
  fi
  marker="$(marker_for "$driver")"
  if [ -n "$marker" ] && ! grep -Fq "$marker" "$log"; then
    reason="${reason:+$reason; }missing \"$marker\""
  fi

  if [ -z "$reason" ]; then
    echo "ci-weaver-pty: PASS $driver"
    passed=$((passed + 1))
  else
    echo "ci-weaver-pty: FAIL $driver ($reason)" >&2
    echo "ci-weaver-pty: --- tail of $log ---" >&2
    tail -n 60 "$log" >&2 || true
    echo "ci-weaver-pty: --- end $log ---" >&2
    failed=$((failed + 1))
    failed_names+=("$driver")
  fi
done

total=${#drivers[@]}
echo "ci-weaver-pty: $passed/$total drivers passed"
if [ "$failed" -ne 0 ]; then
  keep=1
  echo "ci-weaver-pty: failed: ${failed_names[*]}" >&2
  echo "ci-weaver-pty: logs kept in $run" >&2
  exit 1
fi
