#!/usr/bin/env bash
# Gate weaver's Python pty repros in CI.
#
# The 13 drivers in scripts/weaver-tui-repro/ are the only automated coverage
# of weaver's raw-mode/TUI loop (plans/implementations/weaver.md records the
# gap; plans/implementations/2026-10-25-weaver-pty-ci-stopgap.md is this
# script's plan). They run against the compiled `target-monad/release/weaver`.
#
# THE EXIT CODE IS NOT THE VERDICT. Three drivers print a failure and still
# exit 0: pty_repro.py (`PASSn ...: False`), pty_repro_round2.py (`FAIL`), and
# pty_repro_async.py (`FAIL` plus a summary). So every run is classified from
# its OUTPUT as well: a FAIL line, a `: False`, a traceback, no PASS line, or
# a missing per-driver success marker is a failure even when `$?` is zero.
# The per-driver markers are in `marker_for` below; keep that table in one
# place so an output-wording change is one auditable diff.
#
# ISOLATION. Every driver gets its own HOME, session root, proc root, and
# WV_REPRO_TMP under one mktemp root, plus a staged single-read turn fixture
# for the base driver (whose /tmp/wv_repro path was removed from the script).
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
  "$run/repro" "$run/session-tmp" "$run/fixtures"

# The base driver used to read /tmp/wv_repro/turns.json, a hand-staged file
# that nothing created. Its first turn is the single-read pick the script
# expects, so derive that fixture from the checked-in two-read one.
python3 - "$root/scripts/weaver-tui-repro/turns_two_reads.json" \
  "$run/fixtures/turns_single_read.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as fh:
    turns = json.load(fh)
if not turns:
    raise SystemExit("turns_two_reads.json is empty")
with open(sys.argv[2], "w", encoding="utf-8") as fh:
    json.dump(turns[:1], fh)
PY

export HOME="$run/home"
export WEAVER_SESSION_ROOT="$run/sessions"
export WEAVER_PROC_ROOT="$run/procs"
export WV_SESSION_TMP="$run/session-tmp"
export WV_BIN="$bin"
export WV_TURNS="$run/fixtures/turns_single_read.json"
export WV_TURNS_LONG="$root/scripts/weaver-tui-repro/turns_long.json"
export PYTHONUNBUFFERED=1
unset NO_COLOR

# --- the driver table -------------------------------------------------------

drivers=(
  pty_repro_ctrl_d.py
  pty_repro_models.py
  pty_repro_input.py
  pty_repro_dialogs.py
  pty_repro_resize.py
  pty_repro_selection.py
  pty_repro_crash.py
  pty_repro_processes.py
  pty_repro_round2.py
  pty_repro_async.py
  pty_repro_bigplan.py
  pty_repro_sessions.py
  pty_repro_resume.py
  pty_repro.py
)

# The final success line a driver prints on a fully green run. An empty marker
# means the driver has none: the exit code, the no-FAIL scan, and the PASS-line
# requirement are its verdict.
marker_for() {
  case "$1" in
    pty_repro_async.py) echo "ASYNC PTY REPRO: ALL PASS" ;;
    pty_repro_sessions.py) echo "SESSION REPRO: ALL PASS" ;;
    pty_repro_input.py) echo "input repro: ok" ;;
    pty_repro_crash.py) echo "crash repro: ok" ;;
    pty_repro_dialogs.py) echo "dialog repro: ok" ;;
    pty_repro_resize.py) echo "resize repro: ok" ;;
    pty_repro_bigplan.py) echo "big-plan repro: ok" ;;
    pty_repro_processes.py) echo "processes repro: ok" ;;
    pty_repro_selection.py) echo "selection repro: ok" ;;
    pty_repro_resume.py) echo "RESUME PICKER REPRO: ALL PASS" ;;
    *) echo "" ;;
  esac
}

# Sessions pages a 1200-line store and measures RSS over an 18 MB session;
# bigplan generates a 100 KB / 2000-line plan. Everything else is seconds.
timeout_for() {
  case "$1" in
    pty_repro_sessions.py | pty_repro_bigplan.py) echo 420 ;;
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
  if [ "$driver" = "pty_repro.py" ] && grep -q ': False$' "$log"; then
    reason="${reason:+$reason; }: False"
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
