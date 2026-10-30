#!/usr/bin/env bash
# Fixture tests for scripts/ci-self-compile.sh's gate decisions. No network,
# no real compiler: a fake monadup, nightly and fallback host drive each
# branch, so the failure paths are tested rather than assumed.
#
#   scripts/check-nightly-gate.sh
#
# The cases cover: the bootstrap window (nightly before the floor), the
# strict success path, a nightly that cannot build, a nightly-built compiler
# that cannot check itself, the explicit local opt-out, and the no-monadup
# failure.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
gate="$root/scripts/ci-self-compile.sh"
head_commit="$(git -C "$root" rev-parse HEAD)"
# A real floor for cases 1-5. The repo's own file may say `pending` (the
# workspace-inheritance window), which is tested separately below.
real_floor="$(git -C "$root" rev-parse 0af9ff59 2>/dev/null || git -C "$root" rev-parse "$head_commit^")"

work="$(mktemp -d "${TMPDIR:-/tmp}/monad-nightly-gate.XXXXXX")"
trap 'rm -rf "$work"' EXIT
passed=0
failed=0

fail() { echo "FAIL: $*" >&2; failed=$((failed + 1)); }
pass() { passed=$((passed + 1)); }

# ─── fixtures ───────────────────────────────────────────────────────────────

mkdir -p "$work/bin" "$work/home/bin" "$work/out"
printf '%s\n' "$real_floor" > "$work/floor-real"

# The fallback host, and the nightly's build path (the fake nightly execs it).
# It accepts both shapes build-self-hosted.sh uses:
#   build cli/src/main.mo -o OUT                          (a `monad` host)
#   run cli/src/main.mo build cli/src/main.mo -o OUT      (everything else)
# FAKE_FAIL_ONE_RUNG=1 makes only the one-rung (nightly) build fail, so the
# opt-out case can have a working fallback.
cat > "$work/host" <<'HOST'
#!/usr/bin/env bash
set -eu
if [ "$1" = build ] && [ "${FAKE_FAIL_ONE_RUNG:-0}" = 1 ]; then
  echo "host: simulated nightly build failure" >&2
  exit 1
fi
out="" prev=""
for a in "$@"; do
  if [ "$prev" = "-o" ]; then out="$a"; fi
  prev="$a"
done
[ -n "$out" ] || { echo "host: no -o argument" >&2; exit 1; }
mkdir -p "$(dirname "$out")"
cat > "$out" <<'MONAD'
#!/usr/bin/env bash
case "${1:-}" in
  version) printf '%s\n' "${FAKE_BUILT_COMMIT:-fake-built}" ;;
  check) exit "${FAKE_CHECK_RC:-0}" ;;
  *) exit 0 ;;
esac
MONAD
chmod +x "$out"
HOST
chmod +x "$work/host"

# monadup default succeeds; the nightly is pre-installed by make_nightly.
cat > "$work/bin/monadup" <<'UP'
#!/usr/bin/env bash
exit 0
UP
chmod +x "$work/bin/monadup"

make_nightly() {
  cat > "$work/home/bin/monad" <<NIGHTLY
#!/usr/bin/env bash
set -eu
if [ "\${1:-}" = version ]; then printf '%s\n' "\${FAKE_NIGHTLY_COMMIT:-unknown}"; exit 0; fi
exec "\$FAKE_HOST_SCRIPT" "\$@"
NIGHTLY
  chmod +x "$work/home/bin/monad"
}

# run_gate EXPECT_RC LABEL [env assignments...]
run_gate() {
  local expect="$1" label="$2"
  shift 2
  local log="$work/log-$RANDOM"
  local rc=0
  env PATH="$work/bin:$PATH" MONAD_HOME="$work/home" \
    MONAD_HOST_BIN="$work/host" FAKE_HOST_SCRIPT="$work/host" \
    FAKE_NIGHTLY_COMMIT="${NIGHTLY:-$head_commit}" \
    FAKE_BUILT_COMMIT="fake-built" FAKE_CHECK_RC=0 FAKE_FAIL_ONE_RUNG=0 \
    MONAD_NIGHTLY_FLOOR="${MONAD_NIGHTLY_FLOOR:-$work/floor-real}" \
    "$@" "$gate" "$work/out" >"$log" 2>&1 || rc=$?
  if [ "$expect" = 0 ] && [ "$rc" -ne 0 ]; then
    cat "$log" >&2
    fail "$label: expected success, got $rc"
  elif [ "$expect" != 0 ] && [ "$rc" -eq 0 ]; then
    cat "$log" >&2
    fail "$label: expected failure, got 0"
  else
    pass
  fi
  LAST_LOG="$log"
}

expect_log() {
  local needle="$1" label="$2"
  if ! grep -qF "$needle" "$LAST_LOG"; then
    cat "$LAST_LOG" >&2
    fail "$label: log does not contain: $needle"
  fi
}

# ─── cases ─────────────────────────────────────────────────────────────────

make_nightly

# 0. A `pending` floor: the tree needs a loader the published nightlies
#    predate, expressed as a sentinel rather than a commit that a rebase-merge
#    would orphan.
printf 'pending\n' > "$work/floor-pending"
NIGHTLY="$head_commit" MONAD_NIGHTLY_FLOOR="$work/floor-pending" run_gate 0 "pending floor"
expect_log "floor is pending" "pending floor"

# 1. The nightly predates the floor: a loud bootstrap window, then the Rust
#    host. The fake nightly's commit must be an ancestor of the floor.
old_nightly="$(git -C "$root" rev-list --max-count=1 "$real_floor^" 2>/dev/null || true)"
if [ -n "$old_nightly" ]; then
  NIGHTLY="$old_nightly" run_gate 0 "bootstrap window"
  expect_log "bootstrap window" "bootstrap window"
else
  pass
fi

# 2. The nightly is at/after the floor and builds a working compiler.
NIGHTLY="$head_commit" run_gate 0 "strict success"
expect_log "self-compile OK with the latest nightly host" "strict success"

# 3. The nightly is at/after the floor but cannot compile the tree; strict
#    default must fail (not fall back).
NIGHTLY="$head_commit" run_gate 1 "strict build failure" FAKE_FAIL_ONE_RUNG=1
expect_log "last nightly must be able to build this tree" "strict build failure"

# 4. The same failure with the explicit local opt-out falls back.
NIGHTLY="$head_commit" run_gate 0 "opt-out fallback" \
  FAKE_FAIL_ONE_RUNG=1 MONAD_ALLOW_RUST_FALLBACK=1
expect_log "Rust host fallback" "opt-out fallback"

# 5. The nightly builds, but the binary it produced cannot check its own
#    source (the miscompile class the old fallback accepted).
NIGHTLY="$head_commit" run_gate 1 "built compiler check failure" FAKE_CHECK_RC=1
expect_log "cannot check cli/src/main.mo" "built compiler check failure"

# 6. No usable installer is a failure by default. `MONADUP_BIN` is the
#    explicit override; an unusable one must fail rather than silently reach
#    for the repo stub (which would hit the network).
bash_bin="$(command -v bash)"
mkdir -p "$work/nopath"
rc=0
env PATH="$work/nopath" MONAD_HOME="$work/home" \
  MONADUP_BIN="$work/nopath/monadup" \
  "$bash_bin" "$gate" "$work/out" >"$work/log-nomonadup" 2>&1 || rc=$?
[ "$rc" -ne 0 ] || fail "no monadup: expected failure, got 0"
grep -qF "MONADUP_BIN" "$work/log-nomonadup" \
  || { cat "$work/log-nomonadup" >&2; fail "no monadup: missing diagnosis"; }
pass

echo "check-nightly-gate: $passed passed, $failed failed"
[ "$failed" -eq 0 ]
