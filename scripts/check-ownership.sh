#!/bin/sh
# Ownership drop-glue check (ownership-regions-memory O4).
#
# Builds the fixture with a compiler from THIS checkout under each ownership
# mode and asserts:
#   1. `MONAD_OWNERSHIP=1` balances owned-constructors and owned-frees, and
#      actually allocates (a non-zero count);
#   2. `MONAD_OWNERSHIP=poison` balances too (every drop point executes even
#      though nothing is returned to the allocator);
#   3. the default build reports no owned allocations or frees at all;
#   4. the warn-mode gate refuses a build whose loaded closure includes a
#      `[affine] mode = "warn"` mote (`examples/` inherits the root
#      manifest, which is warn).
#
# Run from the repository root. Override the host with MONAD_BIN, same
# convention as scripts/golden-ir.sh.
set -u
bin=${MONAD_BIN:-monad}
out=$(mktemp -d)
status=0

# The stats printer runs at each process's exit, so the log carries one block
# per process (the fixture's test binary, then the compiler itself). Taking
# the maximum per kind picks the fixture's block: the compiler was built
# default-mode and always reports zero owned activity.
counts() {
    kind=$1
    log=$2
    sed -n "s/.*${kind}[[:space:]]*count=\([0-9][0-9]*\).*/\1/p" "$log" | sort -n | tail -n 1
}

check_balance() {
    mode=$1
    log="$out/fixture-$mode.log"
    MONAD_OWNERSHIP="$mode" MONAD_ALLOC_STATS=1 \
        "$bin" run cli/src/main.mo -- test init/src/ownership_tests.mo > "$log" 2>&1
    rc=$?
    allocs=$(counts owned-constructors "$log")
    frees=$(counts owned-frees "$log")
    if [ "$rc" -ne 0 ]; then
        echo "FAIL ownership=$mode: fixture exited $rc (see $log)"
        status=1
    elif [ -z "$allocs" ] || [ -z "$frees" ]; then
        echo "FAIL ownership=$mode: no owned counters in $log"
        status=1
    elif [ "$allocs" -eq 0 ]; then
        echo "FAIL ownership=$mode: no owned allocations (see $log)"
        status=1
    elif [ "$allocs" -ne "$frees" ]; then
        echo "FAIL ownership=$mode: owned-constructors=$allocs owned-frees=$frees"
        status=1
    else
        echo "ok    ownership=$mode: $allocs owned allocations, $frees frees"
    fi
}

check_balance 1
check_balance poison

# Default build: no ownership, so the counters must stay at zero.
log="$out/fixture-default.log"
MONAD_ALLOC_STATS=1 "$bin" run cli/src/main.mo -- test init/src/ownership_tests.mo > "$log" 2>&1
rc=$?
allocs=$(counts owned-constructors "$log")
frees=$(counts owned-frees "$log")
if [ "$rc" -ne 0 ] || [ "${allocs:-x}" != "0" ] || [ "${frees:-x}" != "0" ]; then
    echo "FAIL default build: expected no owned allocations/frees (see $log)"
    status=1
else
    echo "ok    default build: no owned allocations"
fi

# Warn-mode gate: examples/ has no manifest of its own, so it inherits the
# root `[affine] mode = "warn"` and an ownership build must refuse it.
gate="$out/gate.log"
MONAD_OWNERSHIP=1 "$bin" run cli/src/main.mo -- build examples/hello.mo --no-cache -o "$out/hello" > "$gate" 2>&1
rc=$?
if [ "$rc" -eq 0 ]; then
    echo "FAIL gate: ownership build of examples/hello.mo was not refused"
    status=1
elif ! grep -q 'affine.*warn' "$gate"; then
    echo "FAIL gate: refusal message missing (see $gate)"
    status=1
else
    echo "ok    gate: warn-mode mote refused"
fi

[ "$status" -eq 0 ] && echo "ownership checks passed" || echo "ownership checks FAILED"
echo "logs: $out"
exit "$status"
