#!/usr/bin/env bash
# Self-test for scripts/check-affine-closure.sh.
#
# The gate is only worth wiring into pre-commit/CI if it fails on the bugs
# it exists for. This drives it against a throwaway closure root: a new
# warn table, a stale allowlist entry, an `[affine] mode = "error"` table,
# a comment that only mentions warn, an escape hatch outside the exempt
# test, closure-list drift, and the dynamic ceiling/FAIL parsing (including
# --affine-only) and its killed-check refusal to grade a partial log.
#
# Usage: scripts/check-affine-closure-selftest.sh
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
checker="$root/scripts/check-affine-closure.sh"
tmp=$(mktemp -d)
bindir=$(mktemp -d)
trap 'rm -rf "$tmp" "$bindir"' EXIT

fail=0
pass() { echo "ok:   $*"; }
bad() { echo "FAIL: $*" >&2; fail=1; }

fixture() {
    rm -rf "$tmp"
    mkdir -p "$tmp/scripts/lib" "$tmp/alpha/src" "$tmp/beta/src"
    printf 'alpha\nbeta\n' > "$tmp/scripts/lib/compiler-closure.txt"
    : > "$tmp/scripts/affine-closure-allowlist.txt"
}

manifest() { # mode: none|warn|error|other
    case "$1" in
        none) printf '[mote]\nname = "alpha"\n' > "$tmp/$2/mote.toml" ;;
        warn) printf '[mote]\nname = "alpha"\n\n[affine]\nmode = "warn"\n' > "$tmp/$2/mote.toml" ;;
        error) printf '[mote]\nname = "alpha"\n\n[affine]\nmode = "error"\n' > "$tmp/$2/mote.toml" ;;
        other) printf '[mote]\nname = "alpha"\n\n[affine]\nmode = "off"\n' > "$tmp/$2/mote.toml" ;;
    esac
}

run_static() {
    set +e
    out=$(AFFINE_CLOSURE_ROOT="$tmp" "$checker" --static 2>&1)
    rc=$?
    set -e
}

expect() { # want needle label
    local want=$1 needle=${2:-} label=$3
    if [ "$rc" -ne "$want" ]; then
        bad "$label: exit $rc, wanted $want"
        # shellcheck disable=SC2001  # sed is the clearest way to indent a block
        echo "$out" | sed 's/^/      /' >&2
    elif [ -n "$needle" ] && ! grep -q -- "$needle" <<<"$out"; then
        bad "$label: output lacks '$needle'"
        # shellcheck disable=SC2001  # sed is the clearest way to indent a block
        echo "$out" | sed 's/^/      /' >&2
    else
        pass "$label"
    fi
}

# 1. A new warn table that is not allowlisted.
fixture
manifest warn alpha
manifest none beta
run_static
expect 1 "not allowlisted" "new warn table fails"

# 2. The same table, allowlisted.
fixture
manifest warn alpha
manifest none beta
printf 'alpha\n' > "$tmp/scripts/affine-closure-allowlist.txt"
run_static
expect 0 "" "allowlisted warn passes"

# 3. A stale allowlist entry (the mote is already clean).
fixture
manifest none alpha
manifest none beta
printf 'alpha\n' > "$tmp/scripts/affine-closure-allowlist.txt"
run_static
expect 1 "no longer warn" "stale allowlist entry fails"

# 4. An [affine] table in error mode: delete the table, error is the default.
fixture
manifest error alpha
manifest none beta
run_static
expect 1 "delete the table" "error-mode table fails"

# 5. A comment that mentions the table must not count as one.
fixture
manifest none alpha
manifest none beta
printf '# [affine]\n# mode = "warn"\n[mote]\nname = "alpha"\n' > "$tmp/alpha/mote.toml"
run_static
expect 0 "" "comment mentioning warn is ignored"

# 6. #[allow_non_affine] outside the one exempt negative test.
fixture
manifest none alpha
manifest none beta
printf '#[allow_non_affine "selftest"]\ndef f : I64 := 1\n' > "$tmp/alpha/src/x.mo"
run_static
expect 1 "allow_non_affine" "escape hatch outside the test fails"

# 7. Closure-list drift against build-self-hosted.sh. The fixture's scan is
# the real one in miniature, `motes/toolkit` line included: that line is what
# closes the group, and the checker anchors on it.
scan_fixture() { # extra-trees...  -- writes a build-self-hosted.sh whose find
                  # list is the real prefix plus beta plus the given extras
    local extras=""
    [ "$#" -gt 0 ] && extras=" $* "
    # shellcheck disable=SC2016  # the literal `$(find ...)` is the fixture's point
    printf '  newer="$(find init std sys lang codegen cli llvm runtime build eval \\\n    motes/clap motes/fmt motes/json motes/log motes/lsp motes/parsec motes/toml motes/toolkit%s\\\n    \\( -name "*.mo" -print -quit)"\n' \
        "$extras" > "$tmp/scripts/build-self-hosted.sh"
}

fixture
manifest none alpha
manifest none beta
printf 'extra\n' >> "$tmp/scripts/lib/compiler-closure.txt"
scan_fixture
run_static
expect 1 "drift" "closure-list drift fails"

# 8. THE REGRESSION THIS ANCHOR EXISTS FOR. A new tree joined the build's
# find list (`mlir`, 8257f9af) and the closure list was not updated. The old
# text anchor stopped matching entirely, so the parse was EMPTY and the diff
# blamed all 19 closure motes for one missing line. The failure must instead
# name the unmatched entries, which here are the fixture's alpha/beta/extra
# against a list carrying only the real trees plus `zzznew`.
fixture
manifest none alpha
manifest none beta
scan_fixture zzznew
run_static
expect 1 "drift" "a newly added tree still reports drift, not an empty parse"
if grep -q 'cannot parse' <<<"$out"; then
    bad "case 8: an inserted tree must not be reported as an unparseable scan"
elif ! grep -q -e '^+zzznew$' <<<"$out" || ! grep -q -e '^-alpha$' <<<"$out"; then
    bad "case 8: drift diff must name both sides (+zzznew, -alpha)"
else
    pass "case 8: drift diff names the added and the missing entries"
fi

# 9. A scan the checker cannot read is its OWN failure, never "drift": an
# empty parse must not render as every mote having drifted.
fixture
manifest none alpha
manifest none beta
printf '#!/usr/bin/env bash\necho no scan here\n' > "$tmp/scripts/build-self-hosted.sh"
run_static
expect 1 "cannot parse" "an unreadable scan fails loudly"
if grep -q 'drift against' <<<"$out"; then
    bad "case 9: an unparseable scan must not be reported as closure drift"
else
    pass "case 9: an unparseable scan is not reported as drift"
fi

# 10. A scan missing its closing `motes/toolkit` line is unparseable too: a
# truncated read would otherwise silently grade a prefix of the closure.
fixture
manifest none alpha
manifest none beta
# shellcheck disable=SC2016  # the literal `$(find ...)` is the fixture's point
printf '  newer="$(find init std sys lang codegen cli llvm runtime build eval \\\n    motes/clap motes/fmt \\\n    \\( -name "*.mo" -print -quit)"\n' > "$tmp/scripts/build-self-hosted.sh"
run_static
expect 1 "cannot parse" "a scan with no closing motes/toolkit fails loudly"

# ── dynamic: a fake compiler with canned output ──────────────────────

fake="$bindir/fake-monad"
cat > "$fake" <<'FAKE'
#!/usr/bin/env bash
case "$1" in
    version) echo "${FAKE_VERSION:-deadbee}" ;;
    check) cat "${FAKE_CHECK_OUTPUT:?}"; exit "${FAKE_CHECK_RC:-0}" ;;
    *) echo "fake: unsupported $1" >&2; exit 2 ;;
esac
FAKE
chmod +x "$fake"

run_dynamic() { # output rc
    printf '%s\n' "$1" > "$tmp/check.out"
    set +e
    out=$(AFFINE_CLOSURE_ROOT="$tmp" FAKE_CHECK_OUTPUT="$tmp/check.out" FAKE_CHECK_RC="$2" \
        "$checker" --dynamic "$fake" --no-commit-check 2>&1)
    rc=$?
    set -e
}

fixture
manifest warn alpha
manifest none beta
printf 'alpha 2\n' > "$tmp/scripts/affine-closure-allowlist.txt"
run_dynamic 'WARN  alpha/src/x.mo (3 warning(s))
ok    beta/src/y.mo
2 file(s) checked, 0 error(s), 3 warning(s)' 0
expect 1 "ceiling is 2" "dynamic: count above the ceiling fails"

fixture
manifest warn alpha
manifest none beta
printf 'alpha 5\n' > "$tmp/scripts/affine-closure-allowlist.txt"
run_dynamic 'WARN  alpha/src/x.mo (3 warning(s))
ok    beta/src/y.mo
2 file(s) checked, 0 error(s), 3 warning(s)' 0
expect 0 "lower the ceiling" "dynamic: count below the ceiling passes with a note"

fixture
manifest none alpha
manifest none beta
run_dynamic 'FAIL  beta/src/y.mo (1 error(s))
2 file(s) checked, 1 error(s), 0 warning(s)' 1
expect 1 "error(s)" "dynamic: a FAIL fails the gate"

# The FAIL count is the header's error count, not the number of files.
fixture
manifest none alpha
manifest none beta
run_dynamic 'FAIL  beta/src/y.mo (6 error(s))
2 file(s) checked, 6 error(s), 0 warning(s)' 1
expect 1 "beta: 6 error(s)" "dynamic: a FAIL reports its error count"
if grep -q 'ok:   beta' <<<"$out"; then
    bad "dynamic: a failed mote must not also print ok"
else
    pass "dynamic: a failed mote does not also print ok"
fi

# --affine-only: a non-affine error (the nightly lagging main) is a note;
# an affine error still fails.
run_dynamic_affine() { # output rc
    printf '%s\n' "$1" > "$tmp/check.out"
    set +e
    out=$(AFFINE_CLOSURE_ROOT="$tmp" FAKE_CHECK_OUTPUT="$tmp/check.out" FAKE_CHECK_RC="$2" \
        "$checker" --dynamic "$fake" --no-commit-check --affine-only 2>&1)
    rc=$?
    set -e
}

fixture
manifest none alpha
manifest none beta
# shellcheck disable=SC2016  # backticks are literal diagnostic text
run_dynamic_affine 'FAIL  beta/src/y.mo (1 error(s))
error: non-exhaustive match: `Vec.cons` is not covered (add an arm for it, or a `_` arm) in t
  --> beta/src/y.mo

2 file(s) checked, 1 error(s), 0 warning(s)' 1
expect 0 "not graded" "dynamic --affine-only: a non-affine error is a note"

fixture
manifest none alpha
manifest none beta
# shellcheck disable=SC2016  # backticks are literal diagnostic text
run_dynamic_affine 'FAIL  beta/src/y.mo (2 error(s))
error: non-exhaustive match: `Vec.cons` is not covered (add an arm for it, or a `_` arm) in t
  --> beta/src/y.mo

error: `x` : Thing is used 2 times but is affine; share it with `Shared`, give its type a Copy instance, or copy it with `Clone.clone` in f
  --> beta/src/y.mo

2 file(s) checked, 2 error(s), 0 warning(s)' 1
expect 1 "beta: 1 error(s)" "dynamic --affine-only: an affine error fails"

# A killed check (137, e.g. the OOM killer) leaves a partial or empty log.
# Grading it would report every mote at zero; it must fail loudly instead.
fixture
manifest none alpha
manifest none beta
run_dynamic '' 137
expect 1 "killed" "dynamic: a killed check fails"
if grep -q 'within ceiling' <<<"$out"; then
    bad "dynamic: a killed check must not grade the partial log"
else
    pass "dynamic: a killed check does not grade the partial log"
fi

if [ "$fail" -ne 0 ]; then
    echo "check-affine-closure selftest: FAILED" >&2
    exit 1
fi
echo "check-affine-closure selftest: OK"
