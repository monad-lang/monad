#!/usr/bin/env bash
# usage: check-mlir-goldens.sh [--require] [--write] [path/to/monad]
#
# Phase 1 of plans/bootstrapping/mlir-codegen.md: the golden suite.
#
# Three checks per golden, in increasing strength:
#
#   1. EMIT == GOLDEN. `monad script mlir-goldens --name X` renders the
#      module `mlir/src/tests/golden_modules.mo` builds, and the bytes must
#      equal `fixtures/mlir/goldens/X.mlir`. This is the SHAPE test
#      (Verification Strategy layer 2): a `memref<16xf32>` that silently
#      became `memref<?xf32>` still compiles and still runs, and only a
#      byte comparison sees it.
#
#   2. `mlir-opt --verify-each` ACCEPTS it. A printer can be
#      self-consistently wrong -- the first version of `print.mo` emitted
#      `func.return` where MLIR prints `return`, put an op's `loc(...)`
#      where it is a parse error, and used `%argN` for an `scf.for`
#      induction variable that has no block argument. Every one of those
#      byte-compared clean against a golden this same printer wrote. Real
#      `mlir-opt` caught all four.
#
#   3. THE MODULE ROUND-TRIPS. `mlir-opt X.mlir -o Y.mlir` twice, and the
#      two outputs must be byte-identical. That is Decision 2's defence
#      against MLIR release churn: textual MLIR is not a versioned
#      interface, so the round trip IS the version test.
#
#      NOTE what is compared: `mlir-opt`'s output against ITSELF, not
#      against the golden. `mlir-opt` renames every SSA value (`%c0` ->
#      `%arg2`), re-spells float constants (`1.0` -> `1.000000e+00`) and
#      drops `loc(...)` unless `--mlir-print-debuginfo` is passed -- so
#      comparing its output to OUR text would fail for reasons that are not
#      errors. The golden's own spelling is pinned by check 1; the round
#      trip pins MLIR's stability of its own output. Both matter, and only
#      this split tests both.
#
# `--write` regenerates the goldens from the emitter. Use it ONLY for a
# deliberate printer change, and read the resulting diff: a golden updated
# to match a bug is a golden that stops testing anything.
#
# SKIP semantics, the same as check-mlir-toolchain.sh and for the same
# reason: `mlir-opt` is not on PATH unless the dev shell was rebuilt, so a
# missing tool prints `SKIP` and exits 0, `--require` turns that into a
# failure for a job that is supposed to have the toolchain. Check 1 needs
# no MLIR at all, so it always runs -- a golden script that skipped
# everything would be the green-and-empty job Phase 0's `--require` exists
# to prevent.
#
# This script is opt-in: it is NOT part of the default sweep.

set -euo pipefail

require=false
write_mode=false
monad="monad"
while [ $# -gt 0 ]; do
    case "$1" in
        --require) require=true; shift ;;
        --write) write_mode=true; shift ;;
        # The header comment block, from line 2 to the last consecutive
        # `#` line -- not a hard-coded range, which truncates silently the
        # instant the header grows (it has).
        -h|--help) awk 'NR>1 && /^#/ { print; next } NR>1 { exit }' "${BASH_SOURCE[0]}" \
                       | sed 's/^# \{0,1\}//'; exit 0 ;;
        -*) echo "error: unknown flag $1" >&2; exit 2 ;;
        *) monad="$1"; shift ;;
    esac
done

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

goldens=fixtures/mlir/goldens

tmp=$(mktemp -d "${TMPDIR:-/tmp}/monad-mlir-goldens.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

# ── the emitter ────────────────────────────────────────────────────────
#
# The compiler writes ONE progress line to STDOUT before the program
# starts, and that line is ANSI-coloured (`compiling: ...` / `cached: ...`
# wrapped in escapes). So a plain stdout redirect is not clean, and the
# first version of this script silently wrote that line into the first
# golden's bytes.
#
# Two mechanisms, both needed:
#   * `ANSI` strips the escapes.
#   * `strip_progress` drops the progress lines themselves.
# A `grep -v` on the coloured text does NOT work -- the escape is before the
# word, so `^cached:` never matches. That is what produced
# `cached:.mlir is missing` from this script's own error message.
ANSI=$'\033\[[0-9;]*m'
strip_progress() {
    sed -e "s/${ANSI}//g" \
        | grep -v '^cached: \|^compiling: \|^Compilation finished' || true
}

emit() {
    "$monad" script mlir-goldens -- --name "$1" 2>/dev/null | strip_progress
}

names=$("$monad" script mlir-goldens -- --list 2>/dev/null | strip_progress)
[ -n "$names" ] || fail "the emitter listed no goldens (is scripts/mlir_goldens.mo registered in mote.toml?)"

count=0
for name in $names; do
    golden="$goldens/$name.mlir"
    count=$((count + 1))

    # ── 1. emit == golden ──────────────────────────────────────────
    emit "$name" > "$tmp/$name.emit.mlir"
    [ -s "$tmp/$name.emit.mlir" ] || fail "$name rendered EMPTY"

    if $write_mode; then
        cp "$tmp/$name.emit.mlir" "$golden"
        echo "  wrote   $golden"
        continue
    fi

    [ -f "$golden" ] || fail "$golden is missing -- run this script with --write once and review the result"
    if ! cmp -s "$tmp/$name.emit.mlir" "$golden"; then
        # A unified diff, capped: an unbounded one on a large module helps
        # nobody, and the first hunk is what localises a printer change.
        echo "--- $name: emitted vs $golden ---" >&2
        diff -u "$golden" "$tmp/$name.emit.mlir" >&2 || true
        fail "$name: print_module does not match its golden"
    fi
    echo "  match   $golden"

    # ── 2 and 3 need the toolchain ─────────────────────────────────
    if ! command -v mlir-opt >/dev/null 2>&1; then
        continue
    fi

    # `--verify-each` puts the verifier after every pass; with no pass
    # pipeline at all it still verifies the parsed module, which is what
    # catches an op-level spelling MLIR's parser would accept and its
    # verifier would not.
    if ! mlir-opt --verify-each "$golden" -o "$tmp/$name.verified.mlir" >"$tmp/$name.log" 2>&1; then
        echo "--- mlir-opt --verify-each rejected $name ---" >&2
        cat "$tmp/$name.log" >&2
        fail "$name: the emitted module is not valid MLIR"
    fi

    mlir-opt "$tmp/$name.verified.mlir" -o "$tmp/$name.rt1.mlir" >>"$tmp/$name.log" 2>&1 \
        || { cat "$tmp/$name.log" >&2; fail "$name: mlir-opt could not re-read its own output"; }
    mlir-opt "$tmp/$name.rt1.mlir" -o "$tmp/$name.rt2.mlir" >>"$tmp/$name.log" 2>&1 \
        || { cat "$tmp/$name.log" >&2; fail "$name: mlir-opt could not re-read its second output"; }
    if ! cmp -s "$tmp/$name.rt1.mlir" "$tmp/$name.rt2.mlir"; then
        diff -u "$tmp/$name.rt1.mlir" "$tmp/$name.rt2.mlir" >&2 || true
        fail "$name: mlir-opt's own output does not round-trip byte-identically"
    fi
    echo "  verify  $golden (mlir-opt --verify-each, round-trip stable)"
done

[ "$count" -gt 0 ] || fail "no goldens were checked"

if $write_mode; then
    echo "ok: wrote $count golden(s) -- review the diff before committing"
    exit 0
fi

if ! command -v mlir-opt >/dev/null 2>&1; then
    if $require; then
        fail "mlir-opt is not on PATH (this job requires the MLIR toolchain; rebuild the dev shell -- nix/packages.nix pins llvmPackages_21, mlir included)"
    fi
    echo "SKIP: $count golden(s) byte-matched, but mlir-opt is absent so NOTHING was verified against real MLIR"
    echo "SKIP: not a full pass -- rebuild the dev shell, or run with --require to make this fatal"
    exit 0
fi

echo "ok: $count MLIR golden(s) matched, verified and round-tripped"