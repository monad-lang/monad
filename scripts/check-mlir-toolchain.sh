#!/usr/bin/env bash
# usage: check-mlir-toolchain.sh [--inventory] [--require] [path/to/monad]
#
# Phase 0 of plans/bootstrapping/mlir-codegen.md: the toolchain and ABI
# spike. NO EMITTER is involved -- this script exists to retire the three
# risks that would otherwise only surface after a few thousand lines of
# MLIR emitter were written:
#
#   1. TOOLCHAIN CONTENTS. That the pinned `llvmPackages_21` set really
#      carries `mlir-opt`, `mlir-translate` and `mlir-runner` at the same
#      version as the `llc`/`clang` that consume the output, and that
#      `libmlir_cuda_runtime.so` is really absent (Decision 4's premise).
#      `--inventory` is the mode that prints this; it needs no fixtures.
#   2. THE BARE-POINTER MEMREF ABI. `fixtures/mlir/saxpy.mlir` takes
#      `memref<16xf32>` arguments; lowered through
#      `convert-func-to-llvm{use-bare-ptr-memref-call-conv=1}` each becomes
#      a bare pointer, so the result is a plain C function that
#      `fixtures/mlir/saxpy_caller/` reaches through `#[extern "c"]`
#      with a `Ptr` and no new host codegen.
#   3. DIAGNOSTICS BLINDNESS. `exec_cmd` returns only an exit status and a
#      failing `mlir-opt` pipeline reports its entire signal on stderr. The
#      last section drives a deliberately malformed pipeline and asserts
#      MLIR's own text reaches the caller.
#
# SKIP semantics: `mlir-opt` is not in the pinned set's PATH unless the dev
# shell has been rebuilt, and there is no MLIR in a plain checkout. A
# missing tool therefore prints `SKIP` and exits 0 -- a green CI job that
# tested nothing is worse than a skip, but a red job for a tool the shell
# was never given is worse still. `--inventory` distinguishes the two, and
# `--require` turns the skip into a failure for a job that is *supposed* to
# have the toolchain (the dev-shell-gated CI step).
#
# This script is opt-in: it is NOT part of the default sweep, exactly as
# scripts/check-wasm-target.sh is not. Wire it into CI beside that one.

set -euo pipefail

inventory_only=false
require=false
monad="monad"
while [ $# -gt 0 ]; do
    case "$1" in
        --inventory) inventory_only=true; shift ;;
        --require) require=true; shift ;;
        -h|--help) sed -n '2,32p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
        -*) echo "error: unknown flag $1" >&2; exit 2 ;;
        *) monad="$1"; shift ;;
    esac
done

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

tmp=$(mktemp -d "${TMPDIR:-/tmp}/monad-mlir-check.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

skip() {
    if $require; then
        echo "FAIL: $* (this job requires the MLIR toolchain)" >&2
        exit 1
    fi
    echo "SKIP: $*"
    echo "SKIP: not a pass -- nothing about MLIR was verified in this run"
    exit 0
}

# ── tool inventory ─────────────────────────────────────────────────────
#
# Version agreement is the point. `mlir-opt` emits LLVM-dialect IR that
# `mlir-translate` reads and `llc` compiles; textual MLIR and textual LLVM
# IR are both unversioned interfaces (Decision 2), so a version skew
# between any two of them is a confusing diagnostic rather than an
# evaluation error. `nix/packages.nix` pins all four from one attribute
# set for this reason; this is the check that the pin is actually in
# effect.
echo "== toolchain inventory =="
missing=""
for tool in mlir-opt mlir-translate mlir-runner llc clang; do
    if path=$(command -v "$tool" 2>/dev/null); then
        printf '  %-16s %s\n' "$tool" "$path"
    else
        printf '  %-16s MISSING\n' "$tool"
        missing="$missing $tool"
    fi
done

if [ -n "$missing" ]; then
    skip "missing tool(s):$missing -- rebuild the dev shell (nix/packages.nix pins llvmPackages_21, mlir included)"
fi

# The version each tool reports. `mlir-opt --version` prints
# "LLVM version 21.1.8", `llc --version` prints one too; clang prints
# "clang version 21.1.8". Compare the numbers, not the whole string.
version_of() {
    "$1" --version 2>/dev/null | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -1
}
mlir_v=$(version_of mlir-opt)
translate_v=$(version_of mlir-translate)
llc_v=$(version_of llc)
clang_v=$(version_of clang)
printf '  versions        mlir-opt=%s mlir-translate=%s llc=%s clang=%s\n' \
    "$mlir_v" "$translate_v" "$llc_v" "$clang_v"

[ -n "$mlir_v" ] || fail "mlir-opt --version printed no version"
[ "$mlir_v" = "$translate_v" ] \
    || fail "mlir-opt $mlir_v and mlir-translate $translate_v disagree"
[ "$mlir_v" = "$llc_v" ] \
    || fail "mlir-opt $mlir_v and llc $llc_v disagree -- the nix/packages.nix pin is not in effect"
[ "$mlir_v" = "$clang_v" ] \
    || fail "mlir-opt $mlir_v and clang $clang_v disagree -- the nix/packages.nix pin is not in effect"

# Decision 4's premise: the CUDA runner library is NOT in the nixpkgs MLIR
# output (it would need -DMLIR_ENABLE_CUDA_RUNNER=ON plus a CUDA toolkit at
# LLVM build time). If it ever appears, Phase 5's design is worth
# revisiting -- so this records it rather than silently assuming it.
mlir_prefix=$(cd "$(dirname "$(command -v mlir-opt)")/.." && pwd)
if find "$mlir_prefix" -name 'libmlir_cuda_runtime*' -print -quit 2>/dev/null | grep -q .; then
    echo "  NOTE            libmlir_cuda_runtime is PRESENT -- Decision 4 can be revisited"
else
    echo "  cuda runtime    absent, as Decision 4 requires"
fi
# `mlir-runner` is the renamed `mlir-cpu-runner` (LLVM 20). The old name
# must never appear in this repo, so assert the new one resolves.
command -v mlir-runner >/dev/null 2>&1 || fail "mlir-runner is missing (renamed from mlir-cpu-runner in LLVM 20)"

if $inventory_only; then
    echo "ok: MLIR toolchain inventory ($mlir_v)"
    exit 0
fi

# ── the pass pipeline ──────────────────────────────────────────────────
#
# The exact sequence Phase 2 will use. Ordering-sensitive, and the three
# passes most often omitted are the ones with a comment. This list is the
# one thing here that must be re-verified against `mlir-opt --help` on a
# version bump (the plan says so in "The CPU pass pipeline"; pass names
# have been renamed before -- `convert-memref-to-llvm` became
# `finalize-memref-to-llvm` in LLVM 17).
#
#   convert-scf-to-cf           the loop vocabulary leaves scf
#   expand-strided-metadata     omitted-by-default #1 -- required before
#                               the memref lowering for a bare-pointer ABI
#   convert-arith-to-llvm       scalar ops
#   convert-cf-to-llvm          what convert-scf-to-cf landed in
#   finalize-memref-to-llvm     omitted-by-default #2 (renamed in LLVM 17)
#   convert-func-to-llvm        use-bare-ptr-memref-call-conv=1 is the
#                               whole ABI decision -- a bare `float*` per
#                               memref argument, not a descriptor struct
#   reconcile-unrealized-casts  omitted-by-default #3, MANDATORY, last
pipeline='builtin.module('
pipeline="$pipeline"'convert-scf-to-cf,'
pipeline="$pipeline"'expand-strided-metadata,'
pipeline="$pipeline"'convert-arith-to-llvm,'
pipeline="$pipeline"'convert-cf-to-llvm,'
pipeline="$pipeline"'finalize-memref-to-llvm,'
pipeline="$pipeline"'convert-func-to-llvm{use-bare-ptr-memref-call-conv=1},'
pipeline="$pipeline"'reconcile-unrealized-casts)'

echo "== mlir-opt --verify-each =="
# `--verify-each` puts the verifier after every pass, so a lowering that
# produces structurally invalid IR fails at the pass that broke it rather
# than several stages later. That is the drift defence Decision 2 asks
# for.
mlir-opt --verify-each "--pass-pipeline=$pipeline" \
    fixtures/mlir/saxpy.mlir -o "$tmp/saxpy.llvm.mlir"
[ -s "$tmp/saxpy.llvm.mlir" ] || fail "mlir-opt produced no output"

# The round-trip half of the drift defence: re-parsing the lowered module
# must be byte-identical. If a future MLIR changes its pretty-printer, this
# is what notices.
mlir-opt "$tmp/saxpy.llvm.mlir" -o "$tmp/saxpy.llvm.rt.mlir"
cmp -s "$tmp/saxpy.llvm.mlir" "$tmp/saxpy.llvm.rt.mlir" \
    || fail "the lowered module does not round-trip byte-identically through mlir-opt"

# The ABI, asserted on the TEXT before any toolchain downstream of it can
# confuse the diagnosis. A `llvm.func` taking three bare pointers (plus the
# i32 scalar) is the whole of Decision 3; a descriptor struct would show up
# here as `!llvm.struct`.
grep -q 'llvm.func @saxpy' "$tmp/saxpy.llvm.mlir" \
    || fail "@saxpy did not lower to an llvm.func: $(head -20 "$tmp/saxpy.llvm.mlir")"
if grep -q '!llvm.struct' "$tmp/saxpy.llvm.mlir"; then
    fail "the lowering emitted a memref DESCRIPTOR struct -- use-bare-ptr-memref-call-conv did not apply"
fi
grep -q 'llvm.noalias' "$tmp/saxpy.llvm.mlir" \
    || fail "llvm.noalias was dropped by the lowering (Decision 5's aliasing carrier)"

echo "== mlir-translate --mlir-to-llvmir =="
mlir-translate --mlir-to-llvmir "$tmp/saxpy.llvm.mlir" -o "$tmp/saxpy.ll"
[ -s "$tmp/saxpy.ll" ] || fail "mlir-translate produced no output"
grep -q 'define.*@saxpy' "$tmp/saxpy.ll" \
    || fail "@saxpy is not a defined function in the translated LLVM IR"
grep -q 'define.*@total' "$tmp/saxpy.ll" \
    || fail "@total is not a defined function in the translated LLVM IR"
grep -q 'define.*@checksum' "$tmp/saxpy.ll" \
    || fail "@checksum is not a defined function in the translated LLVM IR"

echo "== llc =="
llc -filetype=obj "$tmp/saxpy.ll" -o "$tmp/saxpy.o"
[ -s "$tmp/saxpy.o" ] || fail "llc produced no object file"

# An archive rather than a bare object: `clang ... -lsaxpyfixture` finds a
# `lib*.a` on `-L`, which is the shape a mote's `[link] libs` already
# describes. No manifest is needed for that in this script, but keeping the
# archive shape means the eventual fixture mote needs no new plumbing.
ar rcs "$tmp/libsaxpyfixture.a" "$tmp/saxpy.o"

echo "== monad build (the #[extern \"c\"] caller) =="
# The caller reaches the kernel through the EXISTING extern wrapper: a
# `Ptr` in, `F64`/`I32` out, every cast already emitted by
# `emit_extern_param_cast`. Nothing here is MLIR-aware -- which is the
# point. `-L` comes through `LIBRARY_PATH` because `monad build` has no
# per-invocation link-flag flag; the mote-level `[link] libs` mechanism is
# for manifests, and this fixture deliberately has none.
#
# TWO mechanisms, and both are the real ones. `fixtures/mlir/saxpy_caller/
# mote.toml` supplies `[link] libs = ["saxpyfixture"]`, which becomes
# `-lsaxpyfixture` (`map_dash_l` in `llvm/src/link.mo`); `LIBRARY_PATH`
# supplies the matching `-L`, because clang turns it into `-L` entries and
# the archive lives in a temp dir. Be honest about the second half: there is
# no per-invocation `-L` flag on `monad build`, so a *user* would use a
# store/derivation path in `[link]` or install the library. For a fixture
# that must not bake in a /nix/store path, `LIBRARY_PATH` is the hook.
if [ -n "${LIBRARY_PATH:-}" ]; then
    export LIBRARY_PATH="$tmp:$LIBRARY_PATH"
else
    export LIBRARY_PATH="$tmp"
fi
"$monad" build fixtures/mlir/saxpy_caller \
    -o "$tmp/saxpy_caller" --no-cache \
    || fail "monad build failed"

# The archive has to have been reachable to the linker, or the build above
# would have failed on an undefined symbol -- so this is a second, explicit
# assertion that `-L` from LIBRARY_PATH really was in play, rather than the
# kernel symbols having come from somewhere unexpected.
command -v nm >/dev/null 2>&1 && {
    nm -g "$tmp/saxpy_caller" 2>/dev/null | grep -q ' T saxpy' \
        || fail "saxpy is not linked into the caller as a defined symbol"
}

[ -x "$tmp/saxpy_caller" ] || fail "monad build produced no binary"
"$tmp/saxpy_caller" >"$tmp/out.txt" 2>"$tmp/err.txt" \
    || fail "the caller crashed: $(cat "$tmp/err.txt")"

# Three numbers, one per line: the memref total, the scalar-only checksum,
# and the narrow-integer return. A comparison per line so a failure names
# the broken stage rather than just "wrong output".
# The first three lines are the three numbers; the fourth is the caller's
# own self-check. Asserted separately so a failure says WHICH broke --
# a wrong number is a kernel/ABI problem, a missing `ok` is a
# caller-logic problem.
expected='376
28
42'
actual=$(head -3 "$tmp/out.txt")
[ "$actual" = "$expected" ] \
    || fail "wrong numbers
--- expected ---
$expected
--- actual ---
$actual
(376 = saxpy's total through a bare-pointer memref, sum of 3i+1 for i in 0..15;
 28 = checksum 8, the pure-scalar path, sum of 0..7;
 42 = answer, the narrow i32 return)"

grep -qx 'ok' "$tmp/out.txt" \
    || fail "the caller's own self-check did not print ok: $(cat "$tmp/out.txt")"

echo "== diagnostics: a malformed pipeline must surface MLIR's message =="
# THE point of this section. A pass-pipeline failure's entire signal is a
# stderr diagnostic, and `exec_cmd` returns only an exit status -- so
# without a capture the compiler would report "exit 1" and nothing else.
# `Proc.capture` (std/src/process.mo) merges stdout+stderr and reads it
# back; this asserts the message survives. If this ever regresses, every
# Phase 2+ diagnostic regresses with it.
#
# There is no Monad program in the repo that drives mlir-opt yet (that is
# Phase 1's tool.mo), so the guarantee is exercised through `sh -c` with
# the same redirect Proc.capture uses. That is the mechanism under test.
set +e
sh -c "mlir-opt --pass-pipeline='builtin.module(no-such-pass)' fixtures/mlir/saxpy.mlir" \
    >"$tmp/bad.log" 2>&1
bad_rc=$?
set -e
[ "$bad_rc" -ne 0 ] || fail "mlir-opt accepted a non-existent pass"
grep -qi 'no-such-pass\|unregistered\|unknown' "$tmp/bad.log" \
    || fail "mlir-opt's diagnostic did not name the bad pass: $(cat "$tmp/bad.log")"

# And the same for a source-level error, which is what a bad kernel will
# look like: the location must survive, because `loc(...)` suffixes are how
# Phase 2 points a diagnostic back at Monad source.
cat >"$tmp/broken.mlir" <<'MLIR'
func.func @oops() -> i64 {
    %c = arith.constant 0 : i64
    %bad = arith.addi %c, %c : i32
    return %bad : i64
}
MLIR
set +e
mlir-opt --verify-each "$tmp/broken.mlir" -o /dev/null >"$tmp/broken.log" 2>&1
broken_rc=$?
set -e
[ "$broken_rc" -ne 0 ] || fail "mlir-opt accepted an ill-typed module"
grep -qi 'error' "$tmp/broken.log" \
    || fail "mlir-opt's error text was lost: $(cat "$tmp/broken.log")"

echo "ok: MLIR toolchain checks passed ($mlir_v)"
