#!/bin/sh
# Transparency oracle for debug info.
#
# `--debug` may change what the compiler ANNOTATES; it must never change
# what the compiler DECIDES. For each file: compile twice, strip every
# debug addition from the --debug build, and require the two to be
# byte-identical.
#
# This exists because source locations ride the AST as `Term.ctx` wrappers,
# and ~180 sites across lang/scope.mo and lang/typecheck/infer.mo match on
# term SHAPE (`flatten_call_spine`, `class_method_ref`, `collect_db_params`,
# `term_has_struct_lit`, ...). A wrapper interposed where one of those looks
# makes it silently stop matching -- no type error, no crash, just a call
# that quietly fails to resolve or a function compiled with the wrong arity.
# Auditing every such site by hand is not a gate. This is: any such break
# changes the emitted instruction text, so the diff points straight at the
# offending function.
#
# What is gated is the SELF-HOSTED BINARY, not `monad-rs run cli/src/main.mo`
# -- the compiler interpreted by the Rust host. The binary is the artifact
# that ships, so it is the artifact that should be held to this property,
# and it is also ~40x faster per file (0.4s against ~18s), which is the
# difference between a 6-minute CI step and a few seconds. Build one first
# (`monad:bootstrap-compile` does, and CI runs that step immediately
# before this one) or point MONAD_BIN at your own.
#
# The comparison stops at the `.ll`. A file that fails to compile is a
# FAIL, not a skip -- a gate that quietly drops files is not a gate -- but
# what happens AFTER the IR is emitted (llc, clang, link) is deliberately
# not consulted: the property lives entirely in the emitted IR, half the
# corpus has no `def main` for runtime.c's `main` to call and so cannot
# link at all, and linking is already gated by `monad:bootstrap-compile`,
# which links the whole compiler and then runs it.
#
# Usage:  tools/debug_transparency_oracle.sh examples/*.mo
#         MONAD_BIN=/path/to/monad tools/debug_transparency_oracle.sh ...
# Needs a devenv shell (the generated runtime links against boehmgc).
# Scratch dir for the two builds per file; override to keep them. Made
# here rather than assumed: `mktemp -d` creates it, but a caller's
# ORACLE_TMP is a name they want kept and so is usually one that does not
# exist yet -- and an absent scratch dir does not fail loudly, it makes
# every `>"$SP/x.log"` redirect fail and reports the whole corpus as
# "no IR emitted".
SP="${ORACLE_TMP:-$(mktemp -d)}"
mkdir -p "$SP"
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE" || exit 1

# The self-hosted compiler under test. A missing binary is a hard error
# and never a fallback to the interpreter: quietly gating a different
# artifact than the one named is precisely the silence this oracle exists
# to remove.
# Where the ladder's scratch compiler lives, by the same definition the four
# scripts in scripts/ use -- see scripts/lib/bootstrap-dir.sh. This script had
# its own copy of the path, spelled into /tmp, which is shared by every
# worktree on the machine.
# shellcheck disable=SC2034  # read by the sourced helper, not here
MONAD_REPO_ROOT="$HERE"
# shellcheck source=scripts/lib/bootstrap-dir.sh
# shellcheck disable=SC1091  # the hook runs bare `shellcheck`; the line above names the path for -x
. "$HERE/scripts/lib/bootstrap-dir.sh" || {
  echo "cannot read $HERE/scripts/lib/bootstrap-dir.sh" >&2
  exit 1
}
MONAD_BIN="${MONAD_BIN:-$MONAD_BOOTSTRAP_BIN}"
if [ ! -x "$MONAD_BIN" ]; then
  echo "no self-hosted compiler at $MONAD_BIN"
  echo "build one:  cargo run --manifest-path rust/Cargo.toml --release -- run cli/src/main.mo build cli/src/main.mo -o \"$MONAD_BIN\" --release"
  echo "or point MONAD_BIN at an existing binary."
  exit 1
fi

# The build store, moved out of the way for the duration.
#
# `build` is the only verb left (the `compile` verb this oracle used to
# call was removed -- two verbs that both produce a binary differ only in
# which one you remember), and `build` is CACHED. This oracle gates what
# the compiler EMITS, so every one of its files has to compile for real
# rather than possibly replay a recorded emission.
#
# A hit no longer *breaks* this oracle -- the IR is keyed and a hit replays
# it beside the binary (`replay_ir_beside`, cli/src/main.mo), so the `.ll`
# this reads exists either way. That is what the private store used to be
# for, back when a hit wrote no `.ll` and every replayed file read as
# "no IR emitted" -- a FAIL with no compiler anywhere in it. What the
# private store still buys is the stronger claim: with it, the emission
# being gated was produced by the compiler under test in this run, not
# recorded earlier from the same key. Sound either way (the key covers the
# compiler digest), so this is a choice about what the oracle is evidence
# for -- and for an oracle, "the compiler just emitted this" is the one
# worth paying for.
#
# A private store per run is how that is guaranteed, rather than left to
# the accident of a cold one -- and a fresh `mktemp -d` per run is how it
# stays private, rather than a fixed name this script would have to clear
# first. `ORACLE_TMP` exists to KEEP the scratch of a run, so a second run
# sharing one must not find the first run's entries in it. Nothing is
# deleted here, on purpose: `ORACLE_TMP` is a caller's path and this
# script has no business removing anything under it.
MONAD_TARGET_DIR="$(mktemp -d "$SP/store.XXXXXX")"
export MONAD_TARGET_DIR

norm() { awk 'BEGIN{n=0}{l[n++]=$0}END{while(n>0&&l[n-1]=="")n--;for(i=0;i<n;i++)print l[i]}' "$1"; }
pass=0; fail=0
for f in "$@"; do
  b=$(basename "$f" .mo)
  # `--release`, not a bare build: debug info is ON by default since
  # stage 5, so a bare build is itself a --debug build and comparing
  # it to `--debug` passes vacuously.
  "$MONAD_BIN" build "$f" --release -o "$SP/o_$b.ll" >"$SP/o_$b.log" 2>&1
  "$MONAD_BIN" build "$f" --debug -o "$SP/d_$b.ll" >"$SP/d_$b.log" 2>&1
  # The compiler's OWN verdict on whether it got as far as trustworthy
  # IR. Not the exit code, which says "linked" and so fails on every
  # file without a `main`; and not file existence either, because a
  # parse failure still writes an (empty) .ll.ll through the
  # `compile_parsed_decls` error-reporting fallback.
  broke=$(grep -h -m1 -E "^(parse error:|FAILED at stage:)" "$SP/o_$b.log" "$SP/d_$b.log" 2>/dev/null | head -n 1)
  if [ -n "$broke" ]; then
    echo "FAIL  $f (did not compile: $broke)"; fail=$((fail+1)); continue
  fi
  if [ ! -f "$SP/o_$b.ll.ll" ] || [ ! -f "$SP/d_$b.ll.ll" ]; then
    echo "FAIL  $f (no IR emitted)"; fail=$((fail+1)); continue
  fi
  norm "$SP/o_$b.ll.ll" > "$SP/o_$b.norm"
  "$HERE/tools/strip_dbg.sh" "$SP/d_$b.ll.ll" > "$SP/d_$b.norm"
  if diff -q "$SP/o_$b.norm" "$SP/d_$b.norm" >/dev/null; then
    echo "ok    $f"; pass=$((pass+1))
  else
    echo "FAIL  $f  ($(diff "$SP/o_$b.norm" "$SP/d_$b.norm" | grep -c '^[<>]') differing lines)"; fail=$((fail+1))
  fi
done
echo "--- oracle: $pass ok, $fail FAIL"
[ "$fail" -eq 0 ]
