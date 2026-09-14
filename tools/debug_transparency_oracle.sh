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
# offending function. A file that fails to compile in EITHER mode is a
# FAIL, not a skip -- a gate that quietly drops files is not a gate.
#
# Usage:  tools/debug_transparency_oracle.sh examples/*.mo
# Needs a devenv shell (the generated runtime links against boehmgc).
# Scratch dir for the two builds per file; override to keep them.
SP="${ORACLE_TMP:-$(mktemp -d)}"
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE"
norm() { awk 'BEGIN{n=0}{l[n++]=$0}END{while(n>0&&l[n-1]=="")n--;for(i=0;i<n;i++)print l[i]}' "$1"; }
pass=0; fail=0
for f in "$@"; do
  b=$(basename "$f" .mo)
  # `--release`, not a bare compile: debug info is ON by default since
  # stage 5, so a bare compile is itself a --debug build and comparing
  # it to `--debug` passes vacuously.
  # Check EXIT CODES, not output files: a compile that fails still writes
  # the .ll.ll (an empty module, then a linker error), so `-f` alone would
  # pass a file that never compiled.
  rel_rc=0; dbg_rc=0
  ./target/release/monad-rs run lang/main.mo -- compile "$f" --release -o "$SP/o_$b.ll" >"$SP/o_$b.log" 2>&1 || rel_rc=$?
  ./target/release/monad-rs run lang/main.mo -- compile "$f" --debug -o "$SP/d_$b.ll" >"$SP/d_$b.log" 2>&1 || dbg_rc=$?
  if [ "$rel_rc" -ne 0 ] || [ "$dbg_rc" -ne 0 ] || [ ! -f "$SP/o_$b.ll.ll" ] || [ ! -f "$SP/d_$b.ll.ll" ]; then
    echo "FAIL  $f (did not compile: --release rc=$rel_rc, --debug rc=$dbg_rc; last line: $(tail -n 1 "$SP/o_$b.log" 2>/dev/null))"
    fail=$((fail+1)); continue
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
