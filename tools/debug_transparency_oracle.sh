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
# Scratch dir for the two builds per file; override to keep them.
SP="${ORACLE_TMP:-$(mktemp -d)}"
HERE=$(cd "$(dirname "$0")/.." && pwd)
cd "$HERE" || exit 1

# The self-hosted compiler under test. A missing binary is a hard error
# and never a fallback to the interpreter: quietly gating a different
# artifact than the one named is precisely the silence this oracle exists
# to remove.
MONAD_BIN="${MONAD_BIN:-${TMPDIR:-/tmp}/monad-bootstrap-ci/monad}"
if [ ! -x "$MONAD_BIN" ]; then
  echo "no self-hosted compiler at $MONAD_BIN"
  echo "build one:  cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o \"$MONAD_BIN\" --release"
  echo "or point MONAD_BIN at an existing binary."
  exit 1
fi

# Known gaps: these do not compile through the self-hosted pipeline yet.
# Each is a TODO, not a transparency failure -- the oracle has nothing to
# compare, because no IR is produced at all. Delete an entry the moment
# its gap closes. Do NOT add one to quiet a new failure: that is the exact
# silence this oracle's skip-to-FAIL change removed.
#
#   derive    -- `#[derive BEq ...]` does not expand. The ATTRIBUTE itself
#                parses (lang/parser.mo's own
#                test_attribute_parser_multi_ident_args covers it) and a
#                bare `struct` parses; `expand_decls` (lang/module.mo) has
#                no derive-macro expansion, so parse_all_decls stops at the
#                attribute. Reproduced identically against a worktree of
#                `main` -- pre-existing, not a branch regression.
#   json      -- native `f64_to_string` is not wired into the LLVM backend.
#   sha256    -- 11 unwired natives: u8_add, u32_{and,add,xor,sub,or,shl,
#                shr}, u8_to_u32, i64_to_u32, u32_to_u8.
#   structs   -- named-call param defaults (`def scale {factor : I64 := 2,
#                ...}`) are unsupported: named_call_check_missing_fields
#                (lang/typecheck/infer.mo) requires every declared param,
#                and its own doc comment says no default mechanism exists.
#   test_mote -- the mote system is Rust-host only (build_default_search_paths,
#                core/src/lib.rs); the self-hosted loader cannot resolve
#                `use greet {greet}` against motes/example/mote.toml.
KNOWN_GAPS="derive json sha256 structs test_mote"
gap_reason() {
  case "$1" in
    derive)    echo "\`#[derive ...]\` does not expand in the self-hosted \`expand_decls\`" ;;
    json)      echo "native \`f64_to_string\` is not wired into the LLVM backend" ;;
    sha256)    echo "11 unwired natives (u8_add, u32_{and,add,xor,sub,or,shl,shr}, u8_to_u32, i64_to_u32, u32_to_u8)" ;;
    structs)   echo "named-call param defaults (\`{factor : I64 := 2}\`) unsupported by the self-hosted typechecker" ;;
    test_mote) echo "the mote system is Rust-host only; no self-hosted resolution for \`use greet {greet}\`" ;;
    *)         echo "listed in KNOWN_GAPS" ;;
  esac
}
is_known_gap() {
  for g in $KNOWN_GAPS; do
    [ "$1" = "$g" ] && return 0
  done
  return 1
}

norm() { awk 'BEGIN{n=0}{l[n++]=$0}END{while(n>0&&l[n-1]=="")n--;for(i=0;i<n;i++)print l[i]}' "$1"; }
pass=0; fail=0; todo=0
for f in "$@"; do
  b=$(basename "$f" .mo)
  if is_known_gap "$b"; then
    echo "TODO  $f ($(gap_reason "$b"))"; todo=$((todo+1)); continue
  fi
  # `--release`, not a bare compile: debug info is ON by default since
  # stage 5, so a bare compile is itself a --debug build and comparing
  # it to `--debug` passes vacuously.
  "$MONAD_BIN" compile "$f" --release -o "$SP/o_$b.ll" >"$SP/o_$b.log" 2>&1
  "$MONAD_BIN" compile "$f" --debug -o "$SP/d_$b.ll" >"$SP/d_$b.log" 2>&1
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
echo "--- oracle: $pass ok, $fail FAIL, $todo TODO (known gaps)"
if [ "$todo" -gt 0 ]; then
  echo "--- TODO: $KNOWN_GAPS -- see KNOWN_GAPS in $0"
fi
[ "$fail" -eq 0 ]
