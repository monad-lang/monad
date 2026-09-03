/// Regression tests for the `compose_seq` pure-argument splice
/// corruption (fixed via `compose_seq_acc`, `lang/codegen/emit.mo`):
/// a struct update `{ x with f := <expr> }` desugars at typecheck to a
/// constructor application whose EVERY argument is a single-case
/// projection match on `x` -- a BRANCHING argument, so each field
/// value's own fragment ends in a terminator with its computed value
/// sitting in a merge block closed `ret <phi>`. When a field's
/// expression contained a LITERAL operand (`x.f + 1`), that literal
/// argument (no instructions, no blocks) used to be composed via plain
/// `compose_seq`, whose `splice_into_terminal_block` rewrote the
/// projection's merge block from `ret <phi>` to `ret <literal>` --
/// destroying the projected value -- and, since `llvm_value_eq`
/// deliberately never matches literal pairs, left an unmatchable
/// splice-target token so the FOLLOWING compose steps (the arithmetic
/// call, the constructor alloc) all degraded into dead code appended
/// after the branch. The function's real return stayed `ret i64 1`
/// (the raw literal), so every caller did `monad_get_tag` on a small
/// integer and SIGSEGV'd -- the exact crash v29's
/// `module_info_cache_insert`/`module_info_cache_hit` hit on
/// `check examples/hello.mo`.
///
/// `compose_seq_acc` now makes a pure argument a complete no-op at
/// every accumulation site (argument lists, native operands,
/// callee-with-spine): it contributes no code and moves execution
/// nowhere, so the running splice-target token keeps identifying the
/// block execution is actually in. These tests compile each source
/// through the self-hosted backend and run the native binary, so a
/// regression reproduces the miscompile (wrong exit code) rather than
/// just an IR-shape mismatch.
use io {IO}
open IO {println}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// The minimal repro shape: `{ c with b := c.b + 1 }` -- the `+ 1`'s
/// literal operand directly follows the `b`-projection's branching
/// fragment. Before the fix, `bump`'s compiled body returned the raw
/// literal `1` (an untagged i64) instead of the new struct, and main
/// segfaulted on `monad_get_tag(1)`.
#[test]
def test_struct_update_field_plus_one : IO Bool :=
    let source := r#"use io {IO}
struct C {
    a : I64,
    b : I64,
}
def cempty : C := { a := 0, b := 0 }
def bump (c : C) : C := { c with b := c.b + 1 }
def main (args : List String) : IO I64 := do {
    let c : C := bump cempty;
    return c.b
}
"# in
    compile_source_run_expect source "test_struct_update_field_plus_one" 1

/// The `module_info_cache_hit` shape: a MIDDLE field updated with an
/// arithmetic expression while BOTH neighbors are preserved untouched
/// (they compile to their own projection matches before/after the
/// `hits + 1` fragment).
#[test]
def test_struct_update_middle_field_neighbors_preserved : IO Bool :=
    let source := r#"use io {IO}
struct D {
    x : I64,
    hits : I64,
    y : I64,
}
def dempty : D := { x := 7, hits := 0, y := 3 }
def hit (d : D) : D := { d with hits := d.hits + 1 }
def main (args : List String) : IO I64 := do {
    let d : D := hit dempty;
    return (I64.add d.hits (I64.add d.x d.y))
}
"# in
    compile_source_run_expect source "test_struct_update_middle_field_neighbors_preserved" 11

/// A PURE field value (a bare literal, no instructions at all) placed
/// BETWEEN two branching projection arguments -- the literal must reach
/// the constructor's set_field without rewriting the preceding `x`-
/// projection's merge block `ret`. (A literal in the FIRST field
/// composes against an empty accumulator and can't reproduce the
/// corruption -- the desugar emits arguments in struct-field order.)
#[test]
def test_struct_update_literal_field_value : IO Bool :=
    let source := r#"use io {IO}
struct D {
    x : I64,
    hits : I64,
    y : I64,
}
def dempty : D := { x := 7, hits := 41, y := 3 }
def zero_hits (d : D) : D := { d with hits := 0 }
def main (args : List String) : IO I64 := do {
    let d : D := zero_hits dempty;
    return (I64.add d.x (I64.add d.hits d.y))
}
"# in
    compile_source_run_expect source "test_struct_update_literal_field_value" 10

/// MULTIPLE updated fields in one update -- each field's expression
/// fragment must splice into the right place after the previous one
/// (`module_info_cache_insert`'s exact two-field shape: one call-valued
/// field, one arithmetic-valued field).
#[test]
def test_struct_update_two_fields_at_once : IO Bool :=
    let source := r#"use io {IO}
struct D {
    x : I64,
    hits : I64,
    y : I64,
}
def dempty : D := { x := 7, hits := 0, y := 3 }
def both (d : D) : D := { d with x := d.x + 1, y := d.y + 2 }
def main (args : List String) : IO I64 := do {
    let d : D := both dempty;
    return (I64.add d.x (I64.add d.hits d.y))
}
"# in
    compile_source_run_expect source "test_struct_update_two_fields_at_once" 13