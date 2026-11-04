/// Regression tests for the `compose_seq` pure-argument splice
/// corruption (fixed via `compose_seq_acc`, `codegen/emit.mo`).
///
/// A struct update `{ x with f := <expr> }` desugars at typecheck to a
/// constructor application inside a single-case match on `x` -- a
/// BRANCHING term, so the arm's value sits in a merge block closed
/// `ret <phi>`. When these rows were written the desugaring built one
/// projection match PER un-overridden field instead of one match over the
/// base (`type_check_struct_update`, `lang/src/typecheck/infer.mo`,
/// changed 2026-10-05 so the base is evaluated once); the composition
/// hazard is the same either way, and so are these rows' numbers. When a field's
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
open IO {println}
use codegen::test::e2e_harness {compile_source_run_expect}

/// The minimal repro shape: `{ c with b := c.b + 1 }` -- the `+ 1`'s
/// literal operand directly follows the `b`-projection's branching
/// fragment. Before the fix, `bump`'s compiled body returned the raw
/// literal `1` (an untagged i64) instead of the new struct, and main
/// segfaulted on `monad_get_tag(1)`.
#[test]
def test_struct_update_field_plus_one : IO Bool :=
    let source := r#"struct C {
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
    let source := r#"struct D {
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
    let source := r#"struct D {
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
    let source := r#"struct D {
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

/// A struct update whose base is a parenthesized CALL -- which did not
/// parse at all until the base stopped being a bare identifier
/// (`plans/implementations/2026-10-04-struct-update-paren-base-fails-to-
/// parse.md`). It runs the whole way through, so the row covers the
/// desugaring as well as the grammar: the override lands and both
/// untouched fields come back from the base, which is what a wrong binder
/// or a wrong index would change (40 + 5 + 1 = 46; an override that failed
/// to land gives 206, and the harness compares a process exit code, so
/// every total here stays under 256).
///
/// That the base is evaluated ONCE is a property of the term shape rather
/// than of any value this program can print; it is pinned where the shape
/// is built, by `test_struct_update_is_one_match_over_the_base`
/// (`lang/src/typecheck/infer.mo`).
#[test]
def test_struct_update_paren_call_base : IO Bool :=
    let source := r#"struct Resp {
    status : I64,
    body : I64,
    tag : I64,
}
def make (b : I64) : Resp := { status := 200, body := b, tag := 1 : Resp }
def bad_request (b : I64) : Resp := { (make b) with status := 40 }
def rstatus (r : Resp) : I64 := r.status
def rbody (r : Resp) : I64 := r.body
def rtag (r : Resp) : I64 := r.tag
def main (args : List String) : IO I64 := do {
    let r : Resp := bad_request 5;
    return (I64.add (rstatus r) (I64.add (rbody r) (rtag r)))
}
"# in
    compile_source_run_expect source "test_struct_update_paren_call_base" 46
