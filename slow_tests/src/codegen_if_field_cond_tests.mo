/// Regression tests for a struct's `Bool` field used directly as an `if`
/// condition.
///
/// `if t.done then ... else ...` -- ordinary, idiomatic code -- segfaulted
/// the moment it ran, and only when `done` was not the struct's FIRST field
/// (`plans/implementations/2026-10-04-struct-field-access-as-if-cond-
/// segfaults-nonzero-index.md`, found in a TODO app's HTML renderer).
///
/// The cause was two layers up from the crash. `type_check_if`
/// (`lang/src/typecheck/infer.mo`) gave the condition the KIND `Type` as
/// its expected type; a field access desugars to a `match`, whose arm type
/// `type_check_cases` unifies against that -- so the def failed to
/// elaborate, `elaborate_module_decls_best_effort` kept it un-elaborated,
/// and the parser's one-binder `field_access_chain` match reached codegen,
/// where `bind_match_fields` reads binder 0 from field 0. At index 0 that
/// is the right field by accident; at index 1 it is an unboxed `I64` that
/// `ensure_i1_cond` then handed to `monad_get_tag` as a pointer.
///
/// Three indices, because one index proves nothing: the pre-fix build was
/// correct at 0 and crashed at 1 and 2. No `#[test]` def reads a field
/// itself -- that takes the FIELD's LLVM type as the def's return type --
/// so every read lives in the compiled source.
open IO {println}
use codegen::test::e2e_harness {compile_source_run_expect}

/// `done` first: the index that always worked, kept as the control.
#[test]
def test_if_bool_field_at_index_zero : IO Bool :=
    let source := r#"struct FlagB {
    done : Bool,
    x : I64,
}
def ask (f : FlagB) : I64 := if f.done then 11 else 22
def main (args : List String) : IO I64 := do {
    return (ask ({ done := true, x := 1 } : FlagB))
}
"# in
    compile_source_run_expect source "test_if_bool_field_at_index_zero" 11

/// `done` second: the filed segfault.
#[test]
def test_if_bool_field_at_index_one : IO Bool :=
    let source := r#"struct FlagA {
    x : I64,
    done : Bool,
}
def ask (f : FlagA) : I64 := if f.done then 11 else 22
def main (args : List String) : IO I64 := do {
    return (ask ({ x := 1, done := false } : FlagA))
}
"# in
    compile_source_run_expect source "test_if_bool_field_at_index_one" 22

/// `done` third, and the other two fields of different types -- a read at
/// the wrong index lands on an `I64` or a `String` here, so the row
/// distinguishes "reads the right field" from "reads something truthy".
#[test]
def test_if_bool_field_at_index_two : IO Bool :=
    let source := r#"struct Todo {
    id : I64,
    title : String,
    done : Bool,
}
def mark (t : Todo) : I64 := if t.done then 33 else 44
def main (args : List String) : IO I64 := do {
    return (mark ({ id := 1, title := "x", done := true } : Todo))
}
"# in
    compile_source_run_expect source "test_if_bool_field_at_index_two" 33
