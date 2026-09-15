use lang.types {
  Def, Identifier, TypeConstraint, i64, id, lam, lit, mk, mp, named, num, type_,
}
use lang.codegen.ir {emit_module, mk}
use lang.codegen.emit {check_contains, compile_db_decls_ir, empty_attrs, mk}

open Term {lam, lit, type_}
open Literal {num}
open Identifier {id}
open DebugName {named}
open NumSuffix {i64}
open Param {mk}
open Def {mk}
open ModulePath {mp}

#[test]
def test_e2e_simple_literal : Bool :=
    let id := Identifier.id "myfunc" in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id empty_ids))
        (Term.type_ 1)
        (Term.lit (Literal.num 42 NumSuffix.i64))
        empty_cons
        empty_attrs
        Visibility.package_private in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    check_contains text "myfunc"

#[test]
def test_e2e_function_with_param : Bool :=
    let id := Identifier.id "add5" in
    let body := Term.lit (Literal.num 99 NumSuffix.i64) in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id empty_ids))
        (Term.type_ 1)
        term_
        empty_cons
        empty_attrs
        Visibility.package_private in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    check_contains text "add5"

#[test]
def test_e2e_module_structure : Bool :=
    let mod_ := lang.codegen.emit.compile_db_decls_ir empty_defs in
    let text := emit_module mod_ in
    if check_contains text "; ModuleID"
    then check_contains text "Type Definitions"
    else false

#[test]
def test_e2e_runtime_decls_present : Bool :=
    let mod_ := lang.codegen.emit.compile_db_decls_ir empty_defs in
    let text := emit_module mod_ in
    check_contains text "monad_alloc"

#[test]
def test_e2e_calling_convention : Bool :=
    let id := Identifier.id "f" in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id empty_ids))
        (Term.type_ 1)
        (Term.lit (Literal.num 1 NumSuffix.i64))
        empty_cons
        empty_attrs
        Visibility.package_private in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    check_contains text "cc 9"

/// Regression test for the `IO`-typed `main` garbage-exit-code fix
/// (`lang/codegen/emit.mo`'s `unwrap_io_return_blocks`/
/// `emit_type_head_is_io`): a `main` declared `IO I64` must have its
/// generated LLVM body call the runtime's `monad_get_field` to unwrap
/// the boxed `IO.io` payload before returning — confirmed by checking
/// the emitted IR text directly (same `check_contains`-on-IR-text
/// technique this whole file already uses, e.g.
/// `test_e2e_calling_convention`'s `"cc 9"` check).
#[test]
def test_e2e_io_main_unwraps_before_return : Bool :=
    let main_id := Identifier.id "main" in
    let io_type_id := DebugName.named (Identifier.id "IO") in
    let io_typ := Term.app (Term.var sentinel_idx io_type_id) (Term.type_ 1) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons main_id empty_ids))
        io_typ
        (Term.lit (Literal.num 5 NumSuffix.i64))
        empty_cons
        empty_attrs
        Visibility.package_private in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    // `monad_get_field` is always DECLARED at the top of every module
    // (`runtime_declarations`) regardless of whether anything calls it
    // -- checking for the bare name would pass even without the fix.
    // The actual CALL renders as `call i64 @monad_get_field(...)`
    // (`LLVMValue.call`'s own text form, `lang/codegen/ir.mo`), which
    // only appears if `main`'s own body was actually rewritten.
    check_contains text "call i64 @monad_get_field"

/// The negative case: an ordinary `I64`-typed `main` must NOT get the
/// unwrap treatment (it already returns a raw `i64`, unwrapping it
/// would corrupt a genuine numeric exit code) — guards against
/// `emit_type_head_is_io`/`ends_with_main` over-triggering.
#[test]
def test_e2e_non_io_main_does_not_unwrap : Bool :=
    let main_id := Identifier.id "main" in
    let def_ := Def.mk
        (ModulePath.mp (List.cons main_id empty_ids))
        (Term.type_ 1)
        (Term.lit (Literal.num 5 NumSuffix.i64))
        empty_cons
        empty_attrs
        Visibility.package_private in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    Bool.not (check_contains text "call i64 @monad_get_field")

#[partial]
def sentinel_idx : I64 := 0 - 1

#[partial]
def empty_defs : List Def := List.empty

#[partial]
def empty_ids : List Identifier := List.empty

#[partial]
def empty_cons : List TypeConstraint := List.empty
