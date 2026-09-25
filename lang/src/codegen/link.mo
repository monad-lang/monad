// Term -> LLVM IR *text*, for callers that have a bare `List Def` and want
// a module's worth of .ll out of it. The toolchain half of "linking" -- llc,
// clang, the runtime object -- is `llvm/src/link.mo`, in the llvm mote; this
// file stays in lang because it speaks Term.

use lib::types {Def, NamePath, app, i64, id, lam, lit, mk, named, num, var}
use llvm::ir {emit_module, mk}
use lib::codegen::emit {check_contains, compile_db_decls_ir, mk}

open Term {app, lam, lit, var}
open Literal {num}
open Identifier {id}
open NumSuffix {i64}
open Param {mk}
open Def {mk}

/// Generate LLVM IR text from a list of Defs.
#[partial]
def compile_defs_to_ir (defs : List Def) : String :=
    let module_ := compile_db_decls_ir defs in
    emit_module module_

#[test]
def test_link_compile_defs_to_ir : Bool :=
    let id_val := Identifier.id "test" in
    let x_id := Identifier.id "x" in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let body := Term.app (Term.app add_var x_var) two in
    let term_ := Term.lam (DebugName.named x_id) (Term.sort (SortLevel.concrete 1)) body in
    let def_ := Def.mk (NamePath.npath [id_val]) (Term.sort (SortLevel.concrete 1)) term_ List.empty List.empty Visibility.package_private List.empty in
    let text := compile_defs_to_ir (List.cons def_ List.empty) in
    check_contains text "add i64"
