/// Tests moved out of `codegen::decls` so the production module stays readable.

use std::list {List.length}
use lang::types {
    Attribute, Decl, DebugName, Def, Identifier, Inductive, Multiplicity, NamePath, Struct,
    StructField, Term, Visibility, concrete, id_eq, sentinel,
}
use lang::module {ModuleInfo}
use lib::symbols {def_symbol_name}
use lang::name_text {unqualify_def_name}
use lib::free_names {collect_referenced_names}
use lib::util {}
use std::map {HashMap}
use lib::decls {extract_defs, extract_inductives, extract_structs, filter_reachable_decls, unit_test_inductive_decl, unit_test_struct_decl}

/// `filter_reachable_decls` must carry STRUCT decls through, exactly as
/// it carries inductives: the constructor-arity table codegen builds
/// comes from the list THIS function returns (`extract_structs`'s own
/// doc comment), so a struct dropped here is a struct whose implicit
/// `mk` codegen never learns is a constructor -- `examples/derive.mo`'s
/// `llc: use of undefined value '@Point.mk'`, which survived a first
/// attempt at the fix that taught `extract_structs` about structs but
/// left reachability still discarding them.
///
/// No Defs are needed to make the point: an unreachable root leaves the
/// def closure empty, so what comes back is exactly "inductives, structs,
/// and nothing else" -- asserted all three ways so a future filter that
/// keeps too much fails here too.
#[test]
def test_filter_reachable_decls_keeps_structs : Bool :=
    let decls : List Decl := List.cons (Decl.struct_d (unit_test_struct_decl "Point"))
        (List.cons (Decl.inductive_d (unit_test_inductive_decl "Slim")) List.empty) in
    let filtered := filter_reachable_decls (List.cons "cli.main::main" List.empty) decls in
    I64.beq (List.length (extract_structs filtered)) 1
        && I64.beq (List.length (extract_inductives filtered)) 1
        && I64.beq (List.length (extract_defs filtered)) 0

/// The eval path roots the closure at the BARE `main` (elaboration runs
/// before `qualify_modules` renames anything), while codegen roots at the
/// qualified `module::main`. Both are just strings to this filter; pin the
/// bare half, because an EMPTY reachable set would silently make the
/// unconditional elaboration gate vacuous for `monad eval`.
#[test]
def test_filter_reachable_decls_roots_at_a_bare_name : Bool :=
    let main_def : Def := Def.mk (NamePath.mk [Identifier.id "main"]) Term.hole
        (Term.var sentinel (DebugName.named (Identifier.id "helper")))
        List.empty List.empty Visibility.package_private List.empty in
    let helper_def : Def := Def.mk (NamePath.mk [Identifier.id "helper"]) Term.hole Term.hole
        List.empty List.empty Visibility.package_private List.empty in
    let unused_def : Def := Def.mk (NamePath.mk [Identifier.id "unused"]) Term.hole Term.hole
        List.empty List.empty Visibility.package_private List.empty in
    let decls : List Decl := [Decl.def_d main_def, Decl.def_d helper_def, Decl.def_d unused_def] in
    let filtered := filter_reachable_decls ["main"] decls in
    I64.beq (List.length (extract_defs filtered)) 2
        && I64.beq (List.length (extract_structs filtered)) 0
