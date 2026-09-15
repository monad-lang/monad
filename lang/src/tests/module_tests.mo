use lang.types {
  Decl, Def, Identifier, InductConstructor, Inductive, LocalScope, LocalVar,
  ModulePath, NameRef, Param, Scope, ScopeData, ScopeDef, ScopeError,
  TypeConstraint, def_d, hole, id, inductive_d, mk, mp, nid, type_,
}
use lang.scope {
  build_scope_from_decls, resolve_def_in_scope_by_name, scope_find_inductive,
  scope_resolve_name,
}


// --- Helpers ---

def empty_local_scope : LocalScope :=
    let empty_vars : List LocalVar := List.empty in
    let empty_parent : Option LocalScope := Option.none in
    { vars := empty_vars, parent := empty_parent }

def test_module_path : ModulePath :=
    let test_id : Identifier := Identifier.id "Test" in
    let empty_id_list : List Identifier := List.cons test_id List.empty in
    ModulePath.mp empty_id_list

def make_scope (sd : ScopeData) : Scope :=
    let path : ModulePath := test_module_path in
    let empty_parent : Option Scope := Option.none in
    { module_id := path, scope := sd, parent := empty_parent }

def name_to_path (i : Identifier) : ModulePath :=
    let empty_id_list : List Identifier := List.empty in
    ModulePath.mp (List.cons i empty_id_list)

// Typed empty lists to avoid forall inference issues
def empty_decls_list : List Decl := List.empty
def empty_constraints : List TypeConstraint := List.empty
def empty_attrs : List Attribute := List.empty
def empty_params : List Param := List.empty
def empty_constructors : List InductConstructor := List.empty

// --- Test: Empty module has builtins ---

#[test]
def test_parse_empty_has_builtins : Bool :=
    let path : ModulePath := test_module_path in
    let sd : ScopeData := build_scope_from_decls path empty_decls_list in
    let scope : Scope := make_scope sd in
    let type_ref : NameRef := NameRef.nid (Identifier.id "Type") in
    let locals : LocalScope := empty_local_scope in
    match scope_resolve_name type_ref scope locals {
        ok _ => true,
        err _ => false
    }

// --- Test: Build scope with a manually constructed def ---

#[test]
def test_scope_def_resolves : Bool :=
    let path : ModulePath := test_module_path in
    let defname : ModulePath := name_to_path (Identifier.id "add") in
    let def_decl : Def := Def.mk defname (Term.type_ 1) Term.hole empty_constraints empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.def_d def_decl) empty_decls_list in
    let sd : ScopeData := build_scope_from_decls path decl_list in
    let scope : Scope := make_scope sd in
    let add_ref : NameRef := NameRef.nid (Identifier.id "add") in
    let locals : LocalScope := empty_local_scope in
    match scope_resolve_name add_ref scope locals {
        ok _ => true,
        err _ => false
    }

// --- Test: Build scope with a manually constructed inductive ---

#[test]
def test_scope_inductive_found : Bool :=
    let path : ModulePath := test_module_path in
    let color_path : ModulePath := name_to_path (Identifier.id "Color") in
    let red_con_name : ModulePath := name_to_path (Identifier.id "red") in
    let red_con : InductConstructor := InductConstructor.mk red_con_name empty_params Term.hole in
    let constructors : List InductConstructor := List.cons red_con empty_constructors in
    let ind : Inductive := Inductive.mk color_path empty_params (Term.type_ 1) constructors empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.inductive_d ind) empty_decls_list in
    let sd : ScopeData := build_scope_from_decls path decl_list in
    let scope : Scope := make_scope sd in
    match scope_find_inductive color_path scope {
        ok _ => true,
        err _ => false
    }

// --- Test: Constructor resolves as def ---

#[test]
def test_scope_constructor_resolves : Bool :=
    let path : ModulePath := test_module_path in
    let color_path : ModulePath := name_to_path (Identifier.id "Color") in
    let red_con_name : ModulePath := name_to_path (Identifier.id "red") in
    let red_con : InductConstructor := InductConstructor.mk red_con_name empty_params Term.hole in
    let constructors : List InductConstructor := List.cons red_con empty_constructors in
    let ind : Inductive := Inductive.mk color_path empty_params (Term.type_ 1) constructors empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.inductive_d ind) empty_decls_list in
    let sd : ScopeData := build_scope_from_decls path decl_list in
    let scope : Scope := make_scope sd in
    let red_ref : NameRef := NameRef.nid (Identifier.id "red") in
    let locals : LocalScope := empty_local_scope in
    match scope_resolve_name red_ref scope locals {
        ok _ => true,
        err _ => false
    }

// --- Test: Unknown name does not resolve ---

#[test]
def test_scope_unknown_name_fails : Bool :=
    let path : ModulePath := test_module_path in
    let sd : ScopeData := build_scope_from_decls path empty_decls_list in
    let scope : Scope := make_scope sd in
    let y_ref : NameRef := NameRef.nid (Identifier.id "y") in
    let locals : LocalScope := empty_local_scope in
    match scope_resolve_name y_ref scope locals {
        ok _ => false,
        err _ => true
    }

// --- Test: Builtins present (Type resolution) ---

#[test]
def test_builtin_type_resolves : Bool :=
    let path : ModulePath := test_module_path in
    let sd : ScopeData := build_scope_from_decls path empty_decls_list in
    let scope : Scope := make_scope sd in
    let type_name : ModulePath := name_to_path (Identifier.id "Type") in
    let result : Result ScopeError ScopeDef := resolve_def_in_scope_by_name type_name scope in
    match result {
        ok _ => true,
        err _ => false
    }
