use lang::types {
  Attribute, Decl, Def, Identifier, InductConstructor, Inductive,
  LocalScope, LocalVar, ModulePath, NamePath, NameRef, Param, Scope,
  ScopeData, ScopeDef, ScopeError, Term, TypeConstraint, hole, package_private,
  named, sentinel, sort_n, str,
}
use lib::module {def_body_diagnostics}
use lib::scope {
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
    ModulePath.mk empty_id_list

def make_scope (sd : ScopeData) : Scope :=
    let path : ModulePath := test_module_path in
    let empty_parent : Option Scope := Option.none in
    { module_id := path, scope := sd, parent := empty_parent, incomplete_match_ok := false }

/// A one-segment DECL name -- the shape `Def.name`, `Inductive.name`,
/// `InductConstructor.name` and the name arguments of
/// `scope_find_inductive`/`resolve_def_in_scope_by_name` all take.
def name_to_npath (i : Identifier) : NamePath :=
    let empty_id_list : List Identifier := List.empty in
    NamePath.mk (List.cons i empty_id_list)

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
    let defname : NamePath := name_to_npath (Identifier.id "add") in
    let def_decl : Def := Def.mk defname (sort_n 1) Term.hole empty_constraints empty_attrs Visibility.package_private List.empty in
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
    let color_path : NamePath := name_to_npath (Identifier.id "Color") in
    let red_con_name : NamePath := name_to_npath (Identifier.id "red") in
    let red_con : InductConstructor := InductConstructor.mk red_con_name empty_params Term.hole in
    let constructors : List InductConstructor := List.cons red_con empty_constructors in
    let ind : Inductive := Inductive.mk color_path empty_params (sort_n 1) constructors empty_attrs Visibility.package_private in
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
    let color_path : NamePath := name_to_npath (Identifier.id "Color") in
    let red_con_name : NamePath := name_to_npath (Identifier.id "red") in
    let red_con : InductConstructor := InductConstructor.mk red_con_name empty_params Term.hole in
    let constructors : List InductConstructor := List.cons red_con empty_constructors in
    let ind : Inductive := Inductive.mk color_path empty_params (sort_n 1) constructors empty_attrs Visibility.package_private in
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
    let type_name : NamePath := name_to_npath (Identifier.id "Type") in
    let result : Result ScopeError ScopeDef := resolve_def_in_scope_by_name type_name scope in
    match result {
        ok _ => true,
        err _ => false
    }

// --- Def-body signature enforcement (`def_body_diagnostics`) ---
//
// `check_def_with_scope` threaded a def's real declared type into
// `type_check` and then discarded the checked result, so the threading was
// vacuous for every body shape whose arm never compares against
// `expected_type` -- `def p : I64 := "hello"` checked cleanly. These pins
// drive the real rule (not a helper), because the WIRING is what regressed
// silently: replacing `body_signature_diagnostics`'s `unify` with
// `List.empty` turns the first pin below red and leaves the other four
// green, and dropping the hole guard separately turns the last one red.

/// A named type reference, the shape a declared signature's `I64` lowers to.
def type_ref (nm : String) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id nm))

def probe_def (typ : Term) (body : Term) : Def :=
    Def.mk (name_to_npath (Identifier.id "probe")) typ body empty_constraints empty_attrs
        Visibility.package_private List.empty

/// A body-less stub type, standing in for the `I64`/`String` the real
/// prelude supplies. It has to be here because the rule skips a body whose
/// type mentions a name NOTHING in scope binds (that is how an
/// uninstantiated cross-def type variable shows up), so without these the
/// fixture would look like the generic case and never compare anything.
def stub_type (nm : String) : Decl :=
    Decl.def_d (Def.mk (name_to_npath (Identifier.id nm)) (sort_n 1) Term.hole
        empty_constraints empty_attrs Visibility.package_private List.empty)

def probe_scope (typ : Term) (body : Term) : Scope :=
    let path : ModulePath := test_module_path in
    let decl_list : List Decl := [Decl.def_d (probe_def typ body), stub_type "I64", stub_type "String"] in
    make_scope (build_scope_from_decls path decl_list)

def probe_diagnostics (typ : Term) (body : Term) : List String :=
    def_body_diagnostics (probe_def typ body) (probe_scope typ body) empty_local_scope Option.none

def hello : Term := Term.lit (Literal.str "hello")

#[test]
def test_a_def_body_of_the_wrong_literal_type_is_rejected : Bool :=
    match probe_diagnostics (type_ref "I64") hello {
        List.empty => false,
        List.cons _ _ => true,
    }

#[test]
def test_a_def_body_of_the_right_literal_type_has_no_diagnostics : Bool :=
    match probe_diagnostics (type_ref "String") hello {
        List.empty => true,
        List.cons _ _ => false,
    }

/// A body-less (`Term.hole`) def is skipped outright -- the arm
/// `check_def_with_scope` had before this rule existed, and one a wrong
/// declared type must not turn into a false rejection.
#[test]
def test_a_hole_body_is_skipped_not_rejected : Bool :=
    match probe_diagnostics (type_ref "I64") Term.hole {
        List.empty => true,
        List.cons _ _ => false,
    }

/// The guard that keeps the rule from rejecting GENERIC defs: a side that
/// still mentions a type variable is not a fair comparison and is skipped.
/// `def empty_arities : HashMap String I64 := str_map_empty` is the real
/// shape -- its body's checked type is `HashMap String V`, with `V` bound
/// by nothing in scope.
#[test]
def test_a_type_mentioning_an_unbound_typevar_is_not_rejected : Bool :=
    match probe_diagnostics (type_ref "V") hello {
        List.empty => true,
        List.cons _ _ => false,
    }

// The hole guard (`body_has_hole`) is deliberately NOT pinned here. It
// cannot be reproduced by a hand-built fixture: an app whose argument is a
// hole infers a HOLE against a hand-registered signature just as it does
// against `build_scope_from_decls`'s `Term.hole` signature, and `unify`
// accepts a hole -- so every fixture tried passed with the guard removed
// (measured, twice: with the signature absent AND with it registered via
// `scope_data_add_def_sig`). Its control is the real pipeline instead:
// `def p1 : T -> T := apply (fn x => x) _` checks clean on the final build
// and is REJECTED ("expected (T -> T), found T") by a build with the guard
// removed.
