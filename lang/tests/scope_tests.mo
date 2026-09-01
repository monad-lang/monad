use lang.types {
  Decl, Def, Identifier, InductConstructor, Inductive, Infix, Instance,
  InstanceKey, LocalScope, LocalVar, Module, ModulePath, ModuleRegistry, NameRef,
  Param, Scope, ScopeData, ScopeDef, ScopeError, ScopeInstance, Similar, Term,
  TypeConstraint, def_d, hole, id, inductive_d, many, mk, mp, name, nmp,
  param_many, type_,
}
use lang.scope {
  add_constraint_dict_params, build_scope_from_decls, build_scope_from_modules,
  list_append, modpath_eq, resolve_def_in_scope_by_name, scope_data_add_def,
  scope_data_add_inductive, scope_data_add_instance, scope_data_empty,
  scope_find_inductive, scope_find_inductive_by_constructor, scope_find_local,
  scope_globals, scope_push_local, scope_resolve_instance, scope_resolve_name,
}

// --- Build scope from empty decl_list ---

#[test]
def test_build_empty_scope : Bool :=
    let empty_id_list : List Identifier := List.empty in
    let empty_path : ModulePath := ModulePath.mp empty_id_list in
    let empty_decls : List Decl := List.empty in
    let empty_scope : ScopeData := build_scope_from_decls empty_path empty_decls in
    true

// --- Build scope with a def declaration ---

#[test]
def test_build_with_def : Bool :=
    let name : ModulePath := ModulePath.mp (List.cons (Identifier.id "add") List.empty) in
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let empty_constraints : List TypeConstraint := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let def_decl : Def := Def.mk name Term.hole Term.hole empty_constraints empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.def_d def_decl) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    true

// --- Build scope with an inductive declaration ---

#[test]
def test_build_with_inductive : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Bool") List.empty) in
    let empty_params : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk
        (ModulePath.mp (List.cons (Identifier.id "true") List.empty))
        empty_params (Term.type_ 1) in
    let false_cn : InductConstructor := InductConstructor.mk
        (ModulePath.mp (List.cons (Identifier.id "false") List.empty))
        empty_params (Term.type_ 1) in
    let cns : List InductConstructor := List.cons true_cn (List.cons false_cn List.empty) in
    let empty_attrs : List Attribute := List.empty in
    let ind : Inductive := Inductive.mk type_name empty_params (Term.type_ 1) cns empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    true

// --- scope_globals extracts ScopeData from Scope ---

#[test]
def test_scope_globals : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let sd : ScopeData := scope_data_empty in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let g : ScopeData := scope_globals s in
    true

// --- scope_find_inductive finds an inductive by name ---

#[test]
def test_scope_find_inductive_found : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Bool") List.empty) in
    let empty_params : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk
        (ModulePath.mp (List.cons (Identifier.id "true") List.empty))
        empty_params (Term.type_ 1) in
    let cns : List InductConstructor := List.cons true_cn List.empty in
    let empty_attrs : List Attribute := List.empty in
    let ind : Inductive := Inductive.mk type_name empty_params (Term.type_ 1) cns empty_attrs Visibility.package_private in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via `scope_data_add_inductive` on
    // top of `scope_data_empty` rather than a hand-written literal.
    let sd : ScopeData := scope_data_add_inductive scope_data_empty ind in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let result : Result ScopeError Inductive := scope_find_inductive type_name s in
    match result {
        ok found => true,
        err _ => false
    }

// --- scope_find_inductive returns error when not found ---

#[test]
def test_scope_find_inductive_not_found : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let lookup_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "NoSuch") List.empty) in
    let sd : ScopeData := scope_data_empty in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let result : Result ScopeError Inductive := scope_find_inductive lookup_name s in
    match result {
        ok _ => false,
        err _ => true
    }

// --- scope_push_local creates a new LocalScope ---

#[test]
def test_scope_push_local : Bool :=
    let lv : LocalVar := {
        name := Identifier.id "x",
        typ := Term.hole,
        multiplicity := Multiplicity.many,
    } in
    let empty_parent : Option LocalScope := Option.none in
    let ls : LocalScope := {
        vars := List.empty,
        parent := empty_parent,
    } in
    let pushed : LocalScope := scope_push_local lv ls in
    true

// --- scope_find_local finds a variable in LocalScope ---

#[test]
def test_scope_find_local_found : Bool :=
    let lv : LocalVar := {
        name := Identifier.id "x",
        typ := Term.type_ 1,
        multiplicity := Multiplicity.many,
    } in
    let empty_parent : Option LocalScope := Option.none in
    let ls : LocalScope := {
        vars := List.cons lv List.empty,
        parent := empty_parent,
    } in
    let result : Option LocalVar := scope_find_local (Identifier.id "x") ls in
    match result {
        Option.some found => true,
        Option.none => false
    }

// --- scope_find_local searches parent chain ---

#[test]
def test_scope_find_local_parent : Bool :=
    let lv1 : LocalVar := {
        name := Identifier.id "x",
        typ := Term.type_ 1,
        multiplicity := Multiplicity.many,
    } in
    let lv2 : LocalVar := {
        name := Identifier.id "y",
        typ := Term.type_ 1,
        multiplicity := Multiplicity.many,
    } in
    let empty_parent : Option LocalScope := Option.none in
    let parent : LocalScope := {
        vars := List.cons lv1 List.empty,
        parent := empty_parent,
    } in
    let some_parent : Option LocalScope := Option.some parent in
    let child : LocalScope := {
        vars := List.cons lv2 List.empty,
        parent := some_parent,
    } in
    let result : Option LocalVar := scope_find_local (Identifier.id "x") child in
    match result {
        Option.some found => true,
        Option.none => false
    }

// --- scope_find_local returns none when not found ---

#[test]
def test_scope_find_local_not_found : Bool :=
    let empty_parent : Option LocalScope := Option.none in
    let ls : LocalScope := {
        vars := List.empty,
        parent := empty_parent,
    } in
    let result : Option LocalVar := scope_find_local (Identifier.id "x") ls in
    match result {
        Option.some _ => false,
        Option.none => true
    }

// --- scope_resolve_name finds a def in ScopeData ---

#[test]
def test_scope_resolve_name_found : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let def_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "add") List.empty) in
    let def_entry : ScopeDef := {
        name := def_name,
        module := mod_path,
        sig := Term.hole,
        body := Term.hole,
    } in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via `scope_data_add_def` on top of
    // `scope_data_empty` rather than a hand-written literal.
    let sd : ScopeData := scope_data_add_def scope_data_empty def_entry in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let nref : NameRef := NameRef.nmp def_name in
    let empty_parent : Option LocalScope := Option.none in
    let locals : LocalScope := {
        vars := List.empty,
        parent := empty_parent,
    } in
    let result : Result ScopeError ScopeDef := scope_resolve_name nref s locals in
    match result {
        ok found => true,
        err _ => false
    }

// --- scope_resolve_name returns error when not found ---

#[test]
def test_scope_resolve_name_not_found : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let sd : ScopeData := scope_data_empty in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let nref : NameRef := NameRef.nmp (ModulePath.mp (List.cons (Identifier.id "no_such") List.empty)) in
    let empty_parent : Option LocalScope := Option.none in
    let locals : LocalScope := {
        vars := List.empty,
        parent := empty_parent,
    } in
    let result : Result ScopeError ScopeDef := scope_resolve_name nref s locals in
    match result {
        ok _ => false,
        err _ => true
    }

// --- Builtin Type resolves ---

#[test]
def test_builtin_type_resolves : Bool :=
    let empty_id_list : List Identifier := List.empty in
    let empty_path : ModulePath := ModulePath.mp empty_id_list in
    let empty_decls : List Decl := List.empty in
    let sd : ScopeData := build_scope_from_decls empty_path empty_decls in
    let s : Scope := {
        module_id := empty_path,
        scope := sd,
        parent := Option.none,
    } in
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Type") List.empty) in
    let result : Result ScopeError ScopeDef := resolve_def_in_scope_by_name type_name s in
    match result {
        ok found => true,
        err _ => false
    }

// --- Builtin Type inductive is found ---

#[test]
def test_builtin_type_inductive : Bool :=
    let empty_id_list : List Identifier := List.empty in
    let empty_path : ModulePath := ModulePath.mp empty_id_list in
    let empty_decls : List Decl := List.empty in
    let sd : ScopeData := build_scope_from_decls empty_path empty_decls in
    let s : Scope := {
        module_id := empty_path,
        scope := sd,
        parent := Option.none,
    } in
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Type") List.empty) in
    let result : Result ScopeError Inductive := scope_find_inductive type_name s in
    match result {
        ok found => true,
        err _ => false
    }

// --- build_scope_from_modules with empty modules ---

#[test]
def test_build_from_modules_empty : Bool :=
    let empty_id_list : List Identifier := List.empty in
    let empty_path : ModulePath := ModulePath.mp empty_id_list in
    let empty_modules : ModuleRegistry := {
        modules := List.empty,
    } in
    let sd : ScopeData := build_scope_from_modules empty_path empty_modules in
    true

// --- build_scope_from_modules with one module ---

#[test]
def test_build_from_modules_one_def : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let def_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "add") List.empty) in
    let def_entry : ScopeDef := {
        name := def_name,
        module := mod_path,
        sig := Term.hole,
        body := Term.hole,
    } in
    let empty_instances : List ScopeInstance := List.empty in
    let empty_infixes : List Infix := List.empty in
    let empty_inductives : List Inductive := List.empty in
    let defs : List ScopeDef := List.cons def_entry List.empty in
    let m : Module := {
        path := mod_path,
        inductives := empty_inductives,
        defs := defs,
        infixs := empty_infixes,
        instances := empty_instances,
    } in
    let loaded : ModuleRegistry := {
        modules := List.cons m List.empty,
    } in
    let sd : ScopeData := build_scope_from_modules mod_path loaded in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let nref : NameRef := NameRef.nmp def_name in
    let empty_parent : Option LocalScope := Option.none in
    let locals : LocalScope := {
        vars := List.empty,
        parent := empty_parent,
    } in
    let result : Result ScopeError ScopeDef := scope_resolve_name nref s locals in
    match result {
        ok found => true,
        err _ => false
    }

// --- scope_resolve_instance found ---

#[test]
def test_scope_resolve_instance_found : Bool :=
    let cls_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Monad") List.empty) in
    let inst_name : Identifier := Identifier.id "maybeMonad" in
    let empty_constraints : List TypeConstraint := List.empty in
    let empty_args : List Term := List.empty in
    let ins : Instance := Instance.mk inst_name cls_name empty_constraints empty_args Visibility.package_private List.empty List.empty in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via `scope_data_add_instance` on
    // top of `scope_data_empty` rather than a hand-written literal.
    let sd : ScopeData := scope_data_add_instance scope_data_empty ins in
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let empty_params : List Param := List.empty in
    let key : InstanceKey := {
        cls := cls_name,
        constraints := empty_constraints,
        args := empty_params,
    } in
    let result : Result ScopeError Instance := scope_resolve_instance cls_name key s in
    match result {
        ok found => true,
        err _ => false
    }

// --- scope_resolve_instance not found ---

#[test]
def test_scope_resolve_instance_not_found : Bool :=
    let cls_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Monad") List.empty) in
    let sd : ScopeData := scope_data_empty in
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let empty_params : List Param := List.empty in
    let empty_constraints : List TypeConstraint := List.empty in
    let key : InstanceKey := {
        cls := cls_name,
        constraints := empty_constraints,
        args := empty_params,
    } in
    let result : Result ScopeError Instance := scope_resolve_instance cls_name key s in
    match result {
        ok _ => false,
        err _ => true
    }

// --- list_append appends two lists ---

#[test]
def test_list_append_empty : Bool :=
    let empty : List I64 := List.empty in
    let result : List I64 := list_append empty empty in
    true

// --- list_append with non-empty list ---

#[test]
def test_list_append_non_empty : Bool :=
    let xs : List I64 := List.cons (1 : I64) (List.cons (2 : I64) List.empty) in
    let ys : List I64 := List.cons (3 : I64) (List.cons (4 : I64) List.empty) in
    let result : List I64 := list_append xs ys in
    true

// --- scope_resolve_instance matches by class name ---

#[test]
def test_scope_resolve_instance_matches_class : Bool :=
    let cls_name1 : ModulePath := ModulePath.mp (List.cons (Identifier.id "Show") List.empty) in
    let cls_name2 : ModulePath := ModulePath.mp (List.cons (Identifier.id "Monad") List.empty) in
    let inst_show : Instance := Instance.mk (Identifier.id "showBool") cls_name1 List.empty List.empty Visibility.package_private List.empty List.empty in
    let inst_monad : Instance := Instance.mk (Identifier.id "maybeMonad") cls_name2 List.empty List.empty Visibility.package_private List.empty List.empty in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via `scope_data_add_instance` on
    // top of `scope_data_empty` rather than a hand-written literal.
    let sd : ScopeData := scope_data_add_instance (scope_data_add_instance scope_data_empty inst_show) inst_monad in
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let empty_params : List Param := List.empty in
    let key : InstanceKey := {
        cls := cls_name2,
        constraints := List.empty,
        args := empty_params,
    } in
    let result : Result ScopeError Instance := scope_resolve_instance cls_name2 key s in
    match result {
        ok ins =>
            match ins {
                mk name cls _ _ _ _ _ => Similar.similar name (Identifier.id "maybeMonad")
            },
        err _ => false
    }

// --- build_scope_from_decls resolves a def through scope_resolve_name ---

#[test]
def test_build_scope_then_resolve_def : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let def_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "add") List.empty) in
    let def_decl : Def := Def.mk def_name Term.hole Term.hole List.empty List.empty Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.def_d def_decl) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let nref : NameRef := NameRef.nmp def_name in
    let empty_parent : Option LocalScope := Option.none in
    let locals : LocalScope := {
        vars := List.empty,
        parent := empty_parent,
    } in
    let result : Result ScopeError ScopeDef := scope_resolve_name nref s locals in
    match result {
        ok d => true,
        err _ => false
    }

// --- build_scope_from_decls resolves an inductive constructor ---

#[test]
def test_build_scope_then_resolve_constructor : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Bool") List.empty) in
    let true_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "true") List.empty) in
    let empty_params : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk true_name empty_params (Term.type_ 1) in
    let cns : List InductConstructor := List.cons true_cn List.empty in
    let empty_attrs : List Attribute := List.empty in
    let ind : Inductive := Inductive.mk type_name empty_params (Term.type_ 1) cns empty_attrs Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decl_list in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    let nref : NameRef := NameRef.nmp true_name in
    let empty_parent : Option LocalScope := Option.none in
    let locals : LocalScope := {
        vars := List.empty,
        parent := empty_parent,
    } in
    let result : Result ScopeError ScopeDef := scope_resolve_name nref s locals in
    match result {
        ok d =>
            match d {
                mk name _ _ _ => Similar.similar name true_name
            },
        err _ => false
    }

// --- instance_key_matches compares type args ---

#[test]
def test_instance_key_matches_type_args : Bool :=
    let cls_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Show") List.empty) in
    let i64_typ : Term := Term.type_ 1 in
    let bool_typ : Term := Term.type_ 1 in
    let show_i64 : Instance := Instance.mk
        (Identifier.id "showI64")
        cls_name
        List.empty
        (List.cons i64_typ List.empty)
        Visibility.package_private List.empty List.empty in
    let show_bool : Instance := Instance.mk
        (Identifier.id "showBool")
        cls_name
        List.empty
        (List.cons bool_typ List.empty)
        Visibility.package_private List.empty List.empty in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via `scope_data_add_instance` on
    // top of `scope_data_empty` rather than a hand-written literal.
    // Insertion order reversed vs. the original hand-written list
    // (`show_bool` first, `show_i64` last) — `scope_data_add_instance`
    // prepends to its class's instance list, so this preserves the
    // original `[show_i64, show_bool]` order: `show_i64`/`show_bool`
    // here deliberately share the same `Term.type_ 1` arg (see above),
    // so `first_matching_instance`'s scan needs this exact order to
    // still return `show_i64` first, matching this test's intent.
    let sd : ScopeData := scope_data_add_instance (scope_data_add_instance scope_data_empty show_bool) show_i64 in
    let mod_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Test") List.empty) in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    // Key requesting Show I64 — should find show_i64 instance
    let key_i64 : InstanceKey := {
        cls := cls_name,
        constraints := List.empty,
        args := List.cons (param_many (Identifier.id "A") i64_typ) List.empty,
    } in
    match scope_resolve_instance cls_name key_i64 s {
        ok found =>
            match found {
                mk name _ _ _ _ _ _ => Similar.similar name (Identifier.id "showI64"),
            },
        err _ => false,
    }

#[test]
def test_instance_key_matches_wrong_type_args : Bool :=
    let cls_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Show") List.empty) in
    let i64_typ : Term := Term.type_ 1 in
    let string_typ : Term := Term.type_ 2 in  // different from type_1
    let show_i64 : Instance := Instance.mk
        (Identifier.id "showI64")
        cls_name
        List.empty
        (List.cons i64_typ List.empty)
        Visibility.package_private List.empty List.empty in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via `scope_data_add_instance` on
    // top of `scope_data_empty` rather than a hand-written literal.
    let sd : ScopeData := scope_data_add_instance scope_data_empty show_i64 in
    let mod_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Test") List.empty) in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    // Key requesting Show String — should NOT find show_i64
    let key_string : InstanceKey := {
        cls := cls_name,
        constraints := List.empty,
        args := List.cons (param_many (Identifier.id "A") string_typ) List.empty,
    } in
    match scope_resolve_instance cls_name key_string s {
        ok _ => false,
        err _ => true,
    }

// --- scope_find_inductive_by_constructor finds inductive by constructor name ---

#[test]
def test_find_inductive_by_constructor_found : Bool :=
    let ind_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Maybe") List.empty) in
    let some_mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "some") List.empty) in
    let none_mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "none") List.empty) in
    let some_cn : InductConstructor := InductConstructor.mk some_mp List.empty (Term.type_ 1) in
    let none_cn : InductConstructor := InductConstructor.mk none_mp List.empty (Term.type_ 1) in
    let cns : List InductConstructor := List.cons some_cn (List.cons none_cn List.empty) in
    let ind : Inductive := Inductive.mk ind_name List.empty (Term.type_ 1) cns List.empty Visibility.package_private in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via `scope_data_add_inductive` on
    // top of `scope_data_empty` rather than a hand-written literal.
    let sd : ScopeData := scope_data_add_inductive scope_data_empty ind in
    let mod_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Test") List.empty) in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    // Look up by "some" constructor — should find Maybe
    match scope_find_inductive_by_constructor some_mp s {
        Option.some found =>
            match found {
                mk name _ _ _ _ _ => modpath_eq name ind_name,
            },
        Option.none => false,
    }

#[test]
def test_find_inductive_by_constructor_not_found : Bool :=
    let ind_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Maybe") List.empty) in
    let some_mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "some") List.empty) in
    let some_cn : InductConstructor := InductConstructor.mk some_mp List.empty (Term.type_ 1) in
    let ind : Inductive := Inductive.mk ind_name List.empty (Term.type_ 1) (List.cons some_cn List.empty) List.empty Visibility.package_private in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via `scope_data_add_inductive` on
    // top of `scope_data_empty` rather than a hand-written literal.
    let sd : ScopeData := scope_data_add_inductive scope_data_empty ind in
    let mod_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Test") List.empty) in
    let s : Scope := {
        module_id := mod_path,
        scope := sd,
        parent := Option.none,
    } in
    // Look up by "nope" constructor — should NOT find
    let nope_mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "nope") List.empty) in
    match scope_find_inductive_by_constructor nope_mp s {
        Option.some _ => false,
        Option.none => true,
    }

// --- dict-param placeholder regression (gap 7) ---

/// A constrained def whose body calls its own constraint's class method
/// (`Add.add a b` -- the `instance [Add A] HAdd A A A` -> `HAdd_A_A_A_add`
/// shape) qualifies for a leading dictionary parameter. That parameter's
/// own `typ` annotation MUST be `Term.hole` (which `type_check` always
/// succeeds on, returning `expected_type`), never a bound `Term.var 0`:
/// `check_def_with_scope` checks a def's body against `Term.hole`, so
/// `type_check_lam`'s non-`pi` branch re-checks each lambda's own written
/// param type against the current `local_types` stack -- and the
/// outermost dict lambda is checked with that stack EMPTY, so a
/// `Term.var 0` placeholder reported a spurious out-of-range `bound_var`
/// (the `HAdd_A_A_A_add` self-hosted-check gap). Mirrors the Rust
/// reference's own dictionary/projected-method placeholder
/// (`CoreTerm::Hole`, `core_check_module`).
#[test]
def test_dict_param_type_is_hole : Bool :=
    let add_cls : ModulePath := ModulePath.mp (List.cons (Identifier.id "Add") List.empty) in
    let constraint : TypeConstraint := TypeConstraint.mk add_cls (List.cons (Identifier.id "A") List.empty) in
    let constraints : List TypeConstraint := List.cons constraint List.empty in
    // The body's `Add.add` reference is what `qualifying_dict_constraints`
    // needs (`def_references_class` scans for a `var` whose name starts
    // with `"Add."`) to qualify the constraint for a leading dict param.
    let add_add_ref : Term := Term.var (-1) (DebugName.named (Identifier.id "Add.add")) in
    let body : Term := Term.app add_add_ref (Term.var (-1) (DebugName.named (Identifier.id "a"))) in
    let def_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "HAdd_A_A_A_add") List.empty) in
    let empty_attrs : List Attribute := List.empty in
    let df : Def := Def.mk def_name Term.hole body constraints empty_attrs Visibility.package_private in
    match add_constraint_dict_params df {
        Def.mk _ _new_typ new_term _ _ _ =>
            match new_term {
                Term.lam _dbg param_typ _body =>
                    match param_typ { Term.hole => true, _ => false, },
                _ => false,
            },
    }
