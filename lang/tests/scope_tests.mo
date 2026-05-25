use lang.types
open types
use lang.scope
open scope

// --- Build scope from empty decls ---

@[test]
def test_build_empty_scope : Bool :=
    let empty_id_list : List Identifier := List.empty in
    let empty_path : ModulePath := ModulePath.mp empty_id_list in
    let empty_decls : List Decl := List.empty in
    let empty_scope : ScopeData := build_scope_from_decls empty_path empty_decls in
    true

// --- Build scope with a def declaration ---

@[test]
def test_build_with_def : Bool :=
    let name : ModulePath := ModulePath.mp (List.cons (Identifier.id "add") List.empty) in
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let empty_constraints : List TypeConstraint := List.empty in
    let empty_attrs : List String := List.empty in
    let def_decl : Def := Def.mk name Term.hole Term.hole empty_constraints empty_attrs in
    let decls : List Decl := List.cons (Decl.def_d def_decl) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decls in
    true

// --- Build scope with an inductive declaration ---

@[test]
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
    let empty_attrs : List String := List.empty in
    let ind : Inductive := Inductive.mk type_name empty_params (Term.type_ 1) cns empty_attrs in
    let decls : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decls in
    true

// --- scope_globals extracts ScopeData from Scope ---

@[test]
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

@[test]
def test_scope_find_inductive_found : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Bool") List.empty) in
    let empty_params : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk
        (ModulePath.mp (List.cons (Identifier.id "true") List.empty))
        empty_params (Term.type_ 1) in
    let cns : List InductConstructor := List.cons true_cn List.empty in
    let empty_attrs : List String := List.empty in
    let ind : Inductive := Inductive.mk type_name empty_params (Term.type_ 1) cns empty_attrs in
    let sd : ScopeData := {
        def_refs := List.empty,
        class_defs := List.empty,
        instances := List.empty,
        inductives := List.cons ind List.empty,
        classes := List.empty,
        infixes := List.empty,
        conflicts := List.empty,
    } in
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

@[test]
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

@[test]
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

@[test]
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

@[test]
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

@[test]
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

@[test]
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
    let sd : ScopeData := {
        def_refs := List.cons def_entry List.empty,
        class_defs := List.empty,
        instances := List.empty,
        inductives := List.empty,
        classes := List.empty,
        infixes := List.empty,
        conflicts := List.empty,
    } in
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

@[test]
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

@[test]
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

@[test]
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

@[test]
def test_build_from_modules_empty : Bool :=
    let empty_id_list : List Identifier := List.empty in
    let empty_path : ModulePath := ModulePath.mp empty_id_list in
    let empty_modules : LoadedModules := {
        modules := List.empty,
    } in
    let sd : ScopeData := build_scope_from_modules empty_path empty_modules in
    true

// --- build_scope_from_modules with one module ---

@[test]
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
    let loaded : LoadedModules := {
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

@[test]
def test_scope_resolve_instance_found : Bool :=
    let cls_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Monad") List.empty) in
    let inst_name : Identifier := Identifier.id "maybeMonad" in
    let empty_constraints : List TypeConstraint := List.empty in
    let empty_args : List Term := List.empty in
    let ins : Instance := Instance.mk inst_name cls_name empty_constraints empty_args in
    let si : ScopeInstance := {
        class_name := cls_name,
        instances := List.cons ins List.empty,
    } in
    let sd : ScopeData := {
        def_refs := List.empty,
        class_defs := List.empty,
        instances := List.cons si List.empty,
        inductives := List.empty,
        classes := List.empty,
        infixes := List.empty,
        conflicts := List.empty,
    } in
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

@[test]
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

@[test]
def test_list_append_empty : Bool :=
    let empty : List I64 := List.empty in
    let result : List I64 := list_append empty empty in
    true

// --- list_append with non-empty list ---

@[test]
def test_list_append_non_empty : Bool :=
    let xs : List I64 := List.cons (1 : I64) (List.cons (2 : I64) List.empty) in
    let ys : List I64 := List.cons (3 : I64) (List.cons (4 : I64) List.empty) in
    let result : List I64 := list_append xs ys in
    true

// --- scope_resolve_instance matches by class name ---

@[test]
def test_scope_resolve_instance_matches_class : Bool :=
    let cls_name1 : ModulePath := ModulePath.mp (List.cons (Identifier.id "Show") List.empty) in
    let cls_name2 : ModulePath := ModulePath.mp (List.cons (Identifier.id "Monad") List.empty) in
    let inst_show : Instance := Instance.mk (Identifier.id "showBool") cls_name1 List.empty List.empty in
    let inst_monad : Instance := Instance.mk (Identifier.id "maybeMonad") cls_name2 List.empty List.empty in
    let si1 : ScopeInstance := {
        class_name := cls_name1,
        instances := List.cons inst_show List.empty,
    } in
    let si2 : ScopeInstance := {
        class_name := cls_name2,
        instances := List.cons inst_monad List.empty,
    } in
    let sd : ScopeData := {
        def_refs := List.empty,
        class_defs := List.empty,
        instances := List.cons si1 (List.cons si2 List.empty),
        inductives := List.empty,
        classes := List.empty,
        infixes := List.empty,
        conflicts := List.empty,
    } in
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
                mk name cls _ _ => Similar.similar name (Identifier.id "maybeMonad")
            },
        err _ => false
    }

// --- build_scope_from_decls resolves a def through scope_resolve_name ---

@[test]
def test_build_scope_then_resolve_def : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let def_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "add") List.empty) in
    let def_decl : Def := Def.mk def_name Term.hole Term.hole List.empty List.empty in
    let decls : List Decl := List.cons (Decl.def_d def_decl) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decls in
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

@[test]
def test_build_scope_then_resolve_constructor : Bool :=
    let mod_id : Identifier := Identifier.id "Test" in
    let mod_path : ModulePath := ModulePath.mp (List.cons mod_id List.empty) in
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Bool") List.empty) in
    let true_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "true") List.empty) in
    let empty_params : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk true_name empty_params (Term.type_ 1) in
    let cns : List InductConstructor := List.cons true_cn List.empty in
    let empty_attrs : List String := List.empty in
    let ind : Inductive := Inductive.mk type_name empty_params (Term.type_ 1) cns empty_attrs in
    let decls : List Decl := List.cons (Decl.inductive_d ind) List.empty in
    let sd : ScopeData := build_scope_from_decls mod_path decls in
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
