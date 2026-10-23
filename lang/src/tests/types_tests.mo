use lang::types {
  Attribute, CubicalPrim, Identifier, InductConstructor, Inductive, Infix,
  InstanceKey, LocalVar, Module, ModulePath, ModuleRegistry, Multiplicity,
  NamePath, Operator, Param, Scope, ScopeClassDef, ScopeConflict, ScopeData,
  ScopeDef, ScopeError, ScopeInstance, Similar, Term, cub_i0, cub_i1, cub_imeet,
  cub_ineg, cub_interval, cubical_arity, cubical_is_endpoint, cubical_prim_eq,
  cubical_prim_of, nid, nnp, nop, package_private, sort_n, visibility_beq,
  Location,
}
use lib::scope {scope_data_add_def, scope_data_add_inductive, scope_data_empty}

// --- Similar instances for scope types ---

pub instance Similar Infix {
    def similar (a : Infix) (b : Infix) : Bool :=
        match a {
            mk op1 nm1 => match b {
                mk op2 nm2 => Similar.similar op1 op2 && Similar.similar nm1 nm2
            }
        }
}

pub instance Similar InstanceKey {
    def similar (a : InstanceKey) (b : InstanceKey) : Bool :=
        match a {
            mk cls1 cons1 args1 => match b {
                mk cls2 cons2 args2 =>
                    Similar.similar cls1 cls2
            }
        }
}

pub instance Similar ScopeDef {
    def similar (a : ScopeDef) (b : ScopeDef) : Bool :=
        match a {
            mk nm1 mod1 sig1 body1 vis1 => match b {
                mk nm2 mod2 sig2 body2 vis2 =>
                    Similar.similar nm1 nm2 && Similar.similar mod1 mod2
                    && Similar.similar sig1 sig2 && Similar.similar body1 body2
                    && visibility_beq vis1 vis2
            }
        }
}

pub instance Similar ScopeClassDef {
    def similar (a : ScopeClassDef) (b : ScopeClassDef) : Bool :=
        match a {
            mk cls1 fn1 id1 sig1 => match b {
                mk cls2 fn2 id2 sig2 =>
                    Similar.similar cls1 cls2 && Similar.similar fn1 fn2
                    && Similar.similar id1 id2 && Similar.similar sig1 sig2
            }
        }
}

pub instance Similar ScopeInstance {
    def similar (a : ScopeInstance) (b : ScopeInstance) : Bool :=
        match a {
            mk cn1 ins1 => match b {
                mk cn2 ins2 => Similar.similar cn1 cn2
            }
        }
}

pub instance Similar ScopeConflict {
    def similar (a : ScopeConflict) (b : ScopeConflict) : Bool :=
        match a {
            mk nm1 cands1 => match b {
                mk nm2 cands2 => Similar.similar nm1 nm2
            }
        }
}

pub instance Similar LocalVar {
    def similar (a : LocalVar) (b : LocalVar) : Bool :=
        match a {
            mk nm1 typ1 mult1 => match b {
                mk nm2 typ2 mult2 =>
                    Similar.similar nm1 nm2 && Similar.similar typ1 typ2
                    && Similar.similar mult1 mult2
            }
        }
}

pub instance Similar Module {
    def similar (a : Module) (b : Module) : Bool :=
        match a {
            mk p1 ind1 defs1 infs1 ins1 => match b {
                mk p2 ind2 defs2 infs2 ins2 => Similar.similar p1 p2
            }
        }
}

pub instance Similar ModuleRegistry {
    def similar (a : ModuleRegistry) (b : ModuleRegistry) : Bool :=
        match a {
            mk mods1 => match b {
                mk mods2 => true
            }
        }
}

// --- Scope type construction tests ---

#[test]
def test_infix_construct : Bool :=
    let expected_op : Operator := Operator.mk "+" in
    let expected_name : NamePath := NamePath.mk (List.cons (Identifier.id "add") List.empty) in
    let inf : Infix := {
        operator := expected_op,
        name := expected_name,
    } in
    match inf {
        mk op nm => Similar.similar op expected_op && Similar.similar nm expected_name
    }

#[test]
def test_instance_key_construct : Bool :=
    let expected_cls : NamePath := NamePath.mk (List.cons (Identifier.id "Show") List.empty) in
    let key : InstanceKey := {
        cls := expected_cls,
        constraints := List.empty,
        args := List.empty,
    } in
    match key {
        mk cls cons args => Similar.similar cls expected_cls
    }

#[test]
def test_scope_def_construct : Bool :=
    let expected_name : NamePath := NamePath.mk (List.cons (Identifier.id "add") List.empty) in
    let expected_module : ModulePath := ModulePath.mk (List.cons (Identifier.id "Prelude") List.empty) in
    let sd : ScopeDef := {
        name := expected_name,
        module := expected_module,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.package_private,
    } in
    match sd {
        mk nm modl sig body vis => Similar.similar nm expected_name && Similar.similar modl expected_module
    }

#[test]
def test_scope_class_def_construct : Bool :=
    let expected_full_name : NamePath := NamePath.mk (List.cons (Identifier.id "Eq") List.empty) in
    let expected_id : Identifier := Identifier.id "beq" in
    let expected_class : NamePath := NamePath.mk (List.cons (Identifier.id "BEq") List.empty) in
    let d : ScopeClassDef := {
        class_name := expected_class,
        full_name := expected_full_name,
        name := expected_id,
        sig := Term.hole,
    } in
    match d {
        mk _cls_name fnm id sig => Similar.similar fnm expected_full_name && Similar.similar id expected_id
    }

#[test]
def test_scope_instance_construct : Bool :=
    let expected_cn : NamePath := NamePath.mk (List.cons (Identifier.id "Show") List.empty) in
    let si : ScopeInstance := {
        class_name := expected_cn,
        instances := List.empty,
    } in
    match si {
        mk cn ins => Similar.similar cn expected_cn
    }

#[test]
def test_scope_conflict_construct : Bool :=
    let expected_name : NamePath := NamePath.mk (List.cons (Identifier.id "foo") List.empty) in
    let sc : ScopeConflict := {
        name := expected_name,
        candidates := List.empty,
    } in
    match sc {
        mk nm cands => Similar.similar nm expected_name
    }

#[test]
def test_local_var_construct : Bool :=
    let expected_id : Identifier := Identifier.id "x" in
    let expected_type : Term := Term.hole in
    let expected_mult : Multiplicity := Multiplicity.many in
    let lv : LocalVar := {
        name := expected_id,
        typ := expected_type,
        multiplicity := expected_mult,
    } in
    match lv {
        mk nm typ mult => Similar.similar nm expected_id
    }

#[test]
def test_scope_data_construct : Bool :=
    let tcon : Identifier := Identifier.id "Bool" in
    let tdef_mp : NamePath := NamePath.mk (List.cons tcon List.empty) in
    let none_term : Option Term := Option.none in
    let dummy_params : List Param := List.cons (Param.mk tcon Term.hole Multiplicity.many none_term List.empty) List.empty in
    let empty_param_list : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk (NamePath.mk [Identifier.id "true"]) empty_param_list (sort_n 1) in
    let false_cn : InductConstructor := InductConstructor.mk (NamePath.mk [Identifier.id "false"]) empty_param_list (sort_n 1) in
    let dummy_constructors : List InductConstructor := List.cons true_cn (List.cons false_cn List.empty) in
    let dummy_attrs : List Attribute := List.empty in
    let dummy_type : Inductive := Inductive.mk tdef_mp dummy_params (sort_n 1) dummy_constructors dummy_attrs Visibility.package_private in
    let expected_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Prelude") List.empty) in
    let dummy_module : ModulePath := ModulePath.mk (List.cons (Identifier.id "Prelude") List.empty) in
    let tdef_def : ScopeDef := {
        name := tdef_mp,
        module := dummy_module,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.package_private,
    } in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via scope_data_add_def/
    // scope_data_add_inductive on top of scope_data_empty rather than a
    // hand-written literal.
    let sd : ScopeData := scope_data_add_inductive (scope_data_add_def scope_data_empty tdef_def) dummy_type in
    match sd {
        { .. } => true
    }

#[test]
def test_scope_construct : Bool :=
    let expected_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Prelude") List.empty) in
    let tcon : Identifier := Identifier.id "Bool" in
    let tdef_mp : NamePath := NamePath.mk (List.cons tcon List.empty) in
    let none_term : Option Term := Option.none in
    let dummy_params : List Param := List.cons (Param.mk tcon Term.hole Multiplicity.many none_term List.empty) List.empty in
    let empty_param_list : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk (NamePath.mk [Identifier.id "true"]) empty_param_list (sort_n 1) in
    let false_cn : InductConstructor := InductConstructor.mk (NamePath.mk [Identifier.id "false"]) empty_param_list (sort_n 1) in
    let dummy_constructors : List InductConstructor := List.cons true_cn (List.cons false_cn List.empty) in
    let dummy_attrs : List Attribute := List.empty in
    let dummy_type : Inductive := Inductive.mk tdef_mp dummy_params (sort_n 1) dummy_constructors dummy_attrs Visibility.package_private in
    let dummy_module : ModulePath := ModulePath.mk (List.cons (Identifier.id "Prelude") List.empty) in
    let dummy_def : ScopeDef := {
        name := tdef_mp,
        module := dummy_module,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.package_private,
    } in
    // `def_refs` is a `std.map` `HashMap` (see `lang/scope.mo`'s own `use
    // std.map {}` doc comment) — built via scope_data_add_def/
    // scope_data_add_inductive on top of scope_data_empty rather than a
    // hand-written literal.
    let scope : Scope := {
        module_id := expected_path,
        scope := scope_data_add_inductive (scope_data_add_def scope_data_empty dummy_def) dummy_type,
        parent := Option.none,
        incomplete_match_ok := false,
    } in
    match scope {
        mk mod_id _ _ _ => Similar.similar mod_id expected_path
    }

#[test]
def test_module_construct : Bool :=
    let expected_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "Prelude") List.empty) in
    let dummy_module : ModulePath := ModulePath.mk (List.cons (Identifier.id "Prelude") List.empty) in
    let expected_np : NamePath := NamePath.mk (List.cons (Identifier.id "Prelude") List.empty) in
    let dummy_def : ScopeDef := {
        name := expected_np,
        module := dummy_module,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.package_private,
    } in
    let modu : Module := {
        path := expected_path,
        inductives := List.empty,
        defs := List.cons dummy_def List.empty,
        infixs := List.empty,
        instances := List.empty,
    } in
    match modu {
        mk p inds defs infs ins => Similar.similar p expected_path
    }

#[test]
def test_loaded_modules_construct : Bool :=
    let lm : ModuleRegistry := {
        modules := List.empty,
    } in
    match lm {
        mk mods => true
    }

#[test]
def test_scope_error_construct : Bool :=
    let expected_id : Identifier := Identifier.id "x" in
    let e : ScopeError := ScopeError.name_not_found (NameRef.nid expected_id) in
    match e {
        name_not_found nr => match nr {
            NameRef.nid id => Similar.similar id expected_id,
            NameRef.nnp _ => false,
            NameRef.nop _ => false
        },
        _ => false
    }

// --- Cubical primitives -------------------------------------------------
//
// `Cubical` carries its arity in `args`' length rather than in a field, so
// the arity TABLE is the only statement of what each primitive expects and
// these pins are what keep it honest. `type_check_cubical`
// (`lang/typecheck/infer.mo`) is what enforces it; `lang/tests/infer_tests.mo`
// pins that side.

#[test]
def test_cubical_arity_table : Bool :=
    I64.beq (cubical_arity CubicalPrim.interval) 0
        && I64.beq (cubical_arity CubicalPrim.i0) 0
        && I64.beq (cubical_arity CubicalPrim.i1) 0
        && I64.beq (cubical_arity CubicalPrim.ineg) 1
        && I64.beq (cubical_arity CubicalPrim.imeet) 2
        && I64.beq (cubical_arity CubicalPrim.ijoin) 2

/// The smart constructors must agree with the table they are checked
/// against, or every well-formed term is rejected for arity.
#[test]
def test_cubical_constructors_match_their_arity : Bool :=
    match cubical_prim_of cub_i0 {
        Option.some p => I64.beq (cubical_arity p) 0,
        Option.none => false,
    }

/// `similar` must distinguish primitives. `i0` against `i1` is the pair that
/// matters: they are both nullary, so a tag comparison that fell back to
/// "same arity, same args" would wrongly call them equal -- and a `Similar`
/// answering `true` for two different terms is the silent kind of wrong
/// (`term_matches_carrier` picks an instance off it).
#[test]
def test_cubical_similar_distinguishes_endpoints : Bool :=
    Similar.similar cub_i0 cub_i0
        && Similar.similar cub_i1 cub_i1
        && Bool.not (Similar.similar cub_i0 cub_i1)

/// ...and must distinguish a cubical term from every other `Term` shape.
/// `similar_term_go` is a hand-expanded cross product, so a missed pair is
/// exactly the kind of omission nothing else catches.
#[test]
def test_cubical_similar_distinguishes_from_other_terms : Bool :=
    Bool.not (Similar.similar cub_i0 (sort_n 1))
        && Bool.not (Similar.similar (sort_n 1) cub_i0)
        && Bool.not (Similar.similar cub_interval Term.hole)
        && Bool.not (Similar.similar Term.hole cub_interval)

/// Arguments are compared pointwise, so two applications of the same
/// primitive differ exactly when their arguments do.
#[test]
def test_cubical_similar_compares_arguments : Bool :=
    Similar.similar (cub_ineg cub_i0) (cub_ineg cub_i0)
        && Bool.not (Similar.similar (cub_ineg cub_i0) (cub_ineg cub_i1))
        && Bool.not (Similar.similar (cub_ineg cub_i0) (cub_imeet cub_i0 cub_i1))

/// `cubical_prim_of` peels a location wrapper, like every other shape probe
/// in this codebase must (`term_peel`'s own doc comment).
#[test]
def test_cubical_prim_of_peels_a_location : Bool :=
    let loc : Location := { offset := 0, line := 1, column := 1 } in
    let wrapped : Term := Term.ctx loc cub_i1 in
    match cubical_prim_of wrapped {
        Option.some p => cubical_prim_eq p CubicalPrim.i1,
        Option.none => false,
    }

#[test]
def test_cubical_endpoint_predicate : Bool :=
    cubical_is_endpoint CubicalPrim.i0
        && cubical_is_endpoint CubicalPrim.i1
        && Bool.not (cubical_is_endpoint CubicalPrim.interval)
        && Bool.not (cubical_is_endpoint CubicalPrim.ineg)
