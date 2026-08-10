use lang.types {
  Identifier, InductConstructor, Inductive, Infix, InstanceKey, LoadedModules,
  LocalVar, Module, ModulePath, Multiplicity, Operator, Param, Scope,
  ScopeClassDef, ScopeConflict, ScopeData, ScopeDef, ScopeError, ScopeInstance,
  Similar, Term, hole, id, many, mk, mp, name_not_found, nid, nmp, nop, operator,
  type_,
}

// --- Similar instances for scope types ---

instance Similar Infix {
    def similar (a : Infix) (b : Infix) : Bool :=
        match a {
            mk op1 nm1 => match b {
                mk op2 nm2 => Similar.similar op1 op2 && Similar.similar nm1 nm2
            }
        }
}

instance Similar InstanceKey {
    def similar (a : InstanceKey) (b : InstanceKey) : Bool :=
        match a {
            mk cls1 cons1 args1 => match b {
                mk cls2 cons2 args2 =>
                    Similar.similar cls1 cls2
            }
        }
}

instance Similar ScopeDef {
    def similar (a : ScopeDef) (b : ScopeDef) : Bool :=
        match a {
            mk nm1 mod1 sig1 body1 => match b {
                mk nm2 mod2 sig2 body2 =>
                    Similar.similar nm1 nm2 && Similar.similar mod1 mod2
                    && Similar.similar sig1 sig2 && Similar.similar body1 body2
            }
        }
}

instance Similar ScopeClassDef {
    def similar (a : ScopeClassDef) (b : ScopeClassDef) : Bool :=
        match a {
            mk cls1 fn1 id1 sig1 => match b {
                mk cls2 fn2 id2 sig2 =>
                    Similar.similar cls1 cls2 && Similar.similar fn1 fn2
                    && Similar.similar id1 id2 && Similar.similar sig1 sig2
            }
        }
}

instance Similar ScopeInstance {
    def similar (a : ScopeInstance) (b : ScopeInstance) : Bool :=
        match a {
            mk cn1 ins1 => match b {
                mk cn2 ins2 => Similar.similar cn1 cn2
            }
        }
}

instance Similar ScopeConflict {
    def similar (a : ScopeConflict) (b : ScopeConflict) : Bool :=
        match a {
            mk nm1 cands1 => match b {
                mk nm2 cands2 => Similar.similar nm1 nm2
            }
        }
}

instance Similar LocalVar {
    def similar (a : LocalVar) (b : LocalVar) : Bool :=
        match a {
            mk nm1 typ1 mult1 => match b {
                mk nm2 typ2 mult2 =>
                    Similar.similar nm1 nm2 && Similar.similar typ1 typ2
                    && Similar.similar mult1 mult2
            }
        }
}

instance Similar Module {
    def similar (a : Module) (b : Module) : Bool :=
        match a {
            mk p1 ind1 defs1 infs1 ins1 => match b {
                mk p2 ind2 defs2 infs2 ins2 => Similar.similar p1 p2
            }
        }
}

instance Similar LoadedModules {
    def similar (a : LoadedModules) (b : LoadedModules) : Bool :=
        match a {
            mk mods1 => match b {
                mk mods2 => true
            }
        }
}

// --- Scope type construction tests ---

#[test]
def test_infix_construct : Bool :=
    let expected_op : Operator := Operator.operator "+" in
    let expected_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "add") List.empty) in
    let inf : Infix := {
        operator := expected_op,
        name := expected_name,
    } in
    match inf {
        mk op nm => Similar.similar op expected_op && Similar.similar nm expected_name
    }

#[test]
def test_instance_key_construct : Bool :=
    let expected_cls : ModulePath := ModulePath.mp (List.cons (Identifier.id "Show") List.empty) in
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
    let expected_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "add") List.empty) in
    let expected_module : ModulePath := ModulePath.mp (List.cons (Identifier.id "Prelude") List.empty) in
    let sd : ScopeDef := {
        name := expected_name,
        module := expected_module,
        sig := Term.hole,
        body := Term.hole,
    } in
    match sd {
        mk nm modl sig body => Similar.similar nm expected_name && Similar.similar modl expected_module
    }

#[test]
def test_scope_class_def_construct : Bool :=
    let expected_full_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Eq") List.empty) in
    let expected_id : Identifier := Identifier.id "beq" in
    let expected_class : ModulePath := ModulePath.mp (List.cons (Identifier.id "BEq") List.empty) in
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
    let expected_cn : ModulePath := ModulePath.mp (List.cons (Identifier.id "Show") List.empty) in
    let si : ScopeInstance := {
        class_name := expected_cn,
        instances := List.empty,
    } in
    match si {
        mk cn ins => Similar.similar cn expected_cn
    }

#[test]
def test_scope_conflict_construct : Bool :=
    let expected_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "foo") List.empty) in
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
    let tdef_mp : ModulePath := ModulePath.mp (List.cons tcon List.empty) in
    let none_term : Option Term := Option.none in
    let dummy_params : List Param := List.cons (Param.mk tcon Term.hole Multiplicity.many none_term) List.empty in
    let empty_param_list : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "true") List.empty)) empty_param_list (Term.type_ 1) in
    let false_cn : InductConstructor := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "false") List.empty)) empty_param_list (Term.type_ 1) in
    let dummy_constructors : List InductConstructor := List.cons true_cn (List.cons false_cn List.empty) in
    let dummy_attrs : List String := List.empty in
    let dummy_type : Inductive := Inductive.mk tdef_mp dummy_params (Term.type_ 1) dummy_constructors dummy_attrs in
    let expected_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Prelude") List.empty) in
    let dummy_module : ModulePath := ModulePath.mp (List.cons (Identifier.id "Prelude") List.empty) in
    let tdef_def : ScopeDef := {
        name := tdef_mp,
        module := dummy_module,
        sig := Term.hole,
        body := Term.hole,
    } in
    let sd : ScopeData := {
        def_refs := List.cons tdef_def List.empty,
        class_defs := List.empty,
        instances := List.empty,
        inductives := List.cons dummy_type List.empty,
        classes := List.empty,
        infixes := List.empty,
        conflicts := List.empty,
    } in
    match sd {
        mk dr cd ins ind cls infs conf => true
    }

#[test]
def test_scope_construct : Bool :=
    let expected_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Prelude") List.empty) in
    let tcon : Identifier := Identifier.id "Bool" in
    let tdef_mp : ModulePath := ModulePath.mp (List.cons tcon List.empty) in
    let none_term : Option Term := Option.none in
    let dummy_params : List Param := List.cons (Param.mk tcon Term.hole Multiplicity.many none_term) List.empty in
    let empty_param_list : List Param := List.empty in
    let true_cn : InductConstructor := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "true") List.empty)) empty_param_list (Term.type_ 1) in
    let false_cn : InductConstructor := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "false") List.empty)) empty_param_list (Term.type_ 1) in
    let dummy_constructors : List InductConstructor := List.cons true_cn (List.cons false_cn List.empty) in
    let dummy_attrs : List String := List.empty in
    let dummy_type : Inductive := Inductive.mk tdef_mp dummy_params (Term.type_ 1) dummy_constructors dummy_attrs in
    let dummy_module : ModulePath := ModulePath.mp (List.cons (Identifier.id "Prelude") List.empty) in
    let dummy_def : ScopeDef := {
        name := tdef_mp,
        module := dummy_module,
        sig := Term.hole,
        body := Term.hole,
    } in
    let scope : Scope := {
        module_id := expected_path,
        scope := {
            def_refs := List.cons dummy_def List.empty,
            class_defs := List.empty,
            instances := List.empty,
            inductives := List.cons dummy_type List.empty,
            classes := List.empty,
            infixes := List.empty,
            conflicts := List.empty,
        },
        parent := Option.none,
    } in
    match scope {
        mk mod_id _ _ => Similar.similar mod_id expected_path
    }

#[test]
def test_module_construct : Bool :=
    let expected_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Prelude") List.empty) in
    let dummy_module : ModulePath := ModulePath.mp (List.cons (Identifier.id "Prelude") List.empty) in
    let dummy_def : ScopeDef := {
        name := expected_path,
        module := dummy_module,
        sig := Term.hole,
        body := Term.hole,
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
    let lm : LoadedModules := {
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
            NameRef.nmp _ => false,
            NameRef.nop _ => false
        },
        _ => false
    }
