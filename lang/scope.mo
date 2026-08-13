use lang.types {
  Class, ClassDef, Decl, Def, Identifier, InductConstructor, Inductive, Infix,
  Instance, InstanceKey, LoadedModules, LocalScope, LocalVar, Module, ModulePath,
  NameRef, Operator, Param, Scope, ScopeClassDef, ScopeData, ScopeDef, ScopeError,
  ScopeInstance, Similar, Term, class_d, class_not_found, def_d, hole, id,
  inductive_d, inductive_not_found, infix_d, instance_d, instance_not_found, mk,
  mp, name, name_not_found, nid, nmp, nop, open_d, scoped_open_d, struct_d, type_,
  use_d,
}

// --- Helper: empty ScopeData ---

def scope_data_empty : ScopeData := {
    def_refs := List.empty,
    class_defs := List.empty,
    instances := List.empty,
    inductives := List.empty,
    classes := List.empty,
    infixes := List.empty,
    conflicts := List.empty,
}

// --- Helper: module path equality ---

def modpath_eq (a : ModulePath) (b : ModulePath) : Bool :=
    Similar.similar a b

// --- Helper: add a ScopeDef to ScopeData ---

def scope_data_add_def (sd : ScopeData) (d : ScopeDef) : ScopeData :=
    match sd {
        mk dr cd ins ind cls infs conf => {
            def_refs := List.cons d dr,
            class_defs := cd,
            instances := ins,
            inductives := ind,
            classes := cls,
            infixes := infs,
            conflicts := conf,
        }
    }

// --- Helper: add an Inductive to ScopeData ---

def scope_data_add_inductive (sd : ScopeData) (ind : Inductive) : ScopeData :=
    match sd {
        mk dr cd ins inds cls infs conf => {
            def_refs := dr,
            class_defs := cd,
            instances := ins,
            inductives := List.cons ind inds,
            classes := cls,
            infixes := infs,
            conflicts := conf,
        }
    }

// --- build_scope_from_decls: build ScopeData from parsed declarations ---

def build_scope_from_decls (path : ModulePath) (decls : List Decl) : ScopeData :=
    let empty : ScopeData := scope_data_empty in
    let with_decls : ScopeData := build_scope_from_decls_go decls path empty in
    add_builtins with_decls

def build_scope_from_decls_go (decls : List Decl) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match decls {
        List.empty => acc,
        List.cons d ds =>
            let new_acc : ScopeData := build_scope_one_decl d path acc in
            build_scope_from_decls_go ds path new_acc
    }

def build_scope_one_decl (d : Decl) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match d {
        Decl.def_d df => build_scope_def df path acc,
        Decl.inductive_d ind => build_scope_inductive ind path acc,
        Decl.class_d cls => build_scope_class cls path acc,
        Decl.instance_d ins => scope_data_add_instance acc ins,
        Decl.infix_d op name _vis => scope_data_add_infix acc op name,
        Decl.use_d _ _ _ => acc,
        Decl.open_d _ _ => acc,
        Decl.struct_d _ => acc,
        Decl.scoped_open_d _ _ inner => build_scope_one_decl inner path acc
    }

def build_scope_def (df : Def) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match df {
        mk defname _ _ _ _ _ =>
            let sd : ScopeDef := {
                name := defname,
                module := path,
                sig := Term.hole,
                body := Term.hole,
            } in
            scope_data_add_def acc sd
    }

def build_scope_inductive (ind : Inductive) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    let with_ind : ScopeData := scope_data_add_inductive acc ind in
    match ind {
        mk _ _ _ constructors _ _ =>
            add_constructors_as_defs with_ind constructors path
    }

def add_constructors_as_defs (acc : ScopeData) (cns : List InductConstructor) (path : ModulePath) : ScopeData :=
    add_constructors_go acc cns path

def add_constructors_go (acc : ScopeData) (cns : List InductConstructor) (path : ModulePath) : ScopeData :=
    match cns {
        List.empty => acc,
        List.cons cn rest =>
            match cn {
                mk cnname _ _ =>
                    let sd : ScopeDef := {
                        name := cnname,
                        module := path,
                        sig := Term.hole,
                        body := Term.hole,
                    } in
                    let new_acc : ScopeData := scope_data_add_def acc sd in
                    add_constructors_go new_acc rest path
            }
    }

def build_scope_class (cls : Class) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match cls {
        mk clsname _ _ methods _vis =>
            let name_list : List Identifier := List.cons clsname List.empty in
            let cls_mp : ModulePath := ModulePath.mp name_list in
            let empty_params : List Param := List.empty in
            let empty_constructors : List InductConstructor := List.empty in
            let empty_attrs : List String := List.empty in
            let dummy_ind : Inductive := Inductive.mk cls_mp empty_params (Term.type_ 1) empty_constructors empty_attrs Visibility.package_private in
            let with_cls : ScopeData := scope_data_add_class acc dummy_ind in
            add_class_methods with_cls methods cls_mp
    }

def add_class_methods (acc : ScopeData) (methods : List ClassDef) (cls_mp : ModulePath) : ScopeData :=
    add_methods_go acc methods cls_mp

def add_methods_go (acc : ScopeData) (methods : List ClassDef) (cls_mp : ModulePath) : ScopeData :=
    match methods {
        List.empty => acc,
        List.cons m rest =>
            match m {
                mk method_name _ _ =>
                    match cls_mp {
                        ModulePath.mp cls_ids =>
                            let method_id_list : List Identifier := List.cons method_name List.empty in
                            let method_ids : List Identifier := List.append cls_ids method_id_list in
                            let full_name : ModulePath := ModulePath.mp method_ids in
                            let scd : ScopeClassDef := {
                                class_name := cls_mp,
                                full_name := full_name,
                                name := method_name,
                                sig := Term.hole,
                            } in
                            let new_acc : ScopeData := scope_data_add_class_def acc scd in
                            add_methods_go new_acc rest cls_mp
                    }
            }
    }

// --- scope_globals: extract ScopeData from Scope ---

def scope_globals (s : Scope) : ScopeData :=
    match s {
        Scope.mk _ d _ => d,
        _ => scope_data_empty
    }

// --- ScopeData: find a class def (method) by ModulePath ---

def scope_data_find_class_def (sd : ScopeData) (name : ModulePath) : Option ScopeClassDef :=
    match sd {
        mk _ cds _ _ _ _ _ => find_class_def_in_list cds name
    }

def find_class_def_in_list (cds : List ScopeClassDef) (name : ModulePath) : Option ScopeClassDef :=
    match cds {
        List.empty => Option.none,
        List.cons cd rest =>
            match cd {
                mk _class_name full_name _ _ =>
                    if modpath_eq full_name name
                    then Option.some cd
                    else find_class_def_in_list rest name
            }
    }

// ---- scope_find_inductive ---

def scope_find_inductive (name : ModulePath) (s : Scope) : Result ScopeError Inductive :=
    let g : ScopeData := scope_globals s in
    let result : Option Inductive := scope_data_find_inductive g name in
    match result {
        Option.some ind => ok ind,
        Option.none => err (ScopeError.inductive_not_found name)
    }

// --- scope_find_class_def ---

def scope_find_class_def (name : ModulePath) (s : Scope) : Result ScopeError ScopeClassDef :=
    let g : ScopeData := scope_globals s in
    let result : Option ScopeClassDef := scope_data_find_class_def g name in
    match result {
        Option.some cd => ok cd,
        Option.none => err (ScopeError.class_not_found name)
    }

// --- scope_find_inductive_by_constructor ---

def scope_find_inductive_by_constructor (con_name : ModulePath) (s : Scope) : Option Inductive :=
    let g : ScopeData := scope_globals s in
    scope_data_find_inductive_by_constructor g con_name

def scope_data_find_inductive_by_constructor (sd : ScopeData) (con_name : ModulePath) : Option Inductive :=
    match sd {
        mk _ _ _ inds _ _ _ => find_inductive_by_constructor_in_list inds con_name
    }

def find_inductive_by_constructor_in_list (inds : List Inductive) (con_name : ModulePath) : Option Inductive :=
    match inds {
        List.empty => Option.none,
        List.cons ind rest =>
            if inductive_has_constructor ind con_name
            then Option.some ind
            else find_inductive_by_constructor_in_list rest con_name
    }

def inductive_has_constructor (ind : Inductive) (con_name : ModulePath) : Bool :=
    match ind {
        mk _ _ _ constructors _ _ =>
            match constructors {
                List.empty => false,
                List.cons cn rest =>
                    match cn {
                        mk cn_mp _ _ =>
                            if modpath_eq cn_mp con_name
                            then true
                            else inductive_has_constructor_rest rest con_name
                    }
            }
    }

#[terminating]
def inductive_has_constructor_rest (cns : List InductConstructor) (con_name : ModulePath) : Bool :=
    match cns {
        List.empty => false,
        List.cons cn rest =>
            match cn {
                mk cn_mp _ _ =>
                    if modpath_eq cn_mp con_name
                    then true
                    else inductive_has_constructor_rest rest con_name
            }
    }

// --- Find a constructor by name in an inductive, return the constructor ---

def find_constructor_in_inductive (ind : Inductive) (con_name : ModulePath) : Option InductConstructor :=
    match ind {
        mk _ _ _ constructors _ _ => find_constructor_in_list constructors con_name
    }

#[terminating]
def find_constructor_in_list (cns : List InductConstructor) (con_name : ModulePath) : Option InductConstructor :=
    match cns {
        List.empty => Option.none,
        List.cons cn rest =>
            match cn {
                mk cn_mp params typ =>
                    if modpath_eq cn_mp con_name
                    then Option.some cn
                    else find_constructor_in_list rest con_name
            }
    }

// --- scope_find_constructor: find a constructor by name in the scope ---

def scope_find_constructor (con_name : ModulePath) (s : Scope) : Option InductConstructor :=
    match scope_find_inductive_by_constructor con_name s {
        Option.some ind => find_constructor_in_inductive ind con_name,
        Option.none => Option.none,
    }

// --- scope_find_class_def_by_name: search by simple method name (last segment) ---

def scope_find_class_def_by_name (method_name : Identifier) (s : Scope) : Result ScopeError ScopeClassDef :=
    let g : ScopeData := scope_globals s in
    let result : Option ScopeClassDef := scope_data_find_class_def_by_name g method_name in
    match result {
        Option.some cd => ok cd,
        Option.none =>
            let mp : ModulePath := ModulePath.mp (List.cons method_name List.empty) in
            err (ScopeError.class_not_found mp)
    }

def scope_data_find_class_def_by_name (sd : ScopeData) (name : Identifier) : Option ScopeClassDef :=
    match sd {
        mk _ cds _ _ _ _ _ => find_class_def_by_name_in_list cds name
    }

def find_class_def_by_name_in_list (cds : List ScopeClassDef) (name : Identifier) : Option ScopeClassDef :=
    match cds {
        List.empty => Option.none,
        List.cons cd rest =>
            match cd {
                mk _class_name _full_name cd_name _ =>
                    if Similar.similar cd_name name
                    then Option.some cd
                    else find_class_def_by_name_in_list rest name
            }
    }

// --- scope_push_local ---

def scope_push_local (lv : LocalVar) (ls : LocalScope) : LocalScope :=
    let some_ls : Option LocalScope := Option.some ls in
    {
        vars := List.cons lv List.empty,
        parent := some_ls,
    }

// --- scope_find_local ---

#[terminating]
def scope_find_local (name : Identifier) (ls : LocalScope) : Option LocalVar :=
    match ls {
        mk vars parent => find_local_in_list vars name parent
    }

#[terminating]
def find_local_in_list (vars : List LocalVar) (name : Identifier) (parent : Option LocalScope) : Option LocalVar :=
    match vars {
        List.empty =>
            match parent {
                Option.none => Option.none,
                Option.some p => scope_find_local name p
            },
        List.cons lv rest =>
            match lv {
                mk lvname _ _ =>
                    if Similar.similar lvname name
                    then Option.some lv
                    else find_local_in_list rest name parent
            }
    }

// --- scope_resolve_name ---

def scope_resolve_name (nref : NameRef) (s : Scope) (locals : LocalScope) : Result ScopeError ScopeDef :=
    let local_result : Option ScopeDef := resolve_name_in_locals nref locals in
    match local_result {
        Option.some d => ok d,
        Option.none => resolve_name_in_scope nref s
    }

def resolve_name_in_locals (nref : NameRef) (locals : LocalScope) : Option ScopeDef :=
    match nref {
        NameRef.nid i =>
            let lv_opt : Option LocalVar := scope_find_local i locals in
            match lv_opt {
                Option.none => Option.none,
                Option.some lv =>
                    match lv {
                        LocalVar.mk lvname lvtyp _ =>
                            let empty_id_list : List Identifier := List.empty in
                            let lv_mp : ModulePath := ModulePath.mp (List.cons lvname empty_id_list) in
                            let empty_mp : ModulePath := ModulePath.mp empty_id_list in
                            let sd : ScopeDef := {
                                name := lv_mp,
                                module := empty_mp,
                                sig := lvtyp,
                                body := Term.hole,
                            } in
                            Option.some sd
                    }
            },
        NameRef.nmp _ => Option.none,
        NameRef.nop _ => Option.none
    }

def resolve_name_in_scope (nref : NameRef) (s : Scope) : Result ScopeError ScopeDef :=
    match nref {
        NameRef.nid i =>
            let name : ModulePath := ModulePath.mp (List.cons i List.empty) in
            resolve_def_in_scope_by_name name s,
        NameRef.nmp mp =>
            resolve_def_in_scope_by_name mp s,
        NameRef.nop _ =>
            err (ScopeError.name_not_found nref)
    }

def resolve_def_in_scope_by_name (name : ModulePath) (s : Scope) : Result ScopeError ScopeDef :=
    let g : ScopeData := scope_globals s in
    let result : Option ScopeDef := scope_data_find_def g name in
    match result {
        Option.some d => ok d,
        Option.none => err (ScopeError.name_not_found (NameRef.nmp name))
    }

// --- ScopeData: find a ScopeDef by ModulePath in def_refs ---

def scope_data_find_def (sd : ScopeData) (name : ModulePath) : Option ScopeDef :=
    match sd {
        mk dr _ _ _ _ _ _ => find_def_in_list dr name
    }

def find_def_in_list (defs : List ScopeDef) (name : ModulePath) : Option ScopeDef :=
    match defs {
        List.empty => Option.none,
        List.cons d rest =>
            match d {
                mk dname _ _ _ =>
                    if modpath_eq dname name
                    then Option.some d
                    else find_def_in_list rest name
            }
    }

// --- ScopeData: find an Inductive by ModulePath ---

def scope_data_find_inductive (sd : ScopeData) (name : ModulePath) : Option Inductive :=
    match sd {
        mk _ _ _ inds _ _ _ => find_inductive_in_list inds name
    }

def find_inductive_in_list (inds : List Inductive) (name : ModulePath) : Option Inductive :=
    match inds {
        List.empty => Option.none,
        List.cons ind rest =>
            match ind {
                mk indname _ _ _ _ _ =>
                    if modpath_eq indname name
                    then Option.some ind
                    else find_inductive_in_list rest name
            }
    }

// --- Instance handling helpers ---

def scope_data_add_instance (sd : ScopeData) (ins : Instance) : ScopeData :=
    match ins {
        mk _ cname _ _ _ =>
            match sd {
                mk dr cd insts ind cls infs conf =>
                    let updated_insts : List ScopeInstance := scope_add_to_instances insts cname ins in
                    {
                        def_refs := dr,
                        class_defs := cd,
                        instances := updated_insts,
                        inductives := ind,
                        classes := cls,
                        infixes := infs,
                        conflicts := conf,
                    }
            }
    }

def scope_add_to_instances (insts : List ScopeInstance) (cls_name : ModulePath) (ins : Instance) : List ScopeInstance :=
    match insts {
        List.empty =>
            let ins_list : List Instance := List.cons ins List.empty in
            let si : ScopeInstance := {
                class_name := cls_name,
                instances := ins_list,
            } in
            let empty_rest : List ScopeInstance := List.empty in
            List.cons si empty_rest,
        List.cons si rest =>
            match si {
                mk cn ins_list =>
                    if modpath_eq cn cls_name
                    then
                        let new_ins_list : List Instance := List.cons ins ins_list in
                        let new_si : ScopeInstance := {
                            class_name := cn,
                            instances := new_ins_list,
                        } in
                        List.cons new_si rest
                    else List.cons si (scope_add_to_instances rest cls_name ins)
            }
    }

def scope_data_add_infix (sd : ScopeData) (op : Operator) (name : ModulePath) : ScopeData :=
    let inf : Infix := { operator := op, name := name } in
    match sd {
        mk dr cd ins ind cls infs conf => {
            def_refs := dr,
            class_defs := cd,
            instances := ins,
            inductives := ind,
            classes := cls,
            infixes := List.cons inf infs,
            conflicts := conf,
        }
    }

def scope_data_add_class (sd : ScopeData) (cls : Inductive) : ScopeData :=
    match sd {
        mk dr cd ins ind clss infs conf => {
            def_refs := dr,
            class_defs := cd,
            instances := ins,
            inductives := ind,
            classes := List.cons cls clss,
            infixes := infs,
            conflicts := conf,
        }
    }

def scope_data_add_class_def (sd : ScopeData) (cd : ScopeClassDef) : ScopeData :=
    match sd {
        mk dr cds ins ind cls infs conf => {
            def_refs := dr,
            class_defs := List.cons cd cds,
            instances := ins,
            inductives := ind,
            classes := cls,
            infixes := infs,
            conflicts := conf,
        }
    }

// --- Builtins ---

def add_builtins (sd : ScopeData) : ScopeData :=
    let sd_with_type : ScopeData := add_builtin_type sd in
    add_builtin_prop sd_with_type

def add_builtin_type (sd : ScopeData) : ScopeData :=
    let type_id : Identifier := Identifier.id "Type" in
    let empty_id_list : List Identifier := List.empty in
    let type_name : ModulePath := ModulePath.mp (List.cons type_id empty_id_list) in
    let empty_params : List Param := List.empty in
    let empty_constructors : List InductConstructor := List.empty in
    let empty_attrs : List String := List.empty in
    let type_ind : Inductive := Inductive.mk type_name empty_params Term.hole empty_constructors empty_attrs Visibility.package_private in
    let type_sd : ScopeDef := {
        name := type_name,
        module := ModulePath.mp empty_id_list,
        sig := Term.hole,
        body := Term.hole,
    } in
    let sd1 : ScopeData := scope_data_add_inductive sd type_ind in
    scope_data_add_def sd1 type_sd

def add_builtin_prop (sd : ScopeData) : ScopeData :=
    let prop_id : Identifier := Identifier.id "Prop" in
    let empty_id_list : List Identifier := List.empty in
    let prop_name : ModulePath := ModulePath.mp (List.cons prop_id empty_id_list) in
    let empty_params : List Param := List.empty in
    let empty_constructors : List InductConstructor := List.empty in
    let empty_attrs : List String := List.empty in
    let prop_ind : Inductive := Inductive.mk prop_name empty_params Term.hole empty_constructors empty_attrs Visibility.package_private in
    let prop_sd : ScopeDef := {
        name := prop_name,
        module := ModulePath.mp empty_id_list,
        sig := Term.hole,
        body := Term.hole,
    } in
    let sd1 : ScopeData := scope_data_add_inductive sd prop_ind in
    scope_data_add_def sd1 prop_sd

// --- build_scope_from_modules: build ScopeData from loaded modules ---

def build_scope_from_modules (path : ModulePath) (loaded : LoadedModules) : ScopeData :=
    match loaded {
        mk modules =>
            let empty : ScopeData := scope_data_empty in
            build_scope_from_modules_go modules empty
    }

def build_scope_from_modules_go (modules : List Module) (acc : ScopeData) : ScopeData :=
    match modules {
        List.empty => acc,
        List.cons m rest =>
            let with_mod : ScopeData := build_scope_from_one_module m acc in
            build_scope_from_modules_go rest with_mod
    }

def build_scope_from_one_module (m : Module) (acc : ScopeData) : ScopeData :=
    match m {
        mk _path _inductives defs infxs _instances =>
            let with_defs : ScopeData := add_module_defs acc defs in
            let with_inds : ScopeData := add_module_inductives with_defs _inductives in
            let with_inst : ScopeData := add_module_instances with_inds _instances in
            add_module_infixes with_inst infxs
    }

def add_module_defs (acc : ScopeData) (defs : List ScopeDef) : ScopeData :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            let new_acc : ScopeData := scope_data_add_def acc d in
            add_module_defs new_acc rest
    }

def add_module_inductives (acc : ScopeData) (inds : List Inductive) : ScopeData :=
    match inds {
        List.empty => acc,
        List.cons ind rest =>
            let new_acc : ScopeData := scope_data_add_inductive acc ind in
            add_module_inductives new_acc rest
    }

def add_module_instances (acc : ScopeData) (insts : List ScopeInstance) : ScopeData :=
    match insts {
        List.empty => acc,
        List.cons si rest =>
            let new_acc : ScopeData := add_module_instance_group acc si in
            add_module_instances new_acc rest
    }

def add_module_instance_group (acc : ScopeData) (si : ScopeInstance) : ScopeData :=
    match acc {
        mk dr cd insts ind cls infs conf =>
            let merged : List ScopeInstance := scope_add_instance_group insts si in
            {
                def_refs := dr,
                class_defs := cd,
                instances := merged,
                inductives := ind,
                classes := cls,
                infixes := infs,
                conflicts := conf,
            }
    }

def scope_add_instance_group (insts : List ScopeInstance) (si : ScopeInstance) : List ScopeInstance :=
    match si {
        mk cn ins_list =>
            scope_add_instances_to_group insts cn ins_list
    }

def scope_add_instances_to_group (insts : List ScopeInstance) (cls_name : ModulePath) (ins_list : List Instance) : List ScopeInstance :=
    match insts {
        List.empty =>
            let si : ScopeInstance := {
                class_name := cls_name,
                instances := ins_list,
            } in
            let empty_rest : List ScopeInstance := List.empty in
            List.cons si empty_rest,
        List.cons existing rest =>
            match existing {
                mk cn existing_list =>
                    if modpath_eq cn cls_name
                    then
                        let merged_list : List Instance := list_append existing_list ins_list in
                        let new_si : ScopeInstance := {
                            class_name := cn,
                            instances := merged_list,
                        } in
                        List.cons new_si rest
                    else List.cons existing (scope_add_instances_to_group rest cls_name ins_list)
            }
    }

def add_module_infixes (acc : ScopeData) (infxs : List Infix) : ScopeData :=
    match infxs {
        List.empty => acc,
        List.cons inf rest =>
            match acc {
                mk dr cd ins ind cls infs conf => {
                    def_refs := dr,
                    class_defs := cd,
                    instances := ins,
                    inductives := ind,
                    classes := cls,
                    infixes := List.cons inf infs,
                    conflicts := conf,
                }
            }
    }

// --- scope_resolve_instance: find concrete instance by class name ---

def scope_resolve_instance (class_name : ModulePath) (instance_key : InstanceKey) (s : Scope) : Result ScopeError Instance :=
    let g : ScopeData := scope_globals s in
    let candidates : List Instance := scope_instance_candidates g class_name in
    first_matching_instance candidates instance_key

def scope_instance_candidates (sd : ScopeData) (cls_name : ModulePath) : List Instance :=
    match sd {
        mk _ _ insts _ _ _ _ => find_instances_by_class insts cls_name
    }

def find_instances_by_class (insts : List ScopeInstance) (cls_name : ModulePath) : List Instance :=
    match insts {
        List.empty => List.empty,
        List.cons si rest =>
            match si {
                mk cn ins_list =>
                    if modpath_eq cn cls_name
                    then list_append ins_list (find_instances_by_class rest cls_name)
                    else find_instances_by_class rest cls_name
            }
    }

def first_matching_instance (candidates : List Instance) (key : InstanceKey) : Result ScopeError Instance :=
    match candidates {
        List.empty => err (ScopeError.instance_not_found key),
        List.cons ins rest =>
            if instance_key_matches ins key
            then ok ins
            else first_matching_instance rest key
    }

def instance_key_matches (ins : Instance) (key : InstanceKey) : Bool :=
    match ins {
        mk _ cls_name constraints ins_args _ =>
            match key {
                mk key_cls _ key_args =>
                    if Similar.similar cls_name key_cls
                    then term_args_match ins_args key_args
                    else false
            }
    }

/// Compare instance type args (List Term) against key type args (List Param).
/// Extracts type_ field from each Param and uses term_similar_pairwise.
def term_args_match (ins_args : List Term) (key_args : List Param) : Bool :=
    match ins_args {
        List.empty =>
            match key_args {
                List.empty => true,
                _ => false,
            },
        List.cons t rest_ins =>
            match key_args {
                List.empty => false,
                List.cons p rest_key =>
                    match p {
                        mk _ p_typ _ _ =>
                            if Similar.similar t p_typ
                            then term_args_match rest_ins rest_key
                            else false,
                    },
            },
    }

// --- list_append helper (prelude List.append is curried) ---

def list_append {A : Type} (xs : List A) (ys : List A) : List A :=
    match xs {
        List.empty => ys,
        List.cons x rest => List.cons x (list_append rest ys)
    }

// Exports
// infix (++) := list_append
