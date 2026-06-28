use lang.types
open types

/// Free variable sentinel index from parser (t2_sentinel = -1).
/// de Bruijn index >= 0 means bound; -1 means free/unknown.
def sentinel : I64 := -1


/// Collect all free type variables from a Term.
/// A free variable is a var with de Bruijn index == sentinel (-1)
/// and a named debug name that is NOT in known_names.
/// Mirrors Rust's free_vars (type.rs:1901).
def free_vars (typ : Term) (known_names : List Identifier) : List Identifier :=
    match typ {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id =>
                    if I64.beq idx sentinel
                    then
                        if id_member id known_names
                        then List.empty
                        else
                            let rest : List Identifier := List.empty in
                            List.cons id rest
                    else List.empty,
                DebugName.unnamed => List.empty,
            },
        Term.lam dbg typ_ body =>
            union_ids (free_vars typ_ known_names) (free_vars body known_names),
        Term.forall dbg kind body =>
            union_ids (free_vars kind known_names) (free_vars body known_names),
        Term.pi arg ret =>
            union_ids (free_vars arg known_names) (free_vars ret known_names),
        Term.app fun_ arg =>
            union_ids (free_vars fun_ known_names) (free_vars arg known_names),
        Term.lit lit_val => match lit_val {
            Literal.str _ => List.empty,
            Literal.num _ _ => List.empty,
            Literal.if_ one two three =>
                let a := free_vars one known_names in
                let b := free_vars two known_names in
                let ab := union_ids a b in
                let c := free_vars three known_names in
                union_ids ab c,
            Literal.match_ value cases =>
                let vv := free_vars value known_names in
                free_vars_of_cases cases known_names vv,
        },
        Term.con c =>
            match c {
                Con.mk _ _ _ args => free_vars_of_opt_terms args known_names,
            },
        Term.ntv _ => List.empty,
        Term.type_ _ => List.empty,
        Term.hole => List.empty,
    }

/// Collect free vars from match case bodies.
def free_vars_of_cases (cases : List MatchCase) (known_names : List Identifier) (acc : List Identifier) : List Identifier :=
    match cases {
        List.cons elem rest =>
            match elem {
                MatchCase.mc _ _ body =>
                    let body_vars := free_vars body known_names in
                    let acc_ := union_ids acc body_vars in
                    free_vars_of_cases rest known_names acc_,
            },
        List.empty => acc,
    }

/// Collect free vars from Option Term list (Con args).
def free_vars_of_opt_terms (args : List (Option Term)) (known_names : List Identifier) : List Identifier :=
    match args {
        List.cons opt rest =>
            let hd_vars := match opt {
                Option.some t => free_vars t known_names,
                Option.none => List.empty,
            } in
            let rest_vars := free_vars_of_opt_terms rest known_names in
            union_ids hd_vars rest_vars,
        List.empty => List.empty,
    }

/// Collect type variable names from a list of type constraints.
def collect_constraint_vars (constraints : List TypeConstraint) (known_names : List Identifier) : List Identifier :=
    match constraints {
        List.cons elem rest =>
            match elem {
                TypeConstraint.mk _ vars =>
                    let filtered := filter_known vars known_names in
                    let rest_vars := collect_constraint_vars rest known_names in
                    union_ids filtered rest_vars,
            },
        List.empty => List.empty,
    }

/// Filter a list of identifiers, keeping only those NOT in known_names.
def filter_known (ids : List Identifier) (known_names : List Identifier) : List Identifier :=
    match ids {
        List.cons hd rest =>
            if id_member hd known_names
            then filter_known rest known_names
            else List.cons hd (filter_known rest known_names),
        List.empty => List.empty,
    }

/// Elaborate a type by adding Forall bindings for free type variables.
/// Mirrors Rust's elaborate_type (type.rs:2860).
def elaborate_type (typ : Term) (constraints : List TypeConstraint) (known_names : List Identifier) : Term :=
    let fv := free_vars typ known_names in
    let cv := collect_constraint_vars constraints known_names in
    let all_vars := union_ids fv cv in
    wrap_forall typ all_vars

/// Wrap a type with Forall binders for each free var (in order).
def wrap_forall (typ : Term) (vars : List Identifier) : Term :=
    match vars {
        List.cons hd rest =>
            let typ_ := Term.type_ 1 in
            let forall_term := Term.forall (DebugName.named hd) typ_ (wrap_forall typ rest) in
            forall_term,
        List.empty => typ,
    }

/// Elaborate a function definition's type signature.
/// Mirrors Rust's elaborate_def (type.rs:2877).
def elaborate_def (d : Def) (known_names : List Identifier) : Def :=
    match d {
        Def.mk name typ term constraints attrs =>
            let elaborated_typ := elaborate_type typ constraints known_names in
            Def.mk name elaborated_typ term constraints attrs,
    }

/// Elaborate an inductive type definition.
/// Mirrors Rust's elaborate_inductive (type.rs:2959).
def elaborate_inductive (ind : Inductive) (known_names : List Identifier) : Inductive :=
    match ind {
        Inductive.mk name params typ constructors attrs =>
            let elaborated_constructors := elaborate_constructors constructors known_names in
            Inductive.mk name params typ elaborated_constructors attrs,
    }

/// Elaborate a list of constructors.
def elaborate_constructors (constructors : List InductConstructor) (known_names : List Identifier) : List InductConstructor :=
    match constructors {
        List.cons hd rest =>
            let elaborated_hd := elaborate_constructor hd known_names in
            let elaborated_rest := elaborate_constructors rest known_names in
            List.cons elaborated_hd elaborated_rest,
        List.empty => List.empty,
    }

/// Elaborate a single constructor's type signature.
/// For inductives with params, those params are already bound (known).
def elaborate_constructor (con : InductConstructor) (known_names : List Identifier) : InductConstructor :=
    match con {
        InductConstructor.mk name params typ =>
            // Add the inductive's own params to known_names
            // (they are bound by the inductive's forall)
            let param_names := collect_param_names params in
            let extended_names := union_ids param_names known_names in
            let elaborated_typ := elaborate_type typ List.empty extended_names in
            InductConstructor.mk name params elaborated_typ,
    }

/// Collect identifier names from a list of params.
def collect_param_names (params : List Param) : List Identifier :=
    match params {
        List.cons param rest =>
            match param {
                Param.mk name _ _ _ => List.cons name (collect_param_names rest),
            },
        List.empty => List.empty,
    }

/// Elaborate a class definition.
def elaborate_class (cls : Class) (known_names : List Identifier) : Class :=
    match cls {
        Class.mk name params constraints methods =>
            let param_names := collect_param_names params in
            let extended_names := union_ids param_names known_names in
            let elaborated_methods := elaborate_class_defs methods extended_names in
            Class.mk name params constraints elaborated_methods,
    }

/// Elaborate a list of class method definitions.
def elaborate_class_defs (methods : List ClassDef) (known_names : List Identifier) : List ClassDef :=
    match methods {
        List.cons hd rest =>
            let elaborated_hd := elaborate_class_def hd known_names in
            let elaborated_rest := elaborate_class_defs rest known_names in
            List.cons elaborated_hd elaborated_rest,
        List.empty => List.empty,
    }

/// Elaborate a single class method definition's type signature.
def elaborate_class_def (m : ClassDef) (known_names : List Identifier) : ClassDef :=
    match m {
        ClassDef.mk name typ default =>
            let elaborated_typ := elaborate_type typ List.empty known_names in
            ClassDef.mk name elaborated_typ default,
    }

/// Elaborate an instance definition.
/// Instance types are already concrete — we just pass through.
def elaborate_instance (ins : Instance) (known_names : List Identifier) : Instance :=
    ins

/// Elaborate a struct definition.
def elaborate_struct (s : Struct) (known_names : List Identifier) : Struct :=
    s

/// Extract an identifier from a ModulePath if it has exactly one segment.
def mp_to_maybe_id (mp : ModulePath) : Option Identifier :=
    match mp {
        ModulePath.mp ids => match ids {
            List.cons x rest => match rest {
                List.empty => Option.some x,
                _ => Option.none,
            },
            List.empty => Option.none,
        },
    }

/// Collect all names introduced by a declaration.
def names_of_decl (decl : Decl) : List Identifier :=
    match decl {
        Decl.def_d d =>
            match d {
                Def.mk name _ _ _ _ =>
                    match mp_to_maybe_id name {
                        Option.some id =>
                            let empty : List Identifier := List.empty in
                            List.cons id empty,
                        Option.none => List.empty,
                    },
            },
        Decl.inductive_d i =>
            match i {
                Inductive.mk name _ _ _ _ =>
                    match mp_to_maybe_id name {
                        Option.some id =>
                            let empty : List Identifier := List.empty in
                            List.cons id empty,
                        Option.none => List.empty,
                    },
            },
        Decl.class_d c =>
            match c {
                Class.mk name _ _ _ =>
                    let empty : List Identifier := List.empty in
                    List.cons name empty,
            },
        Decl.struct_d s =>
            match s {
                Struct.mk name _ =>
                    let empty : List Identifier := List.empty in
                    List.cons name empty,
            },
        Decl.instance_d i =>
            match i {
                Instance.mk name _ _ _ =>
                    let empty : List Identifier := List.empty in
                    List.cons name empty,
            },
        _ => List.empty,
    }

/// Collect all names from a list of declarations.
def names_of_decls (decls : List Decl) : List Identifier :=
    match decls {
        List.cons hd rest =>
            let hd_names := names_of_decl hd in
            let rest_names := names_of_decls rest in
            union_ids hd_names rest_names,
        List.empty => List.empty,
    }

/// Elaborate a module name from ModulePath (single-segment → Identifier, else keep in known as module path)
def name_of_module (mp : ModulePath) : List Identifier :=
    match mp_to_maybe_id mp {
        Option.some id =>
            let empty : List Identifier := List.empty in
            List.cons id empty,
        Option.none => List.empty,
    }

/// Elaborate a single declaration.
def elaborate_decl (decl : Decl) (known_names : List Identifier) : Decl :=
    match decl {
        Decl.def_d d => Decl.def_d (elaborate_def d known_names),
        Decl.inductive_d i => Decl.inductive_d (elaborate_inductive i known_names),
        Decl.class_d c => Decl.class_d (elaborate_class c known_names),
        Decl.struct_d s => Decl.struct_d (elaborate_struct s known_names),
        Decl.instance_d i => Decl.instance_d (elaborate_instance i known_names),
        Decl.infix_d op p => Decl.infix_d op p,
        Decl.use_d p => Decl.use_d p,
        Decl.open_d p => Decl.open_d p,
    }

/// Elaborate all declarations in a module.
/// Builds known_names from the decls' own names plus existing names,
/// then maps elaborate_decl over each decl.
/// Mirrors Rust's elaborate_decls (type.rs:3074).
def elaborate_decls (decls : List Decl) (existing_names : List Identifier) : List Decl :=
    let decl_names := names_of_decls decls in
    let known_names := union_ids existing_names decl_names in
    elaborate_decls_map decls known_names

/// Map elaborate_decl over a list of decls with a fixed known_names set.
def elaborate_decls_map (decls : List Decl) (known_names : List Identifier) : List Decl :=
    match decls {
        List.cons hd rest =>
            let elaborated_hd := elaborate_decl hd known_names in
            let elaborated_rest := elaborate_decls_map rest known_names in
            List.cons elaborated_hd elaborated_rest,
        List.empty => List.empty,
    }
