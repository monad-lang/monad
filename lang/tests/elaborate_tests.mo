use lang.types {
  Class, ClassDef, Decl, Def, Identifier, ModulePath, Param, Term, TypeConstraint,
  class_d, def_d, forall, hole, id, id_eq, id_member, many, mk, mp, named, pi,
  type_, unnamed, use_bare, use_d, var,
}
use lang.elaborate {
  elaborate_class, elaborate_decls, elaborate_def, elaborate_type, free_vars,
  names_of_decl, names_of_decls, sentinel,
}

open Term {forall, hole, pi, type_, var}
open Decl {class_d, def_d, use_d}
open DebugName {named, unnamed}
open Identifier {id}
open ModulePath {mp}
open Multiplicity {many}

// --- Helper definitions ---

def id_A : Identifier := Identifier.id "A"
def id_B : Identifier := Identifier.id "B"
def id_Bool : Identifier := Identifier.id "Bool"
def id_Eq : Identifier := Identifier.id "Eq"

def v_A : Term := var sentinel (named id_A)
def v_B : Term := var sentinel (named id_B)
def v_Bool : Term := var sentinel (named id_Bool)

def no_ids : List Identifier := List.empty
def empty_constraints : List TypeConstraint := List.empty
def empty_attrs : List String := List.empty
def empty_class_defs : List ClassDef := List.empty
def empty_params : List Param := List.empty
def none_term : Option Term := Option.none

// --- sentinel test ---

#[test]
def test_sentinel : Bool :=
    sentinel == (-1)

// --- id_eq tests ---

#[test]
def test_id_eq_same : Bool :=
    id_eq (Identifier.id "A") (Identifier.id "A")

#[test]
def test_id_eq_diff : Bool :=
    Bool.not (id_eq (Identifier.id "A") (Identifier.id "B"))

// --- id_member tests ---

#[test]
def test_id_member_true : Bool :=
    let ids : List Identifier := List.cons id_A (List.cons id_B List.empty) in
    id_member id_A ids

#[test]
def test_id_member_false : Bool :=
    let ids : List Identifier := List.cons id_A List.empty in
    Bool.not (id_member id_B ids)

// --- free_vars tests ---

#[test]
def test_free_vars_var_named : Bool :=
    let v : Term := var sentinel (named (Identifier.id "x")) in
    let result : List Identifier := free_vars v no_ids in
    match result {
        List.cons x rest => match rest {
            List.empty => id_eq x (Identifier.id "x"),
            _ => false,
        },
        List.empty => false,
    }

#[test]
def test_free_vars_var_unnamed : Bool :=
    let v : Term := var sentinel DebugName.unnamed in
    let result : List Identifier := free_vars v no_ids in
    match result {
        List.empty => true,
        _ => false,
    }

#[test]
def test_free_vars_var_known : Bool :=
    let known : List Identifier := List.cons id_A List.empty in
    let result : List Identifier := free_vars v_A known in
    match result {
        List.empty => true,
        _ => false,
    }

#[test]
def test_free_vars_var_bound : Bool :=
    let v : Term := var 0 (named id_A) in
    let result : List Identifier := free_vars v no_ids in
    match result {
        List.empty => true,
        _ => false,
    }

#[test]
def test_free_vars_hole : Bool :=
    let result : List Identifier := free_vars Term.hole no_ids in
    match result {
        List.empty => true,
        _ => false,
    }

#[test]
def test_free_vars_pi : Bool :=
    let typ : Term := pi v_A v_B in
    let result : List Identifier := free_vars typ no_ids in
    id_member id_A result && id_member id_B result

// --- elaborate_type tests ---

#[test]
def test_elaborate_type_pi_free_vars : Bool :=
    let typ : Term := pi v_A v_A in
    let elaborated : Term := elaborate_type typ empty_constraints no_ids in
    match elaborated {
        forall dbg kind body =>
            match dbg {
                named n =>
                    if id_eq n id_A
                    then
                        match body {
                            pi a r => true,
                            _ => false,
                        }
                    else false,
                unnamed => false,
            },
        _ => false,
    }

#[test]
def test_elaborate_type_no_free_vars : Bool :=
    let typ : Term := pi v_Bool v_Bool in
    let known : List Identifier := List.cons id_Bool no_ids in
    let elaborated : Term := elaborate_type typ empty_constraints known in
    match elaborated {
        pi _ _ => true,
        _ => false,
    }

// --- elaborate_def tests ---

#[test]
def test_elaborate_def_free_var : Bool :=
    let typ : Term := pi v_A v_A in
    let body : Term := var 0 (named (Identifier.id "x")) in
    let mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "f") List.empty) in
    let d : Def := Def.mk mp typ body empty_constraints empty_attrs in
    let elaborated : Def := elaborate_def d no_ids in
    match elaborated {
        Def.mk _ elab_typ _ _ _ =>
            match elab_typ {
                forall _ _ _ => true,
                _ => false,
            },
    }

// --- elaborate_class tests ---

#[test]
def test_elaborate_class_method : Bool :=
    let p_A : Param := Param.mk id_A (type_ 1) Multiplicity.many none_term in
    let eq_typ : Term := pi v_A (pi v_A (type_ 0)) in
    let meth : ClassDef := ClassDef.mk (Identifier.id "eq") eq_typ none_term in
    let methods : List ClassDef := List.cons meth List.empty in
    let params : List Param := List.cons p_A List.empty in
    let cls : Class := Class.mk id_Eq params empty_constraints methods in
    let elaborated : Class := elaborate_class cls no_ids in
    match elaborated {
        Class.mk _ _ _ elaborated_methods =>
            match elaborated_methods {
                List.cons em _ =>
                    match em {
                        ClassDef.mk _ elab_typ _ =>
                            match elab_typ {
                                forall _ _ _ => false,
                                _ => true,
                            },
                    },
                List.empty => false,
            },
    }

// --- elaborate_decls tests ---

#[test]
def test_elaborate_decls_empty : Bool :=
    let decls : List Decl := List.empty in
    let result : List Decl := elaborate_decls decls no_ids in
    match result {
        List.empty => true,
        _ => false,
    }

// --- names_of_decl tests ---

#[test]
def test_names_of_decl_def : Bool :=
    let mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "f") List.empty) in
    let d : Def := Def.mk mp (type_ 1) Term.hole empty_constraints empty_attrs in
    let decl : Decl := Decl.def_d d in
    let names : List Identifier := names_of_decl decl in
    match names {
        List.cons x rest => match rest {
            List.empty => id_eq x (Identifier.id "f"),
            _ => false,
        },
        List.empty => false,
    }

#[test]
def test_names_of_decl_class : Bool :=
    let cls : Class := Class.mk id_Eq empty_params empty_constraints empty_class_defs in
    let decl : Decl := Decl.class_d cls in
    let names : List Identifier := names_of_decl decl in
    match names {
        List.cons x rest => match rest {
            List.empty => id_eq x id_Eq,
            _ => false,
        },
        List.empty => false,
    }

#[test]
def test_names_of_decl_use_empty : Bool :=
    let mp : ModulePath := ModulePath.mp no_ids in
    let decl : Decl := Decl.use_d mp UseFilter.use_bare in
    let names : List Identifier := names_of_decl decl in
    match names {
        List.empty => true,
        _ => false,
    }

// --- names_of_decls tests ---

#[test]
def test_names_of_decls_multiple : Bool :=
    let mp_f : ModulePath := ModulePath.mp (List.cons (Identifier.id "f") List.empty) in
    let mp_g : ModulePath := ModulePath.mp (List.cons (Identifier.id "g") List.empty) in
    let d1 : Decl := Decl.def_d (Def.mk mp_f (type_ 1) Term.hole empty_constraints empty_attrs) in
    let d2 : Decl := Decl.def_d (Def.mk mp_g (type_ 1) Term.hole empty_constraints empty_attrs) in
    let decls : List Decl := List.cons d1 (List.cons d2 List.empty) in
    let names : List Identifier := names_of_decls decls in
    id_member (Identifier.id "f") names && id_member (Identifier.id "g") names
