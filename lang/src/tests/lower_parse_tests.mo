// Pins on `lang::parser::lower_parse`'s DE BRUIJN output -- the indices a
// parsed term ends up with, which `show_term` cannot show (it prints names).
//
// The rule these pin: a `Term.pi`'s codomain sits one binder deep, so a
// name bound OUTSIDE the arrow must be one index higher inside it. The
// anonymous-arrow case used to skip that binder entirely, which left every
// `A -> B` in the tree one index short and made delta-unfolding such a def
// produce a dangling parameter (univalence.md, 2026-10-30).

use lang::types {Decl, Term}
use lib::module {parse_all_decls}

open ParseResult {fail, success}

/// The `term` of the first `def` in `decls`.
def def_term_of (decls : List Decl) : Option Term :=
    match decls {
        List.empty => Option.none,
        List.cons d rest =>
            match d {
                Decl.def_d dd => Option.some dd.term,
                _ => def_term_of rest,
            },
    }

/// ...and its declared `typ`.
def def_typ_of (decls : List Decl) : Option Term :=
    match decls {
        List.empty => Option.none,
        List.cons d rest =>
            match d {
                Decl.def_d dd => Option.some dd.typ,
                _ => def_typ_of rest,
            },
    }

/// A two-parameter def's term is `lam A (lam B body)`.
def two_lams (t : Term) : Option Term :=
    match t {
        Term.lam _ _ inner =>
            match inner {
                Term.lam _ _ core => Option.some core,
                _ => Option.none,
            },
        _ => Option.none,
    }

def pi_cod_idx (t : Term) : I64 :=
    match t {
        Term.pi _ _ cod =>
            match cod {
                Term.var i _ => i,
                _ => -100,
            },
        _ => -101,
    }

def pi_dom_idx (t : Term) : I64 :=
    match t {
        Term.pi _ dom _ =>
            match dom {
                Term.var i _ => i,
                _ => -100,
            },
        _ => -101,
    }

/// `def ArrowT (A B : Type) : Type := A -> B` -- the body's arrow.
def arrow_body (decls : List Decl) : Option Term :=
    match def_term_of decls {
        Option.some t => two_lams t,
        Option.none => Option.none,
    }

/// The param chain is `pi A (pi B (pi g (A -> B) B))`; hand back the
/// parameter's OWN arrow `A -> B`.
def param_arrow (decls : List Decl) : Option Term :=
    match def_typ_of decls {
        Option.some t =>
            match t {
                Term.pi _ _ r1 =>
                    match r1 {
                        Term.pi _ _ r2 =>
                            match r2 {
                                Term.pi _ dom _ => Option.some dom,
                                _ => Option.none,
                            },
                        _ => Option.none,
                    },
                _ => Option.none,
            },
        Option.none => Option.none,
    }

def cod_is (o : Option Term) (want : I64) : Bool :=
    match o {
        Option.some t => I64.beq (pi_cod_idx t) want,
        Option.none => false,
    }

def dom_is (o : Option Term) (want : I64) : Bool :=
    match o {
        Option.some t => I64.beq (pi_dom_idx t) want,
        Option.none => false,
    }

/// A def's own body: an anonymous arrow's codomain still sits one binder
/// deep, so `B` is index 1 (the same index `A` has in the domain slot).
/// Reverting `pi_ret_ctx`'s anonymous arm to "do not extend" makes this
/// report 0.
#[test]
def test_anonymous_arrow_codomain_counts_its_binder : Bool :=
    match parse_all_decls "def ArrowT (A B : Type) : Type := A -> B" {
        success _ decls =>
            dom_is (arrow_body decls) 1 && cod_is (arrow_body decls) 1,
        fail _ => false,
    }

/// The same arrow written as a PARAMETER's type, which lowers through the
/// same arm: `(g : A -> B)`. This is the shape every higher-order
/// parameter has, so it is the one that matters corpus-wide.
#[test]
def test_parameter_arrow_codomain_counts_its_binder : Bool :=
    match parse_all_decls "def use_arrow (A B : Type) (g : A -> B) : B := g" {
        success _ decls =>
            dom_is (param_arrow decls) 1 && cod_is (param_arrow decls) 1,
        fail _ => false,
    }

/// The NAMED arrow was already correct -- pinned as the control that says
/// the fix did not change the one case that worked.
#[test]
def test_named_arrow_codomain_counts_its_binder : Bool :=
    match parse_all_decls "def Named (A B : Type) : Type := (x : A) -> B" {
        success _ decls => cod_is (arrow_body decls) 1,
        fail _ => false,
    }
