/// Generic one-level structural recursion over the canonical `Term` tree.
///
/// `term_map_children f t` applies `f` to every immediate child `Term` of
/// `t` and rebuilds it; `f` itself decides whether and how to recurse
/// further, so this file only ever looks one level down. Each sibling
/// helper does the same for a node kind that carries `Term`s but isn't
/// one (`Literal`, `MatchCase`, `StructLitField`, `Con`, `Native`, and
/// the `Option`/`List` shapes those use).
///
/// Extracted from [[lang/typecheck/macro_expand.mo]], which originally
/// defined this family for `expand_term`/`resolve_quote`'s own fallback
/// cases. It was already being imported across module boundaries by
/// `lang/scope.mo`'s `resolve_infix_term`, so it was shared
/// infrastructure in practice before it was one by name -- this module
/// makes that explicit and gives the substitution walkers
/// ([[lang/typecheck/name_subst.mo]], [[lang/typecheck/subst.mo]]) a
/// home to build on rather than re-deriving the same ~10 helpers each.
use lang.types {Con, Literal, MatchCase, Native, StructLitField, Term}

// ─── Generic structural recursion ──────────────────────────────────
//
// Applies `f` to every immediate child `Term` of `t` and rebuilds it —
// shared by `expand_term`/`resolve_quote`'s own fallback cases (an
// `App`/`Quote` shape that ISN'T a macro call/`unquote`, or any other
// node kind entirely). `f` itself decides whether/how to recurse
// further; this function only ever looks one level down.

#[partial]
def term_map_children (f : Term -> Term) (t : Term) : Term :=
    match t {
        Term.var idx dbg => Term.var idx dbg,
        Term.var_macro idx dbg => Term.var_macro idx dbg,
        Term.lam dbg typ body => Term.lam dbg (f typ) (f body),
        Term.forall dbg kind body => Term.forall dbg (f kind) (f body),
        Term.pi arg ret => Term.pi (f arg) (f ret),
        Term.app callee arg => Term.app (f callee) (f arg),
        Term.lit value => Term.lit (literal_map_children f value),
        Term.ntv n => Term.ntv (native_map_children f n),
        Term.con c => Term.con (con_map_children f c),
        Term.type_ u => Term.type_ u,
        Term.hole => Term.hole,
        Term.quote_ inner => Term.quote_ (f inner),
    }

#[partial]
def literal_map_children (f : Term -> Term) (l : Literal) : Literal :=
    match l {
        Literal.str v => Literal.str v,
        Literal.num n suf => Literal.num n suf,
        Literal.flt t suf => Literal.flt t suf,
        Literal.if_ a b c => Literal.if_ (f a) (f b) (f c),
        Literal.match_ scrut cases => Literal.match_ (f scrut) (match_cases_map_children f cases),
        Literal.struct_lit fields type_name => Literal.struct_lit (struct_fields_map_children f fields) (opt_term_map_children f type_name),
        Literal.struct_update base fields => Literal.struct_update (f base) (struct_fields_map_children f fields),
    }

#[partial]
def match_cases_map_children (f : Term -> Term) (cases : List MatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest => List.cons (match_case_map_children f c) (match_cases_map_children f rest),
    }

#[partial]
def match_case_map_children (f : Term -> Term) (c : MatchCase) : MatchCase :=
    match c { MatchCase.mc name args body fp => MatchCase.mc name args (f body) fp }

#[partial]
def struct_fields_map_children (f : Term -> Term) (fields : List StructLitField) : List StructLitField :=
    match fields {
        List.empty => List.empty,
        List.cons fld rest => List.cons (struct_field_map_children f fld) (struct_fields_map_children f rest),
    }

#[partial]
def struct_field_map_children (f : Term -> Term) (fld : StructLitField) : StructLitField :=
    match fld { StructLitField.mk name value => StructLitField.mk name (f value) }

#[partial]
def opt_term_map_children (f : Term -> Term) (t : Option Term) : Option Term :=
    match t {
        Option.some x => Option.some (f x),
        Option.none => Option.none,
    }

#[partial]
def opt_terms_map_children (f : Term -> Term) (ts : List (Option Term)) : List (Option Term) :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (opt_term_map_children f x) (opt_terms_map_children f rest),
    }

#[partial]
def con_map_children (f : Term -> Term) (c : Con) : Con :=
    match c { Con.mk name typ_name num_args args => Con.mk name typ_name num_args (opt_terms_map_children f args) }

#[partial]
def native_map_children (f : Term -> Term) (n : Native) : Native :=
    match n { Native.mk name num_args args => Native.mk name num_args (opt_terms_map_children f args) }
