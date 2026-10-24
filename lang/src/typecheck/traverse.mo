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
use lib::types {Con, Cubical, Elim, Literal, MatchCase, Native, StructLitField, Term}
use std::list {List.length}

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
        // One arm for all three binder flavours: `forall` folded into
        // `pi` in R2b, and the walk is the same either way -- a former
        // `forall`'s kind is its `arg` here, unchanged.
        Term.pi b arg ret => Term.pi b (f arg) (f ret),
        Term.app callee arg => Term.app (f callee) (f arg),
        Term.lit value => Term.lit (literal_map_children f value),
        Term.ntv n => Term.ntv (native_map_children f n),
        Term.con c => Term.con (con_map_children f c),
        // A leaf: a level is data, not a child, so `f` is not applied to it.
        Term.sort level => Term.sort level,
        Term.hole => Term.hole,
        Term.quote_ inner => Term.quote_ (f inner),
        // PRESERVING, not transparent. This is the generic rebuild every
        // pass-through pass routes through, so dropping the wrapper here
        // would erase every source position the moment any pass walked a
        // term -- which is most of them. `loc` is data, not a child, so
        // `f` is not applied to it.
        Term.ctx loc inner => Term.ctx loc (f inner),
        // No cubical form is a binder, so every argument is an ordinary
        // child at this node's own depth -- which is why the depth-aware
        // sibling below can pass 0 for all of them.
        Term.cubical c => Term.cubical (cubical_map_children f c),
        // `elim` binds nothing at its own node (unlike `MatchCase`'s
        // simultaneous multi-binder, which is exactly what this
        // representation retires): `params`/`motive`/`scrutinee` are
        // ordinary children, and so are `minors` -- each one is its own
        // `Term.lam` chain, so the binder it introduces is crossed only
        // when `f` recurses INTO that chain, not here. Unlike the affine
        // analyses in usage.mo (which skip `motive`/`params` because they
        // are erased before run time), this walker is substitution's own
        // plumbing and must reach every subterm, type positions included,
        // or a substituted variable's occurrence inside a motive would be
        // silently missed.
        Term.elim e => Term.elim (elim_map_children f e),
    }

def elim_map_children (f : Term -> Term) (e : Elim) : Elim :=
    { e with
      params := terms_map_children f e.params,
      motive := f e.motive,
      minors := terms_map_children f e.minors,
      scrutinee := f e.scrutinee }

/// `args` is positional and its length is the primitive's arity, so this
/// maps in place and never reshapes the list.
def cubical_map_children (f : Term -> Term) (c : Cubical) : Cubical :=
    let mapped : List Term := terms_map_children f c.args in
    { c with args := mapped }

#[partial]
def terms_map_children (f : Term -> Term) (ts : List Term) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (f x) (terms_map_children f rest),
    }

#[partial]
def literal_map_children (f : Term -> Term) (l : Literal) : Literal :=
    match l {
        Literal.str v => Literal.str v,
        Literal.char v => Literal.char v,
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
    match c { MatchCase.mk name args body fp typ_name => MatchCase.mk name args (f body) fp typ_name }

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

// ─── Depth-aware structural recursion ──────────────────────────────
//
// `term_map_children_at_depth f t` is `term_map_children` for walks that
// need to know how many binders they are under -- de Bruijn shifting and
// substitution ([[lang/typecheck/subst.mo]]). `f` receives the binder
// depth of each child relative to `t`: 0 for every child except the BODY
// of a `lam`/`pi`, which is 1 (those two are the only binding
// forms in `Term`, and each binds only over its body, not over its
// type/argument).
//
// Callers thread their own absolute depth through the closure they pass,
// adding the relative depth they are handed. A depth-agnostic caller
// should use plain `term_map_children` instead.
//
// IMPORTANT: `lam`/`pi` are not the only binding forms a walk
// crosses. A `MatchCase`'s own pattern bindings (`args`) bind over its
// BODY too, so a `Literal.match_`'s arms are walked by the depth-aware
// `match_cases_map_children_at_depth` below, which adds
// `List.length args` -- NOT by the depth-agnostic sibling, which would
// silently walk arm bodies at the wrong depth. This exact mistake is
// what `lang/typecheck/subst.mo`'s own
// `test_match_case_binder_depth_shift` guards against.
#[partial]
def term_map_children_at_depth (f : I64 -> Term -> Term) (t : Term) : Term :=
    match t {
        Term.var idx dbg => Term.var idx dbg,
        Term.var_macro idx dbg => Term.var_macro idx dbg,
        Term.lam dbg typ body => Term.lam dbg (f 0 typ) (f 1 body),
        // As above: one arm, all three flavours. The DEPTH is what made
        // the old two arms look different, and it is the same either way
        // -- `forall`'s kind sat at depth 0 exactly as `pi`'s arg does.
        Term.pi b arg ret => Term.pi b (f 0 arg) (f 1 ret),
        Term.app callee arg => Term.app (f 0 callee) (f 0 arg),
        Term.lit value => Term.lit (literal_map_children_at_depth f value),
        Term.ntv n => Term.ntv (native_map_children (f 0) n),
        Term.con c => Term.con (con_map_children (f 0) c),
        // A leaf: a level is data, not a child, so `f` is not applied to it.
        Term.sort level => Term.sort level,
        Term.hole => Term.hole,
        Term.quote_ inner => Term.quote_ (f 0 inner),
        // Depth 0: a wrapper introduces no binder, so the term inside it
        // sits at exactly the depth the wrapper does. Passing 1 here would
        // shift every free index under a located term by one.
        Term.ctx loc inner => Term.ctx loc (f 0 inner),
        // Depth 0 for every argument: no cubical form binds. A path
        // abstraction is an ordinary `Term.lam` with an `I`-typed binder, so
        // dimension variables are counted by the `lam` arm above like any
        // other de Bruijn binder.
        Term.cubical c => Term.cubical (cubical_map_children (f 0) c),
        // Depth 0 for every field, same reasoning as `cubical` just
        // above: `elim` itself binds nothing, so nothing here sits deeper
        // than the node's own depth. A minor's OWN `Term.lam` chain bumps
        // the depth when `f` recurses into it, exactly like a cubical
        // argument that happens to contain a `lam`.
        Term.elim e => Term.elim (elim_map_children_at_depth f e),
    }

def elim_map_children_at_depth (f : I64 -> Term -> Term) (e : Elim) : Elim :=
    { e with
      params := terms_map_children (f 0) e.params,
      motive := f 0 e.motive,
      minors := terms_map_children (f 0) e.minors,
      scrutinee := f 0 e.scrutinee }

#[partial]
def literal_map_children_at_depth (f : I64 -> Term -> Term) (l : Literal) : Literal :=
    match l {
        Literal.str v => Literal.str v,
        Literal.char v => Literal.char v,
        Literal.num n suf => Literal.num n suf,
        Literal.flt t suf => Literal.flt t suf,
        Literal.if_ a b c => Literal.if_ (f 0 a) (f 0 b) (f 0 c),
        Literal.match_ scrut cases => Literal.match_ (f 0 scrut) (match_cases_map_children_at_depth f cases),
        Literal.struct_lit fields type_name => Literal.struct_lit (struct_fields_map_children (f 0) fields) (opt_term_map_children (f 0) type_name),
        Literal.struct_update base fields => Literal.struct_update (f 0 base) (struct_fields_map_children (f 0) fields),
    }

#[partial]
def match_cases_map_children_at_depth (f : I64 -> Term -> Term) (cases : List MatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest => List.cons (match_case_map_children_at_depth f c) (match_cases_map_children_at_depth f rest),
    }

/// A match arm's own pattern bindings bind over its body: the body sits
/// `List.length args` binders deeper than the `Literal.match_` node.
#[partial]
def match_case_map_children_at_depth (f : I64 -> Term -> Term) (c : MatchCase) : MatchCase :=
    match c { MatchCase.mk name args body fp typ_name => MatchCase.mk name args (f (List.length args) body) fp typ_name }

// ─── Read-only one-level children ──────────────────────────────────
//
// The observing sibling of `term_map_children`: the same walk, but it
// RETURNS the child terms instead of rebuilding the node around them.
// A pass that folds over a term without producing one -- a collector of
// diagnostics -- cannot express itself through `Term -> Term` without
// rebuilding a tree nobody reads. Kept beside the map family so a new
// `Term` variant updates both walks in this one file, and every
// collector built on the children view inherits the arm.

pub def term_children (t : Term) : List Term :=
    match t {
        Term.var _idx _dbg => List.empty,
        Term.var_macro _idx _dbg => List.empty,
        Term.lam _dbg typ body => [typ, body],
        Term.pi _b arg ret => [arg, ret],
        Term.app callee arg => [callee, arg],
        Term.lit value => literal_children value,
        Term.ntv n => native_children n,
        Term.con c => con_children c,
        Term.sort _level => List.empty,
        Term.hole => List.empty,
        Term.quote_ inner => [inner],
        Term.ctx _loc inner => [inner],
        Term.cubical c => cubical_children c,
        Term.elim e => elim_children e,
    }

def cubical_children (c : Cubical) : List Term := c.args

/// Same order as `literal_children`'s `match_` arm: scrutinee first, then
/// the arm/minor bodies -- plus `params`/`motive`, which `MatchCase` had
/// no counterpart for (an un-elaborated `match` carries no explicit
/// motive or inductive parameters yet; `Elim` does).
def elim_children (e : Elim) : List Term :=
    List.append e.params (List.cons e.motive (List.append e.minors (List.singleton e.scrutinee)))

def literal_children (l : Literal) : List Term :=
    match l {
        Literal.str _v => List.empty,
        Literal.char _v => List.empty,
        Literal.num _n _suf => List.empty,
        Literal.flt _t _suf => List.empty,
        Literal.if_ a b c => [a, b, c],
        Literal.match_ scrut cases => List.cons scrut (match_cases_children cases),
        Literal.struct_lit fields type_name => List.append (struct_fields_children fields) (opt_term_children type_name),
        Literal.struct_update base fields => List.cons base (struct_fields_children fields),
    }

def match_cases_children (cases : List MatchCase) : List Term :=
    match cases {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                MatchCase.mk _name _args body _fp _typ_name => List.cons body (match_cases_children rest),
            },
    }

def struct_fields_children (fields : List StructLitField) : List Term :=
    match fields {
        List.empty => List.empty,
        List.cons fld rest =>
            match fld {
                StructLitField.mk _name value => List.cons value (struct_fields_children rest),
            },
    }

def opt_term_children (t : Option Term) : List Term :=
    match t {
        Option.none => List.empty,
        Option.some x => [x],
    }

def con_children (c : Con) : List Term :=
    match c { Con.mk _name _typ_name _num_args args => opt_terms_children args }

def native_children (n : Native) : List Term :=
    match n { Native.mk _name _num_args args => opt_terms_children args }

def opt_terms_children (ts : List (Option Term)) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.append (opt_term_children x) (opt_terms_children rest),
    }
