/// De Bruijn shift/substitution for the canonical `Term` type — the two
/// primitives the macro-expansion phase's TERM-producing macro
/// application (`defmacro name params := <term>`) needs.
///
/// Standard, well-known PL theory (Pierce, *Types and Programming
/// Languages*, §6/§7) — no macro-specific hygiene/gensym-renaming
/// needed here, unlike the Rust reference's own `subst_macro`
/// (core/src/eval/macro_expand.rs), which is NAME-based (walks a
/// pre-de-Bruijn-resolution `Term` matching `NameRef`s) and needs
/// `alpha_rename_body`'s gensym counter specifically to stop two
/// DIFFERENT macro expansions' own introduced binders from colliding
/// on the same name. Self-hosted's canonical `Term` is de-Bruijn-
/// indexed from the parser itself — there is no "same name" for two
/// binders to collide on, so this whole class of bug is inherently
/// impossible here by construction. See
/// plans/bootstrapping/self-hosted-compiler.md's macro-expansion-phase
/// section for the full reasoning.
///
/// NOTE: this module is intentionally NOT used for the DECL-generating
/// macro form (`defmacro name params := decls { ... }`) — a decl
/// template's own top-level decls have no enclosing lambda binder, so
/// a macro param referenced inside one is an ordinary FREE/qualified
/// `Term.var sentinel (DebugName.named X)` reference, not a bound de
/// Bruijn index. That form needs a separate, NAME-based substitution
/// (mirroring the reference's own `subst_macro`/`subst_decl_var` much
/// more directly) — a different module, not this one.
use lang.types {
  Con, Literal, MatchCase, Native, StructLitField, Term,
}
use std.list {length}

// ─── Shift ───────────────────────────────────────────────────────────
//
// `term_shift d t` adds `d` (positive or negative) to every FREE
// variable's de Bruijn index in `t` (index >= the current binder
// depth, which starts at 0 and increases by exactly the number of new
// bindings introduced each time the walk descends through a binder —
// 1 for lam/forall/pi's own return type, N for a match case's own N
// pattern-bound field names). Bound variables (idx < depth) are left
// untouched.

def term_shift (d : I64) (t : Term) : Term := term_shift_go d 0 t

#[partial]
def term_shift_go (d : I64) (cutoff : I64) (t : Term) : Term :=
    match t {
        Term.var idx dbg =>
            if Bool.not (I64.lt idx cutoff) then Term.var (idx + d) dbg else Term.var idx dbg,
        Term.var_macro idx dbg =>
            if Bool.not (I64.lt idx cutoff) then Term.var_macro (idx + d) dbg else Term.var_macro idx dbg,
        Term.lam dbg typ body =>
            Term.lam dbg (term_shift_go d cutoff typ) (term_shift_go d (cutoff + 1) body),
        Term.forall dbg kind body =>
            Term.forall dbg (term_shift_go d cutoff kind) (term_shift_go d (cutoff + 1) body),
        Term.pi arg ret =>
            Term.pi (term_shift_go d cutoff arg) (term_shift_go d (cutoff + 1) ret),
        Term.app callee arg =>
            Term.app (term_shift_go d cutoff callee) (term_shift_go d cutoff arg),
        Term.lit value => Term.lit (literal_shift d cutoff value),
        Term.ntv n => Term.ntv (native_shift d cutoff n),
        Term.con c => Term.con (con_shift d cutoff c),
        Term.type_ u => Term.type_ u,
        Term.hole => Term.hole,
        Term.quote_ inner => Term.quote_ (term_shift_go d cutoff inner),
    }

#[partial]
def literal_shift (d : I64) (cutoff : I64) (l : Literal) : Literal :=
    match l {
        Literal.str v => Literal.str v,
        Literal.num n suf => Literal.num n suf,
        Literal.flt t suf => Literal.flt t suf,
        Literal.if_ a b c =>
            Literal.if_ (term_shift_go d cutoff a) (term_shift_go d cutoff b) (term_shift_go d cutoff c),
        Literal.match_ scrut cases =>
            Literal.match_ (term_shift_go d cutoff scrut) (match_cases_shift d cutoff cases),
        Literal.struct_lit fields type_name =>
            Literal.struct_lit (struct_fields_shift d cutoff fields) (opt_term_shift d cutoff type_name),
        Literal.struct_update base fields =>
            Literal.struct_update (term_shift_go d cutoff base) (struct_fields_shift d cutoff fields),
    }

#[partial]
def match_cases_shift (d : I64) (cutoff : I64) (cases : List MatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest => List.cons (match_case_shift d cutoff c) (match_cases_shift d cutoff rest),
    }

#[partial]
def match_case_shift (d : I64) (cutoff : I64) (c : MatchCase) : MatchCase :=
    match c {
        MatchCase.mc name args body =>
            MatchCase.mc name args (term_shift_go d (cutoff + List.length args) body),
    }

#[partial]
def struct_fields_shift (d : I64) (cutoff : I64) (fields : List StructLitField) : List StructLitField :=
    match fields {
        List.empty => List.empty,
        List.cons f rest => List.cons (struct_field_shift d cutoff f) (struct_fields_shift d cutoff rest),
    }

#[partial]
def struct_field_shift (d : I64) (cutoff : I64) (f : StructLitField) : StructLitField :=
    match f { StructLitField.mk name value => StructLitField.mk name (term_shift_go d cutoff value) }

#[partial]
def opt_term_shift (d : I64) (cutoff : I64) (t : Option Term) : Option Term :=
    match t {
        Option.some x => Option.some (term_shift_go d cutoff x),
        Option.none => Option.none,
    }

#[partial]
def opt_terms_shift (d : I64) (cutoff : I64) (ts : List (Option Term)) : List (Option Term) :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (opt_term_shift d cutoff x) (opt_terms_shift d cutoff rest),
    }

#[partial]
def con_shift (d : I64) (cutoff : I64) (c : Con) : Con :=
    match c { Con.mk name typ_name num_args args => Con.mk name typ_name num_args (opt_terms_shift d cutoff args) }

#[partial]
def native_shift (d : I64) (cutoff : I64) (n : Native) : Native :=
    match n { Native.mk name num_args args => Native.mk name num_args (opt_terms_shift d cutoff args) }

// ─── Substitution ────────────────────────────────────────────────────
//
// `term_subst j s t` replaces the de Bruijn index `j` in `t` with `s`
// (shifted up by however many binders the walk has crossed by the time
// it reaches an occurrence, so `s`'s OWN free variables stay correctly
// scoped relative to that deeper position) and, for every OTHER free
// variable with an index greater than `j`, decrements it by 1 (closing
// the gap left by the binder `j` refers to no longer existing once
// substituted). This is the standard FUSED single-pass formulation of
// beta-reduction's usual two-step "shift argument up, substitute,
// shift whole result down" (Pierce §6.3) — verified against that
// definition case by case before trusting it; see `beta_reduce`
// below, this module's only real entry point, for the intended usage
// (peel one `Term.lam` per macro-call argument, substitute at index 0
// each time).

def term_subst (j : I64) (s : Term) (t : Term) : Term := term_subst_go j s 0 t

#[partial]
def term_subst_go (j : I64) (s : Term) (depth : I64) (t : Term) : Term :=
    let target : I64 := j + depth in
    match t {
        Term.var idx dbg =>
            if I64.beq idx target then term_shift depth s
            else if I64.gt idx target then Term.var (idx - 1) dbg
            else Term.var idx dbg,
        Term.var_macro idx dbg =>
            if I64.beq idx target then term_shift depth s
            else if I64.gt idx target then Term.var_macro (idx - 1) dbg
            else Term.var_macro idx dbg,
        Term.lam dbg typ body =>
            Term.lam dbg (term_subst_go j s depth typ) (term_subst_go j s (depth + 1) body),
        Term.forall dbg kind body =>
            Term.forall dbg (term_subst_go j s depth kind) (term_subst_go j s (depth + 1) body),
        Term.pi arg ret =>
            Term.pi (term_subst_go j s depth arg) (term_subst_go j s (depth + 1) ret),
        Term.app callee arg =>
            Term.app (term_subst_go j s depth callee) (term_subst_go j s depth arg),
        Term.lit value => Term.lit (literal_subst j s depth value),
        Term.ntv n => Term.ntv (native_subst j s depth n),
        Term.con c => Term.con (con_subst j s depth c),
        Term.type_ u => Term.type_ u,
        Term.hole => Term.hole,
        Term.quote_ inner => Term.quote_ (term_subst_go j s depth inner),
    }

#[partial]
def literal_subst (j : I64) (s : Term) (depth : I64) (l : Literal) : Literal :=
    match l {
        Literal.str v => Literal.str v,
        Literal.num n suf => Literal.num n suf,
        Literal.flt t suf => Literal.flt t suf,
        Literal.if_ a b c =>
            Literal.if_ (term_subst_go j s depth a) (term_subst_go j s depth b) (term_subst_go j s depth c),
        Literal.match_ scrut cases =>
            Literal.match_ (term_subst_go j s depth scrut) (match_cases_subst j s depth cases),
        Literal.struct_lit fields type_name =>
            Literal.struct_lit (struct_fields_subst j s depth fields) (opt_term_subst j s depth type_name),
        Literal.struct_update base fields =>
            Literal.struct_update (term_subst_go j s depth base) (struct_fields_subst j s depth fields),
    }

#[partial]
def match_cases_subst (j : I64) (s : Term) (depth : I64) (cases : List MatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest => List.cons (match_case_subst j s depth c) (match_cases_subst j s depth rest),
    }

#[partial]
def match_case_subst (j : I64) (s : Term) (depth : I64) (c : MatchCase) : MatchCase :=
    match c {
        MatchCase.mc name args body =>
            MatchCase.mc name args (term_subst_go j s (depth + List.length args) body),
    }

#[partial]
def struct_fields_subst (j : I64) (s : Term) (depth : I64) (fields : List StructLitField) : List StructLitField :=
    match fields {
        List.empty => List.empty,
        List.cons f rest => List.cons (struct_field_subst j s depth f) (struct_fields_subst j s depth rest),
    }

#[partial]
def struct_field_subst (j : I64) (s : Term) (depth : I64) (f : StructLitField) : StructLitField :=
    match f { StructLitField.mk name value => StructLitField.mk name (term_subst_go j s depth value) }

#[partial]
def opt_term_subst (j : I64) (s : Term) (depth : I64) (t : Option Term) : Option Term :=
    match t {
        Option.some x => Option.some (term_subst_go j s depth x),
        Option.none => Option.none,
    }

#[partial]
def opt_terms_subst (j : I64) (s : Term) (depth : I64) (ts : List (Option Term)) : List (Option Term) :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (opt_term_subst j s depth x) (opt_terms_subst j s depth rest),
    }

#[partial]
def con_subst (j : I64) (s : Term) (depth : I64) (c : Con) : Con :=
    match c { Con.mk name typ_name num_args args => Con.mk name typ_name num_args (opt_terms_subst j s depth args) }

#[partial]
def native_subst (j : I64) (s : Term) (depth : I64) (n : Native) : Native :=
    match n { Native.mk name num_args args => Native.mk name num_args (opt_terms_subst j s depth args) }

// ─── Beta-reduction ──────────────────────────────────────────────────

/// Beta-reduce `Term.app (Term.lam _ _ body) arg` — substitute `arg`
/// for the lambda's own bound variable (de Bruijn index 0, always,
/// since `body` is examined immediately after peeling exactly this one
/// lambda — never a deeper index) throughout `body`. This IS the whole
/// "apply macro args to macro params" step the macro-expansion phase's
/// term-producing `defmacro` form needs (`apply_macro`'s own "peel one
/// Lam per supplied arg" loop, mirrored from the Rust reference) — no
/// separate outer shift needed, `term_subst`'s own fused formula
/// already closes the gap left by the consumed binder.
def beta_reduce (body : Term) (arg : Term) : Term := term_subst 0 arg body

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Term`/`MatchCase` fixtures, asserted directly against the
// returned shape (this codebase's own established convention — see
// e.g. `lang/typecheck/infer.mo`'s `test_type_check_con_*` family) —
// no pipeline wiring, no evaluation, purely exercising these two
// primitives in isolation before anything calls them.

#[partial]
def term_var_idx (t : Term) : I64 :=
    match t { Term.var idx _ => idx }

#[partial]
def term_type_level (t : Term) : I64 :=
    match t { Term.type_ u => u }

#[test]
def test_term_shift_free_var_shifted : Bool :=
    // A free variable (nothing binds it at cutoff 0) has `d` added.
    let t : Term := Term.var 0 DebugName.unnamed in
    I64.beq (term_var_idx (term_shift 2 t)) 2

#[test]
def test_term_shift_bound_var_under_lam_untouched : Bool :=
    // `Term.var 0` inside a `Term.lam`'s own body refers to that
    // lambda's own binder (cutoff becomes 1 there) -- it must NOT be
    // shifted, regardless of `d`.
    let t : Term := Term.lam DebugName.unnamed (Term.type_ 1) (Term.var 0 DebugName.unnamed) in
    match term_shift 5 t {
        Term.lam _ _ body => I64.beq (term_var_idx body) 0,
        _ => false,
    }

#[test]
def test_term_shift_free_var_under_lam_shifted : Bool :=
    // `Term.var 1` inside that same lambda's body refers to something
    // OUTSIDE it (cutoff 1, idx 1 >= cutoff) -- this one must shift.
    let t : Term := Term.lam DebugName.unnamed (Term.type_ 1) (Term.var 1 DebugName.unnamed) in
    match term_shift 5 t {
        Term.lam _ _ body => I64.beq (term_var_idx body) 6,
        _ => false,
    }

#[test]
def test_term_subst_replaces_target_index : Bool :=
    // `term_subst 0 s t` on `t = Term.var 0` -- the exact target --
    // replaces wholesale with `s`.
    let s : Term := Term.type_ 7 in
    let t : Term := Term.var 0 DebugName.unnamed in
    I64.beq (term_type_level (term_subst 0 s t)) 7

#[test]
def test_term_subst_lower_index_untouched : Bool :=
    // `term_subst 1 s t` on `t = Term.var 0` -- refers to something
    // MORE local than the binder being substituted away -- must be
    // left completely alone.
    let s : Term := Term.type_ 7 in
    let t : Term := Term.var 0 DebugName.unnamed in
    I64.beq (term_var_idx (term_subst 1 s t)) 0

#[test]
def test_term_subst_closes_gap_for_higher_index : Bool :=
    // `term_subst 0 s t` on `t = Term.var 2` -- some OTHER free
    // variable further out than the one being substituted away --
    // must decrement by 1 to close the gap left by the removed binder.
    let s : Term := Term.type_ 9 in
    let t : Term := Term.var 2 DebugName.unnamed in
    I64.beq (term_var_idx (term_subst 0 s t)) 1

#[test]
def test_term_subst_shifts_replacement_under_binder : Bool :=
    // Substituting under one `Term.lam` (depth 1): the target index
    // seen at that depth is `j + depth = 0 + 1 = 1`. The replacement
    // `s` itself (`Term.var 0`, free relative to the OUTER scope) must
    // come out shifted by that same depth, so it stays correctly
    // scoped relative to the lambda it now sits inside.
    let s : Term := Term.var 0 DebugName.unnamed in
    let t : Term := Term.lam DebugName.unnamed (Term.type_ 1) (Term.var 1 DebugName.unnamed) in
    match term_subst 0 s t {
        Term.lam _ _ body => I64.beq (term_var_idx body) 1,
        _ => false,
    }

#[test]
def test_match_case_binder_depth_shift : Bool :=
    // A 2-arg `MatchCase` binds 2 new indices in its own `body` -- an
    // occurrence of index 2 there refers to something OUTSIDE the
    // match arm entirely (past both pattern bindings) and must shift;
    // an occurrence of index 1 (one of the pattern's own bindings)
    // must not.
    let outer_ref : MatchCase :=
        MatchCase.mc (Identifier.id "some") (List.cons (Identifier.id "a") (List.cons (Identifier.id "b") List.empty)) (Term.var 2 DebugName.unnamed) in
    let bound_ref : MatchCase :=
        MatchCase.mc (Identifier.id "some") (List.cons (Identifier.id "a") (List.cons (Identifier.id "b") List.empty)) (Term.var 1 DebugName.unnamed) in
    match match_case_shift 3 0 outer_ref { MatchCase.mc _ _ body => I64.beq (term_var_idx body) 5 } &&
    match match_case_shift 3 0 bound_ref { MatchCase.mc _ _ body => I64.beq (term_var_idx body) 1 }

#[test]
def test_beta_reduce_replaces_bound_occurrence : Bool :=
    // `beta_reduce body arg` where `body` is exactly `Term.var 0`
    // (the lambda's own bound occurrence, already peeled) must
    // replace it wholesale with `arg`.
    let arg : Term := Term.type_ 3 in
    I64.beq (term_type_level (beta_reduce (Term.var 0 DebugName.unnamed) arg)) 3

#[test]
def test_beta_reduce_closes_gap_for_outer_reference : Bool :=
    // `body = Term.var 1` refers to something one level further OUT
    // than the lambda's own param -- after beta-reducing away that
    // lambda, the reference must shift down by exactly 1 to still
    // point at the same outer binding.
    let arg : Term := Term.type_ 3 in
    I64.beq (term_var_idx (beta_reduce (Term.var 1 DebugName.unnamed) arg)) 0

#[test]
def test_beta_reduce_curried_lam_partial_application : Bool :=
    // Peeling one `Term.lam` per macro-call arg (`apply_macro`'s own
    // loop, mirrored from the Rust reference): for `\x. \y. x y`
    // applied to one arg, peeling the OUTER lambda gives
    // `body = \y. x y` (a `Term.lam` whose own body is
    // `Term.app (Term.var 1) (Term.var 0)` -- `x` at index 1, one
    // level further out than `y`'s own index 0). Beta-reducing that
    // peeled body against `arg` must: replace `x`'s occurrence with
    // `arg` (correctly re-shifted for now sitting one binder deeper),
    // leave the still-bound `y` untouched, and leave the outer
    // `Term.lam` structure itself intact (ready for the next arg).
    let arg : Term := Term.type_ 42 in
    let peeled_body : Term :=
        Term.lam DebugName.unnamed (Term.type_ 1) (Term.app (Term.var 1 DebugName.unnamed) (Term.var 0 DebugName.unnamed)) in
    match beta_reduce peeled_body arg {
        Term.lam _ _ inner =>
            match inner {
                Term.app callee remaining_arg =>
                    I64.beq (term_type_level callee) 42 && I64.beq (term_var_idx remaining_arg) 0,
                _ => false,
            },
        _ => false,
    }
