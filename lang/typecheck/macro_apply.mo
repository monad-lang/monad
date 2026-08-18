/// Macro APPLICATION — the layer directly above [[lang/typecheck/subst.mo]]
/// (de Bruijn `beta_reduce`, term-macro form) and
/// [[lang/typecheck/name_subst.mo]] (name-based `name_subst_decls`,
/// decl-macro form): given an already-parsed macro definition and the
/// concrete args a call site supplied, produce the expanded result.
///
/// Deliberately NOT wired into any pipeline yet (`lang/module.mo`'s
/// `check_file`/scope-building) — that's later staging (work-queue +
/// pipeline splice, Step 5-7 of the macro-expansion plan). This module
/// only has to answer "given a macro def and call args, what does
/// applying them produce" — the caller (a future `expand_term`/outer
/// work-queue) is responsible for finding which macro a given call
/// site's name actually refers to.
use lang.types {Decl, Identifier, Param, Term}
use lang.typecheck.subst {beta_reduce}
use lang.typecheck.name_subst {name_subst_decls}
use std.list {length}

// ─── Term-macro application (`defmacro name params := <term>`) ───────

/// Peel one `Term.lam` per supplied arg, beta-reducing as we go —
/// mirrors the reference's own `apply_macro`, minus its mandatory
/// `alpha_rename_body` hygiene pass (not needed — see `subst.mo`'s own
/// doc comment) and minus its "final result must be `Quote{term}` or
/// error" requirement: self-hosted's own real test fixtures
/// (`lang/parser.mo`'s `test_defmacro_term_body_basic`,
/// `defmacro double x := x`) use bare, non-`quote`-wrapped bodies and
/// are expected to expand directly to their substituted result — a
/// materially simpler contract than the reference's, matching this
/// whole effort's established "self-hosted deviates when de Bruijn
/// makes the reference's own extra machinery unnecessary" pattern.
/// If the result genuinely is (or contains) a `Term.quote_` node —
/// written directly in the macro body, or produced by substitution —
/// that's a separate concern for a later `expand_term`/`resolve_quote`
/// walk (Step 5) to handle, not this function's job.
///
/// Over-application (more args than the macro's own `Term.lam` chain
/// has binders for) falls back to ordinary `Term.app` on the leftover
/// args, rather than silently dropping them or erroring — the same
/// "keep going, don't special-case" choice this module makes
/// throughout, flagged here since it's a real, deliberate design
/// choice rather than an oversight.
#[partial]
def apply_term_macro (body : Term) (args : List Term) : Term :=
    match args {
        List.empty => body,
        List.cons arg rest =>
            match body {
                Term.lam _ _ inner => apply_term_macro (beta_reduce inner arg) rest,
                _ => apply_term_macro (Term.app body arg) rest,
            },
    }

// ─── Decl-macro template expansion (`defmacro name params := decls {...}`) ───

#[partial]
def param_name (p : Param) : Identifier :=
    match p { Param.mk name _ _ _ _ => name }

/// Fold `name_subst_decls` over every `(param, arg)` pair, threading
/// each substitution's own output into the next — mirrors the
/// reference's `expand_macro_call`'s own fold over
/// `subst_decl_var(decl, param_name, arg)`. Caller (`expand_macro_call`
/// below) is responsible for the arity check; called with mismatched
/// list lengths this simply stops substituting once either list runs
/// out (silently leaves any further param references un-substituted
/// rather than crashing) — safe because the real entry point below
/// never calls this without checking arity first.
#[partial]
def fold_decl_gen_subst (params : List Param) (args : List Term) (decls : List Decl) : List Decl :=
    match params {
        List.empty => decls,
        List.cons p prest =>
            match args {
                List.cons a arest => fold_decl_gen_subst prest arest (name_subst_decls (param_name p) a decls),
                List.empty => decls,
            },
    }

/// The decl-form entry point: given a `Decl.decl_gen_d` template's own
/// `params`/`decls` (already looked up by name and arity-relevant by
/// the caller — this function does NOT itself look anything up by
/// name, matching this module's own scope note above) and the concrete
/// `args` a `Decl.macro_call_d` supplied, produce the expanded decl
/// list. `Option.none` on an arity mismatch — mirrors the reference's
/// own arity check in `expand_macro_call`, translated to this
/// codebase's existing `Option`-based error convention (a real
/// diagnostic-carrying error type is pipeline-wiring's job, not this
/// primitive's).
#[partial]
def expand_decl_gen_call (params : List Param) (decls : List Decl) (args : List Term) : Option (List Decl) :=
    if I64.beq (List.length params) (List.length args)
    then Option.some (fold_decl_gen_subst params args decls)
    else Option.none

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Def`/`Decl.decl_gen_d` fixtures — same convention as
// `subst.mo`/`name_subst.mo`'s own tests, no pipeline wiring.

def x_ident : Identifier := Identifier.id "x"
def y_ident : Identifier := Identifier.id "y"

#[partial]
def term_type_level (t : Term) : I64 :=
    match t { Term.type_ u => u }

#[test]
def test_apply_term_macro_single_param_substitutes : Bool :=
    // `defmacro double x := x` (real `lang/parser.mo` test fixture
    // shape) applied to one arg -- `Term.lam _ _ (Term.var 0 _)`
    // beta-reduces straight to the supplied arg.
    let body : Term := Term.lam DebugName.unnamed Term.hole (Term.var 0 DebugName.unnamed) in
    let arg : Term := Term.type_ 5 in
    I64.beq (term_type_level (apply_term_macro body (List.cons arg List.empty))) 5

#[test]
def test_apply_term_macro_no_params_passthrough : Bool :=
    // `defmacro answer := 42` -- no params, no args, body returned as-is.
    let body : Term := Term.type_ 42 in
    let no_args : List Term := List.empty in
    I64.beq (term_type_level (apply_term_macro body no_args)) 42

#[test]
def test_apply_term_macro_two_params_curried : Bool :=
    // `defmacro pick x y := x` applied to 2 args -- peels both
    // lambdas in order, `x`'s own occurrence (index 1, one level
    // further out than `y`) ends up correctly re-shifted by the
    // second beta_reduce, `y` (index 0) is discarded entirely since
    // the body never references it.
    let body : Term :=
        Term.lam DebugName.unnamed Term.hole (Term.lam DebugName.unnamed Term.hole (Term.var 1 DebugName.unnamed)) in
    let arg1 : Term := Term.type_ 7 in
    let arg2 : Term := Term.type_ 8 in
    I64.beq (term_type_level (apply_term_macro body (List.cons arg1 (List.cons arg2 List.empty)))) 7

#[test]
def test_apply_term_macro_over_application_falls_back_to_app : Bool :=
    // More args than the macro declares params -- the leftover arg
    // becomes an ordinary `Term.app` on the (already fully-applied)
    // result, rather than being silently dropped.
    let body : Term := Term.lam DebugName.unnamed Term.hole (Term.var 0 DebugName.unnamed) in
    let arg1 : Term := Term.type_ 3 in
    let arg2 : Term := Term.type_ 4 in
    match apply_term_macro body (List.cons arg1 (List.cons arg2 List.empty)) {
        Term.app callee extra => I64.beq (term_type_level callee) 3 && I64.beq (term_type_level extra) 4,
        _ => false,
    }

#[test]
def test_expand_decl_gen_call_matches_std_derive_shape : Bool :=
    // The real `std/derive.mo` shape: `defmacro derive_lens T := decls
    // { reflect_type_info! T derive_lens_meta }`, invoked as
    // `derive_lens! Point`.
    let t_param : Param := Param.mk (Identifier.id "T") Term.hole Multiplicity.many Option.none List.empty in
    let named_t : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "T")) in
    let meta_ref : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "derive_lens_meta")) in
    let template_decls : List Decl :=
        List.cons (Decl.macro_call_d (Identifier.id "reflect_type_info") (List.cons named_t (List.cons meta_ref List.empty))) List.empty in
    let call_arg : Term := Term.type_ 9 in
    match expand_decl_gen_call (List.cons t_param List.empty) template_decls (List.cons call_arg List.empty) {
        Option.some expanded =>
            match expanded {
                List.cons only_decl _ =>
                    match only_decl {
                        Decl.macro_call_d _ args =>
                            match args { List.cons a _ => I64.beq (term_type_level a) 9, List.empty => false },
                        _ => false,
                    },
                List.empty => false,
            },
        Option.none => false,
    }

#[test]
def test_expand_decl_gen_call_arity_mismatch_is_none : Bool :=
    let t_param : Param := Param.mk (Identifier.id "T") Term.hole Multiplicity.many Option.none List.empty in
    let too_few_args : List Term := List.empty in
    match expand_decl_gen_call (List.cons t_param List.empty) List.empty too_few_args {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_expand_decl_gen_call_two_params_both_substituted : Bool :=
    let x_param : Param := Param.mk x_ident Term.hole Multiplicity.many Option.none List.empty in
    let y_param : Param := Param.mk y_ident Term.hole Multiplicity.many Option.none List.empty in
    let x_ref : Term := Term.var (0 - 1) (DebugName.named x_ident) in
    let y_ref : Term := Term.var (0 - 1) (DebugName.named y_ident) in
    let template_decls : List Decl :=
        List.cons (Decl.macro_call_d (Identifier.id "combine") (List.cons x_ref (List.cons y_ref List.empty))) List.empty in
    let arg_x : Term := Term.type_ 1 in
    let arg_y : Term := Term.type_ 2 in
    match expand_decl_gen_call (List.cons x_param (List.cons y_param List.empty)) template_decls (List.cons arg_x (List.cons arg_y List.empty)) {
        Option.some expanded =>
            match expanded {
                List.cons only_decl _ =>
                    match only_decl {
                        Decl.macro_call_d _ args =>
                            match args {
                                List.cons a1 rest =>
                                    I64.beq (term_type_level a1) 1 &&
                                    match rest { List.cons a2 _ => I64.beq (term_type_level a2) 2, List.empty => false },
                                List.empty => false,
                            },
                        _ => false,
                    },
                List.empty => false,
            },
        Option.none => false,
    }
