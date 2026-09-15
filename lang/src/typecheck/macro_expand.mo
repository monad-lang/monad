/// The term-level expansion walk — `expand_term`/`resolve_quote`,
/// mirroring `core/src/eval/macro_expand.rs`'s own pair of the same
/// name, built on [[lang/typecheck/macro_apply.mo]]'s
/// `apply_term_macro` (itself built on [[lang/typecheck/subst.mo]]).
///
/// Deliberately NOT wired into any pipeline yet (see `macro_apply.mo`'s
/// own scope note — same reasoning applies here). This module answers
/// "given a way to look up a macro definition by name, and a `Term`,
/// what does it look like with every macro call resolved" — the
/// caller (a future outer decl-level work-queue, Step 6-7) is
/// responsible for building that lookup from a real set of registered
/// `Decl.def_macro_d`s and threading the whole thing through the
/// pipeline.
use lang.types {Con, Identifier, Literal, MatchCase, Native, StructLitField, Term, id_eq}
use lang.typecheck.macro_apply {apply_term_macro}
use lang.typecheck.traverse {con_map_children, literal_map_children, match_case_map_children, match_cases_map_children, native_map_children, opt_term_map_children, opt_terms_map_children, struct_field_map_children, struct_fields_map_children, term_map_children}

// ─── Application-spine helpers ─────────────────────────────────────
//
// Self-hosted term-position macro calls (`name! a b c`, parsed by
// `macro_call_term`/`atom_parsers` into a `Term.var_macro` atom
// followed by ordinary curried juxtaposition — `App(App(App(VarMacro,
// a), b), c)`, exactly like any other multi-arg call) need their FULL
// arg list collected before `apply_term_macro` can run (it consumes a
// `List Term`, not one arg at a time) — these two walk down an
// App-chain's own left spine to find what's at the bottom and what
// was applied along the way, in left-to-right supplied order.

// Peels: a macro call's head must be visible as a `var_macro` through any
// location wrapper.
#[partial]
def spine_head (t : Term) : Term :=
    match term_peel t {
        Term.app callee _ => spine_head callee,
        _ => term_peel t,
    }

#[partial]
def spine_args (t : Term) (acc : List Term) : List Term :=
    match term_peel t {
        Term.app callee arg => spine_args callee (List.cons arg acc),
        _ => acc,
    }

/// `Option.some macro_name` when `t`'s own application spine bottoms
/// out at a term-position macro reference (`Term.var_macro`) with a
/// real name attached; `Option.none` for any other shape (ordinary
/// application, or a `var_macro` with no `DebugName` at all — which
/// shouldn't occur in practice, `macro_call_term` always attaches one,
/// but this isn't the place to assume that).
#[partial]
def macro_call_head (t : Term) : Option Identifier :=
    match spine_head t {
        Term.var_macro _ dbg =>
            match dbg {
                DebugName.named id => Option.some id,
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

#[partial]
def unquote_ident : Identifier := Identifier.id "unquote"

/// `unquote(x)` has no dedicated grammar of its own (matches the Rust
/// reference — it isn't special syntax there either, just a plain
/// call to a name that `resolve_quote` recognizes): it parses as an
/// ordinary `Term.var sentinel (DebugName.named (Identifier.id
/// "unquote"))` applied to one arg, structurally indistinguishable
/// from any other single-arg call until this check runs.
#[partial]
def is_unquote_call (t : Term) : Bool :=
    match spine_head t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => id_eq id unquote_ident,
                DebugName.unnamed => false,
            },
        _ => false,
    }

#[partial]
def exactly_one (xs : List Term) : Option Term :=
    match xs {
        List.cons x rest => match rest { List.empty => Option.some x, List.cons _ _ => Option.none },
        List.empty => Option.none,
    }

// ─── The walk itself ────────────────────────────────────────────────

/// Structural `Term` recursion; on an application spine bottoming out
/// at a registered macro, expands the (already-`expand_term`ed) args
/// then applies the macro, then re-runs the RESULT through
/// `expand_term` again (matches the reference — a macro's own
/// expansion may itself contain further macro calls, e.g. a template
/// that quotes another `name!` call). An unresolved macro name is NOT
/// an error — passed through, expanded only structurally. Hitting
/// `Term.quote_` dispatches to `resolve_quote` instead of continuing
/// this same walk (its `unquote`-recognizing behavior only applies
/// inside a quote).
#[partial]
def expand_term (lookup : Identifier -> Option Term) (t : Term) : Term :=
    match t {
        Term.app _ _ =>
            match macro_call_head t {
                Option.some macro_name =>
                    match lookup macro_name {
                        Option.some macro_body =>
                            let args : List Term := List.map (expand_term lookup) (spine_args t List.empty) in
                            expand_term lookup (apply_term_macro macro_body args),
                        Option.none => term_map_children (expand_term lookup) t,
                    },
                Option.none => term_map_children (expand_term lookup) t,
            },
        Term.quote_ inner => Term.quote_ (resolve_quote lookup inner),
        _ => term_map_children (expand_term lookup) t,
    }

/// Walks a quoted body. `unquote(x)` (an application spine bottoming
/// out at a plain `Term.var` named `"unquote"`, with exactly one arg)
/// is replaced by that arg itself — already concrete by this point, no
/// evaluation — then that arg is re-run through `expand_term` (it may
/// itself contain live macro calls). Any OTHER macro call found
/// directly in the quote body is expanded right here too (mirrors the
/// reference exactly). Everything else recurses structurally,
/// remaining quoted (a nested `Term.quote_` stays a `Term.quote_` —
/// this walk doesn't collapse it).
#[partial]
def resolve_quote (lookup : Identifier -> Option Term) (t : Term) : Term :=
    match t {
        Term.app _ _ =>
            if is_unquote_call t
            then
                match exactly_one (spine_args t List.empty) {
                    Option.some arg => expand_term lookup arg,
                    // Malformed unquote call (0 or 2+ args) -- not this
                    // primitive's job to diagnose (later pipeline
                    // wiring's); fall back rather than silently drop.
                    Option.none => term_map_children (resolve_quote lookup) t,
                }
            else
                match macro_call_head t {
                    Option.some macro_name =>
                        match lookup macro_name {
                            Option.some macro_body =>
                                let args : List Term := List.map (resolve_quote lookup) (spine_args t List.empty) in
                                resolve_quote lookup (apply_term_macro macro_body args),
                            Option.none => term_map_children (resolve_quote lookup) t,
                        },
                    Option.none => term_map_children (resolve_quote lookup) t,
                },
        _ => term_map_children (resolve_quote lookup) t,
    }

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built lookup functions + `Term` fixtures, no pipeline wiring.

def double_ident : Identifier := Identifier.id "double"

#[partial]
def term_type_level (t : Term) : I64 :=
    match t { Term.type_ u => u }

/// `defmacro double x := x` -- the one real `lang/parser.mo` test
/// fixture shape this whole module is built to expand correctly.
def double_body : Term := Term.lam DebugName.unnamed Term.hole (Term.var 0 DebugName.unnamed)

def no_macros_lookup (id : Identifier) : Option Term := Option.none

def double_lookup (id : Identifier) : Option Term :=
    if id_eq id double_ident then Option.some double_body else Option.none

#[test]
def test_macro_call_head_recognizes_var_macro_spine : Bool :=
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.type_ 1) in
    match macro_call_head call {
        Option.some id => id_eq id double_ident,
        Option.none => false,
    }

#[test]
def test_macro_call_head_none_for_ordinary_app : Bool :=
    let call : Term := Term.app (Term.var 0 DebugName.unnamed) (Term.type_ 1) in
    match macro_call_head call {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_spine_args_collects_left_to_right : Bool :=
    // `f a b c` == `App(App(App(f, a), b), c)` -- args must come back
    // in the order they were originally supplied, not reversed.
    let f : Term := Term.var_macro (0 - 1) (DebugName.named double_ident) in
    let a : Term := Term.type_ 1 in
    let b : Term := Term.type_ 2 in
    let c : Term := Term.type_ 3 in
    let call : Term := Term.app (Term.app (Term.app f a) b) c in
    match spine_args call List.empty {
        List.cons x1 rest1 =>
            I64.beq (term_type_level x1) 1 &&
            match rest1 {
                List.cons x2 rest2 =>
                    I64.beq (term_type_level x2) 2 &&
                    match rest2 { List.cons x3 _ => I64.beq (term_type_level x3) 3, List.empty => false },
                List.empty => false,
            },
        List.empty => false,
    }

#[test]
def test_expand_term_expands_registered_macro_call : Bool :=
    // `double! 9` -- expands to `9` directly (beta-reduction result,
    // no `Quote` wrapper required, matching `apply_term_macro`'s own
    // documented contract).
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.type_ 9) in
    I64.beq (term_type_level (expand_term double_lookup call)) 9

#[test]
def test_expand_term_passes_through_unknown_macro_name : Bool :=
    // An unresolved macro name is NOT an error -- structurally
    // recursed into (its own arg still gets expanded) and left as an
    // unexpanded `Term.app`/`Term.var_macro` call.
    let unknown : Identifier := Identifier.id "unknown_macro" in
    let inner_call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.type_ 4) in
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named unknown)) inner_call in
    match expand_term double_lookup call {
        Term.app callee arg =>
            (match callee { Term.var_macro _ dbg => match dbg { DebugName.named id => id_eq id unknown, DebugName.unnamed => false }, _ => false }) &&
            I64.beq (term_type_level arg) 4,
        _ => false,
    }

#[test]
def test_expand_term_recurses_under_lambda : Bool :=
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.type_ 6) in
    let t : Term := Term.lam DebugName.unnamed Term.hole call in
    match expand_term double_lookup t {
        Term.lam _ _ body => I64.beq (term_type_level body) 6,
        _ => false,
    }

#[test]
def test_expand_term_no_macro_calls_structural_noop : Bool :=
    let t : Term := Term.app (Term.var 0 DebugName.unnamed) (Term.type_ 2) in
    match expand_term no_macros_lookup t {
        Term.app _ arg => I64.beq (term_type_level arg) 2,
        _ => false,
    }

#[test]
def test_resolve_quote_unwraps_unquote : Bool :=
    // `quote { unquote(x) }` where `x` is already a concrete value --
    // `resolve_quote` on the quote's own inner term replaces the
    // `unquote(...)` call with that value directly.
    let unquote_ref : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "unquote")) in
    let inner : Term := Term.app unquote_ref (Term.type_ 13) in
    I64.beq (term_type_level (resolve_quote no_macros_lookup inner)) 13

#[test]
def test_resolve_quote_expands_macro_call_inside_quote : Bool :=
    // A macro call written directly inside a quoted body (not wrapped
    // in `unquote`) is ALSO expanded right there -- matches the
    // reference exactly.
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.type_ 21) in
    I64.beq (term_type_level (resolve_quote double_lookup call)) 21

#[test]
def test_resolve_quote_leaves_nested_quote_wrapped : Bool :=
    let inner_quote : Term := Term.quote_ (Term.type_ 8) in
    match resolve_quote no_macros_lookup inner_quote {
        Term.quote_ inner => I64.beq (term_type_level inner) 8,
        _ => false,
    }

#[test]
def test_expand_term_dispatches_quote_to_resolve_quote : Bool :=
    // Hitting `Term.quote_` during `expand_term` must dispatch to
    // `resolve_quote` (which knows about `unquote`) rather than
    // continuing `expand_term`'s own plain structural walk.
    let unquote_ref : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "unquote")) in
    let quoted : Term := Term.quote_ (Term.app unquote_ref (Term.type_ 17)) in
    match expand_term no_macros_lookup quoted {
        Term.quote_ inner => I64.beq (term_type_level inner) 17,
        _ => false,
    }
