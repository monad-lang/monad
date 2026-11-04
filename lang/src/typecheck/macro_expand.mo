/// The term-level expansion walk — `expand_term`/`resolve_quote`,
/// mirroring `rust/core/src/eval/macro_expand.rs`'s own pair of the same
/// name, built on [[lang/typecheck/macro_apply.mo]]'s
/// `apply_term_macro` (itself built on [[lang/typecheck/subst.mo]]).
///
/// Two layers:
///
/// - The pure `expand_term`/`resolve_quote` pair, called by
///   `lang/typecheck/macro_queue.mo`'s per-file `expand_decls`. It has
///   only a macro lookup, so it expands ordinary term macros and leaves
///   every `meta!` call untouched.
/// - The `Result`-returning `expand_term_with_meta`, called by the
///   whole-graph pass (`lang/module.mo`'s `expand_decls_graph`), which
///   additionally carries a `MetaIntrinsicCtx` so a term-position
///   `meta!`/`reflect_type_info!` can be evaluated and its `Expr`
///   reified. Evaluation can fail, which is why this half returns
///   `Result` (the pure wrappers cannot, and swallow a depth-limit
///   failure by leaving the term unexpanded — the graph pass diagnoses
///   it).
use lang::core_value {Value}
use lang::types {
  Con, Decl, Identifier, Inductive, Literal, MatchCase, NamePath, Native,
  StructLitField, Term, binder_anon, concrete, id_eq, level_const, named,
  sentinel, show_identifier, term_peel, unnamed,
}
use lib::typecheck::macro_apply {apply_term_macro}
use lib::typecheck::meta_eval {meta_eval_invoke}
use lib::typecheck::meta_reflect {
  build_type_info_value, find_inductive_by_bare_name, reify_value_to_term,
  str_val, strip_term_ctx, term_free_var_name,
}
use lib::typecheck::traverse {result_bind, term_map_children_result}

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

// ─── The meta intrinsic's evaluation environment ──────────────────────
//
// `meta! subject meta_def` at TERM position needs three things beyond
// the macro lookup: the decl list the meta def is evaluated against
// (already prepared for real execution — see `meta_eval.mo`'s header),
// the inductives the subject and the reifier resolve names against, and
// nothing else. The graph pass builds it once and shares it; the
// per-file pure walk has none and leaves `meta!` in place.

pub struct MetaIntrinsicCtx {
    mic_dispatched : List Decl,
    mic_inductives : List Inductive,
}

/// `BUILTIN_INTRINSICS`'s self-hosted twin: `reflect_type_info` stays an
/// accepted ALIAS of `meta` for one nightly rollout window (the last
/// published nightly resolves only the hardcoded spelling at
/// `lang/module.mo`'s `is_reflect_type_info_call`).
def is_intrinsic_ident (id : Identifier) : Bool :=
    id_eq id (Identifier.id "meta") || id_eq id (Identifier.id "reflect_type_info")

/// A recursive macro (`defmacro loopy x := quote { loopy! x }`) would
/// otherwise recurse until the stack dies. The reference caps at 64
/// (`MAX_EXPANSION_DEPTH`); 32 is already far past any real template.
def max_expansion_depth : I64 := 32

// ─── The Result-returning walk ────────────────────────────────────────

/// The walk with an optional meta-evaluation environment. `Option.none`
/// is exactly the per-file pure walk: ordinary macros expand, `meta!`
/// calls are left untouched. `depth` bounds the number of macro
/// applications along one expansion chain.
#[partial]
def expand_term_go
    (lookup : Identifier -> Option Term)
    (ctx : Option MetaIntrinsicCtx)
    (depth : I64)
    (t : Term) : Result String Term :=
    if I64.gt depth max_expansion_depth then
        Result.err "macro expansion exceeded the depth limit (does a macro expand into itself?)"
    else
        match t {
            Term.app _ _ =>
                match macro_call_head t {
                    Option.some macro_name =>
                        if is_intrinsic_ident macro_name then
                            expand_intrinsic_go (expand_term_go lookup ctx (I64.add depth 1)) ctx macro_name (spine_args t List.empty)
                        else
                            match lookup macro_name {
                                Option.some macro_body =>
                                    result_bind
                                        (map_terms_result (expand_term_go lookup ctx (I64.add depth 1)) (spine_args t List.empty))
                                        (fn (args : List Term) =>
                                            apply_macro_expansion_go lookup ctx (I64.add depth 1) macro_body args),
                                Option.none => term_map_children_result (expand_term_go lookup ctx depth) t,
                            },
                    Option.none => term_map_children_result (expand_term_go lookup ctx depth) t,
                },
            Term.quote_ inner =>
                result_bind (resolve_quote_go lookup ctx depth inner) (fn (inner2 : Term) =>
                    Result.ok (Term.quote_ inner2)),
            _ => term_map_children_result (expand_term_go lookup ctx depth) t,
        }

/// The quote-body twin of `expand_term_go`. `unquote(x)` splices its arg
/// back into term context; any other macro call is expanded right here.
#[partial]
def resolve_quote_go
    (lookup : Identifier -> Option Term)
    (ctx : Option MetaIntrinsicCtx)
    (depth : I64)
    (t : Term) : Result String Term :=
    if I64.gt depth max_expansion_depth then
        Result.err "macro expansion exceeded the depth limit (does a macro expand into itself?)"
    else
        match t {
            Term.app _ _ =>
                if is_unquote_call t
                then
                    match exactly_one (spine_args t List.empty) {
                        Option.some arg => expand_term_go lookup ctx depth arg,
                        Option.none => term_map_children_result (resolve_quote_go lookup ctx depth) t,
                    }
                else
                    match macro_call_head t {
                        Option.some macro_name =>
                            if is_intrinsic_ident macro_name then
                                expand_intrinsic_go (resolve_quote_go lookup ctx (I64.add depth 1)) ctx macro_name (spine_args t List.empty)
                            else
                                match lookup macro_name {
                                    Option.some macro_body =>
                                        result_bind
                                            (map_terms_result (resolve_quote_go lookup ctx (I64.add depth 1)) (spine_args t List.empty))
                                            (fn (args : List Term) =>
                                                apply_macro_expansion_go lookup ctx (I64.add depth 1) macro_body args),
                                    Option.none => term_map_children_result (resolve_quote_go lookup ctx depth) t,
                                },
                        Option.none => term_map_children_result (resolve_quote_go lookup ctx depth) t,
                    },
            _ => term_map_children_result (resolve_quote_go lookup ctx depth) t,
        }

/// Apply a term macro and give back the EXPANSION, not a quoted template.
///
/// A term macro's body is normally `quote { ... }` (`fmt`'s is
/// `quote { meta! template fmt_meta }`), and the reference requires the
/// applied result to be that quote, resolves its inside, and strips the
/// quote (`rust/core/src/eval/macro_expand.rs`'s `apply_macro`). Without
/// the strip, `fmt! "..."` would expand to a `quote_` node — syntax as
/// data — and the checker rejects it. The bare-body form (`defmacro
/// double x := x + x`) is this compiler's own deliberate deviation: it
/// has no quote to strip, so it is expanded as the term it already is.
#[partial]
def apply_macro_expansion_go
    (lookup : Identifier -> Option Term)
    (ctx : Option MetaIntrinsicCtx)
    (depth : I64)
    (macro_body : Term)
    (args : List Term) : Result String Term :=
    strip_applied_quote_go lookup ctx depth (apply_term_macro macro_body args)

/// The strip half, split out so the applied term is a PARAMETER
/// (`applied`) rather than a catch-all pattern binder — a bare lowercase
/// pattern name can resolve against an unrelated global instead of
/// binding.
#[partial]
def strip_applied_quote_go
    (lookup : Identifier -> Option Term)
    (ctx : Option MetaIntrinsicCtx)
    (depth : I64)
    (applied : Term) : Result String Term :=
    // The parser wraps terms in source locations, and a macro body is a
    // term like any other — strip before asking whether the RESULT is a
    // quote (the reference does the same, `strip_ctx` in `apply_macro`).
    match strip_term_ctx applied {
        Term.quote_ inner =>
            result_bind (resolve_quote_go lookup ctx depth inner) (fn (resolved : Term) =>
                expand_term_go lookup ctx depth resolved),
        _ => expand_term_go lookup ctx depth applied,
    }

/// Expand the arguments (already in the caller's walk — `expand` is
/// `expand_term_go` or `resolve_quote_go`), then dispatch. Arguments are
/// expanded BEFORE the intrinsic runs, matching the reference.
#[partial]
def expand_intrinsic_go
    (expand : Term -> Result String Term)
    (ctx : Option MetaIntrinsicCtx)
    (name : Identifier)
    (args : List Term) : Result String Term :=
    result_bind (map_terms_result expand args) (fn (args2 : List Term) =>
        match ctx {
            // The per-file pure walk has no evaluation environment; leave
            // the call for the whole-graph pass rather than failing here.
            Option.none => Result.err (String.concat (show_identifier name)
                "!: the meta intrinsic needs the whole-graph expansion environment"),
            Option.some c => dispatch_meta c name args2,
        })

/// `meta! subject meta_def` — reflect the subject to a value, invoke the
/// ordinary Monad def, reify its `Expr` result.
#[partial]
def dispatch_meta (ctx : MetaIntrinsicCtx) (name : Identifier) (args : List Term) : Result String Term :=
    match args {
        List.cons subject rest =>
            match rest {
                List.cons meta_ref rest2 =>
                    match rest2 {
                        List.empty =>
                            result_bind (reflect_subject name subject ctx.mic_inductives) (fn (subject_value : Value) =>
                                match term_free_var_name meta_ref {
                                    Option.none => Result.err (String.concat (show_identifier name)
                                        "!: second argument must name a top-level def"),
                                    Option.some meta_name =>
                                        result_bind
                                            (meta_eval_invoke ctx.mic_dispatched (single_name_path meta_name) subject_value)
                                            (fn (result_value : Value) =>
                                                match reify_value_to_term result_value {
                                                    Result.err message => Result.err (String.concat (show_identifier name) (String.concat "!: " message)),
                                                    Result.ok term => Result.ok term,
                                                }),
                                }),
                        List.cons _ _ => Result.err (String.concat (show_identifier name) "! expects 2 arguments (a subject and a meta-function name)"),
                    },
                List.empty => Result.err (String.concat (show_identifier name) "! expects 2 arguments (a subject and a meta-function name)"),
            },
        List.empty => Result.err (String.concat (show_identifier name) "! expects 2 arguments (a subject and a meta-function name)"),
    }

def single_name_path (name : String) : NamePath :=
    NamePath.mk (List.cons (Identifier.id name) List.empty)

/// The single reflection step, whatever the position: a string literal
/// reflects to itself; a plain type name reflects to its `TypeInfo`.
def reflect_subject (name : Identifier) (subject : Term) (inds : List Inductive) : Result String Value :=
    reflect_stripped name (strip_term_ctx subject) inds

def reflect_stripped (name : Identifier) (stripped : Term) (inds : List Inductive) : Result String Value :=
    match stripped {
        Term.lit l => reflect_literal_subject name l stripped inds,
        _ => reflect_type_subject name stripped inds,
    }

def reflect_literal_subject (name : Identifier) (l : Literal) (stripped : Term) (inds : List Inductive) : Result String Value :=
    match l {
        Literal.str value => Result.ok (str_val value),
        _ => reflect_type_subject name stripped inds,
    }

def reflect_type_subject (name : Identifier) (stripped : Term) (inds : List Inductive) : Result String Value :=
    match term_free_var_name stripped {
        Option.none => Result.err (String.concat (show_identifier name)
            "!: first argument must be a string literal or a type name"),
        Option.some type_name =>
            match find_inductive_by_bare_name inds type_name {
                Option.none => Result.err (String.concat (show_identifier name)
                    (String.concat "!: unknown type " type_name)),
                Option.some ind =>
                    match build_type_info_value ind {
                        Result.err e => Result.err e,
                        Result.ok v => Result.ok v,
                    },
            },
    }

/// Detection-only walk: `Result.err` as soon as a term-position macro call
/// the whole-graph pass could still expand appears — an intrinsic, or any
/// name the graph-wide registry knows. Reuses the Result traversal's
/// short-circuit rather than adding a second scan pass.
#[partial]
pub def scan_live_call (lookup : Identifier -> Option Term) (t : Term) : Result String Term :=
    match t {
        Term.app _ _ =>
            match macro_call_head t {
                Option.some name =>
                    if is_intrinsic_ident name then Result.err "found"
                    else
                        match lookup name {
                            Option.some _ => Result.err "found",
                            Option.none => term_map_children_result (scan_live_call lookup) t,
                        },
                Option.none => term_map_children_result (scan_live_call lookup) t,
            },
        _ => term_map_children_result (scan_live_call lookup) t,
    }

pub def term_has_live_call (lookup : Identifier -> Option Term) (t : Term) : Bool :=
    match scan_live_call lookup t {
        Result.ok _ => false,
        Result.err _ => true,
    }

/// Short-circuiting map over a term list, in order.
#[partial]
def map_terms_result (f : Term -> Result String Term) (ts : List Term) : Result String (List Term) :=
    match ts {
        List.empty => Result.ok List.empty,
        List.cons x rest =>
            result_bind (f x) (fn (x2 : Term) =>
                result_bind (map_terms_result f rest) (fn (rest2 : List Term) =>
                    Result.ok (List.cons x2 rest2))),
    }

// ─── The pure entry points ────────────────────────────────────────────

/// The per-file walk `macro_queue.mo` uses: no evaluation environment, so
/// an intrinsic is left in place. A depth-limit failure (a macro that
/// expands into itself) leaves the term unexpanded; the whole-graph pass
/// is where that becomes a diagnostic.
#[partial]
pub def expand_term (lookup : Identifier -> Option Term) (t : Term) : Term :=
    match expand_term_go lookup Option.none 0 t {
        Result.ok expanded => expanded,
        Result.err _ => t,
    }

#[partial]
pub def resolve_quote (lookup : Identifier -> Option Term) (t : Term) : Term :=
    match resolve_quote_go lookup Option.none 0 t {
        Result.ok expanded => expanded,
        Result.err _ => t,
    }

/// The whole-graph entry point: ordinary macros plus the term-position
/// `meta!`/`reflect_type_info!` intrinsic, with real error propagation.
pub def expand_term_with_meta
    (lookup : Identifier -> Option Term)
    (ctx : MetaIntrinsicCtx)
    (t : Term) : Result String Term :=
    expand_term_go lookup (Option.some ctx) 0 t

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built lookup functions + `Term` fixtures, no pipeline wiring.

def double_ident : Identifier := Identifier.id "double"

#[partial]
def term_type_level (t : Term) : I64 :=
    match t {
        // A sort with an unresolved level (a `var`, or a `succ`/`max` over
        // one) has no I64 to report, so it answers the free-variable
        // sentinel rather than a guessed level.
        Term.sort l => match level_const l {
            Option.some n => n,
            Option.none => sentinel,
        },
        // A private test-canary helper: decodes a `Term.sort N` canary
        // value after it has run through the transformation under test.
        // Any other shape has no level to report either, so it is the
        // same "nothing to report" sentinel, not a guess.
        _ => sentinel,
    }

/// `defmacro double x := x` -- the one real `lang/parser.mo` test
/// fixture shape this whole module is built to expand correctly.
def double_body : Term := Term.lam binder_anon Term.hole (Term.var 0 DebugName.unnamed)

def no_macros_lookup (id : Identifier) : Option Term := Option.none

def double_lookup (id : Identifier) : Option Term :=
    if id_eq id double_ident then Option.some double_body else Option.none

/// `defmacro quoted_double x := quote { x }` — the shape a real
/// `quote`-bodied term macro (`fmt`) has. Applying it must yield `x`
/// itself, not a `quote_` wrapper (syntax-as-data).
def quoted_double_ident : Identifier := Identifier.id "quoted_double"

def quoted_double_body : Term := Term.lam binder_anon Term.hole (Term.quote_ (Term.var 0 DebugName.unnamed))

def quoted_double_lookup (id : Identifier) : Option Term :=
    if id_eq id quoted_double_ident then Option.some quoted_double_body else Option.none

#[test]
def test_macro_call_head_recognizes_var_macro_spine : Bool :=
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.sort (SortLevel.concrete 1)) in
    match macro_call_head call {
        Option.some id => id_eq id double_ident,
        Option.none => false,
    }

#[test]
def test_macro_call_head_none_for_ordinary_app : Bool :=
    let call : Term := Term.app (Term.var 0 DebugName.unnamed) (Term.sort (SortLevel.concrete 1)) in
    match macro_call_head call {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_spine_args_collects_left_to_right : Bool :=
    // `f a b c` == `App(App(App(f, a), b), c)` -- args must come back
    // in the order they were originally supplied, not reversed.
    let f : Term := Term.var_macro (0 - 1) (DebugName.named double_ident) in
    let a : Term := Term.sort (SortLevel.concrete 1) in
    let b : Term := Term.sort (SortLevel.concrete 2) in
    let c : Term := Term.sort (SortLevel.concrete 3) in
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
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.sort (SortLevel.concrete 9)) in
    I64.beq (term_type_level (expand_term double_lookup call)) 9

#[test]
def test_expand_term_unwraps_a_quote_bodied_macro : Bool :=
    // `quoted_double! 7` -- a `quote`-bodied term macro (the shape `fmt`
    // has) expands to its inside, NOT to a `quote_` node. The reference
    // requires and strips the quote (`apply_macro`); leaving it wrapped
    // hands the checker syntax-as-data and fails.
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named quoted_double_ident)) (Term.sort (SortLevel.concrete 7)) in
    match expand_term quoted_double_lookup call {
        // The expansion is exactly the substituted argument, not a
        // `quote_` around it.
        Term.sort l => match level_const l {
            Option.some n => I64.beq n 7,
            Option.none => false,
        },
        _ => false,
    }

// ── The term-position meta intrinsic ──
//
// These stay short of a real evaluation: building a dispatched decl list
// that defines a meta function is the end-to-end test's job
// (`slow_tests/src/fmt_macro_tests.mo`), which is also what proves a real
// `Expr` comes back. Here the reflection step and the arity/error
// plumbing are pinned.

def empty_meta_ctx : MetaIntrinsicCtx := {
    mic_dispatched := List.empty,
    mic_inductives := List.empty,
}

def meta_ident : Identifier := Identifier.id "meta"

def echo_meta_term : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "echo_meta"))

#[test]
def test_meta_intrinsic_requires_two_args : Bool :=
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named meta_ident)) (Term.lit (Literal.str "hi")) in
    match expand_term_with_meta no_macros_lookup empty_meta_ctx call {
        Result.err message => String.contains message "expects 2 arguments",
        Result.ok _ => false,
    }

#[test]
def test_meta_intrinsic_rejects_an_unreflectable_subject : Bool :=
    let subject : Term := Term.sort (SortLevel.concrete 0) in
    let call : Term := Term.app (Term.app (Term.var_macro (0 - 1) (DebugName.named meta_ident)) subject) echo_meta_term in
    match expand_term_with_meta no_macros_lookup empty_meta_ctx call {
        Result.err message => String.contains message "first argument",
        Result.ok _ => false,
    }

#[test]
def test_meta_intrinsic_reflects_a_string_subject_then_evaluates : Bool :=
    // A string literal is a valid subject, so expansion gets as far as
    // invoking the named def; with an empty dispatched list that fails
    // in lowering, which is the proof the reflection step accepted it.
    let call : Term := Term.app (Term.app (Term.var_macro (0 - 1) (DebugName.named meta_ident)) (Term.lit (Literal.str "hi"))) echo_meta_term in
    match expand_term_with_meta no_macros_lookup empty_meta_ctx call {
        Result.err message => String.contains message "failed to lower",
        Result.ok _ => false,
    }

#[test]
def test_expand_term_passes_through_unknown_macro_name : Bool :=
    // An unresolved macro name is NOT an error -- structurally
    // recursed into (its own arg still gets expanded) and left as an
    // unexpanded `Term.app`/`Term.var_macro` call.
    let unknown : Identifier := Identifier.id "unknown_macro" in
    let inner_call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.sort (SortLevel.concrete 4)) in
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named unknown)) inner_call in
    match expand_term double_lookup call {
        Term.app callee arg =>
            (match callee { Term.var_macro _ dbg => match dbg { DebugName.named id => id_eq id unknown, DebugName.unnamed => false }, _ => false }) &&
            I64.beq (term_type_level arg) 4,
        _ => false,
    }

#[test]
def test_expand_term_recurses_under_lambda : Bool :=
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.sort (SortLevel.concrete 6)) in
    let t : Term := Term.lam binder_anon Term.hole call in
    match expand_term double_lookup t {
        Term.lam _ _ body => I64.beq (term_type_level body) 6,
        _ => false,
    }

#[test]
def test_expand_term_no_macro_calls_structural_noop : Bool :=
    let t : Term := Term.app (Term.var 0 DebugName.unnamed) (Term.sort (SortLevel.concrete 2)) in
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
    let inner : Term := Term.app unquote_ref (Term.sort (SortLevel.concrete 13)) in
    I64.beq (term_type_level (resolve_quote no_macros_lookup inner)) 13

#[test]
def test_resolve_quote_expands_macro_call_inside_quote : Bool :=
    // A macro call written directly inside a quoted body (not wrapped
    // in `unquote`) is ALSO expanded right there -- matches the
    // reference exactly.
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named double_ident)) (Term.sort (SortLevel.concrete 21)) in
    I64.beq (term_type_level (resolve_quote double_lookup call)) 21

#[test]
def test_resolve_quote_leaves_nested_quote_wrapped : Bool :=
    let inner_quote : Term := Term.quote_ (Term.sort (SortLevel.concrete 8)) in
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
    let quoted : Term := Term.quote_ (Term.app unquote_ref (Term.sort (SortLevel.concrete 17))) in
    match expand_term no_macros_lookup quoted {
        Term.quote_ inner => I64.beq (term_type_level inner) 17,
        _ => false,
    }
