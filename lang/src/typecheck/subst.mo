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
/// template's own top-level decl_list have no enclosing lambda binder, so
/// a macro param referenced inside one is an ordinary FREE/qualified
/// `Term.var sentinel (DebugName.named X)` reference, not a bound de
/// Bruijn index. That form needs a separate, NAME-based substitution
/// (mirroring the reference's own `subst_macro`/`subst_decl_var` much
/// more directly) — a different module, not this one.
use lang::types {
  Con, Cubical, FieldPattern, Literal, MatchCase, Native, StructLitField, Term,
  binder_anon, concrete, cub_ineg, id, level_const, sentinel, unnamed,
}

use lib::typecheck::traverse {term_map_children_at_depth}

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
        // Everything else is ordinary structural recursion; the shared
        // combinator hands back how many binders each child sits under
        // (1 for a lam/forall/pi BODY, 0 everywhere else).
        _ => term_map_children_at_depth (fn (under : I64) => fn (child : Term) => term_shift_go d (cutoff + under) child) t,
    }


// ─── Permutation ─────────────────────────────────────────────────────
//
// `term_permute` -- `plans/implementations/struct-field-destructuring.md`'s
// Phase 7, needed for the SAME reason the Rust reference's own
// `core_term::permute_binders` is: a field-pattern match case's body
// (`{ x, y } => ...`) is de-Bruijn-indexed once, at PARSE time
// (`match_case_field_pattern_arrow`, `lang/parser.mo`, Phase 6), against
// the pattern's own WRITTEN field order -- the only order knowable that
// early, since this file's canonical `Term` is de Bruijn from the parser
// itself (unlike the reference's separate parse-then-lower split). The
// runtime, however, always binds a matched constructor's fields
// POSITIONALLY in its DECLARED order (`lang/lower_core_ir.mo`'s
// `lower_one_match_arm`, mirroring `core_eval.rs`'s own documented
// convention) -- which is only knowable once `type_check_match_case`
// resolves the real target constructor, by which point the body's
// indices are already fixed relative to written order.
// `term_permute` bridges the two: given the resolved written-order ->
// declared-order mapping, it retargets the ALREADY-INDEXED body from
// written order onto declared order directly.
//
// `old_depths`/`new_depths` are two PARALLEL lists (not a `Pair`-keyed
// assoc list, avoiding a cross-module dependency for this file's own
// canonical machinery, same reason `lang/types.mo`'s own
// `FieldPatternEntry` avoids a generic `Pair`) -- `old_depths[i]` maps to
// `new_depths[i]` for each `i`; a `Bound` matching neither (its absolute
// index minus `cutoff` isn't in `old_depths` at all) falls through to the
// generic "outer reference" shift case unconditionally, since every
// permuted frame's OWN written-order slot is always present in
// `old_depths` by construction (the caller builds both lists from the
// SAME already-validated `written_to_declared` resolution).

def term_permute (old_n : I64) (new_n : I64) (old_depths : List I64) (new_depths : List I64) (t : Term) : Term :=
    term_permute_go old_n new_n old_depths new_depths 0 t

#[partial]
def term_permute_go (old_n : I64) (new_n : I64) (old_depths : List I64) (new_depths : List I64) (cutoff : I64) (t : Term) : Term :=
    match t {
        Term.var idx dbg =>
            if I64.lt idx cutoff then Term.var idx dbg
            else if I64.lt idx (cutoff + old_n) then
                let local : I64 := idx - cutoff in
                Term.var (cutoff + (permute_lookup local old_depths new_depths)) dbg
            else
                Term.var (idx + (new_n - old_n)) dbg,
        Term.var_macro idx dbg =>
            if I64.lt idx cutoff then Term.var_macro idx dbg
            else if I64.lt idx (cutoff + old_n) then
                let local : I64 := idx - cutoff in
                Term.var_macro (cutoff + (permute_lookup local old_depths new_depths)) dbg
            else
                Term.var_macro (idx + (new_n - old_n)) dbg,
        _ => term_map_children_at_depth (fn (under : I64) => fn (child : Term) => term_permute_go old_n new_n old_depths new_depths (cutoff + under) child) t,
    }


/// `local`'s remapped position, or `local` unchanged if not found in
/// `old_depths` (see this section's own doc comment for why that
/// shouldn't happen for a well-formed call, but a safe identity
/// fallback is cheap insurance regardless).
#[partial]
def permute_lookup (local : I64) (old_depths : List I64) (new_depths : List I64) : I64 :=
    match old_depths {
        List.cons od rest_old =>
            match new_depths {
                List.cons nd rest_new =>
                    if I64.beq od local then nd else permute_lookup local rest_old rest_new,
                List.empty => local,
            },
        List.empty => local,
    }

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
        _ => term_map_children_at_depth (fn (under : I64) => fn (child : Term) => term_subst_go j s (depth + under) child) t,
    }


// ─── Abstraction (core-term-simplification.md R4b) ────────────────────
//
// `term_abstract_var j t` is `term_subst`'s dual: instead of replacing a
// bound occurrence with a term, it closes one OVER a fresh outer binder --
// what `type_check_elim_motive` (R4) needs a CALLER to hand it when the
// motive isn't given explicitly but must be derived from a dependent
// expected type that mentions the scrutinee as an ordinary bound variable
// (`core-term-simplification.md`'s R4b: `Sigma.snd`'s declared
// `B (Sigma.fst p)` needs `fn q => B (Sigma.fst q)`, i.e. `p` -- a plain
// `Term.var` -- abstracted out and rebound to the motive's own fresh
// argument). Every occurrence of `Term.var (j + depth)` (the variable
// being abstracted, re-targeted at the walk's current depth the same way
// `term_subst_go`'s `target` does) becomes `Term.var depth` (a reference
// to the brand-new OUTERMOST binder, at whatever depth the walk has
// reached); every occurrence with a STRICTLY GREATER index is shifted up
// by 1 (opening the gap the new binder needs, the mirror image of
// `term_subst`'s closing one); anything smaller is untouched, since it is
// bound more tightly than the thing being abstracted and the new binder
// sits outside that. The caller wraps the result in one `Term.lam`/
// `Term.pi` (`derive_motive`, `infer.mo`) -- this function only produces
// the body.
//
// Deliberately scoped to a single BOUND-VARIABLE scrutinee, not an
// arbitrary subterm: finding every occurrence of a general term (rather
// than one de Bruijn index) is a different, harder operation (structural
// matching under binders, since the target term's own free variables
// shift as the walk descends) that no caller needs yet -- `Sigma.snd`'s
// own scrutinee `p` is exactly a bound variable, the common shape for
// "the thing being eliminated is a `match`'s own operand or a def's own
// parameter." Recorded in `core-term-simplification.md`'s R4b detail as
// the scope line, not silently assumed to generalize.
def term_abstract_var (j : I64) (t : Term) : Term := term_abstract_var_go j 0 t

#[partial]
def term_abstract_var_go (j : I64) (depth : I64) (t : Term) : Term :=
    let target : I64 := j + depth in
    match t {
        Term.var idx dbg =>
            if I64.beq idx target then Term.var depth dbg
            else if I64.gt idx target then Term.var (idx + 1) dbg
            else Term.var idx dbg,
        Term.var_macro idx dbg =>
            if I64.beq idx target then Term.var_macro depth dbg
            else if I64.gt idx target then Term.var_macro (idx + 1) dbg
            else Term.var_macro idx dbg,
        _ => term_map_children_at_depth (fn (under : I64) => fn (child : Term) => term_abstract_var_go j (depth + under) child) t,
    }

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

// Private test-canary helpers: decode a hand-built `Term.var N`/
// `Term.sort N` canary value after it has run through the transformation
// under test. Any other shape has nothing to report, so each answers the
// same free-variable sentinel `term_type_level`'s own `Option.none`
// branch already establishes, not a guess.
#[partial]
def term_var_idx (t : Term) : I64 :=
    match t {
        Term.var idx _ => idx,
        _ => sentinel,
    }

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
        _ => sentinel,
    }

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
    let t : Term := Term.lam binder_anon (Term.sort (SortLevel.concrete 1)) (Term.var 0 DebugName.unnamed) in
    match term_shift 5 t {
        Term.lam _ _ body => I64.beq (term_var_idx body) 0,
        _ => false,
    }

#[test]
def test_term_shift_free_var_under_lam_shifted : Bool :=
    // `Term.var 1` inside that same lambda's body refers to something
    // OUTSIDE it (cutoff 1, idx 1 >= cutoff) -- this one must shift.
    let t : Term := Term.lam binder_anon (Term.sort (SortLevel.concrete 1)) (Term.var 1 DebugName.unnamed) in
    match term_shift 5 t {
        Term.lam _ _ body => I64.beq (term_var_idx body) 6,
        _ => false,
    }

#[test]
def test_term_subst_replaces_target_index : Bool :=
    // `term_subst 0 s t` on `t = Term.var 0` -- the exact target --
    // replaces wholesale with `s`.
    let s : Term := Term.sort (SortLevel.concrete 7) in
    let t : Term := Term.var 0 DebugName.unnamed in
    I64.beq (term_type_level (term_subst 0 s t)) 7

#[test]
def test_term_subst_lower_index_untouched : Bool :=
    // `term_subst 1 s t` on `t = Term.var 0` -- refers to something
    // MORE local than the binder being substituted away -- must be
    // left completely alone.
    let s : Term := Term.sort (SortLevel.concrete 7) in
    let t : Term := Term.var 0 DebugName.unnamed in
    I64.beq (term_var_idx (term_subst 1 s t)) 0

#[test]
def test_term_subst_closes_gap_for_higher_index : Bool :=
    // `term_subst 0 s t` on `t = Term.var 2` -- some OTHER free
    // variable further out than the one being substituted away --
    // must decrement by 1 to close the gap left by the removed binder.
    let s : Term := Term.sort (SortLevel.concrete 9) in
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
    let t : Term := Term.lam binder_anon (Term.sort (SortLevel.concrete 1)) (Term.var 1 DebugName.unnamed) in
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
    let no_fp : Option FieldPattern := Option.none in
    let outer_ref : MatchCase :=
        MatchCase.mk (Identifier.id "some") (List.cons (Identifier.id "a") (List.cons (Identifier.id "b") List.empty)) (Term.var 2 DebugName.unnamed) no_fp Option.none in
    let bound_ref : MatchCase :=
        MatchCase.mk (Identifier.id "some") (List.cons (Identifier.id "a") (List.cons (Identifier.id "b") List.empty)) (Term.var 1 DebugName.unnamed) no_fp Option.none in
    // Asserted through the public `term_shift` entry point (the
    // per-node `match_case_shift` helper this used to call directly is
    // now `traverse.mo`'s shared `match_case_map_children_at_depth`).
    // Wrapping each arm in a real `Literal.match_` exercises the same
    // binder arithmetic end-to-end.
    let scrut : Term := Term.hole in
    let shift_arm_body : MatchCase -> I64 :=
        fn (arm : MatchCase) =>
            match term_shift 3 (Term.lit (Literal.match_ scrut (List.cons arm List.empty))) {
                Term.lit l =>
                    match l {
                        Literal.match_ _ cases =>
                            match cases {
                                List.cons c _ => match c { MatchCase.mk _ _ body _ _ => term_var_idx body },
                                List.empty => 0 - 1,
                            },
                        _ => 0 - 1,
                    },
                _ => 0 - 1,
            } in
    I64.beq (shift_arm_body outer_ref) 5 && I64.beq (shift_arm_body bound_ref) 1

// -------------------------------------------------------------------
// `term_permute` (`plans/implementations/struct-field-destructuring.md`'s
// Phase 7).
// -------------------------------------------------------------------

#[test]
def test_term_permute_swaps_two_written_order_bindings : Bool :=
    // Written `{ a, b }` (a first, b second -- b ends up innermost,
    // depth 0, per this file's own "last-written innermost" push
    // convention, same as `test_match_case_binder_depth_shift` above).
    // Declared order is the OPPOSITE (b first, a second):
    // `written_to_declared = [1, 0]` (written slot 0 = "a" -> declared
    // position 1; written slot 1 = "b" -> declared position 0).
    let old_depths : List I64 := [1, 0] in
    let new_depths : List I64 := [0, 1] in
    // "b" (old depth 0, innermost) must move OUT to new depth 1 (b is
    // now declared FIRST, i.e. outermost of the two).
    let b_ref : Term := Term.var 0 DebugName.unnamed in
    // "a" (old depth 1) must move IN to new depth 0 (a is now declared
    // SECOND, innermost).
    let a_ref : Term := Term.var 1 DebugName.unnamed in
    I64.beq (term_var_idx (term_permute 2 2 old_depths new_depths b_ref)) 1
        && I64.beq (term_var_idx (term_permute 2 2 old_depths new_depths a_ref)) 0

#[test]
def test_term_permute_shifts_outer_reference_unchanged_when_arity_matches : Bool :=
    // An occurrence OUTSIDE this frame entirely (old_n = new_n = 2, so
    // no width change) must be left completely untouched.
    let old_depths : List I64 := [1, 0] in
    let new_depths : List I64 := [0, 1] in
    let outer_ref : Term := Term.var 2 DebugName.unnamed in
    I64.beq (term_var_idx (term_permute 2 2 old_depths new_depths outer_ref)) 2

#[test]
def test_term_permute_widens_frame_for_rest_and_shifts_outer_refs : Bool :=
    // Only "a" was written (`{ a, .. }`), old_n = 1; the real
    // constructor has 2 declared fields, new_n = 2, "a" resolved to
    // declared position 1 (the discarded field is declared position 0).
    // "a" itself (old depth 0) maps to new depth 0 (still innermost,
    // since it's the LAST declared field here) -- an OUTER reference
    // (old depth >= old_n = 1) must shift by (new_n - old_n) = 1 to
    // still reach the same outer binder now that the frame is wider.
    let old_depths : List I64 := [0] in
    let new_depths : List I64 := [0] in
    let a_ref : Term := Term.var 0 DebugName.unnamed in
    let outer_ref : Term := Term.var 1 DebugName.unnamed in
    I64.beq (term_var_idx (term_permute 1 2 old_depths new_depths a_ref)) 0
        && I64.beq (term_var_idx (term_permute 1 2 old_depths new_depths outer_ref)) 2

#[test]
def test_beta_reduce_replaces_bound_occurrence : Bool :=
    // `beta_reduce body arg` where `body` is exactly `Term.var 0`
    // (the lambda's own bound occurrence, already peeled) must
    // replace it wholesale with `arg`.
    let arg : Term := Term.sort (SortLevel.concrete 3) in
    I64.beq (term_type_level (beta_reduce (Term.var 0 DebugName.unnamed) arg)) 3

#[test]
def test_beta_reduce_closes_gap_for_outer_reference : Bool :=
    // `body = Term.var 1` refers to something one level further OUT
    // than the lambda's own param -- after beta-reducing away that
    // lambda, the reference must shift down by exactly 1 to still
    // point at the same outer binding.
    let arg : Term := Term.sort (SortLevel.concrete 3) in
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
    let arg : Term := Term.sort (SortLevel.concrete 42) in
    let peeled_body : Term :=
        Term.lam binder_anon (Term.sort (SortLevel.concrete 1)) (Term.app (Term.var 1 DebugName.unnamed) (Term.var 0 DebugName.unnamed)) in
    match beta_reduce peeled_body arg {
        Term.lam _ _ inner =>
            match inner {
                Term.app callee remaining_arg =>
                    I64.beq (term_type_level callee) 42 && I64.beq (term_var_idx remaining_arg) 0,
                _ => false,
            },
        _ => false,
    }

/// A cubical primitive introduces NO binder, so every argument sits at the
/// node's own depth and a free variable inside one shifts like any other.
///
/// This is the pin on the claim that lets `term_shift`/`term_subst`/
/// `term_permute` stay untouched by the cubical fragment: a path abstraction
/// is an ordinary `Term.lam` with an `I`-typed binder, so dimension
/// variables are counted by the `lam` arm and nothing needs a second index
/// space. If a future primitive ever DOES bind, this test is what fails.
#[test]
def test_term_shift_through_cubical_arg_is_depth_zero : Bool :=
    let t : Term := cub_ineg (Term.var 0 DebugName.unnamed) in
    match term_shift 3 t {
        Term.cubical c => match c {
            { prim := _, args := args } => match args {
                List.cons a rest =>
                    if List.is_empty rest then I64.beq (term_var_idx a) 3 else false,
                List.empty => false,
            },
        },
        _ => false,
    }

/// The companion: under a `lam`, a cubical argument's `var 0` refers to that
/// lambda's binder and must NOT shift -- so the cubical node really is
/// transparent to depth rather than resetting it.
#[test]
def test_term_shift_cubical_under_lam_respects_the_binder : Bool :=
    let inner : Term := cub_ineg (Term.var 0 DebugName.unnamed) in
    let t : Term := Term.lam binder_anon (Term.sort (SortLevel.concrete 1)) inner in
    match term_shift 5 t {
        Term.lam _ _ body => match body {
            Term.cubical c => match c {
                { prim := _, args := args } => match args {
                    List.cons a _ => I64.beq (term_var_idx a) 0,
                    List.empty => false,
                },
            },
            _ => false,
        },
        _ => false,
    }

// ─── Abstraction (core-term-simplification.md R4b) ────────────────────

#[test]
def test_term_abstract_var_replaces_target_with_new_binder_ref : Bool :=
    // `Term.app (Term.var 0) (Term.var 1)`, abstracting index 0 (the
    // `app`'s own left arm, playing `Sigma.snd`'s own scrutinee `p`):
    // the target occurrence becomes `Term.var 0` (the brand-new OUTER
    // binder, at depth 0 since there's no intervening binder here), and
    // the OTHER reference (index 1, something outside the thing being
    // abstracted) shifts up by 1 to stay pointed at the same binding now
    // that a new binder sits in front of it.
    let t : Term := Term.app (Term.var 0 DebugName.unnamed) (Term.var 1 DebugName.unnamed) in
    match term_abstract_var 0 t {
        Term.app a b => I64.beq (term_var_idx a) 0 && I64.beq (term_var_idx b) 2,
        _ => false,
    }

#[test]
def test_term_abstract_var_leaves_inner_binder_untouched : Bool :=
    // Under a `lam`, `Term.var 0` refers to THAT lambda's own binder, not
    // the thing being abstracted from outside it -- it must stay exactly
    // `Term.var 0`, the same "idx < target" untouched case `term_subst_go`
    // has for the variable below the one it's substituting.
    let t : Term := Term.lam binder_anon Term.hole (Term.var 0 DebugName.unnamed) in
    match term_abstract_var 0 t {
        Term.lam _ _ body => I64.beq (term_var_idx body) 0,
        _ => false,
    }

#[test]
def test_term_abstract_var_targets_correct_depth_under_binder : Bool :=
    // Under one `lam`, `Term.var 1` refers OUTSIDE it -- to the same
    // external variable (index 0 at depth 0) being abstracted. The walk's
    // `depth` (1, from crossing the `lam`) is what the occurrence must
    // retarget to: the new outer binder, seen from one level inside the
    // intervening `lam`, is `Term.var 1`, not `Term.var 0` (which would
    // wrongly claim the `lam`'s OWN binder instead).
    let t : Term := Term.lam binder_anon Term.hole (Term.var 1 DebugName.unnamed) in
    match term_abstract_var 0 t {
        Term.lam _ _ body => I64.beq (term_var_idx body) 1,
        _ => false,
    }

#[test]
def test_term_abstract_var_then_subst_back_recovers_the_original : Bool :=
    // Round-trip: abstracting index 0 out and then substituting the SAME
    // reference back in for the new binder must reproduce the original
    // free-variable reference exactly -- `derive_motive`'s whole point is
    // that `Term.app motive scrutinee` type-checks against the ORIGINAL
    // expected type, which only holds if this round-trip holds.
    let outer_ref : Term := Term.var 1 DebugName.unnamed in
    let abstracted : Term := term_abstract_var 0 outer_ref in
    I64.beq (term_var_idx (term_subst 0 (Term.var 0 DebugName.unnamed) abstracted)) 1
