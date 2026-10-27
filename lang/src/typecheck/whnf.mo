use std::list {List.length}
use lib::types {
  Con, Cubical, CubicalPrim, DebugName, Elim, Identifier, InductConstructor,
  Literal, LocalScope, MatchCase, NamePath, NameRef, Scope, Similar, Term,
  cub_face_eq0, cub_face_eq1, cub_i0, cub_i1, cub_it_is_one, cubical_arity, cubical_prim_eq, id_eq,
  show_identifier, sentinel, term_peel,
}
use lib::scope {
  CallSpine, flatten_call_spine, last_dot_index, scope_find_cubical_prim, scope_find_def_body,
  scope_find_inductive, scope_find_inductive_by_constructor, scope_find_local,
  scope_resolve_name,
}
use lib::typecheck::faces {face_decide}
use lib::typecheck::subst {beta_reduce, term_shift, term_subst}

// ─── Weak-head normal form ───────────────────────────────────────────
//
// Conversion checking: two types are definitionally equal when they
// REDUCE to the same thing, not only when they are written the same
// way. `lang/typecheck/unify.mo` compares `Term`s structurally, so a
// declared type that is still an unreduced application (`identity_type
// foo`) never gets compared against what it computes to (`Bool`). This
// module supplies the missing reduction step; `unify` calls it only
// after a structural comparison has already failed, so the happy path
// pays nothing.
//
// Four reduction rules, which is what conversion checking at this stage
// needs:
//
//   beta   `(fn x => body) arg`  ->  `body[x := arg]`
//   delta  a free `Term.var` naming a global def  ->  that def's body
//   iota   `match c { K xs => body }` (c a KNOWN constructor
//          application) -> `body[xs := c's fields]`; same for `if` on
//          `Bool.true`/`Bool.false`
//   demorgan  the interval's lattice simplifications (Stage 1 step 5,
//          `whnf_cubical` below): `ineg i0 -> i1`, `imeet i1 j -> j`, ...
//
// Beta and delta are needed together, and neither is useful alone
// here: a type-level application like `identity_type foo` is headed by
// a FREE variable, not a `Term.lam`, so beta has nothing to fire on
// until delta has unfolded the head into the `Term.lam` chain a `def`'s
// body actually is (`def_params_of_term`, `lang/scope.mo`). Iota sits on
// top of both: a scrutinee like `f P.p0` only becomes a constructor
// application after delta and beta have had their turn.
//
// Iota is the delicate one because `Literal.match_`'s arms are a
// binding form that binds `List.length args` de Bruijn levels at once
// (AGENTS.md item 22) -- substituting several levels simultaneously is
// where this kind of code goes subtly wrong; see
// `whnf_subst_case_fields`'s own doc comment for the exact trap.
//
// Iota is also step 1 of the eliminator roadmap recorded in
// `plans/type-system/match-to-recursor.md`: iota -> dependent index
// refinement -> `Eq.rec` as a real def -> optionally generating `T.rec`
// per inductive. Converting `match` to recursors would need this same
// reduction machinery (a primitive recursor reduces by a MORE complex
// rule than this arm), so this arm is the cheap half of that path
// either way.
//
// There is no metavariable handling here because this checker has no
// metavariables: `Term.hole` is a matches-anything wildcard, not a
// solvable meta (see `unify`'s own `Term.hole` arms). A reducer for a
// checker WITH metas would have to avoid committing to a reduction
// path before they are solved.

/// Default step budget. Conversion checking needs a handful of steps --
/// unfold a type-level def, beta it, look at the head -- so this is
/// generous rather than tight. It is a bound on DIVERGENCE, not a
/// tuning knob: the self-hosted compiler has no termination checker
/// yet, and `#[partial]` is applied to ~2000 defs in this tree, so
/// nothing verifies that an unfolded body terminates. Running out of
/// fuel is not an error -- reduction simply stops and the term is
/// compared in whatever form it reached, which is exactly the
/// (conservative) behaviour this had before reduction existed.
def whnf_fuel : I64 := 64

/// Reduce `t` to weak-head normal form: keep reducing at the HEAD until
/// the head is rigid (a `pi`, a sort, a literal, a constructor, a
/// variable with no body, ...). Sub-terms are left alone -- the head is
/// all a structural comparison looks at before recursing, and each
/// recursive step goes back through `unify`, which reduces again.
///
/// `pub` because the Stage 3 reducer pins
/// (`proofs/src/checker/cubical_props.mo`) observe the cubical
/// reductions directly, not only through `type_check` -- the
/// constant-family/variable-family distinction lives here and nowhere
/// else.
pub def whnf (scope : Scope) (locals : LocalScope) (t : Term) : Term :=
    whnf_go whnf_fuel scope locals t

/// `#[partial]`: fuel-bounded, but the decrement is not a structural
/// subterm the checker can see.
#[partial]
def whnf_go (fuel : I64) (scope : Scope) (locals : LocalScope) (t0 : Term) : Term :=
    // Peel `Term.ctx` here rather than at each arm: a located wrapper
    // would otherwise fall through to the rigid-head case and stop
    // reduction dead, silently.
    let t : Term := term_peel t0 in
    if I64.lt fuel 1 then
        t
    else
        match t {
            Term.app f a =>
                // Reducing `f` recursively is what handles a spine of
                // any length: `f g x` reduces `f g` first, so a
                // multi-parameter def unfolds and betas one argument at
                // a time without collecting the spine explicitly.
                let f_r : Term := whnf_go (fuel - 1) scope locals f in
                match f_r {
                    Term.lam _dbg _typ body => whnf_go (fuel - 1) scope locals (beta_reduce body a),
                    // Stuck head. Keep the reduced head anyway -- it is
                    // no less reduced than what came in, and a caller
                    // comparing two stuck applications compares heads.
                    //
                    // ...but a SATURATED cubical-primitive call is not
                    // stuck: `type_check_app` rewrites `ineg i0` and
                    // `PathP L a b` into a `Term.cubical` at check time,
                    // and reduction has to reach the same canonical form
                    // or a type SPELLED as a def never compares equal to
                    // it. Measured: `Path A b a` delta-unfolds to an
                    // `PathP L b a` APPLICATION SPINE, so it never matched
                    // the `PathP` term the path rules echo back, and every
                    // `proofs/src/paths.mo` combinator was rejected ("type
                    // mismatch: expected (Path A b a), found (PathP (fn _
                    // => A) b a)").
                    _ =>
                        // A canonical `Term.cubical` is a REDUCIBLE head
                        // (the De Morgan arm below), so keep reducing it
                        // rather than returning it: `ineg i0` reached as a
                        // source spine should still come out `i1`.
                        let canonical : Term := as_cubical_type (Term.app f_r a) scope locals in
                        match canonical {
                            Term.cubical _c => whnf_go (fuel - 1) scope locals canonical,
                            _ => canonical,
                        },
                },
            Term.var idx dbg =>
                if I64.beq idx sentinel then
                    match whnf_delta scope locals dbg {
                        Option.some body => whnf_go (fuel - 1) scope locals body,
                        Option.none => t,
                    }
                else
                    // A bound de Bruijn variable. Its binder is outside
                    // this term, so there is nothing to unfold.
                    t,
            Term.lit l =>
                // Iota. A `match`/`if` reduces only when its scrutinee
                // has already reduced to a KNOWN constructor
                // application; anything else is rigid here exactly
                // like the heads below. The reduced scrutinee is kept
                // in the stuck case -- a caller comparing two stuck
                // matches then compares reduced scrutinees.
                match l {
                    Literal.match_ scrut cases =>
                        let scrut_r : Term := whnf_go (fuel - 1) scope locals scrut in
                        match whnf_iota_case scrut_r cases scope {
                            Option.some body => whnf_go (fuel - 1) scope locals body,
                            Option.none => Term.lit (Literal.match_ scrut_r cases),
                        },
                    Literal.if_ cond then_ else_ =>
                        let cond_r : Term := whnf_go (fuel - 1) scope locals cond in
                        match whnf_bool_con cond_r scope {
                            Option.some b =>
                                if b
                                then whnf_go (fuel - 1) scope locals then_
                                else whnf_go (fuel - 1) scope locals else_,
                            Option.none => Term.lit (Literal.if_ cond_r then_ else_),
                        },
                    // `str`/`char`/`num`/`flt` and the two deprecated
                    // struct forms are rigid. Already in WHNF.
                    _ => t,
                },
            // The interval's De Morgan lattice (Stage 1 step 5): a
            // cubical head is reducible, not rigid -- see the section
            // below this def.
            Term.cubical c => whnf_cubical (fuel - 1) scope locals c,
            // Iota on `Elim` (`core-term-simplification.md` R5): reduce
            // the scrutinee, then fire whichever minor its constructor
            // selects -- see the `whnf_elim_iota` section below. The
            // reduced scrutinee is kept in the stuck case, same
            // discipline as `Literal.match_`/`if_` above.
            Term.elim e =>
                let scrut_r : Term := whnf_go (fuel - 1) scope locals e.scrutinee in
                match whnf_elim_iota e scrut_r scope {
                    Option.some body => whnf_go (fuel - 1) scope locals body,
                    // `{ e with .. }`, not a positional `Elim.mk` rebuild
                    // (R4c's own `indices` field growth found this site --
                    // a positional call silently drops/misorders whatever
                    // field comes next; the update syntax carries every
                    // field through unchanged except the one named here).
                    Option.none =>
                        Term.elim { e with scrutinee := scrut_r },
                },
            // Rigid heads: `pi`, `forall`, `type_`, `sort`, `ntv`, `con`,
            // `hole`, and the two macro-only forms. Already in WHNF.
            //
            // `sort` is listed rather than matched: it is a leaf like
            // `type_`, so it belongs to this fallback. Nothing here
            // normalizes a LEVEL -- `level_le`/`level_normalize` handle
            // levels, and they are never reached through `whnf` (W1 is
            // built so that stays true; see `unify_sort`).
            _ => t,
        }

// ─── De Morgan lattice normalization (Stage 1 step 5) ────────────────
//
// The interval carries the free De Morgan algebra on dimension
// generators -- CCHM's cartesian cubes. Conversion of two dimension
// terms is syntactic identity (`Similar.similar`, which is what
// cartesian cubical type theory wants: interval conversion is DECIDED,
// never reduced to anything else), but only once both sides are in the
// form these rules compute. `imeet i1 j` and `j` are the same
// dimension, and nothing above `whnf` can see that until this step
// rewrites one to the other.
//
// The rules are the standard De Morgan simplifications, applied to
// ALREADY-REDUCED arguments -- arguments reduce first, so no rule ever
// fires on a still-reducible subterm and every step's result is built
// from pieces that are themselves in WHNF:
//
//   ineg i0       = i1
//   ineg i1       = i0
//   ineg (ineg i) = i            -- involutivity
//   imeet i0 _    = i0          -- the absorbing constant
//   imeet i1 j    = j           -- the unit
//   imeet i i     = i           -- idempotence
//   ijoin i1 _    = i1          -- dual of absorbing
//   ijoin i0 j    = j           -- dual of unit
//   ijoin i i     = i
//
// Deliberately absent: absorption (`imeet i (ijoin i j) = i`) and
// distribution. They are sound, but every rule here is one step at a
// SPINE head -- `whnf` is weak-head, and no argument position is ever
// re-entered -- while absorption has to look INSIDE an argument, which
// would make normalization quadratic in exchange for no conversion the
// current corpus asks of it. `sym (sym p) ≡ p` -- the one soundness pin
// Stage 2 has on this normalizer -- needs `ineg (ineg i) = i` and
// nothing more.
//
// Idempotence compares its two arguments with `Similar.similar`, which
// peels `Term.ctx` on both sides -- the debug-transparency property --
// and needs no scope: a dimension variable is a de Bruijn index, and
// two indices are similar or they are not.

/// Is `t` the bare, argument-free primitive `p`? `cubical_prim_eq` is
/// the dense-tag comparison (the `Term`-arm style rule), and arity 0 is
/// part of the test: a cubical term WITH arguments is a dimension
/// expression, not the constant the rules look for.
def whnf_term_is_bare_prim (t : Term) (p : CubicalPrim) : Bool :=
    match t {
        // Two-step match: a variant constructor with a single struct
        // payload has no field names at the constructor level, so the
        // payload match is its own `match` (verified -- the directly
        // nested form does not parse).
        Term.cubical c =>
            match c {
                { prim := q, args := as } => cubical_prim_eq q p && List.is_empty as,
            },
        _ => false,
    }

/// The De Morgan step for `ineg` on its single, already-reduced
/// argument, or `Option.none` when no rule applies.
def whnf_demorgan_ineg (i : Term) : Option Term :=
    match i {
        Term.cubical inner =>
            match inner {
                { prim := q, args := inner_as } =>
                    if cubical_prim_eq q CubicalPrim.i0 && List.is_empty inner_as then Option.some cub_i1
                    else if cubical_prim_eq q CubicalPrim.i1 && List.is_empty inner_as then Option.some cub_i0
                    else if cubical_prim_eq q CubicalPrim.ineg then
                        // Involutivity. The inner `ineg` must itself be
                        // well-formed (arity 1) -- `args` is
                        // arity-unchecked by design (smart constructors
                        // plus `type_check_cubical`), so a malformed
                        // inner term does not get to reduce.
                        match inner_as {
                            List.cons x rest => if List.is_empty rest then Option.some x else Option.none,
                            List.empty => Option.none,
                        }
                    else Option.none,
            },
        _ => Option.none,
    }

/// The De Morgan step `imeet` and `ijoin` share -- the two lattice
/// operations have the same shape of rule, parameterized by which
/// constant absorbs and which is the unit. For `imeet` the absorbing
/// constant is `i0` and the unit is `i1`; for `ijoin` the dual. Both
/// arguments are already reduced.
def whnf_demorgan_meet_join (left : Term) (right : Term)
    (absorbing : CubicalPrim) (unit : CubicalPrim) : Option Term :=
    if whnf_term_is_bare_prim left absorbing then Option.some left
    else if whnf_term_is_bare_prim left unit then Option.some right
    else if Similar.similar left right then Option.some left
    else Option.none

/// The De Morgan step for one primitive on already-reduced arguments,
/// or `Option.none` when no rule applies and the term is stuck. Arity
/// is checked before any rule fires, for the same reason as in
/// `whnf_demorgan_ineg`: a malformed `args` list is representable and
/// must not silently reduce.
def whnf_demorgan (c : Cubical) : Option Term :=
    match c {
        { prim := p, args := as } =>
            match p {
                CubicalPrim.ineg =>
                    match as {
                        List.cons i rest => if List.is_empty rest then whnf_demorgan_ineg i else Option.none,
                        List.empty => Option.none,
                    },
                CubicalPrim.imeet =>
                    match as {
                        List.cons i rest =>
                            match rest {
                                List.cons j rest2 =>
                                    if List.is_empty rest2
                                    then whnf_demorgan_meet_join i j CubicalPrim.i0 CubicalPrim.i1
                                    else Option.none,
                                List.empty => Option.none,
                            },
                        List.empty => Option.none,
                    },
                CubicalPrim.ijoin =>
                    match as {
                        List.cons i rest =>
                            match rest {
                                List.cons j rest2 =>
                                    if List.is_empty rest2
                                    then whnf_demorgan_meet_join i j CubicalPrim.i1 CubicalPrim.i0
                                    else Option.none,
                                List.empty => Option.none,
                            },
                        List.empty => Option.none,
                    },
                // The interval and the two endpoints carry no reduction.
                _ => Option.none,
            },
    }

/// Reduce every argument of a cubical term to WHNF, preserving order.
#[partial]
def whnf_cubical_args (fuel : I64) (scope : Scope) (locals : LocalScope) (as : List Term) : List Term :=
    match as {
        List.empty => List.empty,
        List.cons a rest =>
            List.cons (whnf_go (fuel - 1) scope locals a) (whnf_cubical_args (fuel - 1) scope locals rest),
    }

/// `transp A x` over a CONSTANT family: `A` is a lambda whose body does
/// not mention its dimension binder, so every `A i` is the same type
/// and transporting `x` there is `x` itself (Stage 3,
/// plans/type-system/univalence.md).
///
/// Constant is decided by substituting the two endpoints for the binder
/// and comparing: `body[i0/i]` and `body[i1/i]` differ exactly when the
/// binder occurs, because the two cubical endpoints are never similar
/// while everything else in the two results is identical. That reuses
/// `term_subst` -- the one walker over every `Term` constructor that
/// already tracks binder depth -- rather than adding a bespoke
/// free-variable walker, which would be one more constructor for a walk
/// to miss (the coverage check catches a miss since Phase 1 of
/// strict-exhaustiveness.md, but the point is not to add the arm at all).
///
/// Anything else stays STUCK, and that is a recorded limit, not an
/// omission: the structural reductions (a `Term.pi` family transported
/// domain-and-codomain separately, a `PathP` family structurally, an
/// inductive head by congruence over its fields) all need to build
/// lambdas or recurse over a type's constructors here, and the
/// inductive case is expressible only through a recursor -- R5 of
/// `core-term-simplification.md`. A stuck `transp` compares as itself,
/// which is sound: it only makes conversion LESS defined, never wrong.
def whnf_transp (c : Cubical) : Option Term :=
    match c {
        { prim := p, args := as } =>
            match cubical_prim_eq p CubicalPrim.transp {
                false => Option.none,
                true =>
                    // Nested constructor patterns do not parse; the two
                    // args are peeled one level at a time. The arity
                    // table (cubical_arity) already rejected any other
                    // count at formation, but whnf is also handed
                    // hand-built terms, so the peel answers none rather
                    // than assuming.
                    match as {
                        List.cons line rest =>
                            match rest {
                                List.cons elem rest2 =>
                                    match rest2 {
                                        List.empty =>
                                            match term_peel line {
                                                Term.lam _dbg _dom body =>
                                                    if Similar.similar
                                                        (term_subst 0 cub_i0 body)
                                                        (term_subst 0 cub_i1 body)
                                                    then Option.some elem
                                                    else Option.none,
                                                _ => Option.none,
                                            },
                                        _ => Option.none,
                                    },
                                _ => Option.none,
                            },
                        _ => Option.none,
                    },
            },
    }

/// The face-lattice step (Stage 4, `univalence.md`): the cofibration
/// generators on their single, already-reduced dimension, plus the one
/// contradiction law over a meet. Or `Option.none` when no rule applies
/// and the head is stuck.
///
/// Two rules are deliberately ABSENT, and the absence is soundness
/// rather than laziness. `ijoin (face_eq0 u) (face_eq1 u) = i1` would
/// say `u = 0 ∨ u = 1` holds everywhere -- CCHM POSTULATES the converse
/// (`isOne1 = 0`) precisely because it is not derivable, and a reducer
/// that folded the disjunction would prove, by conversion, that the
/// interval has exactly the two endpoint points. Likewise
/// `face_eq0 (imeet u v)` is not decomposed into
/// `ijoin (face_eq0 u) (face_eq0 v)`: the presheaf semantics of the
/// mixed law is not part of CCHM's cofibration quotient, so the term
/// stays stuck and `face_decide` (`faces.mo`) answers none.
///
/// A bare dimension is NOT a cofibration and this pass does not fire on
/// one: only the generators and their meet carry face-lattice meaning.
def whnf_face (c : Cubical) : Option Term :=
    match c {
        { prim := p, args := as } =>
            match p {
                CubicalPrim.face_eq0 =>
                    match as {
                        List.cons u rest =>
                            if List.is_empty rest then whnf_face_gen CubicalPrim.i0 cub_face_eq1 u else Option.none,
                        List.empty => Option.none,
                    },
                CubicalPrim.face_eq1 =>
                    match as {
                        List.cons u rest =>
                            if List.is_empty rest then whnf_face_gen CubicalPrim.i1 cub_face_eq0 u else Option.none,
                        List.empty => Option.none,
                    },
                CubicalPrim.imeet =>
                    // The one face rule on a lattice head: `u = 0` and
                    // `u = 1` together name the empty subobject, in
                    // either argument order. It lives here rather than
                    // in `whnf_demorgan` because reading the generators
                    // is face-lattice reasoning, not pure De Morgan.
                    match as {
                        List.cons left rest =>
                            match rest {
                                List.cons right rest2 =>
                                    if List.is_empty rest2 then whnf_face_contradicts left right else Option.none,
                                List.empty => Option.none,
                            },
                        List.empty => Option.none,
                    },
                // `ijoin` is deliberately absent -- see the pass doc.
                _ => Option.none,
            },
    }

/// The SATISFIED-face answer on its own, because it is the one branch
/// whose guard is narrower than the decider's: `u i1 it_is_one`, and only
/// when `φ` is the literal `i1`.
///
/// The narrowness is the rule, not an optimisation. `it_is_one` is a
/// proof of `is_one i1`; feeding it to a system expecting `is_one φ` is
/// justified only by `φ` BEING `i1`, and reduction has no conversion
/// check that could supply the missing step. `face_decide` answers a
/// FACT about `φ`, which is enough for the refuted half (`hcomp ≡ u0`
/// asks nothing of the system) and not for this one. Nothing reachable
/// is lost: `whnf_cubical_args` reduces `φ` before this runs, and
/// `whnf_face`/`whnf_demorgan` fold every satisfiable non-literal shape
/// (`face_eq0 i0`, a meet with an `i1` factor, a join with a satisfied
/// disjunct) to a literal endpoint first -- the same reason the face
/// pass leaves `ijoin`-of-opposite-faces stuck rather than reasoning
/// about it.
def whnf_hcomp_satisfied (a_face : Term) (a_sys : Term) : Option Term :=
    if whnf_term_is_bare_prim a_face CubicalPrim.i1
    then Option.some (Term.app (Term.app a_sys cub_i1) cub_it_is_one)
    else Option.none

/// The Kan rule for `hcomp A φ u u0`. Its input is the already-reduced
/// `Cubical` -- `whnf_cubical` whnfs every argument before dispatching --
/// which is what lets `face_decide` be consulted at all: that decision
/// procedure reads flat literals, and its contract is a NORMALIZED
/// cofibration. Here the contract is met by construction rather than by
/// a call, since the arguments arrived reduced.
///
/// One case reduces, one reduces only at the literal endpoint.
///
/// * `φ` REFUTED (`some false`): every disjunct has a definitely-false
///   literal or the contradiction pair, so `φ` is the empty subobject. A
///   system over nothing constrains nothing, and the composite of a box
///   with no sides is its base: `hcomp A i0 u u0 ≡ u0`.
/// * `φ` the LITERAL `i1`: the boundary law applies and the composite is
///   the system's top, `hcomp A i1 u u0 ≡ u i1 it_is_one` (`whnf_hcomp_satisfied`
///   above, and `cub_it_is_one`). Note the asymmetry this states: `u0` is
///   the system's BOTTOM (`u i0 = u0` on `φ`), so answering `u0` here
///   would be outright unsound -- the `u i1` half is the whole point of
///   the rule.
/// * `φ` satisfied by `face_decide` but not literally `i1`: STUCK, for
///   the reason `whnf_hcomp_satisfied` states.
///
/// A malformed `hcomp` never reduces: the argument count is re-checked
/// rather than trusted, the same discipline `whnf_face`'s arms use.
def whnf_hcomp (c : Cubical) : Option Term :=
    match c {
        { prim := p, args := as } =>
            if cubical_prim_eq p CubicalPrim.hcomp then
                match as {
                    List.cons _a_typ rest =>
                        match rest {
                            List.cons a_face rest2 =>
                                match rest2 {
                                    List.cons a_sys rest3 =>
                                        match rest3 {
                                            List.cons a_base rest4 =>
                                                if List.is_empty rest4 then
                                                    match face_decide a_face {
                                                        Option.some b =>
                                                            if b then
                                                                whnf_hcomp_satisfied a_face a_sys
                                                            else Option.some a_base,
                                                        Option.none => Option.none,
                                                    }
                                                else Option.none,
                                            List.empty => Option.none,
                                        },
                                    List.empty => Option.none,
                                },
                            List.empty => Option.none,
                        },
                    List.empty => Option.none,
                }
            else Option.none,
    }

/// The generator step `face_eq0` and `face_eq1` share, on the single,
/// already-reduced argument. At the endpoint where the constraint HOLDS
/// the cofibration is `i1` (`face_eq0 i0`: the face `i = 0` is all of
/// the cube at `i0`); at the opposite endpoint it is `i0`
/// (`face_eq1 i0` constrains nothing there). A NEGATED argument swaps
/// the two generators -- `ineg u = 0` IS `u = 1` -- which is the reason
/// there are two generators and not four. Parameterized by the
/// endpoint that holds and the generator the negated arm builds.
def whnf_face_gen (holds : CubicalPrim) (negated : Term -> Term) (u : Term) : Option Term :=
    let fails : CubicalPrim :=
        if cubical_prim_eq holds CubicalPrim.i0 then CubicalPrim.i1 else CubicalPrim.i0 in
    if whnf_term_is_bare_prim u holds then Option.some cub_i1
    else if whnf_term_is_bare_prim u fails then Option.some cub_i0
    else
        match u {
            Term.cubical inner =>
                match inner {
                    { prim := q, args := inner_as } =>
                        // The inner `ineg` must be well-formed (arity 1)
                        // -- the same discipline as
                        // `whnf_demorgan_ineg`: a malformed args list
                        // does not get to reduce.
                        if cubical_prim_eq q CubicalPrim.ineg then
                            match inner_as {
                                List.cons x rest =>
                                    if List.is_empty rest then Option.some (negated x) else Option.none,
                                List.empty => Option.none,
                            }
                        else Option.none,
                },
            _ => Option.none,
        }

/// The dimension under a face-generator head, with arity checked, or
/// `Option.none` when `t` is not that generator applied to exactly one
/// argument. For the contradiction law's two sides.
def whnf_face_gen_arg (p : CubicalPrim) (t : Term) : Option Term :=
    match t {
        Term.cubical inner =>
            match inner {
                { prim := q, args := inner_as } =>
                    if cubical_prim_eq q p then
                        match inner_as {
                            List.cons u rest =>
                                if List.is_empty rest then Option.some u else Option.none,
                            List.empty => Option.none,
                        }
                    else Option.none,
            },
        _ => Option.none,
    }

/// Do `l` and `r` contradict as face literals -- one `face_eq0 u`, the
/// other `face_eq1 u`, over `Similar` dimensions? Then their meet is
/// `i0`: no point of the cube is both `u = 0` and `u = 1`. `Similar`
/// peels `Term.ctx` on both sides and compares dimensions as terms --
/// the same notion of "same dimension" the De Morgan idempotence rule
/// uses.
def whnf_face_contradicts (l : Term) (r : Term) : Option Term :=
    match whnf_face_gen_arg CubicalPrim.face_eq0 l {
        Option.some u =>
            match whnf_face_gen_arg CubicalPrim.face_eq1 r {
                Option.some v => if Similar.similar u v then Option.some cub_i0 else Option.none,
                Option.none => Option.none,
            },
        Option.none =>
            match whnf_face_gen_arg CubicalPrim.face_eq1 l {
                Option.some u =>
                    match whnf_face_gen_arg CubicalPrim.face_eq0 r {
                        Option.some v => if Similar.similar u v then Option.some cub_i0 else Option.none,
                        Option.none => Option.none,
                    },
                Option.none => Option.none,
            },
    }

/// Normalize a cubical head: reduce each argument to WHNF, then take
/// one De Morgan step if any applies, then one face-lattice step, then
/// one transport step if the family is constant. No further pass over
/// any of THOSE steps' results is needed -- each is assembled from pieces
/// that are already in WHNF (whnf_transp answers the already-reduced
/// element, which came out of `whnf_cubical_args`), and a stuck head keeps
/// its reduced arguments, so a caller comparing two stuck terms compares
/// them as reduced as they can be.
///
/// `hcomp`'s satisfied-face answer is the ONE that is not already reduced:
/// it is the system applied to `i1` and then to the witness, i.e. a beta
/// redex, so it goes back through the reducer. Without that the head would
/// be a `Term.lam` and `whnf`'s contract ("keep reducing at the head until
/// the head is rigid") would be broken for every caller.
/// `#[partial]`, exactly as `whnf_go` is and for the same reason: the
/// `hcomp` step hands its answer back to the reducer, so the recursion is
/// fuel-bounded rather than structural.
#[partial]
def whnf_cubical (fuel : I64) (scope : Scope) (locals : LocalScope) (c : Cubical) : Term :=
    match c {
        { prim := p, args := as } =>
            let as_r : List Term := whnf_cubical_args fuel scope locals as in
            // Annotated local, never a bare struct literal in argument
            // position (the miscompile trap; AGENTS.md).
            let c_r : Cubical := { prim := p, args := as_r } in
            match whnf_demorgan c_r {
                Option.some t => t,
                Option.none =>
                    match whnf_face c_r {
                        Option.some t => t,
                        Option.none =>
                            match whnf_hcomp c_r {
                                Option.some t => whnf_go (fuel - 1) scope locals t,
                                Option.none =>
                                    match whnf_transp c_r {
                                        Option.some t => t,
                                        Option.none => Term.cubical c_r,
                                    },
                            },
                    },
            },
    }

// ─── Iota ────────────────────────────────────────────────────────────
//
// Dispatch and substitution for the two literal reduction rules. The
// order of the pieces below mirrors reduction order: recognize a
// constructor application (`whnf_con_head`), pick the arm
// (`whnf_case_for`), then substitute its pattern binders
// (`whnf_fire_case`).

/// The constructor's own simple name: the LAST dotted segment of
/// whatever spelling the term carries. Constructor references are
/// written qualified (`Sigma.dpair`, `P.p0`) or bare (`dpair`, after
/// an `open`), but scope registers them under their bare name only
/// (`add_constructors_go`, `lang/scope.mo`) and match arms are stored
/// stripped the same way (`match_case_name`, `lang/parser.mo`), so the
/// simple name is the one thing all three spellings agree on. Local
/// twin of `last_dotted_segment` (`lang/typecheck/infer.mo`) -- the
/// same cannot just be imported from there, since `infer.mo` itself
/// depends on this module's `unify` path.
def whnf_simple_name (id : Identifier) : Identifier :=
    let s : String := show_identifier id in
    let dot : I64 := last_dot_index s 0 (0 - 1) in
    if I64.lt dot 0 then id else Identifier.id (String.drop (dot + 1) s)

/// Whether `simple` names SOME registered constructor. One lookup
/// settles it because constructors live in scope under their bare
/// name; this is what keeps iota from firing on a stuck NON-constructor
/// head that merely shares a case's name -- a head that named a `def`
/// would have been delta-unfolded already, but a type name, a class,
/// or an unbound name all stay stuck and must not dispatch.
def whnf_is_constructor (simple : Identifier) (scope : Scope) : Bool :=
    match scope_find_inductive_by_constructor (NamePath.mk (List.cons simple List.empty)) scope {
        Option.some _ => true,
        Option.none => false,
    }

/// A reduced scrutinee read as a constructor application: the
/// constructor's simple name and its field arguments in declaration
/// order. `Option.none` when the scrutinee is anything else -- a
/// variable, a stuck head, another literal.
///
/// Two shapes, because a constructor application has two spellings in
/// this compiler. What the parser and elaborator actually build is a
/// FREE-VAR application spine (`Two.mk a b` -- the parser never builds
/// `Term.con`, see `type_check_con`'s own doc comment,
/// `lang/typecheck/infer.mo`); `Term.con` exists for lowering, pretty
/// printing and hand-built fixtures, and is trusted rather than
/// re-resolved.
def whnf_con_head (scrut : Term) (scope : Scope) : Option (Pair Identifier (List Term)) :=
    match scrut {
        Term.con c =>
            match c {
                Con.mk cname _typ_name _num_args args =>
                    match whnf_con_args args {
                        Option.some field_args =>
                            Option.some (Pair.pair (whnf_simple_name cname) field_args),
                        Option.none => Option.none,
                    },
            },
        _ =>
            match flatten_call_spine scrut {
                CallSpine.mk head args =>
                    match head {
                        Term.var idx dbg =>
                            if I64.beq idx sentinel then
                                match dbg {
                                    DebugName.named id =>
                                        let simple : Identifier := whnf_simple_name id in
                                        if whnf_is_constructor simple scope
                                        then Option.some (Pair.pair simple args)
                                        else Option.none,
                                    DebugName.unnamed => Option.none,
                                }
                            else Option.none,
                        _ => Option.none,
                    },
            },
    }

/// `Con`'s arguments are `Option Term` (unelaborated positions stay
/// `none`); every one must be present for iota to fire.
#[partial]
def whnf_con_args (args : List (Option Term)) : Option (List Term) :=
    match args {
        List.empty => Option.some List.empty,
        List.cons hd rest =>
            match hd {
                Option.some a =>
                    match whnf_con_args rest {
                        Option.some tl => Option.some (List.cons a tl),
                        Option.none => Option.none,
                    },
                Option.none => Option.none,
            },
    }

/// The first NAMED case whose pattern name matches, else none. Wildcard
/// fallback is `whnf_iota_case`'s job -- it has to rescan from the
/// ORIGINAL list, since a `_` arm may sit before the named scan's
/// position. Mirrors `find_case_for_ctor` + `find_wildcard_case`
/// (`lang/lower_core_ir.mo`) so reduction and the runtime's tag-indexed
/// dispatch agree on which arm wins. Case names are stored
/// already-stripped, but `whnf_simple_name` is applied anyway so
/// hand-built terms written qualified behave the same.
#[partial]
def whnf_named_case_for (con_name : Identifier) (cases : List MatchCase) : Option MatchCase :=
    match cases {
        List.empty => Option.none,
        List.cons hd rest =>
            match hd {
                MatchCase.mk name _ _ _ _ =>
                    if id_eq (whnf_simple_name name) con_name
                    then Option.some hd
                    else whnf_named_case_for con_name rest,
            },
    }

/// The `_` fallback arm, reached only after every named case missed --
/// scanned from the head of the FULL case list, because a wildcard
/// written before other arms must still win the fallback. A wildcard
/// binds nothing (`type_check_match_case` rejects `_` with arguments),
/// and that is enforced again at fire time by the arity check in
/// `whnf_fire_case`.
#[partial]
def whnf_wildcard_case (cases : List MatchCase) : Option MatchCase :=
    match cases {
        List.empty => Option.none,
        List.cons hd rest =>
            match hd {
                MatchCase.mk name _ _ _ _ =>
                    if String.beq (show_identifier (whnf_simple_name name)) "_"
                    then Option.some hd
                    else whnf_wildcard_case rest,
            },
    }

/// Dispatch: reduce `match scrut cases` by firing whichever arm `scrut`
/// selects. `Option.none` = stuck (scrutinee not a constructor, no
/// matching arm, or an arity mismatch -- reduction only ever widens
/// what a sound checker accepts, so an ill-shaped match stays as it
/// came in).
def whnf_iota_case (scrut : Term) (cases : List MatchCase) (scope : Scope) : Option Term :=
    match whnf_con_head scrut scope {
        Option.none => Option.none,
        Option.some p =>
            match p {
                Pair.pair con_name field_args =>
                    match whnf_named_case_for con_name cases {
                        Option.some case_ => whnf_fire_case case_ field_args,
                        Option.none =>
                            match whnf_wildcard_case cases {
                                Option.some case_ => whnf_fire_case case_ field_args,
                                Option.none => Option.none,
                            },
                    },
            },
    }

/// Fire one arm: substitute the constructor's field arguments for the
/// case's pattern binders. `Option.none` unless the argument count
/// matches the binder count -- a partial application has nothing to
/// project, and a well-typed checked match never over-applies.
def whnf_fire_case (case_ : MatchCase) (field_args : List Term) : Option Term :=
    match case_ {
        MatchCase.mk _name binders body _field_pattern _typ_name =>
            let n : I64 := List.length binders in
            if I64.beq n (List.length field_args)
            then Option.some (whnf_subst_case_fields body field_args n)
            else Option.none,
    }

/// Substitute `args` (the constructor's fields, in declaration order)
/// for a case body's `n` pattern binders.
///
/// The binders are the case's `List.length args` levels-at-once
/// (AGENTS.md item 22), FIRST-declared field OUTERMOST -- the same
/// convention as a `Term.lam` chain, and as the runtime's
/// `extend_env_with_fields` (`lang/core_eval.mo`), which binds fields
/// in declaration order so the last one ends up innermost. So the
/// outermost binder sits at de Bruijn index `n-1`, and the fold
/// substitutes OUTERMOST-FIRST: step `k` replaces index `k-1` with its
/// argument shifted up by the `k-1` binders still in scope, and each
/// later step's decrement brings every earlier argument down again.
///
/// Substituting innermost-first instead would insert each argument
/// under-scoped -- its free variables still counting binders that have
/// not been substituted yet -- and the next step would then overwrite
/// them. `beta_reduce` never faces this because it peels exactly ONE
/// `Term.lam` at a time; this is the many-at-once sibling.
#[partial]
def whnf_subst_case_fields (body : Term) (args : List Term) (k : I64) : Term :=
    match args {
        List.empty => body,
        List.cons a rest =>
            whnf_subst_case_fields (term_subst (k - 1) (term_shift (k - 1) a) body) rest (k - 1),
    }

// ─── Iota on `Elim` (core-term-simplification.md R5) ──────────────────
//
// `Elim.minors` are POSITIONAL (R3b's `build_elim_minors` walks an
// inductive's own declared constructor order), not named like
// `MatchCase` -- so dispatch is a lockstep walk of `ind`'s constructors
// against `e.minors`, not a name scan. Each minor is a plain `Term.lam`
// chain over one constructor's fields (`build_named_lambda_chain`/
// `build_anon_lambda_chain`, R3b), so "firing" one is: peel exactly as
// many lambdas as the constructor has fields, then substitute with
// `whnf_subst_case_fields` -- the SAME many-at-once substitution
// `Literal.match_`'s iota already uses, since a lambda chain and a
// `MatchCase`'s simultaneous binders share the identical convention
// (first-declared field OUTERMOST).

/// The minor paired with `con_name`, found by walking `ctors` and
/// `minors` together -- the position where `ctors`' name matches IS
/// `minors`' corresponding entry, by construction (`build_elim_minors`).
/// `Option.none` on a length mismatch (an ill-shaped `Elim` reaching
/// reduction) or when no constructor matches; reduction only ever widens
/// what a sound checker accepts, so this stays stuck rather than guessing.
def whnf_elim_minor_for_ctor (ctors : List InductConstructor) (minors : List Term)
    (con_name : Identifier) : Option Term :=
    match ctors {
        List.empty => Option.none,
        List.cons ctor crest =>
            match minors {
                List.empty => Option.none,
                List.cons minor mrest =>
                    if id_eq (whnf_simple_name (whnf_constructor_bare_name ctor.name)) con_name
                    then Option.some minor
                    else whnf_elim_minor_for_ctor crest mrest con_name,
            },
    }

/// A constructor's own simple name, read off its (qualified) `NamePath`.
/// Local twin of `constructor_bare_name` (`lang/typecheck/infer.mo`) --
/// the same cannot be imported from there for the reason `whnf_simple_
/// name`'s own doc comment already gives: `infer.mo` depends on this
/// module, not the other way around.
def whnf_constructor_bare_name (np : NamePath) : Identifier :=
    match np {
        NamePath.mk ids =>
            match List.last ids {
                Option.some last_id => last_id,
                Option.none => Identifier.id "",
            },
    }

/// Peel exactly `n` `Term.lam` layers off `t`, returning the body
/// underneath. `Option.none` when `t` has fewer than `n` lambdas -- an
/// arity mismatch between a minor and its constructor, which a sound
/// checker never produces, but reduction must not crash on regardless.
#[partial]
def whnf_peel_lambda_n (t : Term) (n : I64) : Option Term :=
    if I64.lt n 1 then Option.some t
    else
        match term_peel t {
            Term.lam _b _typ body => whnf_peel_lambda_n body (n - 1),
            _ => Option.none,
        }

/// Fire one minor: peel its `List.length field_args` lambdas, then
/// substitute the constructor's fields for the same-many pattern
/// binders -- `whnf_subst_case_fields` needs no new logic here, since a
/// lambda chain's binders are bound OUTERMOST-first exactly like a
/// `MatchCase`'s `whnf_subst_case_fields` already assumes.
def whnf_elim_fire_minor (minor : Term) (field_args : List Term) : Option Term :=
    let n : I64 := List.length field_args in
    match whnf_peel_lambda_n minor n {
        Option.some body => Option.some (whnf_subst_case_fields body field_args n),
        Option.none => Option.none,
    }

/// Dispatch: reduce `Term.elim e` when `scrut_r` (the already-reduced
/// scrutinee) is a known constructor application. `Option.none` = stuck
/// -- not a constructor, an unresolvable `e.inductive`, or no matching
/// minor -- mirroring `whnf_iota_case`'s own contract for `match`.
def whnf_elim_iota (e : Elim) (scrut_r : Term) (scope : Scope) : Option Term :=
    match whnf_con_head scrut_r scope {
        Option.none => Option.none,
        Option.some p =>
            match p {
                Pair.pair con_name field_args =>
                    match scope_find_inductive e.inductive scope {
                        err _ => Option.none,
                        ok ind =>
                            match whnf_elim_minor_for_ctor ind.constructors e.minors con_name {
                                Option.some minor => whnf_elim_fire_minor minor field_args,
                                Option.none => Option.none,
                            },
                    },
            },
    }

/// `Option.some b` when `cond` has reduced to `Bool`'s constructor
/// `true`/`false` (by simple name -- those two are the only
/// constructors an `if` condition can inhabit; the con-shape and
/// constructor-ness checks are shared with `match` dispatch above).
/// Anything else is stuck.
def whnf_bool_con (cond : Term) (scope : Scope) : Option Bool :=
    match whnf_con_head cond scope {
        Option.some p =>
            match p {
                Pair.pair name args =>
                    match args {
                        List.empty =>
                            if String.beq (show_identifier name) "true"
                            then Option.some true
                            else if String.beq (show_identifier name) "false"
                            then Option.some false
                            else Option.none,
                        _ => Option.none,
                    },
            },
        Option.none => Option.none,
    }

/// Classify `t` as the `Term.cubical` it denotes when it is a SATURATED
/// application of a bound cubical primitive -- the pure half of
/// `type_check_app`'s own `try_type_check_cubical_call` preamble, for a
/// term that arrives as a TYPE rather than as a call being checked.
///
/// It exists because `path_parts_of` (`lang/typecheck/cubical.mo`) is
/// syntactic: it recognizes `Term.cubical`. A path type SPELLED as a
/// library def -- `Path A a b`, whose body is `Cubical.PathP (fn _ => A) a
/// b` -- unfolds under delta into `PathP (fn _ => A) a b`, an APPLICATION
/// SPINE of the `pathp` primitive's NAME, so before this every path rule
/// (the `fn i =>` dispatch, the endpoint rewrite in
/// `normalize_path_boundary`, and `unify`'s comparison of a `Path`-spelled
/// type against the `PathP` the rules echo back) missed it.
///
/// Same guards, and the same reasons, as the checked-call probe: a
/// sentinel free head, no LOCAL shadowing the name, a registered
/// primitive, and an arity EQUALITY (a partially applied `imeet i` is not
/// the cubical term).
pub def as_cubical_type (t : Term) (scope : Scope) (locals : LocalScope) : Term :=
    match flatten_call_spine t {
        CallSpine.mk head args =>
            match head {
                Term.var idx dbg =>
                    if I64.beq idx sentinel then
                        match dbg {
                            DebugName.named id =>
                                match scope_find_local id locals {
                                    Option.some _ => t,
                                    Option.none =>
                                        match scope_resolve_name (NameRef.nid id) scope locals {
                                            err _ => t,
                                            ok sd =>
                                                match sd {
                                                    mk resolved _ _ _ _ =>
                                                        match scope_find_cubical_prim resolved scope {
                                                            Option.none => t,
                                                            Option.some prim =>
                                                                if I64.beq (List.length args) (cubical_arity prim)
                                                                then
                                                                    let c : Cubical := { prim := prim, args := args } in
                                                                    Term.cubical c
                                                                else t,
                                                        },
                                                },
                                        },
                                },
                            DebugName.unnamed => t,
                        }
                    else t,
                _ => t,
            },
    }

/// Delta: the body of the global `def` this free variable names, if it
/// names one.
///
/// The local check is not an optimisation -- it is what keeps this
/// sound. A free `Term.var` is not necessarily a global: `locals_with_
/// def_typevars` (`lang/module.mo`) skolemises a def's implicit type
/// parameters into NAMED locals, and those resolve through this same
/// path. Unfolding a local `V` into a same-named global `V`'s body
/// would substitute an unrelated definition for a bound type variable.
def whnf_delta (scope : Scope) (locals : LocalScope) (dbg : DebugName) : Option Term :=
    match dbg {
        DebugName.named id =>
            match scope_find_local id locals {
                Option.some _ => Option.none,
                Option.none =>
                    // Resolve first, then look the body up under the
                    // name resolution returned: the same two-step
                    // `type_check_free_var` uses for `def_sigs`, so a
                    // bare name and its qualified form reach the same
                    // entry.
                    match scope_resolve_name (NameRef.nid id) scope locals {
                        ok sd => scope_find_def_body sd.name scope,
                        err _ => Option.none,
                    },
            },
        DebugName.unnamed => Option.none,
    }
