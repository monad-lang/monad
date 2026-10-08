// Stage 4 (`plans/type-system/univalence.md`): the FACE decision
// procedure. `whnf_face` (whnf.mo) normalizes a cofibration one
// weak-head step at a time, and weak-head eyes cannot see under a
// stuck head: in `face_eq0 i ∧ (face_eq1 i ∧ j)` the contradiction sits
// under the outer meet, which never reduces because no rule at that
// head fires. `face_decide` answers the whole question at once by
// flattening the cofibration to disjunctive normal form -- a
// disjunction of conjunctions of literals -- and classifying:
//
//   some true  -- some conjunction is satisfied: every literal in it
//                 is definitely true
//   some false -- every conjunction is refuted: each has a literal
//                 that is definitely false, or the CONTRADICTION pair
//                 `face_eq0 u` and `face_eq1 u` over a similar `u`
//   none       -- no decision, always the safe answer
//
// Stage 5's `hcomp` consumes this to decide a cofibration. The input
// is expected to be a NORMALIZED one -- the caller whnfs first, so the
// generator laws (`face_eq0 i0 = i1`, the argument-De Morgan swaps)
// have already folded and this module reads only flat literals.
// Anything it does not recognize answers none: a bare dimension is not
// a cofibration, a negated generator argument is whnf's job to fold, a
// `ijoin` inside a meet is not distributed, and a malformed arity
// never decides.
//
// Deliberately free of checker state, like `lang/typecheck/cubical.mo`: everything
// here is a `Term` -> `Option Bool` question over the same shapes.

use lib::types {
    Similar, Term,
    cub_face_eq0, cub_face_eq1, cub_i0, cub_i1, cub_imeet, cub_ijoin, cub_ineg,
    cubical_prim_eq, sentinel, term_peel,
    face_eq0, face_eq1, i0, i1, id, ijoin, imeet, named,
}
use lib::typecheck::cubical {endpoint_of}

/// The truth of one face LITERAL -- a bare endpoint, or a generator
/// applied to exactly one BARE-endpoint argument. `i0` and `i1` are
/// themselves cofibrations (the always-false and always-true ones);
/// `face_eq0 u` reads as `u = 0`, true at `u = i0` and refuted at
/// `u = i1`, and `face_eq1` the dual. A generator over any other
/// dimension answers none -- its truth is unknown, not decided -- and
/// so does everything else.
pub def face_literal_truth (t : Term) : Option Bool :=
    match term_peel t {
        Term.cubical c =>
            match c {
                { prim := p, args := as } =>
                    match as {
                        List.empty =>
                            match p {
                                CubicalPrim.i0 => Option.some false,
                                CubicalPrim.i1 => Option.some true,
                                _ => Option.none,
                            },
                        List.cons u rest =>
                            if List.is_empty rest then
                                if cubical_prim_eq p CubicalPrim.face_eq0 then
                                    // "u = 0": holds at i0, refuted at i1.
                                    match endpoint_of u {
                                        Option.some q =>
                                            if cubical_prim_eq q CubicalPrim.i0 then Option.some true
                                            else if cubical_prim_eq q CubicalPrim.i1 then Option.some false
                                            else Option.none,
                                        Option.none => Option.none,
                                    }
                                else if cubical_prim_eq p CubicalPrim.face_eq1 then
                                    // "u = 1": the dual endpoint reading.
                                    match endpoint_of u {
                                        Option.some q =>
                                            if cubical_prim_eq q CubicalPrim.i1 then Option.some true
                                            else if cubical_prim_eq q CubicalPrim.i0 then Option.some false
                                            else Option.none,
                                        Option.none => Option.none,
                                    }
                                else Option.none
                            else Option.none,
                    },
            },
        _ => Option.none,
    }

/// Is `t` literal-SHAPED -- a bare endpoint or a generator over
/// exactly one argument, whatever that argument is? Distinct from
/// `face_literal_truth` answering none: `face_eq0 i` over an unknown
/// dimension is a literal whose truth is unknown, and the conjunct
/// flattener must still collect it, because the contradiction law
/// reads unknown literals.
def face_is_literal (t : Term) : Bool :=
    match term_peel t {
        Term.cubical c =>
            match c {
                { prim := p, args := as } =>
                    match as {
                        List.empty =>
                            cubical_prim_eq p CubicalPrim.i0 || cubical_prim_eq p CubicalPrim.i1,
                        List.cons _u rest =>
                            List.is_empty rest &&
                            (cubical_prim_eq p CubicalPrim.face_eq0
                                || cubical_prim_eq p CubicalPrim.face_eq1),
                    },
            },
        _ => false,
    }

/// The dimension of a `face_eq0` literal -- `face_eq0 u` answers `u`,
/// with arity checked -- or none when `t` is not that generator. For
/// the contradiction law's two sides; the same shape whnf.mo's
/// `whnf_face_gen_arg` reads, over the literals the flattener
/// collected instead of a meet head's two arguments.
def face_lit_zero_dim (t : Term) : Option Term :=
    match term_peel t {
        Term.cubical c =>
            match c {
                { prim := p, args := as } =>
                    if cubical_prim_eq p CubicalPrim.face_eq0 then
                        match as {
                            List.cons u rest =>
                                if List.is_empty rest then Option.some u else Option.none,
                            List.empty => Option.none,
                        }
                    else Option.none,
            },
        _ => Option.none,
    }

/// The dimension of a `face_eq1` literal; dual of
/// `face_lit_zero_dim`.
def face_lit_one_dim (t : Term) : Option Term :=
    match term_peel t {
        Term.cubical c =>
            match c {
                { prim := p, args := as } =>
                    if cubical_prim_eq p CubicalPrim.face_eq1 then
                        match as {
                            List.cons u rest =>
                                if List.is_empty rest then Option.some u else Option.none,
                            List.empty => Option.none,
                        }
                    else Option.none,
            },
        _ => Option.none,
    }

/// Do two collected literals contradict -- the same dimension
/// constrained to both endpoints, in either order? `Similar` compares
/// the dimensions as terms (it peels `Term.ctx`), the same notion of
/// "same dimension" as whnf's contradiction rule.
def face_lit_contradicts (l : Term) (r : Term) : Bool :=
    match face_lit_zero_dim l {
        Option.some u =>
            match face_lit_one_dim r {
                Option.some v => Similar.similar u v,
                Option.none => false,
            },
        Option.none =>
            match face_lit_one_dim l {
                Option.some u =>
                    match face_lit_zero_dim r {
                        Option.some v => Similar.similar u v,
                        Option.none => false,
                    },
                Option.none => false,
            },
    }

/// Does `l` contradict ANY literal in `lits`?
def face_lit_contradicts_any (l : Term) (lits : List Term) : Bool :=
    match lits {
        List.empty => false,
        List.cons hd rest => face_lit_contradicts l hd || face_lit_contradicts_any l rest,
    }

/// The literals of one CONJUNCTION: a literal answers itself, and an
/// `imeet` (arity checked) answers both sides' literals, recursively --
/// the flattening that makes buried contradictions visible to a
/// decision the weak-head reducer cannot make. A `ijoin` inside a meet
/// is deliberately NOT distributed; a mixed position answers none.
///
/// `#[terminating]` because the recursion is on strict structural
/// subterms -- the two arguments of a meet -- but they sit behind the
/// struct field and a List cons, which the structural checker does not
/// look through.
#[terminating]
def face_conjunct_literals (t : Term) : Option (List Term) :=
    match term_peel t {
        Term.cubical c =>
            match c {
                { prim := p, args := as } =>
                    if cubical_prim_eq p CubicalPrim.imeet then
                        match as {
                            List.cons l rest =>
                                match rest {
                                    List.cons r rest2 =>
                                        if List.is_empty rest2 then
                                            match face_conjunct_literals l {
                                                Option.none => Option.none,
                                                Option.some ls =>
                                                    match face_conjunct_literals r {
                                                        Option.none => Option.none,
                                                        Option.some rs => Option.some (List.append ls rs),
                                                    },
                                            }
                                        else Option.none,
                                    List.empty => Option.none,
                                },
                            List.empty => Option.none,
                        }
                    else if face_is_literal t then Option.some [t]
                    else Option.none,
            },
        _ => Option.none,
    }

/// Does any literal of the conjunction definitely fail?
def face_any_false (lits : List Term) : Bool :=
    match lits {
        List.empty => false,
        List.cons hd rest =>
            match face_literal_truth hd {
                Option.some b => if b then face_any_false rest else true,
                Option.none => face_any_false rest,
            },
    }

/// Is every literal of the conjunction definitely true?
def face_all_true (lits : List Term) : Bool :=
    match lits {
        List.empty => true,
        List.cons hd rest =>
            match face_literal_truth hd {
                Option.some b => if b then face_all_true rest else false,
                Option.none => false,
            },
    }

/// Does ANY pair of the conjunction's literals contradict?
def face_contradiction_in (lits : List Term) : Bool :=
    match lits {
        List.empty => false,
        List.cons hd rest =>
            face_lit_contradicts_any hd rest || face_contradiction_in rest,
    }

/// Decide one conjunction from its literals: a definitely-false
/// literal refutes it, and so does a contradiction pair; only when
/// every literal is definitely true is it satisfied; otherwise
/// unknown.
def face_conjunct_value (lits : List Term) : Option Bool :=
    if face_any_false lits then Option.some false
    else if face_contradiction_in lits then Option.some false
    else if face_all_true lits then Option.some true
    else Option.none

/// Combine two tri-state truths under DISJUNCTION: a true anywhere
/// decides the whole; only two falses decide a false; anything else is
/// unknown.
def face_decide_or (a : Option Bool) (b : Option Bool) : Option Bool :=
    match a {
        Option.some x =>
            if x then Option.some true else b,
        Option.none =>
            match b {
                Option.some y => if y then Option.some true else Option.none,
                Option.none => Option.none,
            },
    }

/// Decide a cofibration: `some true` when it definitely holds, `some
/// false` when it definitely fails, `none` when no decision -- always
/// the safe answer for a bare dimension, a non-cubical term, a mixed
/// lattice position, or a malformed arity. See the module doc for the
/// normalized-input contract.
///
/// `#[terminating]` for the same reason as `face_conjunct_literals`:
/// each disjunct is a strict structural subterm behind a struct field
/// and a List cons.
#[terminating]
pub def face_decide (t : Term) : Option Bool :=
    match term_peel t {
        Term.cubical c =>
            match c {
                { prim := p, args := as } =>
                    if cubical_prim_eq p CubicalPrim.ijoin then
                        // A disjunction: each side is decided
                        // recursively, so nested joins flatten. Arity
                        // is checked -- a malformed join never decides.
                        match as {
                            List.cons l rest =>
                                match rest {
                                    List.cons r rest2 =>
                                        if List.is_empty rest2 then
                                            face_decide_or (face_decide l) (face_decide r)
                                        else Option.none,
                                    List.empty => Option.none,
                                },
                            List.empty => Option.none,
                        }
                    else
                        // One conjunction: a literal, or a (nested)
                        // meet of literals.
                        match face_conjunct_literals t {
                            Option.none => Option.none,
                            Option.some lits => face_conjunct_value lits,
                        },
            },
        _ => Option.none,
    }

/// A free dimension variable, for the tests: the shape a checked
/// cofibration carries for a dimension outside any binder.
def test_dim (nm : String) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id nm))

/// The buried all-true case that weak-head reduction cannot see: the
/// true literal `face_eq1 i1` sits under a meet whose OTHER argument is
/// the bare unit `i1`.
#[test]
def test_face_decide_true_on_a_buried_all_true_conjunction : Bool :=
    let phi : Term := cub_imeet cub_i1 (cub_face_eq1 cub_i1) in
    match face_decide phi {
        Option.some b => b,
        Option.none => false,
    }

/// The buried contradiction from the plan doc: `i = 0` and `i = 1`
/// under one nested meet, with a third literal along so no whnf rule
/// at any single head would ever fire. (The third literal is itself a
/// face literal -- a bare dimension is not a cofibration, and the
/// flattener correctly refuses to read one.)
#[test]
def test_face_decide_false_on_a_buried_contradiction : Bool :=
    let i : Term := test_dim "i" in
    let j : Term := test_dim "j" in
    let phi : Term := cub_imeet (cub_face_eq0 i) (cub_imeet (cub_face_eq1 i) (cub_face_eq1 j)) in
    match face_decide phi {
        Option.some b => Bool.not b,
        Option.none => false,
    }

/// A disjunction with one satisfied side is satisfied.
#[test]
def test_face_decide_true_on_a_disjunction : Bool :=
    let i : Term := test_dim "i" in
    let phi : Term := cub_ijoin (cub_face_eq0 i) (cub_face_eq1 cub_i1) in
    match face_decide phi {
        Option.some b => b,
        Option.none => false,
    }

/// A disjunction is refuted only when EVERY side is: here one side is
/// refuted at an endpoint and the other by the contradiction pair.
#[test]
def test_face_decide_false_only_when_every_disjunct_is_refuted : Bool :=
    let i : Term := test_dim "i" in
    let phi : Term :=
        cub_ijoin (cub_face_eq0 cub_i1) (cub_imeet (cub_face_eq0 i) (cub_face_eq1 i)) in
    match face_decide phi {
        Option.some b => Bool.not b,
        Option.none => false,
    }

/// A bare dimension is not a cofibration: the conservative answer, and
/// the one Stage 5 must treat as "cannot decide", never as false.
#[test]
def test_face_decide_none_on_a_bare_dimension : Bool :=
    match face_decide (test_dim "i") {
        Option.some _ => false,
        Option.none => true,
    }

/// An un-normalized generator argument: `face_eq0 (ineg i)` means
/// `i = 1`, but folding it is whnf's argument-De Morgan law, not this
/// module's -- the literal's truth stays unknown here.
#[test]
def test_face_decide_none_on_an_unnormalized_negated_argument : Bool :=
    let i : Term := test_dim "i" in
    match face_decide (cub_face_eq0 (cub_ineg i)) {
        Option.some _ => false,
        Option.none => true,
    }

/// A `ijoin` inside a meet is a mixed lattice position: it is not
/// distributed, and the whole answers none rather than guessing.
#[test]
def test_face_decide_none_on_a_join_inside_a_meet : Bool :=
    let i : Term := test_dim "i" in
    let phi : Term :=
        cub_imeet cub_i1 (cub_ijoin (cub_face_eq0 i) (cub_face_eq1 i)) in
    match face_decide phi {
        Option.some _ => false,
        Option.none => true,
    }

/// The literal classifier on bare endpoints: `i0` is the always-false
/// cofibration and `i1` the always-true one.
#[test]
def test_face_literal_truth_on_the_bare_endpoints : Bool :=
    match face_literal_truth cub_i0 {
        Option.some b => Bool.not b && match face_literal_truth cub_i1 {
            Option.some b2 => b2,
            Option.none => false,
        },
        Option.none => false,
    }

/// A generator at the endpoint where its constraint holds, and at the
/// endpoint where it fails: `face_eq0 i0` is true, `face_eq0 i1` and
/// `face_eq1 i0` are false, `face_eq1 i1` is true.
#[test]
def test_face_literal_truth_on_generators_at_endpoints : Bool :=
    let all_four : Bool :=
        match face_literal_truth (cub_face_eq0 cub_i0) {
            Option.some b => b,
            Option.none => false,
        }
        && match face_literal_truth (cub_face_eq0 cub_i1) {
            Option.some b => Bool.not b,
            Option.none => false,
        }
        && match face_literal_truth (cub_face_eq1 cub_i0) {
            Option.some b => Bool.not b,
            Option.none => false,
        }
        && match face_literal_truth (cub_face_eq1 cub_i1) {
            Option.some b => b,
            Option.none => false,
        } in
    all_four