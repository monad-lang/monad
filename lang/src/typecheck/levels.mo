/// Level variables: the substitution half of universe polymorphism.
///
/// W1.1 put `SortLevel` and the COMPARISON helpers (`level_const`,
/// `level_eq`, `level_le`, `level_lt`, `sort_level_of`,
/// `sort_term_of_level`, `level_of_type`) in `lang/types.mo`, beside the
/// type they operate on. Those all answer a question about a level
/// without walking a `Term`, so they have no dependency beyond `types`
/// itself.
///
/// These do walk a `Term`, and that is why they live here instead:
/// `subst_levels_term` and `free_level_vars` reuse
/// `term_map_children` (`lang/typecheck/traverse.mo`), and `traverse`
/// imports `types` -- so putting them in `types.mo` is an import CYCLE,
/// not a style choice. Measured, not assumed: the first draft of this
/// work had them there and every dependent file failed with `unbound
/// variable term_map_children`.
///
/// Why levels are name-keyed rather than de Bruijn, which is what makes
/// all of this short: a level variable can only be introduced at a DEF
/// BOUNDARY, so it is free by construction. There is no second index
/// space, and `term_shift`/`term_subst`/`term_permute` need no change --
/// they reach a sort through their existing catch-alls.
use lang::types {
  Identifier, Similar, SortLevel, Term, binder_anon, binder_level, free_level_vars_of,
  level_const, level_subst, sort_level_of, union_ids,
}
use lib::typecheck::traverse {term_map_children}

/// Substitute level variables throughout a TERM.
///
/// Four lines of real work because `term_map_children` already walks all
/// of `Term`'s variants; only the sort arm needs saying, since a level
/// is DATA on that node rather than a child (`traverse.mo` documents
/// `Term.sort` as a leaf for exactly this reason, which is what makes
/// the catch-all safe here).
#[partial]
pub def subst_levels_term (t: Term) (binds: List (Pair Identifier SortLevel)) : Term := match t {
    Term.sort l => Term.sort (level_subst l binds),
    _ => term_map_children (fn c => subst_levels_term c binds) t,
}

/// The level instantiation half (W1.4): bind a call site's level variable
/// from one argument.
///
/// The rule is deliberately narrow. Only a parameter whose type is
/// literally `Sort (var u)` contributes, and only when the argument's own
/// inferred type is a sort; `u` then takes that sort's level, normalized
/// to a concrete numeral when `level_const` folds it (`Sort 1` arrives
/// here as `succ (concrete 0)` from `type_check_sort_full`).
///
/// First binding wins, and everything else is left FREE rather than
/// defaulted -- the same non-committal discipline `solve_typevars`
/// documents, and for the same reason: `level_le` (`lang/types.mo`)
/// answers `false` for a variable it cannot evaluate, so guessing a level
/// the call site did not determine turns a missing constraint into a
/// wrong one. Cumulativity is the unifier's job (`unify_sort`), which is
/// why the MINIMAL binding is the right one here.
///
/// `Sort (max u v)` parameters and non-sort arguments contribute nothing
/// (which of the two operands to bind is not determined); that is the
/// documented completeness gap, not an oversight.
pub def solve_levels (param_ty : Term) (actual_ty : Term) (binds : List (Pair Identifier SortLevel)) : List (Pair Identifier SortLevel) :=
    match sort_level_of param_ty {
        Option.some param_level => match param_level {
            SortLevel.var name => match sort_level_of actual_ty {
                Option.some actual_level =>
                    if level_binds_has name binds
                    then binds
                    else List.cons (Pair.pair name (level_instantiation actual_level)) binds,
                Option.none => binds,
            },
            _ => binds,
        },
        Option.none => binds,
    }

/// A solved level, written as the numeral it folds to when it has one.
/// The solver reads sorts through `type_check_sort_full`, which builds
/// `succ n` rather than `concrete (n + 1)`, so normalizing here is what
/// makes the substituted level compare by `level_eq` without relying on
/// `level_const` at every use.
#[partial]
def level_instantiation (l : SortLevel) : SortLevel := match level_const l {
    Option.some n => SortLevel.concrete n,
    Option.none => l,
}

#[partial]
def level_binds_has (name : Identifier) (binds : List (Pair Identifier SortLevel)) : Bool :=
    match binds {
        List.cons entry rest => match entry {
            Pair.pair key _ =>
                if Similar.similar key name then true else level_binds_has name rest,
        },
        List.empty => false,
    }

/// Every free level variable in a TERM, in first-seen order.
///
/// Spelled out per variant rather than routed through
/// `term_map_children`, because that combinator REBUILDS a term and
/// this one accumulates a list -- the shapes do not match. The arms
/// that matter are the binders and the sort; everything else either
/// holds no level or holds one only under a child listed here.
#[partial]
pub def free_level_vars (t: Term) : List Identifier := match t {
    Term.sort l => free_level_vars_of l,
    Term.lam _dbg typ body => union_ids (free_level_vars typ) (free_level_vars body),
    Term.pi _b arg cod => union_ids (free_level_vars arg) (free_level_vars cod),
    Term.app callee arg => union_ids (free_level_vars callee) (free_level_vars arg),
    Term.quote_ inner => free_level_vars inner,
    Term.ctx _loc inner => free_level_vars inner,
    // Spelled out rather than left to the catch-all: a cubical primitive's
    // arguments are ordinary `Term`s and `PathP`'s first argument is a LINE
    // OF TYPES (`I -> Sort l`), so a level variable can and does occur under
    // one. Falling through to `List.empty` would drop it, and
    // `wrap_level_forall` would then fail to generalize a level the def
    // really is polymorphic in.
    Term.cubical c => match c { { prim := _, args := args } => free_level_vars_of_terms args },
    _ => List.empty,
}

#[partial]
def free_level_vars_of_terms (ts : List Term) : List Identifier := match ts {
    List.empty => List.empty,
    List.cons x rest => union_ids (free_level_vars x) (free_level_vars_of_terms rest),
}

// ─── Test helpers ─────────────────────────────────────────────────────
//
// Written out because the self-hosted parser has no NESTED patterns:
// `List.cons a (List.cons b List.empty)` does not parse, so a shape
// assertion has to be spelled as a function over the list.

/// Is `ids` exactly `[want]`?
def ids_are_exactly_one (ids : List Identifier) (want : Identifier) : Bool :=
    match ids {
        List.cons hd rest =>
            if List.is_empty rest then Similar.similar hd want else false,
        List.empty => false,
    }

/// Is `ids` exactly `[a, b]`, in that order?
def ids_are_exactly_two (ids : List Identifier) (a : Identifier) (b : Identifier) : Bool :=
    match ids {
        List.cons hd rest =>
            if Similar.similar hd a then ids_are_exactly_one rest b else false,
        List.empty => false,
    }

/// Is `t` a sort whose level is concretely `want`?
#[partial]
def sort_term_has_level (t : Term) (want : I64) : Bool :=
    match t {
        Term.sort l => match level_const l {
            Option.some n => I64.beq n want,
            Option.none => false,
        },
        _ => false,
    }

// ─── Tests ────────────────────────────────────────────────────────────

#[test]
def test_free_level_vars_of_finds_a_bare_var : Bool :=
    ids_are_exactly_one (free_level_vars_of (SortLevel.var (Identifier.id "u"))) (Identifier.id "u")

#[test]
def test_free_level_vars_of_concrete_is_empty : Bool :=
    List.is_empty (free_level_vars_of (SortLevel.concrete 3))

/// `max u (succ v)` reaches BOTH sides and through a `succ`. A version
/// that only recursed on `left`, or that treated `succ` as a leaf,
/// still passes the two tests above -- this is the one that separates
/// them.
#[test]
def test_free_level_vars_of_reaches_both_sides_and_through_succ : Bool :=
    let l : SortLevel := SortLevel.max (SortLevel.var (Identifier.id "u"))
                                       (SortLevel.succ (SortLevel.var (Identifier.id "v"))) in
    ids_are_exactly_two (free_level_vars_of l) (Identifier.id "u") (Identifier.id "v")

#[test]
def test_level_subst_replaces_a_var : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        List.cons (Pair.pair (Identifier.id "u") (SortLevel.concrete 2)) List.empty in
    match level_const (level_subst (SortLevel.var (Identifier.id "u")) binds) {
        Option.some n => I64.beq n 2,
        Option.none => false,
    }

/// An UNMENTIONED variable is left alone, not defaulted. The solver has
/// to stay partial: defaulting here would silently commit a level the
/// call site never determined.
#[test]
def test_level_subst_leaves_an_unmentioned_var_alone : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        List.cons (Pair.pair (Identifier.id "u") (SortLevel.concrete 2)) List.empty in
    match level_subst (SortLevel.var (Identifier.id "other")) binds {
        SortLevel.var name => Similar.similar name (Identifier.id "other"),
        _ => false,
    }

#[test]
def test_level_subst_goes_under_succ_and_max : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        List.cons (Pair.pair (Identifier.id "u") (SortLevel.concrete 1)) List.empty in
    let l : SortLevel := SortLevel.max (SortLevel.succ (SortLevel.var (Identifier.id "u")))
                                       (SortLevel.concrete 0) in
    match level_const (level_subst l binds) {
        // max (succ 1) 0 = 2
        Option.some n => I64.beq n 2,
        Option.none => false,
    }

#[test]
def test_subst_levels_term_rewrites_a_sort : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        List.cons (Pair.pair (Identifier.id "u") (SortLevel.concrete 4)) List.empty in
    sort_term_has_level (subst_levels_term (Term.sort (SortLevel.var (Identifier.id "u"))) binds) 4

/// The substitution must reach a sort nested under a BINDER, which is
/// where a generalized level actually sits. A `subst_levels_term` that
/// handled only a bare top-level sort passes the test above and fails
/// this one.
#[test]
def test_subst_levels_term_reaches_under_a_binder : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        List.cons (Pair.pair (Identifier.id "u") (SortLevel.concrete 7)) List.empty in
    let inner : Term := Term.sort (SortLevel.var (Identifier.id "u")) in
    let t : Term := Term.pi binder_anon (Term.sort (SortLevel.concrete 0)) inner in
    match subst_levels_term t binds {
        Term.pi _ _arg ret => sort_term_has_level ret 7,
        _ => false,
    }

/// A substitution must pass a concrete level through UNCHANGED: a
/// concrete level holds no variable, so there is nothing to substitute.
/// The test used to be named for "spelling" -- it asserted that
/// `subst_levels_term` returned the SPELLING it was handed rather than
/// converting to the other one. There is one spelling now, so what is
/// left to pin is the level itself, read back through the local
/// `sort_term_has_level`.
#[test]
def test_subst_levels_term_leaves_a_concrete_level_alone : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        [(Pair.pair (Identifier.id "u") (SortLevel.concrete 4))] in
    sort_term_has_level (subst_levels_term (Term.sort (SortLevel.concrete 1)) binds) 1

#[test]
def test_free_level_vars_reaches_under_a_binder : Bool :=
    let inner : Term := Term.sort (SortLevel.var (Identifier.id "u")) in
    let t : Term := Term.pi (binder_level (Identifier.id "k")) (Term.sort (SortLevel.concrete 0)) inner in
    ids_are_exactly_one (free_level_vars t) (Identifier.id "u")

// ─── W1.4: level instantiation at call sites ──────────────────────────

#[partial]
def bound_level_of (binds : List (Pair Identifier SortLevel)) (name : Identifier) : Option SortLevel :=
    match binds {
        List.cons entry rest => match entry {
            Pair.pair key val =>
                if Similar.similar key name
                then Option.some val
                else bound_level_of rest name,
        },
        List.empty => Option.none,
    }

#[test]
def test_solve_levels_binds_a_concrete_level : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.var (Identifier.id "u")))
                     (Term.sort (SortLevel.concrete 1)) List.empty in
    match bound_level_of binds (Identifier.id "u") {
        Option.some l => match l {
            SortLevel.concrete n => I64.beq n 1,
            _ => false,
        },
        Option.none => false,
    }

/// `type_check_sort_full` builds an argument's sort as `succ n`, so the
/// solver must normalize it: the stored level is literally `concrete 1`,
/// not `succ (concrete 0)`. A version that skipped the fold passes the
/// concrete test above and fails this one.
#[test]
def test_solve_levels_normalizes_a_succ : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.var (Identifier.id "u")))
                     (Term.sort (SortLevel.succ (SortLevel.concrete 0))) List.empty in
    match bound_level_of binds (Identifier.id "u") {
        Option.some l => match l {
            SortLevel.concrete n => I64.beq n 1,
            _ => false,
        },
        Option.none => false,
    }

/// A variable solved by an earlier argument keeps that binding: a later
/// argument cannot retract a level the call site already determined.
#[test]
def test_solve_levels_first_binding_wins : Bool :=
    let first : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.var (Identifier.id "u")))
                     (Term.sort (SortLevel.concrete 1)) List.empty in
    let second : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.var (Identifier.id "u")))
                     (Term.sort (SortLevel.concrete 2)) first in
    match bound_level_of second (Identifier.id "u") {
        Option.some l => match l {
            SortLevel.concrete n => I64.beq n 1,
            _ => false,
        },
        Option.none => false,
    }

/// Nothing is defaulted: an argument whose type is not a sort leaves the
/// variable free (an empty substitution, not `u := 1`).
#[test]
def test_solve_levels_leaves_a_non_sort_alone : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.var (Identifier.id "u"))) Term.hole List.empty in
    List.is_empty binds

/// `Sort (max u v)` does not say which operand to bind, so it binds
/// neither -- the documented completeness gap, pinned so it cannot start
/// guessing silently.
#[test]
def test_solve_levels_ignores_a_max_parameter : Bool :=
    let max_param : Term := Term.sort (SortLevel.max (SortLevel.var (Identifier.id "u"))
                                                     (SortLevel.var (Identifier.id "v"))) in
    let binds : List (Pair Identifier SortLevel) :=
        solve_levels max_param (Term.sort (SortLevel.concrete 1)) List.empty in
    List.is_empty binds

/// A concrete parameter's level is not a variable, so there is nothing to
/// solve even when the argument is a different sort.
#[test]
def test_solve_levels_ignores_a_concrete_parameter : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.concrete 1))
                     (Term.sort (SortLevel.concrete 2)) List.empty in
    List.is_empty binds

/// Two level VARIABLES: the parameter's takes the argument's, so a later
/// `Sort v` is CARRIED rather than guessed at.
#[test]
def test_solve_levels_binds_a_level_var_to_a_level_var : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.var (Identifier.id "u")))
                     (Term.sort (SortLevel.var (Identifier.id "v"))) List.empty in
    match bound_level_of binds (Identifier.id "u") {
        Option.some l => match l {
            SortLevel.var n => Similar.similar n (Identifier.id "v"),
            _ => false,
        },
        Option.none => false,
    }

/// A repeated variable does not grow the substitution: first binding wins,
/// one entry.
#[test]
def test_solve_levels_does_not_duplicate_a_binding : Bool :=
    let first : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.var (Identifier.id "u")))
                     (Term.sort (SortLevel.concrete 1)) List.empty in
    let second : List (Pair Identifier SortLevel) :=
        solve_levels (Term.sort (SortLevel.var (Identifier.id "u")))
                     (Term.sort (SortLevel.concrete 2)) first in
    match second {
        List.cons _ rest => List.is_empty rest,
        List.empty => false,
    }
