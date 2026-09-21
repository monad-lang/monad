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
use lib::types {
  DebugName, Identifier, Similar, SortLevel, Term, free_level_vars_of,
  level_const, level_subst, union_ids,
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
    // `Term.type_` is the concrete spelling and carries no variable, so
    // it is deliberately NOT special-cased -- the catch-all rebuilds it.
    _ => term_map_children (fn c => subst_levels_term c binds) t,
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
    Term.type_ _ => List.empty,
    Term.lam _dbg typ body => union_ids (free_level_vars typ) (free_level_vars body),
    Term.forall _dbg kind body => union_ids (free_level_vars kind) (free_level_vars body),
    Term.pi arg ret => union_ids (free_level_vars arg) (free_level_vars ret),
    Term.app callee arg => union_ids (free_level_vars callee) (free_level_vars arg),
    Term.quote_ inner => free_level_vars inner,
    Term.ctx _loc inner => free_level_vars inner,
    _ => List.empty,
}

/// Is this `forall` binder a LEVEL binder rather than a type-variable
/// binder? `wrap_level_forall` (`lang/elaborate.mo`) marks one by giving
/// it a SORT as its kind, where `wrap_forall` gives a term binder
/// `Term.type_ 1`.
///
/// Reading the marker with `sort_level_of` covers both spellings, and
/// `Term.type_ 1` is NOT a level binder -- that is the term-binder
/// marker -- so the test is "is a sort AND is at level 0". Nothing else
/// inspects a binder's kind shape, which is what makes this marker safe
/// (see `wrap_level_forall`'s own comment).
///
/// The marker cannot collide with a user-written binder, because there
/// is no way to write one: the grammar has NO `forall` keyword
/// (`ParseTermKind`'s own comment in `lang/types.mo` records this), so
/// every `Term.forall` in the tree is built by `wrap_forall` or
/// `wrap_level_forall`. If a `forall` syntax is ever added, a source
/// binder written at `Prop` would land here and this test would need a
/// real discriminator instead of a level comparison.
#[partial]
pub def is_level_binder_kind (kind : Term) : Bool :=
    match sort_level_of kind {
        Option.some l => match level_const l {
            Option.some n => I64.beq n 0,
            Option.none => false,
        },
        Option.none => false,
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
    let t : Term := Term.pi (Term.type_ 0) inner in
    match subst_levels_term t binds {
        Term.pi _arg ret => sort_term_has_level ret 7,
        _ => false,
    }

/// `Term.type_` is the concrete spelling and carries no variable, so a
/// substitution must pass it through UNCHANGED rather than converting
/// it into the `Term.sort` spelling -- the same spelling-preservation
/// discipline `sort_term_of_level` implements in the other direction.
#[test]
def test_subst_levels_term_leaves_the_concrete_spelling_alone : Bool :=
    let binds : List (Pair Identifier SortLevel) :=
        List.cons (Pair.pair (Identifier.id "u") (SortLevel.concrete 4)) List.empty in
    match subst_levels_term (Term.type_ 1) binds {
        Term.type_ n => I64.beq n 1,
        _ => false,
    }

#[test]
def test_free_level_vars_reaches_under_a_binder : Bool :=
    let inner : Term := Term.sort (SortLevel.var (Identifier.id "u")) in
    let t : Term := Term.forall DebugName.unnamed (Term.type_ 0) inner in
    ids_are_exactly_one (free_level_vars t) (Identifier.id "u")
