// Pins on the CHECKER half of the cubical name-binding (Stage 1 step 3,
// plans/type-system/univalence.md): a resolved reference to a
// `#[cubical "..."]`-marked name must come back from `type_check` as the
// `Term.cubical` it stands for, not as the free variable the source
// spelling suggests.
//
// TERM-SHAPED, not accept/reject, and the reason is the hazard itself:
// the marked declarations carry real declared signatures
// (`ineg : I -> I`), so `ineg i0` is ACCEPTED by the ordinary
// signature-driven path too -- an accept/reject pin passes with the
// rewrite missing, which is precisely the failure mode
// (`try_type_check_def_call` typing the call fine and the rewrite
// silently never happening) that putting the cubical probe FIRST in
// `type_check_app` exists to prevent. Reading `tt.term` is the only
// observation that discriminates. `type_check`'s `TypedTerm` is `pub`
// and its `.term` field is readable, so no export widening is needed.
//
// The scope is built by the REAL parse + scope-build pipeline
// (`try_parse_decls` + `build_scope_from_decls`) over the exact
// twelve-declaration source of `proofs/src/cubical.mo`, because what is
// under test includes the marker's survival from source text to
// `ScopeData.cubical_prims`. The same string is pinned from the scope
// side in `lang/src/tests/cubical_bind_tests.mo`; if the declaration
// list ever changes, both copies change with it.

use lang::module {try_parse_decls}
use lang::scope {build_scope_from_decls}
use lang::typecheck::cubical {peels_to_bare_interval}
use lang::typecheck::infer {empty_local_types, empty_locals, type_check}
use lang::typecheck::whnf {whnf}
use lang::types {
  CubicalPrim, ModulePath, Scope, ScopeData, SortLevel, Similar, Term, binder_named,
  cub, cub_face_eq0, cub_face_eq1, cub_hcomp, cub_i0, cub_i1, cub_imeet,
  cub_ijoin, cub_ineg, cub_interval, cub_is_one, cub_pathp, cub_transp,
  cubical_prim_eq, sentinel, sort_n,
}
use init::borrow {Borrow}

def checker_synthetic_path : ModulePath :=
    ModulePath.mp (List.cons (Identifier.id "proofs_checker") List.empty)

/// The twelve Stage 1+2+3+4+5 declarations, spelled exactly as they are
/// in `proofs/src/cubical.mo`.
def cubical_decls_source : String :=
    String.concat "#[cubical \"interval\"] def I : Type\n"
    (String.concat "#[cubical \"i0\"] def i0 : I\n"
    (String.concat "#[cubical \"i1\"] def i1 : I\n"
    (String.concat "#[cubical \"ineg\"] def ineg (i : I) : I\n"
    (String.concat "#[cubical \"imeet\"] def imeet (i : I) (j : I) : I\n"
    (String.concat "#[cubical \"ijoin\"] def ijoin (i : I) (j : I) : I\n"
    (String.concat "#[cubical \"pathp\"] def PathP (A : I -> Type) (a : A i0) (b : A i1) : Type\n"
    (String.concat "#[cubical \"transp\"] def transp (A : I -> Type) (a : A i0) : A i1\n"
    (String.concat "#[cubical \"face_eq0\"] def face_eq0 (i : I) : I\n"
    (String.concat "#[cubical \"face_eq1\"] def face_eq1 (i : I) : I\n"
    (String.concat "#[cubical \"is_one\"] def is_one (i : I) : Type\n"
    "#[cubical \"hcomp\"] def hcomp (A : Type) (phi : I) (u : I -> is_one phi -> A) (u0 : A) : A\n"))))))))))

/// The scope the checker sees when `proofs/src/cubical.mo` is loaded.
/// A parse failure yields an empty scope, which makes every pin below
/// fail rather than silently pass against a scope with nothing bound.
def cubical_scope : Scope :=
    let sd : ScopeData :=
        match try_parse_decls cubical_decls_source {
            Option.some decl_list => build_scope_from_decls checker_synthetic_path decl_list,
            Option.none => build_scope_from_decls checker_synthetic_path List.empty,
        } in
    {
        module_id := checker_synthetic_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// The same declarations WITHOUT any `#[cubical]` markers -- the
/// negative control's scope. These are ordinary body-less defs with
/// ordinary declared signatures, which is what a user's own
/// same-named defs are.
def unmarked_scope : Scope :=
    let source : String :=
        String.concat "def I : Type\n"
        (String.concat "def i0 : I\n"
        (String.concat "def i1 : I\n"
        (String.concat "def ineg (i : I) : I\n"
        (String.concat "def imeet (i : I) (j : I) : I\n"
        "def ijoin (i : I) (j : I) : I")))) in
    let sd : ScopeData :=
        match try_parse_decls source {
            Option.some decl_list => build_scope_from_decls checker_synthetic_path decl_list,
            Option.none => build_scope_from_decls checker_synthetic_path List.empty,
        } in
    {
        module_id := checker_synthetic_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// A free (global) reference by name -- `sentinel` is what marks a var as
/// unbound-and-resolved-by-name, the same helper idiom
/// `lang/src/tests/whnf_tests.mo` uses.
def free_var (nm : String) : Term := Term.var sentinel (DebugName.named (Identifier.id nm))

/// Does checking `t` in `succeed and produce a checked term that is
/// exactly the primitive `p` applied to no arguments?
def checks_as_bare_prim (s : Scope) (t : Term) (p : CubicalPrim) : Bool :=
    match type_check t Term.hole s empty_local_types empty_locals {
        ok tt =>
            match tt.term {
                // Two-step match: a variant constructor with a single
                // struct payload has no field names at the constructor
                // level, so the payload match is its own `match`
                // (verified -- the directly nested form does not parse).
                Term.cubical c =>
                    match c {
                        { prim := q, args := as } => cubical_prim_eq q p && List.is_empty as,
                    },
                _ => false,
            },
        err _ => false,
    }

/// Does checking `t` in `s` succeed and produce a checked term that is
/// `p` applied to exactly one checked argument, itself the bare
/// primitive `arg`?
def checks_as_prim_applied_to (s : Scope) (t : Term) (p : CubicalPrim) (arg : CubicalPrim) : Bool :=
    match type_check t Term.hole s empty_local_types empty_locals {
        ok tt =>
            match tt.term {
                Term.cubical c =>
                    match c {
                        { prim := q, args := as } =>
                            cubical_prim_eq q p
                                && match as {
                                    List.cons a rest =>
                                        List.is_empty rest
                                            && match a {
                                                Term.cubical c2 =>
                                                    match c2 {
                                                        { prim := q2, args := as2 } =>
                                                            cubical_prim_eq q2 arg && List.is_empty as2,
                                                    },
                                                _ => false,
                                            },
                                    List.empty => false,
                                },
                    },
                _ => false,
            },
        err _ => false,
    }

/// Does checking `t` in `s` succeed and produce a checked term that is
/// `p` applied to exactly two checked arguments, themselves the bare
/// primitives `arg1` then `arg2` -- pinning spine ORDER, since a
/// substitution that peels arguments in the wrong direction silently
/// swaps them.
def checks_as_prim_applied_to_two (s : Scope) (t : Term) (p : CubicalPrim)
    (arg1 : CubicalPrim) (arg2 : CubicalPrim) : Bool :=
    match type_check t Term.hole s empty_local_types empty_locals {
        ok tt =>
            match tt.term {
                Term.cubical c =>
                    match c {
                        { prim := q, args := as } =>
                            cubical_prim_eq q p
                                && match as {
                                    List.cons a1 rest1 =>
                                        match rest1 {
                                            List.cons a2 rest2 =>
                                                List.is_empty rest2
                                                    && arg_is_bare_prim a1 arg1
                                                    && arg_is_bare_prim a2 arg2,
                                            List.empty => false,
                                        },
                                    List.empty => false,
                                },
                    },
                _ => false,
            },
        err _ => false,
    }

/// Is `t` the cubical term of the bare primitive `p`?
def arg_is_bare_prim (t : Term) (p : CubicalPrim) : Bool :=
    match t {
        Term.cubical c =>
            match c {
                { prim := q, args := as } => cubical_prim_eq q p && List.is_empty as,
            },
        _ => false,
    }

/// Does checking `t` in `s` succeed WITHOUT rewriting the head into a
/// cubical term? The under-applied and unmarked cases must both land
/// here: the rewrite owns saturated calls on MARKED names only.
def checks_without_cubical_rewrite (s : Scope) (t : Term) : Bool :=
    match type_check t Term.hole s empty_local_types empty_locals {
        ok tt =>
            match tt.term {
                Term.cubical _ => false,
                _ => true,
            },
        err _ => false,
    }

/// Does checking `t` against `expected` in `s` fail? The REJECTION pins:
/// a cubical call with an argument that is not a dimension must not
/// check, whichever path types it. The expected type is a parameter
/// because the Stage 2 rules -- path abstraction especially -- only
/// exist relative to a `PathP` expected type.
def check_fails_against (s : Scope) (t : Term) (expected : Term) : Bool :=
    match type_check t expected s empty_local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

/// Does checking `t` against `expected` in `s` fail, carrying a local
/// TYPE list? The sym-direction reject needs a local `p` in scope --
/// through the empty-list variant it would fail for the WRONG reason
/// (an unbound variable), not because the endpoints disagree.
def check_fails_against_with (s : Scope) (local_types : List Term) (t : Term)
    (expected : Term) : Bool :=
    match type_check t expected s local_types empty_locals {
        err _ => true,
        ok _ => false,
    }

/// Does checking `t` in `s` fail with NO expected type? The Stage 1
/// rejects are all formation-independent -- the rewrite either happens
/// or the call is ill-typed outright.
def check_fails_in (s : Scope) (t : Term) : Bool :=
    check_fails_against s t Term.hole

// ─── the rewrite itself ───────────────────────────────────────────────

#[test]
def test_bare_interval_reference_is_the_cubical_term : Bool :=
    // `I` referenced bare: arity-0, so the reference IS the term --
    // `type_check_free_var`'s cubical arm, not the declared-signature
    // fallback.
    checks_as_bare_prim cubical_scope (free_var "I") CubicalPrim.interval

#[test]
def test_bare_endpoint_references_are_the_cubical_terms : Bool :=
    checks_as_bare_prim cubical_scope (free_var "i0") CubicalPrim.i0
        && checks_as_bare_prim cubical_scope (free_var "i1") CubicalPrim.i1

#[test]
def test_saturated_call_rewrites_to_cubical : Bool :=
    // `ineg i0`: the cubical probe in `type_check_app` owns the call,
    // and the argument is itself rewritten (it is checked by the same
    // checker, recursively) before being stored in `args`.
    checks_as_prim_applied_to
        cubical_scope (Term.app (free_var "ineg") (free_var "i0")) CubicalPrim.ineg CubicalPrim.i0

#[test]
def test_two_argument_call_rewrites_to_cubical : Bool :=
    // `imeet i0 i1` -- nested application spine; `flatten_call_spine`
    // must collect both arguments in order.
    let spine : Term := Term.app (Term.app (free_var "imeet") (free_var "i0")) (free_var "i1") in
    checks_as_prim_applied_to_two cubical_scope spine CubicalPrim.imeet CubicalPrim.i0 CubicalPrim.i1

// ─── what must NOT be rewritten ────────────────────────────────────────

#[test]
def test_under_applied_call_is_not_rewritten : Bool :=
    // `imeet i0` -- one argument short of the arity. The probe declines,
    // the declared-signature path types it, and the term stays an
    // application whose type is the residual `I -> I`. Checking must
    // still SUCCEED: the declared signatures exist to carry exactly
    // this case.
    checks_without_cubical_rewrite cubical_scope (Term.app (free_var "imeet") (free_var "i0"))

#[test]
def test_unmarked_name_is_not_rewritten : Bool :=
    // Same names, no markers: the binding is keyed off the MARKER, never
    // the bare spelling, so these stay ordinary defs.
    checks_without_cubical_rewrite unmarked_scope (Term.app (free_var "ineg") (free_var "i0"))
        && checks_without_cubical_rewrite unmarked_scope (free_var "I")

// ─── rejection ──────────────────────────────────────────────────────────

#[test]
def test_cubical_call_rejects_non_interval_argument : Bool :=
    // `ineg Type` -- a sort is not a dimension. Both the cubical probe
    // (argument checked against `I`) and the declared-signature path
    // reject it; the pin holds the line either way, and is the one
    // genuinely negative claim this file makes about the rewrite.
    check_fails_in cubical_scope (Term.app (free_var "ineg") (sort_n 1))

// ─── Stage 2: PathP formation ───────────────────────────────────────────
//
// The formation rule is pinned TERM-SHAPED as well as by rejection:
// the rewritten call must come back as the cubical `pathp` primitive
// carrying the checked LINE (a `Term.lam`), not stay an app spine on
// the free `PathP` -- the declared-signature path would ACCEPT the
// call too, so acceptance alone does not discriminate.

/// The line every formation pin uses: `fn i => I`, the constant line
/// into `Type`. The binder annotation is a hole on purpose -- the
/// formation rule INFERS the line, and a hole domain is exactly the
/// shape `path_line_dom_ok` accepts.
def const_line : Term :=
    Term.lam (binder_named (Identifier.id "i")) Term.hole (free_var "I")

/// The saturated source spine `PathP line left right`, with the
/// endpoints in their SOURCE spelling so the pins exercise the rewrite
/// on the way through, exactly as a real call site would.
def pathp_call (line : Term) (left : String) (right : String) : Term :=
    Term.app (Term.app (Term.app (free_var "PathP") line) (free_var left))
        (free_var right)

/// Does checking `t` against `expected` in `s` succeed and come back as
/// the cubical `pathp` primitive applied to exactly the checked line,
/// `left`, `right` -- with result type a sort, as a former of types must
/// produce?
def checks_as_pathp (s : Scope) (t : Term) (expected : Term)
    (left : CubicalPrim) (right : CubicalPrim) : Bool :=
    match type_check t expected s empty_local_types empty_locals {
        // Two-step match, same reason as `checks_as_bare_prim` above: `ok`
        // is a variant constructor with a single struct payload, so the
        // payload's own record pattern is a second `match` -- one
        // destructure of `tt`, not two field reads (`.typ` then `.term`).
        ok tt =>
            match tt {
                { term := tm, typ := ty } =>
                    match ty {
                        Term.sort _ =>
                            match tm {
                                Term.cubical c =>
                                    match c {
                                        { prim := q, args := as } =>
                                            cubical_prim_eq q CubicalPrim.pathp
                                                && match as {
                                                    // Exactly three args, pinned by the
                                                    // peeling below reaching `List.empty` --
                                                    // the arity table rejects any other
                                                    // count at formation, so this match
                                                    // is a shape read, not an arity check.
                                                    List.cons ln rest =>
                                                        match ln {
                                                            Term.lam _dbg _dom _body =>
                                                                match rest {
                                                                    List.cons lft rest2 =>
                                                                        match rest2 {
                                                                            List.cons rgt rest3 =>
                                                                                List.is_empty rest3
                                                                                    && arg_is_bare_prim lft left
                                                                                    && arg_is_bare_prim rgt right,
                                                                            List.empty => false,
                                                                        },
                                                                    List.empty => false,
                                                                },
                                                            _ => false,
                                                        },
                                                    List.empty => false,
                                                },
                                    },
                                _ => false,
                            },
                        _ => false,
                    },
            },
        err _ => false,
    }

#[test]
def test_pathp_formation_checks_and_rewrites : Bool :=
    // `PathP (fn i => I) i0 i1` checks against `Type 1`: the line is a
    // function out of the interval into a sort, both endpoints are
    // dimensions, and the checked term is the cubical primitive.
    checks_as_pathp cubical_scope (pathp_call const_line "i0" "i1") (sort_n 1)
        CubicalPrim.i0 CubicalPrim.i1

#[test]
def test_pathp_rejects_a_line_not_out_of_the_interval : Bool :=
    // `fn (i : Type) => I`: a dimension binder is the only domain the
    // line rule accepts -- a sort domain is not the interval.
    check_fails_in cubical_scope
        (pathp_call
            (Term.lam (binder_named (Identifier.id "i")) (sort_n 1) (free_var "I"))
            "i0" "i1")

#[test]
def test_pathp_rejects_a_line_not_into_a_sort : Bool :=
    // `fn i => i0`: the line lands in the interval, and the result sort
    // is read off the line's codomain -- there is none to read.
    check_fails_in cubical_scope
        (pathp_call
            (Term.lam (binder_named (Identifier.id "i")) Term.hole (free_var "i0"))
            "i0" "i1")

#[test]
def test_pathp_rejects_an_endpoint_not_in_the_line : Bool :=
    // `PathP (fn i => I) (fn j => i0) i1`: the left endpoint is a
    // function, but the line's codomain at `i0` is the interval -- the
    // endpoints are checked AGAINST `A i0`/`A i1`, not merely collected.
    check_fails_in cubical_scope
        (Term.app (Term.app (Term.app (free_var "PathP") const_line)
            (Term.lam (binder_named (Identifier.id "j")) Term.hole (free_var "i0")))
            (free_var "i1"))

// ─── Stage 2: path abstraction (check_path_lam) ──────────────────────────

/// Does checking `t` against `expected` in `s` succeed and come back as
/// a lambda whose BINDER is the bare interval? The binder type is the
/// pin: the written annotation may be a hole, but the rule binds a
/// dimension, and the checked term records that. The local TYPE list is
/// a parameter because the boundary pins need a local `p` in scope.
def checks_with_interval_binder (s : Scope) (local_types : List Term)
    (t : Term) (expected : Term) : Bool :=
    match type_check t expected s local_types empty_locals {
        ok tt =>
            match tt.term {
                Term.lam _dbg binder_typ _body => peels_to_bare_interval binder_typ,
                _ => false,
            },
        err _ => false,
    }

#[test]
def test_path_abstraction_checks_with_an_interval_binder : Bool :=
    // `fn i => i0` against `PathP (fn i => I) i0 i0`: both boundaries
    // agree with the constantly-`i0` body, so the abstraction is
    // accepted -- and the checked binder is the interval itself, not
    // the hole the source wrote.
    checks_with_interval_binder cubical_scope empty_local_types
        (Term.lam (binder_named (Identifier.id "i")) Term.hole (free_var "i0"))
        (cub_pathp const_line (cub_i0) (cub_i0))

#[test]
def test_path_abstraction_rejects_a_wrong_i1_boundary : Bool :=
    // Same body against `PathP (fn i => I) i0 i1`: the body is
    // constantly `i0`, so at `i1` it disagrees with the type's right
    // endpoint.
    check_fails_against cubical_scope
        (Term.lam (binder_named (Identifier.id "i")) Term.hole (free_var "i0"))
        (cub_pathp const_line (cub_i0) (cub_i1))

#[test]
def test_path_abstraction_rejects_a_wrong_i0_boundary : Bool :=
    // `fn i => i1` against the same type: the LEFT boundary is the one
    // that disagrees this time -- both directions of the rule are
    // pinned, not just the first one the walk hits.
    check_fails_against cubical_scope
        (Term.lam (binder_named (Identifier.id "i")) Term.hole (free_var "i1"))
        (cub_pathp const_line (cub_i0) (cub_i1))

#[test]
def test_path_abstraction_rejects_a_non_interval_binder : Bool :=
    // `fn (i : Type) => i0`: the annotation must check AS the bare
    // interval; a sort is not a dimension, even though both boundaries
    // would otherwise agree.
    check_fails_against cubical_scope
        (Term.lam (binder_named (Identifier.id "i")) (sort_n 1) (free_var "i0"))
        (cub_pathp const_line (cub_i0) (cub_i0))

// ─── Stage 2: path application and the stuck-endpoint mitigation ──────────

/// The expected type of a local `p : PathP (fn i => I) i0 i1`, as a raw
/// term: the elimination rule peels it, nothing checks it.
def path_typ : Term := cub_pathp const_line (cub_i0) (cub_i1)

/// A de Bruijn local at `idx` named `nm`: `type_check_var` resolves by
/// index through the local TYPE list, so the pins can carry the type in
/// `local_types` without hand-building a `LocalScope`.
def local_at (idx : I64) (nm : String) : Term :=
    Term.var idx (DebugName.named (Identifier.id nm))

#[test]
def test_path_applied_at_an_endpoint_returns_the_boundary : Bool :=
    // `p i0` for a stuck local `p`: whnf cannot reduce a path
    // application whose head is a variable -- the incompleteness the
    // elimination arm exists to patch -- so the checked term must come
    // back as the LEFT endpoint the path's own type carries.
    match type_check (Term.app (local_at 0 "p") (free_var "i0")) Term.hole
        cubical_scope (List.cons path_typ empty_local_types) empty_locals {
        ok tt => arg_is_bare_prim tt.term CubicalPrim.i0,
        err _ => false,
    }

#[test]
def test_path_applied_at_a_stuck_dimension_stays_an_application : Bool :=
    // `p q` for a stuck local dimension `q : I`: not an endpoint, so
    // the mitigation declines and the checked term is the application
    // itself -- the rule rewrites ONLY at the boundary.
    let local_types : List Term :=
        List.cons cub_interval (List.cons path_typ empty_local_types) in
    match type_check (Term.app (local_at 1 "p") (local_at 0 "q")) Term.hole
        cubical_scope local_types empty_locals {
        ok tt =>
            match tt.term {
                Term.app _f _a => true,
                _ => false,
            },
        err _ => false,
    }

// ─── Stage 2: boundary normalization (the term-level `sym`) ──────────────
//
// `fn i => p (ineg i)` against `PathP (fn i => I) i1 i0` is `sym p` with
// the constant line: the endpoints SWAP. The substituted boundaries are
// `p (ineg i0)` and `p (ineg i1)` -- stuck applications whose dimensions
// whnf folds to the opposite endpoint, and which still do not reduce --
// so the check succeeds only because `normalize_path_boundary` rewrites
// each to the boundary value `p`'s own type carries. This is the one
// pin on the normalizer + stuck rewriter pair, and the direction pin
// below it is what keeps the rewrite honest about WHICH endpoint.

/// `fn i => p (ineg i)` with `p` one binder out: the body is a path
/// application at the negated dimension.
def sym_body : Term :=
    Term.lam (binder_named (Identifier.id "i")) Term.hole
        (Term.app (local_at 1 "p")
            (cub_ineg (local_at 0 "i")))

#[test]
def test_sym_boundaries_check_through_the_stuck_rewriter : Bool :=
    checks_with_interval_binder cubical_scope (List.cons path_typ empty_local_types)
        sym_body (cub_pathp const_line (cub_i1) (cub_i0))

#[test]
def test_sym_rejects_when_the_endpoints_do_not_swap : Bool :=
    // The SAME body against the UNswapped type: if the boundary
    // comparison were vacuous -- or the rewriter answered the wrong
    // endpoint -- this would check. It must not: at `i0` the body
    // normalizes to `p`'s RIGHT endpoint, and the type's left is `i0`.
    check_fails_against_with cubical_scope (List.cons path_typ empty_local_types)
        sym_body (cub_pathp const_line (cub_i0) (cub_i1))

// ─── Stage 3: transp ───────────────────────────────────────────────────
//
// `transp (A : I -> Sort l) (a : A i0) : A i1` -- transport along a line
// of types, chosen over CCHM's `comp` so that this stage lands without
// the face lattice. The typing mirrors PathP's line discipline exactly
// (a function out of the interval into a sort); the reduction is the
// new thing: a CONSTANT family -- both endpoint substitutions yield
// the same body -- reduces to the element, everything else stays
// stuck. Constancy is read by substituting both endpoints into the
// line's body and comparing, never by walking for the binder's
// occurrences.

/// The saturated source spine `transp line elem`, with the head in its
/// source spelling so the pins exercise the cubical probe on the way
/// through, exactly as a real call site would.
def transp_call (line : Term) (elem : Term) : Term :=
    Term.app (Term.app (free_var "transp") line) elem

/// Does checking `t` against `expected` in `s` succeed and come back as
/// the cubical `transp` primitive over exactly a LAMBDA line and an
/// element matching `elem_is`? The line must be a lambda because the
/// rule checks the line through the ordinary binder machinery and
/// rebuilds from the checked one; the element is a PREDICATE because
/// its shape is pin-specific -- a bare dimension for the constant
/// family, a path lambda for the varying one.
def checks_as_transp (s : Scope) (t : Term) (expected : Term)
    (elem_is : Term -> Bool) : Bool :=
    match type_check t expected s empty_local_types empty_locals {
        ok tt =>
            match tt.term {
                Term.cubical c =>
                    match c {
                        { prim := q, args := as } =>
                            cubical_prim_eq q CubicalPrim.transp
                                && match as {
                                    // Exactly two args, pinned by the peeling
                                    // below reaching `List.empty` -- the arity
                                    // table rejects any other count at
                                    // formation, so this match is a shape
                                    // read, not an arity check.
                                    List.cons ln rest =>
                                        match ln {
                                            Term.lam _dbg _dom _body =>
                                                match rest {
                                                    List.cons el rest2 =>
                                                        List.is_empty rest2 && elem_is el,
                                                    List.empty => false,
                                                },
                                            _ => false,
                                        },
                                    List.empty => false,
                                },
                    },
                _ => false,
            },
        err _ => false,
    }

#[test]
def test_transp_formation_checks_and_rewrites : Bool :=
    // `transp (fn i => I) i0` checks against `I` -- spelled as the
    // cubical interval, because that is what CHECKING `I` produces, and
    // the result type `A i1` is compared through unify, which reduces
    // the application to exactly that term. The line is a function out
    // of the interval into a sort, the element is a dimension at `A i0`,
    // and the checked term is the cubical primitive.
    checks_as_transp cubical_scope (transp_call const_line (free_var "i0"))
        cub_interval (fn el => arg_is_bare_prim el CubicalPrim.i0)

#[test]
def test_transp_rejects_a_line_not_out_of_the_interval : Bool :=
    // `transp (fn (i : Type) => I) i0`: the line discipline is
    // `PathP`'s -- a dimension binder is the only domain a line over
    // the interval can have.
    check_fails_in cubical_scope
        (transp_call
            (Term.lam (binder_named (Identifier.id "i")) (sort_n 1) (free_var "I"))
            (free_var "i0"))

#[test]
def test_transp_rejects_a_line_not_into_a_sort : Bool :=
    // `transp (fn i => i0) i0`: the line lands in the interval, and a
    // family of DIMENSIONS is not a family of types -- the sort guard
    // is read off the line's codomain, and there is none.
    check_fails_in cubical_scope
        (transp_call
            (Term.lam (binder_named (Identifier.id "i")) Term.hole (free_var "i0"))
            (free_var "i0"))

#[test]
def test_transp_rejects_a_line_into_a_non_sort_family : Bool :=
    // The sort guard, ISOLATED. The line is `fn i => p` for a local
    // `p : PathP (fn i => I) i0 i1` -- the family lands in `p`'s own
    // TYPE, a `PathP` term, not a sort. The element `q : p` (local 1)
    // checks fine against `A i0 = p`, and the expected type is a
    // hole, so the ONLY rule that can reject this call is the guard
    // reading the line's codomain. A family of paths is not a family
    // of types, even when both the line and the element check.
    check_fails_against_with cubical_scope
        (List.cons path_typ (List.cons (local_at 0 "p") empty_local_types))
        (transp_call
            (Term.lam (binder_named (Identifier.id "i")) Term.hole (local_at 1 "p"))
            (local_at 1 "q"))
        Term.hole

#[test]
def test_transp_rejects_an_element_not_in_the_line : Bool :=
    // `transp (fn i => I) (fn j => i0)`: the element is checked AGAINST
    // `A i0` -- the interval -- not merely collected, and a function is
    // not a dimension.
    check_fails_in cubical_scope
        (transp_call const_line
            (Term.lam (binder_named (Identifier.id "j")) Term.hole (free_var "i0")))

// ─── Stage 3: the direction of the endpoint reads ───────────────────────
//
// The pins above cannot discriminate WHICH endpoint each read uses --
// over a constant line, `A i0` and `A i1` are the same type. This one
// needs a family that genuinely varies.

/// `fn j => I` in its CHECKED spelling: checking `I` rewrites the free
/// variable to the cubical interval, so every type the rule derives
/// over the varying family below carries this inner line, and the
/// pin's expected type must spell it the same way to unify.
def inner_line_checked : Term :=
    Term.lam (binder_named (Identifier.id "j")) Term.hole cub_interval

/// A genuinely varying line into a sort, in its SOURCE spelling so the
/// pin exercises the rewrites on the way through:
/// `fn i => PathP (fn j => I) i0 (ineg i)`. `A i0` is a path `i0 -> i1`
/// (De Morgan folds `ineg i0` to `i1`); `A i1` is a path `i0 -> i0`.
/// The endpoints differ, which is exactly what the direction pin needs.
def dependent_line : Term :=
    Term.lam (binder_named (Identifier.id "i")) Term.hole
        (Term.app (Term.app (Term.app (free_var "PathP") inner_line_checked)
            (cub_i0))
            (Term.app (free_var "ineg")
                (Term.var 0 (DebugName.named (Identifier.id "i")))))

/// The identity path `fn j => j`: an element of `A i0` -- a path whose
/// boundaries are the endpoints themselves -- and of no OTHER member of
/// the family.
def id_path : Term :=
    Term.lam (binder_named (Identifier.id "j")) Term.hole
        (Term.var 0 (DebugName.named (Identifier.id "j")))

/// Does `t` peel to a lambda? The varying family's element is a path
/// abstraction, and the pin must observe the rule checked it as one.
def is_a_lambda (t : Term) : Bool :=
    match t {
        Term.lam _dbg _dom _body => true,
        _ => false,
    }

#[test]
def test_transp_reads_both_endpoints_off_the_line : Bool :=
    // `transp A (fn j => j)` for the varying family checks against
    // `A i1`, spelled in its whnf'd shape `PathP (fn j => I) i0 i0`.
    // Both endpoint reads are pinned at once: the element lives at
    // `A i0` -- where `fn j => j` fits and no CONSTANT path does, so a
    // rule reading the element against `A i1` rejects it -- and the
    // result is `A i1`, not `A i0` -- a rule returning `A i0` fails
    // against this expected type, whose right endpoint is `i0` while
    // the identity path's is `i1`.
    checks_as_transp cubical_scope (transp_call dependent_line id_path)
        (cub_pathp inner_line_checked (cub_i0) (cub_i0)) is_a_lambda

// ─── Stage 3: the reducer ───────────────────────────────────────────────
//
// `whnf` observed directly: the constant-family rule is the only
// reduction, and its complement is the refusal -- a varying family and
// a stuck line must both stay the cubical application.

/// Is `t` the cubical `transp` primitive, still applied -- i.e. did
/// whnf decline to reduce the transport?
def stays_transp (t : Term) : Bool :=
    match t {
        Term.cubical c =>
            match c {
                { prim := p, args := _as } => cubical_prim_eq p CubicalPrim.transp,
            },
        _ => false,
    }

#[test]
def test_transp_in_a_constant_family_reduces_to_the_element : Bool :=
    // `transp (fn i => I) i0` in whnf is just `i0`: the line's body
    // does not mention its binder, both endpoint substitutions yield
    // the same body, and transporting in a constant family is the
    // identity.
    arg_is_bare_prim
        (whnf cubical_scope empty_locals (cub_transp const_line (cub_i0)))
        CubicalPrim.i0

/// The varying family in its whnf-facing spelling -- the pins here are
/// reducer probes, so the terms are hand-built rather than routed
/// through `type_check`: `fn i => PathP (fn j => I) i0 (ineg i)`, the
/// same family the direction pin checks through.
def varying_line : Term :=
    Term.lam (binder_named (Identifier.id "i")) Term.hole
        (cub_pathp inner_line_checked (cub_i0)
            (cub_ineg (Term.var 0 (DebugName.named (Identifier.id "i")))))

#[test]
def test_transp_in_a_varying_family_stays_stuck : Bool :=
    // `transp A i0` for the varying family stays the cubical
    // application: the two substituted bodies genuinely differ. The
    // STRUCTURAL reductions -- transporting in a pi or `PathP` family,
    // or across an inductive head -- are the recorded limit of Stage 3;
    // they wait for R5's recursors.
    stays_transp (whnf cubical_scope empty_locals (cub_transp varying_line (cub_i0)))

#[test]
def test_transp_with_a_stuck_line_stays_stuck : Bool :=
    // `transp I i0` where the line is a RIGID reference: `I` is
    // body-less (P1), delta cannot unfold it, and there is no lambda
    // body to substitute into. The reducer declines to guess -- a stuck
    // line is not treated as constant.
    stays_transp (whnf cubical_scope empty_locals (cub_transp (free_var "I") (cub_i0)))

// ─── Stage 4: the face lattice ──────────────────────────────────────────
//
// `face_eq0`/`face_eq1` -- the cofibration generators `i = 0` / `i = 1`
// -- and `is_one`, the truth predicate that makes a partial element an
// ordinary function `is_one φ -> A`. Cofibrations are INTERVAL terms:
// `∧`/`∨` reuse imeet/ijoin and `0`/`1` reuse i0/i1, so the only new
// TYPING is the three result rows (interval, interval, Sort 1) plus the
// Stage-1 dimension discipline on the argument. The reducer's face pass
// (`whnf_face`, whnf.mo) is where the stage's real content sits -- and
// three of its rules are pinned by their ABSENCE: CCHM POSTULATES
// `isOne1 = 0`, so `ijoin (face_eq0 u) (face_eq1 u) = i1` is not
// derivable, and neither are `ineg (face_eq0 u) = face_eq1 u` nor the
// decomposition of `face_eq0 (imeet u v)`. Folding any of the three
// would make the interval two-point by conversion; the stuck pins below
// fail if any is ever added. The whole-term decision procedure
// (`face_decide`, faces.mo) is pinned in its own module's tests.

/// The saturated source spine `face_eq0 u` / `face_eq1 u` / `is_one u`,
/// with the head in its source spelling so the pins exercise the
/// cubical probe on the way through, exactly as a real call site would.
def face_call (nm : String) (arg : Term) : Term :=
    Term.app (free_var nm) arg

/// The dimension the whnf pins constrain -- a free, rigid variable, so
/// no reduction of the dimension itself can blur which rule fired.
def dim_u : Term := free_var "u"

/// Is `t` the sort `Type 1`? `is_one` is a former of types and lands in
/// `Sort 1` -- the same `l = 1` instance discipline as `PathP`'s
/// declared signature.
def is_sort_one (t : Term) : Bool :=
    match t {
        Term.sort lv =>
            match lv {
                SortLevel.concrete n => I64.beq n 1,
                _ => false,
            },
        _ => false,
    }

/// Does checking `t` against `expected` in `s` succeed, produce the
/// cubical `p` applied to exactly one argument matching `arg_is`, and
/// answer a type matching `typ_is`? The result-type read is
/// load-bearing: `cubical_result_type`'s three new rows are the whole of
/// this stage's typing, and a pin that only reads the term cannot see a
/// wrong row.
def checks_as_prim_with (s : Scope) (t : Term) (p : CubicalPrim) (expected : Term)
    (arg_is : Term -> Bool) (typ_is : Term -> Bool) : Bool :=
    match type_check t expected s empty_local_types empty_locals {
        // Two-step match: `ok`'s single struct payload is its own `match`
        // (see `checks_as_bare_prim`'s comment) -- one destructure of `tt`,
        // not two field reads.
        ok tt =>
            match tt {
                { term := tm, typ := ty } =>
                    let shape_ok : Bool :=
                        match tm {
                            Term.cubical c =>
                                match c {
                                    { prim := q, args := as } =>
                                        cubical_prim_eq q p
                                            && match as {
                                                List.cons a rest =>
                                                    List.is_empty rest && arg_is a,
                                                List.empty => false,
                                            },
                                },
                            _ => false,
                        } in
                    shape_ok && typ_is ty,
            },
        err _ => false,
    }

/// Is `t` the cubical generator `gen` applied to exactly one argument
/// that is itself the bare primitive `bare`? For `is_one`'s argument:
/// the cofibration it is asked about is a generator's checked term.
def arg_is_face_gen_of_bare (gen : CubicalPrim) (t : Term) (bare : CubicalPrim) : Bool :=
    match t {
        Term.cubical c =>
            match c {
                { prim := q, args := as } =>
                    cubical_prim_eq q gen
                        && match as {
                            List.cons a rest =>
                                List.is_empty rest && arg_is_bare_prim a bare,
                            List.empty => false,
                        },
            },
        _ => false,
    }

/// Is `t` the cubical generator `p` applied to exactly one argument,
/// `Similar` to `u`? The argument-De Morgan pins observe WHICH
/// generator the negated arm builds, without pinning the dimension's
/// identity any tighter than the rules themselves compare it.
def is_face_gen_of (t : Term) (p : CubicalPrim) (u : Term) : Bool :=
    match t {
        Term.cubical c =>
            match c {
                { prim := q, args := as } =>
                    cubical_prim_eq q p
                        && match as {
                            List.cons a rest =>
                                List.is_empty rest && Similar.similar a u,
                            List.empty => false,
                        },
            },
        _ => false,
    }

/// Is `t` the cubical `p` head, still applied -- i.e. did whnf decline
/// to reduce it? The stuck shape for the three deliberate absences.
def stays_cubical_prim (t : Term) (p : CubicalPrim) : Bool :=
    match t {
        Term.cubical c =>
            match c {
                { prim := q, args := _as } => cubical_prim_eq q p,
            },
        _ => false,
    }

#[test]
def test_face_eq0_checks_and_rewrites : Bool :=
    // `face_eq0 i0` checks against the interval: the argument is a
    // dimension, the checked term is the cubical primitive applied to
    // the checked argument, and the result type is the interval row.
    checks_as_prim_with cubical_scope (face_call "face_eq0" (free_var "i0"))
        CubicalPrim.face_eq0 cub_interval
        (fn a => arg_is_bare_prim a CubicalPrim.i0)
        (fn ty => arg_is_bare_prim ty CubicalPrim.interval)

#[test]
def test_face_eq1_checks_and_rewrites : Bool :=
    // The dual generator, pinned on its own: `face_eq1 i1` is the
    // constraint `i = 1` at the endpoint where it holds.
    checks_as_prim_with cubical_scope (face_call "face_eq1" (free_var "i1"))
        CubicalPrim.face_eq1 cub_interval
        (fn a => arg_is_bare_prim a CubicalPrim.i1)
        (fn ty => arg_is_bare_prim ty CubicalPrim.interval)

#[test]
def test_is_one_checks_as_a_type_in_sort_one : Bool :=
    // `is_one (face_eq0 i0)` is a TYPE: the checked term is the
    // primitive applied to the checked cofibration, and the result is
    // `Type 1`. The result-type read is the pin on the is_one row -- a
    // mutation to the interval row fails here even though the term
    // shape is unchanged.
    checks_as_prim_with cubical_scope
        (face_call "is_one" (face_call "face_eq0" (free_var "i0")))
        CubicalPrim.is_one (sort_n 1)
        (fn a => arg_is_face_gen_of_bare CubicalPrim.face_eq0 a CubicalPrim.i0)
        is_sort_one

#[test]
def test_face_eq0_rejects_a_non_dimension_argument : Bool :=
    // `face_eq0 (Type 1)`: a sort is not a dimension. The argument
    // discipline is Stage 1's -- the same rule that rejects
    // `ineg (Type 1)`.
    check_fails_in cubical_scope (face_call "face_eq0" (sort_n 1))

#[test]
def test_is_one_rejects_a_non_dimension_argument : Bool :=
    // `is_one (Type 1)`: the argument is a dimension regardless of the
    // result being a type -- a cofibration is an interval term, and the
    // discipline does not loosen because the primitive changed sorts.
    check_fails_in cubical_scope (face_call "is_one" (sort_n 1))

#[test]
def test_whnf_folds_the_face_eq0_endpoint_laws : Bool :=
    // `face_eq0 i0 = i1` -- the constraint `i = 0` holds on all of the
    // cube at `i0` -- and `face_eq0 i1 = i0`.
    arg_is_bare_prim (whnf cubical_scope empty_locals (cub_face_eq0 cub_i0)) CubicalPrim.i1
        && arg_is_bare_prim (whnf cubical_scope empty_locals (cub_face_eq0 cub_i1)) CubicalPrim.i0

#[test]
def test_whnf_folds_the_face_eq1_endpoint_laws : Bool :=
    // The dual: `face_eq1 i1 = i1` and `face_eq1 i0 = i0` -- the
    // generator keeps its endpoints, it does not swap them.
    arg_is_bare_prim (whnf cubical_scope empty_locals (cub_face_eq1 cub_i1)) CubicalPrim.i1
        && arg_is_bare_prim (whnf cubical_scope empty_locals (cub_face_eq1 cub_i0)) CubicalPrim.i0

#[test]
def test_whnf_swaps_the_generator_under_a_negated_argument : Bool :=
    // `face_eq0 (ineg u) = face_eq1 u` and the dual: `ineg u = 0` IS
    // `u = 1`. This is the reason there are two generators and not
    // four -- and the only De Morgan law the face pass has.
    is_face_gen_of (whnf cubical_scope empty_locals (cub_face_eq0 (cub_ineg dim_u)))
        CubicalPrim.face_eq1 dim_u
        && is_face_gen_of (whnf cubical_scope empty_locals (cub_face_eq1 (cub_ineg dim_u)))
        CubicalPrim.face_eq0 dim_u

#[test]
def test_whnf_folds_a_face_contradiction_to_i0 : Bool :=
    // `face_eq0 u ∧ face_eq1 u = i0`: no cube point is both endpoints.
    arg_is_bare_prim
        (whnf cubical_scope empty_locals (cub_imeet (cub_face_eq0 dim_u) (cub_face_eq1 dim_u)))
        CubicalPrim.i0

#[test]
def test_whnf_folds_a_face_contradiction_in_either_order : Bool :=
    // The meet is commutative at the contradiction: the swapped spine
    // folds too, pinning the second branch of the order check.
    arg_is_bare_prim
        (whnf cubical_scope empty_locals (cub_imeet (cub_face_eq1 dim_u) (cub_face_eq0 dim_u)))
        CubicalPrim.i0

#[test]
def test_whnf_leaves_the_disjunction_of_opposite_faces_stuck : Bool :=
    // `ijoin (face_eq0 u) (face_eq1 u)` does NOT fold to `i1`: CCHM
    // POSTULATES `isOne1 = 0` because `u = 0 ∨ u = 1` is not derivable,
    // and a reducer that folded it would make the interval two-point by
    // conversion. This pin fails if the absent rule is ever added.
    stays_cubical_prim
        (whnf cubical_scope empty_locals (cub_ijoin (cub_face_eq0 dim_u) (cub_face_eq1 dim_u)))
        CubicalPrim.ijoin

#[test]
def test_whnf_leaves_the_negation_of_a_face_stuck : Bool :=
    // `ineg (face_eq0 u)` has no law: the endpoint lattice is De
    // Morgan's, and the generator lattice has no complement. Folding
    // it to `face_eq1 u` would give every cofibration a negated
    // cofibration -- not derivable, so the term stays stuck.
    stays_cubical_prim
        (whnf cubical_scope empty_locals (cub_ineg (cub_face_eq0 dim_u)))
        CubicalPrim.ineg

#[test]
def test_whnf_leaves_a_face_of_a_meet_stuck : Bool :=
    // `face_eq0 (imeet u v)` is not decomposed into a disjunction: the
    // mixed law `(u ∧ v) = 0 ⇒ u = 0 ∨ v = 0` is presheaf semantics,
    // not part of CCHM's cofibration quotient. Stuck -- and
    // `face_decide` answers none over it too.
    stays_cubical_prim
        (whnf cubical_scope empty_locals (cub_face_eq0 (cub_imeet dim_u (free_var "v"))))
        CubicalPrim.face_eq0

// ─── Stage 5: Kan composition ───────────────────────────────────────────
//
// `hcomp A φ u u0` is the first rule whose content is an ASYMMETRY, and
// getting the asymmetry wrong is unsound rather than merely incomplete.
// CCHM's boundary law is `hcomp A φ u u0 ≡ u i1` on `φ` -- the composite
// IS the system's top -- while `u0` is the system's BOTTOM (`u i0 = u0`
// on `φ`). So exactly one of the two decided cases reduces:
//
//   * `φ` REFUTED (`face_decide φ = some false`): the empty subobject,
//     where a system constrains nothing. `≡ u0`.
//   * `φ` SATISFIED: the honest answer is `u i1`, which needs a witness
//     of `is_one i1` that this syntax has no canonical term for. STUCK.
//
// The plan sketch asked for `≡ u0` on a decided `φ`; that is the unsound
// half, and the satisfied-face pin below is what fails if anyone lands
// it. The refuted-face pins are its complement.

/// The checked system `fn (i : I) => fn (h : is_one φ) => i0` -- a
/// well-typed system over `phi`, spelled the way the checker itself
/// builds one (a lambda chain, both binder types bound).
def system_over (phi : Term) : Term :=
    Term.lam (binder_named (Identifier.id "i")) cub_interval
        (Term.lam (binder_named (Identifier.id "h")) (cub_is_one phi) cub_i0)

/// Is `t` the checked system `fn (i : I) => fn (h : is_one φ) => base`?
/// The INNER BINDER TYPE is the pin: the rule must build `is_one` over
/// the cofibration it CHECKED, not over the source-spelled argument, and
/// a rule that reused the source term would agree here only by accident.
def is_system_over (t : Term) (phi : Term) (base : Term) : Bool :=
    match t {
        Term.lam _dbg_i dom_i body =>
            match body {
                Term.lam _dbg_h dom_h inner =>
                    Similar.similar dom_i cub_interval
                        && Similar.similar dom_h (cub_is_one phi)
                        && Similar.similar inner base,
                _ => false,
            },
        _ => false,
    }

/// Does checking `t` against `expected` in `s` succeed, produce the
/// cubical primitive `p` applied to exactly FOUR arguments satisfying
/// `args_ok`, and answer a type matching `typ_is`? The four-argument
/// twin of `checks_as_prim_with` above.
def checks_as_prim_with4 (s : Scope) (t : Term) (p : CubicalPrim) (expected : Term)
    (args_ok : Term -> Term -> Term -> Term -> Bool) (typ_is : Term -> Bool) : Bool :=
    match type_check t expected s empty_local_types empty_locals {
        // Two-step match: `ok`'s single struct payload is its own `match`
        // (see `checks_as_bare_prim`'s comment) -- one destructure of `tt`,
        // not two field reads.
        ok tt =>
            match tt {
                { term := tm, typ := ty } =>
                    let shape_ok : Bool :=
                        match tm {
                            Term.cubical c =>
                                match c {
                                    { prim := q, args := as } =>
                                        cubical_prim_eq q p
                                            && match as {
                                                List.cons a1 r1 =>
                                                    match r1 {
                                                        List.cons a2 r2 =>
                                                            match r2 {
                                                                List.cons a3 r3 =>
                                                                    match r3 {
                                                                        List.cons a4 r4 =>
                                                                            List.is_empty r4
                                                                                && args_ok a1 a2 a3 a4,
                                                                        List.empty => false,
                                                                    },
                                                                List.empty => false,
                                                            },
                                                        List.empty => false,
                                                    },
                                                List.empty => false,
                                            },
                                },
                            _ => false,
                        } in
                    shape_ok && typ_is ty,
            },
        err _ => false,
    }

/// `hcomp A φ sys base` in its SOURCE spelling with every position
/// supplied, so each rejection pin varies exactly one of the four against
/// a shape that otherwise checks.
def hcomp_call_with (a_typ : Term) (phi : Term) (sys : Term) (base : Term) : Term :=
    Term.app
        (Term.app (Term.app (Term.app (free_var "hcomp") a_typ) phi) sys)
        base

/// The good system in its SOURCE spelling: `fn (i : I) => fn (h : is_one
/// i0) => i0`. Both binder types are written as holes, so the checker
/// takes them from the expected Pi it is checked against -- which is the
/// path the acceptance pin exists to exercise.
def good_system : Term :=
    Term.lam (binder_named (Identifier.id "i")) Term.hole
        (Term.lam (binder_named (Identifier.id "h")) Term.hole (free_var "i0"))

/// `hcomp I φ (fn i => fn h => i0) i0` -- the acceptance and reducer
/// pins' shared spine, varying only the cofibration.
def hcomp_call_over (phi : Term) : Term :=
    hcomp_call_with (free_var "I") phi good_system (free_var "i0")

/// The system's inner body replaced by a SORT -- a shape no system can
/// have. Deliberately not a variable: the variable and free-variable arms
/// return their own type WITHOUT unifying against the expectation, so a
/// pin built from one would stay green against a rule that never built
/// the Pi at all.
def non_system : Term :=
    Term.lam (binder_named (Identifier.id "i")) Term.hole
        (Term.lam (binder_named (Identifier.id "h")) Term.hole (sort_n 1))

/// The four checked arguments of `hcomp_call_over (free_var "i0")`: the
/// interval, the empty face, the checked system over it, and the base.
def hcomp_args_ok (a_typ : Term) (a_face : Term) (a_sys : Term) (a_base : Term) : Bool :=
    arg_is_bare_prim a_typ CubicalPrim.interval
        && arg_is_bare_prim a_face CubicalPrim.i0
        && is_system_over a_sys cub_i0 cub_i0
        && arg_is_bare_prim a_base CubicalPrim.i0

#[test]
def test_hcomp_formation_checks_and_rewrites : Bool :=
    // `hcomp I i0 (fn i => fn h => i0) i0` checks against `I`: the first
    // argument is a type, the face a dimension, the system the Pi rebuilt
    // from the CHECKED face and type, and the base an element of that
    // type. The result type is read too -- `A` is an ARGUMENT here, so a
    // rule that took its result from the expected type would still have
    // to answer `I` and cannot be told apart by shape alone.
    checks_as_prim_with4 cubical_scope (hcomp_call_over (free_var "i0"))
        CubicalPrim.hcomp cub_interval hcomp_args_ok
        (fn ty => arg_is_bare_prim ty CubicalPrim.interval)

#[test]
def test_hcomp_rejects_a_face_that_is_not_a_cofibration : Bool :=
    // Cofibrations are INTERVAL terms (Stage 4): `Type 1` is not one.
    check_fails_in cubical_scope (hcomp_call_over (sort_n 1))

#[test]
def test_hcomp_rejects_a_base_of_the_wrong_type : Bool :=
    // The base is checked against `A`, not against the expected type:
    // `Type 1` is not an `I`.
    check_fails_in cubical_scope
        (hcomp_call_with (free_var "I") (free_var "i0") good_system (sort_n 1))

#[test]
def test_hcomp_rejects_a_system_that_is_not_over_the_cofibration : Bool :=
    // The system is checked against the Pi `I -> is_one φ -> A` rebuilt
    // from the two checked arguments. A rule that checked it against
    // `Term.hole` instead would take the inferring lambda arm and accept
    // this.
    check_fails_in cubical_scope
        (hcomp_call_with (free_var "I") (free_var "i0") non_system (free_var "i0"))

#[test]
def test_hcomp_rejects_a_type_that_is_not_a_type : Bool :=
    // `A` is inferred and then guarded by `sort_level_of`: a dimension is
    // a term, not a type, and this is the pin on that guard.
    //
    // The base is `Term.hole` so the guard is the ONLY thing rejecting
    // this: with the guard dropped the call would sail through -- `i0`'s
    // own type `I` unifies with a hole, and the result `i0` unifies with
    // the hole expectation. (With `free_var "i0"` as the base instead the
    // pin stayed GREEN under the mutation, because `unify I i0` rejected
    // the base before the guard ever mattered -- a pin that names the
    // guard while testing something else.)
    check_fails_in cubical_scope
        (hcomp_call_with (free_var "i0") (free_var "i0") good_system Term.hole)

#[test]
def test_hcomp_rejects_a_base_that_is_a_type_not_an_element : Bool :=
    // The base's own inferred type must UNIFY with `A`. `I` is a TYPE, so
    // checked against `A = I` it comes back typed `Type` -- and the
    // free-variable arm returns a type without comparing it to the
    // expectation, so only the rule's own unify rejects this. Drop that
    // unify and this pin goes red while every other hcomp pin stays green.
    check_fails_in cubical_scope
        (hcomp_call_with (free_var "I") (free_var "i0") good_system (free_var "I"))

#[test]
def test_hcomp_result_type_is_unified_with_the_expected_type : Bool :=
    // `hcomp`'s result is `A`, and it is unified with the expected type
    // exactly as `check_cubical_args_then` unifies every other
    // primitive's. Checking against `Type` is a mismatch that a rule
    // simply returning `A` would accept.
    check_fails_against cubical_scope (hcomp_call_over (free_var "i0")) (sort_n 1)

/// `hcomp I φ (fn i => fn h => i0) i0` as a WHNF probe: hand-built and
/// already checked-shaped, because `whnf` is what is under test.
///
/// `phi` is read twice (the composite's own face and the system built
/// over it), so it is borrowed: `Borrow Term` is Copy, `Term` is not.
def hcomp_in (phi : Term) : Term :=
    let b : Borrow Term := Borrow.of phi in
    cub_hcomp cub_interval (Borrow.get b) (system_over (Borrow.get b)) cub_i0

#[test]
def test_whnf_reduces_hcomp_over_a_refuted_face_to_the_base : Bool :=
    // `hcomp A i0 u u0 ≡ u0`: the empty subobject constrains nothing, and
    // the composite of a box with no sides is its base. The acceptance
    // half of the rule.
    arg_is_bare_prim (whnf cubical_scope empty_locals (hcomp_in cub_i0)) CubicalPrim.i0

#[test]
def test_whnf_leaves_hcomp_over_a_satisfied_face_stuck : Bool :=
    // THE SOUNDNESS PIN. `hcomp A i1 u u0` is `u i1` -- the system's top,
    // not its base, which is `u i0`. Reducing to `u0` here is what the
    // plan's sketch of this rule asked for and is wrong; the rule is
    // deliberately absent, so the term stays stuck. This pin goes red the
    // moment anyone adds `some true => a_base` to `whnf_hcomp`.
    stays_cubical_prim (whnf cubical_scope empty_locals (hcomp_in cub_i1)) CubicalPrim.hcomp

#[test]
def test_whnf_leaves_hcomp_over_an_undecided_face_stuck : Bool :=
    // A bare dimension is no cofibration and `face_decide` answers none
    // over it (`faces.mo`): no rule applies, so the term stays stuck.
    stays_cubical_prim
        (whnf cubical_scope empty_locals (hcomp_in dim_u)) CubicalPrim.hcomp

#[test]
def test_whnf_leaves_hcomp_over_a_disjunction_of_opposite_faces_stuck : Bool :=
    // `hcomp A (u = 0 ∨ u = 1) u u0` stays stuck: `face_decide` never
    // answers `some true` -- `isOne1 = 0` is POSTULATED in CCHM, not
    // derivable -- so neither branch can fire. The dual of the soundness
    // pin, on the decider's other blind spot.
    stays_cubical_prim
        (whnf cubical_scope empty_locals
            (hcomp_in (cub_ijoin (cub_face_eq0 dim_u) (cub_face_eq1 dim_u))))
        CubicalPrim.hcomp

/// A cofibration that is refuted but NOT at the head: `u = 0 ∧ (u = 1 ∧
/// v = 1)`. `whnf`'s face pass folds only a meet whose two arguments are
/// the two generators of ONE dimension, so this one stays stuck -- which
/// is exactly what makes it the witness that `whnf_hcomp` reads the
/// whole-term `face_decide` rather than the head.
def buried_contradiction : Term :=
    cub_imeet (cub_face_eq0 dim_u)
        (cub_imeet (cub_face_eq1 dim_u) (cub_face_eq1 (free_var "v")))

#[test]
def test_whnf_leaves_a_buried_face_contradiction_stuck : Bool :=
    // The premise of the pin below, pinned on its own: no rule of the
    // face pass fires on this cofibration, so it reaches `whnf_hcomp`
    // still an `imeet`. (That `face_decide` sees the contradiction is
    // pinned separately, in the decider's own module's tests.)
    stays_cubical_prim (whnf cubical_scope empty_locals buried_contradiction) CubicalPrim.imeet

#[test]
def test_whnf_reads_the_whole_term_decider_for_the_face : Bool :=
    // `hcomp A (u = 0 ∧ u = 1 ∧ v = 1) u u0 ≡ u0`: refuted, so the base --
    // even though the face pass above could not see it. This is the pin
    // on `face_decide` being LOAD-BEARING in the rule: swapping it for
    // the shallow literal reader (`face_literal_truth`) leaves the `i0`
    // pin above green and turns this one red.
    arg_is_bare_prim
        (whnf cubical_scope empty_locals (hcomp_in buried_contradiction)) CubicalPrim.i0

/// A `hcomp` spine with a FIFTH argument -- a shape `cubical_arity` never
/// lets through formation, but which `whnf` can still be handed.
def over_applied_hcomp : Term :=
    cub CubicalPrim.hcomp [cub_interval, cub_i0, system_over cub_i0, cub_i0, cub_i0]

#[test]
def test_whnf_leaves_an_over_applied_hcomp_stuck : Bool :=
    // The reducer re-checks the argument count rather than trusting the
    // formation-time arity table. Without that check this five-argument
    // spine would have reduced to `i0` on its refuted face.
    stays_cubical_prim
        (whnf cubical_scope empty_locals over_applied_hcomp) CubicalPrim.hcomp