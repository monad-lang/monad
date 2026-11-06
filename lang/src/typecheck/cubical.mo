// Stage 2 (`plans/type-system/univalence.md`): the pure PATH-side halves of
// the `PathP` rules -- peeling a path type into its parts, recognizing the
// bare interval, recognizing an endpoint. Deliberately free of checker
// state: everything here is a `Term` -> `Term`/`Option` question, so this
// module imports only `lang/types.mo` and the formation/boundary rules
// that need the checker's scope and local types live in
// `lang/typecheck/infer.mo` next to the arms that call them (they need
// `nth_type`, which is infer's own local-type lookup, and importing infer
// from here would be a cycle).

use lib::types {
    CubicalPrim, Term,
    cubical_is_endpoint, cubical_prim_eq, term_peel,
}

/// The three components of a saturated `PathP`: the LINE of types the
/// path lives over, and the LEFT/RIGHT endpoint values.
pub struct PathParts {
    line : Term,
    left : Term,
    right : Term,
}

/// Peel `t` into `PathParts` if it is a SATURATED `PathP` type -- the
/// shape `type_check_cubical` rebuilds and the path-abstraction and
/// path-application rules match on. A `pathp` primitive with the wrong
/// argument count answers `none`: the arity table rejects it at formation
/// and no later rule should have an opinion about a malformed one.
pub def path_parts_of (t : Term) : Option PathParts := match term_peel t {
    Term.cubical c =>
        match c {
            { prim := p, args := as } =>
                match cubical_prim_eq p CubicalPrim.pathp {
                    // Nested constructor patterns do not parse; the three
                    // args are peeled one level at a time.
                    true =>
                        match as {
                            List.cons ln rest =>
                                match rest {
                                    List.cons lft rest2 =>
                                        match rest2 {
                                            List.cons rgt rest3 =>
                                                match rest3 {
                                                    List.empty =>
                                                        let parts : PathParts :=
                                                            { line := ln, left := lft, right := rgt } in
                                                        Option.some parts,
                                                    _ => Option.none,
                                                },
                                            _ => Option.none,
                                        },
                                    _ => Option.none,
                                },
                            _ => Option.none,
                        },
                    false => Option.none,
                },
        },
    _ => Option.none,
}

/// Is `t` the BARE interval -- `I` itself, not a dimension expression?
/// The line-domain and path-binder rules ask this of a CHECKED term (the
/// checked term is what carries the `cubical` rewrite a raw source
/// spelling does not), which is why this takes a `Term` rather than a
/// `CubicalPrim`.
pub def peels_to_bare_interval (t : Term) : Bool := match term_peel t {
    Term.cubical c =>
        match c {
            { prim := p, args := as } =>
                cubical_prim_eq p CubicalPrim.interval && List.is_empty as,
        },
    _ => false,
}

/// Which ENDPOINT a checked term is, if it is one: bare `i0` or bare `i1`.
/// The path-application rule's mitigation keys on this (see
/// `extract_pi_ret` in `lang/typecheck/infer.mo`); a dimension EXPRESSION
/// -- `ineg i`, `imeet i j` -- answers `none` even though it evaluates to an
/// endpoint at the boundary, because at the application site it has not
/// been substituted yet. The caller that has substituted normalizes
/// first.
pub def endpoint_of (t : Term) : Option CubicalPrim := match term_peel t {
    Term.cubical c =>
        match c {
            { prim := p, args := as } =>
                match cubical_is_endpoint p {
                    true =>
                        match List.is_empty as {
                            true => Option.some p,
                            false => Option.none,
                        },
                    false => Option.none,
                },
        },
    _ => Option.none,
}
