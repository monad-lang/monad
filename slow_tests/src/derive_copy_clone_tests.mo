/// Negative cases for `#[derive Copy]` / `#[derive Clone]`, through the REAL
/// load + expand + check path (the same `Test.write_fixture` harness
/// `view_type_tests.mo` uses).
///
/// The interesting rejections are not in `std/derive_tests.mo` because a
/// fixture that must FAIL to compile cannot live in the swept test file.
///
/// One case is deliberately NOT tested here: a monomorphic type whose field
/// has no `Copy`/`Clone` instance. The checker still fails open on the
/// generated `Copy.dup`/`Clone.clone_field` call (the generated instance's
/// match binders have no written type, the same attribution gap
/// `quantitative-types.md` Known Gap #2 records), so the rejection shows up at
/// CODEGEN as `no instance found`, not as a check diagnostic. `derive.mo`'s
/// `Copy.dup`/`Clone.clone_field` comments and the plan record that limit; a
/// codegen-level test is the right place to pin it once the checker attributes
/// match binders.
use lib::typecheck_harness {check_source_diags, diags_contain}

/// The acceptance twin: a monomorphic struct with `I64` fields derives both
/// instances with no diagnostic at all.
#[test]
def test_a_valid_copy_clone_derive_is_clean : IO Bool := do {
    let src : String :=
        "use std::derive {derive_clone, derive_copy}\n"
        ++ "#[derive Copy Clone]\n"
        ++ "struct P { n : I64 }\n"
        ++ "def twice (p : P) : P := p\n";
    let diags <- check_source_diags src "valid";
    return (List.is_empty diags)
}

/// A `#[linear]` type must never get a `Copy`/`Clone` instance: the
/// instance-kind rule (`view_rules.mo`) is an unconditional error.
#[test]
def test_derive_copy_on_a_linear_type_is_rejected : IO Bool := do {
    let src : String :=
        "use std::derive {derive_copy}\n"
        ++ "#[linear]\n"
        ++ "#[derive Copy]\n"
        ++ "type L { l1 (n : I64) }\n";
    let diags <- check_source_diags src "linear";
    return (diags_contain "is not allowed for the linear or proof type" diags)
}

/// An `#[opaque]` type cannot be rebuilt: its only constructor is the
/// unreferenceable witness, so the generated `copy`/`clone` body is rejected.
#[test]
def test_derive_copy_on_an_opaque_type_is_rejected : IO Bool := do {
    let src : String :=
        "use std::derive {derive_copy}\n"
        ++ "#[opaque]\n"
        ++ "#[derive Copy]\n"
        ++ "type H { h_witness }\n";
    let diags <- check_source_diags src "opaque";
    return (diags_contain "witness constructor" diags)
}

/// A generic type cannot be derived: `TypeInfo.params` is non-empty, and the
/// generated instance cannot carry the `[Copy A]` constraint it would need
/// (and `copy_class.mo` refuses a constrained parametric `Copy` instance
/// anyway). The error comes from the meta function's `d_error`.
#[test]
def test_derive_copy_on_a_generic_type_is_rejected : IO Bool := do {
    let src : String :=
        "use std::derive {derive_copy}\n"
        ++ "#[derive Copy]\n"
        ++ "type B A { box (value : A) }\n";
    let diags <- check_source_diags src "generic_copy";
    return (diags_contain "cannot derive Copy for a generic type" diags)
}

#[test]
def test_derive_clone_on_a_generic_type_is_rejected : IO Bool := do {
    let src : String :=
        "use std::derive {derive_clone}\n"
        ++ "#[derive Clone]\n"
        ++ "type B A { box (value : A) }\n";
    let diags <- check_source_diags src "generic_clone";
    return (diags_contain "cannot derive Clone for a generic type" diags)
}
