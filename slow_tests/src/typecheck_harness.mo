/// Shared helpers for the corpus type-check suites
/// (`typecheck_init_tests.mo`, `typecheck_std_tests.mo`,
/// `typecheck_lang_tests.mo`), which each carried their own copy.
///
/// `typecheck_file` was three byte-identical bodies modulo a `mod_name`
/// parameter that two of them declared and none of them USED -- 33 call
/// sites passed a string that was immediately discarded. The shared
/// version drops it.
///
/// `empty_local_scope` had six copies across `slow_tests/` and
/// `lang/tests/`, in two spellings of the same value.
open IO {println}
use lang::types {LocalScope}
use lang::module {
    ElaboratedModules, check_module_with_scope, check_module_with_scope_affine,
    elaborate_loaded_modules, typecheck_module_with_scope,
}
use std::test {Test.write_fixture}

pub def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// Type check a file with its full dependency scope (ambient prelude/init
/// included), reporting a load failure as a test failure rather than a
/// crash.
///
/// `check_deps` is `false` deliberately, and must not be flipped. It was
/// measured both ways on 2026-09-23: with `true` this file's callers go
/// from 18/18 to 11/18 on `typecheck_init_tests.mo` (188 spurious
/// `No recursive parameters found for '__Dict_...'` diagnostics), because
/// `check_module_with_scope` runs `check_termination_all` over whatever
/// decl list it is handed and that pass works on ONE module's own
/// declarations; and on `cli/src/main.mo`'s ~2200-decl closure it does not
/// finish at all (flat 152.4MB RSS at ~100% CPU for 5+ min against a
/// 23.28s baseline). Nothing is lost by leaving it `false`: the sweep's
/// check phase body-checks every `.mo` file in the corpus as its own
/// target, so dependencies are covered there. Measurements:
/// `plans/bootstrapping/check-deps-memory-blowup.md`.
#[partial]
pub def typecheck_file (file_path : String) : IO Bool := do {
    let result <- elaborate_loaded_modules file_path false false;
    match result {
        Result.ok em => typecheck_module_with_scope em.scope em.target_decls empty_local_scope,
        Result.err e => do {
            println ("error loading " ++ file_path ++ ": " ++ e);
            return false
        },
    }
}

/// Whether any rendered diagnostic contains `needle`. The negative suites
/// (`view_type_tests`, `derive_copy_clone_tests`, `typecheck_constraint_tests`)
/// shared three byte-identical copies of this and the helper below.
#[partial]
pub def diags_contain (needle : String) (diags : List String) : Bool :=
    match diags {
        List.empty => false,
        List.cons d rest => if String.contains d needle then true else diags_contain needle rest,
    }

/// Write `source` to a scratch fixture and return every diagnostic the real
/// load + elaborate + check path reports for it. `affine` selects
/// `check_module_with_scope_affine` (forces error mode and returns errors AND
/// warnings — the copy/borrow rules) instead of the ordinary
/// `check_module_with_scope`. The fixture name must be unique across suites;
/// the path is `/tmp/monad_typecheck_<name>.mo`.
#[partial]
pub def check_source_diags_with (affine : Bool) (source : String) (fixture_name : String) : IO (List String) := do {
    let path : String := String.concat "/tmp/monad_typecheck_" (String.concat fixture_name ".mo");
    let _written <- Test.write_fixture (Path.path path) source;
    let loaded <- elaborate_loaded_modules path false false;
    match loaded {
        Result.err e => do {
            return (List.cons (String.concat "LOAD FAILED: " e) List.empty)
        },
        // Destructured, not projected twice: two `em.field` reads of an
        // affine record would be an over-use.
        Result.ok em => match em {
            { scope, target_decls, .. } =>
                if affine
                then check_module_with_scope_affine scope target_decls empty_local_scope (Option.some path) false
                else check_module_with_scope scope target_decls empty_local_scope (Option.some path) false,
        },
    }
}

/// The affine/kind-check variant: error mode, errors AND warnings.
pub def check_source_diags (source : String) (fixture_name : String) : IO (List String) :=
    check_source_diags_with true source fixture_name

/// The ordinary type-check variant (constraint tests).
pub def check_source_diags_plain (source : String) (fixture_name : String) : IO (List String) :=
    check_source_diags_with false source fixture_name
