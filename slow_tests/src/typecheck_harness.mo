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
use io {IO}
open IO {println}
use lang::types {LocalScope}
use lang::module {ElaboratedModules, elaborate_loaded_modules, typecheck_module_with_scope}

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
    // Annotated the same way cli/src/main.mo annotates its own
    // `elaborate_loaded_modules` bind: the checker needs the bind's
    // type stated to type the match below.
    let result : Result String ElaboratedModules <- elaborate_loaded_modules file_path false false;
    match result {
        Result.ok em => typecheck_module_with_scope em.scope em.target_decls empty_local_scope,
        Result.err e => do {
            println ("error loading " ++ file_path ++ ": " ++ e);
            return false
        },
    }
}
