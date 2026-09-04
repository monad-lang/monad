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
use lang.types {LocalScope}
use lang.module {elaborate_loaded_modules, typecheck_module_with_scope}

pub def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// Type check a file with its full dependency scope (ambient prelude/init
/// included), reporting a load failure as a test failure rather than a
/// crash.
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
