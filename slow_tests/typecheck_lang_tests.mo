use io {IO}
use lang.types {
  Decl, Def, Identifier, InductConstructor, Inductive, LocalScope, ModulePath,
  Scope, ScopeData, Term, def_d, hole, id, inductive_d, mk, mp,
}
use lang.module {
  elaborate_loaded_modules, mk, typecheck_module_with_scope,
}
use lang.parser.core {mk}
use lang.typecheck.infer {empty_local_types, empty_locals, mk, type_check}

open IO {println}

def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

def make_scope (path : ModulePath) (sd : ScopeData) : Scope := {
    module_id := path,
    scope := sd,
    parent := Option.none,
}

def is_hole (t : Term) : Bool := 
    match t {
        Term.hole => true,
        _ => false
    }

def typecheck_module (path : ModulePath) (scope : Scope) (decls : List Decl) : Bool := 
    match decls {
        List.empty => true,
        List.cons d rest =>
            let result : Bool := typecheck_decl d path scope in
            if result then
                typecheck_module path scope rest
            else
                false
    }

def typecheck_decl (d : Decl) (path : ModulePath) (scope : Scope) : Bool := 
    match d {
        Decl.def_d df => typecheck_def df scope,
        Decl.inductive_d ind => typecheck_inductive ind scope,
        _ => true  // Skip use, open, infix, class, instance for now
    }

def typecheck_def (df : Def) (scope : Scope) : Bool := 
    match df {
        mk _name typ body _constraints _attrs =>
            // Skip native/abstract definitions (body is Term.hole)
            if is_hole body then
                true
            else
                match type_check body Term.hole scope empty_local_types empty_locals {
                    ok _ => true,
                    err _ => false,
                }
    }

def typecheck_inductive (ind : Inductive) (scope : Scope) : Bool := 
    match ind {
        mk _name _params _typ constructors _attrs =>
            typecheck_constructors constructors scope
    }

def typecheck_constructors (cons : List InductConstructor) (scope : Scope) : Bool := 
    match cons {
        List.empty => true,
        List.cons c rest =>
            let result : Bool := typecheck_constructor c scope in
            if result then
                typecheck_constructors rest scope
            else
                false
    }

def typecheck_constructor (c : InductConstructor) (scope : Scope) : Bool := 
    match c {
        mk _name params typ =>
            match type_check typ Term.hole scope empty_local_types empty_locals {
                ok _ => true,
                err _ => false
            }
    }

/// Type check a file by loading it with all dependencies and type checking
/// the result — routes through `elaborate_loaded_modules`, the one
/// canonical front-end pipeline `check`/`compile`/`test`/`slow_tests` all
/// now share (see `bootstrapping/unify-check-compile-test-elaboration.md`).
///
/// Passes `check_deps=false` for now, same as
/// `slow_tests/typecheck_init_tests.mo`'s `typecheck_file` (see its own
/// doc comment for the general rationale). `check_deps=true` is the
/// eventual goal specifically for THIS test, though — it's the natural
/// place for a genuine full-closure safety-net check to live — but isn't
/// safe to turn on yet: see `elaborate_loaded_modules`'s own doc comment
/// (`lang/module.mo`) for what `check_deps=true` does, and
/// `bootstrapping/check-deps-memory-blowup.md` for why it's still off
/// everywhere.
def typecheck_file (file_path : String) : IO Bool := do {
    let result <- elaborate_loaded_modules file_path false;
    match result {
        Result.ok em => typecheck_module_with_scope em.scope em.target_decls empty_local_scope,
        Result.err e => do {
            println ("error loading " ++ file_path ++ ": " ++ e);
            return false
        },
    }
}

// --- lang/ non-test files ---


#[test]
def test_typecheck_lang_main : IO Bool := typecheck_file "lang/main.mo"

/// Self-hosted counterpart to `lang/tests/cli_derive_tests.mo` -- bare
/// `derive_cli!` (not `#[derive_cli]` attribute sugar), proving
/// `reflect_type_info!`'s self-hosted evaluation
/// (`lang/typecheck/meta_eval.mo`) works for `lang/cli.mo`'s own
/// meta-def too, not just `std/derive.mo`'s four derives (see
/// `known_broken_typecheck_std_derive_tests`, `typecheck_std_tests.mo`).
#[test]
def test_typecheck_lang_cli_derive_self_hosted : IO Bool := typecheck_file "lang/tests/cli_derive_self_hosted_tests.mo"

