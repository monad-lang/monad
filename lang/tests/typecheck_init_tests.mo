use io
use lang.types
use lang.module
use lang.parser
use lang.scope
use lang.typecheck.infer

open IO
open types
open module
open parser
open scope
open infer

def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

def make_scope (path : ModulePath) (sd : ScopeData) : Scope := {
    module_id := path,
    scope := sd,
    parent := Option.none,
}

/// Try to type check all definitions in a module
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

/// Type check a single declaration
def typecheck_decl (d : Decl) (path : ModulePath) (scope : Scope) : Bool :=
    match d {
        Decl.def_d df => typecheck_def df scope,
        Decl.inductive_d ind => typecheck_inductive ind scope,
        _ => true  // Skip use, open, infix, class, instance for now
    }

/// Type check an inductive type
def typecheck_inductive (ind : Inductive) (scope : Scope) : Bool :=
    match ind {
        mk _name _params _typ constructors _attrs =>
            // For now, just check that all constructors are valid
            typecheck_constructors constructors scope
    }

/// Type check all constructors in a list
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

/// Type check a single constructor
def typecheck_constructor (c : InductConstructor) (scope : Scope) : Bool :=
    match c {
        mk _name params typ =>
            // Check the constructor type
            match type_check typ Term.hole scope empty_local_types empty_locals {
                ok _ => true,
                err _ => false
            }
    }

/// Check if a term is a hole (used for native/abstract definitions)
def is_hole (t : Term) : Bool :=
    match t {
        Term.hole => true,
        _ => false
    }

/// Type check a definition
def typecheck_def (df : Def) (scope : Scope) : Bool :=
    match df {
        mk _name typ body _constraints _attrs =>
            // Skip native/abstract definitions (body is Term.hole)
            if is_hole body then
                true
            else
                match type_check body Term.hole scope empty_local_types empty_locals {
                    ok _ => true,
                    err e => 
                        // For now, just return false on error
                        // In the future, we could print the error for debugging
                        false,
                }
    }

/// Build scope and try to type check a file
def typecheck_file (file_path : String) (mod_name : String) : Bool := 
    match IO.read_file file_path {
        io content => 
            match parse_all_decls content {
                success _ decls => 
                    let path := ModulePath.mp (List.cons (Identifier.id mod_name) List.empty) in
                    let sd := build_scope_from_decls path decls in
                    let scope := make_scope path sd in
                    typecheck_module path scope decls,
                fail _ => false
            },
        _ => false
    }

// --- Simple init/ files ---

@[test]
def test_typecheck_init_id : Bool := typecheck_file "init/id.mo" "id"

@[test]
def test_typecheck_init_io : Bool := typecheck_file "init/io.mo" "io"

@[test]
def test_typecheck_init_math : Bool := typecheck_file "init/math.mo" "math"

@[test]
def test_typecheck_init_number : Bool := typecheck_file "init/number.mo" "number"

// --- More complex init/ files ---

@[test]
def test_typecheck_init_string : Bool := typecheck_file "init/string.mo" "string"

// Skip process.mo for now - it has native functions with dependencies
// @[test]
// def test_typecheck_init_process : Bool := typecheck_file "init/process.mo" "process"

@[test]
def test_typecheck_init_init : Bool := typecheck_file "init/init.mo" "init"

@[test]
def test_typecheck_init_parser : Bool := typecheck_file "init/parser.mo" "parser"

// --- Most complex init/ file ---

@[test]
def test_typecheck_init_prelude : Bool := typecheck_file "init/prelude.mo" "prelude"

// --- Test files with type definitions ---

@[test]
def test_typecheck_init_foldable : Bool := typecheck_file "init/foldable.mo" "foldable"

@[test]
def test_typecheck_init_optics : Bool := typecheck_file "init/optics.mo" "optics"

@[test]
def test_typecheck_init_test_constraints : Bool := typecheck_file "init/test_constraints.mo" "test_constraints"

// --- Remaining non-test init/ files ---

@[test]
def test_typecheck_init_string_profile : Bool := typecheck_file "init/string_profile.mo" "string_profile"

// Note: test files (foldable_tests*, optics_tests, tests.mo) require module loading
// and are skipped for now. They can be added once module dependency resolution is implemented.

// @[test]
// def test_typecheck_init_foldable_tests : Bool := typecheck_file "init/foldable_tests.mo" "foldable_tests"
// 
// @[test]
// def test_typecheck_init_foldable_tests_fold : Bool := typecheck_file "init/foldable_tests_fold.mo" "foldable_tests_fold"
// 
// @[test]
// def test_typecheck_init_foldable_tests_semi_monoid : Bool := typecheck_file "init/foldable_tests_semi_monoid.mo" "foldable_tests_semi_monoid"
// 
// @[test]
// def test_typecheck_init_optics_tests : Bool := typecheck_file "init/optics_tests.mo" "optics_tests"
// 
// @[test]
// def test_typecheck_init_tests : Bool := typecheck_file "init/tests.mo" "tests"
