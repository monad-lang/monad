use io
use lang.types
use lang.module
use lang.parser
use lang.parser.core
use lang.scope
use lang.typecheck.infer

open IO
open types
open module
open parser
open parser.core
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

def typecheck_file (file_path : String) (mod_name : String) : Bool := 
    match IO.read_file file_path {
        IO.io content => 
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

// --- std/ non-test files ---

@[test]
def test_typecheck_std_test : Bool := typecheck_file "std/test.mo" "test"

@[test]
def test_typecheck_std_base : Bool := typecheck_file "std/base.mo" "base"

@[test]
def test_typecheck_std_bench : Bool := typecheck_file "std/bench.mo" "bench"

@[test]
def test_typecheck_std_list : Bool := typecheck_file "std/list.mo" "list"

@[test]
def test_typecheck_std_map : Bool := typecheck_file "std/map.mo" "map"

// --- std/concurrent/ files ---

@[test]
def test_typecheck_std_concurrent_fiber : Bool := typecheck_file "std/concurrent/fiber.mo" "concurrent_fiber"

@[test]
def test_typecheck_std_concurrent_combine : Bool := typecheck_file "std/concurrent/combine.mo" "concurrent_combine"

// Note: Test files (list_tests*, map_tests*, etc.) require module loading
// and are skipped for now.
