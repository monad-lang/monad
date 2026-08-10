use io {io, read_file}
use lang.types {
  Decl, Def, InductConstructor, Inductive, LocalScope, ModulePath, Scope,
  ScopeData, Term, def_d, hole, id, inductive_d, mk, mp,
}
use lang.module {mk, parse_all_decls}
use lang.parser.core {fail, mk, success}
use lang.scope {build_scope_from_decls}
use lang.typecheck.infer {empty_local_types, empty_locals, mk, type_check}

open IO {io, read_file}

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

// --- examples/ non-test files ---

#[test]
def test_typecheck_examples_do_block : Bool := typecheck_file "examples/do_block.mo" "do_block"

// These examples depend on external modules (io, init, math, etc.) and require module loading
// #[test]
// def test_typecheck_examples_factorial : Bool := typecheck_file "examples/factorial.mo" "factorial"
// 
// #[test]
// def test_typecheck_examples_hello : Bool := typecheck_file "examples/hello.mo" "hello"

#[test]
def test_typecheck_examples_indexed_monads : Bool := typecheck_file "examples/indexed_monads.mo" "indexed_monads"

// #[test]
// def test_typecheck_examples_iteration : Bool := typecheck_file "examples/iteration.mo" "iteration"
// 
// #[test]
// def test_typecheck_examples_iteration_advanced : Bool := typecheck_file "examples/iteration_advanced.mo" "iteration_advanced"

#[test]
def test_typecheck_examples_optics : Bool := typecheck_file "examples/optics.mo" "optics"

// #[test]
// def test_typecheck_examples_pattern_matching : Bool := typecheck_file "examples/pattern_matching.mo" "pattern_matching"

#[test]
def test_typecheck_examples_structs : Bool := typecheck_file "examples/structs.mo" "structs"

// TODO this can not be tested without full mote support
// #[test]
// def test_typecheck_examples_test_mote : Bool := typecheck_file "examples/test_mote.mo" "test_mote"

// Note: Some examples require module loading (io, init, math, etc.) and are skipped for now.
