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

// --- lang/ non-test files ---

// These files form the self-hosted compiler and may have interdependencies.
// We test them individually to see which can type check in isolation.

@[test]
def test_typecheck_lang_types : Bool := typecheck_file "lang/types.mo" "types"

@[test]
def test_typecheck_lang_elaborate : Bool := typecheck_file "lang/elaborate.mo" "elaborate"

@[test]
def test_typecheck_lang_eval : Bool := typecheck_file "lang/eval.mo" "eval"

@[test]
def test_typecheck_lang_eval_t2 : Bool := typecheck_file "lang/eval_t2.mo" "eval_t2"

@[test]
def test_typecheck_lang_eval_term : Bool := typecheck_file "lang/eval_term.mo" "eval_term"

@[test]
def test_typecheck_lang_lower : Bool := typecheck_file "lang/lower.mo" "lower"

@[test]
def test_typecheck_lang_main : Bool := typecheck_file "lang/main.mo" "main"

@[test]
def test_typecheck_lang_module : Bool := typecheck_file "lang/module.mo" "module"

@[test]
def test_typecheck_lang_parser : Bool := typecheck_file "lang/parser.mo" "parser"

@[test]
def test_typecheck_lang_pretty : Bool := typecheck_file "lang/pretty.mo" "pretty"

@[test]
def test_typecheck_lang_scope : Bool := typecheck_file "lang/scope.mo" "scope"

// Note: typecheck/infer.mo and typecheck/unify.mo are part of the type checker itself
// and may have circular dependencies.

@[test]
def test_typecheck_lang_typecheck_infer : Bool := typecheck_file "lang/typecheck/infer.mo" "typecheck_infer"

@[test]
def test_typecheck_lang_typecheck_unify : Bool := typecheck_file "lang/typecheck/unify.mo" "typecheck_unify"

// --- lang/codegen/ files ---

@[test]
def test_typecheck_lang_codegen_ir : Bool := typecheck_file "lang/codegen/ir.mo" "codegen_ir"

@[test]
def test_typecheck_lang_codegen_emit : Bool := typecheck_file "lang/codegen/emit.mo" "codegen_emit"

@[test]
def test_typecheck_lang_codegen_link : Bool := typecheck_file "lang/codegen/link.mo" "codegen_link"
