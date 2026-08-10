use lang.types {mk, name}
use lang.module {mk}
use lang.codegen.ir {LLVMDeclaration, LLVMFunction, LLVMGlobal, LLVMModule, mk}
use lang.codegen.emit {mk}

open Param {mk}
open Def {mk, name}

/// Extract the name from an LLVMFunction
#[partial]
def get_function_name (func : LLVMFunction) : String := 
    match func {
        LLVMFunction.mk name _ _ _ _ => name
    }

/// Extract the name from an LLVMGlobal
#[partial]
def get_global_name (global : LLVMGlobal) : String := 
    match global {
        LLVMGlobal.mk name _ _ _ => name
    }

/// Extract the name from an LLVMDeclaration
#[partial]
def get_declaration_name (decl : LLVMDeclaration) : String := 
    match decl {
        LLVMDeclaration.mk name _ _ => name
    }

/// Extract names from a list using a extraction function
#[partial]
def extract_names (items : List A) (getter : A -> String) : List String := 
    match items {
        List.empty => List.empty,
        List.cons h t => List.cons (getter h) (extract_names t getter)
    }

/// Get all defined symbol names from an LLVMModule
#[partial]
def get_module_symbol_names (mod : LLVMModule) : List String := 
    match mod {
        LLVMModule.mk _ globals functions declarations =>
            List.append (List.append (extract_names functions get_function_name) (extract_names globals get_global_name)) (extract_names declarations get_declaration_name)
    }

/// Check if IR text contains a symbol definition
#[partial]
def ir_contains_symbol (ir_text : String) (symbol : String) : Bool := 
    String.contains ir_text symbol
