use io
open IO
use process
use lang.types
use lang.codegen.ir
use lang.codegen.emit
use lang.module
use lang.parser
use lang.parser.core
use lang.parser.combinators
use lang.typecheck.infer
use lang.scope
use std.list

open LLVMType
open LLVMValue
open Term
open Literal
open Identifier
open DebugName
open ParseResult
open NumSuffix
open Param
open Def
open ModulePath
open TypeError


@[partial]
def empty_str_list : List String := []

@[partial]
def mk_var (name : String) : Term :=
    Term.var 0 (DebugName.named (Identifier.id name))

@[partial]
def mk_native_app (op_name : String) (a : I64) (b : I64) : Term :=
    let nid := mk_var op_name in
    Term.app (Term.app nid (Term.lit (Literal.num a NumSuffix.i64)))
        (Term.lit (Literal.num b NumSuffix.i64))

@[partial]
def mk_native_app_t (op_name : String) (a : Term) (b : Term) : Term :=
    let nid := mk_var op_name in
    Term.app (Term.app nid a) b

@[partial]
def mk_call (fn_name : String) (arg : Term) : Term :=
    Term.app (mk_var fn_name) arg

@[partial]
def mk_i64 (n : I64) : Term :=
    Term.lit (Literal.num n NumSuffix.i64)

@[partial]
def mk_lam (name : String) (body : Term) : Term :=
    Term.lam (DebugName.named (Identifier.id name)) (Term.type_ 1) body

/// Empty local scope for type checking
@[partial]
def empty_locals : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// Empty list of local types for type checking
@[partial]
def empty_local_types : List Term := List.empty

/// Create a scope with builtins for type checking
@[partial]
def make_scope_with_builtins : Scope :=
    let empty_path := ModulePath.mp List.empty in
    let sd := lang.scope.scope_data_empty in
    let sd_with_builtins := lang.scope.add_builtins sd in
    {
        module_id := empty_path,
        scope := sd_with_builtins,
        parent := Option.none,
    }

/// Type-check a list of Defs. Returns true if all type-check successfully.
@[partial]
def typecheck_defs (defs : List Def) : Bool :=
    match defs {
        List.empty => true,
        List.cons def_ rest =>
            match typecheck_def def_ {
                true => typecheck_defs rest,
                false => false,
            },
    }

/// Type-check a single Def by checking its term.
@[partial]
def typecheck_def (def_ : Def) : Bool :=
    match def_ {
        Def.mk name typ term_ constraints attrs =>
            let scope := make_scope_with_builtins in
            match type_check term_ typ scope empty_local_types empty_locals {
                Result.ok tt => true,
                Result.err e => false,
            },
    }

/// Type-check a list of Defs and print results
@[partial]
def typecheck_and_print (defs : List Def) : IO I64 :=
    if typecheck_defs defs then do {
        println "Type check: PASS";
        return 0
    } else do {
        println "Type check: FAIL";
        return 1
    }

@[partial]
def mk_def (name : String) (body : Term) : Def :=
    Def.mk (ModulePath.mp [Identifier.id name]) (Term.type_ 1) body
        ([] : List TypeConstraint) ([] : List String)

@[partial]
def mk_if (cond : Term) (then_ : Term) (else_ : Term) : Term :=
    Term.lit (Literal.if_ cond then_ else_)

/// Parse a source file and compile + run it via LLVM.
@[partial]
def compile_parsed_decls (decls : List Decl) (output_dir : String) (output_name : String) (verbose: Bool) : IO I64 {
    let mod_ := compile_db_module decls;
    let ir_text := emit_module mod_;
    let ir_path := String.concat output_dir (String.concat "/" (String.concat output_name ".ll"));
    let obj_path := String.concat output_dir (String.concat "/" (String.concat output_name ".o"));
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir (String.concat "/" output_name);

    IO.write_file ir_path ir_text;

    let result <- exec_cmd "llc" [ "-filetype=obj", ir_path, "-o", obj_path];
    if not (result == 0) then do {
        println <| (String.concat "Compiling ir " (String.concat ir_path " with llc failed"));
        return 1
    } else do {
    let result <- exec_cmd "clang" (List.append [ "-c", "lang/codegen/runtime.c", "-o", runtime_obj] (if verbose then ["-v"] else [""]));
    if not (result == 0) then do {
        println <| "compiling runtime failed";
        return 1
    } else do {
    let result <- exec_cmd "lld" (List.append [ obj_path, runtime_obj, "-o", output_path] (if verbose then ["-v"] else [""]));
    if not (result == 0) then do {
        println <| "linking failed";
        return 1
    } else do {

    println "Compilation finished";
    return 0
    }}}
}

/// Load a file and all its transitive dependencies, returning a single list of declarations.
/// This function uses the module loading infrastructure to resolve all `use` dependencies.
@[partial]
def load_file_decls_with_dependencies (file_path : String) : Option (List Decl) :=
    // Extract the directory from the file path to use as base_dir for resolving relative imports
    let base_dir : String := lang.module.extract_directory file_path in
    // Extract module name from file path (remove .mo extension and directory)
    let last_slash : I64 := lang.module.string_find_last_slash file_path in
    let file_name_only :=
        if I64.lt last_slash 0 then
            file_path
        else
            String.slice file_path (last_slash + 1) (String.length file_path) in
    let module_name : String :=
        // Remove .mo extension
        if String.ends_with file_name_only ".mo" then
            String.slice file_name_only 0 (String.length file_name_only - 3)
        else
            file_name_only in
    let mp : ModulePath := ModulePath.mp [Identifier.id module_name] in
    // Load the file and all its dependencies
    lang.module.load_module_decls_with_dependencies base_dir mp

struct CompileOptions {
    file_path : String,
    output_dir : String,
    output_name : String,
    verbose : Bool,
}

/// Parse a source file and compile + run it via LLVM.
@[partial]
def compile_file (file_path : String) (output_dir : String) (output_name : String) (verbose : Bool) : IO I64 {
    // First try to load with dependencies
    match load_file_decls_with_dependencies file_path {
        Option.some decls => do {
            println (String.concat "parsed decls " (String.concat (List.length decls |> I64.to_string) " succesfully"));
            compile_parsed_decls decls output_dir output_name verbose
        },
        Option.none => do {
            println "Failed to parse dependencies";
            // Fallback to simple parsing without dependencies (for error reporting)
            let source <- IO.read_file file_path;
            match lang.module.try_parse_decls source {
                Option.some decls => compile_parsed_decls decls output_dir output_name verbose,
                Option.none => do {
                    println (String.concat "Parse error: " file_path);
                    return 1
                }
            }
        }
    }
}

/// Current main entrypoint of self hosted compiler
def main (args : List String) : IO I64 {
    let cmd := first_arg args;
    let out_dir := "/tmp";
    let verbose := false;
    if cmd == "compile" then do {
        let file_path := second_arg args;
        let out_name := if third_arg args == ""
            then "source"
            else third_arg args;
        compile_file file_path out_dir out_name verbose
    }
    else do {
        print_help
    }
}

@[partial]
def print_help : IO I64 {
    println "Usage: monad compile <path> [name]  Parse and compile a .mo source file";
    return 0
}
def first_arg (args : List String) : String :=
    match args {
        List.cons cmd rest => cmd,
        List.empty => ""
    }

def second_arg (args : List String) : String :=
    let tail :=
        match args {
            List.cons cmd rest => rest,
            List.empty => List.empty
        } in
    first_arg tail

def third_arg (args : List String) : String :=
    let tail :=
        match args {
            List.cons cmd rest => rest,
            List.empty => List.empty
        } in
    second_arg tail

