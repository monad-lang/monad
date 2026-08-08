use io {IO, println, read_file, write_file}
open IO {println, read_file, write_file}
use process {exec_cmd}
use lang.types {
  Decl, Def, LoadedModules, LocalScope, ModulePath, Scope, Term, TypeConstraint,
  app, i64, id, if_, lam, lit, mk, mp, name, named, nid, num, type_, var,
}
use lang.codegen.ir {add, emit_module, mk}
use lang.codegen.emit {compile_db_module, compile_loaded_modules_to_ir, mk, ok}
use lang.module {
  LoadedModules, extract_directory, load_file_modules,
  load_module_decls_with_dependencies, mk, string_find_last_slash,
  try_parse_decls,
}
use lang.parser.core {mk}
use lang.typecheck.infer {empty_local_types, empty_locals, mk, type_check}
use lang.scope {add_builtins, scope_data_empty}
use lang.cli {*}
use std.list {Show, length}

open LLVMType {}
open LLVMValue {add}
open Term {app, lam, lit, type_, var}
open Literal {if_, num}
open Identifier {id}
open DebugName {named}
open ParseResult {}
open NumSuffix {i64}
open Param {mk}
open Def {mk, name}
open ModulePath {mp}
open TypeError {}


#[partial]
def empty_str_list : List String := []

#[partial]
def mk_var (name : String) : Term :=
    Term.var 0 (DebugName.named (Identifier.id name))

#[partial]
def mk_native_app (op_name : String) (a : I64) (b : I64) : Term :=
    let nid := mk_var op_name in
    Term.app (Term.app nid (Term.lit (Literal.num a NumSuffix.i64)))
        (Term.lit (Literal.num b NumSuffix.i64))

#[partial]
def mk_native_app_t (op_name : String) (a : Term) (b : Term) : Term :=
    let nid := mk_var op_name in
    Term.app (Term.app nid a) b

#[partial]
def mk_call (fn_name : String) (arg : Term) : Term :=
    Term.app (mk_var fn_name) arg

#[partial]
def mk_i64 (n : I64) : Term :=
    Term.lit (Literal.num n NumSuffix.i64)

#[partial]
def mk_lam (name : String) (body : Term) : Term :=
    Term.lam (DebugName.named (Identifier.id name)) (Term.type_ 1) body

/// Empty local scope for type checking
#[partial]
def empty_locals : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// Empty list of local types for type checking
#[partial]
def empty_local_types : List Term := List.empty

/// Create a scope with builtins for type checking
#[partial]
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
#[partial]
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
#[partial]
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
#[partial]
def typecheck_and_print (defs : List Def) : IO I64 :=
    if typecheck_defs defs then do {
        println "Type check: PASS";
        return 0
    } else do {
        println "Type check: FAIL";
        return 1
    }

#[partial]
def mk_def (name : String) (body : Term) : Def :=
    Def.mk (ModulePath.mp [Identifier.id name]) (Term.type_ 1) body
        ([] : List TypeConstraint) ([] : List String)

#[partial]
def mk_if (cond : Term) (then_ : Term) (else_ : Term) : Term :=
    Term.lit (Literal.if_ cond then_ else_)

/// Parse a source file and compile + run it via LLVM.
#[partial]
def compile_parsed_decls (decls : List Decl) (output_dir : String) (output_name : String) (verbose: Bool) : IO I64 {
    let mod_ := compile_db_module decls;
    let ir_text := emit_module mod_;
    let ir_path := String.concat output_dir (String.concat "/" (String.concat output_name ".ll"));
    let obj_path := String.concat output_dir (String.concat "/" (String.concat output_name ".o"));
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir (String.concat "/" output_name);

    println <| "Writing LLVM IR to: " ++ ir_path;
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
    let result <- exec_cmd "clang" (List.append [ obj_path, runtime_obj, "-o", output_path] (if verbose then ["-v"] else [""]));
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
#[partial]
def load_file_decls_with_dependencies (file_path : String) : IO (Option (List Decl)) :=
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
#[partial]
def compile_file (file_path : String) (output_dir : String) (output_name : String) (verbose : Bool) : IO I64 {
    println <| "compiling: " ++ file_path ++ " to " ++ output_dir ++ "/" ++ output_name;
    // First try to load with module boundaries preserved
    let res : Result String LoadedModules <- load_file_modules file_path;
    match res {
        Result.ok loaded => do {
            println <| "modules loaded:\n" ++ Show.show loaded;
            let mod_ <- compile_loaded_modules_to_ir loaded;
            let ir_text := emit_module mod_;
            let ir_path := output_dir ++ "/" ++ output_name ++ ".ll";
            let obj_path := output_dir ++ "/" ++ output_name ++ ".o";
            let runtime_obj := output_dir ++ "/monad_runtime.o";
            let output_path := output_dir ++ "/" ++ output_name;

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
                    let result <- exec_cmd "clang" (List.append [ obj_path, runtime_obj, "-o", output_path] (if verbose then ["-v"] else [""]));
                    if not (result == 0) then do {
                        println <| "linking failed";
                        return 1
                    } else do {
                        println "Compilation finished";
                        return 0
                    }
                }
            }
        },
        Result.err e => do {
            println ("Failed to parse dependencies: " ++ e);
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

// `Command` and its argv parser are hand-written (not `#[derive_cli]`) and
// this file stays free of any macro/attribute-derive syntax on purpose: the
// self-hosted compiler's own parser/typechecker (lang/parser.mo,
// lang/typecheck/infer.mo) doesn't understand `#[derive_cli]` yet, and
// lang/main.mo is one of the files the self-hosted parse/scope/typecheck
// test suite (lang/tests/parser_file_tests.mo, scope_all_tests.mo,
// typecheck_lang_tests.mo) re-parses with that self-hosted pipeline. It
// does share `lang/cli.mo`'s small runtime helpers with the macro-derived
// demo in lang/tests/cli_derive_tests.mo, though — same argv-munging
// primitives either way.
type Command {
    compile (file: String) (out_name: String) (verbose: Bool),
    pretty (file: String),
    help
}

/// `compile <path> [name]` (original positional form) and `compile <path>
/// [--output/-o <name>] [--verbose/-v]` (flag form) both work; an explicit
/// `--output`/`-o` wins over a positional name if both are given.
def Command.from_args (args : List String) : Command :=
    match args {
        List.cons cmd rest =>
            if cmd == "compile" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        match Cli.take_opt "output" "o" "" rest1 {
                            Cli.OptResult.opt_result opt_out_name rest2 =>
                                match Cli.take_positional rest2 {
                                    Cli.PosResult.pos_result path_opt rest3 =>
                                        match Cli.take_positional rest3 {
                                            Cli.PosResult.pos_result name_opt _ =>
                                                let out_name :=
                                                    if String.is_empty opt_out_name then
                                                        match name_opt {
                                                            Option.some n => n,
                                                            Option.none => "source",
                                                        }
                                                    else
                                                        opt_out_name
                                                in
                                                match path_opt {
                                                    Option.some path => Command.compile path out_name verbose,
                                                    Option.none => Command.help,
                                                },
                                        },
                                },
                        },
                }
            else if cmd == "pretty" then
                match Cli.take_positional rest {
                    Cli.PosResult.pos_result path_opt _ =>
                        match path_opt {
                            Option.some path => Command.pretty path,
                            Option.none => Command.help,
                        },
                }
            else
                Command.help,
        List.empty => Command.help,
    }

// Smoke tests for `Command.from_args` live in lang/tests/main_tests.mo
// (run via `cargo run -- test lang/tests/main_tests.mo`), not inline here.

/// Current main entrypoint of self hosted compiler
def main (args : List String) : IO I64 {
    let out_dir := "/tmp";
    let cmd : Command := Command.from_args args;
    match cmd {
        compile file_path out_name verbose => do {
            compile_file file_path out_dir out_name verbose
        },
        pretty file_path => do {
            println <| "loading " ++ file_path;
            // TODO fix type checking bug on res
            let res : Result String LoadedModules <- load_file_modules file_path;
            match res {
                ok loaded => do {
                    println <| "modules loaded:\n" ++ Show.show loaded;
                    return 0
                },
                err e => do {
                    println ("Failed to parse dependencies: " ++ e);
                    return 1
                }
            }
        },
        help => do {
            print_help
        }
    }
}

#[partial]
def print_help : IO I64 {
    println "Usage: monad compile <path> [name] [--output/-o <name>] [--verbose/-v]";
    println "         Parse and compile a .mo source file";
    println "       monad pretty <path>  Parse and pretty print a .mo source file";
    return 0
}
