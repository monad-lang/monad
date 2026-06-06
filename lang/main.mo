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
def args4 (a : String) (b : String) (c : String) (d : String) : List String :=
    [a, b, c, d]

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
                ok tt => true,
                err e => false,
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

// === Examples ===

@[partial]
def build_const42 : List Def :=
    [mk_def "main" (mk_i64 42)]

@[partial]
def build_add : List Def :=
    [mk_def "main" (mk_native_app "I64_add" 1 2)]

@[partial]
def build_arithmetic : List Def :=
    let one := mk_i64 1 in
    let mul_2_3 := mk_native_app "I64_mul" 2 3 in
    let body := Term.app (Term.app (mk_var "I64_add") one) mul_2_3 in
    [mk_def "main" body]

@[partial]
def build_nested_if : List Def :=
    let inner_cond := mk_native_app "I64_eq" 1 2 in
    let inner_if := mk_if inner_cond (mk_i64 1) (mk_i64 2) in
    let outer_cond := mk_native_app "I64_eq" 1 1 in
    let body := mk_if outer_cond inner_if (mk_i64 3) in
    [mk_def "main" body]

@[partial]
def build_iftrue : List Def :=
    let cond := mk_native_app "I64_eq" 1 1 in
    [mk_def "main" (mk_if cond (mk_i64 42) (mk_i64 0))]

@[partial]
def build_iffalse : List Def :=
    let cond := mk_native_app "I64_eq" 1 2 in
    [mk_def "main" (mk_if cond (mk_i64 99) (mk_i64 100))]

@[partial]
def build_multicall : List Def :=
    let square_body := mk_native_app_t "I64_mul" (mk_var "x") (mk_var "x") in
    let square_def := mk_def "square" (mk_lam "x" square_body) in
    let main_def := mk_def "main" (mk_call "square" (mk_i64 5)) in
    [square_def, main_def]

@[partial]
def build_lambda : List Def :=
    let lam_body := mk_native_app_t "I64_add" (mk_var "x") (mk_i64 1) in
    let lam := mk_lam "x" lam_body in
    let call := Term.app lam (mk_i64 5) in
    [mk_def "main" call]

@[partial]
def build_factorial : List Def :=
    let n_var := mk_var "n" in
    let zero_ := mk_i64 0 in
    let one_ := mk_i64 1 in
    let n_minus_1 := mk_native_app_t "I64_sub" n_var one_ in
    let fact_rec := mk_call "factorial" n_minus_1 in
    let mul_rec := mk_native_app_t "I64_mul" n_var fact_rec in
    let eq_zero := mk_native_app_t "I64_eq" n_var zero_ in
    let if_body := mk_if eq_zero one_ mul_rec in
    let fact_def := mk_def "factorial" (mk_lam "n" if_body) in
    let main_def := mk_def "main" (mk_call "factorial" (mk_i64 5)) in
    [fact_def, main_def]

// === Names ===

@[partial]
def example_names : List String :=
    ["const42", "add", "arithmetic", "iftrue", "iffalse",
     "multicall", "lambda", "factorial"]

@[partial]
def get_example_defs (name : String) : Option (List Def) :=
    if String.beq name "const42" then Option.some build_const42
    else if String.beq name "add" then Option.some build_add
    else if String.beq name "arithmetic" then Option.some build_arithmetic
    else if String.beq name "iftrue" then Option.some build_iftrue
    else if String.beq name "iffalse" then Option.some build_iffalse
    else if String.beq name "multicall" then Option.some build_multicall
    else if String.beq name "lambda" then Option.some build_lambda
    else if String.beq name "factorial" then Option.some build_factorial
    else Option.none

@[partial]
def get_expected (name : String) : I64 :=
    if String.beq name "const42" then 42
    else if String.beq name "add" then 3
    else if String.beq name "arithmetic" then 7
    else if String.beq name "iftrue" then 42
    else if String.beq name "iffalse" then 100
    else if String.beq name "multicall" then 25
    else if String.beq name "lambda" then 6
    else if String.beq name "factorial" then 120
    else 0

// === Compile & run ===

@[partial]
def compile_and_run (defs : List Def) (output_dir : String) (output_name : String) (expect : I64) : IO I64 {
    let ir_path := String.concat output_dir (String.concat "/" (String.concat output_name ".ll"));
    let obj_path := String.concat output_dir (String.concat "/" (String.concat output_name ".o"));
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir (String.concat "/" output_name);

    let mod_ := lang.codegen.emit.compile_db_decls_ir defs;
    let ir_text := lang.codegen.ir.emit_module mod_;
    IO.write_file ir_path ir_text;

    let _ <- exec_cmd "llc" (args4 "-filetype=obj" ir_path "-o" obj_path);
    let _ <- exec_cmd "clang" (args4 "-c" "lang/codegen/runtime.c" "-o" runtime_obj);
    let _ <- exec_cmd "clang" (args4 obj_path runtime_obj "-o" output_path);

    let exit_code <- exec_cmd output_path empty_str_list;
    if I64.beq exit_code expect then do {
        println (String.concat "PASS " (String.concat output_name (String.concat ": exit " (I64.to_string exit_code))));
        return 0
    } else do {
        println (String.concat "FAIL " (String.concat output_name (String.concat ": exit " (String.concat (I64.to_string exit_code) (String.concat " expected " (I64.to_string expect))))));
        return 1
    }
}

@[partial]
def missing_name (name : String) : IO I64 {
    println (String.concat "Missing: " name);
    return 1
}

@[partial]
def run_one (name : String) (out_dir : String) : IO I64 :=
    let expect := get_expected name in
    match get_example_defs name {
        Option.some defs => compile_and_run defs out_dir name expect,
        Option.none => missing_name name
    }

@[partial]
def all_done : IO I64 {
    println "All examples passed";
    return 0
}

@[partial]
def abort_failure : IO I64 {
    println "Aborting after failure";
    return 1
}

@[partial]
def run_all_cont (rest : List String) (out_dir : String) (r : I64) : IO I64 :=
    if I64.beq r 0
    then run_all rest out_dir
    else abort_failure

@[partial]
def run_all (names : List String) (out_dir : String) : IO I64 :=
    match names {
        List.cons name rest =>
            Monad.bind (run_one name out_dir) (run_all_cont rest out_dir),
        List.empty => all_done
    }

@[partial]
def print_help : IO I64 {
    println "Usage: monad compile-test <name>    Compile and run named example";
    println "       monad compile <path> [name]  Parse and compile a .mo source file";
    println "       monad test-all               Compile and run all examples";
    println "       monad typecheck <name>       Type-check a named example";
    println "       monad typecheck-all          Type-check all examples";
    println "       monad list                   List available examples";
    return 0
}

@[partial]
def print_one (name : String) : IO I64 {
    let expect := get_expected name;
    let msg := String.concat "  " (String.concat name (String.concat " (expect: " (String.concat (I64.to_string expect) ")")));
    println msg;
    return 0
}

@[partial]
def print_list_cont (rest : List String) (_ : I64) : IO I64 := print_list rest

def print_list (names : List String) : IO I64 :=
    match names {
        List.cons name rest =>
            (print_one name) >>= (print_list_cont rest),
        List.empty => Monad.pure 0
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

/// Parse a source file and compile + run it via LLVM.
@[partial]
def compile_parsed_decls (decls : List Decl) (output_dir : String) (output_name : String) : IO I64 {
    let mod_ := lang.codegen.emit.compile_db_module decls;
    let ir_text := lang.codegen.ir.emit_module mod_;
    let ir_path := String.concat output_dir (String.concat "/" (String.concat output_name ".ll"));
    let obj_path := String.concat output_dir (String.concat "/" (String.concat output_name ".o"));
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir (String.concat "/" output_name);

    IO.write_file ir_path ir_text;

    let _ <- exec_cmd "llc" (args4 "-filetype=obj" ir_path "-o" obj_path);
    let _ <- exec_cmd "clang" (args4 "-c" "lang/codegen/runtime.c" "-o" runtime_obj);
    let _ <- exec_cmd "clang" (args4 obj_path runtime_obj "-o" output_path);

    let exit_code <- exec_cmd output_path empty_str_list;
    println (String.concat (String.concat output_name " => exit ") (I64.to_string exit_code));
    return 0
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
    let mp : ModulePath := ModulePath.mp (List.cons (Identifier.id module_name) List.empty) in
    // Load the file and all its dependencies
    lang.module.load_module_decls_with_dependencies base_dir mp

/// Parse a source file and compile + run it via LLVM.
@[partial]
def compile_file (file_path : String) (output_dir : String) (output_name : String) : IO I64 {
    // First try to load with dependencies
    match load_file_decls_with_dependencies file_path {
        Option.some decls => compile_parsed_decls decls output_dir output_name,
        Option.none => do {
            // Fallback to simple parsing without dependencies (for error reporting)
            let source <- IO.read_file file_path;
            match lang.module.try_parse_decls source {
                Option.some decls => compile_parsed_decls decls output_dir output_name,
                Option.none => do {
                    println (String.concat "Parse error: " file_path);
                    return 1
                }
            }
        }
    }
}

/// Type-check a named example and print results
@[partial]
def typecheck_one (name : String) : IO I64 :=
    match get_example_defs name {
        Option.some defs => typecheck_and_print defs,
        Option.none => missing_name name
    }

/// Type-check all examples
@[partial]
def typecheck_all_cont (rest : List String) (r : I64) : IO I64 :=
    if I64.beq r 0
    then typecheck_all rest
    else abort_failure

/// Type-check all examples
@[partial]
def typecheck_all (names : List String) : IO I64 :=
    match names {
        List.cons name rest =>
            Monad.bind (typecheck_one name) (typecheck_all_cont rest),
        List.empty => all_done
    }

/// Current main entrypoint of self hosted compiler
def main (args : List String) : IO I64 {
    let cmd := first_arg args;
    let out_dir := "/tmp";
    if cmd == "compile-test" then do {
        let name := second_arg args;
        run_one name out_dir
    }
    else if cmd == "compile" then do {
        let file_path := second_arg args;
        let out_name := if third_arg args == ""
            then "source"
            else third_arg args;
        compile_file file_path out_dir out_name
    }
    else if cmd == "test-all" then do {
        println "Running all examples...";
        run_all example_names out_dir
    }
    else if cmd == "typecheck" then do {
        let name := second_arg args;
        typecheck_one name
    }
    else if cmd == "typecheck-all" then do {
        println "Type-checking all examples...";
        typecheck_all example_names
    }
    else if cmd == "list" then do {
        println "Available examples:";
        print_list example_names
    }
    else do {
        print_help
    }
}
