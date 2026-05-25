use io
open IO
use process
use lang.types
use lang.codegen.ir
use lang.codegen.emit

open LLVMType
open LLVMValue
open TermV0
open Literal
open Identifier
open NameRef
open NumSuffix
open ParamV0
open DefV0
open ModulePath

@[partial]
def args4 (a : String) (b : String) (c : String) (d : String) : List String :=
    List.cons a (List.cons b (List.cons c (List.cons d List.empty)))

@[partial]
def empty_str_list : List String := List.empty

@[partial]
def make_native_app (op_name : String) (a : I64) (b : I64) : TermV0 :=
    let nid := NameRef.nid (Identifier.id op_name) in
    let var_ := TermV0.var nid in
    let app1 := TermV0.app var_ (TermV0.lit (LiteralV0.num a NumSuffix.i64)) in
    TermV0.app app1 (TermV0.lit (LiteralV0.num b NumSuffix.i64))

@[partial]
def build_const42 : List DefV0 :=
    let id := Identifier.id "main" in
    let body := TermV0.lit (LiteralV0.num 42 NumSuffix.i64) in
    let def_ := DefV0.mk
        (ModulePath.mp (List.cons id List.empty))
        (TermV0.type_ 1)
        body
        List.empty
        List.empty in
    List.cons def_ List.empty

@[partial]
def build_add : List DefV0 :=
    let id := Identifier.id "main" in
    let body := make_native_app "I64_add" 1 2 in
    let def_ := DefV0.mk
        (ModulePath.mp (List.cons id List.empty))
        (TermV0.type_ 1)
        body
        List.empty
        List.empty in
    List.cons def_ List.empty

@[partial]
def build_arithmetic : List DefV0 :=
    let id := Identifier.id "main" in
    let one := TermV0.lit (LiteralV0.num 1 NumSuffix.i64) in
    let mul_2_3 := make_native_app "I64_mul" 2 3 in
    let nid := NameRef.nid (Identifier.id "I64_add") in
    let var_ := TermV0.var nid in
    let app1 := TermV0.app var_ one in
    let body := TermV0.app app1 mul_2_3 in
    let def_ := DefV0.mk
        (ModulePath.mp (List.cons id List.empty))
        (TermV0.type_ 1)
        body
        List.empty
        List.empty in
    List.cons def_ List.empty

@[partial]
def build_iftrue : List DefV0 :=
    let id := Identifier.id "main" in
    let cond := make_native_app "I64_eq" 1 1 in
    let body := TermV0.lit
        (LiteralV0.if_ cond
            (TermV0.lit (LiteralV0.num 42 NumSuffix.i64))
            (TermV0.lit (LiteralV0.num 0 NumSuffix.i64))) in
    let def_ := DefV0.mk
        (ModulePath.mp (List.cons id List.empty))
        (TermV0.type_ 1)
        body
        List.empty
        List.empty in
    List.cons def_ List.empty

@[partial]
def build_iffalse : List DefV0 :=
    let id := Identifier.id "main" in
    let cond := make_native_app "I64_eq" 1 2 in
    let body := TermV0.lit
        (LiteralV0.if_ cond
            (TermV0.lit (LiteralV0.num 99 NumSuffix.i64))
            (TermV0.lit (LiteralV0.num 100 NumSuffix.i64))) in
    let def_ := DefV0.mk
        (ModulePath.mp (List.cons id List.empty))
        (TermV0.type_ 1)
        body
        List.empty
        List.empty in
    List.cons def_ List.empty

@[partial]
def example_names : List String :=
    List.cons "const42"
        (List.cons "add"
        (List.cons "arithmetic"
        (List.cons "iftrue"
        (List.cons "iffalse"
        List.empty))))

@[partial]
def get_example_defs (name : String) : Option (List DefV0) :=
    if String.beq name "const42" then Option.some build_const42
    else if String.beq name "add" then Option.some build_add
    else if String.beq name "arithmetic" then Option.some build_arithmetic
    else if String.beq name "iftrue" then Option.some build_iftrue
    else if String.beq name "iffalse" then Option.some build_iffalse
    else Option.none

@[partial]
def get_expected (name : String) : I64 :=
    if String.beq name "const42" then 42
    else if String.beq name "add" then 3
    else if String.beq name "arithmetic" then 7
    else if String.beq name "iftrue" then 42
    else if String.beq name "iffalse" then 100
    else 0

@[partial]
def compile_and_run (defs : List DefV0) (output_dir : String) (output_name : String) (expect : I64) : IO I64 {
    let ir_path := String.concat output_dir (String.concat "/" (String.concat output_name ".ll"));
    let obj_path := String.concat output_dir (String.concat "/" (String.concat output_name ".o"));
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir (String.concat "/" output_name);

    let mod_ := lang.codegen.emit.compile_decls_ir defs;
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
    println "Usage: monad-self compile <name>     Compile and run named example";
    println "       monad-self test-all           Compile and run all examples";
    println "       monad-self list               List available examples";
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

/// Current main entrypoint of self hosted compiler
def main (args : List String) : IO I64 {
    let cmd := first_arg args;
    let out_dir := "/tmp";
    if cmd == "compile" then do {
        let name := second_arg args;
        run_one name out_dir
    }
    else if cmd == "test-all" then do {
        println "Running all examples...";
        run_all example_names out_dir
    }
    else if cmd == "list" then do {
        println "Available examples:";
        print_list example_names
    }
    else do {
        print_help
    }
}
