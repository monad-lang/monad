use process {exec_cmd}
use lang.types {
  Def, Term, TypeConstraint, i64, id, lit, mk, mp, name, num, type_,
}
use lang.codegen.ir {emit_module, mk}
use lang.codegen.emit {compile_db_decls_ir, mk}

open Term {lit, type_}
open Literal {num}
open Identifier {id}
open DebugName {}
open NumSuffix {i64}
open Param {mk}
open Def {mk, name}
open ModulePath {mp}
open Monad {}
open IO {println, write_file}

#[partial]
def mk_def (name : String) (body : Term) : Def :=
    Def.mk (ModulePath.mp [Identifier.id name]) (Term.type_ 1) body
        ([] : List TypeConstraint) ([] : List String)

#[partial]
def mk_i64 (n : I64) : Term :=
    Term.lit (Literal.num n NumSuffix.i64)

/// Simple test: compile and run a program that returns 42
#[test]
def test_compile_42 : IO Bool := do {
    let defs := [mk_def "main" (mk_i64 42)];
    
    let output_dir := "/tmp/monad_e2e";
    let ir_path := String.concat output_dir "/test_42.ll";
    let obj_path := String.concat output_dir "/test_42.o";
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir "/test_42";
    
    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    
    let mod_ := lang.codegen.emit.compile_db_decls_ir defs;
    let ir_text := lang.codegen.ir.emit_module mod_;
    IO.write_file ir_path ir_text;
    println ("wrote ir to: " ++ ir_path);
    
    let llc_result <- exec_cmd "llc" ["-filetype=obj", ir_path, "-o", obj_path];
    if not (llc_result == 0) then do {
        println <| "llc failed";
        return false
    } else do {
    
        let rt_result <- exec_cmd "clang" ["-c" "lang/codegen/runtime.c" "-o" runtime_obj];
        if not (rt_result == 0) then do {
            println <| "compiling runtime failed";
            return false
        } else do {
    
            let link_args := [obj_path, runtime_obj];
            let link_result <- exec_cmd "clang" (List.append link_args ["-o", output_path]);
            if not (link_result == 0) then do {
                println <| "clang linker failed";
                return false
            } else do {    
                let exec_result <- exec_cmd output_path [];

                let _ <- exec_cmd "rm" ["-f", ir_path, obj_path, runtime_obj, output_path];

                return (exec_result == 42)
            }
        }
    }
}
