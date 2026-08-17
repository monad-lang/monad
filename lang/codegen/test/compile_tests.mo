use process {exec_cmd}
use lang.types {
  Def, Term, TypeConstraint, i64, id, lit, mk, mp, name, num, type_,
}
use lang.codegen.ir {emit_module, mk}
use lang.codegen.emit {compile_db_decls_ir, mk}

open Term {lit, type_}
open Literal {num}
open Identifier {id}
open NumSuffix {i64}
open Param {mk}
open Def {mk, name}
open ModulePath {mp}
open IO {println, write_file}

#[partial]
def mk_def (name : String) (body : Term) : Def :=
    Def.mk (ModulePath.mp [Identifier.id name]) (Term.type_ 1) body
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private

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

/// Shared compile+link+execute helper for the regression tests below --
/// same llc/clang/clang pipeline as test_compile_42, parameterized by a
/// unique basename (so tests don't clobber each other's /tmp files) and
/// the expected process exit code.
#[partial]
def compile_link_run_expect (defs : List Def) (basename : String) (expected : I64) : IO Bool := do {
    let output_dir := "/tmp/monad_e2e";
    let ir_path := output_dir ++ "/" ++ basename ++ ".ll";
    let obj_path := output_dir ++ "/" ++ basename ++ ".o";
    // Per-test runtime object path (not the shared "monad_runtime.o"
    // test_compile_42 uses) -- tests in this file can run concurrently,
    // and a shared path raced between them (one test's cleanup `rm`
    // deleting/overwriting the .o file while another was still linking
    // against or executing it), producing spurious wrong-output failures
    // unrelated to the codegen logic actually under test.
    let runtime_obj := output_dir ++ "/" ++ basename ++ "_runtime.o";
    let output_path := output_dir ++ "/" ++ basename;

    let _ <- exec_cmd "mkdir" ["-p", output_dir];

    let mod_ := lang.codegen.emit.compile_db_decls_ir defs;
    let ir_text := lang.codegen.ir.emit_module mod_;
    IO.write_file ir_path ir_text;

    let llc_result <- exec_cmd "llc" ["-filetype=obj", ir_path, "-o", obj_path];
    if not (llc_result == 0) then do {
        println <| basename ++ ": llc failed";
        return false
    } else do {
        let rt_result <- exec_cmd "clang" ["-c", "lang/codegen/runtime.c", "-o", runtime_obj];
        if not (rt_result == 0) then do {
            println <| basename ++ ": compiling runtime failed";
            return false
        } else do {
            let link_args := [obj_path, runtime_obj];
            let link_result <- exec_cmd "clang" (List.append link_args ["-o", output_path]);
            if not (link_result == 0) then do {
                println <| basename ++ ": clang linker failed";
                return false
            } else do {
                let exec_result <- exec_cmd output_path [];
                let _ <- exec_cmd "rm" ["-f", ir_path, obj_path, runtime_obj, output_path];
                println <| basename ++ ": expected " ++ I64.to_string expected ++ ", got " ++ I64.to_string exec_result;
                return (exec_result == expected)
            }
        }
    }
}

/// Regression test for the multi-arg direct-call fix
/// (compile_general_db_call/flatten_app_spine, lang/codegen/emit.mo):
/// a call to a top-level 2-param function used to compile as two
/// separate, each-wrong, single-argument calls instead of one correct
/// 2-argument call. `subtract 10 3` must produce 7.
#[test]
def test_compile_multiarg_call : IO Bool := do {
    let x_id := Identifier.id "x";
    let y_id := Identifier.id "y";
    let x_var := Term.var 0 (DebugName.named x_id);
    let y_var := Term.var 1 (DebugName.named y_id);
    let sub_var := Term.var 0 (DebugName.named (Identifier.id "I64_sub"));
    let sub_body := Term.app (Term.app sub_var x_var) y_var;
    let subtract_term := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) sub_body);
    let subtract_def := Def.mk (ModulePath.mp (List.cons (Identifier.id "subtract") List.empty)) (Term.type_ 1) subtract_term
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private;
    let subtract_ref := Term.var 0 (DebugName.named (Identifier.id "subtract"));
    let main_body := Term.app (Term.app subtract_ref (mk_i64 10)) (mk_i64 3);
    let main_def := mk_def "main" main_body;
    compile_link_run_expect [subtract_def, main_def] "test_multiarg" 7
}

/// Regression tests for the real compile_match_ir tag-dispatch
/// implementation (lang/codegen/emit.mo), the runtime tag/field
/// accessors and List/constructor tag fixes (runtime.c), and the
/// compile_db_def_ir "already terminated" fix (needed because a
/// whole-body match like this compiles its own terminator, same shape
/// as init/prelude.mo's List.last/Option.get_or_default). Matching on
/// `some 42` must take the `some` branch (42), and matching on `none`
/// must take the `none` branch (99) -- the two tests sharing the same
/// case structure but different scrutinees is what actually proves tag
/// dispatch discriminates: the old "always compile the first arm" stub
/// would make BOTH tests return the same value.
#[partial]
def build_option_match_main (scrutinee : Term) : Def :=
    let option_typ := ModulePath.mp (List.cons (Identifier.id "Option") List.empty) in
    let a_id := Identifier.id "a" in
    let some_case := MatchCase.mc (Identifier.id "some") (List.cons a_id List.empty) (Term.var 0 (DebugName.named a_id)) in
    let none_case := MatchCase.mc (Identifier.id "none") List.empty (mk_i64 99) in
    let cases := List.cons some_case (List.cons none_case List.empty) in
    let main_body := Term.lit (Literal.match_ scrutinee cases) in
    mk_def "main" main_body

#[test]
def test_compile_match_dispatch_some : IO Bool := do {
    let option_typ := ModulePath.mp (List.cons (Identifier.id "Option") List.empty);
    let some_con := Con.mk (Identifier.id "some") option_typ 1 (List.cons (Option.some (mk_i64 42)) List.empty);
    let scrutinee := Term.con some_con;
    let main_def := build_option_match_main scrutinee;
    compile_link_run_expect [main_def] "test_match_some" 42
}

#[test]
def test_compile_match_dispatch_none : IO Bool := do {
    let option_typ := ModulePath.mp (List.cons (Identifier.id "Option") List.empty);
    let none_con := Con.mk (Identifier.id "none") option_typ 0 List.empty;
    let scrutinee := Term.con none_con;
    let main_def := build_option_match_main scrutinee;
    compile_link_run_expect [main_def] "test_match_none" 99
}
