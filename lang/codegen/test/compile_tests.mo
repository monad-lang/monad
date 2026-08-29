use process {exec_cmd}
use lang.types {
  Decl, Def, Term, TypeConstraint, i64, id, lit, mk, mp, name, num, type_,
}
use lang.codegen.ir {emit_module, mk}
use lang.codegen.emit {compile_db_decls_ir, compile_db_module, mk}
use lang.scope {add_constraint_dict_params_decls, promote_instance_defs, resolve_class_calls_decls}

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
    let some_case := MatchCase.mc (Identifier.id "some") (List.cons a_id List.empty) (Term.var 0 (DebugName.named a_id)) Option.none in
    let none_case := MatchCase.mc (Identifier.id "none") List.empty (mk_i64 99) Option.none in
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

/// Builds `def add5 (a b : I64) : I64 := a + b` as a hand-constructed
/// Def -- shared by the two Phase 0 (closure-boxing/indirect-call)
/// regression tests below.
#[partial]
def build_add5_def : Def :=
    let a_id := Identifier.id "a" in
    let b_id := Identifier.id "b" in
    let a_var := Term.var 0 (DebugName.named a_id) in
    let b_var := Term.var 1 (DebugName.named b_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let add5_body := Term.app (Term.app add_var a_var) b_var in
    let add5_term := Term.lam (DebugName.named a_id) (Term.type_ 1) (Term.lam (DebugName.named b_id) (Term.type_ 1) add5_body) in
    Def.mk (ModulePath.mp (List.cons (Identifier.id "add5") List.empty)) (Term.type_ 1) add5_term
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private

/// Phase 0 regression test (see
/// plans/bootstrapping/self-hosted-compiler.md's dictionary-passing
/// plan): a bare reference to an arity>0 top-level def, used as a
/// VALUE (not immediately applied), used to compile as an invalid
/// eager 0-arg call -- `Term.var`'s value-position case now boxes it
/// via `alloc_closure` instead. Passing that boxed value as an ordinary
/// PARAMETER and calling it back through the parameter
/// (`compile_general_db_call`'s indirect-call dispatch via
/// `apply_closureN`) proves both halves round-trip correctly:
/// `apply_binary add5 2 3` must produce 5.
#[test]
def test_compile_function_value_as_parameter : IO Bool := do {
    let add5_def := build_add5_def;

    let f_id := Identifier.id "f";
    let x_id := Identifier.id "x";
    let y_id := Identifier.id "y";
    let f_var := Term.var 0 (DebugName.named f_id);
    let x_var := Term.var 1 (DebugName.named x_id);
    let y_var := Term.var 2 (DebugName.named y_id);
    let apply_body := Term.app (Term.app f_var x_var) y_var;
    let apply_term := Term.lam (DebugName.named f_id) (Term.type_ 1)
        (Term.lam (DebugName.named x_id) (Term.type_ 1)
            (Term.lam (DebugName.named y_id) (Term.type_ 1) apply_body));
    let apply_def := Def.mk (ModulePath.mp (List.cons (Identifier.id "apply_binary") List.empty)) (Term.type_ 1) apply_term
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private;

    let add5_ref := Term.var 0 (DebugName.named (Identifier.id "add5"));
    let apply_ref := Term.var 0 (DebugName.named (Identifier.id "apply_binary"));
    let main_body := Term.app (Term.app (Term.app apply_ref add5_ref) (mk_i64 2)) (mk_i64 3);
    let main_def := mk_def "main" main_body;
    compile_link_run_expect [add5_def, apply_def, main_def] "test_fn_value_param" 5
}

/// Phase 0 regression test, the OTHER half of the same fix: a function
/// value extracted from a constructor field via `match` is bound as a
/// `var_`-shaped local (an SSA temp holding the field's runtime value,
/// NOT a `parm_`) -- before this fix, `compile_general_db_call`'s
/// dispatch could not tell such a local apart from a literal callable
/// global NAME (both were `LLVMValue.var_`), so calling it either
/// mis-called a nonexistent `@tempN` symbol or (via the old `parm_`-only
/// path) silently produced `void_val`. `ir.mo`'s new `fn_ref` variant
/// (produced ONLY by a genuine bare-global-name callee) fixes the
/// ambiguity. `match (some add5) { some f => f 2 3, none => 0 }` must
/// produce 5.
#[test]
def test_compile_function_value_from_struct_field : IO Bool := do {
    let add5_def := build_add5_def;

    let option_typ := ModulePath.mp (List.cons (Identifier.id "Option") List.empty);
    let add5_ref := Term.var 0 (DebugName.named (Identifier.id "add5"));
    let some_con := Con.mk (Identifier.id "some") option_typ 1 (List.cons (Option.some add5_ref) List.empty);
    let scrutinee := Term.con some_con;

    let f_id := Identifier.id "f";
    let f_var := Term.var 0 (DebugName.named f_id);
    let call_f := Term.app (Term.app f_var (mk_i64 2)) (mk_i64 3);
    let some_case := MatchCase.mc (Identifier.id "some") (List.cons f_id List.empty) call_f Option.none;
    let none_case := MatchCase.mc (Identifier.id "none") List.empty (mk_i64 0) Option.none;
    let cases := List.cons some_case (List.cons none_case List.empty);
    let main_body := Term.lit (Literal.match_ scrutinee cases);
    let main_def := mk_def "main" main_body;
    compile_link_run_expect [add5_def, main_def] "test_fn_value_field" 5
}

/// Regression test for the `let`-chain beta-reduction fix
/// (`try_compile_let_beta_db`, lang/codegen/emit.mo): `let a := 2 in let
/// b := 3 in I64.add a b` desugars (lang/parser.mo's `let_term_body`) to
/// `Term.app (Term.lam a _ (Term.app (Term.lam b _ (I64.add a b)) 3)) 2`
/// -- BEFORE this fix, each `Term.lam` here compiled via
/// `compile_db_lam_ir`'s "lift to a brand-new top-level function" path
/// (correct for an escaping first-class lambda, wrong for a `let`): the
/// inner lifted function's only real parameter is its own `%p0`, but the
/// stale binding for `a` (itself only meaningful as the OUTER lifted
/// function's own `%p0`) was still carried into the inner function's
/// context, so BOTH `a` and `b` resolved to the exact same `%p0` --
/// `I64.add a b` silently compiled as `add i64 %p0, %p0`, returning 6
/// (3+3) instead of 5 (2+3). Also exercises the DOTTED name
/// ("I64.add", exactly as real parsed source produces, not the
/// pre-mangled "I64_add" `build_add5_def`/`test_compile_multiarg_call`
/// use above) through `lookup_native_any`'s own fix.
#[test]
def test_compile_nested_let_chain : IO Bool := do {
    let a_id := Identifier.id "a";
    let b_id := Identifier.id "b";
    let a_var := Term.var 0 (DebugName.named a_id);
    let b_var := Term.var 1 (DebugName.named b_id);
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64.add"));
    let add_call := Term.app (Term.app add_var a_var) b_var;
    let inner_let := Term.app (Term.lam (DebugName.named b_id) (Term.type_ 1) add_call) (mk_i64 3);
    let outer_let := Term.app (Term.lam (DebugName.named a_id) (Term.type_ 1) inner_let) (mk_i64 2);
    let main_def := mk_def "main" outer_let;
    compile_link_run_expect [main_def] "test_nested_let" 5
}

/// Regression test for `I64.to_string`'s missing runtime backing
/// (`monad_i64_to_string`, runtime.c + the `op_i64_to_string` NativeOp,
/// lang/codegen/emit.mo/ir.mo): like `I64.add`, `I64.to_string`
/// (init/number.mo) has no `:=` body at all -- before this fix it had
/// NO runtime implementation whatsoever (not even a broken one), so any
/// call compiled through the generic per-decl path (`compile_db_def_ir`
/// on `I64.to_string`'s own `Term.hole` body) produced a bogus `Unit`
/// constructor stub. Confirmed via a real repro (`println (I64.to_string
/// 6)` printed nothing at all). `String.length (I64.to_string 12345)`
/// must be 5 --
/// exercises both the new runtime primitive AND that its result is a
/// real, correctly-NUL-terminated string another native (`String.length`,
/// itself dispatched via the separate `Term.ntv`/`compile_ntv_ir`
/// mechanism) can consume.
#[test]
def test_compile_i64_to_string_native : IO Bool := do {
    let to_string_var := Term.var 0 (DebugName.named (Identifier.id "I64.to_string"));
    let str_val := Term.app to_string_var (mk_i64 12345);
    let native_args := List.cons (Option.some str_val) List.empty;
    let length_ntv := Native.mk (Identifier.id "string_length") 1 native_args;
    let main_body := Term.ntv length_ntv;
    let main_def := mk_def "main" main_body;
    compile_link_run_expect [main_def] "test_i64_to_string" 5
}

/// Regression test for the LLVM string-constant escaping bug
/// (`lang/codegen/ir.mo`'s `show_llvm_global`/`llvm_escape_string`,
/// fixed 2026-08-25): a string literal containing an embedded `"` and
/// `\` used to splice those raw bytes straight into the LLVM `c"..."`
/// constant with no escaping, producing textually-invalid IR (`llc`
/// rejected it: LLVM's parser treats the first unescaped `"` as the
/// string's end, so the declared `[N x i8]` length mismatched what
/// actually parsed). `String.length` of the raw literal (7 bytes: `a`
/// `"` `b` `\` `c` `"` `d`) must survive round-trip through emitted IR
/// unchanged -- this is exactly the shape `lang/json.mo`'s own string
/// literals hit (confirmed via a live repro compiling that file).
#[test]
def test_compile_string_literal_with_embedded_quote_and_backslash : IO Bool := do {
    let str_val := Term.lit (Literal.str "a\"b\\c\"d");
    let native_args := List.cons (Option.some str_val) List.empty;
    let length_ntv := Native.mk (Identifier.id "string_length") 1 native_args;
    let main_body := Term.ntv length_ntv;
    let main_def := mk_def "main" main_body;
    compile_link_run_expect [main_def] "test_string_escape" 7
}

/// Shared compile+link+execute helper, for a `List Decl` (as
/// `promote_instance_defs` produces) rather than a `List Def` --
/// `compile_db_module` (unlike `compile_db_decls_ir`) extracts every
/// `def_d` from a flat decl list itself, with no reachability
/// filtering (unlike the real `compile` CLI pipeline) -- exactly what a
/// direct, low-level test of `promote_instance_defs`'s own output
/// needs, no dependency on the wider check/scope pipeline.
#[partial]
def compile_decls_link_run_expect (decl_list : List Decl) (basename : String) (expected : I64) : IO Bool := do {
    let output_dir := "/tmp/monad_e2e";
    let ir_path := output_dir ++ "/" ++ basename ++ ".ll";
    let obj_path := output_dir ++ "/" ++ basename ++ ".o";
    let runtime_obj := output_dir ++ "/" ++ basename ++ "_runtime.o";
    let output_path := output_dir ++ "/" ++ basename;

    let _ <- exec_cmd "mkdir" ["-p", output_dir];

    let mod_ := lang.codegen.emit.compile_db_module decl_list;
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

/// Phase 2 (dictionary-passing plan) end-to-end regression test:
/// `promote_instance_defs` (lang/scope.mo) turns `class MyAdd A { def
/// add : A -> A -> A }` + `instance MyAdd I64 { def add := my_add }`
/// into a real top-level method def PLUS a real dictionary VALUE def (a
/// `Term.con` whose one field boxes that method as a callable value,
/// per Phase 0). Destructuring the dict value via `match` and calling
/// the extracted field proves the whole promotion pipeline is genuinely
/// compilable end-to-end (not just shape-correct at the AST level, per
/// the unit tests in lang/scope.mo) -- `match __Dict_MyAdd_I64 { mk f =>
/// f 2 3 }` must produce 5.
#[test]
def test_promote_instance_defs_compiles_and_runs : IO Bool := do {
    let a_id := Identifier.id "a";
    let b_id := Identifier.id "b";
    let a_var := Term.var 0 (DebugName.named a_id);
    let b_var := Term.var 1 (DebugName.named b_id);
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add"));
    let my_add_body := Term.app (Term.app add_var a_var) b_var;
    let my_add_term := Term.lam (DebugName.named a_id) (Term.type_ 1) (Term.lam (DebugName.named b_id) (Term.type_ 1) my_add_body);
    let my_add_name := ModulePath.mp (List.cons (Identifier.id "add") List.empty);
    let my_add_def := Def.mk my_add_name (Term.type_ 1) my_add_term ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private;

    let a_param := param_many (Identifier.id "A") (Term.type_ 1);
    let add_method := ClassDef.mk (Identifier.id "add") Term.hole (Option.none : Option Term);
    let cls := Class.mk (Identifier.id "MyAdd") [a_param] ([] : List TypeConstraint) [add_method] Visibility.package_private;

    let cls_name := ModulePath.mp (List.cons (Identifier.id "MyAdd") List.empty);
    let i64_arg := Term.var 0 (DebugName.named (Identifier.id "I64"));
    let ins := Instance.mk (Identifier.id "_") cls_name ([] : List TypeConstraint) [i64_arg] Visibility.package_private ([] : List Param) [my_add_def];

    let f_id := Identifier.id "f";
    let f_var := Term.var 0 (DebugName.named f_id);
    let dict_ref := Term.var 0 (DebugName.named (Identifier.id "__Dict_MyAdd_I64"));
    let call_f := Term.app (Term.app f_var (mk_i64 2)) (mk_i64 3);
    let mk_case := MatchCase.mc (Identifier.id "mk") [f_id] call_f Option.none;
    let main_body := Term.lit (Literal.match_ dict_ref [mk_case]);
    let main_def := mk_def "main" main_body;

    let base_decls := [Decl.class_d cls, Decl.instance_d ins, Decl.def_d main_def];
    let promoted_decls := promote_instance_defs base_decls;
    compile_decls_link_run_expect promoted_decls "test_dict_promote" 5
}

/// Runs the full dictionary-passing pipeline in Phase 5's own intended
/// order (see lang/codegen/emit.mo's compile_loaded_modules_to_ir /
/// lang/codegen/test_driver.mo's compile_loaded_modules_to_test_ir,
/// once wired there) -- promotion (Phase 2) must run before dict-param
/// insertion (Phase 3), which must run before call-site resolution
/// (Phase 4), since each phase's output is the next phase's own input
/// (a promoted method's constraints, from Phase 2's threading of
/// Instance.constraints, are exactly what Phase 3 reads next).
#[partial]
def full_dict_pipeline (decl_list : List Decl) : Result String (List Decl) :=
    resolve_class_calls_decls (add_constraint_dict_params_decls (promote_instance_defs decl_list))

/// Runs `full_dict_pipeline` then `compile_decls_link_run_expect` --
/// these are hand-built, deliberately-valid dict-pipeline fixtures, so a
/// `Result.err` here means the fixture itself regressed, not a real
/// "no instance available" case; report it as a failed test rather than
/// silently swallowing it.
#[partial]
def run_full_dict_pipeline (decl_list : List Decl) (basename : String) (expected : I64) : IO Bool :=
    match full_dict_pipeline decl_list {
        Result.err e => do {
            println (basename ++ ": full_dict_pipeline failed to resolve class-method calls: " ++ e);
            return false
        },
        Result.ok dispatched => compile_decls_link_run_expect dispatched basename expected,
    }

/// Phase 4 (D4) end-to-end regression test: a plain concrete class-
/// method call (`MyEq.eq2 2 3`, no wildcard/constrained instance
/// involved) resolves to a real direct call on the promoted method.
#[test]
def test_resolve_class_calls_concrete_d4 : IO Bool := do {
    let a_id := Identifier.id "a";
    let b_id := Identifier.id "b";
    let a_var := Term.var 0 (DebugName.named a_id);
    let b_var := Term.var 1 (DebugName.named b_id);
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add"));
    let eq2_body := Term.app (Term.app add_var a_var) b_var;
    let eq2_term := Term.lam (DebugName.named a_id) (Term.type_ 1) (Term.lam (DebugName.named b_id) (Term.type_ 1) eq2_body);
    let eq2_name := ModulePath.mp (List.cons (Identifier.id "eq2") List.empty);
    let eq2_def := Def.mk eq2_name (Term.type_ 1) eq2_term ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private;

    let a_param := param_many (Identifier.id "A") (Term.type_ 1);
    let eq2_method := ClassDef.mk (Identifier.id "eq2") Term.hole (Option.none : Option Term);
    let cls := Class.mk (Identifier.id "MyEq") [a_param] ([] : List TypeConstraint) [eq2_method] Visibility.package_private;

    let cls_name := ModulePath.mp (List.cons (Identifier.id "MyEq") List.empty);
    let i64_arg := Term.var 0 (DebugName.named (Identifier.id "I64"));
    let ins := Instance.mk (Identifier.id "_") cls_name ([] : List TypeConstraint) [i64_arg] Visibility.package_private ([] : List Param) [eq2_def];

    let call := Term.app (Term.app (Term.var 0 (DebugName.named (Identifier.id "MyEq.eq2"))) (mk_i64 2)) (mk_i64 3);
    let main_def := mk_def "main" call;

    let base_decls := [Decl.class_d cls, Decl.instance_d ins, Decl.def_d main_def];
    run_full_dict_pipeline base_decls "test_d4_concrete" 5
}

/// Phase 4 (D4 with a recursive inner dict arg) end-to-end regression
/// test -- mirrors the real corpus's own `[Add A] HAdd A A A` shape
/// (`instance [Add2 A] Wrapped2 A { def wadd2 := Add2.add2 a b }`)
/// that motivated choosing genuine dictionary-passing over the earlier-
/// rejected eager-monomorphic shortcut: `Wrapped2.wadd2 2 3` must
/// resolve through the wildcard instance's own promoted method, which
/// itself needs `Add2 I64`'s dict spliced in as ITS OWN leading arg to
/// resolve `Add2.add2 a b` inside its own body -- a genuinely two-level
/// resolution, not just one direct lookup.
#[test]
def test_resolve_class_calls_recursive_dict_arg : IO Bool := do {
    let a_id := Identifier.id "a";
    let b_id := Identifier.id "b";
    let a_var := Term.var 0 (DebugName.named a_id);
    let b_var := Term.var 1 (DebugName.named b_id);
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add"));

    // instance Add2 I64 { def add2 := i64_add2 }
    let add2_body := Term.app (Term.app add_var a_var) b_var;
    let add2_term := Term.lam (DebugName.named a_id) (Term.type_ 1) (Term.lam (DebugName.named b_id) (Term.type_ 1) add2_body);
    let add2_name := ModulePath.mp (List.cons (Identifier.id "add2") List.empty);
    let add2_def := Def.mk add2_name (Term.type_ 1) add2_term ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private;

    let a_param := param_many (Identifier.id "A") (Term.type_ 1);
    let add2_method := ClassDef.mk (Identifier.id "add2") Term.hole (Option.none : Option Term);
    let add2_cls := Class.mk (Identifier.id "Add2") [a_param] ([] : List TypeConstraint) [add2_method] Visibility.package_private;

    let add2_cls_name := ModulePath.mp (List.cons (Identifier.id "Add2") List.empty);
    let i64_arg := Term.var 0 (DebugName.named (Identifier.id "I64"));
    let add2_ins := Instance.mk (Identifier.id "_") add2_cls_name ([] : List TypeConstraint) [i64_arg] Visibility.package_private ([] : List Param) [add2_def];

    // instance [Add2 A] Wrapped2 A { def wadd2 (a b : A) : A := Add2.add2 a b }
    let wadd2_body := Term.app (Term.app (Term.var 0 (DebugName.named (Identifier.id "Add2.add2"))) a_var) b_var;
    let wadd2_term := Term.lam (DebugName.named a_id) Term.hole (Term.lam (DebugName.named b_id) Term.hole wadd2_body);
    let wadd2_name := ModulePath.mp (List.cons (Identifier.id "wadd2") List.empty);
    let wadd2_def := Def.mk wadd2_name Term.hole wadd2_term ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private;

    let wadd2_method := ClassDef.mk (Identifier.id "wadd2") Term.hole (Option.none : Option Term);
    let wrapped2_cls := Class.mk (Identifier.id "Wrapped2") [a_param] ([] : List TypeConstraint) [wadd2_method] Visibility.package_private;

    let wrapped2_cls_name := ModulePath.mp (List.cons (Identifier.id "Wrapped2") List.empty);
    let add2_constraint := TypeConstraint.mk add2_cls_name [Identifier.id "A"];
    let a_wildcard_arg := Term.var 0 (DebugName.named (Identifier.id "A"));
    let wrapped2_ins := Instance.mk (Identifier.id "_") wrapped2_cls_name [add2_constraint] [a_wildcard_arg]
        Visibility.package_private ([] : List Param) [wadd2_def];

    let call := Term.app (Term.app (Term.var 0 (DebugName.named (Identifier.id "Wrapped2.wadd2"))) (mk_i64 2)) (mk_i64 3);
    let main_def := mk_def "main" call;

    let base_decls := [
        Decl.class_d add2_cls, Decl.instance_d add2_ins,
        Decl.class_d wrapped2_cls, Decl.instance_d wrapped2_ins,
        Decl.def_d main_def,
    ];
    run_full_dict_pipeline base_decls "test_d4_recursive" 5
}

/// Phase 4 capstone (D5, genuine polymorphism): a `[MyShow3 A]`-
/// constrained function is called at TWO different concrete types in
/// the SAME compiled program -- one compiled body, genuinely dictionary-
/// parameterized (not resolved-per-call-site at compile time), proving
/// the actual payoff of choosing dictionary-passing over the earlier-
/// rejected eager-monomorphic shortcut. `show_twice 5` (I64 instance,
/// `x + 100` doubled = 210) plus `show_twice mytrue` (MyBool instance,
/// a fixed 200 doubled = 400) must total 610.
#[test]
def test_resolve_class_calls_genuine_polymorphism : IO Bool := do {
    let x_id := Identifier.id "x";
    let x_var := Term.var 0 (DebugName.named x_id);
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add"));

    // type MyBool { mytrue, myfalse }
    let mytrue_ctor := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "mytrue") List.empty)) [] (Term.type_ 1);
    let myfalse_ctor := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "myfalse") List.empty)) [] (Term.type_ 1);
    let mybool_ind := Inductive.mk (ModulePath.mp (List.cons (Identifier.id "MyBool") List.empty)) [] (Term.type_ 1)
        [mytrue_ctor, myfalse_ctor] ([] : List Attribute) Visibility.package_private;

    // instance MyShow3 I64 { def show3 (x : I64) : I64 := x + 100 }
    let show3_i64_body := Term.app (Term.app add_var x_var) (mk_i64 100);
    let show3_i64_term := Term.lam (DebugName.named x_id) Term.hole show3_i64_body;
    let show3_i64_name := ModulePath.mp (List.cons (Identifier.id "show3") List.empty);
    let show3_i64_def := Def.mk show3_i64_name Term.hole show3_i64_term ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private;

    let a_param := param_many (Identifier.id "A") (Term.type_ 1);
    let show3_method := ClassDef.mk (Identifier.id "show3") Term.hole (Option.none : Option Term);
    let myshow3_cls := Class.mk (Identifier.id "MyShow3") [a_param] ([] : List TypeConstraint) [show3_method] Visibility.package_private;

    let myshow3_cls_name := ModulePath.mp (List.cons (Identifier.id "MyShow3") List.empty);
    let i64_arg := Term.var 0 (DebugName.named (Identifier.id "I64"));
    let show3_i64_ins := Instance.mk (Identifier.id "_") myshow3_cls_name ([] : List TypeConstraint) [i64_arg]
        Visibility.package_private ([] : List Param) [show3_i64_def];

    // instance MyShow3 MyBool { def show3 (x : MyBool) : I64 := 200 }
    let show3_bool_term := Term.lam (DebugName.named x_id) Term.hole (mk_i64 200);
    let show3_bool_def := Def.mk show3_i64_name Term.hole show3_bool_term ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private;
    let mybool_arg := Term.var 0 (DebugName.named (Identifier.id "MyBool"));
    let show3_bool_ins := Instance.mk (Identifier.id "_") myshow3_cls_name ([] : List TypeConstraint) [mybool_arg]
        Visibility.package_private ([] : List Param) [show3_bool_def];

    // def show_twice [MyShow3 A] (x : A) : I64 := MyShow3.show3 x + MyShow3.show3 x
    let show3_call := Term.app (Term.var 0 (DebugName.named (Identifier.id "MyShow3.show3"))) x_var;
    let show_twice_body := Term.app (Term.app add_var show3_call) show3_call;
    let show_twice_term := Term.lam (DebugName.named x_id) Term.hole show_twice_body;
    let show_twice_name := ModulePath.mp (List.cons (Identifier.id "show_twice") List.empty);
    let myshow3_constraint := TypeConstraint.mk myshow3_cls_name [Identifier.id "A"];
    let show_twice_def := Def.mk show_twice_name Term.hole show_twice_term [myshow3_constraint] ([] : List Attribute) Visibility.package_private;

    // main := show_twice 5 + show_twice mytrue
    let mytrue_val := Term.con (Con.mk (Identifier.id "mytrue") (ModulePath.mp (List.cons (Identifier.id "MyBool") List.empty)) 0 []);
    let call_i64 := Term.app (Term.var 0 (DebugName.named (Identifier.id "show_twice"))) (mk_i64 5);
    let call_bool := Term.app (Term.var 0 (DebugName.named (Identifier.id "show_twice"))) mytrue_val;
    let main_body := Term.app (Term.app add_var call_i64) call_bool;
    let main_def := mk_def "main" main_body;

    let base_decls := [
        Decl.inductive_d mybool_ind,
        Decl.class_d myshow3_cls, Decl.instance_d show3_i64_ins, Decl.instance_d show3_bool_ins,
        Decl.def_d show_twice_def, Decl.def_d main_def,
    ];
    // 98, not 610 -- process exit codes are POSIX 8-bit values (0-255);
    // 610 mod 256 = 98 is the real observable exit code even though
    // the underlying I64 computation inside the compiled program
    // itself is genuinely 610 throughout (confirmed separately by
    // temporarily printing the raw I64 before truncation).
    run_full_dict_pipeline base_decls "test_d5_polymorphism" 98
}
