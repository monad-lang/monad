/// Regression tests for `tag_keyword` (`lang/parser/combinators.mo`):
/// the parser's own `return`-recognition sites (`do_stmt_return`,
/// `return_shorthand_parser`) used a bare `is_prefix`-based `tag "return"`
/// check with NO word-boundary check, so an ORDINARY identifier that
/// merely starts with the substring "return" (e.g. a def or local named
/// `return_foo`) was silently mis-parsed as the keyword `return` applied
/// to whatever remained after stripping the literal 6 characters --
/// `return_foo 41` parsed as `return (_foo 41)`.
///
/// This compiled and linked cleanly (both `_foo` -- an unrelated,
/// nonexistent local/def reference -- and the spurious `Monad.pure` wrap
/// are syntactically valid AST shapes) and only surfaced as a downstream
/// "unknown variable" or "undefined symbol" failure far from the actual
/// bug -- confirmed via `compile`'s own explicit typecheck gate
/// (`unknown variable '_foo'`) and, independently, via
/// `bootstrap compile lang/main.mo monad`'s self-compile hitting the
/// identical class of bug on `lang/scope.mo`'s own real
/// `return_type_after_n_args` (`llc: use of undefined value
/// '@Monad_pure'`, `lang/scope.mo:2189`'s call to it compiled to a call
/// to undefined `@_type_after_n_args` plus a spurious `@Monad_pure`
/// wrap) -- see `implementations/2026-08-29-return-prefixed-def-name-
/// mangled-with-spurious-monad-pure.md`.
///
/// Fixed by adding `tag_keyword` (checks a genuine word boundary --
/// end of input or a non-identifier character -- after the keyword tag
/// succeeds) and using it at both `return`-recognition call sites instead
/// of the bare `tag`.
use io {IO}
use process {exec_cmd}
use lang.types {LoadedModules}
use lang.module {load_file_modules}
use lang.codegen.ir {emit_module}
use lang.codegen.emit {compile_loaded_modules_to_ir}

#[partial]
def compile_source_run_expect (source : String) (basename : String) (expected : I64) : IO Bool := do {
    let output_dir := "/tmp/monad_e2e";
    let src_path := output_dir ++ "/" ++ basename ++ ".mo";
    let ir_path := output_dir ++ "/" ++ basename ++ ".ll";
    let obj_path := output_dir ++ "/" ++ basename ++ ".o";
    let runtime_obj := output_dir ++ "/" ++ basename ++ "_runtime.o";
    let output_path := output_dir ++ "/" ++ basename;

    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file src_path source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path;
    match loaded_result {
        Result.err e => do {
            IO.println (basename ++ ": failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_ <- compile_loaded_modules_to_ir loaded false;
            let ir_text := emit_module mod_;
            IO.write_file ir_path ir_text;

            let llc_result <- exec_cmd "llc" ["-filetype=obj", ir_path, "-o", obj_path];
            if not (llc_result == 0) then do {
                IO.println (basename ++ ": llc failed");
                return false
            } else do {
                let rt_result <- exec_cmd "clang" ["-c", "lang/codegen/runtime.c", "-o", runtime_obj];
                if not (rt_result == 0) then do {
                    IO.println (basename ++ ": compiling runtime failed");
                    return false
                } else do {
                    let link_args := [obj_path, runtime_obj];
                    let link_result <- exec_cmd "clang" (List.append link_args ["-o", output_path]);
                    if not (link_result == 0) then do {
                        IO.println (basename ++ ": clang linker failed");
                        return false
                    } else do {
                        let exec_result <- exec_cmd output_path [];
                        let _ <- exec_cmd "rm" ["-f", src_path, ir_path, obj_path, runtime_obj, output_path];
                        IO.println (basename ++ ": expected " ++ I64.to_string expected ++ ", got " ++ I64.to_string exec_result);
                        return (exec_result == expected)
                    }
                }
            }
        },
    }
}

/// An ordinary, non-monadic def whose name starts with `return_`, called
/// as a plain `let`-bound expression -- the exact shape that used to
/// mis-parse as `return (_foo 41)`.
#[test]
def test_return_prefixed_def_name_ordinary_call : IO Bool :=
    let source := r#"def return_foo (x : I64) : I64 := x

def main (args : List String) : IO I64 := do {
    let y := return_foo 41;
    return y
}
"# in
    compile_source_run_expect source "test_return_prefixed_def_name_ordinary_call" 41

/// Same shape as a bare do-block STATEMENT (not `let`-bound) -- exercises
/// `do_stmt_return`'s own `tag_keyword` call, not just
/// `return_shorthand_parser`'s. `return_marker` must be `IO`-typed to be
/// a valid bare statement (mirrors `lang/main.mo`'s own established
/// `IO.write_file path content;` bare-statement idiom).
#[test]
def test_return_prefixed_def_name_bare_statement : IO Bool :=
    let source := r#"use io {IO}
def return_marker (x : I64) : IO Unit := IO.println (I64.to_string x)

def main (args : List String) : IO I64 := do {
    return_marker 0;
    return 7
}
"# in
    compile_source_run_expect source "test_return_prefixed_def_name_bare_statement" 7
