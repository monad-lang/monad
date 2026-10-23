/// Regression test for `class_method_ref` requiring a class to DECLARE the
/// method its qualifier names (`lang/src/scope.mo`, mirrored in
/// `lang/src/typecheck/infer.mo`'s `ref_names_class_method`).
///
/// The filed repro was `Map.get`: `class Map` declares `empty`/`insert`/
/// `lookup`/`delete` and no `get`, so `Map.get` named a method no class
/// declares -- but the checker accepted it, because the loose test only
/// asked whether the QUALIFIER named a class and then looked the bare
/// suffix up in every class. `get` exists, in `MonadState`. Three measured
/// before-states, all silent:
///
///   * `monad check` reported 0 errors (the checker never looked);
///   * `monad compile` failed with `call to undefined symbol(s):
///     std.map::Map_BTreeMap_get` -- a mangled name nothing emits, because
///     emission is driven by the class's DECLARED method list, and the
///     error names a symbol rather than the line;
///   * with a same-named method on another class that HAS a matching
///     instance, it compiled and ran, dispatching to the OTHER class's
///     method.
///
/// The fixture below is that third shape, self-contained so the row does
/// not depend on which motes a working directory can resolve: `Bag` does
/// not declare `zzz`, `Other` does, and both have an `I64` instance. The
/// call MUST be reachable from `main` -- elaboration and the codegen
/// validator both work on the reachable decls only, so an unreferenced
/// `use_it` would be filtered out and the row would pass for the wrong
/// reason.
///
/// The message is asserted to name the call AS WRITTEN (`Bag.zzz`) and not
/// the other class's promoted def, which is what separates "reported to
/// the user" from "silently rewired to a working symbol".
use std::test {Test.write_fixture}
use std::process {exec_cmd, process_id}
use lang::module {load_file_modules}
use lang::codegen::emit {compile_loaded_modules_to_ir}

#[test]
def test_undeclared_class_method_fails_the_compile_clearly : IO Bool := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/undeclared_class_method.mo";
    let source := r#"class Bag A {
	def put (a : A) : A
}

pub instance Bag I64 {
	def put (a : I64) : I64 := a
}

class Other A {
	def zzz (a : A) : A
}

pub instance Other I64 {
	def zzz (a : I64) : I64 := a
}

def use_it (x : I64) : I64 := Bag.zzz x

def main (args : List String) : IO I64 := do {
    return (use_it 1)
}
"#;
    exec_cmd "mkdir" ["-p", output_dir];
    let _w <- Test.write_fixture (Path.path src_path) source;

    let loaded_result <- load_file_modules src_path false;
    match loaded_result {
        Result.err e => do {
            IO.println ("test_undeclared_class_method_fails_the_compile_clearly: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err msg => do {
                    let names_the_call := String.contains msg "Bag.zzz";
                    let not_rewired := Bool.not (String.contains msg "Other_I64_zzz");
                    if names_the_call && not_rewired then return true
                    else do {
                        IO.println ("test_undeclared_class_method_fails_the_compile_clearly: message names the wrong thing: " ++ msg);
                        return false
                    }
                },
                Result.ok _ => do {
                    IO.println "test_undeclared_class_method_fails_the_compile_clearly: expected Result.err (Bag declares no `zzz`), got Result.ok -- the call was silently rewired to another class's method";
                    return false
                },
            }
        },
    }
}
