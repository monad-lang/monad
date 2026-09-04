/// Regression tests for the constructor-tag collision fail-fast gate
/// (`validate_no_ctor_tag_collisions`, lang/codegen/emit.mo).
///
/// Codegen keys a constructor's runtime tag AND its recorded field
/// count by the constructor's BARE name (`assign_constructor_tags`/
/// `build_constructor_arity_map`) because match dispatch can only ever
/// supply the bare name. Every `type X { mk ... }` therefore claims the
/// same `"mk"` key: last-writer-wins, so all such constructors share one
/// tag while their values have different layouts, and any
/// `monad_get_field`/match-arm field read on one can read another's
/// memory. This class cost the v29 rung-3 ladder rung (283 constructors
/// sharing one tag at seven different arities in the self-compiled
/// binary's own IR; a raw unboxed `1` ended up where a `List` spine
/// pointer belonged, SIGSEGV in `List_filter_map` on the first module
/// load) -- silent, structural, `llc`-verified clean.
///
/// The gate rejects the memory-unsafe case (two owners of one key at
/// DIFFERING arities) loudly at compile time instead. Same-arity
/// collisions stay tolerated deliberately: alloc and match sites read
/// the same map entry, so a uniform-layout key is consistent by
/// construction (and the nested Inner/Outer regression shape in
/// `codegen_struct_literal_ctor_arg_tests.mo` relies on it).
use io {IO}
open IO {println}
use std.process {process_id, exec_cmd}
use lang.module {LoadedModules, load_file_modules}
use lang.codegen.emit {compile_loaded_modules_to_ir}


/// Two one-file types both declaring `mk`, at arities 1 and 3, both
/// constructed and matched from `main` (reachable, so the gate sees
/// them). Must be REJECTED with a message naming the bare key and both
/// owning types -- not compiled into a binary whose field reads cross
/// the two layouts.
///
/// Red-checked: before the gate existed this compile SUCCEEDED (and
/// the resulting binary read `Wide`'s fields at `Slim`'s offsets).
#[test]
def test_ctor_tag_collision_fails_fast : IO Bool := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/ctor_tag_collision.mo";
    let source := r#"use io {IO}
type Slim { mk (only : I64) }
type Wide { mk (a : I64) (b : I64) (c : I64) }
def main (args : List String) : IO I64 := do {
    let s := Slim.mk 1;
    let w := Wide.mk 1 2 3;
    match s { Slim.mk x => match w { Wide.mk p _ _ => return (x + p) } }
}
"#;
    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file (Path.path src_path) source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path;
    match loaded_result {
        Result.err e => do {
            println ("test_ctor_tag_collision_fails_fast: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            let _ <- exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err msg =>
                    if String.contains msg "constructor-tag key `mk`" && String.contains msg "Slim" && String.contains msg "Wide"
                    then return true
                    else do {
                        println ("test_ctor_tag_collision_fails_fast: error message missing key / owner names: " ++ msg);
                        return false
                    },
                Result.ok _ => do {
                    println "test_ctor_tag_collision_fails_fast: compile SUCCEEDED, expected a fail-fast error";
                    return false
                },
            }
        },
    }
}

/// The deliberate tolerance: same key, SAME arity -- the map entry is
/// layout-uniform, so alloc and match sites agree by construction and
/// the compile must keep working. Pins the gate's precision so it can
/// never regress into rejecting the benign nested-record shapes the
/// corpus (and `codegen_struct_literal_ctor_arg_tests.mo`) relies on.
#[test]
def test_ctor_tag_same_arity_still_compiles : IO Bool := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/ctor_tag_same_arity.mo";
    let source := r#"use io {IO}
type Inner { mk (path : String) (rest : List String) }
type Outer { mk (result : Inner) (cache : I64) }
def main (args : List String) : IO I64 := do {
    let i := Inner.mk "x" [];
    let o := Outer.mk i 7;
    match o { Outer.mk r c => match r { Inner.mk p _ => return (if String.beq p "x" then c else 1) } }
}
"#;
    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file (Path.path src_path) source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path;
    match loaded_result {
        Result.err e => do {
            println ("test_ctor_tag_same_arity_still_compiles: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            let _ <- exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err msg => do {
                    println ("test_ctor_tag_same_arity_still_compiles: compile rejected a same-arity key (gate over-firing): " ++ msg);
                    return false
                },
                Result.ok _ => return true,
            }
        },
    }
}