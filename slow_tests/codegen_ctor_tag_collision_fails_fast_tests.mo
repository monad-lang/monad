/// Regression tests for constructor-tag disambiguation by arity
/// (`build_constructor_tag_map`/`constructor_tag_at`,
/// lang/codegen/emit.mo).
///
/// Codegen used to key a constructor's runtime tag AND its recorded
/// field count by the constructor's BARE name only (match dispatch's
/// `MatchCase.mc` carries just the bare Identifier). Every
/// `type X { mk ... }` claimed the same `"mk"` key: last-writer-wins,
/// so in the v29 self-compiled binary's own IR 283 constructors shared
/// one tag at seven different arities, a value-position `mk` reference
/// sized its allocation from the last claimant's arity, and
/// `monad_get_field` read a neighbouring object -- a raw unboxed `1`
/// where a `List` spine pointer belonged, SIGSEGV in `List_filter_map`
/// on the first module load. An interim commit (21b215b) failed such
/// compiles loudly; this keying (bare name + declared field count, a
/// count every alloc/dispatch site already knows: the case's binder
/// list, the application's arg list, the wrapper's param list) makes
/// differing-arity colliders structurally distinguishable, so those
/// programs now compile AND run correctly instead of being rejected.
///
/// These compile, link and EXECUTE (via `compile_source_run_expect`)
/// rather than inspecting IR text -- only running a compiled binary
/// catches a wrong-layout read, which is how the v29 crash stayed
/// invisible through `check` and `llc` both.
use io {IO}
open IO {println}
use lang.codegen.test.e2e_harness {compile_source_run_expect}
use std.process {process_id, exec_cmd}
use lang.module {LoadedModules, load_file_modules}
use lang.codegen.emit {compile_loaded_modules_to_ir}
use lang.codegen.ir {emit_module}


/// Two types both declaring `mk`, at arities 1 and 3, both constructed
/// and matched from `main`. Must compile AND run with every field
/// landing where it was written -- exit 7. Before the arity-keyed tags
/// this exact shape was rejected by the interim fail-fast gate
/// (commit 21b215b), and before THAT compiled to a binary whose
/// `Slim`/`Wide` field reads crossed the two layouts.
#[test]
def test_ctor_differing_arity_collision_runs_correctly : IO Bool :=
    let source := r#"use io {IO}
type Slim { mk (only : I64) }
type Wide { mk (a : I64) (b : I64) (c : I64) }
def main (args : List String) : IO I64 := do {
    let s := Slim.mk 1;
    let w := Wide.mk 10 20 30;
    match s { Slim.mk x => match w { Wide.mk p q r => return (if x + p + q + r == 61 then 7 else 1) } }
}
"# in
    compile_source_run_expect source "ctor_differing_arity" 7

/// The benign shape the differing-arity fix must NOT break: same bare
/// key, SAME arity -- layout-uniform, so alloc and match sites agree by
/// construction (the nested Inner/Outer pattern
/// `codegen_struct_literal_ctor_arg_tests.mo` also relies on). Exit 7
/// means both levels round-tripped through construction, match, and
/// field reads.
#[test]
def test_ctor_same_arity_collision_still_runs : IO Bool :=
    let source := r#"use io {IO}
type Inner { mk (path : String) (rest : List String) }
type Outer { mk (result : Inner) (cache : I64) }
def main (args : List String) : IO I64 := do {
    let i := Inner.mk "x" [];
    let o := Outer.mk i 7;
    match o { Outer.mk r c => match r { Inner.mk p _ => return (if String.beq p "x" then c else 1) } }
}
"# in
    compile_source_run_expect source "ctor_same_arity" 7

/// The value-position path -- the exact v29 crash mechanism. `Box.mk`
/// is referenced as a FIRST-CLASS VALUE (`List.map Box.mk nums`), which
/// boxes a closure shim that allocates on application; the shim's tag
/// and arity come from the arity-unknown lookup, resolved through the
/// owner-qualified alias ("Box.mk"). The same program also declares
/// `mk` at two OTHER arities (2 and 3), so the bare name is maximally
/// ambiguous -- with bare-name keying the shim sized its allocations
/// from whichever type claimed `"mk"` last, and `sum_boxes`' field
/// reads walked off into neighbouring memory. Exit 7 means every
/// shim-constructed Box matched its own case and read back its own
/// field.
#[test]
def test_ctor_value_position_shim_with_ambiguous_bare_name : IO Bool :=
    let source := r#"use io {IO}
type Box { mk (v : I64) }
type Slim { mk (a : I64) (b : I64) }
type Wide { mk (x : I64) (y : I64) (z : I64) }
def sum_boxes (xs : List Box) (acc : I64) : I64 :=
    match xs {
        List.empty => acc,
        List.cons b rest => match b { Box.mk v => sum_boxes rest (acc + v) },
    }
def main (args : List String) : IO I64 := do {
    let nums : List I64 := List.cons 1 (List.cons 2 (List.cons 3 List.empty));
    let boxes : List Box := List.map Box.mk nums;
    let s := sum_boxes boxes 0;
    let sl := Slim.mk 4 5;
    let w := Wide.mk 6 7 8;
    match sl { Slim.mk p q => match w { Wide.mk x y z => return (if s + p + q + x + y + z == 36 then 7 else 1) } }
}
"# in
    compile_source_run_expect source "ctor_value_position_shim" 7

/// A user constructor that shares a BUILTIN's bare name at a different
/// arity -- `CompileResult.ok` (6 fields) against builtin `Result.ok`
/// (1 field) is the real instance, in lang/codegen/emit.mo itself.
///
/// The builtin tag tables are consulted before the arity-keyed map, and
/// `Con.mk`'s own `name` field is the constructor's BARE name, so a user
/// `Wide.ok` reached `constructor_tag` as plain "ok" and matched the
/// builtin outright. The ALLOCATION site then got builtin tag 10 while
/// the constructor's own wrapper function got its real composite tag --
/// two incompatible layouts for one constructor. That cost a v30 ladder
/// rung: a `CompileResult` allocated with 6 fields and read back as a
/// 1-field `Result.ok` left a raw unboxed `1` where an `Identifier`'s
/// `char*` belonged, SIGSEGV in `__strcmp_avx2` via
/// `Similar_Identifier_similar` <- `term_matches_carrier`, ~45s into
/// `check lang/main.mo`.
///
/// Asserted on the IR rather than an exit code, deliberately: in a
/// SMALL program every site picks the same wrong tag consistently, so
/// the binary still returns the right answer and an exit-code test
/// passes either way (verified -- it stayed green with the fix
/// reverted). What actually distinguishes the two states is that the
/// unguarded compiler emits BOTH tag 10 and the real tag for the same
/// 3-field constructor; the guarded one emits only the real tag. The
/// match arm is written BARE (`ok x y z`), which is what a real `match`
/// supplies and what makes the bare-name tiers fire.
#[test]
def test_user_ctor_shadowing_builtin_name_keeps_own_layout : IO Bool := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/ctor_builtin_shadow.mo";
    let source := r#"use io {IO}
type Wide { ok (a : I64) (b : I64) (c : I64) }
def build : Wide := Wide.ok 1 2 3
def unwrap (w : Wide) : I64 :=
    match w { ok x y z => x + y + z }
def main (args : List String) : IO I64 :=
    return (if unwrap build == 6 then 7 else 1)
"#;
    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file (Path.path src_path) source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path;
    match loaded_result {
        Result.err e => do {
            println ("test_user_ctor_shadowing_builtin_name: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            let _ <- exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err e => do {
                    println ("test_user_ctor_shadowing_builtin_name: compile failed: " ++ e);
                    return false
                },
                Result.ok mod_ => do {
                    let ir := emit_module mod_;
                    // Builtin `ok`'s tag is 10 and its real arity is 1,
                    // so a 3-field allocation carrying that tag is the
                    // bug and nothing else.
                    if String.contains ir "alloc_constructor(i64 10, i64 3)"
                    then do {
                        println "test_user_ctor_shadowing_builtin_name: 3-field ctor borrowed builtin `ok`'s tag 10";
                        return false
                    }
                    else return true
                },
            }
        },
    }
}