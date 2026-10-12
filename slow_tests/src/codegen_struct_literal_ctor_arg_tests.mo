/// Regression test for the struct-literal-in-constructor-argument
/// miscompile (AGENTS.md's "known pitfall when applying rule 1").
///
/// A bare struct literal written directly as a constructor ARGUMENT --
/// `Option.some { field := val, ... }` -- has no concrete expected type
/// at that point, and the checker does not reliably desugar it to a
/// real constructor there. The REFERENCE interpreter tolerates it. This
/// backend did not: it compiled to a value whose fields were then read
/// at the wrong offsets.
///
/// That cost a full ladder rung. A self-compiled compiler binary
/// SIGSEGV'd in `__strlen_avx2`, reached via `String_length` <-
/// `string_find_last_slash` <- `extract_directory` <-
/// `load_file_modules` -- i.e. on the FIRST module load, so every
/// `check` and every `compile` the compiler ran on itself. The culprit
/// was one `Option.some { ... }` in `load_module_with_info`
/// (lang/module.mo); the emitted IR read fields 0/1/2 straight off the
/// `Option` payload, and the closure env slot holding `file_path` came
/// back as 0x31 -- a small integer that `String.length` then
/// dereferenced as a `char*`.
///
/// `check` stays completely silent about this, and so does `llc` --
/// only RUNNING a compiled binary finds it, which is why this test
/// compiles, links and executes rather than inspecting IR text.
use lang::codegen::test::e2e_harness {compile_source_run_expect}

/// The safe form, and the one every site in `lang/` now uses: bind the
/// literal to a local with an explicit type annotation first, then pass
/// the local. A multi-field struct reached through an `Option` -- the
/// exact shape of `load_module_with_info`'s `ModuleInfo` -- with a
/// String field read back after the round trip.
///
/// Exit code 7 means the String field survived; a crash (139) or 1 means
/// it was read at the wrong offset.
#[test]
def test_struct_literal_via_annotated_local_round_trips : IO Bool :=
    let source := r#"struct Info { tag_ : I64, name : String, count : I64 }
def build : IO (Option Info) :=
    let info : Info := { tag_ := 1, name := "examples/hello.mo", count := 3 } in
    return (Option.some info)
def main (args : List String) : IO I64 := do {
    let m <- build;
    match m {
        Option.some i =>
            match i {
                Info.mk _t nm _c =>
                    return (if String.length nm == 17 && String.beq nm "examples/hello.mo" then 7 else 1)
            },
        Option.none => return 1,
    }
}
"# in
    compile_source_run_expect source "struct_lit_annotated" 7

/// The same shape one level deeper: a struct built inside a `return
/// match ...`, which is precisely how `load_module_with_info` produced
/// its `ModuleInfo`, and with the String field consumed by a native
/// (`String.length`) rather than just compared -- that native call is
/// what actually dereferenced the bad pointer and crashed.
#[test]
def test_struct_from_return_match_field_reaches_native : IO Bool :=
    let source := r#"struct Rec { first : String, second : String }
def pick (which : Option I64) : IO (Option Rec) := do {
    let chosen : String := match which { Option.some _ => "chosen/path.mo", Option.none => "fallback.mo" };
    return match which {
        Option.some _ =>
            let r : Rec := { first := chosen, second := "tail" } in
            Option.some r,
        Option.none => Option.none
    }
}
def main (args : List String) : IO I64 := do {
    let m <- pick (Option.some 1);
    match m {
        Option.some r =>
            match r {
                Rec.mk f s => do {
                    let lens := String.length f + String.length s;
                    return (if lens == 18 && String.beq f "chosen/path.mo" then 7 else 1)
                }
            },
        Option.none => return 1,
    }
}
"# in
    compile_source_run_expect source "struct_lit_return_match" 7

/// The variant that cost the SECOND ladder rung, in its FIXED form:
/// the same nested `FileCheckAndCache`/`FileCheckResult` shape
/// `check_file_cached` (lang/module.mo) builds, with both levels bound
/// to annotated locals before `return` sees them.
///
/// Written bare -- `return { result := { path := fp, diagnostics := ds
/// }, cache := 7 }` -- this compiled to a void placeholder: the
/// self-compiled compiler printed `FAIL   (0 error(s))` (empty path, and
/// a `diagnostics` value that answered "cons" to one match while
/// `List.length` read it as empty), then `print_diagnostics` recursed on
/// the garbage tail until the 16MB stack was gone. `compile`/`check`
/// only typecheck the TARGET file, so a dependency module's literal
/// never reached `type_check_struct_lit` at all.
/// This one pins the annotated form; the bare form is the last test here.
///
/// Exit code 7 means both levels round-tripped.
#[test]
def test_nested_struct_literals_via_annotated_locals_round_trip : IO Bool :=
    let source := r#"struct Inner { path : String, diagnostics : List String }
struct Outer { result : Inner, cache : I64 }
def make (fp : String) (ds : List String) : IO Outer := do {
    let inner : Inner := { path := fp, diagnostics := ds };
    let outer : Outer := { result := inner, cache := 7 };
    return outer
}
def main (args : List String) : IO I64 := do {
    let o <- make "examples/hello.mo" [];
    match o {
        Outer.mk r c =>
            match r {
                Inner.mk p ds =>
                    match ds {
                        List.empty => return (if String.beq p "examples/hello.mo" then c else 1),
                        List.cons _ _ => return 1,
                    }
            }
    }
}
"# in
    compile_source_run_expect source "struct_lit_annotated_nested" 7

/// The BARE form of the nested literal: the checker elaborates it to real
/// constructors from the expected type (`IO Outer`, then `Outer.result`), so it
/// no longer needs the annotated locals above. `validate_no_undesugared_struct_lits`
/// stays as the backstop for a literal the checker could not resolve.
///
/// Exit code 7 means both levels round-tripped.
#[test]
def test_bare_nested_struct_literal_round_trips : IO Bool :=
    let source := r#"struct Inner { path : String, diagnostics : List String }
struct Outer { result : Inner, cache : I64 }
def make (fp : String) (ds : List String) : IO Outer := do {
    return { result := { path := fp, diagnostics := ds }, cache := 7 }
}
def main (args : List String) : IO I64 := do {
    let o <- make "examples/hello.mo" [];
    match o {
        Outer.mk r c =>
            match r {
                Inner.mk p ds =>
                    match ds {
                        List.empty => return (if String.beq p "examples/hello.mo" then c else 1),
                        List.cons _ _ => return 1,
                    }
            }
    }
}
"# in
    compile_source_run_expect source "struct_lit_bare_nested" 7
