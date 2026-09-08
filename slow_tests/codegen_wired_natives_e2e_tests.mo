/// End-to-end tests for the natives wired in the bootstrap-ladder pass:
/// the GENERATED ones (`lang/codegen/runtime.mo` -- LLVM IR built in
/// Monad itself) and the C-shaped ones (`lang/codegen/runtime.c`).
///
/// Each compiles real `.mo` source through the same pipeline
/// `lang/main.mo`'s own `compile_file_codegen` uses, links it against
/// the real runtime, RUNS the binary, and asserts its exit code --
/// following `codegen_string_repr_tests.mo`'s
/// `compile_source_run_expect` convention (reused verbatim).
///
/// Running the binary is the whole point: every bug in this family was
/// invisible to `llc`'s verifier. `String_to_list` silently compiling to
/// a "return Unit" stub produced structurally valid IR and a binary that
/// SIGSEGV'd inside `List_reverse_append` the moment `String.reverse`
/// walked the Unit object as if it were a cons cell -- see
/// `validate_no_unwired_natives`'s own doc comment for that story.
/// `String.reverse` is therefore deliberately exercised below.
use io {IO}
use std.process {process_id}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// The generated `monad_string_starts_with` byte loop. A too-long
/// prefix must fall out through the byte comparison against the NUL
/// terminator, not a bounds check -- hence the "hello!" case.
#[test]
def test_generated_string_starts_with : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let yes := String.starts_with "he" "hello";
    let no := String.starts_with "xy" "hello";
    let too_long := String.starts_with "hello!" "hello";
    let empty_prefix := String.starts_with "" "hello";
    return (if yes && not no && not too_long && empty_prefix then 7 else 1)
}
"# in
    compile_source_run_expect source "gen_starts_with" 7

/// `String.reverse` -- the exact path that SIGSEGV'd in v25. Routes
/// through the generated `string_to_list`, `List.reverse`, and the C
/// `string_from_list`, so it covers the cons-chain marshaling across
/// the generated/C boundary in both directions.
#[test]
def test_generated_to_list_reverse_round_trip : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let there_and_back := String.beq (String.reverse (String.reverse "bootstrap")) "bootstrap";
    let reversed := String.beq (String.reverse "abc") "cba";
    let empty_ok := String.beq (String.reverse "") "";
    return (if there_and_back && reversed && empty_ok then 7 else 1)
}
"# in
    compile_source_run_expect source "gen_reverse_round_trip" 7

/// `String.ends_with` builds directly on reverse + starts_with, and is
/// what `module_name_from_path` (lang/module.mo) calls on EVERY module
/// load -- the first thing a self-compiled compiler binary executes.
#[test]
def test_generated_ends_with : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let yes := String.ends_with "lang/main.mo" ".mo";
    let no := String.ends_with "lang/main.rs" ".mo";
    return (if yes && not no then 7 else 1)
}
"# in
    compile_source_run_expect source "gen_ends_with" 7

/// The generated `monad_string_get`: `Option U8` tags (none 3, some 4)
/// through `alloc_constructor`, plus both out-of-bounds directions.
#[test]
def test_generated_string_get_option : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let at_1 := match String.get "hello" 1 { Option.some b => U8.beq b 101u8, Option.none => false };
    let past_end := match String.get "hello" 99 { Option.some _ => false, Option.none => true };
    let negative := match String.get "hello" (0 - 1) { Option.some _ => false, Option.none => true };
    return (if at_1 && past_end && negative then 7 else 1)
}
"# in
    compile_source_run_expect source "gen_string_get" 7

/// The generated unsigned ops, including the zero-divisor guard both
/// `u8_div` and `u64_mod` carry (the reference returns 0 rather than
/// trapping). `U64.mod` backs `std/map.mo`'s own bucket arithmetic, so
/// the compiler's every HashMap depends on it.
#[test]
def test_generated_unsigned_ops : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let m := U64.beq (U64.mod 17u64 5u64) 2u64;
    let m0 := U64.beq (U64.mod 17u64 0u64) 0u64;
    let d := U8.beq (U8.div 17u8 5u8) 3u8;
    let d0 := U8.beq (U8.div 17u8 0u8) 0u8;
    let cmp := U8.lt 3u8 7u8 && U8.gt 7u8 3u8;
    return (if m && m0 && d && d0 && cmp then 7 else 1)
}
"# in
    compile_source_run_expect source "gen_unsigned_ops" 7

/// The C `monad_string_to_lowercase` and `monad_u64_to_string`. The
/// unsigned formatting cannot share `monad_i64_to_string`: a U64 near
/// the top of its range is a negative i64 in this backend's uniform
/// representation.
#[test]
def test_c_lowercase_and_unsigned_to_string : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let lower := String.beq (String.to_lowercase "MiXeD Case") "mixed case";
    let u := String.beq (U64.to_string 42u64) "42";
    let b := String.beq (U8.to_string 255u8) "255";
    return (if lower && u && b then 7 else 1)
}
"# in
    compile_source_run_expect source "c_lowercase_to_string" 7

/// The C `monad_exec_cmd` -- THE load-bearing native for the bootstrap
/// ladder (`lang/codegen/link.mo` invokes `llc`/`clang` through it, so
/// a self-compiled compiler cannot run its own `compile` command
/// without it). Asserts real exit-code passthrough from a real child
/// process, including a non-zero code and a nonexistent binary.
#[test]
def test_c_exec_cmd_exit_codes : IO Bool :=
    let source := r#"use std.process {exec_cmd}
def main (args : List String) : IO I64 := do {
    let ok <- exec_cmd "true" [];
    let bad <- exec_cmd "false" [];
    let seven <- exec_cmd "sh" ["-c", "exit 7"];
    let missing <- exec_cmd "definitely_no_such_binary_xyz" [];
    return (if ok == 0 && bad == 1 && seven == 7 && missing == 127 then 7 else 1)
}
"# in
    compile_source_run_expect source "c_exec_cmd" 7

/// The C `monad_list_dir`: bare names, one level, SORTED. The sort is
/// load-bearing rather than cosmetic -- readdir order is
/// filesystem-dependent, and the reference sorts, so an unsorted
/// implementation would make a compiled binary and the interpreter
/// disagree on any directory walk.
#[test]
def test_c_list_dir_sorted : IO Bool :=
    let dir := "/tmp/monad_e2e_listdir_" ++ I64.to_string process_id in
    let source := r#"use io {IO}
use std.process {exec_cmd}
def main (args : List String) : IO I64 := do {
    let dir := ""# ++ dir ++ r#"";
    exec_cmd "rm" ["-rf", dir];
    exec_cmd "mkdir" ["-p", dir];
    exec_cmd "touch" [dir ++ "/zeta", dir ++ "/alpha", dir ++ "/mid"];
    let entries <- IO.list_dir (Path.path dir);
    exec_cmd "rm" ["-rf", dir];
    let at := \i => match List.get i entries { Option.some e => e, Option.none => "<missing>" };
    // Index 3 must be absent -- that plus the three names below pins
    // both the contents and the sort order, without `List.length`
    // (which needs an explicit `use std.list` import to compile).
    let sorted := String.beq (at 0) "alpha" && String.beq (at 1) "mid" && String.beq (at 2) "zeta";
    let no_extra := String.beq (at 3) "<missing>";
    return (if sorted && no_extra then 7 else 1)
}
"# in
    compile_source_run_expect source "c_list_dir" 7

// --- `std/array.mo`'s six natives -----------------------------------
//
// The COMPILED half of what `std/array.mo`'s own `#[test]`s cover on
// the Rust host. That split is the point: a native that passes every
// host test can still be wired nowhere in codegen (the failure mode
// `validate_no_unwired_natives` exists for), and only running a real
// binary proves otherwise.

/// `array_new` + `array_len` + `array_get`: allocation with a fill,
/// the O(1) length, and an in-range read.
#[test]
def test_array_new_len_get : IO Bool :=
    let source := r#"use std.array {Array}
def main (args : List String) : IO I64 := do {
    let a : Array I64 := Array.new 3 7;
    let len_ok := I64.beq (Array.length a) 3;
    let fill_ok := I64.beq (Array.get_or a 2 0) 7;
    return (if len_ok && fill_ok then 7 else 1)
}
"# in
    compile_source_run_expect source "array_new_len_get" 7

/// Every out-of-range read is `Option.none` -- below zero, at `len`,
/// and past it. In the compiled backend this is the difference between
/// a bounds check and reading past the end of a heap object.
#[test]
def test_array_get_bounds : IO Bool :=
    let source := r#"use std.array {Array}
def main (args : List String) : IO I64 := do {
    let a : Array I64 := Array.new 2 5;
    let below := I64.beq (Array.get_or a (0 - 1) 99) 99;
    let at_len := I64.beq (Array.get_or a 2 99) 99;
    let past := I64.beq (Array.get_or a 77 99) 99;
    return (if below && at_len && past then 7 else 1)
}
"# in
    compile_source_run_expect source "array_get_bounds" 7

/// `array_with` is PERSISTENT: the result carries the new value and
/// the INPUT IS UNCHANGED. Without the second half, an implementation
/// that writes through and returns the same object passes everything
/// else -- and that implementation is exactly the cheaper wrong one.
#[test]
def test_array_set_is_persistent : IO Bool :=
    let source := r#"use std.array {Array}
def main (args : List String) : IO I64 := do {
    let a : Array I64 := Array.new 3 0;
    let b : Array I64 := Array.set a 1 42;
    let wrote := I64.beq (Array.get_or b 1 0) 42;
    let input_untouched := I64.beq (Array.get_or a 1 0) 0;
    return (if wrote && input_untouched then 7 else 1)
}
"# in
    compile_source_run_expect source "array_set_persistent" 7

/// Elements are one machine word whatever their type, so the same
/// natives serve `Array String` -- the polymorphism the design rests
/// on, asserted in the backend where a wrong assumption would be a
/// wild pointer rather than a type error.
#[test]
def test_array_holds_strings : IO Bool :=
    let source := r#"use std.array {Array}
def main (args : List String) : IO I64 := do {
    let a : Array String := Array.new 2 "x";
    let b : Array String := Array.set a 0 "hello";
    let wrote := String.beq (Array.get_or b 0 "none") "hello";
    let other := String.beq (Array.get_or b 1 "none") "x";
    return (if wrote && other then 7 else 1)
}
"# in
    compile_source_run_expect source "array_strings" 7

/// `from_list`/`to_list` round trip with order preserved, which
/// exercises the `set`-fold that builds an array from a list.
#[test]
def test_array_from_list_round_trip : IO Bool :=
    let source := r#"use std.array {Array}
def main (args : List String) : IO I64 := do {
    let xs : List I64 := List.cons 10 (List.cons 20 (List.cons 30 List.empty));
    let a : Array I64 := Array.from_list xs;
    let len_ok := I64.beq (Array.length a) 3;
    let first := I64.beq (Array.get_or a 0 0) 10;
    let last := I64.beq (Array.get_or a 2 0) 30;
    let back := I64.beq (List.length (Array.to_list a)) 3;
    return (if len_ok && first && last && back then 7 else 1)
}
"# in
    compile_source_run_expect source "array_from_list" 7

/// The mutable half: `set_in_place` writes through (genuinely O(1)
/// here, unlike the interpreter's copy-on-write), and `freeze` COPIES
/// -- so mutating the builder AFTER freezing must not disturb the
/// frozen array. That aliasing assertion is the one that fails if
/// `freeze` is ever "optimised" into a cast.
#[test]
def test_array_builder_freeze_does_not_alias : IO Bool :=
    let source := r#"use std.array {Array, ArrayBuilder}
def main (args : List String) : IO I64 := do {
    let b : ArrayBuilder I64 := Array.builder 3 0;
    Array.set_in_place b 1 42;
    let frozen : Array I64 <- Array.freeze b;
    let saw_write := I64.beq (Array.get_or frozen 1 0) 42;
    Array.set_in_place b 1 99;
    let frozen_unchanged := I64.beq (Array.get_or frozen 1 0) 42;
    return (if saw_write && frozen_unchanged then 7 else 1)
}
"# in
    compile_source_run_expect source "array_builder_freeze" 7
