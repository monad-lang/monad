/// Tests moved out of `codegen::test_driver` so the production module stays readable.

use lib::decls {filter_reachable_decls}
use lib::errors {CodegenError}
use lib::qualify {qualified_def_name_str, qualify_modules}
use lib::test::support {qtest_def}
use lang::types {
    Attribute, Class, DebugName, Decl, Def, ModulePath, NamePath, Term, has_attr, i64, id, no_attrs, num, package_private,
    show_identifier, struct_lit, use_bare,
}
use lib::emit {
    CompileInput, compile_db_module_with_debug, compile_input_of_modules, emit_type_head_is_io,
    gate_then, validate_reachable_elaborated
}
use lib::symbols {
    bare_npath, module_path_to_str, name_path_to_str, symbol_identifier,
}
use parsec::number {parse_i64}
use lib::validate {
    report_elab_stats, validate_no_colliding_def_symbols,
    validate_no_undesugared_struct_lits, validate_no_undesugared_elims,
    validate_no_unwired_natives
}
use llvm::ir {LLVMModule}
use lang::module {
    BestEffortElab, LoadedModules, ModuleInfo, best_effort_errors, get_loaded_all,
    get_loaded_main, resolve_open_aliases_in_modules, try_parse_decls,
}
use lang::scope {
    collect_classes, strip_all_leading_binders,
    validate_no_unresolved_class_calls,
}
use std::list {List.intercalate, List.length}
use std::log {fail_line}
use std::stream {StreamError, StreamError.is_not_found}
use lib::test_driver {
    TestSpec, classify_test_def, discover_test_defs, display_prefix_of,
    fmt_dur_ns, fmt_dur_source, is_no_tests_error, is_test_def,
    parse_driver_result, rename_user_main,
    result_file_marker, synth_test_stmts, synthesize_test_driver_source,
    test_driver_gates,
}

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Decl.def_d` fixtures (some `#[test]`-attributed, some
// not), same construction style as `codegen/link.mo`'s own
// existing `test_link_compile_defs_to_ir` fixture. No pipeline wiring
// exercised here — pure discovery-function unit tests.

def test_attr : List Attribute := List.cons (Attribute.mk (Identifier.id "test") List.empty) List.empty
/// A one-segment MODULE path -- the `use`-path role
/// (`test_discover_test_defs_ignores_non_def_decls` builds a `Decl.use_d`
/// with it, and `Decl.use_d` is the one decl form that kept a real
/// `ModulePath` through the qualified-names split).
def dummy_module_path (name : String) : ModulePath := ModulePath.mk (List.cons (Identifier.id name) List.empty)

/// The DEF-name role of the same one-segment shape -- `Def.name` is a
/// `NamePath`, so the fixtures below cannot reuse `dummy_module_path`.
def dummy_npath (name : String) : NamePath := NamePath.mk (List.cons (Identifier.id name) List.empty)

def dummy_def (name : String) (attrs : List Attribute) : Def :=
    Def.mk (dummy_npath name) Term.hole (Term.lit (Literal.num 1 NumSuffix.i64)) List.empty attrs Visibility.package_private List.empty

/// A `Def` whose declared type is `Bool` / `IO Bool`, for
/// `classify_test_def`. The type term is built the same way the parser
/// would leave it: a bare `Term.var` head for `Bool`, and an
/// application of the `IO` head to it for `IO Bool`.
def typed_def (name : String) (typ : Term) : Def :=
    Def.mk (dummy_npath name) typ (Term.lit (Literal.num 1 NumSuffix.i64)) List.empty test_attr Visibility.package_private List.empty

def ty_var (name : String) : Term := Term.var 0 (DebugName.named (Identifier.id name))

def bool_spec (name : String) : TestSpec :=
    { display := "m::" ++ name, call := name, io_test := false, result_test := false }

def io_spec (name : String) : TestSpec :=
    { display := "m::" ++ name, call := name, io_test := true, result_test := false }

def result_spec (name : String) : TestSpec :=
    { display := "m::" ++ name, call := name, io_test := false, result_test := true }

def io_result_spec (name : String) : TestSpec :=
    { display := "m::" ++ name, call := name, io_test := true, result_test := true }

// Every unit test below synthesizes with the same result path -- only
// presence in the emitted source is asserted; nothing is ever written.
def test_result_path : String := "/tmp/__monad_test_driver_result.txt"

#[partial]
def decl_list_has_exactly_one_main (decl_list : List Decl) : Bool :=
    I64.beq (count_main_defs decl_list) 1

#[partial]
def count_main_defs (decl_list : List Decl) : I64 :=
    match decl_list {
        List.empty => 0,
        List.cons d rest =>
            let here : I64 := match d {
                Decl.def_d def_val => if String.beq (name_path_to_str (Def.name def_val)) "main" then 1 else 0,
                _ => 0,
            } in
            here + count_main_defs rest,
    }

#[partial]
def bool_specs_upto (n : I64) : List TestSpec :=
    if I64.lt n 1
    then List.empty
    else List.cons (bool_spec "t") (bool_specs_upto (n - 1))

#[test]
def test_is_test_def_true_for_tagged : Bool :=
    is_test_def (dummy_def "test_a" test_attr)

#[test]
def test_is_test_def_false_for_untagged : Bool :=
    Bool.not (is_test_def (dummy_def "helper" no_attrs))

#[test]
def test_discover_test_defs_filters_correctly : Bool :=
    let decl_list : List Decl :=
        List.cons (Decl.def_d (dummy_def "test_a" test_attr))
            (List.cons (Decl.def_d (dummy_def "helper" no_attrs))
                (List.cons (Decl.def_d (dummy_def "test_b" test_attr)) List.empty)) in
    let found : List Def := discover_test_defs decl_list in
    I64.beq (List.length found) 2

#[test]
def test_discover_test_defs_ignores_non_def_decls : Bool :=
    let use_decl : Decl := Decl.use_d (dummy_module_path "std") UseFilter.use_bare true in
    let decl_list : List Decl := List.cons use_decl (List.cons (Decl.def_d (dummy_def "test_a" test_attr)) List.empty) in
    I64.beq (List.length (discover_test_defs decl_list)) 1

#[test]
def test_discover_test_defs_empty_when_none_tagged : Bool :=
    let decl_list : List Decl := List.cons (Decl.def_d (dummy_def "helper" no_attrs)) List.empty in
    match discover_test_defs decl_list { List.empty => true, List.cons _ _ => false }

#[test]
def test_classify_test_def_bool_is_not_io : Bool :=
    let spec : TestSpec := classify_test_def "m::" (typed_def "test_a" (ty_var "Bool")) in
    Bool.not spec.io_test && String.beq spec.call "test_a"

#[test]
def test_classify_test_def_io_bool_is_io : Bool :=
    let io_bool : Term := Term.app (ty_var "IO") (ty_var "Bool") in
    let spec : TestSpec := classify_test_def "m::" (typed_def "test_a" io_bool) in
    spec.io_test

/// The display name is what the runner prints, and the `::` separator
/// is the whole point of it -- `module::sub::test_name`.
#[test]
def test_classify_test_def_display_name_uses_prefix : Bool :=
    let spec : TestSpec := classify_test_def "a::b::" (typed_def "t" (ty_var "Bool")) in
    String.beq spec.display "a::b::t"

#[test]
def test_display_prefix_of_joins_with_colons : Bool :=
    let mp : ModulePath := ModulePath.mk (List.cons (Identifier.id "a") (List.cons (Identifier.id "b") List.empty)) in
    String.beq (display_prefix_of mp) "a::b::"

/// `rename_user_main` must rename `main` and nothing else -- a def
/// merely CONTAINING "main" keeps its name.
#[test]
def test_rename_user_main_renames_only_main : Bool :=
    let decl_list : List Decl :=
        List.cons (Decl.def_d (dummy_def "main" no_attrs))
            (List.cons (Decl.def_d (dummy_def "main_helper" no_attrs)) List.empty) in
    let renamed : List Decl := rename_user_main decl_list in
    match renamed {
        List.cons d1 rest =>
            match d1 {
                Decl.def_d dv1 =>
                    String.beq (name_path_to_str (Def.name dv1)) "__monad_user_entry" &&
                    match rest {
                        List.cons d2 _ => match d2 {
                            Decl.def_d dv2 => String.beq (name_path_to_str (Def.name dv2)) "main_helper",
                            _ => false,
                        },
                        List.empty => false,
                    },
                _ => false,
            },
        List.empty => false,
    }

#[test]
def test_rename_user_main_keeps_decl_count : Bool :=
    let decl_list : List Decl :=
        List.cons (Decl.def_d (dummy_def "main" no_attrs))
            (List.cons (Decl.def_d (dummy_def "helper" no_attrs)) List.empty) in
    I64.beq (List.length (rename_user_main decl_list)) 2

/// The degenerate zero-test driver must still PARSE -- the caller
/// reports "no tests" before reaching this, but a function that emits
/// unparseable source turns that into an unrelated internal error.
#[test]
def test_synthesize_test_driver_source_no_tests_still_parses : Bool :=
    match try_parse_decls (synthesize_test_driver_source List.empty "m.mo" test_result_path) {
        Option.some decl_list => decl_list_has_exactly_one_main decl_list,
        Option.none => false,
    }

#[test]
def test_synthesize_test_driver_source_parses_and_names_main : Bool :=
    // The whole point of the string-templating architecture decision
    // (see this file's own top-of-file doc comment): the synthesized
    // source must round-trip through the REAL parser, producing exactly
    // one `Decl.def_d` named "main" (plus the leading `open IO {...}` decl
    // and the `__pad2`/`__fmt_dur` helpers the driver source also declares).
    let specs : List TestSpec := List.cons (bool_spec "test_a") (List.cons (bool_spec "test_b") List.empty) in
    let source : String := synthesize_test_driver_source specs "m.mo" test_result_path in
    match try_parse_decls source {
        Option.some decl_list => decl_list_has_exactly_one_main decl_list,
        Option.none => false,
    }

/// A file mixing both shapes is the common case in
/// `slow_tests/src/codegen_*_tests.mo`; the two bind differently
/// (`:=` vs `<-`) and both must still parse.
#[test]
def test_synthesize_test_driver_source_mixed_shapes_parse : Bool :=
    let specs : List TestSpec := List.cons (bool_spec "t_pure") (List.cons (io_spec "t_io") List.empty) in
    match try_parse_decls (synthesize_test_driver_source specs "m.mo" test_result_path) {
        Option.some decl_list => decl_list_has_exactly_one_main decl_list,
        Option.none => false,
    }

/// The display name reaches the emitted source -- this is the
/// regression guard for the `::` presentation.
#[test]
def test_synthesize_test_driver_source_embeds_display_name : Bool :=
    let specs : List TestSpec := List.cons (bool_spec "test_a") List.empty in
    String.contains (synthesize_test_driver_source specs "m.mo" test_result_path) "m::test_a"

/// An `IO Bool` test binds with `<-`, a `Bool` test with `:=`. Getting
/// this backwards produces source that either fails to typecheck or
/// (worse) tests the IO action itself rather than its result.
#[test]
def test_synthesize_test_driver_source_io_uses_bind : Bool :=
    let io_src : String := synthesize_test_driver_source (List.cons (io_spec "t") List.empty) "m.mo" test_result_path in
    let pure_src : String := synthesize_test_driver_source (List.cons (bool_spec "t") List.empty) "m.mo" test_result_path in
    String.contains io_src "__b0 <- t;" && String.contains pure_src "__b0 := t;"

/// The failure accumulator is threaded through explicit `I64.add`
/// calls, never a chained `+`. A chain re-introduces the generic
/// `Add A` dictionary recursion that segfaulted every multi-test
/// driver -- see `synth_test_stmts`.
#[test]
def test_synthesize_test_driver_source_accumulates_without_plus_chain : Bool :=
    let specs : List TestSpec :=
        List.cons (bool_spec "a") (List.cons (bool_spec "b") (List.cons (bool_spec "c") List.empty)) in
    let src : String := synthesize_test_driver_source specs "m.mo" test_result_path in
    String.contains src "I64.add __f0" && String.contains src "I64.add __f1"

#[test]
def test_fmt_dur_ns_below_microsecond_is_raw_nanos : Bool :=
    String.beq (fmt_dur_ns 0) "0ns" && String.beq (fmt_dur_ns 999) "999ns"

#[test]
def test_fmt_dur_ns_microseconds_truncate : Bool :=
    // `{:.0}` on `as_micros()` -- an integer count that has ALREADY
    // truncated, so 1999ns is 1µs, not 2µs.
    String.beq (fmt_dur_ns 1000) "1µs" && String.beq (fmt_dur_ns 1999) "1µs"

// The case the old whole-part-first shape could not express: the
// fraction rounds up to 100 hundredths and has to CARRY into the whole
// part. Red before the rounding fix (it printed "1.99ms").
#[test]
def test_fmt_dur_ns_milliseconds_round_half_up_with_carry : Bool :=
    String.beq (fmt_dur_ns 1999996) "2.00ms"

#[test]
def test_fmt_dur_ns_milliseconds_round_half_up : Bool :=
    // 1.235ms -> 1.24ms (half rounds away from zero, as `{:.2}` does).
    String.beq (fmt_dur_ns 1235000) "1.24ms"

#[test]
def test_fmt_dur_ns_milliseconds_pad_fraction : Bool :=
    String.beq (fmt_dur_ns 1000000) "1.00ms" && String.beq (fmt_dur_ns 1050000) "1.05ms"

// The largest value still in the ms branch: rounds up past the branch's
// own nominal ceiling, so the whole part is 1000, not 1.
#[test]
def test_fmt_dur_ns_milliseconds_top_of_range_carries_to_1000 : Bool :=
    String.beq (fmt_dur_ns 999999999) "1000.00ms"

#[test]
def test_fmt_dur_ns_seconds : Bool :=
    String.beq (fmt_dur_ns 1000000000) "1.00s"
    && String.beq (fmt_dur_ns 1500000000) "1.50s"
    && String.beq (fmt_dur_ns 2345000000) "2.35s"

// The host clock is the wall clock (`SystemTime::now`), so an interval
// can come back negative if it steps backwards mid-test.
#[test]
def test_fmt_dur_ns_negative_clamps_to_zero : Bool :=
    String.beq (fmt_dur_ns (0 - 5)) "0ns"

// Drift guard: `fmt_dur_source` embeds a TEXT copy of `fmt_dur_ns` that
// no test can call directly. If the rounding is ever reverted there, the
// generated driver silently goes back to truncating while `fmt_dur_ns`
// above keeps passing -- so assert the rounding constants are present in
// the emitted source too.
#[test]
def test_fmt_dur_source_carries_the_rounding_constants : Bool :=
    String.contains fmt_dur_source "I64.add d 5000"
    && String.contains fmt_dur_source "I64.add d 5000000"
    && String.contains fmt_dur_source "if I64.lt d 0 then"

#[test]
def test_is_no_tests_error_true_for_the_sentinel : Bool :=
    is_no_tests_error CodegenError.no_tests

// The `no `-prefix hazard this predicate exists for: an unresolved
// instance error starts with the same two words and must NOT be read as
// "this file has no tests".
#[test]
def test_is_no_tests_error_false_for_instance_failure : Bool :=
    Bool.not (is_no_tests_error (CodegenError.of_message "no instance found for `Foldable.foldl` (needed in `m::t`)"))

#[test]
def test_is_no_tests_error_false_for_native_failure : Bool :=
    Bool.not (is_no_tests_error (CodegenError.of_message "native `f64_mul` is not wired into the native backend"))

// ─── The result-file protocol ────────────────────────────────────────
//
// The old exit-code channel had a hard ceiling: a failure COUNT is 8
// bits, so a file with more than 255 tests could not report through it
// at all (`lang/src/parser.mo`, at 288 tests, used to be refused
// outright). The result FILE has no ceiling -- the count is decimal
// text -- so the boundary that needs pinning is now the PROTOCOL: the
// marker shape `parse_driver_result` accepts, and the write's presence
// in the emitted source. Not an end-to-end test on purpose: running a
// real driver binary is the parent's job; what can go wrong at THIS
// layer is a malformed marker or a synthesis that forgets the write.

// The write lands right before `return`, AFTER the summary println --
// a driver that dies mid-print leaves no file, and the parent reads
// "crashed" rather than trusting a stale count.
#[test]
def test_driver_source_writes_the_result_marker : Bool :=
    let src : String := synthesize_test_driver_source (List.cons (bool_spec "t") List.empty) "m.mo" test_result_path in
    String.contains src ("IO.write_file (Path.path \"" ++ test_result_path ++ "\")")
    && String.contains src ("\"" ++ result_file_marker ++ "\" ++ I64.to_string __f0")

// Zero tests still writes the file (with the literal 0) -- "no tests"
// is reported by the caller before synthesis, but if synthesis is ever
// reached the emitted source must not name the nonexistent `__f-1`.
#[test]
def test_driver_source_writes_marker_with_zero_for_no_tests : Bool :=
    let src : String := synthesize_test_driver_source List.empty "m.mo" test_result_path in
    String.contains src ("\"" ++ result_file_marker ++ "\" ++ I64.to_string 0")

// A file the old ceiling refused outright now synthesizes a driver
// whose last accumulator is `__f287` -- `lang/src/parser.mo`'s own
// 288-test count, the corpus file that motivated the ceiling. This is
// pure string synthesis (no parse, no link): the point is only that
// nothing in the synthesis layer clamps or refuses the count.
#[test]
def test_driver_source_has_no_test_count_ceiling : Bool :=
    let src : String := synthesize_test_driver_source (bool_specs_upto 288) "m.mo" test_result_path in
    String.contains src "__f287"
    && String.contains src ("\"" ++ result_file_marker ++ "\" ++ I64.to_string __f287")

#[test]
def test_parse_driver_result_round_trips : Bool :=
    match parse_driver_result (result_file_marker ++ "7") {
        Option.some n => I64.beq n 7,
        Option.none => false,
    }

#[test]
def test_parse_driver_result_round_trips_the_corpus_count : Bool :=
    match parse_driver_result (result_file_marker ++ "288") {
        Option.some n => I64.beq n 288,
        Option.none => false,
    }

// The count is written with no trailing newline, but the parent trims
// before parsing anyway -- a driver edited by hand, or a native write
// that ever grows a newline, must still round-trip.
#[test]
def test_parse_driver_result_trims_whitespace : Bool :=
    match parse_driver_result (result_file_marker ++ " 12 \n") {
        Option.some n => I64.beq n 12,
        Option.none => false,
    }

// A count of zero is a VALID parse, not "nothing" -- this is the all-
// tests-passed report and must reach the parent as `Option.some 0`.
#[test]
def test_parse_driver_result_zero_is_some : Bool :=
    match parse_driver_result (result_file_marker ++ "0") {
        Option.some n => I64.beq n 0,
        Option.none => false,
    }

// The reject tests match rather than `Bool.not`-ing the `Option`
// directly: `parse_driver_result` returns an `Option I64`, and the
// self-hosted checker (unlike the Rust host's) accepted
// `Bool.not (Option ...)` silently -- these tests once "passed" that
// way while asserting nothing.
#[test]
def test_parse_driver_result_rejects_a_missing_marker : Bool :=
    match parse_driver_result "7" {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_parse_driver_result_rejects_garbage_after_the_marker : Bool :=
    match parse_driver_result (result_file_marker ++ "x") {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_parse_driver_result_rejects_input_shorter_than_the_marker : Bool :=
    match parse_driver_result "" {
        Option.some _ => false,
        Option.none => match parse_driver_result "__MONAD" {
            Option.some _ => false,
            Option.none => true,
        },
    }

#[test]
def test_parse_driver_result_rejects_a_wrong_marker : Bool :=
    match parse_driver_result "__MONAD_CHECK__ 7" {
        Option.some _ => false,
        Option.none => true,
    }

// ─── The `Result` test shape ────────────────────────────────────────
//
// A `Result`-typed test binds its call to a `__q<i>` holder and derives
// the verdict from the constructor, rather than binding the call
// straight to the `__b<i>` verdict local. Getting this wrong makes the
// driver either fail to parse (no holder declared) or compare the
// `Result` value itself as a Bool.

#[test]
def test_driver_source_result_test_matches_the_constructor : Bool :=
    let src : String := synthesize_test_driver_source (List.cons (result_spec "t") List.empty) "m.mo" test_result_path in
    String.contains src "let __q0 := t;"
    && String.contains src "let __b0 := match __q0 { Result.ok _ => true, Result.err _ => false };"
    // The constructor match must survive the REAL parser too: a
    // `Result` driver whose source fails to parse is reported as a
    // mystery internal error, not as a run of tests.
    && match try_parse_decls src {
        Option.some decl_list => decl_list_has_exactly_one_main decl_list,
        Option.none => false,
    }

// An `IO (Result ...)` test combines both: the holder binds with `<-`
// like any IO test, then the constructor match derives the verdict.
#[test]
def test_driver_source_io_result_test_binds_then_matches : Bool :=
    let src : String := synthesize_test_driver_source (List.cons (io_result_spec "t") List.empty) "m.mo" test_result_path in
    String.contains src "let __q0 <- t;"
    && String.contains src "let __b0 := match __q0 { Result.ok _ => true, Result.err _ => false };"

// A plain test must NOT grow a holder or a match -- that shape is the
// `Result` shape's alone.
#[test]
def test_driver_source_bool_test_has_no_match : Bool :=
    let src : String := synthesize_test_driver_source (List.cons (bool_spec "t") List.empty) "m.mo" test_result_path in
    Bool.not (String.contains src "match __q0")

#[test]
def test_driver_gates_reject_an_undesugared_struct_literal : Bool :=
    let lit_def := Decl.def_d (Def.mk (dummy_npath "f") Term.hole (Term.lit (Literal.struct_lit List.empty Option.none)) List.empty no_attrs Visibility.package_private List.empty) in
    match test_driver_gates (Result.ok List.empty) List.empty (List.cons lit_def List.empty) {
        Result.err _ => true,
        Result.ok _ => false,
    }

#[test]
def test_driver_gates_reject_two_defs_on_one_symbol : Bool :=
    match test_driver_gates (Result.ok List.empty) List.empty (List.cons (qtest_def "dup" "x") (List.cons (qtest_def "dup" "y") List.empty)) {
        Result.err _ => true,
        Result.ok _ => false,
    }

#[test]
def test_driver_gates_accept_a_clean_program : Bool :=
    match test_driver_gates (Result.ok List.empty) List.empty (List.cons (qtest_def "a::f" "x") (List.cons (qtest_def "b::f" "y") List.empty)) {
        Result.err _ => false,
        Result.ok _ => true,
    }

#[test]
def test_driver_gates_report_the_elaboration_failure_first : Bool :=
    match test_driver_gates (Result.err "elab") List.empty (List.cons (qtest_def "dup" "x") (List.cons (qtest_def "dup" "y") List.empty)) {
        Result.err e => e == "elab",
        Result.ok _ => false,
    }
