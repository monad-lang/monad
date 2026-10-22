/// Spec-parser tests: the strict, typed parser new CLIs use.
use clap::args {*}
use lib::help {Cli.help_text, Cli.usage}
use lib::parse {Cli.parse}
use lib::spec {
    Cli.ArgValueType, Cli.CommandSpec, Cli.ParseResult, Cli.Parsed,
    Cli.command, Cli.flag, Cli.flag_count, Cli.flag_set,
    Cli.option, Cli.option_i64_optional, Cli.option_optional,
    Cli.option_value, Cli.option_value_i64, Cli.parse_i64,
    Cli.positional, Cli.positional_optional, Cli.positional_spec, Cli.required_positional,
    Cli.with_args, Cli.with_subcommands, Cli.with_version,
    parse_err, parse_help, parse_ok, parse_version,
}

pub def demo_spec : Cli.CommandSpec :=
    Cli.with_args [
        Cli.flag "verbose" "v" "verbose output",
        Cli.flag "quiet" "q" "",
        Cli.option_optional "output" "o" "FILE" "output path",
        Cli.option_i64_optional "count" "c" "N" "how many",
        Cli.positional "path" "",
        Cli.positional_optional "rest" "",
    ] (Cli.command "demo" "demo app")

pub def versioned_spec : Cli.CommandSpec :=
    Cli.with_version "1.2.3" demo_spec

pub def required_spec : Cli.CommandSpec :=
    Cli.with_args [Cli.option "name" "" "NAME" ""] (Cli.command "req" "")

pub def ok_parsed (r : Cli.ParseResult) : Option Cli.Parsed :=
    match r {
        Cli.ParseResult.parse_ok p => Option.some p,
        _ => Option.none,
    }

pub def err_msg (r : Cli.ParseResult) : Option String :=
    match r {
        Cli.ParseResult.parse_err m => Option.some m,
        _ => Option.none,
    }

pub def is_help (r : Cli.ParseResult) : Bool :=
    match r {
        Cli.ParseResult.parse_help _ => true,
        _ => false,
    }

pub def is_version (r : Cli.ParseResult) : Bool :=
    match r {
        Cli.ParseResult.parse_version _ => true,
        _ => false,
    }

pub def err_contains (r : Cli.ParseResult) (needle : String) : Bool :=
    match err_msg r {
        Option.some m => String.contains m needle,
        Option.none => false,
    }

pub def opt_string_is (o : Option String) (v : String) : Bool :=
    match o {
        Option.some x => String.beq x v,
        Option.none => false,
    }

pub def opt_i64_is (o : Option I64) (v : I64) : Bool :=
    match o {
        Option.some x => I64.beq x v,
        Option.none => false,
    }

#[test]
pub def test_parse_long_flag : Bool :=
    match ok_parsed (Cli.parse demo_spec ["--verbose", "a.mo"]) {
        Option.some p => Cli.flag_set "verbose" p && Cli.required_positional 0 p == "a.mo",
        Option.none => false,
    }

#[test]
pub def test_parse_short_flag : Bool :=
    match ok_parsed (Cli.parse demo_spec ["-v", "a.mo"]) {
        Option.some p => Cli.flag_set "verbose" p,
        Option.none => false,
    }

#[test]
pub def test_parse_long_option_space : Bool :=
    match ok_parsed (Cli.parse demo_spec ["--output", "out", "a.mo"]) {
        Option.some p => opt_string_is (Cli.option_value "output" p) "out",
        Option.none => false,
    }

#[test]
pub def test_parse_long_option_equals : Bool :=
    match ok_parsed (Cli.parse demo_spec ["--output=out", "a.mo"]) {
        Option.some p => opt_string_is (Cli.option_value "output" p) "out",
        Option.none => false,
    }

#[test]
pub def test_parse_short_option_attached : Bool :=
    match ok_parsed (Cli.parse demo_spec ["-oout", "a.mo"]) {
        Option.some p => opt_string_is (Cli.option_value "output" p) "out",
        Option.none => false,
    }

#[test]
pub def test_parse_short_option_equals : Bool :=
    match ok_parsed (Cli.parse demo_spec ["-o=out", "a.mo"]) {
        Option.some p => opt_string_is (Cli.option_value "output" p) "out",
        Option.none => false,
    }

#[test]
pub def test_parse_short_cluster : Bool :=
    match ok_parsed (Cli.parse demo_spec ["-vq", "a.mo"]) {
        Option.some p => Cli.flag_set "verbose" p && Cli.flag_set "quiet" p,
        Option.none => false,
    }

#[test]
pub def test_parse_repeated_flag_counts : Bool :=
    match ok_parsed (Cli.parse demo_spec ["-v", "-v", "a.mo"]) {
        Option.some p => I64.beq (Cli.flag_count "verbose" p) 2,
        Option.none => false,
    }

#[test]
pub def test_parse_double_dash_fences : Bool :=
    match ok_parsed (Cli.parse demo_spec ["--", "--verbose"]) {
        Option.some p =>
            Bool.not (Cli.flag_set "verbose" p) && Cli.required_positional 0 p == "--verbose",
        Option.none => false,
    }

#[test]
pub def test_parse_unknown_long_flag : Bool :=
    err_contains (Cli.parse demo_spec ["--bogus", "a.mo"]) "bogus"

#[test]
pub def test_parse_unknown_short_flag : Bool :=
    err_contains (Cli.parse demo_spec ["-z", "a.mo"]) "unknown flag"

#[test]
pub def test_parse_missing_option_value : Bool :=
    err_contains (Cli.parse demo_spec ["--output"]) "requires a value"

#[test]
pub def test_parse_option_does_not_consume_flag : Bool :=
    err_contains (Cli.parse demo_spec ["--output", "--verbose", "a.mo"]) "requires a value"

#[test]
pub def test_parse_extra_positional : Bool :=
    err_contains (Cli.parse demo_spec ["a", "b", "c"]) "unexpected argument"

#[test]
pub def test_parse_missing_required_option : Bool :=
    err_contains (Cli.parse required_spec []) "missing required option"

#[test]
pub def test_parse_missing_required_positional : Bool :=
    err_contains (Cli.parse demo_spec ["--output", "out"]) "missing required argument"

#[test]
pub def test_parse_invalid_i64 : Bool :=
    err_contains (Cli.parse demo_spec ["--output", "out", "--count", "x", "a.mo"]) "expected an integer"

#[test]
pub def test_parse_negative_i64_value : Bool :=
    match ok_parsed (Cli.parse demo_spec ["--output", "out", "--count", "-5", "a.mo"]) {
        Option.some p => opt_i64_is (Cli.option_value_i64 "count" p) (I64.sub 0 5),
        Option.none => false,
    }

#[test]
pub def test_parse_help : Bool :=
    is_help (Cli.parse demo_spec ["--help"])

#[test]
pub def test_parse_version : Bool :=
    is_version (Cli.parse versioned_spec ["--version"])

pub def sub_spec : Cli.CommandSpec :=
    Cli.with_subcommands [
        Cli.with_args [Cli.positional "path" ""] (Cli.command "build" "build it"),
        Cli.command "list" "list them",
    ] (Cli.command "tool" "a tool")

#[test]
pub def test_parse_subcommand : Bool :=
    match ok_parsed (Cli.parse sub_spec ["build", "a.mo"]) {
        Option.some p => p.name == "build" && Cli.required_positional 0 p == "a.mo",
        Option.none => false,
    }

#[test]
pub def test_parse_unknown_subcommand : Bool :=
    err_contains (Cli.parse sub_spec ["bogus"]) "unknown subcommand"

#[test]
pub def test_parse_missing_subcommand : Bool :=
    err_contains (Cli.parse sub_spec []) "missing subcommand"

#[test]
pub def test_parse_subcommand_help : Bool :=
    is_help (Cli.parse sub_spec ["--help"])

pub def global_spec : Cli.CommandSpec :=
    Cli.with_args [Cli.flag "verbose" "v" ""]
        (Cli.with_subcommands [
            Cli.with_args [Cli.positional "path" ""] (Cli.command "build" "build it"),
        ] (Cli.command "tool" "a tool"))

#[test]
pub def test_subcommand_long_equals_unknown : Bool :=
    err_contains (Cli.parse global_spec ["--bogus=1", "build", "a.mo"]) "unknown flag: --bogus"

#[test]
pub def test_subcommand_long_equals_flag_rejected : Bool :=
    err_contains (Cli.parse global_spec ["--verbose=1", "build", "a.mo"]) "does not take a value"

#[test]
pub def test_subcommand_long_equals_option_accepted : Bool :=
    match ok_parsed (Cli.parse global_spec ["--verbose", "build", "a.mo"]) {
        Option.some p => String.beq p.name "build",
        Option.none => false,
    }

#[test]
pub def test_parse_i64_rejects_lone_minus : Bool :=
    match Cli.parse_i64 "-" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
pub def test_parse_i64_rejects_overflow : Bool :=
    match Cli.parse_i64 "99999999999999999999" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
pub def test_parse_i64_accepts_max_boundary : Bool :=
    match Cli.parse_i64 "9223372036854775807" {
        Option.some n => I64.beq n 9223372036854775807,
        Option.none => false,
    }

#[test]
pub def test_usage_omits_absent_sections : Bool :=
    let text : String := Cli.usage (Cli.command "plain" "") in
    Bool.not (String.contains text "[ARGS]") && Bool.not (String.contains text "<SUBCOMMAND>")

#[test]
pub def test_help_lists_builtins : Bool :=
    String.contains (Cli.help_text versioned_spec) "-h, --help"
        && String.contains (Cli.help_text versioned_spec) "-V, --version"

pub def multi_i64_spec : Cli.CommandSpec :=
    Cli.with_args [Cli.positional_spec Cli.ArgValueType.arg_i64 "n" false false "" true ""]
        (Cli.command "nums" "")

#[test]
pub def test_multiple_i64_positionals_validate_all : Bool :=
    err_contains (Cli.parse multi_i64_spec ["1", "x"]) "expected an integer"

#[test]
pub def test_multiple_i64_positionals_valid : Bool :=
    match ok_parsed (Cli.parse multi_i64_spec ["1", "2", "3"]) {
        Option.some _ => true,
        Option.none => false,
    }
