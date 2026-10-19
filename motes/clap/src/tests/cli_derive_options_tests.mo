/// `#[derive Cli]` with options, typed values, attribute arguments, and
/// the single-command/struct forms. The pure parser is covered by
/// `cli_parser_tests.mo`; this file proves the generated spec/decode pair.
use clap::args {*}

#[derive Cli]
type RichCommand {
    run (path : String)
        (#[arg {short := "v"}] verbose : Bool)
        (#[opt {short := "o"}] output : Option String)
        (#[opt {short := "n"}] count : I64),
    list (#[opt] all : Option String),
}

#[derive Cli]
struct DArgs {
    input : String,
    verbose : Bool,
    count : I64 := 3,
}

#[derive Cli]
type SingleArgs {
    single (path : String) (#[arg] verbose : Bool),
}

#[derive Cli]
type NoShort {
    run (#[arg] verbose : Bool) (#[arg {short := ""}] debug : Bool),
}

def opt_string_is (o : Option String) (v : String) : Bool :=
    match o {
        Option.some x => String.beq x v,
        Option.none => false,
    }

#[test]
def test_derive_options_all_forms : Bool :=
    match parse_richcommand ["run", "a.mo", "-v", "-o", "out", "-n", "7"] {
        Result.ok cmd =>
            match cmd {
                RichCommand.run path verbose output count =>
                    String.beq path "a.mo"
                        && verbose
                        && opt_string_is output "out"
                        && I64.beq count 7,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_options_absent_optional : Bool :=
    match parse_richcommand ["run", "a.mo", "--count", "7"] {
        Result.ok cmd =>
            match cmd {
                RichCommand.run path verbose output count =>
                    String.beq path "a.mo"
                        && Bool.not verbose
                        && match output { Option.none => true, Option.some _ => false }
                        && I64.beq count 7,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_options_long_equals : Bool :=
    match parse_richcommand ["run", "a.mo", "--output=out", "--count=7"] {
        Result.ok cmd =>
            match cmd {
                RichCommand.run path verbose output count =>
                    opt_string_is output "out" && I64.beq count 7,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_options_subcommand : Bool :=
    match parse_richcommand ["list", "--all", "x"] {
        Result.ok cmd =>
            match cmd {
                RichCommand.list all => opt_string_is all "x",
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_struct_form_flags_and_defaults : Bool :=
    match parse_dargs ["a.mo", "--verbose"] {
        Result.ok cmd =>
            match cmd {
                DArgs.mk input verbose count =>
                    String.beq input "a.mo" && verbose && I64.beq count 3,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_struct_form_positional_override : Bool :=
    match parse_dargs ["a.mo", "9"] {
        Result.ok cmd =>
            match cmd {
                DArgs.mk input verbose count =>
                    String.beq input "a.mo" && Bool.not verbose && I64.beq count 9,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_single_constructor_type : Bool :=
    match parse_singleargs ["a.mo", "--verbose"] {
        Result.ok cmd =>
            match cmd {
                SingleArgs.single path verbose => String.beq path "a.mo" && verbose,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_no_short : Bool :=
    match parse_noshort ["--debug"] {
        Result.ok cmd =>
            match cmd {
                NoShort.run verbose debug => Bool.not verbose && debug,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_no_short_rejects_short : Bool :=
    match parse_noshort ["-d"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "unknown flag",
    }
