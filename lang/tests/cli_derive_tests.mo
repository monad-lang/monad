/// `#[derive_cli]` — clap-style attribute derive, macro-system maturity test.
///
/// This is the actual proof that `#[derive_cli]` works end to end as a real
/// `.mo` program (not just the Rust-level tests in
/// `core/src/eval/derive_cli_test.rs`): one attribute on a type the user
/// writes themselves generates a full `List String -> Result String
/// DemoCommand` parser, dispatching on subcommand name, `#[arg]`-marked
/// `Bool` fields as `--flag`s, everything else as required positionals.
///
/// Deliberately **not** `use`d by `lang/main.mo` or listed in any
/// self-hosted parse/scope/typecheck test file (`parser_file_tests.mo`,
/// `scope_all_tests.mo`, `typecheck_lang_tests.mo`) — the self-hosted
/// compiler (`lang/parser.mo`) has no concept of `#[derive_cli]` or
/// per-param `#[...]` attributes yet, so this file is only ever run through
/// the Rust host (`cargo run -- test lang/tests/cli_derive_tests.mo`),
/// which does.
use lang.cli {*}

#[derive_cli]
type DemoCommand {
    compile (path : String) (#[arg] verbose : Bool),
    pretty (path : String),
    help,
}

#[test]
def test_derive_cli_compile_with_flag : Bool :=
    match parse_democommand ["compile", "a.mo", "--verbose"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.compile path verbose => path == "a.mo" && verbose == true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_compile_without_flag : Bool :=
    match parse_democommand ["compile", "a.mo"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.compile path verbose => path == "a.mo" && verbose == false,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_pretty : Bool :=
    match parse_democommand ["pretty", "b.mo"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.pretty path => path == "b.mo",
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_help : Bool :=
    match parse_democommand ["help"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.help => true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_unknown_subcommand : Bool :=
    match parse_democommand ["bogus"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "bogus",
    }

#[test]
def test_derive_cli_missing_positional : Bool :=
    match parse_democommand ["compile"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "path",
    }

#[test]
def test_derive_cli_empty_argv : Bool :=
    match parse_democommand [] {
        Result.ok _ => false,
        Result.err _ => true,
    }
