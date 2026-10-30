/// `#[derive Cli]` — clap-style attribute derive, macro-system maturity test.
///
/// This is the actual proof that `#[derive Cli]` works end to end as a real
/// `.mo` program under BOTH compilers (the Rust-level tests in
/// `rust/core/src/eval/derive_cli_test.rs` cover the Rust host only): one
/// attribute on a type the user writes themselves — registered by the
/// `#[derive_handler Cli]` annotation on `derive_cli` in
/// `motes/clap/src/args.mo`, not by any compiler special case — generates
/// a full `List String -> Result String DemoCommand` parser, dispatching
/// on subcommand name, `#[arg]`-marked `Bool` fields as `--flag`s,
/// everything else as required positionals. The attribute-to-macro
/// bridge (`lang/typecheck/macro_queue.mo`'s `derive_bridge_decls`)
/// took this file off the Rust-only list (`scripts/check-monad-tests.sh`,
/// the P10 record) — it now runs self-hosted too.
use lib::args {*}

#[derive Cli]
pub type DemoCommand {
    compile (path : String) (#[arg] verbose : Bool),
    pretty (path : String),
    help,
}

#[test]
pub def test_derive_cli_compile_with_flag : Bool :=
    match parse_democommand ["compile", "a.mo", "--verbose"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.compile path verbose => path == "a.mo" && verbose == true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
pub def test_derive_cli_compile_without_flag : Bool :=
    match parse_democommand ["compile", "a.mo"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.compile path verbose => path == "a.mo" && verbose == false,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
pub def test_derive_cli_pretty : Bool :=
    match parse_democommand ["pretty", "b.mo"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.pretty path => path == "b.mo",
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
pub def test_derive_cli_help : Bool :=
    match parse_democommand ["help"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.help => true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
pub def test_derive_cli_unknown_subcommand : Bool :=
    match parse_democommand ["bogus"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "bogus",
    }

#[test]
pub def test_derive_cli_missing_positional : Bool :=
    match parse_democommand ["compile"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "path",
    }

#[test]
pub def test_derive_cli_empty_argv : Bool :=
    match parse_democommand [] {
        Result.ok _ => false,
        Result.err _ => true,
    }
