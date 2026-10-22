/// Self-hosted counterpart to `motes/clap/src/tests/cli_derive_tests.mo` --
/// proves `derive_cli!` (the bare decl-macro form, not the `#[derive Cli]`
/// attribute sugar) type-checks correctly through the SELF-HOSTED
/// checker (`lang/typecheck/macro_queue.mo`'s `expand_decls_graph` +
/// `lang/typecheck/meta_eval.mo`), the same way
/// `slow_tests/typecheck_std_tests.mo`'s `known_broken_typecheck_std_derive_tests`
/// already proves for `std/derive.mo`'s four derives. The `#[derive Cli]`
/// attribute-sugar dispatch (turning the attribute into a synthesized
/// `derive_cli!` call via clap's own `#[derive_handler Cli]`
/// registration) is proven separately by `cli_derive_tests.mo`, which
/// now runs under both hosts.
///
/// Listed in `slow_tests/typecheck_lang_tests.mo` (self-hosted
/// type-check corpus) -- like `cli_derive_tests.mo`.
use lib::args {*}

pub type DemoCommand {
    compile (path : String) (#[arg] verbose : Bool),
    pretty (path : String),
    help,
}

derive_cli! DemoCommand

#[test]
pub def test_derive_cli_self_hosted_compile_with_flag : Bool :=
    match parse_democommand ["compile", "a.mo", "--verbose"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.compile path verbose => path == "a.mo" && verbose == true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
pub def test_derive_cli_self_hosted_compile_without_flag : Bool :=
    match parse_democommand ["compile", "a.mo"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.compile path verbose => path == "a.mo" && verbose == false,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
pub def test_derive_cli_self_hosted_pretty : Bool :=
    match parse_democommand ["pretty", "b.mo"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.pretty path => path == "b.mo",
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
pub def test_derive_cli_self_hosted_help : Bool :=
    match parse_democommand ["help"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.help => true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
pub def test_derive_cli_self_hosted_unknown_subcommand : Bool :=
    match parse_democommand ["bogus"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "bogus",
    }
