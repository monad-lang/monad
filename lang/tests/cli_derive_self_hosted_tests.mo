/// Self-hosted counterpart to `lang/tests/cli_derive_tests.mo` --
/// proves `derive_cli!` (the bare decl-macro form, not `#[derive_cli]`
/// attribute sugar) type-checks correctly through the SELF-HOSTED
/// checker (`lang/typecheck/macro_queue.mo`'s `expand_decls_graph` +
/// `lang/typecheck/meta_eval.mo`), the same way
/// `slow_tests/typecheck_std_tests.mo`'s `test_typecheck_std_derive_tests`
/// already proves for `std/derive.mo`'s four derives. `#[derive_cli]`
/// attribute-sugar dispatch (turning the attribute into a synthesized
/// `derive_cli!` call) is a separate, smaller, optional follow-up --
/// out of scope here; the bare form alone is enough to prove
/// `reflect_type_info!` evaluation works for `lang/cli.mo`'s own meta-
/// def too, not just `std/derive.mo`'s.
///
/// Listed in `slow_tests/typecheck_lang_tests.mo` (self-hosted
/// type-check corpus) -- unlike `cli_derive_tests.mo`, which is
/// deliberately Rust-host-only.
use lang.cli {*}

type DemoCommand {
    compile (path : String) (#[arg] verbose : Bool),
    pretty (path : String),
    help,
}

derive_cli! DemoCommand

#[test]
def test_derive_cli_self_hosted_compile_with_flag : Bool :=
    match parse_democommand ["compile", "a.mo", "--verbose"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.compile path verbose => path == "a.mo" && verbose == true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_self_hosted_compile_without_flag : Bool :=
    match parse_democommand ["compile", "a.mo"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.compile path verbose => path == "a.mo" && verbose == false,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_self_hosted_pretty : Bool :=
    match parse_democommand ["pretty", "b.mo"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.pretty path => path == "b.mo",
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_self_hosted_help : Bool :=
    match parse_democommand ["help"] {
        Result.ok cmd =>
            match cmd {
                DemoCommand.help => true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_self_hosted_unknown_subcommand : Bool :=
    match parse_democommand ["bogus"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "bogus",
    }
