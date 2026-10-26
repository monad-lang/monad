/// The derived command line: the shapes clap's `#[derive Cli]` gives
/// weaver (long/short, kebab-case, `--flag=value`, typed values, the
/// built-in help/version) and the errors a bad invocation gets. The spec
/// is `cli_spec.mo`'s, the parse is the derive's.
use clap::parse {Cli.parse, Cli.version_text}
use clap::spec {Cli.ParseResult}
// Wildcard: `parse_weavercli` is macro-generated, and a named
// import of one does not resolve in the self-hosted loader.
use weaver::cli {*}
use weaver::cli_spec {
    weaver_cli_spec, WeaverCli.provider_text, WeaverCli.model_text, WeaverCli.max_turns_of,
    WeaverCli.resume_text, WeaverCli.resume_asked, WeaverCli.cont_of, WeaverCli.no_color_of,
    WeaverCli.mcps,
}
use std::list {List.length}

#[test]
def test_cli_defaults_are_unset : Bool :=
    match parse_weavercli [] {
        Result.err _ => false,
        Result.ok c =>
            String.is_empty (WeaverCli.provider_text c)
                && String.is_empty (WeaverCli.model_text c)
                && (match WeaverCli.max_turns_of c { Option.none => true, Option.some _ => false })
                && Bool.not (WeaverCli.resume_asked c)
                && Bool.not (WeaverCli.cont_of c)
                && Bool.not (WeaverCli.no_color_of c)
                && List.length (WeaverCli.mcps c) == 0,
    }

#[test]
def test_cli_every_flag : Bool :=
    match parse_weavercli [
        "--provider", "anthropic", "-m", "claude-opus-5", "--max-turns", "7",
        "-r", "s-9", "--continue", "--no-color", "--mcp", "a", "--mcp", "b",
    ] {
        Result.err _ => false,
        Result.ok c =>
            String.beq (WeaverCli.provider_text c) "anthropic"
                && String.beq (WeaverCli.model_text c) "claude-opus-5"
                && Option.get_or_default 0 (WeaverCli.max_turns_of c) == 7
                && String.beq (WeaverCli.resume_text c) "s-9"
                && WeaverCli.resume_asked c
                && WeaverCli.cont_of c
                && WeaverCli.no_color_of c
                && List.length (WeaverCli.mcps c) == 2,
    }

/// `--max-turns` is typed: the parse names the flag rather than letting a
/// bad value fall through as "absent".
#[test]
def test_cli_rejects_a_non_numeric_max_turns : Bool :=
    match parse_weavercli ["--max-turns", "nope"] {
        Result.ok _ => false,
        Result.err m => String.contains m "max-turns" && String.contains m "integer",
    }

/// There are no positionals: an interactive entry reads stdin.
#[test]
def test_cli_rejects_a_positional : Bool :=
    match parse_weavercli ["stray"] {
        Result.ok _ => false,
        Result.err m => String.contains m "unexpected argument",
    }

#[test]
def test_cli_requires_a_value : Bool :=
    match parse_weavercli ["--resume"] {
        Result.ok _ => false,
        Result.err m => String.contains m "requires a value",
    }

#[test]
def test_cli_long_equals_form : Bool :=
    match parse_weavercli ["--provider=ollama", "--max-turns=12"] {
        Result.err _ => false,
        Result.ok c =>
            String.beq (WeaverCli.provider_text c) "ollama"
                && Option.get_or_default 0 (WeaverCli.max_turns_of c) == 12,
    }

/// The spec's help names the binary, the options and the built-ins.
#[test]
def test_cli_help_text : Bool :=
    match Cli.parse weaver_cli_spec ["--help"] {
        Cli.ParseResult.parse_help text =>
            String.contains text "weaver"
                && String.contains text "--provider"
                && String.contains text "--max-turns"
                && String.contains text "--continue"
                && String.contains text "--mcp"
                // the label/help separator survives the widest label
                && String.contains text "--max-turns <VALUE> ",
        _ => false,
    }

#[test]
def test_cli_version_text : Bool :=
    String.beq (Cli.version_text weaver_cli_spec) "weaver 0.1.0"
        && (match Cli.parse weaver_cli_spec ["--version"] {
            Cli.ParseResult.parse_version text => String.contains text "0.1.0",
            _ => false,
        })
