/// `#[derive Cli]` demo for tui — forward-looking pattern, not real API.
///
/// tui itself has no CLI entry point yet (that is Phase 7 of the library's
/// design, `tui.mo`'s `run_app`). This file only exists to show the
/// `#[derive Cli]` pattern a *future application built on* tui would follow
/// in its own launch argument parser: one attribute on a subcommand type
/// generates a full `List String -> Result String TuiDemoCommand` parser,
/// dispatching on subcommand name, `#[arg]`-marked `Bool` fields as
/// `--flag`s, everything else as required positionals.
///
/// This is also the mote's only reason to depend on `clap`, and the whole of
/// that dependency. It used to name the `cli` mote instead, which dragged
/// `lang`/`llvm`/`runtime`/`build`/`lsp` in behind it.
use clap::args {*}

#[derive Cli]
type TuiDemoCommand {
    run (widget : String) (#[arg] fullscreen : Bool),
    version,
}

#[test]
def test_derive_cli_run_with_flag : Bool :=
    match parse_tuidemocommand ["run", "list", "--fullscreen"] {
        Result.ok cmd =>
            match cmd {
                TuiDemoCommand.run widget fullscreen => widget == "list" && fullscreen == true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_run_without_flag : Bool :=
    match parse_tuidemocommand ["run", "list"] {
        Result.ok cmd =>
            match cmd {
                TuiDemoCommand.run widget fullscreen => widget == "list" && fullscreen == false,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_version : Bool :=
    match parse_tuidemocommand ["version"] {
        Result.ok cmd =>
            match cmd {
                TuiDemoCommand.version => true,
                _ => false,
            },
        Result.err _ => false,
    }

#[test]
def test_derive_cli_unknown_subcommand : Bool :=
    match parse_tuidemocommand ["bogus"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "bogus",
    }

#[test]
def test_derive_cli_missing_positional : Bool :=
    match parse_tuidemocommand ["run"] {
        Result.ok _ => false,
        Result.err msg => String.contains msg "widget",
    }

#[test]
def test_derive_cli_empty_argv : Bool :=
    match parse_tuidemocommand [] {
        Result.ok _ => false,
        Result.err _ => true,
    }
