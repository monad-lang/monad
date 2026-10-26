/// The spec `main` parses against, and the one place that destructures the
/// parsed line.
///
/// These live here, not in `cli.mo`, because the derive's capture
/// re-checks and LOWERS every def in the expanded module before the
/// generated decls exist: a same-module consumer fails with "unbound
/// variable spec_<type>", and a same-module `match` on the type's own
/// constructor fails the capture's lowering with `UnknownInductive`. A
/// module loaded after `cli.mo` is the supported shape (motes/monadup's
/// `dispatch.mo` documents the same constraint).
use clap::spec {Cli.CommandSpec, Cli.with_about, Cli.with_name, Cli.with_version}
use weaver::cli {*}

/// The binary name, about line and version `--help`/`--version` report.
pub def weaver_cli_spec : Cli.CommandSpec :=
    Cli.with_about "an interactive coding agent on shuttle"
        (Cli.with_version "0.1.0" (Cli.with_name "weaver" spec_weavercli))

/// The version `--version` reports and the MCP client announces.
pub def WeaverCli.version : String := "0.1.0"

// The Plan layer's spelling: a flag is "" / none / false when absent, and
// these accessors are the one place that destructuring lives.

pub def WeaverCli.provider_text (c : WeaverCli) : String :=
    match c {
        WeaverCli.weaver provider _model _turns _resume _cont _no_color _mcp =>
            match provider {
                Option.none => "",
                Option.some p => p,
            },
    }

pub def WeaverCli.model_text (c : WeaverCli) : String :=
    match c {
        WeaverCli.weaver _provider model _turns _resume _cont _no_color _mcp =>
            match model {
                Option.none => "",
                Option.some m => m,
            },
    }

pub def WeaverCli.max_turns_of (c : WeaverCli) : Option I64 :=
    match c {
        WeaverCli.weaver _provider _model max_turns _resume _cont _no_color _mcp => max_turns,
    }

/// `--resume`'s value with absent spelled as "" (the Plan layer's own
/// convention, unchanged by the typed parse).
pub def WeaverCli.resume_text (c : WeaverCli) : String :=
    match c {
        WeaverCli.weaver _provider _model _turns resume _cont _no_color _mcp =>
            match resume {
                Option.none => "",
                Option.some r => r,
            },
    }

/// `--resume` was given at all, empty value included.
pub def WeaverCli.resume_asked (c : WeaverCli) : Bool :=
    match c {
        WeaverCli.weaver _provider _model _turns resume _cont _no_color _mcp =>
            match resume {
                Option.none => false,
                Option.some _ => true,
            },
    }

pub def WeaverCli.cont_of (c : WeaverCli) : Bool :=
    match c {
        WeaverCli.weaver _provider _model _turns _resume cont _no_color _mcp => cont,
    }

pub def WeaverCli.no_color_of (c : WeaverCli) : Bool :=
    match c {
        WeaverCli.weaver _provider _model _turns _resume _cont no_color _mcp => no_color,
    }

pub def WeaverCli.mcps (c : WeaverCli) : List String :=
    match c {
        WeaverCli.weaver _provider _model _turns _resume _cont _no_color mcp => mcp,
    }
