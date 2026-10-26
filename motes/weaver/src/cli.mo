/// Weaver's command line, declared once and parsed by the `Cli` derive.
///
/// The derive generates `spec_weavercli` / `decode_weavercli` /
/// `parse_weavercli` from the type below: long and short spellings
/// (`--provider` / `-p`), kebab-case longs (`--max-turns`, `--no-color`),
/// `--flag=value`, typed values (an `I64` option rejects a non-number at
/// PARSE time, with the flag named), and the built-in `--help` /
/// `--version`. There are no positionals -- an interactive entry reads
/// its tasks from stdin, so a bare word is a usage error.
///
/// The derived defs cannot be referenced from THIS module (the derive's
/// capture re-checks every non-`#[test]` def before the generated decls
/// exist), so the spec that adds the program name, about and version lives
/// in `cli_spec.mo`, and `main` runs it through `Cli.run` -- help/version
/// to stdout with exit 0, a usage error to stderr with exit 2.
use clap::args {*}

#[derive Cli]
pub type WeaverCli {
    weaver
        (#[opt {short := "p", help := "provider preset: ollama | mistral | openrouter | anthropic | mock"}] provider : Option String)
        (#[opt {short := "m", help := "model name; the provider's own list decides what exists"}] model : Option String)
        (#[opt {short := "", help := "total model-call budget for the session (default 100)"}] max_turns : Option I64)
        (#[opt {short := "r", help := "open a session id, a session directory, or a /save checkpoint"}] resume : Option String)
        (#[arg {short := "", long := "continue", help := "resume the newest session under the session root"}] cont : Bool)
        (#[arg {short := "", help := "no ANSI colors in the line UI"}] no_color : Bool)
        (#[opt {short := "", help := "mount an MCP server executable (repeatable)"}] mcp : List String),
}
