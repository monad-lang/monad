/// monadup's entry point.
use std::io {IO.write_stderr}
use clap::parse {Cli.run}
use lib::command {*}
use lib::dispatch {*}
use lib::platform {*}
use lib::shell {*}

def main (args : List String) : IO I64 := do {
    // The bash implementation announced an unrecognised machine before
    // dispatching any command; keep that so a fallback install says why.
    // stderr, not stdout: `doctor --json` and `env` write their reports to
    // stdout and must stay machine-readable.
    let uname <- Shell.uname_sm;
    let p : Platform.Resolution := Platform.of_uname (Option.get_or_default "" uname);
    if p.used_fallback
    then IO.write_stderr ("monadup: note: " ++ p.note ++ "\n")
    else return unit;
    let code <- Cli.run Command.setup args decode_command Command.dispatch;
    Shell.remove_self_bin;
    return code
}
