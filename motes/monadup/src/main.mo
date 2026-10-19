/// monadup's entry point.
use clap::args {*}
use lib::command {*}
use lib::platform {*}
use lib::shell {*}

def main (args : List String) : IO I64 := do {
    // The bash implementation announced an unrecognised machine before
    // dispatching any command; keep that so a fallback install says why.
    let uname <- Shell.uname_sm;
    let p : Platform.Resolution := Platform.of_uname uname;
    if p.used_fallback
    then IO.println (String.concat "monadup: note: " p.note)
    else return unit;
    Cli.run Command.setup args decode_command Command.dispatch
}
