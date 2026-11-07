/// moon's entry point: `moon static [DIR] [--port N] [--host H]`.
///
/// A preview server for a directory of built files — the replacement for
/// `python3 -m http.server` in `docs-serve`. The file serving itself is
/// `static_files.mo` (MIME, ETag, ranges, traversal guard, `index.html`).
use std::io {IO.write_stderr}
use clap::parse {Cli.run}
use lib::server {Server.serve_static}
use lib::static_cli {StaticCli, StaticCli.decode, StaticCli.spec}
use lib::static_files {StaticConfig, StaticConfig.default}

def report (msg : String) : IO I64 := do {
    IO.write_stderr (String.concat "moon: " (String.concat msg "\n"));
    return 1
}

def run (cli : StaticCli) : IO I64 := do {
    let served <- Server.serve_static (StaticConfig.default cli.dir) cli.host cli.port;
    match served {
        Result.err e => report e,
        Result.ok _ => return 0,
    }
}

def main (args : List String) : IO I64 :=
    Cli.run StaticCli.spec args StaticCli.decode run
