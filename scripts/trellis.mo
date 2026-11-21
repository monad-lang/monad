// `trellis`: build the latest trellis and serve it for inspection.
//
//     monad script trellis
//     monad script trellis -- --mote std --port 9000
//     monad script trellis -- --no-build --no-docs
//
// Builds both halves from this checkout, then serves one mote's reference
// graph with the browser UI:
//   - the wasm UI (`motes/trellis_ui`) through scripts/build-trellis-ui.sh,
//     inside `nix develop` unless WASI_SDK_PATH is already set, into
//     target-monad/trellis-ui;
//   - the native `trellis` binary with `monad build motes/trellis --release`
//     into target-monad/trellis.
// `trellis serve` then extracts the mote's graph once and holds it in memory.
// `--no-build` serves what is already there, which is the quick way to look
// again after the first build. Ctrl-C stops the server.
//
// `MONAD` selects the compiler for both builds (default: `monad` on PATH).
// Every step runs from the checkout root: the UI build's `gen-web-js.sh`
// step resolves `web_wasm` against the working directory's workspace.

use clap::help {Cli.usage}
use clap::parse {Cli.parse}
use clap::spec {*}

use std::process {exec_cmd, Proc.capture, Proc.shell_quote}
use std::stream {FdStream, Stream}

struct TrellisScriptOptions {
    mote : String,
    port : String,
    host : String,
    ui : String,
    bin : String,
    tests : Bool,
    no_docs : Bool,
    docs : String,
    build : Bool,
}

instance Copy TrellisScriptOptions {
    def copy (o : TrellisScriptOptions) : Pair TrellisScriptOptions TrellisScriptOptions := Pair.pair o o
}

def trellis_script_defaults : TrellisScriptOptions :=
    { mote := "lang",
        port := "8047",
        host := "127.0.0.1",
        ui := "target-monad/trellis-ui",
        bin := "target-monad/trellis",
        tests := false,
        no_docs := false,
        docs := "",
        build := true }

// ─── Arguments ──────────────────────────────────────────────────────────

/// The command line, declared once through `clap`'s spec API. `monad script`
/// hands the script everything after `--`.
def trellis_script_spec : Cli.CommandSpec :=
    Cli.with_args
        [Cli.option_default "mote" "" "MOTE" "lang" "the mote to extract and browse"
            , Cli.option_default "port" "p" "PORT" "8047" "port to listen on"
            , Cli.option_default "host" "H" "HOST" "127.0.0.1" "address to bind"
            , Cli.option_default "ui" "" "DIR" "target-monad/trellis-ui" "where the wasm UI is built and served from"
            , Cli.option_default "bin" "" "FILE" "target-monad/trellis" "where the trellis binary is built"
            , Cli.flag "tests" "" "include the motes' #[test] declarations"
            , Cli.flag "no-docs" "" "leave doc comments out of the graph (signatures stay)"
            , Cli.option_optional "docs-base" "" "URL" "docs site base URL, for an Open in docs link"
            , Cli.flag "no-build" "" "serve what is already built"
        ]
        (Cli.command "trellis" "build the latest trellis and serve a mote's call graph")

#[terminating]
def trellis_fold_options (xs : List Cli.ArgValue) (o : TrellisScriptOptions) : TrellisScriptOptions :=
    match xs {
        List.empty => o,
        List.cons x rest =>
            match x {
                { name, value } =>
                    if String.beq name "mote" then trellis_fold_options rest { o with mote := value }
                    else if String.beq name "port" then trellis_fold_options rest { o with port := value }
                    else if String.beq name "host" then trellis_fold_options rest { o with host := value }
                    else if String.beq name "ui" then trellis_fold_options rest { o with ui := value }
                    else if String.beq name "bin" then trellis_fold_options rest { o with bin := value }
                    else if String.beq name "docs-base" then trellis_fold_options rest { o with docs := value }
                    else trellis_fold_options rest o,
            },
    }

#[terminating]
def trellis_fold_flags (xs : List String) (o : TrellisScriptOptions) : TrellisScriptOptions :=
    match xs {
        List.empty => o,
        List.cons x rest =>
            if String.beq x "tests" then trellis_fold_flags rest { o with tests := true }
            else if String.beq x "no-docs" then trellis_fold_flags rest { o with no_docs := true }
            else if String.beq x "no-build" then trellis_fold_flags rest { o with build := false }
            else trellis_fold_flags rest o,
    }

/// `Cli.Parsed` is affine, so it is destructured once and each list is
/// folded once, as in `scripts/bootstrap_next.mo`.
def trellis_options_of (p : Cli.Parsed) : TrellisScriptOptions :=
    match p {
        { flags, options, .. } => trellis_fold_flags flags (trellis_fold_options options trellis_script_defaults),
    }

// ─── Build ───────────────────────────────────────────────────────────────

/// The checkout's root, from git: the script may be started from anywhere.
def trellis_repo_root : IO (Result String String) := do {
    let r <- Proc.capture "git" ["rev-parse", "--show-toplevel"];
    match r {
        Pair.pair code text =>
            let dir : String := String.trim text in
            if I64.beq code 0 && Bool.not (String.is_empty dir)
            then IO.pure (Result.ok dir)
            else IO.pure (Result.err "not inside a git checkout (git rev-parse --show-toplevel failed)"),
    }
}

/// The compiler both builds use: `$MONAD`, else `monad` on PATH.
def trellis_monad : IO String := do {
    let m <- IO.get_env "MONAD";
    match m {
        Option.none => IO.pure "monad",
        Option.some v =>
            if String.is_empty v then IO.pure "monad" else IO.pure v,
    }
}

/// A path as written on the command line: a relative one is resolved against
/// the checkout root, an absolute one is left alone.
def trellis_at (root : String) (p : String) : String :=
    if String.starts_with "/" p then p else String.concat_list [root, "/", p]

/// The native tool. `--release`: extraction walks whole motes.
def trellis_build_bin (root : String) (monad : String) (bin : String) : IO I64 :=
    exec_cmd "sh" ["-c", String.concat_list
        ["cd ", Proc.shell_quote root, " && exec ", Proc.shell_quote monad,
            " build motes/trellis --release -o ", Proc.shell_quote bin]]

/// The browser UI, through the same script CI checks. The wasm toolchain is
/// only in `nix develop`, so when WASI_SDK_PATH is unset the build runs there.
def trellis_build_ui (root : String) (monad : String) (ui : String) : IO I64 := do {
    let inner : String :=
        String.concat_list
            ["cd ", Proc.shell_quote root, " && exec env MONAD=", Proc.shell_quote monad,
                " bash scripts/build-trellis-ui.sh ", Proc.shell_quote ui];
    let sdk <- IO.get_env "WASI_SDK_PATH";
    match sdk {
        Option.some _ => exec_cmd "sh" ["-c", inner],
        Option.none => do {
            IO.println "trellis: WASI_SDK_PATH is unset; building the UI inside `nix develop`";
            exec_cmd "nix"
                ["develop", String.concat root "#", "--no-pure-eval", "--accept-flake-config", "-c", "bash", "-c", inner]
        },
    }
}

// ─── Port ────────────────────────────────────────────────────────────────

// The port is checked before anything is built: a busy or invalid port
// should not cost a full build first. Parsing mirrors
// `motes/oak_ui_book/scripts/serve.mo` because there is no `I64 -> U16`.

def trellis_digit_of (i : I64) (ds : List U16) : U16 :=
    match ds {
        List.empty => 0u16,
        List.cons d rest => if I64.beq i 0 then d else trellis_digit_of (i - 1) rest,
    }

def trellis_digit_value (b : U8) : Option U16 :=
    if U8.lt b 48u8 || U8.lt 57u8 b then Option.none
    else Option.some (trellis_digit_of (U8.to_i64 b - 48) [0u16, 1u16, 2u16, 3u16, 4u16, 5u16, 6u16, 7u16, 8u16, 9u16])

/// A port in 1..65535. The I64 shadow catches overflow before the U16 wraps.
#[terminating]
def trellis_parse_port_go (bytes : List U8) (acc : U16) (wide : I64) : Option U16 :=
    match bytes {
        List.empty => if I64.lt 0 wide then Option.some acc else Option.none,
        List.cons b rest =>
            match trellis_digit_value b {
                Option.none => Option.none,
                Option.some d =>
                    let next_wide : I64 := wide * 10 + U8.to_i64 b - 48 in
                    if I64.lt 65535 next_wide then Option.none
                    else trellis_parse_port_go rest (U16.add (U16.mul acc 10u16) d) next_wide,
            },
    }

def trellis_parse_port (s : String) : Option U16 :=
    if String.is_empty s then Option.none else trellis_parse_port_go (String.to_list s) 0u16 0

/// Close the probe's socket, so the port is free again for the real server.
def trellis_close_probe (listener : FdStream) : IO (Option String) := do {
    let _ <- Stream.close listener;
    IO.pure Option.none
}

/// Bind the port to prove it is free, then close it again. Split into defs
/// because a `do` block with a bind cannot sit inside a match arm.
def trellis_probe_port (o : TrellisScriptOptions) (port : U16) : IO (Option String) := do {
    let bound <- IO.tcp_listen_on o.host port;
    match bound {
        Result.err _ => IO.pure (Option.some (String.concat_list
            ["cannot listen on ", o.host, ":", o.port, ": address already in use (pass --port N)"])),
        Result.ok listener => trellis_close_probe listener,
    }
}

/// `none` when the port can be bound; otherwise what to tell the user.
def trellis_port_problem (o : TrellisScriptOptions) : IO (Option String) := do {
    match trellis_parse_port o.port {
        Option.none => IO.pure (Option.some (String.concat "--port: not a port (1-65535): " o.port)),
        Option.some port => trellis_probe_port o port,
    }
}

// ─── Serve ───────────────────────────────────────────────────────────────

def trellis_serve_args (o : TrellisScriptOptions) (ui : String) : List String :=
    List.append ["serve", o.mote, "--port", o.port, "--host", o.host, "--ui", ui]
        (List.append (if o.tests then ["--tests"] else List.empty)
            (List.append (if o.no_docs then ["--no-docs"] else List.empty)
                (if String.is_empty o.docs then List.empty else ["--docs-base", o.docs])))

def trellis_build_then_serve (o : TrellisScriptOptions) (root : String) : IO I64 := do {
    let busy <- trellis_port_problem o;
    match busy {
        Option.some problem => do {
            IO.println (String.concat "trellis: " problem);
            IO.pure 1
        },
        Option.none => trellis_build_and_run o root,
    }
}

def trellis_build_and_run (o : TrellisScriptOptions) (root : String) : IO I64 := do {
    let monad <- trellis_monad;
    let ui : String := trellis_at root o.ui;
    let bin : String := trellis_at root o.bin;
    let code <-
        if o.build
        then do {
            IO.println (String.concat "trellis: building the native tool into " bin);
            let bin_code <- trellis_build_bin root monad bin;
            if Bool.not (I64.beq bin_code 0)
            then do {
                IO.println (String.concat "trellis: the native build failed with exit code " (I64.to_string bin_code));
                IO.pure bin_code
            }
            else do {
                IO.println (String.concat "trellis: building the browser UI into " ui);
                let ui_code <- trellis_build_ui root monad ui;
                if Bool.not (I64.beq ui_code 0)
                then do {
                    IO.println (String.concat "trellis: the UI build failed with exit code " (I64.to_string ui_code));
                    IO.pure ui_code
                }
                else IO.pure 0
            }
        }
        else IO.pure 0;
    if I64.beq code 0 then exec_cmd bin (trellis_serve_args o ui) else IO.pure code
}

def trellis_script_run (o : TrellisScriptOptions) : IO I64 := do {
    let root <- trellis_repo_root;
    match root {
        Result.err e => do {
            IO.println (String.concat "trellis: " e);
            IO.pure 1
        },
        Result.ok r => trellis_build_then_serve o r,
    }
}

def main (args : List String) : IO I64 :=
    match Cli.parse trellis_script_spec args {
        Cli.parse_ok parsed => trellis_script_run (trellis_options_of parsed),
        Cli.parse_help text => do { IO.println text; IO.pure 0 },
        Cli.parse_version text => do { IO.println text; IO.pure 0 },
        Cli.parse_err message => do {
            IO.println (String.concat "trellis: " message);
            IO.println (Cli.usage trellis_script_spec);
            IO.pure 2
        },
    }
