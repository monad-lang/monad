// `serve`: build the explorer, then serve it with moon.
//
//     cd motes/oak_ui_book && monad script serve
//     monad script serve -- --port 9000 --no-build
//
// Builds through `scripts/build-oak-ui-book.sh` (the same build CI checks),
// inside `nix develop` unless `WASI_SDK_PATH` says the wasm toolchain is
// already present, then serves the output directory on 127.0.0.1 with
// moon's static handler (byte-exact `.wasm` with `application/wasm`, ETags,
// path-traversal guard), one fiber per connection. Ctrl-C stops it.
//
// Options:
//   --port N      listen on port N (default 8000)
//   --host H      bind address (default 127.0.0.1)
//   --out DIR     build into and serve DIR (default target-monad/oak-ui-book)
//   --no-build    serve the existing output without rebuilding

use std::process {exec_cmd, Proc.capture, Proc.shell_quote}
use std::io {IO.get_env, IO.tcp_listen_on, IO.tcp_accept}
use std::stream {FdStream, FdStream.set_timeout, StreamError}
use std::concurrent::fiber {forkIO}
use http::types {Request, Response, Response.text}
use moon::server {Server.serve_connection}
use moon::handler {Handler.try}
use moon::static_files {StaticConfig, StaticConfig.default, Static.handler}

struct ServeOpts {
    port : U16,
    port_text : String,
    host : String,
    out : String,
    build : Bool
}

instance Copy ServeOpts {
    def copy (o : ServeOpts) : Pair ServeOpts ServeOpts := Pair.pair o o
}

def default_opts : ServeOpts :=
    { port := 8000u16, port_text := "8000", host := "127.0.0.1", out := "", build := true }

// ═══ Arguments ═══

def digit_value (b : U8) : Option U16 :=
    if U8.lt b 48u8 || U8.lt 57u8 b then Option.none
    else Option.some (digit_of (U8.to_i64 b - 48) [0u16, 1u16, 2u16, 3u16, 4u16, 5u16, 6u16, 7u16, 8u16, 9u16])

#[terminating]
def digit_of (i : I64) (ds : List U16) : U16 :=
    match ds {
        List.empty => 0u16,
        List.cons d rest => if I64.beq i 0 then d else digit_of (i - 1) rest,
    }

/// A port in 1..65535. The I64 shadow catches overflow before the U16 wraps.
#[terminating]
def parse_port_go (bytes : List U8) (acc : U16) (wide : I64) : Option U16 :=
    match bytes {
        List.empty => if I64.lt 0 wide then Option.some acc else Option.none,
        List.cons b rest =>
            match digit_value b {
                Option.none => Option.none,
                Option.some d =>
                    let next_wide : I64 := wide * 10 + U8.to_i64 b - 48 in
                    if I64.lt 65535 next_wide then Option.none
                    else parse_port_go rest (U16.add (U16.mul acc 10u16) d) next_wide,
            },
    }

def parse_port (s : String) : Option U16 :=
    if String.is_empty s then Option.none else parse_port_go (String.to_list s) 0u16 0

#[terminating]
def parse_args (args : List String) (o : ServeOpts) : Result String ServeOpts :=
    match args {
        List.empty => Result.ok o,
        List.cons a rest =>
            if String.beq a "--no-build" then parse_args rest { o with build := false }
            else if String.beq a "--port" || String.beq a "--host" || String.beq a "--out"
            then parse_valued a rest o
            else if String.beq a "--" then parse_args rest o
            else Result.err (String.concat "unknown argument: " a),
    }

#[terminating]
def parse_valued (flag : String) (rest : List String) (o : ServeOpts) : Result String ServeOpts :=
    match rest {
        List.empty => Result.err (String.concat flag " needs a value"),
        List.cons v more =>
            if String.beq flag "--host" then parse_args more { o with host := v }
            else if String.beq flag "--out" then parse_args more { o with out := v }
            else
                match parse_port v {
                    Option.some p => parse_args more { o with port := p, port_text := v },
                    Option.none => Result.err (String.concat "not a port (1-65535): " v),
                },
    }

// ═══ Build ═══

/// The checkout's root, from git (the script may run from any directory).
def repo_root : IO (Result String String) := do {
    let r <- Proc.capture "git" ["rev-parse", "--show-toplevel"];
    match r {
        Pair.pair code text =>
            let dir : String := String.trim text in
            if I64.beq code 0 && Bool.not (String.is_empty dir)
            then IO.pure (Result.ok dir)
            else IO.pure (Result.err "not inside a git checkout (git rev-parse --show-toplevel failed)"),
    }
}

/// Runs the build script, wrapped in `nix develop` unless the wasm
/// toolchain is already in the environment. Returns its exit code.
///
/// The build runs FROM the repo root: `monad script` starts in the mote's
/// directory, and from there the build's `examples/gen_web_js.mo` step
/// cannot resolve `web_wasm` (an `examples/` file takes its closure from
/// the working directory's workspace lookup).
def build (root : String) (out : String) : IO I64 := do {
    let cmd : String :=
        String.concat_list
            ["cd ", Proc.shell_quote root, " && exec bash scripts/build-oak-ui-book.sh ", Proc.shell_quote out];
    let sdk <- IO.get_env "WASI_SDK_PATH";
    match sdk {
        Option.some _ => exec_cmd "bash" ["-c", cmd],
        Option.none => do {
            IO.println "serve: WASI_SDK_PATH is unset; building inside `nix develop`";
            exec_cmd "nix"
                ["develop", String.concat root "#", "--no-pure-eval", "--accept-flake-config", "-c", "bash", "-c", cmd]
        },
    }
}

// ═══ Serve ═══

// A browser fetches the page's subresources (web.js, the wasm, the CSS) over
// several parallel connections and keeps each one alive. moon's sequential
// `Server.run` serves one connection at a time, so the second connection
// waited out the first one's keep-alive and the explorer never loaded. Each
// connection therefore gets its own fiber here, and the loop goes straight
// back to `accept`.

/// Idle and write timeouts per connection, so an abandoned keep-alive
/// connection does not hold its fiber forever.
def idle_ms : I64 := 15000

def write_ms : I64 := 30000

def handler (dir : String) : Request -> IO Response :=
    Handler.try (Response.text 500u16 "Internal Server Error") (Static.handler (StaticConfig.default dir))

def serve_socket (dir : String) (sock : FdStream) : IO Unit := do {
    let _ <- FdStream.set_timeout sock idle_ms write_ms;
    Server.serve_connection (handler dir) sock List.empty 1
}

#[terminating]
def accept_loop (dir : String) (listener : FdStream) : IO I64 := do {
    let accepted <- IO.tcp_accept listener;
    match accepted {
        Result.err e => do {
            IO.println (String.concat "serve: accept failed: " e.message);
            IO.pure 1
        },
        Result.ok sock => do {
            let _ <- forkIO (fn (_ : Unit) => serve_socket dir sock);
            accept_loop dir listener
        },
    }
}

def serve (o : ServeOpts) (dir : String) : IO I64 := do {
    let listening <- IO.tcp_listen_on o.host o.port;
    match listening {
        Result.err e => do {
            IO.println (String.concat_list ["serve: cannot listen on ", o.host, ":", o.port_text, ": ", e.message]);
            IO.pure 1
        },
        Result.ok listener => do {
            IO.println (String.concat_list ["serve: http://", o.host, ":", o.port_text, "/  (explorer)"]);
            IO.println (String.concat_list ["serve: http://", o.host, ":", o.port_text, "/gallery/  (static gallery)"]);
            IO.println (String.concat_list ["serve: serving ", dir, "; Ctrl-C to stop"]);
            accept_loop dir listener
        },
    }
}

def build_then_serve (o : ServeOpts) (root : String) : IO I64 := do {
    let dir : String := if String.is_empty o.out then String.concat root "/target-monad/oak-ui-book" else o.out;
    if o.build
    then do {
        let code <- build root dir;
        if I64.beq code 0 then serve o dir
        else do {
            IO.println (String.concat "serve: build failed with exit code " (I64.to_string code));
            IO.pure code
        }
    }
    else serve o dir
}

def main (args : List String) : IO I64 :=
    match parse_args args default_opts {
        Result.err e => do {
            IO.println (String.concat "serve: " e);
            IO.println "usage: monad script serve [-- --port N] [--host H] [--out DIR] [--no-build]";
            IO.pure 2
        },
        Result.ok o => do {
            let root <- repo_root;
            match root {
                Result.err e => do {
                    IO.println (String.concat "serve: " e);
                    IO.pure 1
                },
                Result.ok r => build_then_serve o r,
            }
        },
    }
