// trellis's entry point.
//
//   trellis extract <mote>... [-o FILE] [--tests] [--no-docs] [--docs-base URL] [--verbose]
//   trellis serve <mote>... [--port N] [--host H] [--ui DIR] [--tests] [--no-docs] [--docs-base URL]
//
// `extract` writes the graph file (`trellis 3`, see trellis_ui's model.mo);
// `serve` extracts once and serves the browser UI with the graph. The UI is
// built by scripts/build-trellis-ui.sh into target-monad/trellis-ui.

use std::io {IO.println, IO.write_stderr, IO.write_file, IO.file_exists, IO.read_file, IO.tcp_listen_on, IO.tcp_accept}
use std::path {Path, Path.of, PathError, PathError.to_string}
use std::stream {FdStream, FdStream.set_timeout}
use std::concurrent::fiber {forkIO}
use clap::spec {
    Cli.ArgSpec, Cli.ArgValue, Cli.CommandSpec, Cli.Parsed, Cli.command, Cli.option_default, Cli.flag, Cli.flag_set,
    Cli.positional_multi, Cli.with_args, Cli.with_subcommands, Cli.with_version,
}
use clap::parse {Cli.run}
use http::types {Request, Response, Response.text, Response.with_header}
use moon::server {Server.serve_connection}
use moon::handler {Handler.try}
use moon::static_files {StaticConfig, StaticConfig.default, Static.handler}
use moon::static_cli {StaticCli.parse_port}
use oak_ui::theme {Ui.Theme.light, Ui.Theme.dark}
use oak_ui::css {Ui.css_reset, Ui.stylesheet_auto}
use std::map {HashMap}
use http::uri {Uri.parse_query}
use trellis_ui::model {Trellis.Graph, Trellis.Graph.encode, Trellis.ModuleNode}
use trellis_ui::smap {Smap.empty, Smap.insert, Smap.get}
use trellis_ui::seq {Seq.fold}
use trellis_ui::app {Trellis.css}
use lib::extract {Trellis.Extracted, Trellis.extract}
use lib::load {Trellis.Target, Trellis.Loaded, Trellis.find_target, Trellis.load}

// ═══ Arguments ═══

def common_args : List Cli.ArgSpec :=
    [Cli.flag "tests" "t" "also extract *_tests.mo files and tests/ directories",
        Cli.flag "no-docs" "n" "leave out doc comments (signatures stay; a smaller graph file)",
        Cli.option_default "docs-base" "d" "URL" "" "link each declaration to its docgen page under URL",
        Cli.positional_multi "motes"
            "the motes to extract (a directory with a mote.toml, or a workspace member's name)"]

def extract_spec : Cli.CommandSpec :=
    Cli.with_args
        (List.append
            [Cli.option_default "out" "o" "FILE" "graph.tsv" "where to write the graph (- for stdout)",
                Cli.flag "verbose" "v" "list every unresolved reference on stderr"]
            common_args)
        (Cli.command "extract" "Write the reference graph of the named motes")

def serve_spec : Cli.CommandSpec :=
    Cli.with_args
        (List.append
            [Cli.option_default "port" "p" "PORT" "8040" "port to listen on",
                Cli.option_default "host" "H" "HOST" "127.0.0.1" "address to bind",
                Cli.option_default "ui" "u" "DIR" "target-monad/trellis-ui"
                    "the built UI (scripts/build-trellis-ui.sh)"]
            common_args)
        (Cli.command "serve" "Extract the named motes and browse their graph")

def spec : Cli.CommandSpec :=
    Cli.with_subcommands [extract_spec, serve_spec]
        (Cli.with_version "0.1.0" (Cli.command "trellis" "Call graph visualizer for Monad code"))

struct Args {
    command : String,
    motes : List String,
    out : String,
    verbose : Bool,
    tests : Bool,
    no_docs : Bool,
    docs : String,
    port : String,
    host : String,
    ui : String,
}

def option_or (opts : List Cli.ArgValue) (name : String) (fallback : String) : String :=
    match opts {
        List.empty => fallback,
        List.cons o rest => if String.beq o.name name then o.value else option_or rest name fallback,
    }

def values (ps : List Cli.ArgValue) : List String := List.map (fn (p : Cli.ArgValue) => p.value) ps

def decode (p : Cli.Parsed) : Result String Args :=
    let motes : List String := values p.positionals in
    if List.is_empty motes then Result.err "name at least one mote: trellis extract <mote>..."
    else
        let a : Args :=
            { command := p.name, motes := motes, out := option_or p.options "out" "graph.tsv",
                verbose := Cli.flag_set "verbose" p, tests := Cli.flag_set "tests" p,
                no_docs := Cli.flag_set "no-docs" p,
                docs := option_or p.options "docs-base" "", port := option_or p.options "port" "8040",
                host := option_or p.options "host" "127.0.0.1",
                    ui := option_or p.options "ui" "target-monad/trellis-ui" } in
        Result.ok a

def trellis_fail (msg : String) : IO I64 := do {
    IO.write_stderr (String.concat_list ["trellis: ", msg, "\n"]);
    return 1
}

// ═══ Extraction ═══

def write_text (file : String) (text : String) : IO (Result String Unit) :=
    match Path.of file {
        Result.err e => IO.pure (Result.err (PathError.to_string e)),
        Result.ok p => do {
            let wrote <- IO.write_file p text;
            match wrote {
                Result.err _ => return (Result.err (String.concat "cannot write " file)),
                Result.ok _ => return (Result.ok unit),
            }
        },
    }

def exists (file : String) : IO Bool :=
    match Path.of file {
        Result.err _ => IO.pure false,
        Result.ok p => IO.file_exists p,
    }

#[partial]
def find_all (args : List String) (acc : List Trellis.Target) : IO (Result String (List Trellis.Target)) :=
    match args {
        List.empty => return (Result.ok (List.reverse acc)),
        List.cons a rest => do {
            let t <- Trellis.find_target a;
            match t {
                Result.err e => return (Result.err e),
                Result.ok target => find_all rest (List.cons target acc),
            }
        },
    }

#[terminating]
def report_lines (prefix : String) (xs : List String) : IO Unit :=
    match xs {
        List.empty => IO.pure unit,
        List.cons x rest => do {
            IO.write_stderr (String.concat_list [prefix, x, "\n"]);
            report_lines prefix rest
        },
    }

def summary (g : Trellis.Graph) : String :=
    String.concat_list [I64.to_string (List.length g.modules), " modules, ", I64.to_string (List.length g.decls),
        " declarations, ", I64.to_string (List.length g.edges), " edges; ", I64.to_string g.resolved, " of ",
        I64.to_string g.refs, " references resolved"]

/// Load and extract; parse failures are reported and skipped.
def build_graph (a : Args) : IO (Result String Trellis.Extracted) := do {
    let found <- find_all a.motes List.empty;
    match found {
        Result.err e => return (Result.err e),
        Result.ok targets => do {
            let loaded <- Trellis.load targets a.tests (Bool.not a.no_docs);
            report_lines "trellis: skipped: " loaded.errors;
            let roots : List String := List.map (fn (t : Trellis.Target) => t.name) targets;
            return (Result.ok (Trellis.extract roots a.docs loaded.sources))
        },
    }
}

def run_extract (a : Args) : IO I64 := do {
    let built <- build_graph a;
    match built {
        Result.err e => trellis_fail e,
        Result.ok x => do {
            if a.verbose then report_lines "trellis: unresolved: " (List.reverse x.unresolved) else IO.pure unit;
            let text : String := Trellis.Graph.encode x.graph;
            if String.beq a.out "-"
            then do {
                IO.println text;
                return 0
            }
            else do {
                let wrote <- write_text a.out text;
                match wrote {
                    Result.err e => trellis_fail e,
                    Result.ok _ => do {
                        IO.write_stderr (String.concat_list ["trellis: wrote ", a.out, ": ", summary x.graph, "\n"]);
                        return 0
                    },
                }
            }
        },
    }
}

// ═══ Serving ═══

// A browser fetches the page's files over several parallel keep-alive
// connections, so each connection gets its own fiber (the reason
// motes/oak_ui_book/scripts/serve.mo gives).

def idle_ms : I64 := 15000

def write_ms : I64 := 30000

def stylesheet : String := String.concat_list [Ui.stylesheet_auto Ui.Theme.light Ui.Theme.dark, Ui.css_reset, Trellis.css]

def typed (content_type : String) (body : String) : IO (Result String Response) :=
    IO.pure (Result.ok (Response.with_header "Content-Type" content_type (Response.text 200u16 body)))

/// What the server hands out besides the UI directory: the encoded graph,
/// the stylesheet, and each module's source file by module path.
struct Site {
    ui : String,
    graph : String,
    css : String,
    files : HashMap String String,
}

def not_found : IO (Result String Response) := IO.pure (Result.ok (Response.text 404u16 "Not Found"))

#[terminating]
def lookup_param (name : String) (ps : List (Pair String String)) : String :=
    match ps {
        List.empty => "",
        List.cons p rest => match p { Pair.pair k v => if String.beq k name then v else lookup_param name rest },
    }

def query_param (name : String) (query : Option String) : String :=
    match query { Option.none => "", Option.some q => lookup_param name (Uri.parse_query q) }

/// `/source?m=<module>`: the file of a module in the graph. The module is
/// looked up in the graph's own table, so the request names no path and
/// nothing outside the extracted modules is readable.
def source_of (files : HashMap String String) (module : String) : IO (Result String Response) :=
    match Smap.get module files {
        Option.none => not_found,
        Option.some file =>
            match Path.of file {
                Result.err _ => not_found,
                Result.ok p => do {
                    let text <- IO.read_file p;
                    match text {
                        Result.err _ => not_found,
                        Result.ok src => IO.pure (Result.ok (Response.with_header "Cache-Control" "max-age=300"
                            (Response.with_header "Content-Type" "text/plain; charset=utf-8"
                                (Response.text 200u16 src)))),
                    }
                },
            },
    }

def route (site : Site) (req : Request) : IO (Result String Response) :=
    let path : String := req.uri.path in
    if String.beq path "/graph.tsv" then typed "text/tab-separated-values; charset=utf-8" site.graph
    else if String.beq path "/trellis.css" then typed "text/css; charset=utf-8" site.css
    else if String.beq path "/source" then source_of site.files (query_param "m" req.uri.query)
    else Static.handler (StaticConfig.default site.ui) req

def handler (site : Site) : Request -> IO Response :=
    Handler.try (Response.text 500u16 "Internal Server Error") (route site)

def serve_socket (site : Site) (sock : FdStream) : IO Unit := do {
    let _ <- FdStream.set_timeout sock idle_ms write_ms;
    Server.serve_connection (handler site) sock List.empty 1
}

#[terminating]
def accept_loop (site : Site) (listener : FdStream) : IO I64 := do {
    let accepted <- IO.tcp_accept listener;
    match accepted {
        Result.err e => trellis_fail (String.concat "accept failed: " e.message),
        Result.ok sock => do {
            let _ <- forkIO (fn (_ : Unit) => serve_socket site sock);
            accept_loop site listener
        },
    }
}

def files_of (g : Trellis.Graph) : HashMap String String :=
    Seq.fold (fn (m : HashMap String String) (mo : Trellis.ModuleNode) =>
        if String.is_empty mo.file then m else Smap.insert mo.path mo.file m) Smap.empty g.modules

def run_serve (a : Args) : IO I64 := do {
    let has_ui <- exists (String.concat a.ui "/index.html");
    if Bool.not has_ui
    then trellis_fail (String.concat_list ["no UI at ", a.ui, "; build it with scripts/build-trellis-ui.sh"])
    else match StaticCli.parse_port a.port {
        Option.none => trellis_fail (String.concat "--port: not a port (1-65535): " a.port),
        Option.some port => do {
            let built <- build_graph a;
            match built {
                Result.err e => trellis_fail e,
                Result.ok x => do {
                    let site : Site := { ui := a.ui, graph := Trellis.Graph.encode x.graph, css := stylesheet,
                        files := files_of x.graph };
                    let listening <- IO.tcp_listen_on a.host port;
                    match listening {
                        Result.err e => trellis_fail (String.concat_list ["cannot listen on ", a.host, ":", a.port,
                            ": ", e.message]),
                        Result.ok listener => do {
                            IO.println (String.concat "trellis: " (summary x.graph));
                            IO.println (String.concat_list ["trellis: http://", a.host, ":", a.port,
                                "/  (Ctrl-C to stop)"]);
                            accept_loop site listener
                        },
                    }
                },
            }
        },
    }
}

def run (a : Args) : IO I64 :=
    if String.beq a.command "serve" then run_serve a else run_extract a

def main (args : List String) : IO I64 := Cli.run spec args decode run
