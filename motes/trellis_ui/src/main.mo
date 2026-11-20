// The trellis UI's wasm entry: the three exports every Oak app has
// (`motes/oak_wasm/src/program.mo`) and the host that runs the app's
// effects -- starting a fetch (the graph, or a module's source) and polling
// it until the body is in.
//
// The graph file is `graph.tsv` beside the page; `trellis serve` provides
// it (and `trellis extract -o` writes one for any static server).

use oak::app {Host}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}
use web_wasm::fetch {Fetch.begin, Fetch.poll, Fetch.status, Fetch.read}
use web_wasm::types {RequestId}
use lib::app {Trellis.Model, Trellis.Msg, Trellis.Effect, Trellis.program, Trellis.source_url}

def graph_url : String := "graph.tsv"

def chunk : I64 := 1048576

/// Read the whole body: `Fetch.read` hands it over in chunks and answers
/// `""` once it is consumed.
#[partial]
def read_all (req : RequestId) (acc : List String) : IO String := do {
    let part <- Fetch.read req chunk;
    if String.is_empty part
    then IO.pure (String.concat_all (List.reverse acc))
    else read_all req (List.cons part acc)
}

/// What a finished (or pending) request turns into.
struct Replies {
    what : String,
    waiting : RequestId -> Trellis.Msg,
    done : String -> Trellis.Msg,
    failed : String -> Trellis.Msg,
}

/// Poll `req` once: still waiting, the body, or why it failed.
def poll_once (r : Replies) (req : RequestId) : IO (Option Trellis.Msg) := do {
    let state <- Fetch.poll req;
    if state == 0
    then IO.pure (Option.some (r.waiting req))
    else if state == 1
    then do {
        let status <- Fetch.status req;
        if status == 200
        then do {
            let body <- read_all req List.empty;
            IO.pure (Option.some (r.done body))
        }
        else IO.pure (Option.some (r.failed (String.concat_list [r.what, ": HTTP ", I64.to_string status])))
    }
    else IO.pure (Option.some (r.failed (String.concat r.what ": the request failed")))
}

def graph_replies : Replies :=
    { what := graph_url, waiting := fn (req : RequestId) => Trellis.Msg.fetch_started req,
        done := fn (body : String) => Trellis.Msg.loaded body, failed := fn (why : String) => Trellis.Msg.failed why }

def source_replies (module : String) : Replies :=
    { what := Trellis.source_url module, waiting := fn (req : RequestId) => Trellis.Msg.source_started module req,
        done := fn (body : String) => Trellis.Msg.source_loaded module body,
        failed := fn (why : String) => Trellis.Msg.source_failed module why }

def run_effect (e : Trellis.Effect) : IO (Option Trellis.Msg) :=
    match e {
        Trellis.Effect.fx_fetch url => do {
            let req <- Fetch.begin url 0 "";
            IO.pure (Option.some (Trellis.Msg.fetch_started req))
        },
        Trellis.Effect.fx_poll req => poll_once graph_replies req,
        Trellis.Effect.fx_fetch_source module url => do {
            let req <- Fetch.begin url 0 "";
            IO.pure (Option.some (Trellis.Msg.source_started module req))
        },
        Trellis.Effect.fx_poll_source module req => poll_once (source_replies module) req,
    }

def trellis_host : Host IO Trellis.Effect Trellis.Msg := Host.host run_effect

#[export "c"]
def oak_mount : IO Unit := Runtime.mount (Trellis.program graph_url)

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick (Trellis.program graph_url) trellis_host

def main : IO Unit := IO.pure unit
