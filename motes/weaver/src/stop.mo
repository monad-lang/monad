/// The per-run cooperative stop signal. Esc writes it from the UI; the
/// turn's `RunState.should_stop` seam reads it before a model call and
/// after one (before tools dispatch). A generation number guards against
/// a stale request from an earlier turn or process: only the matching
/// turn's predicate fires.
use json::json {
    Json, Json.to_string, Json.parse, Json.make_object, Json.make_num_int, Json.make_bool,
    Json.get_object, Json.object_get, Json.get_num_i64, Json.get_num, Json.get_bool,
}
use std::map {Map, BTreeMap}
use std::path {Path}
use std::io {IO.read_file, IO.write_file}
use std::process {process_id}
use weaver::store {StoreState, Store.child}

pub struct StopState {
    gen : I64,
    stop : Bool,
}

pub def Stop.default : StopState := { gen := 0, stop := false }

/// The run's signal file: the session store when one exists, else a
/// PID-qualified /tmp path (the usage.txt convention).
pub def Stop.path (store : Option StoreState) : Path :=
    match store {
        Option.some s => Store.child s.dir "stop.txt",
        Option.none =>
            Path.path (String.concat "/tmp/weaver-stop-"
                (String.concat (I64.to_string process_id) ".txt")),
    }

pub def Stop.serialize (s : StopState) : String :=
    Json.to_string (Json.make_object
        (Map.insert "gen" (Json.make_num_int s.gen)
        (Map.insert "stop" (Json.make_bool s.stop) BTreeMap.empty)))

def gen_of (o : Option Json) : I64 :=
    match o {
        Option.some j => match Json.get_num_i64 (Json.get_num j) {
            Result.ok n => n,
            Result.err _ => 0,
        },
        Option.none => 0,
    }

def stop_of (o : Option Json) : Bool :=
    match o {
        Option.some j => match Json.get_bool j {
            Result.ok b => b,
            Result.err _ => false,
        },
        Option.none => false,
    }

def parse_state (text : String) : Option StopState :=
    match Json.parse text {
        Result.err _ => Option.none,
        Result.ok j => match Json.get_object j {
            Result.err _ => Option.none,
            Result.ok obj =>
                let out : StopState := {
                    gen := gen_of (Json.object_get "gen" obj),
                    stop := stop_of (Json.object_get "stop" obj),
                } in
                Option.some out,
        },
    }

pub def Stop.read (store : Option StoreState) : IO (Option StopState) := do {
    let r <- IO.read_file (Stop.path store);
    return (match r {
        Result.err _ => Option.none,
        Result.ok text => parse_state text,
    })
}

pub def Stop.write (store : Option StoreState) (gen : I64) (stop : Bool) : IO Unit := do {
    let s : StopState := { gen := gen, stop := stop };
    let _ <- IO.write_file (Stop.path store) (Stop.serialize s);
    IO.pure unit
}

/// Startup: no request, no generation.
pub def Stop.reset (store : Option StoreState) : IO Unit :=
    Stop.write store 0 false

/// The UI's request for the turn with generation `gen`.
pub def Stop.request (store : Option StoreState) (gen : I64) : IO Unit :=
    Stop.write store gen true

/// The turn's predicate: true only for its OWN generation and a set flag.
pub def Stop.predicate (store : Option StoreState) (gen : I64) : Unit -> IO Bool :=
    fn (_ : Unit) => do {
        let cur <- Stop.read store;
        return (match cur {
            Option.some s => Bool.and s.stop (s.gen == gen),
            Option.none => false,
        })
    }
