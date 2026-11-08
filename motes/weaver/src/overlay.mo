/// The modal dialog's stdin-ownership handshake. A dialog paints
/// directly to the terminal, outside the model's frame pipeline, so the
/// main loop must stop both reading stdin and drawing while one is open.
/// The dialog (on the turn's fiber) publishes `want`; the main loop's
/// `reads_input` acknowledges only after it has folded the poll that
/// marked the overlay open (so its last draw precedes the ack), then
/// polls without reading until the dialog publishes `want := false` and
/// a new `seq`. The loop's poll sees the new seq and forces a clear +
/// repaint, which erases the overlay.
use json::json {
    Json, Json.to_string, Json.parse, Json.make_object, Json.make_bool, Json.make_num_int,
    Json.get_object, Json.object_get, Json.get_bool, Json.get_num_i64, Json.get_num,
}
use std::map {Map, BTreeMap}
use std::path {Path, Path.to_string}
use std::io {IO.read_file, IO.write_file}
use std::process {process_id, exec_cmd}
use std::concurrent::combine {sleepIO}
use weaver::store {StoreState, Store.child}

pub struct OverlayState {
    want : Bool,
    ack : Bool,
    seq : I64,
}

pub def Overlay.default : OverlayState := { want := false, ack := false, seq := 0 }

/// The run's handshake file: the session store when one exists, else a
/// PID-qualified /tmp path (the usage.txt convention).
pub def Overlay.path (store : Option StoreState) : Path :=
    match store {
        Option.some s => Store.child s.dir "ui.json",
        Option.none =>
            Path.path (String.concat "/tmp/weaver-ui-"
                (String.concat (I64.to_string process_id) ".json")),
    }

pub def Overlay.serialize (s : OverlayState) : String :=
    Json.to_string (Json.make_object
        (Map.insert "want" (Json.make_bool s.want)
            (Map.insert "ack" (Json.make_bool s.ack)
                (Map.insert "seq" (Json.make_num_int s.seq) BTreeMap.empty))))

def want_of (o : Option Json) : Bool :=
    match o {
        Option.some j => match Json.get_bool j {
            Result.ok b => b,
            Result.err _ => false,
        },
        Option.none => false,
    }

def seq_of (o : Option Json) : I64 :=
    match o {
        Option.some j => match Json.get_num_i64 (Json.get_num j) {
            Result.ok n => n,
            Result.err _ => 0,
        },
        Option.none => 0,
    }

def parse_state (text : String) : Option OverlayState :=
    match Json.parse text {
        Result.err _ => Option.none,
        Result.ok j => match Json.get_object j {
            Result.err _ => Option.none,
            Result.ok obj =>
                let out : OverlayState := {
                    want := want_of (Json.object_get "want" obj),
                    ack := want_of (Json.object_get "ack" obj),
                    seq := seq_of (Json.object_get "seq" obj),
                } in
                Option.some out,
        },
    }

pub def Overlay.read (store : Option StoreState) : IO (Option OverlayState) := do {
    let r <- IO.read_file (Overlay.path store);
    return (match r {
        Result.err _ => Option.none,
        Result.ok text => parse_state text,
    })
}

pub def Overlay.write_state (store : Option StoreState) (s : OverlayState) : IO Unit := do {
    let _ <- IO.write_file (Overlay.path store) (Overlay.serialize s);
    IO.pure unit
}

/// Startup: no dialog, no history, no monitor.
pub def Overlay.reset (store : Option StoreState) : IO Unit := do {
    Overlay.monitor_close store;
    Overlay.write_state store Overlay.default
}

// ── the /tasks monitor's lock ───────────────────────────────────────────
// The monitor runs on the main loop (it opens mid-turn), outside the
// handshake above: the main loop is the one reading stdin. While its lock
// exists, a turn's dialog waits instead of reading stdin under it.

pub def Overlay.monitor_path (store : Option StoreState) : Path :=
    match store {
        Option.some s => Store.child s.dir "monitor.lock",
        Option.none =>
            Path.path (String.concat "/tmp/weaver-monitor-"
                (String.concat (I64.to_string process_id) ".lock")),
    }

pub def Overlay.monitor_open (store : Option StoreState) : IO Unit := do {
    let _ <- IO.write_file (Overlay.monitor_path store) "1";
    IO.pure unit
}

pub def Overlay.monitor_close (store : Option StoreState) : IO Unit := do {
    let _ <- exec_cmd "rm" ["-f", Path.to_string (Overlay.monitor_path store)];
    IO.pure unit
}

/// Wait (100 ms steps, one self-call) while the monitor is open.
#[partial]
pub def Overlay.wait_monitor (store : Option StoreState) : IO Unit := do {
    let r <- IO.read_file (Overlay.monitor_path store);
    let open_now : Bool := match r { Result.ok _ => true, Result.err _ => false };
    if open_now
    then do {
        let _ <- sleepIO 100;
        Overlay.wait_monitor store
    }
    else IO.pure unit
}

/// Whether the read gate acks a dialog: only while one wants stdin AND
/// the loop's model has already folded the open (so it draws no more
/// frames over the dialog).
pub def Overlay.should_ack (want : Bool) (overlay_open : Bool) : Bool :=
    Bool.and want overlay_open

/// The main loop's acknowledgement: set only while `want` is up and not
/// already acknowledged. Called from the loop's read gate, after the
/// model has folded the open poll.
pub def Overlay.ack (store : Option StoreState) : IO Unit := do {
    let cur <- Overlay.read store;
    let s : OverlayState := match cur { Option.some x => x, Option.none => Overlay.default };
    if Bool.and s.want s.ack
    then IO.pure unit
    else do {
        let _ <- Overlay.write_state store { s with ack := true };
        IO.pure unit
    }
}

/// The dialog's wait for the main loop to yield stdin: same `seq`, acked.
#[partial]
def wait_ack (store : Option StoreState) (seq : I64) (tries : I64) : IO Unit := do {
    if 100 < tries
    then IO.pure unit
    else do {
        let cur <- Overlay.read store;
        let acked : Bool := match cur {
            Option.some s => Bool.and s.ack (s.seq == seq),
            Option.none => false,
        };
        if acked
        then IO.pure unit
        else do {
            // A real sleep: `Terminal.poll` returns at once while stdin
            // holds bytes (a focus-regaining click, typed keys), which
            // burned the ~1 s budget in microseconds and let the dialog
            // paint while the main loop still drew and read.
            let _ <- sleepIO 10;
            wait_ack store seq (tries + 1);
        }
    }
}

/// The dialog opening: publish `want` and wait (bounded, ~1 s) for the
/// main loop to stop reading/drawing. A loop that never polls lets the
/// dialog proceed; the lost-wake hazard is the caller's documented risk.
pub def Overlay.begin (store : Option StoreState) : IO Unit := do {
    let cur <- Overlay.read store;
    let s : OverlayState := match cur { Option.some x => x, Option.none => Overlay.default };
    let want : OverlayState := { want := true, ack := false, seq := s.seq };
    let _ <- Overlay.write_state store want;
    wait_ack store s.seq 0
}

/// The dialog closing (confirm, cancel or EOF): release stdin and bump
/// the sequence so the main loop clears the overlay and repaints.
pub def Overlay.finish (store : Option StoreState) : IO Unit := do {
    let cur <- Overlay.read store;
    let s : OverlayState := match cur { Option.some x => x, Option.none => Overlay.default };
    let next : OverlayState := { want := false, ack := false, seq := s.seq + 1 };
    Overlay.write_state store next
}
