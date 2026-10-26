/// The browser REPL's worker channel, as Monad IO.
///
/// `Worker.run` posts the scratchpad source to `worker.js`, which
/// instantiates `try_engine.wasm` (a fresh instance per run) and posts the
/// result back. `Worker.poll` returns 0 idle, 1 running, 2 done, 3 timed
/// out, 4 failed; the field getters read the finished result. `Cancel`
/// terminates the worker immediately.
///
/// No promise re-enters wasm: the worker's `onmessage` only stores values
/// in the JS host, and the Oak UI polls on its animation-frame tick.
use lib::ffi {
  worker_cancel_raw, worker_error_raw, worker_notes_raw, worker_poll_raw,
  worker_run_raw, worker_status_raw, worker_type_raw, worker_value_raw
}

pub def Worker.run (source : String) : IO I64 := IO.mk (worker_run_raw source)

pub def Worker.poll : IO I64 := IO.mk worker_poll_raw

pub def Worker.status : IO String := IO.mk worker_status_raw

pub def Worker.value : IO String := IO.mk worker_value_raw

pub def Worker.typ : IO String := IO.mk worker_type_raw

pub def Worker.error : IO String := IO.mk worker_error_raw

pub def Worker.notes : IO String := IO.mk worker_notes_raw

pub def Worker.cancel : IO Unit := IO.mk worker_cancel_raw
