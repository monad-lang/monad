/// Two-phase fetch. `begin` starts the request; `poll` answers
/// 0 = pending, 1 = done, 2 = failed; then `status`/`read` inspect it.
///
/// Two phases, deliberately: a JS promise callback must not re-enter wasm
/// while a Monad frame is on the stack. The Monad side drives `poll` from
/// its own frame loop.

use lib::types {RequestId}
use lib::ffi {fetch_begin_raw, fetch_poll_raw, fetch_status_raw, fetch_read_raw}

pub def Fetch.begin (url : String) (method : I64) (body : String) : IO RequestId :=
  IO.mk (fetch_begin_raw url method body)

pub def Fetch.poll (r : RequestId) : IO I64 := IO.mk (fetch_poll_raw r)

pub def Fetch.status (r : RequestId) : IO I64 := IO.mk (fetch_status_raw r)

pub def Fetch.read (r : RequestId) (max : I64) : IO String := IO.mk (fetch_read_raw r max)
