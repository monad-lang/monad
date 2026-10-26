// The /try page's wasm entry: the three exports every Oak app has
// (`motes/oak_wasm/src/program.mo`), plus a trivial `main` for the normal
// entry point.
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}
use lib::app {try_app, try_host}

#[export "c"]
def oak_mount : IO Unit := Runtime.mount try_app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick try_app try_host

def main : IO Unit := IO.pure unit
