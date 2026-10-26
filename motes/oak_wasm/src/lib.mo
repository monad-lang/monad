// The oak_wasm mote's library root -- bare `use oak_wasm` resolves here.
//
// The browser runtime for an Oak `Program`: `Patch` (pure diff + DOM apply)
// and `Runtime` (mount/dispatch/tick). An app exposes it through three
// `#[export "c"]` thunks and calls `Runtime.mount`/`Runtime.dispatch`/
// `Runtime.tick`; see `fixtures/wasm/oak_spa.mo`.

pub use lib::patch {
    Patch, Patch.diff, Patch.apply, Patch.clear, Patch.mount_node,
    Patch.resolve, Patch.set_attribute,
    Patch.hydrate, Patch.hydrate_root, Patch.insert_at,
}

pub use lib::program {
    Runtime.mount, Runtime.dispatch, Runtime.tick,
    Runtime.run_batch, RuntimeState,
}
