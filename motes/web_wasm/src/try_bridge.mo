/// The /try engine's result channel, in Monad terms.
///
/// The engine (`motes/try_engine`) is a separate wasm module with no DOM;
/// its only browser import is this push. The UI polls the JS host copy on
/// its animation-frame tick, so nothing here is asynchronous.
use lib::ffi {try_result_raw}

pub def TryBridge.push_result (status : I64) (value : String) (typ : String)
    (error : String) (notes : String) : IO Unit :=
    IO.mk (try_result_raw status value typ error notes)
