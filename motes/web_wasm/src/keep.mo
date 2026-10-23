/// The export-call state slot.
///
/// A wasm SPA is entered through `#[export "c"]` functions, whose ABI is
/// plain i64 words: no Monad value can be passed in or returned. So the
/// `Ref` holding a Program runtime is stashed in the JS host by the mount
/// export and read back by the dispatch/tick exports.
///
/// `Save` is deliberately untyped-looking: `Ref A` is one opaque heap word
/// at runtime and the JS side only stores it (it never dereferences,
/// compares or retains it), so the slot carries whatever `Ref` the caller
/// saved. `Load` has the same parameter, which the caller's use site fixes.

use std::ref {Ref}
use lib::ffi {keep_get_raw, keep_set_raw}

pub def Keep.save {A : Type} (r : Ref A) : IO Unit := IO.mk (keep_set_raw r)

pub def Keep.load {A : Type} : IO (Ref A) := IO.mk keep_get_raw
