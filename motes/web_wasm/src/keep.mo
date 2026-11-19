/// The export-call state slot.
///
/// A wasm SPA is entered through `#[export "c"]` functions, whose ABI is
/// plain i64 words: no Monad value can be passed in or returned. So the
/// `Ref` holding a Program runtime is stashed in a runtime slot by the
/// mount export and read back by the dispatch/tick exports. The slot lives
/// in linear memory (`platform_web.c`), so the web collector treats the
/// kept `Ref` and everything it reaches as live.
///
/// `Save` is deliberately untyped-looking: `Ref A` is one opaque heap word
/// at runtime and the slot only stores it, so it carries whatever `Ref` the
/// caller saved. `Load` has the same parameter, which the caller's use site
/// fixes.

use std::ref {Ref}
use lib::ffi {keep_get_raw, keep_set_raw}

pub def Keep.save {A : Type} (r : Ref A) : IO Unit := IO.mk (keep_set_raw r)

pub def Keep.load {A : Type} : IO (Ref A) := IO.mk keep_get_raw
