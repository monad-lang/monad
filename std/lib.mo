// The ambient re-export hub for std/ (bare `std` resolves to this
// file, see AGENTS.md's "init vs std" section) -- mirrors init/lib.mo's
// own `pub use submodule {*}` pattern exactly.

// Qualified (not bare `pub use path {*}`/etc): see std/io.mo's own doc
// comment for why -- the Rust reference registers these siblings under
// their full `std.<name>` path, with no base-dir-relative fallback.
pub use std.path {*}
pub use std.io {*}
pub use std.process {*}
