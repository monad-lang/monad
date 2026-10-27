// The ambient re-export hub for proofs/ (bare `proofs` resolves to this
// file, mirroring init/lib.mo and std/lib.mo).
//
// Deliberately EMPTY for now, and the reason is worth keeping: every
// candidate export so far lives in `src/checker/`, and `src/checker/`
// imports the compiler itself. Re-exporting any of it here would mean a
// `use lib` in a mathematical proof file pulled the whole 179-file
// `lang` closure in with it -- turning the cheap half of this mote into
// the expensive half.
//
// The cubical primitives' declarations moved to the prelude
// (`with Cubical { ... }` in init/src/prelude.mo); nothing under proofs/
// declares them any more. The mathematical proof modules (`paths`,
// `nat`, `list`, `vec` follow) get re-exported here as they land.

pub use lib::equiv {*}
pub use lib::paths {*}