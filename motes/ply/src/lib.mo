// The ply mote's library root -- bare `use ply` resolves here.
//
// One module so far, so this is thin by construction: the pure core's
// value types (the rope, selections, changes, the undo history and the
// editor mode). Later phases add the modules that operate on them
// (`rope.mo`, `selection.mo`, `history.mo`, `transaction.mo`, `keymap.mo`)
// and re-export them here by name, so a consumer (Weaver's approval diff, a
// future `monad-shell` line editor) gets the whole reusable core through
// this one import.
//
// No `{*}` globs -- the `motes/json/src/lib.mo` doctrine.

pub use lib::types {Rope, Selection, Selections, Change, Revision, History, Mode}
