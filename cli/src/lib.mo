// The cli mote's library root -- bare `use cli` resolves here.
//
// Only the argv-parsing helpers are re-exported. `main.mo` is the binary
// entry point, not part of the library API: it is what `monad` runs, and
// nothing should `use` it except its own tests.

pub use lib::args {*}
