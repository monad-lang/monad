// The clap mote's library root -- bare `use clap` resolves here.
//
// One module, so one re-export. Consumers normally name it directly
// (`use clap::args {*}`), which is what `#[derive Cli]`'s generated body
// needs in scope.

pub use lib::args {*}
