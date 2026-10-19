// The monadup mote's library root. Every module below is pure or a thin IO
// boundary; `main.mo` is the binary target.
pub use lib::platform {*}
pub use lib::text {*}
pub use lib::layout {*}
pub use lib::release {*}
pub use lib::shell {*}
pub use lib::install {*}
pub use lib::scaffold {*}
pub use lib::doctor {*}
pub use lib::env_report {*}
pub use lib::command {*}
