// The /try engine's library surface. `main.mo` is the wasm ABI; the
// pipeline and the served-sources format live in their own modules so tests
// can import them without the exports.
pub use lib::pipeline {Outcome, run_source}
pub use lib::sources {SourceModule, identity_of_path, parse_sources}
