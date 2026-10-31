// mty -- the Monad-native pty/TUI test harness.
//
// Test-support only: the harness spawns a binary under a pty and asserts on
// its rendered output. The FFI is compiled-backend only, so the tests that use
// it are self-hosted/LLVM-only and are gated (see src/weaver/support.mo).
//
// Test modules are deliberately NOT re-exported here: a test file reachable
// from the hub is undiscoverable by `monad test` (AGENTS.md).

pub use lib::spawn {SpawnConfig, Mty, Output}
pub use lib::ansi {Ansi.strip, Ansi.tight}
pub use lib::grid {Grid}
pub use lib::check {Check.report, Check.skip, Check.enabled, Check.value_set, Check.bin_path}
