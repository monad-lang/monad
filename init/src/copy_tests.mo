/// Tests for `init/src/copy.mo`.
///
/// A separate file because `copy.mo` is in the Rust host's default
/// module set (`core/src/term/module.rs`'s `default_module_source_files`),
/// seeded ambiently into every module closure -- `is_default_module_file`
/// (`core/src/lib.rs`) then filters it out of every Rust-hosted test path
/// (`monad-rs test`, the MCP test tool, the LSP's run-tests code lens), so
/// a `#[test]` inside it is silently never run there. Same reason
/// `std/src/path_tests.mo`/`process_tests.mo` are separate from their
/// ambiently re-exported siblings. The self-hosted `monad test` is
/// unaffected -- its driver has no equivalent default-module filter --
/// but these still move out so every test path agrees.
use init::copy {Copy}

#[test]
def test_copy_i64_duplicates : Bool :=
    match Copy.copy 7 {
        Pair.pair a b => I64.beq a 7 && I64.beq b 7,
    }

#[test]
def test_copy_bool_duplicates : Bool :=
    match Copy.copy true {
        Pair.pair a b => a && b,
    }
