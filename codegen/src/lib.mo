/// The compiler backend's library root -- bare `use codegen` resolves here.
///
/// Deliberately small: external consumers name the stage they need
/// (`codegen::emit`, `codegen::decls`, `codegen::test_driver`), and a hub
/// that mirrored the whole backend would be a second, always-stale index of
/// it. Only the pipeline entry points are re-exported.
pub use lib::emit {
    compile_db_module_with_debug, compile_loaded_modules_to_ir_with_debug,
}
