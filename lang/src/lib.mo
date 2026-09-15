// The lang mote's library root -- bare `use lang` resolves here.
//
// A deliberately small surface: the compiler pipeline's entry points, in
// pipeline order. Everything else is reached by naming the module it lives
// in (`use lang.codegen.emit {...}`), which is how the compiler's own
// modules import from each other and stays the norm -- a re-export hub that
// tried to mirror all of lang/ would be a second, always-stale index of it.
//
// No `{*}` globs here on purpose: a glob over a module this size pulls its
// whole namespace into every importer's scope, which is both slow and a
// name-collision hazard (see lang/src/scope.mo's note on the one real glob
// the corpus still has).

pub use lang.types {Decl, ModulePath, LocalScope}
pub use lang.parser {parse_all_decls}
pub use lang.module {
  ElaboratedModules, LoadedModules, ModuleInfo,
  check_file_cached, elaborate_loaded_modules, expand_check_paths, load_file_modules,
}
pub use lang.pretty {show_decls}
pub use lang.codegen.emit {compile_loaded_modules_to_ir_with_debug}
pub use llvm.ir {LLVMModule, emit_module}
