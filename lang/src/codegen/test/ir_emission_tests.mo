// Formerly held `get_module_symbol_names` / `ir_contains_symbol` plus their
// name-extraction helpers (`get_function_name`/`get_global_name`/
// `get_declaration_name`/`extract_names`) — the whole cluster was unused
// (no callers in the codebase) and has been removed. This file is kept
// (empty) because `core/src/core_check_module.rs`'s
// `test_real_file_lang_codegen_test_ir_emission_tests` includes it via
// `include_str!`; deleting the file would break that build.