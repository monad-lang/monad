/// Tests moved out of `codegen::symbols` so the production module stays readable.

use std::list {List.intercalate}
use lang::types {
    Identifier, ModulePath, NamePath, show_module_path, show_name_path,
}
use std::map {}
use lang::name_text {unqualify_def_name}
use lib::symbols {ends_with_main}

#[test]
def test_ends_with_main_is_the_exact_source_name : Bool :=
    if Bool.not (ends_with_main "cli.main::main") then false
    else if Bool.not (ends_with_main "main") then false
    else if ends_with_main "cli.main::run_main" then false
    else if ends_with_main "codegen.emit::rename_main" then false
    else true
