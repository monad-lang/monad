/// The checked-in `fixtures/cfg/` workspaces: `on` declares
/// `[features] default = ["on"]`, `off` declares the same feature but not
/// in `default`. Both hold the same source, so which declaration survives
/// is decided only by the owning mote's manifest.
///
/// Separate from `cfg_tests.mo` because these read the fixture through the
/// loader's own manifest discovery (`cfg_env_for_file`), which is the one
/// part of the path a pure `CfgEnv` table cannot stand in for.

use std::path {Path}
use std::stream {StreamError}
use std::list {List.intercalate}
use parsec::core {ParseResult.fail, ParseResult.success}
use lang::types {Decl, show_name_path}
use lang::parser {decls_parser_located_cfg}
use lib::module {cfg_env_for_file}

def label (d : Decl) : String :=
    match d {
        Decl.def_d df => show_name_path df.name,
        _ => "?",
    }

def survivors (dir : String) : IO String := do {
    let path : String := String.concat dir "/src/main.mo";
    let read : Result StreamError String <- IO.read_file (Path.path path);
    match read {
        Result.ok source => do {
            let env <- cfg_env_for_file path source;
            match decls_parser_located_cfg env source {
                success _ ds => return (List.intercalate "," (List.map label ds)),
                fail _ => return "<fail>",
            }
        },
        Result.err _ => do { return "<unreadable>" }
    }
}

#[test]
def test_fixture_default_on : IO Bool := do {
    let got <- survivors "fixtures/cfg/on";
    return (String.beq got "on_only")
}

#[test]
def test_fixture_default_off : IO Bool := do {
    let got <- survivors "fixtures/cfg/off";
    return (String.beq got "off_only")
}
