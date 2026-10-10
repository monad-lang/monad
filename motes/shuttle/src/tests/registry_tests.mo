use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::registry {ToolRegistry}
use shuttle::message_types {Content}
use json::json {Json}
use init::transformers {ResultT}
use std::list {List.length}

def mk_tool (name : String) : ToolImpl :=
    { spec := { name := name, description := "", schema := Json.null }, run := fn j => ResultT.mk (return (Result.ok (Content.text name))) }

#[test]
def test_registry_lookup_found : Bool :=
    let reg := ToolRegistry.register (mk_tool "grep") ToolRegistry.empty in
    match ToolRegistry.lookup "grep" reg {
        Option.some _ => true,
        Option.none => false,
    }

#[test]
def test_registry_lookup_missing : Bool :=
    match ToolRegistry.lookup "grep" ToolRegistry.empty {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_registry_specs_count : Bool :=
    let reg := ToolRegistry.register (mk_tool "grep") (ToolRegistry.register (mk_tool "read") ToolRegistry.empty) in
    List.length (ToolRegistry.specs reg) == 2
