/// The approval pick's display: a write/edit must name the file it is
/// about to change, not bury the path inside a truncated JSON dump.
use weaver::gate {pick_header, pick_target}
use shuttle::gate {Capability, Pick}
use json::json {Json, Json.make_object, Json.make_str}
use std::map {Map, BTreeMap}

def tool_input (path : String) : Json :=
    Json.make_object (Map.insert "path" (Json.make_str path)
        (Map.insert "content" (Json.make_str "hello") BTreeMap.empty))

def write_pick (path : String) : Pick :=
    { name := "write", cap := Capability.write, input := tool_input path }

#[test]
def test_pick_target_reads_the_path_field : Bool :=
    match pick_target (write_pick "/tmp/weaver-gate/a.mo") {
        Option.some path => path == "/tmp/weaver-gate/a.mo",
        Option.none => false,
    }

#[test]
def test_pick_header_names_the_file : Bool :=
    let p : Pick := write_pick "/tmp/weaver-gate/target.mo" in
    String.contains (pick_header p) "/tmp/weaver-gate/target.mo"

/// A tool whose input names no path keeps the JSON summary.
#[test]
def test_pick_header_falls_back_to_the_input : Bool :=
    let input : Json := Json.make_object (Map.insert "command" (Json.make_str "make test") BTreeMap.empty) in
    let p : Pick := { name := "shell", cap := Capability.exec, input := input } in
    match pick_target p {
        Option.none => String.contains (pick_header p) "make test",
        Option.some _ => false,
    }
