/// `DiffTool` -- weaver.md Phase 16: a write/edit tool result carries its
/// hunk diff, computed before the write when the old side is still on disk.
use shuttle::tools::file_tools {WriteTool.impl, EditTool.impl}
use shuttle::tool {ToolImpl}
use shuttle::message_types {Content}
use weaver::diff_tool {DiffTool.wrap, DiffTool.sep, DiffTool.split, DiffTool.capped}
use init::transformers {ResultT}
use json::json {Json, Json.make_str, Json.make_object}
use std::test {Test.write_fixture}
use std::path {Path}
use std::map {Map, BTreeMap}
use std::process {process_id, exec_cmd}

def root : String :=
    String.concat "/tmp/weaver_diff_tool_" (I64.to_string process_id)

def file_at : String := String.concat root "/a.txt"

def put (k : String) (v : Json) (m : BTreeMap String Json) : BTreeMap String Json :=
    Map.insert k v m

def output_of (c : Content) : String :=
    match c { Content.tool_result _ out _ => out, _ => "" }

def run_tool (impl : ToolImpl) (id : String) (j : Json) : IO String := do {
    let r <- ResultT.run (impl.run id j);
    return (match r { Result.ok c => output_of c, Result.err _ => "" })
}

def edit_input (path : String) : Json :=
    Json.make_object (put "path" (Json.make_str path)
        (put "expected_content" (Json.make_str "a\nb\nc")
            (put "new_content" (Json.make_str "a\nX\nc") BTreeMap.empty)))

def write_input (path : String) : Json :=
    Json.make_object (put "path" (Json.make_str path)
        (put "content" (Json.make_str "a\nc") BTreeMap.empty))

#[test]
def test_edit_result_carries_the_hunk : IO Bool := do {
    let _ <- exec_cmd "mkdir" ["-p", root];
    let _ <- Test.write_fixture (Path.path file_at) "a\nb\nc";
    let out <- run_tool (DiffTool.wrap EditTool.impl) "c1" (edit_input file_at);
    let _ <- exec_cmd "rm" ["-rf", root];
    return (String.contains out "@@" && String.contains out "| X" && String.contains out "| b")
}

#[test]
def test_write_reads_the_old_side_before_writing : IO Bool := do {
    let _ <- exec_cmd "mkdir" ["-p", root];
    let _ <- Test.write_fixture (Path.path file_at) "a\nb";
    let out <- run_tool (DiffTool.wrap WriteTool.impl) "c2" (write_input file_at);
    let _ <- exec_cmd "rm" ["-rf", root];
    return (String.contains out "@@" && String.contains out "| b" && String.contains out "| c")
}

def write_new_input (path : String) : Json :=
    Json.make_object (put "path" (Json.make_str path)
        (put "content" (Json.make_str "a\nb") BTreeMap.empty))

/// A new file's old side is empty; every line must show as an addition.
#[test]
def test_a_new_file_write_carries_every_line : IO Bool := do {
    let _ <- exec_cmd "mkdir" ["-p", root];
    let fresh : String := String.concat root "/new.txt";
    let out <- run_tool (DiffTool.wrap WriteTool.impl) "c3" (write_new_input fresh);
    let _ <- exec_cmd "rm" ["-rf", root];
    return (String.contains out DiffTool.sep
        && String.contains out "@@ -0,0 +1,2 @@"
        && String.contains out "| a"
        && String.contains out "| b")
}

/// The separator splits at the diff's head, so a multi-hunk result keeps
/// every hunk (the old `\n@@ ` scan split at the LAST header).
#[test]
def test_split_keeps_a_multi_hunk_result_whole : Bool :=
    let output : String := String.concat "wrote file x"
        (String.concat DiffTool.sep
            "@@ -1,2 +1,2 @@\n-x\n+y\n@@ -10,2 +10,2 @@\n-p\n+q") in
    match DiffTool.split output {
        Option.some pr => match pr {
            Pair.pair summary diff =>
                String.beq summary "wrote file x"
                    && String.contains diff "@@ -1,2 +1,2 @@"
                    && String.contains diff "@@ -10,2 +10,2 @@"
                    && String.contains diff "+q",
        },
        Option.none => false,
    }

/// A 32 KB cut must not land inside a multi-byte character (String.slice
/// answers "" there, erasing the whole diff).
#[test]
def test_capped_does_not_split_a_character : Bool :=
    let s : String := String.concat (String.repeat "a" 31999) (String.concat "€" "b") in
    let c : String := DiffTool.capped s in
    String.starts_with (String.repeat "a" 31999) c
        && String.contains c "(diff truncated)"
