use shuttle::tools::file {read_run, write_run, edit_run}
use shuttle::tools::file_args {ReadArgs, WriteArgs, EditArgs}
use shuttle::message_types {Content}
use json::json {Json}
use json::serde_backend {}
use init::transformers {ResultT}
use std::io {IO.get_env}

def scratch_path (name : String) : String :=
    String.concat "/tmp/shuttle_file_tools_test_" name

def write_tool_result : IO (Result String Content) :=
    let args : WriteArgs := { path := scratch_path "a.txt", content := "hello\nworld" } in
    ResultT.run (write_run "w1" (WriteArgs.serialize_json args))

def is_ok_result (c : Content) : Bool :=
    match c { Content.tool_result _ _ is_error => Bool.not is_error, _ => false }

def read_back_result : IO (Result String Content) :=
    let read_args : ReadArgs := { path := scratch_path "a.txt" } in
    ResultT.run (read_run "r1" (ReadArgs.serialize_json read_args))

def read_content_has_numbered_lines (c : Content) : Bool :=
    match c {
        Content.tool_result _ text is_error =>
            Bool.not is_error && String.contains text "1: hello" && String.contains text "2: world",
        _ => false,
    }

#[test]
def test_write_then_read_roundtrip : IO Bool := do {
    let wr <- write_tool_result;
    match wr {
        Result.err _ => return false,
        Result.ok write_content =>
            match is_ok_result write_content {
                false => return false,
                true => do {
                    let rr <- read_back_result;
                    return (match rr {
                        Result.ok read_content => read_content_has_numbered_lines read_content,
                        Result.err _ => false,
                    })
                },
            },
    }
}

def stale_edit_result : IO (Result String Content) :=
    let edit_args : EditArgs := { path := scratch_path "a.txt", expected_content := "WRONG STALE CONTENT", new_content := "new" } in
    ResultT.run (edit_run "e1" (EditArgs.serialize_json edit_args))

def fresh_edit_result : IO (Result String Content) :=
    let edit_args : EditArgs := { path := scratch_path "a.txt", expected_content := "hello\nworld", new_content := "updated" } in
    ResultT.run (edit_run "e2" (EditArgs.serialize_json edit_args))

def is_error_result (c : Content) : Bool :=
    match c { Content.tool_result _ _ is_error => is_error, _ => false }

#[test]
def test_edit_rejects_stale_read : IO Bool := do {
    let wr <- write_tool_result;
    match wr {
        Result.err _ => return false,
        Result.ok _ => do {
            let er <- stale_edit_result;
            return (match er {
                Result.ok edit_content => is_error_result edit_content,
                Result.err _ => false,
            })
        },
    }
}

#[test]
def test_edit_succeeds_with_fresh_read : IO Bool := do {
    let wr <- write_tool_result;
    match wr {
        Result.err _ => return false,
        Result.ok _ => do {
            let er <- fresh_edit_result;
            return (match er {
                Result.ok edit_content => is_ok_result edit_content,
                Result.err _ => false,
            })
        },
    }
}
