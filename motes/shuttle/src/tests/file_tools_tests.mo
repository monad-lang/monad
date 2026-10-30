use shuttle::tools::file {read_run, write_run, edit_run, read_up_to}
use shuttle::tools::file_tools {ReadTool.spec, WriteTool.spec, EditTool.spec}
use shuttle::tool {ToolSpec}
use shuttle::tools::file_args {ReadArgs, WriteArgs, EditArgs}
use shuttle::message_types {Content}
use json::json {Json}
use json::serde_backend {}
use init::transformers {ResultT}
use std::io {IO.get_env, IO.write_file}
use std::path {Path}
use std::process {process_id}

/// PID-qualified so two sessions' test runs sharing this filesystem's
/// /tmp never collide on the same path.
def scratch_path (name : String) : String :=
    String.concat "/tmp/shuttle_file_tools_test_" (String.concat (I64.to_string process_id) (String.concat "_" name))

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

/// A tool whose implementation requires an argument must DECLARE that
/// argument in its schema: with `schema := Json.null` the model has no
/// contract to follow and guesses the argument key (live-verified
/// against Ollama: `file_path` instead of `path`, with the function
/// name stripped into the bargain).
#[test]
def test_tool_specs_declare_parameter_schemas : Bool :=
    let read_spec : ToolSpec := ReadTool.spec in
    let write_spec : ToolSpec := WriteTool.spec in
    let edit_spec : ToolSpec := EditTool.spec in
    let read_s := Json.to_string read_spec.schema in
    let write_s := Json.to_string write_spec.schema in
    let edit_s := Json.to_string edit_spec.schema in
    String.contains read_s "\"path\"" &&
    String.contains write_s "\"content\"" &&
    String.contains edit_s "\"expected_content\""

/// A read of a huge file is clipped with a note instead of entering the
/// history whole: a 4 MB binary otherwise makes the next request ~1M
/// tokens (a live provider 400).
def read_big_verdict (c : Content) : Bool :=
    match c {
        Content.tool_result _ text is_error =>
            Bool.not is_error && String.contains text "truncated",

        _ => false,
    }

/// `n` copies of `s`, built tail-recursively: `String.repeat` is a
/// right-nested concat and takes seconds at this size.
#[partial]
def repeat_chunks (s : String) (n : I64) (acc : List String) : List String :=
    if n < 1i64 then acc else repeat_chunks s (n - 1i64) (List.cons s acc)

#[test]
def test_read_caps_a_huge_file : IO Bool := do {
    // "x" then 2-byte chars: the 262144-byte cut lands on a lead byte with
    // no continuation, so the cut has to back off to a character boundary.
    let big : String := String.concat "x" (String.concat_list (repeat_chunks "é" 131073i64 List.empty));
    let args : WriteArgs := { path := scratch_path "big.txt", content := big };
    let wr <- ResultT.run (write_run "w2" (WriteArgs.serialize_json args));
    match wr {
        Result.err _ => return false,
        Result.ok _ => do {
            let read_args : ReadArgs := { path := scratch_path "big.txt" };
            let rr <- ResultT.run (read_run "r2" (ReadArgs.serialize_json read_args));
            match rr {
                Result.err _ => return false,
                Result.ok c => return (read_big_verdict c),
            }
        },
    }
}

/// The byte cap cuts on a CHARACTER boundary: `é` is two bytes (C3 A9), so a
/// 2-byte cap would end mid-character. The reader backs off to "x" and reports
/// that the file continued.
#[test]
def test_read_up_to_keeps_a_utf8_payload : IO Bool := do {
    let path : String := scratch_path "utf8cap.txt";
    let text : String := String.concat "x" (String.repeat "é" 10i64);
    let w <- IO.write_file (Path.path path) text;
    match w {
        Result.err _ => IO.pure false,
        Result.ok _ => do {
            let r <- read_up_to (Path.path path) 2i64;
            match r {
                Result.err _ => IO.pure false,
                Result.ok pr => match pr {
                    Pair.pair got more => IO.pure (more && String.beq got "x"),
                },
            }
        },
    }
}

/// A file shorter than the cap comes back whole, with the flag off.
#[test]
def test_read_up_to_reports_a_complete_file : IO Bool := do {
    let path : String := scratch_path "short.txt";
    let w <- IO.write_file (Path.path path) "hello";
    match w {
        Result.err _ => IO.pure false,
        Result.ok _ => do {
            let r <- read_up_to (Path.path path) 100i64;
            match r {
                Result.err _ => IO.pure false,
                Result.ok pr => match pr {
                    Pair.pair got more => IO.pure (Bool.not more && String.beq got "hello"),
                },
            }
        },
    }
}
