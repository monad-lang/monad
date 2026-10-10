/// `read`/`write`/`edit` -- agent-skills.md Phase 2's file tools.
/// `edit`'s stale-read check: the caller must supply the content it
/// last read, compared against the file's CURRENT content before
/// writing, so a write based on a stale read is rejected rather than
/// silently clobbering a concurrent change.
use init::transformers {ResultT}
use shuttle::message_types {Content}
use shuttle::tools::file_args {ReadArgs, WriteArgs, EditArgs}
use json::json {Json}
use std::io {IO.read_file, IO.write_file, IO.file_exists}
use std::path {Path, Path.of}
use http::strings {Strings.split_on}
use std::list {List.intercalate}

def tool_err (id : String) (msg : String) : Content := Content.tool_result id msg true
def tool_ok (id : String) (msg : String) : Content := Content.tool_result id msg false

def number_line (n : I64) (line : String) : String :=
    String.concat (I64.to_string n) (String.concat ": " line)

#[partial]
def number_lines_from (n : I64) (lines : List String) : List String :=
    match lines {
        List.empty => List.empty,
        List.cons l rest => List.cons (number_line n l) (number_lines_from (n + 1) rest),
    }

def numbered_text (text : String) : String :=
    List.intercalate "\n" (number_lines_from 1 (Strings.split_on "\n" text))

pub def read_run (id : String) (j : Json) : ResultT String IO Content :=
    match ReadArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                match Path.of args.path {
                    Result.err e => return (Result.ok (tool_err id e)),
                    Result.ok p => do {
                        let text <- IO.read_file p;
                        return (Result.ok (tool_ok id (numbered_text text)))
                    }
                }
            })
    }

pub def write_run (id : String) (j : Json) : ResultT String IO Content :=
    match WriteArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                match Path.of args.path {
                    Result.err e => return (Result.ok (tool_err id e)),
                    Result.ok p => do {
                        IO.write_file p args.content;
                        return (Result.ok (tool_ok id "wrote file"))
                    }
                }
            })
    }

def edit_with_check (id : String) (p : Path) (expected : String) (new_content : String) : IO (Result String Content) := do {
    let current <- IO.read_file p;
    if String.beq current expected
    then do { IO.write_file p new_content; return (Result.ok (tool_ok id "edited file")) }
    else return (Result.ok (tool_err id "stale read: file content changed since it was last read"))
}

pub def edit_run (id : String) (j : Json) : ResultT String IO Content :=
    match EditArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (match Path.of args.path {
                Result.err e => return (Result.ok (tool_err id e)),
                Result.ok p => edit_with_check id p args.expected_content args.new_content,
            })
    }
