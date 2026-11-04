/// The todo list: decoding the tool input, the one-in-progress rule, the
/// display lines and the stored round trip.
use weaver::todo {
    TodoItem, TodoStatus, Todo.decode, Todo.encode, Todo.validate, Todo.lines, Todo.summary,
    Todo.same, Todo.write, Todo.read,
}
use json::json {Json, Json.parse}
use std::list {List.length, List.intercalate}

def parse_todos (text : String) : Result String (List TodoItem) :=
    match Json.parse text {
        Result.err _ => Result.err "not JSON",
        Result.ok j => Todo.decode j,
    }

def three : String :=
    "{\"todos\": [{\"content\": \"Read the module\", \"status\": \"completed\"}, {\"content\": \"Run the tests\", \"status\": \"in_progress\", \"active_form\": \"Running the tests\"}, {\"content\": \"Commit\", \"status\": \"pending\"}]}"

#[test]
def test_decode_and_lines : Bool :=
    match parse_todos three {
        Result.err _ => false,
        Result.ok ts =>
            String.beq (List.intercalate "|" (Todo.lines ts)) "☑ Read the module|◐ Running the tests|☐ Commit"
                && String.beq (Todo.summary ts) "todos 1/3 · Running the tests",
    }

#[test]
def test_decode_rejects_bad_input : Bool :=
    let bad_status : Bool := match parse_todos "{\"todos\": [{\"content\": \"x\", \"status\": \"done\"}]}" { Result.err _ => true, Result.ok _ => false } in
    let no_content : Bool := match parse_todos "{\"todos\": [{\"status\": \"pending\"}]}" { Result.err _ => true, Result.ok _ => false } in
    let no_array : Bool := match parse_todos "{\"items\": []}" { Result.err _ => true, Result.ok _ => false } in
    let status_defaults : Bool := match parse_todos "{\"todos\": [{\"content\": \"x\"}]}" { Result.ok ts => List.length ts == 1, Result.err _ => false } in
    bad_status && no_content && no_array && status_defaults

#[test]
def test_one_in_progress_at_a_time : Bool :=
    match parse_todos "{\"todos\": [{\"content\": \"a\", \"status\": \"in_progress\"}, {\"content\": \"b\", \"status\": \"in_progress\"}]}" {
        Result.err _ => false,
        Result.ok ts => match Todo.validate ts { Result.err _ => true, Result.ok _ => false },
    }

#[test]
def test_encode_round_trips : Bool :=
    match parse_todos three {
        Result.err _ => false,
        Result.ok ts => match Todo.decode (Todo.encode ts) {
            Result.err _ => false,
            Result.ok ts2 => Todo.same ts ts2,
        },
    }

/// The tool writes the list and a later read (the TUI's poll) gets it back.
#[test]
def test_write_then_read : IO Bool := do {
    match parse_todos three {
        Result.err _ => IO.pure false,
        Result.ok ts => do {
            let ok <- Todo.write Option.none ts;
            let back <- Todo.read Option.none;
            let empty : List TodoItem := List.empty;
            let _ <- Todo.write Option.none empty;
            let cleared <- Todo.read Option.none;
            IO.pure (ok && Todo.same ts back && List.is_empty cleared)
        },
    }
}
