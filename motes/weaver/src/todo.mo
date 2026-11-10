/// weaver / todo -- the turn's todo list: the model keeps it with the
/// `todo_write` tool (the whole list each call), the session store holds it
/// in `todos.json`, and the TUI shows it above the input (Ctrl+T folds it).
/// A list the model can see and the user can follow is what keeps a long
/// multi-step task on track.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::message_types {Content}
use json::json {
    Json, Json.parse, Json.to_string, Json.make_object, Json.make_object_pairs, Json.make_array,
    Json.make_str, Json.get_object, Json.get_array, Json.get_str, Json.object_get,
}
use std::io {IO.read_file, IO.write_file}
use std::path {Path, Path.to_string}
use std::process {process_id}
use std::map {Map, BTreeMap}
use std::list {List.filter, List.intercalate}
use init::transformers {ResultT}
use weaver::store {StoreState, Store.child}

pub type TodoStatus {
    todo_pending,
    todo_in_progress,
    todo_completed,
}

/// One item. `active` is the present-tense line shown while the item is in
/// progress ("Running the tests"); empty means show `content`.
pub struct TodoItem {
    content : String,
    status : TodoStatus,
    active : String,
}

// ── codec ───────────────────────────────────────────────────────────────

pub def TodoStatus.parse (s : String) : Option TodoStatus :=
    if String.beq s "pending" then Option.some TodoStatus.todo_pending
    else if String.beq s "in_progress" then Option.some TodoStatus.todo_in_progress
    else if String.beq s "completed" then Option.some TodoStatus.todo_completed
    else Option.none

pub def TodoStatus.show (s : TodoStatus) : String :=
    match s {
        TodoStatus.todo_pending => "pending",
        TodoStatus.todo_in_progress => "in_progress",
        TodoStatus.todo_completed => "completed",
    }

def str_field (key : String) (obj : BTreeMap String Json) : Option String :=
    match Json.object_get key obj {
        Option.none => Option.none,
        Option.some j => match Json.get_str j {
            Result.ok s => Option.some s,
            Result.err _ => Option.none,
        },
    }

def decode_item (j : Json) : Result String TodoItem :=
    match Json.get_object j {
        Result.err _ => Result.err "each todo must be an object",
        Result.ok obj => match str_field "content" obj {
            Option.none => Result.err "each todo needs a \"content\" string",
            Option.some content =>
                if String.is_empty (String.trim content) then Result.err "a todo's content is empty"
                else match TodoStatus.parse (match str_field "status" obj { Option.some s => s, Option.none => "pending" }) {
                    Option.none => Result.err "status must be pending, in_progress or completed",
                    Option.some st =>
                        let active : String := match str_field "active_form" obj { Option.some a => a, Option.none => "" } in
                        let item : TodoItem := { content := content, status := st, active := active } in
                        Result.ok item,
                },
        },
    }

#[partial]
def decode_items (js : List Json) (acc : List TodoItem) : Result String (List TodoItem) :=
    match js {
        List.empty => Result.ok (List.reverse acc),
        List.cons j rest => match decode_item j {
            Result.err e => Result.err e,
            Result.ok it => decode_items rest (List.cons it acc),
        },
    }

/// `{"todos": [...]}` -- the tool input and the file share the shape.
pub def Todo.decode (j : Json) : Result String (List TodoItem) :=
    match Json.get_object j {
        Result.err _ => Result.err "expected an object with a \"todos\" array",
        Result.ok obj => match Json.object_get "todos" obj {
            Option.none => Result.err "expected a \"todos\" array",
            Option.some arr => match Json.get_array arr {
                Result.err _ => Result.err "\"todos\" must be an array",
                Result.ok js => decode_items js List.empty,
            },
        },
    }

def encode_item (t : TodoItem) : Json :=
    Json.make_object_pairs
        [Pair.pair "content" (Json.make_str t.content),
            Pair.pair "status" (Json.make_str (TodoStatus.show t.status)),
            Pair.pair "active_form" (Json.make_str t.active)]

pub def Todo.encode (ts : List TodoItem) : Json :=
    Json.make_object_pairs [Pair.pair "todos" (Json.make_array (List.map encode_item ts))]

/// At most one item is in progress: the list says what is happening now.
pub def Todo.validate (ts : List TodoItem) : Result String (List TodoItem) :=
    let running : List TodoItem := List.filter (fn (t : TodoItem) => Todo.is_running t) ts in
    if I64.lt 1 (List.length running)
    then Result.err "only one todo may be in_progress at a time"
    else Result.ok ts

pub def Todo.is_running (t : TodoItem) : Bool :=
    match t.status { TodoStatus.todo_in_progress => true, _ => false }

pub def Todo.is_done (t : TodoItem) : Bool :=
    match t.status { TodoStatus.todo_completed => true, _ => false }

/// Item-by-item equality (a poll that changed nothing must not repaint).
#[partial]
pub def Todo.same (a : List TodoItem) (b : List TodoItem) : Bool :=
    match a {
        List.empty => List.is_empty b,
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys =>
                if Bool.and (String.beq x.content y.content)
                    (Bool.and (String.beq (TodoStatus.show x.status) (TodoStatus.show y.status)) (String.beq x.active y.active))
                then Todo.same xs ys
                else false,
        },
    }

// ── display ─────────────────────────────────────────────────────────────

/// `☑ done`, `◐ Running the tests`, `☐ next`.
pub def Todo.line (t : TodoItem) : String :=
    match t.status {
        TodoStatus.todo_completed => String.concat "☑ " t.content,
        TodoStatus.todo_in_progress => String.concat "◐ " (if String.is_empty t.active then t.content else t.active),
        TodoStatus.todo_pending => String.concat "☐ " t.content,
    }

pub def Todo.lines (ts : List TodoItem) : List String := List.map Todo.line ts

/// `todos 3/7 · Running the tests` (the folded panel's one line).
pub def Todo.summary (ts : List TodoItem) : String :=
    let done : I64 := List.length (List.filter Todo.is_done ts) in
    let head : String := String.concat "todos " (String.concat (I64.to_string done)
        (String.concat "/" (I64.to_string (List.length ts)))) in
    match List.first (List.filter Todo.is_running ts) {
        Option.none => head,
        Option.some t => String.concat head (String.concat " · " (if String.is_empty t.active then t.content else t.active)),
    }

// ── storage ─────────────────────────────────────────────────────────────

/// `<session>/todos.json`; a per-process file without a store.
pub def Todo.path (store : Option StoreState) : Path :=
    match store {
        Option.some s => Store.child s.dir "todos.json",
        Option.none => Path.path (String.concat "/tmp/weaver-todos-" (String.concat (I64.to_string process_id) ".json")),
    }

pub def Todo.write (store : Option StoreState) (ts : List TodoItem) : IO Bool := do {
    let r <- IO.write_file (Todo.path store) (Json.to_string (Todo.encode ts));
    return (match r { Result.ok _ => true, Result.err _ => false })
}

/// The stored list; empty when there is none or it does not decode (a
/// torn read shows nothing for one poll rather than garbage).
pub def Todo.read (store : Option StoreState) : IO (List TodoItem) := do {
    let r <- IO.read_file (Todo.path store);
    let empty : List TodoItem := List.empty;
    return (match r {
        Result.err _ => empty,
        Result.ok text => match Json.parse text {
            Result.err _ => empty,
            Result.ok j => match Todo.decode j {
                Result.err _ => empty,
                Result.ok ts => ts,
            },
        },
    })
}

// ── the tool ────────────────────────────────────────────────────────────

def todo_schema : Json :=
    let status : Json := Json.make_object_pairs
        [Pair.pair "type" (Json.make_str "string"),
            Pair.pair "enum" (Json.make_array [Json.make_str "pending", Json.make_str "in_progress", Json.make_str "completed"])] in
    let item : Json := Json.make_object_pairs
        [Pair.pair "type" (Json.make_str "object"),
            Pair.pair "properties" (Json.make_object_pairs
                [Pair.pair "content" (Json.make_object_pairs [Pair.pair "type" (Json.make_str "string"),
                    Pair.pair "description" (Json.make_str "The step, imperative: \"Run the tests\".")]),
                    Pair.pair "status" status,
                    Pair.pair "active_form" (Json.make_object_pairs [Pair.pair "type" (Json.make_str "string"),
                        Pair.pair "description" (Json.make_str "Present tense, shown while in progress: \"Running the tests\".")])]),
            Pair.pair "required" (Json.make_array [Json.make_str "content", Json.make_str "status"])] in
    Json.make_object_pairs
        [Pair.pair "type" (Json.make_str "object"),
            Pair.pair "properties" (Json.make_object_pairs
                [Pair.pair "todos" (Json.make_object_pairs [Pair.pair "type" (Json.make_str "array"), Pair.pair "items" item])]),
            Pair.pair "required" (Json.make_array [Json.make_str "todos"])]

pub def TodoTool.spec : ToolSpec :=
    { name := "todo_write",
        description := "Replace the task's todo list (send the whole list each time). Use it for any task with three or more steps: add the steps, mark one in_progress before starting it, and mark it completed as soon as it is done. The user sees the list.",
        schema := todo_schema }

/// `read`-tagged: it changes only the session's own list, so it needs no
/// approval and runs in plan mode.
pub def TodoTool.impl (store : Option StoreState) : ToolImpl :=
    { spec := TodoTool.spec, cap := Capability.read, run := todo_run store }

def todo_run (store : Option StoreState) (id : String) (j : Json) : ResultT String IO Content :=
    ResultT.mk (match Todo.decode j {
        Result.err e => IO.pure (Result.ok (Content.tool_result id (String.concat "todo_write: " e) true)),
        Result.ok ts => match Todo.validate ts {
            Result.err e => IO.pure (Result.ok (Content.tool_result id (String.concat "todo_write: " e) true)),
            Result.ok valid => todo_save store id valid,
        },
    })

def todo_save (store : Option StoreState) (id : String) (ts : List TodoItem) : IO (Result String Content) := do {
    let ok <- Todo.write store ts;
    if ok
    then IO.pure (Result.ok (Content.tool_result id (String.concat (Todo.summary ts)
        (String.concat "\n" (List.intercalate "\n" (Todo.lines ts)))) false))
    else IO.pure (Result.ok (Content.tool_result id "todo_write: could not save the list" true))
}
