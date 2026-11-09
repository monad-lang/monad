/// The `plan` tool: the model records where the session's plan stands --
/// its status, completion, next action, and a changelog line -- in the
/// plan file the session is linked to (`plan_file.mo`). A later session
/// that loads the plan reads it back, so work can stop and resume across
/// sessions and days.
///
/// It only ever touches the linked file, never a path the model names.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::message_types {Content}
use json::json {
    Json, Json.make_object_pairs, Json.make_array, Json.make_str, Json.get_object, Json.get_str,
    Json.get_num, Json.get_num_i64, Json.object_get,
}
use std::map {BTreeMap}
use std::list {List.intercalate}
use init::transformers {ResultT}
use weaver::store {StoreState}
use weaver::plan_file {PlanRepo, PlanDoc, PlanMeta, PlanFile.linked, PlanRepo.update, PlanMeta.with_status, PlanMeta.with_progress}

/// One `plan` call, decoded.
pub struct PlanCall {
    status : Option String,
    completion : Option I64,
    next_action : Option String,
    note : Option String,
}

pub def PlanTool.statuses : List String := ["draft", "approved", "in-progress", "done", "abandoned"]

def plan_str_field (key : String) (obj : BTreeMap String Json) : Option String :=
    match Json.object_get key obj {
        Option.none => Option.none,
        Option.some j => match Json.get_str j {
            Result.ok s => if String.is_empty (String.trim s) then Option.none else Option.some (String.trim s),
            Result.err _ => Option.none,
        },
    }

def plan_int_field (key : String) (obj : BTreeMap String Json) : Option I64 :=
    match Json.object_get key obj {
        Option.none => Option.none,
        Option.some j => match Json.get_num_i64 (Json.get_num j) {
            Result.ok n => Option.some n,
            Result.err _ => Option.none,
        },
    }

#[partial]
def known_status (s : String) (ss : List String) : Bool :=
    match ss {
        List.empty => false,
        List.cons h rest => if h == s then true else known_status s rest,
    }

def check_status (c : PlanCall) : Result String PlanCall :=
    match c.status {
        Option.none => Result.ok c,
        Option.some s =>
            if known_status s PlanTool.statuses then Result.ok c
            else Result.err (String.concat "unknown status " (String.concat s " (draft, approved, in-progress, done, abandoned)")),
    }

def check_completion (c : PlanCall) : Result String PlanCall :=
    match c.completion {
        Option.none => check_status c,
        Option.some n =>
            if Bool.or (I64.lt n 0) (I64.gt n 100) then Result.err "completion must be between 0 and 100"
            else check_status c,
    }

def is_none_str (o : Option String) : Bool :=
    match o { Option.none => true, Option.some _ => false }

def is_none_int (o : Option I64) : Bool :=
    match o { Option.none => true, Option.some _ => false }

def check_any (c : PlanCall) : Result String PlanCall :=
    if is_none_str c.status && is_none_int c.completion && is_none_str c.next_action && is_none_str c.note
    then Result.err "give at least one of status, completion, next_action, note"
    else check_completion c

pub def PlanTool.decode (j : Json) : Result String PlanCall :=
    match Json.get_object j {
        Result.err _ => Result.err "the input must be an object",
        Result.ok obj =>
            let c : PlanCall := {
                status := plan_str_field "status" obj,
                completion := plan_int_field "completion" obj,
                next_action := plan_str_field "next_action" obj,
                note := plan_str_field "note" obj,
            } in
            check_any c,
    }

def status_meta (c : PlanCall) (m : PlanMeta) : PlanMeta :=
    match c.status {
        Option.none => m,
        Option.some s => PlanMeta.with_status s m,
    }

/// The call's metadata change, applied to `m`.
pub def PlanTool.apply (c : PlanCall) (m : PlanMeta) : PlanMeta :=
    PlanMeta.with_progress c.completion c.next_action (status_meta c m)

def plan_part (label : String) (o : Option String) : List String :=
    match o {
        Option.none => List.empty,
        Option.some s => [String.concat label s],
    }

/// The changelog line: the note, else what changed.
pub def PlanTool.line (c : PlanCall) : String :=
    match c.note {
        Option.some n => n,
        Option.none =>
            let pct : Option String := match c.completion {
                Option.none => Option.none,
                Option.some n => Option.some (String.concat (I64.to_string n) "%"),
            } in
            List.intercalate "; " (List.append (plan_part "status: " c.status) (List.append (plan_part "completion: " pct) (plan_part "next: " c.next_action))),
    }

def plan_str_prop (d : String) : Json :=
    Json.make_object_pairs [Pair.pair "type" (Json.make_str "string"), Pair.pair "description" (Json.make_str d)]

def plan_schema : Json :=
    Json.make_object_pairs
        [Pair.pair "type" (Json.make_str "object"),
            Pair.pair "properties" (Json.make_object_pairs
                [Pair.pair "status" (Json.make_object_pairs
                    [Pair.pair "type" (Json.make_str "string"),
                        Pair.pair "enum" (Json.make_array (List.map Json.make_str PlanTool.statuses))]),
                    Pair.pair "completion" (Json.make_object_pairs [Pair.pair "type" (Json.make_str "integer"),
                        Pair.pair "description" (Json.make_str "How much of the plan is done, 0-100.")]),
                    Pair.pair "next_action" (plan_str_prop "The next concrete step, for whoever picks the plan up."),
                    Pair.pair "note" (plan_str_prop "One changelog line: what this session did.")])]

pub def PlanTool.spec : ToolSpec :=
    { name := "plan",
        description := "Record progress on this session's stored plan: its status (draft, approved, in-progress, done, abandoned), completion 0-100, the next action, and a changelog note. A later session that loads the plan sees it. Use it when a plan step lands, when you stop with work left, and when the plan is done.",
        schema := plan_schema }

/// `read`-tagged like `todo_write`: it changes only the session's own
/// plan file, so it needs no approval.
pub def PlanTool.impl (store : Option StoreState) (repo : Option PlanRepo) : ToolImpl :=
    { spec := PlanTool.spec, cap := Capability.read, run := plan_tool_run store repo }

def plan_tool_failed (id : String) (msg : String) : IO (Result String Content) :=
    IO.pure (Result.ok (Content.tool_result id (String.concat "plan: " msg) true))

def plan_tool_run (store : Option StoreState) (repo : Option PlanRepo) (id : String) (j : Json) : ResultT String IO Content :=
    ResultT.mk (match PlanTool.decode j {
        Result.err e => plan_tool_failed id e,
        Result.ok c => match store {
            Option.none => plan_tool_failed id "this session has no store, so no plan file",
            Option.some s => match repo {
                Option.none => plan_tool_failed id "no plan repo is configured",
                Option.some r => plan_linked s r id c,
            },
        },
    })

def plan_linked (s : StoreState) (r : PlanRepo) (id : String) (c : PlanCall) : IO (Result String Content) := do {
    let linked <- PlanFile.linked s;
    match linked {
        Option.none => plan_tool_failed id "no plan is linked to this session (plan mode captures one; /plans load picks a stored one)",
        Option.some path => plan_update r path id c,
    }
}

def plan_update (r : PlanRepo) (path : String) (id : String) (c : PlanCall) : IO (Result String Content) := do {
    let res <- PlanRepo.update r path (PlanTool.apply c) (PlanTool.line c);
    match res {
        Result.err e => plan_tool_failed id e,
        Result.ok d => IO.pure (Result.ok (Content.tool_result id (PlanTool.summary path d) false)),
    }
}

pub def PlanTool.summary (path : String) (d : PlanDoc) : String :=
    String.concat_all ["plan ", path, ": ", d.meta.status, ", ", I64.to_string d.meta.completion, "%",
        if String.is_empty d.meta.next_action then "" else String.concat "; next: " d.meta.next_action]
