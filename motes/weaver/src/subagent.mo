/// The read-only plan subagent: a `task` tool that runs one child loop
/// (`Loop.run_state`) over a fresh Session with only read/grep/glob and
/// `Gate.read_only`, then returns the child's last assistant message.
/// Synchronous: the child runs inside the parent's tool dispatch, depth 1
/// (the child registry has no `task`). Child usage rides the result footer
/// and the debug log, not the parent Session.spent (v1 accounting gap).
use shuttle::agent {RunState, silent_sleep, silent_usage}
use shuttle::context {usage_zero}
use shuttle::gate {Gate}
use shuttle::provider {ProviderConfig}
use shuttle::loop {Loop.run_state}
use shuttle::message {Message, Usage}
use shuttle::message_types {Role, Content}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::tools::file_tools {ReadTool.impl}
use shuttle::tools::search_tools {GrepTool.impl, GlobTool.impl}
use json::json {Json, Json.make_object, Json.make_str, Json.make_array}
use std::map {BTreeMap}
use std::io {IO.current_time_nano}
use std::path {Path, Path.to_string, Path.with_suffix}
use std::process {process_id, exec_cmd}
use init::transformers {ResultT}
use log::logger {Logger}
use weaver::logs {Logs.debug, Logs.info}
use weaver::subagent_args {TaskArgs}
use weaver::store {StoreState, Store.child}
use std::list {List.intercalate}

pub def Subagent.system_prompt : String :=
    "You are a read-only planning subagent. Inspect the workspace with read, grep and glob, then return a concrete, ordered plan with risks and validation steps. You cannot modify files or run commands; do not ask for approval."

/// Read/grep/glob, and nothing else. No `task`, so depth is 1.
pub def Subagent.read_registry : ToolRegistry :=
    ToolRegistry.register ReadTool.impl
        (ToolRegistry.register GrepTool.impl
            (ToolRegistry.register GlobTool.impl ToolRegistry.empty))

def str_param (name : String) (desc : String) : Pair String Json :=
    Pair.pair name (Json.make_object (Map.insert "type" (Json.make_str "string")
        (Map.insert "description" (Json.make_str desc) BTreeMap.empty)))

def num_param (name : String) (desc : String) : Pair String Json :=
    Pair.pair name (Json.make_object (Map.insert "type" (Json.make_str "integer")
        (Map.insert "description" (Json.make_str desc) BTreeMap.empty)))

#[partial]
def params_to_map (params : List (Pair String Json)) (acc : BTreeMap String Json) : BTreeMap String Json :=
    match params {
        List.empty => acc,
        List.cons p rest => match p { Pair.pair k v => params_to_map rest (Map.insert k v acc) },
    }

def pair_fst (p : Pair String Json) : Json :=
    Json.make_str (match p { Pair.pair k _ => k })

def task_schema : Json :=
    let params : List (Pair String Json) :=
        [str_param "prompt" "The question the subagent should answer with a plan.",
         num_param "max_turns" "Model-call budget (1-20; 0 uses 8)."] in
    Json.make_object (Map.insert "type" (Json.make_str "object")
        (Map.insert "properties" (Json.make_object (params_to_map params BTreeMap.empty))
        (Map.insert "required" (Json.make_array [Json.make_str "prompt"]) BTreeMap.empty)))

pub def Subagent.spec : ToolSpec :=
    { name := "task", description := "Ask a read-only subagent to investigate and return a plan.", schema := task_schema }

// ── child session / result ──────────────────────────────────────────────

def user_message (text : String) : Message :=
    let m : Message := { role := Role.user, content := List.cons (Content.text text) List.empty } in
    m

def child_session (cfg : ProviderConfig) (prompt : String) : Session :=
    let s : Session := { config := cfg, system_prompt := Subagent.system_prompt,
      tools := ToolRegistry.specs Subagent.read_registry,
      history := List.cons (user_message prompt) List.empty,
      turns := 0, spent := usage_zero } in
    s

#[partial]
def content_text (c : Content) : String :=
    match c { Content.text s => s, _ => "" }

#[partial]
def message_text (m : Message) : String :=
    List.intercalate "\n" (List.map content_text m.content)

#[partial]
def last_assistant (ms : List Message) : Option String :=
    match List.reverse ms {
        List.empty => Option.none,
        List.cons m rest =>
            match m.role {
                Role.assistant => Option.some (message_text m),
                _ => last_assistant (List.reverse rest),
            },
    }

def usage_footer (s : Session) : String :=
    String.concat "[subagent turns=" (String.concat (I64.to_string s.turns)
        (String.concat " tokens in=" (String.concat (I64.to_string s.spent.input_tokens)
        (String.concat " out=" (String.concat (I64.to_string s.spent.output_tokens) "]")))))

// ── the tool ────────────────────────────────────────────────────────────

def persist_to (dir : Path) (s : Session) : IO Unit := do {
    let now <- IO.current_time_nano;
    let _ <- exec_cmd "mkdir" ["-p", Path.to_string dir];
    let name : String := String.concat (I64.to_string process_id) (String.concat "-" (I64.to_string now));
    let file : String := Path.to_string (Path.with_suffix dir (String.concat "/" (String.concat name ".json")));
    let _ <- Session.save s file;
    IO.pure unit
}

def persist_child (store : Option StoreState) (s : Session) : IO Unit :=
    match store {
        Option.none => IO.pure unit,
        Option.some st => persist_to (Store.child st.dir "agents") s,
    }

def child_emit (log : Option Logger) (frag : String) : IO Unit :=
    Logs.debug log (String.concat "ev=subagent_chunk " frag)

def child_usage (log : Option Logger) (u : Usage) : IO Unit :=
    String.concat "ev=subagent_usage in=" (String.concat (I64.to_string u.input_tokens)
        (String.concat " out=" (I64.to_string u.output_tokens)))
        |> (fn (msg : String) => Logs.debug log msg)

def task_success (id : String) (log : Option Logger) (store : Option StoreState) (final : Session) : IO Content := do {
    let _ <- persist_child store final;
    let _ <- Logs.info log (String.concat "ev=subagent_end " (usage_footer final));
    let hist : List Message := final.history;
    match last_assistant hist {
        Option.none => IO.pure (Content.tool_result id "subagent produced no plan" true),
        Option.some plan =>
            IO.pure (Content.tool_result id (String.concat plan (String.concat "\n" (usage_footer final))) false),
    }
}

def task_result (id : String) (log : Option Logger) (store : Option StoreState) (r : Result String Session) : IO Content :=
    match r {
        Result.err e => IO.pure (Content.tool_result id (String.concat "subagent failed: " e) true),
        Result.ok final => task_success id log store final,
    }

def run_task (cfg : ProviderConfig) (log : Option Logger) (store : Option StoreState)
        (id : String) (j : Json) : ResultT String IO Content :=
    match TaskArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (Content.tool_result id e true))),
        Result.ok args =>
            ResultT.mk (do {
                let n : I64 := if args.max_turns < 1 then 8 else if 20 < args.max_turns then 20 else args.max_turns;
                let sess : Session := child_session cfg args.prompt;
                let st : RunState := { session := sess, reg := Subagent.read_registry, turns_left := n,
                    emit := child_emit log, gate := Gate.read_only, always := List.empty,
                    retries := 1, sleep_ms := silent_sleep, on_usage := child_usage log };
                let _ <- Logs.info log (String.concat "ev=subagent_start turns=" (I64.to_string n));
                let r <- ResultT.run (Loop.run_state st);
                let c <- task_result id log store r;
                IO.pure (Result.ok c)
            }),
    }

/// The per-turn `task` tool. The registry is built each turn so the child
/// uses the CURRENT provider/model and the run's store/log.
pub def Subagent.task_tool (cfg : ProviderConfig) (log : Option Logger)
        (store : Option StoreState) : ToolImpl :=
    { spec := Subagent.spec, cap := Capability.exec, run := run_task cfg log store }
