/// The read-only plan subagent: a `task` tool that runs one child loop
/// (`Loop.run_state`) over a fresh Session with only read/grep/glob and
/// `Gate.read_only`, then returns the child's last assistant message.
/// Synchronous: the child runs inside the parent's tool dispatch, depth 1
/// (the child registry has no `task`). The child's spend goes into the
/// turn's `spend` Ref, which the parent loop folds into its own
/// `session.spent` after the dispatch (`RunState.side_spend`).
use shuttle::agent {RunState, silent_sleep, silent_usage, silent_inbox, silent_side_spend}
use shuttle::context {usage_zero, usage_add}
use std::ref {Ref, Ref.get, Ref.set, Ref.modify}
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
use std::map {Map, BTreeMap}
use std::io {IO.current_time_nano}
use std::path {Path, Path.to_string, Path.with_suffix}
use std::process {process_id, exec_cmd}
use init::transformers {ResultT}
use log::logger {Logger}
use weaver::tasks {Tasks.agent_id, Tasks.record_agent}
use weaver::text {Text.cut}
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
            num_param "max_turns" "Model-call budget (1-50; 0 uses 24)."] in
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
    (stop : Unit -> IO Bool) (spend : Ref Usage) (id : String) (j : Json) : ResultT String IO Content :=
    match TaskArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (Content.tool_result id e true))),
        Result.ok args =>
            ResultT.mk (do {
                let n : I64 := if args.max_turns < 1 then 24 else if 50 < args.max_turns then 50 else args.max_turns;
                let sess : Session := child_session cfg args.prompt;
                let st : RunState := { session := sess, reg := Subagent.read_registry, turns_left := n,
                    emit := child_emit log, gate := Gate.read_only, always := List.empty,
                    retries := 1, sleep_ms := silent_sleep, on_usage := child_usage log,
                    should_stop := stop, inbox := silent_inbox, side_spend := silent_side_spend, stopped := false };
                let _ <- Logs.info log (String.concat "ev=subagent_start turns=" (I64.to_string n));
                let run_id <- Tasks.agent_id;
                let started <- IO.current_time_nano;
                let _ <- Tasks.record_agent store run_id args.prompt "running" started "";
                let r <- ResultT.run (Loop.run_state st);
                let _ <- add_spend spend r;
                let c <- task_result id log store r;
                let _ <- Tasks.record_agent store run_id args.prompt (run_status r) started (run_summary r c);
                IO.pure (Result.ok c)
            }),
    }

/// A finished child's spend is the parent's too (a stopped child returns
/// its partial session; a failed one has none to report).
def add_spend (spend : Ref Usage) (r : Result String Session) : IO Unit :=
    match r {
        Result.ok final => Ref.modify spend (fn (u : Usage) => usage_add u final.spent),
        Result.err _ => IO.pure unit,
    }

/// The turn's `side_spend` seam over the same Ref: what the children
/// spent since the last dispatch, and the Ref starts over.
pub def Subagent.drain (spend : Ref Usage) : Unit -> IO Usage :=
    fn (_ : Unit) => do {
        let u <- Ref.get spend;
        let _ <- Ref.set spend usage_zero;
        IO.pure u
    }

/// The `/tasks` status word: the run ended with an answer or failed (a
/// stopped run comes back as a session too, so it reads as done).
def run_status (r : Result String Session) : String :=
    match r {
        Result.ok _ => "done",
        Result.err _ => "failed",
    }

/// The monitor's detail: the child's spend, then the answer's start (the
/// result's own footer sits at its end, past the cut for a long answer).
def run_summary (r : Result String Session) (c : Content) : String :=
    let text : String := match c {
        Content.tool_result _ out _ => Text.cut 2000 out,
        _ => "",
    } in
    match r {
        Result.ok final => String.concat (usage_footer final) (String.concat "\n" text),
        Result.err _ => text,
    }

/// The per-turn `task` tool. The registry is built each turn so the child
/// uses the CURRENT provider/model and the run's store/log; `stop` is the
/// parent's stop predicate, so Esc also ends a child at its boundaries.
/// `spend` collects the children's usage for `Subagent.drain`.
pub def Subagent.task_tool (cfg : ProviderConfig) (log : Option Logger)
    (store : Option StoreState) (stop : Unit -> IO Bool) (spend : Ref Usage) : ToolImpl :=
    { spec := Subagent.spec, cap := Capability.exec, run := run_task cfg log store stop spend }
