/// Context compaction: summarize the conversation into one system
/// message plus a recent tail, on demand (`/compact`) and automatically
/// before a turn when the ESTIMATED history crosses
/// `context_window * compact_at / 100` tokens.
///
/// History is append-only by design (turn deltas assume it); compaction
/// rewrites the SESSION value in memory and the store appends the result
/// as a new block whose sequence becomes the meta's `history_base`, so a
/// resume replays only from the compacted base. The visible transcript is
/// never rewritten -- only the model's context.
use shuttle::message {Message, Usage, Turn}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::session {Session}
use shuttle::provider {ProviderConfig, Provider.send, Provider.silent_emit}
use shuttle::context {history_tokens, message_tokens, usage_add}
use std::list {List.length, List.intercalate}
use init::transformers {ResultT, ResultT.run}

/// The estimated-token threshold; 0 (a zero window) disables autocompact.
pub def Compact.threshold (window : I64) (percent : I64) : I64 :=
    if window < 1i64 then 0i64 else window * percent / 100i64

/// What the summary has to keep: decisions, files touched, open tasks,
/// and the instructions the user asked `/compact` to add.
pub def Compact.summary_system : String :=
    "You are compacting a coding session into a summary for the same assistant to continue from. Record: what the user asked for, decisions made and why, files changed, commands run and their outcomes, and anything left unfinished. Be terse and factual; no preamble."

/// The context estimate: the history plus the system prompt and tool
/// schemas, which the per-message estimate does not see. `spent` is
/// cumulative billing, NOT the context size -- never use it here.
pub def Compact.estimate (s : Session) : I64 :=
    let prefix : I64 := (String.length s.system_prompt) / 4i64 + 1i64 + (List.length s.tools) * 50i64 in
    prefix + history_tokens s.history

pub def Compact.should_compact (threshold : I64) (s : Session) : Bool :=
    if threshold < 1i64 then false else I64.gt (Compact.estimate s) threshold

/// The tail budget: roughly a fifth of the threshold, so the summary
/// plus recent turns still leave room for the next request.
pub def Compact.keep_budget (threshold : I64) : I64 :=
    if threshold < 5i64 then 1i64 else threshold / 5i64

#[partial]
def drop_messages (n : I64) (ms : List Message) : List Message :=
    if n < 1i64 then ms
    else match ms {
        List.empty => ms,
        List.cons _ rest => drop_messages (n - 1i64) rest,
    }

def role_is_user (m : Message) : Bool :=
    match m { { role, .. } => match role { Role.user => true, _ => false } }

/// The first USER-message boundary whose remaining tail fits the
/// budget: a kept tail never begins with an orphan tool result (both
/// wires reject that), and never begins mid tool_use/result pair.
/// One pass, O(n): `seen` is the tokens before the current message, so
/// the suffix's size is `total - seen`. The first version re-walked the
/// list (`List.length`, `drop_messages`, `history_tokens`) at every user
/// boundary -- quadratic in a long session, exactly when compaction has
/// to run.
#[partial]
def find_split_go (history : List Message) (total : I64) (i : I64) (seen : I64) (budget : I64) : I64 :=
    match history {
        List.empty => 0i64 - 1i64,
        List.cons m rest =>
            let suffix : I64 := total - seen in
            if Bool.and (role_is_user m) (Bool.not (I64.gt suffix budget))
            then i
            else find_split_go rest total (i + 1i64) (seen + message_tokens m) budget,
    }

def find_split (history : List Message) (budget : I64) : I64 :=
    find_split_go history (history_tokens history) 0i64 0i64 budget

/// The recent messages kept verbatim; empty when no user boundary fits
/// (the summary is then the whole context).
pub def Compact.keep_tail (history : List Message) (budget : I64) : List Message :=
    let split : I64 := find_split history budget in
    if split < 0i64 then List.empty else drop_messages split history

#[partial]
def render_content (c : Content) : String :=
    match c {
        Content.text s => s,
        Content.tool_use _ name input => String.concat "[tool " (String.concat name "]"),
        Content.tool_result _ output is_error =>
            let mark : String := if is_error then "[tool result error] " else "[tool result] " in
            String.concat mark output,
        Content.thinking s _ => "",
    }

/// Accumulate each part's text (with its trailing newline) and join in
/// ONE pass: the old right-nested `part ++ rest` re-copied the whole
/// remainder per message, which on a long session is quadratic memory --
/// the compaction prompt is the biggest string weaver builds.
#[partial]
def render_contents_go (cs : List Content) (acc : List String) : List String :=
    match cs {
        List.empty => acc,
        List.cons c rest =>
            let part : String := render_content c in
            if String.is_empty part
            then render_contents_go rest acc
            else render_contents_go rest (List.cons (String.concat part "\n") acc),
    }

def render_contents (cs : List Content) : String :=
    String.concat_list (List.reverse (render_contents_go cs List.empty))

#[partial]
def render_msgs_go (ms : List Message) (acc : List String) : List String :=
    match ms {
        List.empty => acc,
        List.cons m rest =>
            let label : String := match m.role {
                Role.user => "user: ",
                Role.assistant => "assistant: ",
                Role.system_ => "system: ",
                Role.tool => "tool: ",
            } in
            let part : String := String.concat label (render_contents m.content) in
            render_msgs_go rest (List.cons part acc),
    }

def render_history (ms : List Message) : String :=
    List.intercalate "\n\n" (List.reverse (render_msgs_go ms List.empty))

/// The summarization request: the transcript plus any user instructions.
pub def Compact.summary_prompt (history : List Message) (instructions : String) : String :=
    let ask : String := "Summarize the session below so the assistant can continue it from your summary alone." in
    let extra : String := if String.is_empty instructions then "" else String.concat "\n\nThe user asks you to focus on: " (String.concat instructions "\n") in
    let parts : List String := [ask, extra, "\n\n---\n\n", render_history history] in
    String.concat_list parts

#[partial]
def first_text (cs : List Content) : Result String String :=
    match cs {
        List.empty => Result.err "compaction: the summary came back empty",
        List.cons c rest => match c {
            Content.text s => if String.is_empty s then first_text rest else Result.ok s,
            _ => first_text rest
        },
    }

/// One compaction: summarize `before`, keep the newest tail, and return
/// the rewritten session with the summarization call's usage added.
pub struct Compact.Outcome {
    session : Session,
    before : I64,
    after : I64,
    tokens : I64,
}

pub def Compact.compact (cfg : ProviderConfig) (session : Session) (threshold : I64) (instructions : String) : IO (Result String Compact.Outcome) := do {
    let prompt : String := Compact.summary_prompt session.history instructions;
    let msg : Message := { role := Role.user, content := List.cons (Content.text prompt) List.empty };
    let r <- ResultT.run (Provider.send cfg Compact.summary_system List.empty [msg] Provider.silent_emit);
    match r {
        Result.err e => return (Result.err e),
        Result.ok turn => compact_finish session threshold turn,
    }
}

/// The summary's text, or the named failure. A summary cut off by
/// `max_tokens` is refused: storing a truncated summary would discard
/// the real history and resume from a mid-sentence fragment.
def compact_finish (session : Session) (threshold : I64) (turn : Turn) : IO (Result String Compact.Outcome) :=
    match turn.stop {
        StopReason.max_tokens =>
            IO.pure (Result.err "compaction: the summary hit max_tokens; raise max_tokens and retry"),
        _ => match first_text turn.message.content {
            Result.err e => IO.pure (Result.err e),
            Result.ok text => IO.pure (Result.ok (compact_rebuilt session threshold turn.usage text)),
        },
    }

/// The rewritten session: the summary as a system message, then the
/// recent tail; the summarization call's usage lands in `spent`.
def compact_rebuilt (session : Session) (threshold : I64) (u : Usage) (text : String) : Compact.Outcome :=
    let keep : List Message := Compact.keep_tail session.history (Compact.keep_budget threshold) in
    let note_text : String := String.concat "[summary of earlier conversation]\n" text in
    let note : Message := { role := Role.system_, content := List.cons (Content.text note_text) List.empty } in
    let history2 : List Message := List.cons note keep in
    let spent2 : Usage := usage_add session.spent u in
    let sess2 : Session := { session with history := history2, spent := spent2 } in
    let out : Compact.Outcome := { session := sess2, before := List.length session.history, after := List.length history2, tokens := Compact.estimate sess2 } in
    out
