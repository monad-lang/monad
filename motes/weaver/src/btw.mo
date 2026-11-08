/// `/btw <question>`: a side question answered beside the running turn.
///
/// One model call with no tools and a one-call budget, like the session
/// title (`title.mo`). The conversation reaches the model as TEXT (user and
/// assistant prose only, the newest ~24 KB): a request whose history holds
/// `tool_use`/`tool_result` blocks must declare tools, and this call has
/// none. Nothing it does touches the session -- not the history, not the
/// spend.
use shuttle::loop {Loop.run}
use shuttle::registry {ToolRegistry}
use shuttle::gate {Gate}
use shuttle::session {Session}
use shuttle::provider {ProviderConfig}
use shuttle::message {Message}
use shuttle::message_types {Role, Content}
use init::transformers {ResultT}
use weaver::title {Title.last_text, Title.silent_emit}
use std::list {List.intercalate}

/// The context's byte budget: the newest messages that fit.
pub def Btw.context_bytes : I64 := 24576

pub def Btw.max_reply_tokens : I64 := 1024

pub def Btw.system_prompt : String :=
    "You answer a side question about an ongoing coding session. The conversation so far is quoted below as text. Answer briefly and directly from it. You have no tools, and the main task keeps running separately."

/// A message's prose: its text blocks, tool traffic and thinking dropped.
#[partial]
def prose (cs : List Content) (acc : String) : String :=
    match cs {
        List.empty => acc,
        List.cons c rest => match c {
            Content.text s => prose rest (if String.is_empty acc then s else String.concat acc (String.concat "\n" s)),
            _ => prose rest acc,
        },
    }

def speaker (r : Role) : String :=
    match r {
        Role.user => "User",
        Role.assistant => "Assistant",
        _ => "",
    }

/// One quoted turn, or "" for a message with no prose or no speaker.
def quoted (m : Message) : String :=
    let who : String := speaker m.role in
    let text : String := prose m.content "" in
    if Bool.or (String.is_empty who) (String.is_empty text) then ""
    else String.concat who (String.concat ": " text)

/// Newest first, while the budget lasts; the result reads oldest first.
#[partial]
def newest (ms : List Message) (budget : I64) (acc : List String) : List String :=
    match ms {
        List.empty => acc,
        List.cons m rest =>
            let q : String := quoted m in
            if String.is_empty q then newest rest budget acc
            else if I64.lt budget (String.length q) then acc
            else newest rest (budget - String.length q) (List.cons q acc),
    }

/// The one user message the model sees: the quoted conversation, then
/// the question.
pub def Btw.prompt (history : List Message) (question : String) : String :=
    let turns : List String := newest (List.reverse history) Btw.context_bytes List.empty in
    let context : String :=
        if List.is_empty turns then "(no conversation yet)"
        else List.intercalate "\n\n" turns in
    String.concat_list ["Conversation so far:\n\n", context, "\n\nSide question: ", question]

/// Ask: the answer text, or why there is none.
pub def Btw.ask (cfg : ProviderConfig) (history : List Message) (question : String) : IO (Result String String) := do {
    let msg : Message := { role := Role.user, content := List.cons (Content.text (Btw.prompt history question)) List.empty };
    let cfg2 : ProviderConfig := { cfg with max_tokens := Btw.max_reply_tokens, thinking := false };
    let r <- ResultT.run (Loop.run cfg2 ToolRegistry.empty Btw.system_prompt (List.cons msg List.empty) 1 Title.silent_emit Gate.auto);
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok s => btw_answer s,
    }
}

def btw_answer (s : Session) : IO (Result String String) :=
    let t : String := Title.last_text s in
    if String.is_empty (String.trim t) then IO.pure (Result.err "the model gave no answer")
    else IO.pure (Result.ok t)
