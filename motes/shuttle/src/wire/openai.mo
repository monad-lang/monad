/// The adapter between shuttle's own normalized `Message`/`Turn` and
/// `motes/openai`'s wire-faithful `ChatMessage`/`ChatRequest`/
/// `ChatResponse` -- agent-skills.md Design 3. Two harness-specific
/// facts live here, not in `motes/openai`: a `tool_calls[].function.
/// arguments` string is a SECOND JSON document that must be parsed
/// again, and OpenAI represents each tool result as its OWN message
/// (role `tool`, one `tool_call_id`), never several results folded
/// into one message's content the way shuttle's own `Message` allows.
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Usage, Turn}
use shuttle::tool {ToolSpec}
use openai::types {ChatMessage, ChatRequest, ChatResponse, Choice}
use openai::tool {ToolCall, ToolDef}
use openai::client {ApiUsage.tokens}
use json::json {Json, Json.ParseError.to_string}

def role_tag (r : Role) : String :=
    match r {
        Role.system_ => "system",
        Role.user => "user",
        Role.assistant => "assistant",
        Role.tool => "tool",
    }

def tool_spec_to_def (spec : ToolSpec) : ToolDef :=
    { name := spec.name, description := spec.description, parameters := spec.schema }

def content_text_of (c : Content) : Option String :=
    match c {
        Content.text s => Option.some s,
        // OpenAI's reasoning field carries TEXT only -- there is no
        // signature to forward, so it is dropped here and re-synthesized
        // as "" on the way back through the anthropic wire.
        Content.thinking s _ => Option.some s,
        _ => Option.none,
    }

#[partial]
def first_text (cs : List Content) : Option String :=
    match cs {
        List.empty => Option.none,
        List.cons c rest =>
            match content_text_of c {
                Option.some s => Option.some s,
                Option.none => first_text rest,
            }
    }

def content_to_tool_call (c : Content) : Option ToolCall :=
    match c {
        Content.tool_use id name input =>
            let tc : ToolCall := { id := id, name := name, arguments := Json.to_string input } in
            Option.some tc,
        _ => Option.none,
    }

#[partial]
def collect_tool_calls (cs : List Content) : List ToolCall :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            match content_to_tool_call c {
                Option.some tc => List.cons tc (collect_tool_calls rest),
                Option.none => collect_tool_calls rest,
            }
    }

def tool_result_to_message (c : Content) : Option ChatMessage :=
    match c {
        Content.tool_result call_id output is_error =>
            let m : ChatMessage := { role := "tool", content := Option.some output, tool_calls := List.empty, tool_call_id := Option.some call_id, name := Option.none } in
            Option.some m,
        _ => Option.none,
    }

#[partial]
def collect_tool_result_messages (cs : List Content) : List ChatMessage :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            match tool_result_to_message c {
                Option.some m => List.cons m (collect_tool_result_messages rest),
                Option.none => collect_tool_result_messages rest,
            }
    }

/// One shuttle `Message` becomes one or more `ChatMessage`s: a `tool`
/// message with several `Content.tool_result`s expands into one
/// `ChatMessage` per result (each its own `tool_call_id`); every other
/// role collapses its content into a single message.
def encode_message (m : Message) : List ChatMessage :=
    match m {
        Message.mk role content =>
            match role {
                Role.tool => collect_tool_result_messages content,
                _ =>
                    let chat_msg : ChatMessage :=
                        { role := role_tag role, content := first_text content, tool_calls := collect_tool_calls content, tool_call_id := Option.none, name := Option.none } in
                    List.cons chat_msg List.empty,
            }
    }

#[partial]
def encode_history (ms : List Message) : List ChatMessage :=
    match ms {
        List.empty => List.empty,
        List.cons m rest => List.append (encode_message m) (encode_history rest),
    }

pub def OpenAI.encode_request (cfg_model : String) (max_tokens : I64) (system : String) (tools : List ToolSpec) (history : List Message) : ChatRequest :=
    let system_msg : ChatMessage := { role := "system", content := Option.some system, tool_calls := List.empty, tool_call_id := Option.none, name := Option.none } in
    {
        model := cfg_model,
        messages := List.cons system_msg (encode_history history),
        tools := List.map tool_spec_to_def tools,
        max_tokens := Option.some max_tokens,
    }

pub def finish_reason_to_stop (s : String) : StopReason :=
    if s == "stop" then StopReason.end_turn
    else if s == "tool_calls" then StopReason.tool_use_stop
    else if s == "length" then StopReason.max_tokens
    else StopReason.other s

def tool_call_to_content (tc : ToolCall) : Result String Content :=
    match tc {
        ToolCall.mk id name arguments =>
            match Json.parse arguments {
                Result.err e => Result.err (Json.ParseError.to_string e),
                Result.ok input => Result.ok (Content.tool_use id name input),
            }
    }

#[partial]
def tool_calls_to_content (tcs : List ToolCall) : Result String (List Content) :=
    match tcs {
        List.empty => Result.ok List.empty,
        List.cons tc rest =>
            match tool_call_to_content tc {
                Result.err e => Result.err e,
                Result.ok c =>
                    match tool_calls_to_content rest {
                        Result.err e => Result.err e,
                        Result.ok cs => Result.ok (List.cons c cs),
                    }
            }
    }

pub def choice_content (msg : ChatMessage) : Result String (List Content) :=
    match msg {
        ChatMessage.mk msg_role msg_content msg_tool_calls msg_tool_call_id msg_name =>
            match tool_calls_to_content msg_tool_calls {
                Result.err e => Result.err e,
                Result.ok tool_content =>
                    match msg_content {
                        Option.some s => Result.ok (List.cons (Content.text s) tool_content),
                        Option.none => Result.ok tool_content,
                    },
            }
    }

/// Builds the final `Turn` in one shot, with the real token counts
/// already in place -- no intermediate zero-usage `Turn` is ever
/// constructed and later patched. (A two-step "build with placeholder
/// usage, then reconstruct with the real counts" version measurably
/// corrupts the value somewhere between the two steps -- probed
/// directly, not theoretical: the placeholder `Turn` destructures fine
/// on its own, but passing it into a second function that re-matches
/// `Turn.mk` fails at run time with `expected 2 constructor fields,
/// got 0`. One-shot construction sidesteps it entirely.)
pub def decode_choice (c : Choice) (prompt_tokens : I64) (completion_tokens : I64) : Result String Turn :=
    match c {
        Choice.mk msg finish_reason =>
            match choice_content msg {
                Result.err e => Result.err e,
                Result.ok decoded_content =>
                    let decoded_message : Message := { role := Role.assistant, content := decoded_content } in
                    let real_usage : Usage := { input_tokens := prompt_tokens, output_tokens := completion_tokens, cached_tokens := 0 } in
                    let decoded_turn : Turn := { message := decoded_message, usage := real_usage, stop := finish_reason_to_stop finish_reason } in
                    Result.ok decoded_turn,
            }
    }

def first_choice (choices : List Choice) : Option Choice :=
    match choices {
        List.empty => Option.none,
        List.cons c _ => Option.some c,
    }

pub def OpenAI.decode_response (resp : ChatResponse) : Result String Turn :=
    match resp {
        ChatResponse.mk resp_choices resp_usage =>
            match first_choice resp_choices {
                Option.none => Result.err "OpenAI response had no choices",
                Option.some resp_choice =>
                    match ApiUsage.tokens resp_usage {
                        Pair.pair p_tok c_tok => decode_choice resp_choice p_tok c_tok
                    },
            }
    }
