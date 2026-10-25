/// The adapter between shuttle's own normalized `Message`/`Turn` and
/// `motes/anthropic`'s wire-faithful `MessagesRequest`/
/// `MessagesResponse` -- agent-skills.md Design 3. The harness-level
/// facts live here, not in `motes/anthropic`:
///   * `system` is a TOP-LEVEL request field -- a normalized
///     `Role.system_` message mid-history folds into it, never into
///     `messages` (the wire only allows `user`/`assistant` there).
///   * ALL `Content.tool_result`s answering one assistant turn go in
///     a SINGLE user message -- the wire accepts them split across
///     messages and silently degrades parallel tool calling, so the
///     adapter must never split them (Design 3's own "encode as a
///     test, not a production discovery" fact).
///   * `tool_use.input` is already a real JSON object on this wire --
///     NO second parse, unlike the OpenAI adapter's
///     `function.arguments`.
///   * `stop_reason: "refusal"` maps to `StopReason.refusal`, not an
///     error -- it arrives in an ordinary HTTP 200 body.
///   * `cache_read_input_tokens` is the wire name for what the
///     normal form calls `cached_tokens`; the last tool def carries a
///     `cache_control` breakpoint (the tool table is the stable
///     prefix of every request in a turn loop -- the standard
///     breakpoint location; Phase 5's context management owns any
///     refinement).
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Usage, Turn}
use shuttle::tool {ToolSpec}
use anthropic::types {Block, AnthropicMessage, AnthropicTool, MessagesRequest, MessagesResponse, AnthropicUsage}
use json::json {Json}

def content_to_block (c : Content) : Block :=
    match c {
        Content.text s => Block.text s false,
        // The signature rides straight through: replaying an API-authored
        // thinking block without it is a 400 on the next request.
        Content.thinking s signature => Block.thinking s signature false,
        Content.tool_use id name input => Block.tool_use id name input false,
        // `call_id` is the normal form's name; the wire field is
        // `tool_use_id`. This is the one rename in either direction.
        Content.tool_result call_id output is_error => Block.tool_result call_id output is_error false,
    }

def spec_to_tool (spec : ToolSpec) : AnthropicTool :=
    { name := spec.name, description := spec.description, input_schema := spec.schema, cache := false }

def cache_tool (t : AnthropicTool) : AnthropicTool :=
    match t {
        AnthropicTool.mk name description input_schema _ => AnthropicTool.mk name description input_schema true,
    }

/// Mark the LAST tool as the cache breakpoint -- with one, the cache
/// prefix ends where the stable tool table ends, which is the
/// documented use for tool-bearing requests.
#[partial]
def mark_last_tool_cached (ts : List AnthropicTool) : List AnthropicTool :=
    match ts {
        List.empty => List.empty,
        List.cons t rest =>
            match rest {
                List.empty => List.cons (cache_tool t) List.empty,
                List.cons _ _ => List.cons t (mark_last_tool_cached rest),
            },
    }

/// A normalized message becomes exactly ONE wire message -- the
/// parallel-tool-call rule above means a `Role.tool` message's several
/// `tool_result`s share one `user` message rather than splitting.
def encode_one (m : Message) : AnthropicMessage :=
    match m {
        Message.mk role content =>
            let blocks : List Block := List.map (fn (c : Content) => content_to_block c) content in
            let wire_role : String :=
                match role {
                    Role.user => "user",
                    Role.assistant => "assistant",
                    // tool results ride in a `user` message on this wire
                    Role.tool => "user",
                    // unreachable from `encode_message_list` (which skips
                    // `system_`), but total anyway
                    Role.system_ => "user",
                } in
            { role := wire_role, content := blocks },
    }

#[partial]
def encode_message_list (ms : List Message) : List AnthropicMessage :=
    match ms {
        List.empty => List.empty,
        List.cons m rest =>
            match m {
                Message.mk role _ =>
                    match role {
                        // The wire has no system role in `messages`; its text
                        // folds into the top-level system blocks instead.
                        Role.system_ => encode_message_list rest,
                        _ => List.cons (encode_one m) (encode_message_list rest),
                    },
            },
    }

#[partial]
def system_blocks_of (ms : List Message) : List Block :=
    match ms {
        List.empty => List.empty,
        List.cons m rest =>
            match m {
                Message.mk role content =>
                    match role {
                        Role.system_ => List.append (List.map (fn (c : Content) => content_to_block c) content) (system_blocks_of rest),
                        _ => system_blocks_of rest,
                    },
            },
    }

/// `effort` stays unset; `thinking` comes from the provider config
/// (off by default -- it costs tokens and latency). The wire type
/// carries both (`motes/anthropic`'s own tests pin the shapes).
pub def Anthropic.encode_request (cfg_model : String) (max_tokens : I64) (thinking : Bool) (system : String) (tools : List ToolSpec) (history : List Message) : MessagesRequest :=
    let system_block : Block := Block.text system false in
    let system_blocks : List Block := List.cons system_block (system_blocks_of history) in
    let wire_tools : List AnthropicTool := mark_last_tool_cached (List.map (fn (spec : ToolSpec) => spec_to_tool spec) tools) in
    let wire_messages : List AnthropicMessage := encode_message_list history in
    {
        model := cfg_model,
        max_tokens := max_tokens,
        system := system_blocks,
        messages := wire_messages,
        tools := wire_tools,
        thinking := thinking,
        effort := Option.none,
    }

/// `stop_reason` mapping -- `"refusal"` is a STOP REASON here, not an
/// error: it arrives in an HTTP 200 body and the loop treats it as
/// any other non-tool-use end of turn.
def stop_reason_of (s : String) : StopReason :=
    if s == "end_turn" then StopReason.end_turn
    else if s == "tool_use" then StopReason.tool_use_stop
    else if s == "max_tokens" then StopReason.max_tokens
    else if s == "refusal" then StopReason.refusal
    else StopReason.other s

def block_to_content (b : Block) : Content :=
    match b {
        Block.text s _ => Content.text s,
        Block.thinking s signature _ => Content.thinking s signature,
        // `input` is a decoded `Json` object already -- no second
        // parse, unlike the OpenAI wire's string-encoded arguments.
        Block.tool_use id name input _ => Content.tool_use id name input,
        Block.tool_result tool_use_id content is_error _ => Content.tool_result tool_use_id content is_error,
    }

/// One-shot `Turn` construction with the real token counts in place
/// -- the same rule `wire/openai.mo`'s `decode_choice` header
/// documents: never build a placeholder `Turn` and patch it after.
pub def Anthropic.decode_response (resp : MessagesResponse) : Result String Turn :=
    match resp {
        MessagesResponse.mk blocks stop_reason usage =>
            match usage {
                AnthropicUsage.mk input_tokens output_tokens cache_read =>
                    let decoded_content : List Content := List.map (fn (b : Block) => block_to_content b) blocks in
                    let decoded_message : Message := { role := Role.assistant, content := decoded_content } in
                    // Anthropic reports cache reads SEPARATELY from
                    // `input_tokens`; normalize so `Usage.input_tokens` is
                    // the whole prompt on every wire (OpenAI's
                    // `prompt_tokens` already includes cached tokens).
                    let real_usage : Usage := { input_tokens := input_tokens + cache_read, output_tokens := output_tokens, cached_tokens := cache_read } in
                    let decoded_turn : Turn := { message := decoded_message, usage := real_usage, stop := stop_reason_of stop_reason } in
                    Result.ok decoded_turn,
            },
    }
