/// Context management -- agent-skills.md Phase 5: token accounting from
/// `Usage`, oldest-first trimming of tool results, and the byte-stable
/// cached prefix after the system prompt and tool list.
///
/// The token ESTIMATES here are heuristics (`String.length / 4`), not
/// model tokenizer output: providers do not report per-message token
/// counts, and `Usage` is only reported per whole turn. They are for
/// TRIMMING decisions only; the reported `Usage` numbers are the real
/// accounting and are never estimated.
use shuttle::message {Message, Usage}
use shuttle::message_types {Content}
use shuttle::tool {ToolSpec}
use json::json {Json}
use std::list {List.length}

/// The identity for `usage_add`: a turn that cost nothing.
pub def usage_zero : Usage := { input_tokens := 0, output_tokens := 0, cached_tokens := 0 }

/// Sum two `Usage` values field by field -- how the loop accumulates
/// `spent` across turns.
pub def usage_add (a : Usage) (b : Usage) : Usage :=
    let out : Usage := {
        input_tokens := a.input_tokens + b.input_tokens,
        output_tokens := a.output_tokens + b.output_tokens,
        cached_tokens := a.cached_tokens + b.cached_tokens,
    } in
    out

/// Total tokens actually billed for a `Usage`: input plus output.
/// `cached_tokens` is a subset of `input_tokens` (what the provider
/// charged less for), not an extra line item, so it is not added.
pub def usage_total (u : Usage) : I64 :=
    u.input_tokens + u.output_tokens

/// Rough token estimate for a string: four bytes per token, minimum 1.
/// Used only to decide what to trim; see the module header.
pub def estimate_tokens (s : String) : I64 :=
    (String.length s) / 4 + 1

def sum_i64 (xs : List I64) : I64 :=
    match xs {
        List.empty => 0,
        List.cons h t => h + sum_i64 t,
    }

pub def content_tokens (c : Content) : I64 :=
    match c {
        Content.text s => estimate_tokens s,
        Content.tool_use _ name input => estimate_tokens (String.concat name (Json.to_string input)),
        Content.tool_result _ output _ => estimate_tokens output,
        Content.thinking s _ => estimate_tokens s,
    }

pub def message_tokens (m : Message) : I64 :=
    match m {
        { content, .. } => sum_i64 (List.map content_tokens content),
    }

pub def history_tokens (history : List Message) : I64 :=
    sum_i64 (List.map message_tokens history)

/// The stub a trimmed `tool_result` carries. `is_error` stays false: a
/// trimmed result is not a tool failure, and the model must not treat it
/// as one.
def trimmed_marker : String := "[trimmed by the shuttle context manager]"

def stub_content (c : Content) : Content :=
    match c {
        Content.tool_result call_id _ _ =>
            let stubbed : Content := Content.tool_result call_id trimmed_marker false in
            stubbed,
        _ => c,
    }

/// Replace every `tool_result` output in a message with the trim stub.
pub def stub_tool_results (m : Message) : Message :=
    match m {
        { role, content, .. } =>
            let stubbed : Message := { role := role, content := List.map stub_content content } in
            stubbed,
    }

#[partial]
def trim_over (budget : I64) (pos : I64) (len : I64) (used : I64) (m : Message) (rest : List Message) : List Message :=
    let stubbed : Message := stub_tool_results m in
    List.cons stubbed (trim_walk budget (pos + 1) len (used + message_tokens stubbed) rest)

#[partial]
def trim_cons (budget : I64) (pos : I64) (len : I64) (used : I64) (m : Message) (rest : List Message) : List Message :=
    if pos + 1 == len then List.cons m rest
    else if Bool.not (budget < used + message_tokens m) then
        List.cons m (trim_walk budget (pos + 1) len (used + message_tokens m) rest)
    else trim_over budget pos len used m rest

/// Walk the history oldest-first, keeping each message intact while the
/// running estimate fits `budget` and stubbing the tool results of every
/// message past it. The NEWEST message (the last) is never touched --
/// the model's most recent turn and its tool results stay legible.
#[partial]
def trim_walk (budget : I64) (pos : I64) (len : I64) (used : I64) (history : List Message) : List Message :=
    match history {
        List.empty => List.empty,
        List.cons m rest => trim_cons budget pos len used m rest,
    }

/// Oldest-first trimming of tool results: messages are kept byte-for-byte
/// while the estimated total fits `budget`; once it does not, each
/// further message's `tool_result` outputs are replaced by the trim
/// stub (text and `tool_use` blocks are left alone -- only tool OUTPUT
/// is trimmed, never the request that produced it). The newest message
/// is exempt. History is oldest-first: the loop appends at the end.
pub def trim (budget : I64) (history : List Message) : List Message :=
    if Bool.not (budget < history_tokens history) then history
    else trim_walk budget 0 (List.length history) 0 history

#[partial]
def tools_prefix (tools : List ToolSpec) : String :=
    match tools {
        List.empty => "",
        List.cons t rest => String.concat (Json.to_string (ToolSpec.serialize_json t)) (String.concat "\n" (tools_prefix rest)),
    }

/// The byte-stable prompt prefix a provider may cache: the system
/// prompt, then the serialized tool list in registry order. Everything
/// that feeds it is deterministic by construction -- the registry is a
/// `BTreeMap`, so `ToolRegistry.specs` order is key order, and nothing
/// here contributes a timestamp or per-request id -- so the same
/// (system, tools) pair produces the same bytes on every call, which is
/// what makes a provider-side prompt cache actually hit. The wire-level
/// breakpoint marker is the adapter's own (`wire/anthropic.mo` marks the
/// last tool with `cache_control`).
pub def cached_prefix (system : String) (tools : List ToolSpec) : String :=
    String.concat system (String.concat "\n" (tools_prefix tools))
