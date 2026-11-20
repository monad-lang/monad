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
use std::list {}

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

/// Total prompt + output tokens for a `Usage`. The wires normalize
/// `input_tokens` to the WHOLE prompt (Anthropic's cache reads and
/// cache writes are folded in by `wire/anthropic.mo`; OpenAI's
/// `prompt_tokens` already includes cached), so `cached_tokens` is a
/// subset and is not added again -- it is the cheaper slice, not an
/// extra line item.
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

/// The stub a trimmed `tool_result` carries: the same marker text
/// whatever the output was.
def trimmed_marker : String := "[trimmed by the shuttle context manager]"

/// The trim stub keeps `was_error`: a trimmed result must not flip a
/// real tool failure into a success (or the reverse) -- the model
/// would reason from the wrong outcome.
def stub_content (c : Content) : Content :=
    match c {
        Content.tool_result call_id _ was_error =>
            Content.tool_result call_id trimmed_marker was_error,
        _ => c,
    }

/// Replace every `tool_result` output in a message with the trim stub.
pub def stub_tool_results (m : Message) : Message :=
    match m {
        { role, content, .. } =>
            let stubbed : Message := { role := role, content := List.map stub_content content } in
            stubbed,
    }

/// What stubbing a message saves, by the same estimate `trim` budgets with.
/// A function of the message alone, so the prefix `trim` cuts is stable
/// while the history grows (the history is append-only).
def stub_savings (m : Message) : I64 :=
    message_tokens m - message_tokens (stub_tool_results m)

/// Stub oldest-first until `saved` reaches `target`; the rest, and always
/// the NEWEST message, stay byte-for-byte.
#[partial]
def stub_prefix (target : I64) (saved : I64) (left : I64) (history : List Message) : List Message :=
    match history {
        List.empty => List.empty,
        List.cons m rest =>
            if Bool.or (I64.lt left 2i64) (Bool.not (saved < target)) then history
            else List.cons (stub_tool_results m) (stub_prefix target (saved + stub_savings m) (left - 1i64) rest),
    }

/// Oldest-first trimming of tool results. Under `budget` the history is
/// returned as is. Over it, the OLDEST messages' `tool_result` outputs
/// become the trim stub (text and `tool_use` blocks stay: only tool OUTPUT
/// is trimmed, never the request that produced it) until the estimate is
/// back near 70% of the budget. The newest message is exempt.
///
/// The amount to save is rounded UP to a multiple of 30% of the budget, so
/// the cut moves only after that much growth: between moves every request
/// sends a byte-identical prefix, which is what lets a provider's prompt
/// cache keep hitting through a long tool loop.
pub def trim (budget : I64) (history : List Message) : List Message :=
    let total : I64 := history_tokens history in
    if Bool.not (budget < total) then history
    else
        let chunk0 : I64 := budget * 3i64 / 10i64 in
        let chunk : I64 := if I64.lt chunk0 1i64 then 1i64 else chunk0 in
        let excess : I64 := total - budget * 7i64 / 10i64 in
        let target : I64 := (excess + chunk - 1i64) / chunk * chunk in
        stub_prefix target 0i64 (List.length history) history

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

// ── Tool-output cap ────────────────────────────────────────────────────
//
// One tool result is the unit that can blow a context: a 4 MB binary
// read measured ~1M tokens and the provider rejected the next request
// with HTTP 400. The cap is applied where results ENTER the history
// (the loop) and by the read tool before numbering.

/// The most text one tool result contributes. Every byte is re-sent on
/// each later request, so this is a token budget (~12k tokens), with room
/// above `read`'s own 32 KiB page for its gutter and paging marker.
pub def Context.tool_output_max : I64 := 49152

/// A prefix no longer than `max`, ending on a UTF-8 boundary (the
/// runtime's slice answers "" when its end offset is a continuation
/// byte), with a note naming what was dropped.
#[partial]
def cap_slice (text : String) (max : I64) (back : I64) : String :=
    if I64.gt back 3i64 then ""
    else if I64.lt (max - back) 1i64 then ""
    else
        let s : String := String.slice text 0 (max - back) in
        if String.is_empty s then cap_slice text max (back + 1i64) else s

pub def Context.cap_text (text : String) (max : I64) : String :=
    let n : I64 := String.length text in
    if Bool.not (I64.gt n max) then text
    else
        let note : String := String.concat "\n[truncated: "
            (String.concat (I64.to_string n) " bytes total; narrow the command or page the source]") in
        String.concat (cap_slice text max 0i64) note
