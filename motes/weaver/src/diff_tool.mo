/// Wraps shuttle's `write`/`edit` tools so the tool result carries the hunk
/// diff (weaver.md Phase 16). The transcript renders it; the model sees the
/// same text, so it is capped. The old side of a `write` is read BEFORE the
/// tool runs -- after the write both sides are the new content.
use shuttle::tool {ToolImpl}
use shuttle::message_types {Content}
use init::transformers {ResultT}
use json::json {Json}
use weaver::diff {Diff.for_input}
use weaver::diff_hunks {DiffHunks.hunks, DiffHunks.render_text}

/// Byte cap on the appended diff. Past it the tail is dropped with a marker.
pub def DiffTool.max_bytes : I64 := 32000

/// Inputs larger than this are not diffed: Myers is bounded but the line
/// split is not, and a full-file rewrite would spend the turn in the tool.
pub def DiffTool.max_input : I64 := 1000000

def too_big (old : String) (new : String) : Bool :=
    I64.gt (String.length old + String.length new) DiffTool.max_input

def result_output (c : Content) : Option String :=
    match c {
        Content.tool_result _ output is_error => if is_error then Option.none else Option.some output,
        _ => Option.none,
    }

def with_text (c : Content) (text : String) : Content :=
    match c {
        Content.tool_result id output is_error => Content.tool_result id text is_error,
        _ => c,
    }

def capped (diff : String) : String :=
    if I64.gt (String.length diff) DiffTool.max_bytes
    then String.concat (String.slice diff 0 DiffTool.max_bytes) "\n... (diff truncated)"
    else diff

def append_hunks (c : Content) (old : String) (new : String) : Content :=
    if too_big old new
    then
        let note : String := "\n... (diff omitted: input over 1 MB)" in
        match result_output c {
            Option.none => c,
            Option.some output => with_text c (String.concat output note),
        }
    else match DiffHunks.hunks old new {
        Option.none => c,
        Option.some hs =>
            let text : String := DiffHunks.render_text hs in
            if String.is_empty text
            then c
            else match result_output c {
                Option.none => c,
                Option.some output => with_text c (String.concat output (String.concat "\n" (capped text))),
            },
    }

def with_pair (c : Content) (pair : Option (Pair String String)) : Content :=
    match pair {
        Option.none => c,
        Option.some pr => match pr {
            Pair.pair old new => append_hunks c old new,
        },
    }

def wrapped_run (impl : ToolImpl) (id : String) (j : Json) : ResultT String IO Content :=
    ResultT.mk (do {
        // Before the run: a `write`'s old side is read here.
        let pair <- Diff.for_input impl.spec.name j;
        let r <- ResultT.run (impl.run id j);
        match r {
            Result.err e => IO.pure (Result.err e),
            Result.ok c => IO.pure (Result.ok (with_pair c pair)),
        }
    })

/// `impl` with its result enriched by a hunk diff. Apply to `write`/`edit`;
/// other tools' `Diff.for_input` answers none and the result is untouched.
pub def DiffTool.wrap (impl : ToolImpl) : ToolImpl :=
    let t : ToolImpl := { spec := impl.spec, cap := impl.cap, run := wrapped_run impl } in
    t
