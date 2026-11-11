/// Wraps shuttle's `write`/`edit` tools so the tool result carries the hunk
/// diff (weaver.md Phase 16). The transcript renders it; the model sees the
/// same text, so it is capped. The old side of a `write` is read BEFORE the
/// tool runs -- after the write both sides are the new content.
use shuttle::tool {ToolImpl}
use shuttle::message_types {Content}
use init::transformers {ResultT}
use json::json {Json}
use weaver::diff {Diff.for_input, Diff.render}
use weaver::diff_hunks {DiffHunks.hunks, DiffHunks.render_text, DiffHunks.cut_utf8}

/// Byte cap on the appended diff. Past it the tail is dropped with a marker.
pub def DiffTool.max_bytes : I64 := 32000

/// The line that separates the tool's own result from the appended diff.
/// A unique marker (not a `\n@@ ` scan) so a result that itself contains
/// patch text -- a read `.patch`, `git diff` from the shell -- is not
/// mistaken for an appended diff, and a multi-hunk diff splits at its head.
pub def DiffTool.sep : String := "\n[weaver diff]\n"

/// Inputs larger than this are not diffed: Myers is bounded but the line
/// split is not, and a full-file rewrite would spend the turn in the tool.
pub def DiffTool.max_input : I64 := 1000000

def too_big (old : String) (new : String) : Bool :=
    I64.gt (String.length old + String.length new) DiffTool.max_input

/// The FIRST occurrence of `sep`, or -1.
#[partial]
def find_sep_at (s : String) (i : I64) : I64 :=
    let n : I64 := String.length s in
    let m : I64 := String.length DiffTool.sep in
    if I64.gt (i + m) n
    then -1
    else if String.slice s i m == DiffTool.sep
    then i
    else find_sep_at s (i + 1)

/// Split one tool result into its own output and the appended diff, when
/// the wrapper added one. Used by the TUI transcript and dumb mode.
pub def DiffTool.split (output : String) : Option (Pair String String) :=
    let i : I64 := find_sep_at output 0 in
    if I64.lt i 0
    then Option.none
    else Option.some (Pair.pair (String.slice output 0 i) (String.drop (i + String.length DiffTool.sep) output))

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

pub def DiffTool.capped (diff : String) : String :=
    if I64.gt (String.length diff) DiffTool.max_bytes
    then String.concat (DiffHunks.cut_utf8 diff DiffTool.max_bytes) "\n... (diff truncated)"
    else diff

/// The hunk render, or the trim render past the edit-distance bound.
def diff_text (old : String) (new : String) : Option String :=
    match DiffHunks.hunks old new {
        Option.some hs =>
            let t : String := DiffHunks.render_text hs in
            if String.is_empty t then Option.none else Option.some t,
        Option.none =>
            let t : String := Diff.render old new in
            if String.is_empty t then Option.none else Option.some t,
    }

def append_hunks (c : Content) (old : String) (new : String) : Content :=
    if too_big old new
    then
        let note : String := "\n... (diff omitted: input over 1 MB)" in
        match result_output c {
            Option.none => c,
            Option.some output => with_text c (String.concat output note),
        }
    else match diff_text old new {
        Option.none => c,
        Option.some text => match result_output c {
            Option.none => c,
            Option.some output => with_text c (String.concat output (String.concat DiffTool.sep (DiffTool.capped text))),
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
