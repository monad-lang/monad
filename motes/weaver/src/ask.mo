/// The `ask` tool: pose one question with concrete choices (single or
/// multi select, plus a free-text answer) instead of guessing. The UI
/// seam is injected at registration, so the core is pure and testable.
///
/// In `auto` mode the tool NEVER consults the seam: an unattended plan
/// must not block on a human, so it answers with the recommended (else
/// first) option and says so in the result, and the model records the
/// assumption in the plan.
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::message_types {Content}
use json::json {
    Json, Json.get_object, Json.get_array, Json.get_str, Json.get_bool,
    Json.object_get, Json.make_object_pairs, Json.make_array, Json.make_str, Json.make_bool,
}
use std::map {Map, BTreeMap}
use std::list {List.intercalate}
use init::transformers {ResultT}
use weaver::policy {Mode, Mode.is_auto}

pub struct AskOption {
    label : String,
    description : String := "",
    /// The option auto mode assumes when no one is attending.
    recommended : Bool := false,
}

pub struct AskSpec {
    question : String,
    options : List AskOption,
    multi : Bool := false,
    allow_other : Bool := true,
}

/// One answer. `picked` are option indices (the multi set in toggle
/// order); `other` is the typed answer; `cancelled` means Esc/EOF.
pub struct AskReply {
    picked : List I64,
    other : String,
    cancelled : Bool,
    auto : Bool,
}

/// The UI seam: the TUI opens a dialog, the line UI reads a line.
pub struct AskSeam {
    ask : AskSpec -> IO AskReply,
}

// ── decoding ────────────────────────────────────────────────────────────

def str_field (key : String) (obj : BTreeMap String Json) : Option String :=
    match Json.object_get key obj {
        Option.none => Option.none,
        Option.some j => match Json.get_str j {
            Result.ok s => if String.is_empty (String.trim s) then Option.none else Option.some (String.trim s),
            Result.err _ => Option.none,
        },
    }

def bool_field (key : String) (dflt : Bool) (obj : BTreeMap String Json) : Bool :=
    match Json.object_get key obj {
        Option.none => dflt,
        Option.some j => match Json.get_bool j {
            Result.ok b => b,
            Result.err _ => dflt,
        },
    }

def array_field (key : String) (obj : BTreeMap String Json) : List Json :=
    match Json.object_get key obj {
        Option.none => List.empty,
        Option.some j => match Json.get_array j {
            Result.ok xs => xs,
            Result.err _ => List.empty,
        },
    }

def decode_option (j : Json) : Result String AskOption :=
    match Json.get_object j {
        Result.err _ => Result.err "each option must be an object with a label",
        Result.ok o => match str_field "label" o {
            Option.none => Result.err "each option needs a non-empty label",
            Option.some label =>
                let desc : String := match str_field "description" o {
                    Option.none => "",
                    Option.some d => d,
                } in
                let rec : Bool := bool_field "recommended" false o in
                let out : AskOption := { label := label, description := desc, recommended := rec } in
                Result.ok out,
        },
    }

#[partial]
def decode_options (js : List Json) (acc : List AskOption) : Result String (List AskOption) :=
    match js {
        List.empty => Result.ok (List.reverse acc),
        List.cons j rest => match decode_option j {
            Result.err e => Result.err e,
            Result.ok o => decode_options rest (List.cons o acc),
        },
    }

#[partial]
def count_recommended (os : List AskOption) : I64 :=
    match os {
        List.empty => 0,
        List.cons o rest => (if o.recommended then 1 else 0) + count_recommended rest,
    }

#[partial]
def has_label (l : String) (os : List AskOption) : Bool :=
    match os {
        List.empty => false,
        List.cons o rest => if String.beq o.label l then true else has_label l rest,
    }

#[partial]
def duplicate_labels (os : List AskOption) : Bool :=
    match os {
        List.empty => false,
        List.cons o rest => if has_label o.label rest then true else duplicate_labels rest,
    }

def validate (question : String) (options : List AskOption) (multi : Bool) (allow_other : Bool) : Result String AskSpec :=
    let n : I64 := List.length options in
    if I64.gt n 4 then Result.err "give at most 4 options"
    else if Bool.and (I64.lt n 2) (Bool.not allow_other) then Result.err "give at least 2 options (or set allow_other true)"
    else if duplicate_labels options then Result.err "option labels must be distinct"
    else if I64.gt (count_recommended options) 1 then Result.err "mark at most one option recommended"
    else
        let spec : AskSpec := { question := question, options := options, multi := multi, allow_other := allow_other } in
        Result.ok spec

pub def AskTool.decode (j : Json) : Result String AskSpec :=
    match Json.get_object j {
        Result.err _ => Result.err "the input must be an object",
        Result.ok o => match str_field "question" o {
            Option.none => Result.err "give a non-empty `question`",
            Option.some question =>
                let multi : Bool := bool_field "multi" false o in
                let allow_other : Bool := bool_field "allow_other" true o in
                match decode_options (array_field "options" o) List.empty {
                    Result.err e => Result.err e,
                    Result.ok options => validate question options multi allow_other,
                },
        },
    }

// ── the answer text the model reads ─────────────────────────────────────

#[partial]
def label_at (i : I64) (os : List AskOption) : Option String :=
    match os {
        List.empty => Option.none,
        List.cons o rest => if i < 1 then Option.some o.label else label_at (i - 1) rest,
    }

#[partial]
def picked_labels (is : List I64) (os : List AskOption) (acc : List String) : List String :=
    match is {
        List.empty => List.reverse acc,
        List.cons i rest => match label_at i os {
            Option.none => picked_labels rest os acc,
            Option.some l => picked_labels rest os (List.cons l acc),
        },
    }

def picked_text (spec : AskSpec) (picked : List I64) (other : String) : String :=
    let labels : List String := picked_labels picked spec.options List.empty in
    if List.is_empty labels
    then
        if String.is_empty other
        then "the user did not answer (cancelled). Decide yourself or ask again later."
        else String.concat "other: " other
    else
        let head : String := if spec.multi then "answers: " else "answer: " in
        let body : String := String.concat head (List.intercalate ", " labels) in
        if String.is_empty other then body else String.concat body (String.concat "\nother: " other)

#[partial]
def recommended_at (i : I64) (os : List AskOption) : Option I64 :=
    match os {
        List.empty => Option.none,
        List.cons o rest => if o.recommended then Option.some i else recommended_at (i + 1) rest,
    }

/// The option auto mode assumes: the recommended one, else the first.
pub def AskTool.default_index (spec : AskSpec) : Option I64 :=
    match recommended_at 0 spec.options {
        Option.some i => Option.some i,
        Option.none => if List.is_empty spec.options then Option.none else Option.some 0,
    }

def auto_text (spec : AskSpec) : String :=
    match AskTool.default_index spec {
        Option.none => "[auto] no one is attending; there were no options. Decide yourself and record the assumption.",
        Option.some i => match label_at i spec.options {
            Option.none => "[auto] no one is attending; decide yourself and record the assumption.",
            Option.some l => String.concat_list ["[auto] no one is attending; assuming ", l,
                ".\nRecord this assumption in the plan and continue."],
        },
    }

pub def AskTool.answer_text (spec : AskSpec) (r : AskReply) : String :=
    if r.auto then auto_text spec
    else if r.cancelled then "the user did not answer (cancelled). Decide yourself or ask again later."
    else picked_text spec r.picked r.other

/// The reply auto mode uses without any UI.
pub def AskTool.auto_reply (spec : AskSpec) : AskReply :=
    let picked : List I64 := match AskTool.default_index spec {
        Option.none => List.empty,
        Option.some i => List.cons i List.empty,
    } in
    let r : AskReply := { picked := picked, other := "", cancelled := false, auto := true } in
    r

// ── the line UI's seam ──────────────────────────────────────────────────

#[partial]
def digits_value (s : String) (i : I64) (acc : I64) : Option I64 :=
    if Bool.not (i < String.length s) then (if i < 1 then Option.none else Option.some acc)
    else match String.get s i {
        Option.none => Option.none,
        Option.some b =>
            let c : I64 := U8.to_i64 b in
            if Bool.and (I64.lt 47 c) (I64.lt c 58)
            then digits_value s (i + 1) (acc * 10 + (c - 48))
            else Option.none,
    }

def parse_index (t : String) : Option I64 :=
    let s : String := String.trim t in
    digits_value s 0 0

#[partial]
def all_indices (parts : List String) (n : I64) (acc : List I64) : Option (List I64) :=
    match parts {
        List.empty => Option.some (List.reverse acc),
        List.cons p rest => match parse_index p {
            Option.none => Option.none,
            Option.some i =>
                if Bool.and (I64.lt 0 i) (Bool.not (I64.gt i n))
                then all_indices rest n (List.cons (i - 1) acc)
                else Option.none,
        },
    }

pub def AskTool.cancelled_reply : AskReply :=
    let r : AskReply := { picked := List.empty, other := "", cancelled := true, auto := false } in
    r

def other_reply (text : String) : AskReply :=
    let r : AskReply := { picked := List.empty, other := text, cancelled := false, auto := false } in
    r

def numbers_reply (spec : AskSpec) (raw : String) (parts : List String) : AskReply :=
    let n : I64 := List.length spec.options in
    match all_indices parts n List.empty {
        Option.none => other_reply raw,
        Option.some is =>
            let picked : List I64 :=
                if spec.multi
                then is
                else match is { List.cons i _ => List.cons i List.empty, List.empty => List.empty } in
            let r : AskReply := { picked := picked, other := "", cancelled := false, auto := false } in
            r,
    }

/// A typed answer line: numbers pick options (`1` or `1,3`), anything
/// else is the free-text answer, and an empty line is a cancellation.
pub def AskTool.parse_line (spec : AskSpec) (text : String) : AskReply :=
    let s : String := String.trim text in
    if String.is_empty s then AskTool.cancelled_reply
    else numbers_reply spec s (String.split s ",")

#[partial]
def option_lines (os : List AskOption) (i : I64) : String :=
    match os {
        List.empty => "",
        List.cons o rest =>
            let desc : String := if String.is_empty o.description then "" else String.concat " -- " o.description in
            String.concat_list ["  ", I64.to_string i, ") ", o.label, desc, "\n", option_lines rest (i + 1)],
    }

def line_hint (spec : AskSpec) : String :=
    if spec.multi
    then "answer with numbers (e.g. 1,3), or type your own answer: "
    else "answer with a number, or type your own answer: "

pub def AskTool.line_prompt (spec : AskSpec) : String :=
    String.concat_list [spec.question, "\n", option_lines spec.options 1, line_hint spec]

// ── the tool ────────────────────────────────────────────────────────────

def str_prop (d : String) : Json :=
    Json.make_object_pairs [Pair.pair "type" (Json.make_str "string"), Pair.pair "description" (Json.make_str d)]

def bool_prop (d : String) : Json :=
    Json.make_object_pairs [Pair.pair "type" (Json.make_str "boolean"), Pair.pair "description" (Json.make_str d)]

def option_schema : Json :=
    Json.make_object_pairs [
        Pair.pair "type" (Json.make_str "object"),
        Pair.pair "properties" (Json.make_object_pairs [
            Pair.pair "label" (str_prop "The choice, short (a few words)."),
            Pair.pair "description" (str_prop "One line explaining the choice (optional)."),
            Pair.pair "recommended" (bool_prop "Mark the option you suggest (at most one)."),
        ]),
        Pair.pair "required" (Json.make_array (List.cons (Json.make_str "label") List.empty)),
    ]

def ask_schema : Json :=
    Json.make_object_pairs [
        Pair.pair "type" (Json.make_str "object"),
        Pair.pair "properties" (Json.make_object_pairs [
            Pair.pair "question" (str_prop "The question to ask, in one or two sentences."),
            Pair.pair "options" (Json.make_object_pairs [
                Pair.pair "type" (Json.make_str "array"),
                Pair.pair "items" option_schema,
                Pair.pair "description" (Json.make_str "2-4 concrete choices."),
            ]),
            Pair.pair "multi" (bool_prop "Allow several choices (default false)."),
            Pair.pair "allow_other" (bool_prop "Offer a free-text answer (default true)."),
        ]),
        Pair.pair "required" (Json.make_array (List.cons (Json.make_str "question") List.empty)),
    ]

pub def AskTool.spec : ToolSpec :=
    { name := "ask",
        description := "Ask the user to choose between concrete options, or to answer a question in their own words. Use it when the request is ambiguous or a decision is theirs (a trade-off with no clear default) instead of guessing. In auto mode it answers with the recommended option and says so, so record that assumption.",
        schema := ask_schema }

/// The tool against a UI seam. In `auto` the seam is never used.
pub def AskTool.impl (mode : Mode) (seam : Option AskSeam) : ToolImpl :=
    { spec := AskTool.spec, cap := Capability.read, run := ask_run mode seam }

def ask_run (mode : Mode) (seam : Option AskSeam) (id : String) (j : Json) : ResultT String IO Content :=
    ResultT.mk (match AskTool.decode j {
        Result.err e => IO.pure (Result.ok (Content.tool_result id (String.concat "ask: " e) true)),
        Result.ok spec => ask_decoded mode seam id spec,
    })

def ask_decoded (mode : Mode) (seam : Option AskSeam) (id : String) (spec : AskSpec) : IO (Result String Content) :=
    if Mode.is_auto mode
    then IO.pure (Result.ok (Content.tool_result id (AskTool.answer_text spec (AskTool.auto_reply spec)) false))
    else match seam {
        Option.none => IO.pure (Result.ok (Content.tool_result id (AskTool.answer_text spec (AskTool.auto_reply spec)) false)),
        Option.some s => do {
            let r <- s.ask spec;
            IO.pure (Result.ok (Content.tool_result id (AskTool.answer_text spec r) false))
        },
    }
