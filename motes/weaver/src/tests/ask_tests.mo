/// The `ask` tool's pure core: decoding, validation, answer text, and the
/// line UI's parser.
use weaver::ask {
    AskOption, AskSpec, AskReply, AskTool.decode, AskTool.answer_text, AskTool.parse_line,
    AskTool.auto_reply, AskTool.line_prompt, AskTool.cancelled_reply, AskTool.default_index,
}
use json::json {Json, Json.parse}

def spec_of (text : String) : Option AskSpec :=
    match Json.parse text {
        Result.err _ => Option.none,
        Result.ok j => match AskTool.decode j {
            Result.err _ => Option.none,
            Result.ok s => Option.some s,
        },
    }

def err_of (text : String) : Bool :=
    match Json.parse text {
        Result.err _ => false,
        Result.ok j => match AskTool.decode j {
            Result.err _ => true,
            Result.ok _ => false,
        },
    }

def basic : String := r#"{"question":"Which target?","options":[{"label":"debug"},{"label":"release","recommended":true}]}"#

#[test]
def test_decode_defaults : Bool :=
    match spec_of basic {
        Option.none => false,
        Option.some s => Bool.and (Bool.not s.multi) (Bool.and s.allow_other (not (String.is_empty s.question))),
    }

#[test]
def test_decode_multi : Bool :=
    match spec_of r#"{"question":"Pick some","multi":true,"options":[{"label":"a"},{"label":"b"}]}"# {
        Option.none => false,
        Option.some s => s.multi,
    }

#[test]
def test_decode_rejects_bad_shapes : Bool :=
    err_of r#"{"options":[{"label":"a"},{"label":"b"}]}"#
        && err_of r#"{"question":"q","allow_other":false,"options":[{"label":"only"}]}"#
        && err_of r#"{"question":"q","options":[{"label":"a"},{"label":"a"}]}"#
        && err_of r#"{"question":"q","options":[{"label":"a","recommended":true},{"label":"b","recommended":true}]}"#
        && err_of r#"{"question":"q","options":[{"label":"a"},{"label":"b"},{"label":"c"},{"label":"d"},{"label":"e"}]}"#

#[test]
def test_an_open_question_needs_no_options : Bool :=
    match spec_of r#"{"question":"What should I name it?"}"# {
        Option.none => false,
        Option.some s => List.is_empty s.options,
    }

#[test]
def test_answer_text_single : Bool :=
    match spec_of basic {
        Option.none => false,
        Option.some s => String.beq (AskTool.answer_text s (AskTool.parse_line s "2")) "answer: release",
    }

#[test]
def test_answer_text_multi : Bool :=
    match spec_of r#"{"question":"Pick some","multi":true,"options":[{"label":"a"},{"label":"b"},{"label":"c"}]}"# {
        Option.none => false,
        Option.some s => String.beq (AskTool.answer_text s (AskTool.parse_line s "1,3")) "answers: a, c",
    }

#[test]
def test_a_single_pick_takes_only_the_first_number : Bool :=
    match spec_of r#"{"question":"Pick","options":[{"label":"a"},{"label":"b"}]}"# {
        Option.none => false,
        Option.some s => String.beq (AskTool.answer_text s (AskTool.parse_line s "2,1")) "answer: b",
    }

#[test]
def test_free_text_is_other : Bool :=
    match spec_of basic {
        Option.none => false,
        Option.some s => String.beq (AskTool.answer_text s (AskTool.parse_line s "something else")) "other: something else"
            && String.beq (AskTool.answer_text s (AskTool.parse_line s "debug please")) "other: debug please",
    }

#[test]
def test_a_number_out_of_range_is_free_text : Bool :=
    match spec_of basic {
        Option.none => false,
        Option.some s => String.beq (AskTool.answer_text s (AskTool.parse_line s "9")) "other: 9",
    }

#[test]
def test_an_empty_line_cancels : Bool :=
    match spec_of basic {
        Option.none => false,
        Option.some s => Bool.and
            (AskTool.answer_text s (AskTool.parse_line s "  ") == "the user did not answer (cancelled). Decide yourself or ask again later.")
            (AskTool.answer_text s AskTool.cancelled_reply == "the user did not answer (cancelled). Decide yourself or ask again later."),
    }

#[test]
def test_auto_answers_the_recommended_option : Bool :=
    match spec_of basic {
        Option.none => false,
        Option.some s => String.contains (AskTool.answer_text s (AskTool.auto_reply s)) "assuming release",
    }

#[test]
def test_auto_falls_back_to_the_first_option : Bool :=
    match spec_of r#"{"question":"Pick","options":[{"label":"a"},{"label":"b"}]}"# {
        Option.none => false,
        Option.some s => match AskTool.default_index s {
            Option.some i => Bool.and (i == 0) (String.contains (AskTool.answer_text s (AskTool.auto_reply s)) "assuming a"),
            Option.none => false,
        },
    }

#[test]
def test_line_prompt_numbers_the_options : Bool :=
    match spec_of basic {
        Option.none => false,
        Option.some s =>
            let p : String := AskTool.line_prompt s in
            String.contains p "Which target?"
                && String.contains p "1) debug"
                && String.contains p "2) release"
                && String.contains p "type your own answer",
    }
