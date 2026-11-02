/// `textDocument/formatting`: a formatted buffer answers no edits, and anything else
/// answers one edit that replaces the whole document with the formatter's output.
use json::json {Json, Json.to_string}
use lsp::formatting {lsp_format_text}
use toolkit::position {PositionEncoding}

def answer (text : String) : String :=
    match lsp_format_text PositionEncoding.utf16 text {
        Result.ok j => Json.to_string j,
        Result.err e => "error: " ++ e,
    }

#[test]
def test_a_formatted_buffer_answers_no_edits : Bool :=
    String.beq (answer "def a : I64 := 1\n") "[]"

/// The range runs from the start to the end of the old text; the new text is the
/// formatter's.
#[test]
def test_an_unformatted_buffer_answers_one_whole_document_edit : Bool :=
    String.beq (answer "def  a : I64 := 1\n")
        "[{\"newText\":\"def a : I64 := 1\\n\",\"range\":{\"end\":{\"character\":0,\"line\":1},\"start\":{\"character\":0,\"line\":0}}}]"

/// A buffer the formatter cannot lex is refused rather than rewritten.
#[test]
def test_a_buffer_that_does_not_lex_is_refused : Bool :=
    String.starts_with "error: formatting:" (answer "def a : String := \"open\n")
