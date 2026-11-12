/// UTF-8 encoding and decoding.
use unicode::utf8 {Unicode.char_width, Unicode.codepoint_at, Unicode.utf8_of_codepoint}

def decodes (s : String) (cp : U32) : Bool :=
    match Unicode.codepoint_at s {
        Option.some c => U32.beq c cp,
        Option.none => false,
    }

def is_none {A : Type} (o : Option A) : Bool :=
    match o {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_codepoint_at : Bool :=
    decodes "a" 97u32 && decodes "é!" 233u32 && decodes "日本" 26085u32 && decodes "😀" 128512u32
        && is_none (Unicode.codepoint_at "")

#[test]
def test_char_width : Bool :=
    I64.beq (Unicode.char_width "a") 1 && I64.beq (Unicode.char_width "é") 2
        && I64.beq (Unicode.char_width "日") 3 && I64.beq (Unicode.char_width "😀") 4

#[test]
def test_utf8_of_codepoint : Bool :=
    String.beq (Unicode.utf8_of_codepoint 233) "é" && String.beq (Unicode.utf8_of_codepoint 128512) "😀"
        && String.beq (Unicode.utf8_of_codepoint 55296) "\u{fffd}"
        && String.beq (Unicode.utf8_of_codepoint 0) "\u{fffd}"
        && String.beq (Unicode.utf8_of_codepoint 1114112) "\u{fffd}"
        && String.beq (Unicode.utf8_of_codepoint (0 - 1)) "\u{fffd}"
