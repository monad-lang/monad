// Terminal UI Library - Clipboard (OSC 52)
//
// The terminal's clipboard, without a native: an OSC 52 sequence carries
// base64-encoded UTF-8 text to the terminal, which owns the system
// clipboard (and forwards it over SSH). tmux needs `set-clipboard on` /
// passthrough; terminals that ignore OSC 52 simply do not copy.
//
// The encoder works on BYTES (`List U8`) end to end: the alphabet, the
// padding and the six-bit groups are all U8 arithmetic, so no index ever
// needs a cast to I64.

use std::io {IO.write_stdout, IO.flush_stdout}

/// The base64 alphabet as ASCII bytes (A-Z a-z 0-9 + /).
def b64_byte (v : U8) : U8 :=
    if U8.lt v 26u8 then U8.add 65u8 v
    else if U8.lt v 52u8 then U8.add 97u8 (U8.sub v 26u8)
    else if U8.lt v 62u8 then U8.add 48u8 (U8.sub v 52u8)
    else if U8.beq v 62u8 then 43u8
    else 47u8

def b64_top (b : U8) : U8 := U8.div b 64u8

def b64_low6 (b : U8) : U8 := U8.sub b (U8.mul (b64_top b) 64u8)

def b64_low4 (b : U8) : U8 :=
    let top : U8 := U8.div b 16u8 in
    U8.sub b (U8.mul top 16u8)

/// Four ASCII base64 bytes for three input bytes, appended newest-first
/// (the final `List.reverse` restores v1..v4).
def encode_group (b0 b1 b2 : U8) (acc : List U8) : List U8 :=
    let v1 : U8 := U8.div b0 4u8 in
    let v2 : U8 := U8.add (U8.mul (U8.sub b0 (U8.mul v1 4u8)) 16u8) (U8.div b1 16u8) in
    let v3 : U8 := U8.add (U8.mul (b64_low4 b1) 4u8) (b64_top b2) in
    let v4 : U8 := b64_low6 b2 in
    List.cons (b64_byte v4)
        (List.cons (b64_byte v3)
        (List.cons (b64_byte v2)
        (List.cons (b64_byte v1) acc)))

/// One input byte: two alphabet bytes and `==`.
def encode_one (b0 : U8) (acc : List U8) : List U8 :=
    let v1 : U8 := U8.div b0 4u8 in
    let v2 : U8 := U8.mul (U8.sub b0 (U8.mul v1 4u8)) 16u8 in
    List.cons 61u8 (List.cons 61u8 (List.cons (b64_byte v2) (List.cons (b64_byte v1) acc)))

/// Two input bytes: three alphabet bytes and `=`.
def encode_two (b0 b1 : U8) (acc : List U8) : List U8 :=
    let v1 : U8 := U8.div b0 4u8 in
    let v2 : U8 := U8.add (U8.mul (U8.sub b0 (U8.mul v1 4u8)) 16u8) (U8.div b1 16u8) in
    let v3 : U8 := U8.mul (b64_low4 b1) 4u8 in
    List.cons 61u8 (List.cons (b64_byte v3) (List.cons (b64_byte v2) (List.cons (b64_byte v1) acc)))

#[partial]
def encode_go (bytes : List U8) (acc : List U8) : List U8 :=
    match bytes {
        List.empty => List.reverse acc,
        List.cons b0 rest => match rest {
            List.empty => List.reverse (encode_one b0 acc),
            List.cons b1 rest1 => match rest1 {
                List.empty => List.reverse (encode_two b0 b1 acc),
                List.cons b2 rest2 => encode_go rest2 (encode_group b0 b1 b2 acc),
            },
        },
    }

/// Standard base64 (with `=` padding) of the string's UTF-8 bytes.
pub def Clipboard.base64 (s : String) : String :=
    String.from_list (encode_go (String.to_list s) List.empty)

/// The OSC 52 "set clipboard" sequence: `ESC ] 52 ; c ; <base64> ST`.
pub def Clipboard.osc52_code (s : String) : String :=
    String.concat "\u{1b}]52;c;" (String.concat (Clipboard.base64 s) "\u{1b}\\")

/// Send `s` to the terminal's clipboard and flush it immediately (the
/// copy rides a `Cmd.perform`, whose forced repaint follows).
pub def Clipboard.copy (s : String) : IO Unit := do {
    IO.write_stdout (Clipboard.osc52_code s);
    IO.flush_stdout
}

// ==================== tests ====================

#[test]
def test_base64_empty : Bool := Clipboard.base64 "" == ""

#[test]
def test_base64_one_byte : Bool := Clipboard.base64 "f" == "Zg=="

#[test]
def test_base64_two_bytes : Bool := Clipboard.base64 "fo" == "Zm8="

#[test]
def test_base64_three_bytes : Bool := Clipboard.base64 "foo" == "Zm9v"

#[test]
def test_base64_hello : Bool := Clipboard.base64 "hello" == "aGVsbG8="

#[test]
def test_base64_latin1 : Bool := Clipboard.base64 "æ" == "w6Y="

#[test]
def test_base64_wide : Bool := Clipboard.base64 "日" == "5pel"

#[test]
def test_osc52_shape : Bool :=
    String.starts_with "\u{1b}]52;c;aGk=" (Clipboard.osc52_code "hi")
        && String.ends_with (Clipboard.osc52_code "hi") "\u{1b}\\"
