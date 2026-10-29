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
use std::base64 {B64.encode_std}

/// Standard base64 (with `=` padding) of the string's UTF-8 bytes,
/// encoded by `std::base64` (the one home for the codec; the local
/// encoder this replaced is gone).
pub def Clipboard.base64 (s : String) : String :=
    B64.encode_std (String.to_list s)

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
