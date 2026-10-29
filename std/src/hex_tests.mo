/// Codec vectors for `std::hex` (formerly `motes/crypto`'s `hex.mo`).
///
/// Pure (`Bool`), so both hosts run them.

use std::hex {Hex.encode, Hex.decode, HexError, HexError.to_string}

// `BEq (List A)` lives here, not in the ambient prelude; the empty brace
// list pulls the module (and its instances) into scope.
use std::list {}

def decoded_text (r : Result HexError (List U8)) (expected : String) : Bool :=
  match r {
    Result.ok bs => bs == String.to_list expected,
    Result.err _ => false
  }

def decoded_bytes (r : Result HexError (List U8)) (expected : List U8) : Bool :=
  match r {
    Result.ok bs => bs == expected,
    Result.err _ => false
  }

def rejected_with (r : Result HexError (List U8)) (msg : String) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => HexError.to_string e == msg
  }

/// `0xfb 0xff` covers both nibble ranges (high nibble `f`, low `b`/`f`).
def edge_bytes : List U8 := [0xfbu8, 0xffu8]

def one_zero_byte : List U8 := [0u8]

#[test]
def test_hex_encode : Bool :=
  Hex.encode (String.to_list "foobar") == "666f6f626172"
  && Hex.encode one_zero_byte == "00"
  && Hex.encode edge_bytes == "fbff"
  && Hex.encode List.empty == ""

#[test]
def test_hex_decode : Bool :=
  decoded_text (Hex.decode "666f6f626172") "foobar"
  && decoded_text (Hex.decode "666F6F626172") "foobar"
  && decoded_bytes (Hex.decode "00") one_zero_byte
  && decoded_bytes (Hex.decode "") List.empty
  && decoded_bytes (Hex.decode (Hex.encode edge_bytes)) edge_bytes

#[test]
def test_hex_rejects_bad_input : Bool :=
  rejected_with (Hex.decode "abc") "hex: odd length"
  && rejected_with (Hex.decode "zz") "hex: invalid character"
  && rejected_with (Hex.decode "0g") "hex: invalid character"

/// The variant itself, not just its text.
def rejected_odd_length (r : Result HexError (List U8)) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e { HexError.odd_length => true, _ => false }
  }

def rejected_invalid_char (r : Result HexError (List U8)) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e { HexError.invalid_char => true, _ => false }
  }

#[test]
def test_hex_error_variants : Bool :=
  rejected_odd_length (Hex.decode "abc")
  && rejected_invalid_char (Hex.decode "zz")
