/// The header blob codec is pure, so it tests natively. Length prefixes
/// are what let a value contain `:`; cover that explicitly.

use lib::fetch {encode_headers, decode_headers}
use std::list {List.length}

def pair_is (k : String) (v : String) (p : Pair String String) : Bool :=
    match p { Pair.pair ak av => String.beq k ak && String.beq v av }

#[test]
def test_header_blob_empty : Bool :=
    let encoded : String := encode_headers List.empty in
    String.is_empty encoded && I64.beq (List.length (decode_headers "")) 0

#[test]
def test_header_blob_round_trips : Bool :=
    let hs : List (Pair String String) :=
        [Pair.pair "Authorization" "Bearer t", Pair.pair "Content-Type" "application/json"] in
    let back : List (Pair String String) := decode_headers (encode_headers hs) in
    match List.get 0 back {
        Option.some first =>
            match List.get 1 back {
                Option.some second =>
                    pair_is "Authorization" "Bearer t" first
                        && pair_is "Content-Type" "application/json" second,
                Option.none => false,
            },
        Option.none => false,
    }

#[test]
def test_header_value_may_contain_colon : Bool :=
    let hs : List (Pair String String) := [Pair.pair "DPoP" "a:b:c"] in
    match List.get 0 (decode_headers (encode_headers hs)) {
        Option.some first => pair_is "DPoP" "a:b:c" first,
        Option.none => false,
    }

#[test]
def test_header_empty_value : Bool :=
    let hs : List (Pair String String) := [Pair.pair "X-Empty" ""] in
    match List.get 0 (decode_headers (encode_headers hs)) {
        Option.some first => pair_is "X-Empty" "" first,
        Option.none => false,
    }
