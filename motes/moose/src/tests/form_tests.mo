/// `application/x-www-form-urlencoded` encoding vectors.
///
/// The one difference from `http`'s `Uri.format_query` is the space:
/// this encoder emits `+`, which is what an OAuth token request and a
/// classic HTML form send.

use std::list {}
use moose::form {Form.encode, Form.encode_component}

def sample_fields : List (Pair String String) := [
  Pair.pair "a" "b c",
  Pair.pair "d" "e"
]

#[test]
def test_form_encode_empty : Bool :=
  Form.encode List.empty == ""

#[test]
def test_form_encode_pairs : Bool :=
  Form.encode sample_fields == "a=b+c&d=e"

#[test]
def test_form_space_is_plus : Bool :=
  Form.encode_component "a b" == "a+b"

#[test]
def test_form_component_reserved : Bool :=
  Form.encode_component "a b+c/d~e" == "a+b%2Bc%2Fd~e"
  && Form.encode_component "&=%" == "%26%3D%25"
  && Form.encode_component "é" == "%C3%A9"
  && Form.encode_component "AZaz09-._~" == "AZaz09-._~"
