/// JSON parsing and serialization

use std.map
use std.list
use init.string
use init.number
use lang.parser.core
use lang.parser.char_preds
use lang.parser.combinators
use lang.parser.whitespace
use lang.parser.number

open ParseResult
open Json
open Json.Number

// ─── Types ───

/// JSON number: either an integer or a float.
/// NOTE: the parser currently only ever produces `int` (see Json.parse_number below) —
/// float parsing needs an I64/String -> F64 native conversion that doesn't exist yet.
/// The `float` variant and its serialization exist so callers can construct/serialize
/// floats manually with Json.make_num_float.
type Json.Number {
  int I64,
  float F64,
}

def Json.Number.beq (a b : Json.Number) : Bool :=
  match a {
    int ia => match b {
     int ib => ia == ib,
     _ => false,
    },
    float fa => match b {
      float fb => fa == fb,
      _ => false,
    }
  }

instance BEq Json.Number {
  def beq (a b : Json.Number) : Bool := Json.Number.beq a b
}

/// JSON value type
type Json {
  null,
  num (n : Json.Number),
  str (s : String),
  bool (b : Bool),
  array (a : List Json),
  object (o : BTreeMap String Json),
}

// NOTE: array/object equality is hand-rolled below (Json.array_beq / Json.object_beq)
// instead of going through the generic `[BEq A] BEq (List A)` / `BEq (Option A)`
// instances and `==`. Those generic instances don't dispatch correctly to a custom
// `A`'s BEq instance at runtime — a pre-existing evaluator limitation (see the
// similar note on `resolve_class_method_instance` in std/map.mo's HashMap instance).
// Concrete (non-generic) BEq instances, e.g. BEq I64/String/Bool used below, are fine.
def Json.beq (a b : Json) : Bool :=
  match a {
    null => match b {
      null => true,
      _ => false,
    },
    num na => match b {
      num nb => na == nb,
      _ => false
    },
    str sa => match b {
      str sb => sa == sb,
      _ => false
    },
    bool ba => match b {
      bool bb => ba == bb,
      _ => false
    },
    array aa => match b {
      array ab => Json.array_beq aa ab,
      _ => false
    },
    object oa => match b {
      object ob => Json.object_beq oa ob,
      _ => false
    },
  }

def Json.array_beq (a b : List Json) : Bool :=
  match a {
    List.empty => match b {
      List.empty => true,
      List.cons _ _ => false
    },
    List.cons xa ta => match b {
      List.empty => false,
      List.cons xb tb => Json.beq xa xb && Json.array_beq ta tb
    }
  }

def Json.pair_beq (a b : Pair String Json) : Bool :=
  match a {
    Pair.pair ka va => match b {
      Pair.pair kb vb => String.beq ka kb && Json.beq va vb
    }
  }

def Json.pairs_beq (a b : List (Pair String Json)) : Bool :=
  match a {
    List.empty => match b {
      List.empty => true,
      List.cons _ _ => false
    },
    List.cons pa ta => match b {
      List.empty => false,
      List.cons pb tb => Json.pair_beq pa pb && Json.pairs_beq ta tb
    }
  }

@[partial]
def Json.object_beq (a b : BTreeMap String Json) : Bool :=
  Json.pairs_beq (BTreeMap.to_list a) (BTreeMap.to_list b)

instance BEq Json {
  def beq (a b : Json) : Bool := Json.beq a b
}

/// Explicit BEq instance for BTreeMap String Json
instance BEq (BTreeMap String Json) {
  def beq (a b : BTreeMap String Json) : Bool := Json.object_beq a b
}

/// JSON ParseError type
type Json.ParseError {
  expected (e : String) (found : String),
  generic String,
}

def Json.ParseError.beq (a b : Json.ParseError) : Bool :=
  match a {
    expected e f => match b {
      expected eb fb => e == eb && f == fb,
      _ => false,
    },
    generic sa => match b {
      generic sb => sa == sb,
      _ => false
    },
    _ => false,
  }

instance BEq Json.ParseError {
  def beq (a b : Json.ParseError) : Bool := Json.ParseError.beq a b
}

/// Convert core ParseError to Json.ParseError
def Json.from_parse_error (e : ParseError) : Json.ParseError :=
  match e {
    tag s => Json.ParseError.expected s "",
    custom s => Json.ParseError.generic s
  }

/// ParseError to string
def Json.ParseError.to_string (e : Json.ParseError) : String :=
  match e {
    expected e f => "expected: " ++ e ++ " found: " ++ f,
    generic s => s
  }

// ─── Parser: helpers ───

/// Helper function to concatenate a list of strings
@[partial]
def String.concat_list (ss : List String) : String :=
  match ss {
    List.empty => "",
    List.cons hd tl => String.concat hd (String.concat_list tl)
  }

/// EOF parser - succeeds if input is empty
def Json.eof (input : String) : ParseResult Unit :=
  if is_empty input
  then success input unit
  else fail (ParseError.custom "expected end of input")

/// Optional whitespace
def Json.ws (input : String) : ParseResult String :=
  take_while is_space input

/// Comma with optional whitespace on both sides
def Json.comma (input : String) : ParseResult String :=
  delimited_by Json.ws (tag ",") Json.ws input

/// Colon with optional whitespace on both sides
def Json.colon (input : String) : ParseResult String :=
  delimited_by Json.ws (tag ":") Json.ws input

// ─── Parser: null / bool ───

def parse_null_result (r : ParseResult String) : ParseResult Json :=
  match r {
    success rem _ => success rem null,
    fail e => fail e
  }

/// Parse "null" value
def Json.parse_null (input : String) : ParseResult Json :=
  parse_null_result (tag "null" input)

def parse_true_result (r : ParseResult String) : ParseResult Json :=
  match r {
    success rem _ => success rem (bool true),
    fail e => fail e
  }

/// Parse "true"
def Json.parse_true (input : String) : ParseResult Json :=
  parse_true_result (tag "true" input)

def parse_false_result (r : ParseResult String) : ParseResult Json :=
  match r {
    success rem _ => success rem (bool false),
    fail e => fail e
  }

/// Parse "false"
def Json.parse_false (input : String) : ParseResult Json :=
  parse_false_result (tag "false" input)

/// Parse boolean values (true or false)
def Json.parse_bool (input : String) : ParseResult Json :=
  alt Json.parse_true Json.parse_false input

// ─── Parser: number (MVP: integers only) ───

def neg_i64 (n : I64) : I64 := 0 - n

def parse_integer_negative (r : ParseResult I64) : ParseResult I64 :=
  match r {
    success rem n => success rem (neg_i64 n),
    fail _ => fail (ParseError.custom "expected digits after -")
  }

@[partial]
def parse_integer_result (r : ParseResult String) (orig : String) : ParseResult I64 :=
  match r {
    success rem _ => parse_integer_negative (number rem),
    fail _ => number orig
  }

/// Parse signed integer
def Json.parse_integer (input : String) : ParseResult I64 :=
  parse_integer_result (tag "-" input) input

def Json.number_to_json (n : I64) : Json.Number := Json.Number.int n

/// Parse JSON number (currently only integers)
def Json.parse_number (input : String) : ParseResult Json.Number :=
  map_parse Json.number_to_json Json.parse_integer input

// ─── Parser: string ───

/// Parse a single character that is not a quote or backslash
def Json.parse_string_char (input : String) : ParseResult String :=
  if is_empty input
  then fail (ParseError.custom "expected string character")
  else
    let ch : String := String.slice input 0 1 in
    if is_json_string_char ch
    then success (String.drop 1 input) ch
    else fail (ParseError.custom "invalid string character")

@[partial]
def is_json_string_char (c : String) : Bool :=
  if String.beq "\"" c then false
  else if String.beq "\\" c then false
  else true

/// Take exactly 4 characters (used for \uXXXX escapes)
def Json.take4 (input : String) : ParseResult String :=
  if I64.gt (String.length input) 3
  then success (String.drop 4 input) (String.slice input 0 4)
  else fail (ParseError.custom "expected 4 hex digits")

def parse_escape_u_result (r : ParseResult String) : ParseResult String :=
  match r {
    success rem hex => success rem (String.concat "\\u" hex),
    fail e => fail e
  }

@[partial]
def parse_escape_u_body (r : ParseResult String) (orig : String) : ParseResult String :=
  match r {
    success rem _ => parse_escape_u_result (Json.take4 rem),
    fail e => fail e
  }

/// Parse a \uXXXX escape sequence. The 4 hex digits are NOT validated or decoded —
/// they're stored as the literal 6-character sequence "\uXXXX" (simplification per plan).
def Json.parse_escape_u (input : String) : ParseResult String :=
  parse_escape_u_body (tag "\\u" input) input

def match_escape (s : String) : String :=
  if String.beq "\\\"" s then "\""
  else if String.beq "\\\\" s then "\\"
  else if String.beq "\\/" s then "/"
  else if String.beq "\\b" s then "\b"
  else if String.beq "\\f" s then "\f"
  else if String.beq "\\n" s then "\n"
  else if String.beq "\\r" s then "\r"
  else if String.beq "\\t" s then "\t"
  else s

def parse_escape_result (r : ParseResult String) : ParseResult String :=
  match r {
    success rem out => success rem (match_escape out),
    fail e => fail e
  }

def parse_named_escape (input : String) : ParseResult String :=
  parse_escape_result (alt_fold
    [tag "\\\"",
     tag "\\\\",
     tag "\\/",
     tag "\\b",
     tag "\\f",
     tag "\\n",
     tag "\\r",
     tag "\\t"]
    input)

/// Parse an escape sequence (named escape or \uXXXX passthrough)
def Json.parse_escape (input : String) : ParseResult String :=
  alt Json.parse_escape_u parse_named_escape input

def Json.parse_string_content (input : String) : ParseResult (List String) :=
  many0 (alt Json.parse_escape Json.parse_string_char) input

def parse_string_close (r : ParseResult String) (s : String) : ParseResult Json :=
  match r {
    success rem _ => success rem (str s),
    fail e => fail e
  }

@[partial]
def parse_string_content_result (r : ParseResult (List String)) : ParseResult Json :=
  match r {
    success rem chars => parse_string_close (tag "\"" rem) (String.concat_list chars),
    fail e => fail e
  }

@[partial]
def parse_string_open (r : ParseResult String) : ParseResult Json :=
  match r {
    success rem _ => parse_string_content_result (Json.parse_string_content rem),
    fail e => fail e
  }

/// Parse a JSON string
def Json.parse_string (input : String) : ParseResult Json :=
  parse_string_open (tag "\"" input)

// ─── Parser: array / object / value ───

def parse_array_result (r : ParseResult (List Json)) : ParseResult Json :=
  match r {
    success rem elems => success rem (array elems),
    fail e => fail e
  }

@[partial]
def Json.parse_array_body (input : String) : ParseResult (List Json) :=
  delimited_by Json.ws (separated_by Json.comma Json.parse_value) Json.ws input

/// Parse a JSON array
@[partial]
def Json.parse_array (input : String) : ParseResult Json :=
  parse_array_result (delimited_by (tag "[") Json.parse_array_body (tag "]") input)

@[partial]
def parse_object_member_value (r : ParseResult Json) (key : String) : ParseResult (Pair String Json) :=
  match r {
    success rem val => success rem (Pair.pair key val),
    fail e => fail e
  }

@[partial]
def parse_object_member_colon_result (r : ParseResult String) (key : String) : ParseResult (Pair String Json) :=
  match r {
    success rem _ => parse_object_member_value (Json.parse_value rem) key,
    fail e => fail e
  }

@[partial]
def parse_object_member_colon (rem : String) (key : String) : ParseResult (Pair String Json) :=
  parse_object_member_colon_result (Json.colon rem) key

@[partial]
def parse_object_member_key_str (rem : String) (key_json : Json) : ParseResult (Pair String Json) :=
  match key_json {
    str key => parse_object_member_colon rem key,
    _ => fail (ParseError.custom "expected string key")
  }

@[partial]
def parse_object_member_key (r : ParseResult Json) : ParseResult (Pair String Json) :=
  match r {
    success rem key_json => parse_object_member_key_str rem key_json,
    fail e => fail e
  }

/// Parse an object member ("key" : value)
@[partial]
def Json.parse_object_member (input : String) : ParseResult (Pair String Json) :=
  parse_object_member_key (Json.parse_string input)

def pairs_to_map_insert (p : Pair String Json) (acc : BTreeMap String Json) : BTreeMap String Json :=
  match p {
    Pair.pair k v => Map.insert k v acc
  }

def pairs_to_map (pairs : List (Pair String Json)) : BTreeMap String Json :=
  match pairs {
    List.empty => BTreeMap.empty,
    List.cons p rest => pairs_to_map_insert p (pairs_to_map rest)
  }

def parse_object_result (r : ParseResult (List (Pair String Json))) : ParseResult Json :=
  match r {
    success rem members => success rem (object (pairs_to_map members)),
    fail e => fail e
  }

@[partial]
def Json.parse_object_body (input : String) : ParseResult (List (Pair String Json)) :=
  delimited_by Json.ws (separated_by Json.comma Json.parse_object_member) Json.ws input

/// Parse a JSON object
@[partial]
def Json.parse_object (input : String) : ParseResult Json :=
  parse_object_result (delimited_by (tag "{") Json.parse_object_body (tag "}") input)

def parse_number_value_result (r : ParseResult Json.Number) : ParseResult Json :=
  match r {
    success rem n => success rem (num n),
    fail e => fail e
  }

def Json.parse_number_value (input : String) : ParseResult Json :=
  parse_number_value_result (Json.parse_number input)

/// Parse any JSON value
@[partial]
def Json.parse_value (input : String) : ParseResult Json :=
  alt_fold
    [Json.parse_null,
     Json.parse_bool,
     Json.parse_string,
     Json.parse_array,
     Json.parse_object,
     Json.parse_number_value]
    input

// ─── Parser: top-level ───

/// Parse complete JSON document (whitespace-tolerant around the value)
@[partial]
def Json.json (input : String) : ParseResult Json :=
  terminated_by (delimited_by Json.ws Json.parse_value Json.ws) Json.eof input

/// Main parse function
@[partial]
def Json.parse (s : String) : Result Json.ParseError Json :=
  match Json.json s {
    success rem val =>
      if is_empty rem
      then ok val
      else err (Json.ParseError.generic "unexpected trailing input"),
    fail e => err (Json.from_parse_error e)
  }

// ─── Serializer: string escaping ───

@[partial]
def Json.escape_char (c : String) : String :=
  if String.beq "\"" c then "\\\""
  else if String.beq "\\" c then "\\\\"
  else if String.beq "\b" c then "\\b"
  else if String.beq "\f" c then "\\f"
  else if String.beq "\n" c then "\\n"
  else if String.beq "\r" c then "\\r"
  else if String.beq "\t" c then "\\t"
  else c

/// Escape special characters in a string for JSON output.
/// NOTE: raw control characters (0x00-0x1F) other than \b \f \n \r \t are passed
/// through unescaped rather than emitted as \u00XX — deferred, see plan notes.
@[partial]
def Json.escape_string (input : String) : String :=
  if is_empty input
  then ""
  else
    let ch := String.slice input 0 1 in
    String.concat (Json.escape_char ch) (Json.escape_string (String.drop 1 input))

// ─── Serializer: numbers ───

def Json.Number.to_string (n : Json.Number) : String :=
  match n {
    int i => I64.to_string i,
    float f => F64.to_string f
  }

// ─── Serializer: main ───

def List.intercalate (sep : String) (xs : List String) : String :=
  match xs {
    List.empty => "",
    List.cons hd tl => List.intercalate_rest sep hd tl
  }

@[partial]
def List.intercalate_rest (sep : String) (acc : String) (xs : List String) : String :=
  match xs {
    List.empty => acc,
    List.cons hd tl => List.intercalate_rest sep (String.concat acc (String.concat sep hd)) tl
  }

def Json.bool_to_string (b : Bool) : String :=
  if b then "true" else "false"

def Json.string_to_string (s : String) : String :=
  String.concat "\"" (String.concat (Json.escape_string s) "\"")

@[partial]
def Json.to_string (j : Json) : String :=
  match j {
    null => "null",
    bool b => Json.bool_to_string b,
    num n => Json.Number.to_string n,
    str s => Json.string_to_string s,
    array a => Json.array_to_string a,
    object o => Json.object_to_string o
  }

@[partial]
def Json.array_to_string (a : List Json) : String :=
  String.concat "[" (String.concat (List.intercalate "," (List.map Json.to_string a)) "]")

@[partial]
def Json.pair_to_string (p : Pair String Json) : String :=
  match p {
    Pair.pair k v => String.concat (Json.string_to_string k) (String.concat ":" (Json.to_string v))
  }

@[partial]
def Json.object_to_string (o : BTreeMap String Json) : String :=
  String.concat "{" (String.concat (List.intercalate "," (List.map Json.pair_to_string (BTreeMap.to_list o))) "}")

// ─── Show instances ───

instance Show Json.Number {
  def show (n : Json.Number) : String := Json.Number.to_string n
}

instance Show Json {
  def show (j : Json) : String := Json.to_string j
}

// ─── Construction helpers ───

def Json.make_null : Json := null
def Json.make_bool (b : Bool) : Json := bool b
def Json.make_num_int (n : I64) : Json := num (int n)
def Json.make_num_float (n : F64) : Json := num (float n)
def Json.make_str (s : String) : Json := str s
def Json.make_array (a : List Json) : Json := array a
def Json.make_object (o : BTreeMap String Json) : Json := object o

// ─── Type checkers ───

def Json.is_null (j : Json) : Bool :=
  match j { null => true, _ => false }

def Json.is_bool (j : Json) : Bool :=
  match j { bool _ => true, _ => false }

def Json.is_num (j : Json) : Bool :=
  match j { num _ => true, _ => false }

def Json.is_str (j : Json) : Bool :=
  match j { str _ => true, _ => false }

def Json.is_array (j : Json) : Bool :=
  match j { array _ => true, _ => false }

def Json.is_object (j : Json) : Bool :=
  match j { object _ => true, _ => false }

// ─── Accessors ───

def Json.get_bool (j : Json) : Result String Bool :=
  match j { bool b => ok b, _ => err "expected bool" }

def Json.get_num (j : Json) : Result String Json.Number :=
  match j { num n => ok n, _ => err "expected number" }

def Json.get_str (j : Json) : Result String String :=
  match j { str s => ok s, _ => err "expected string" }

def Json.get_array (j : Json) : Result String (List Json) :=
  match j { array a => ok a, _ => err "expected array" }

def Json.get_object (j : Json) : Result String (BTreeMap String Json) :=
  match j { object o => ok o, _ => err "expected object" }

// ─── Object manipulation ───

def Json.object_get (key : String) (o : BTreeMap String Json) : Option Json :=
  Map.lookup key o

def Json.object_set (key : String) (value : Json) (o : BTreeMap String Json) : BTreeMap String Json :=
  Map.insert key value o

def Json.object_delete (key : String) (o : BTreeMap String Json) : BTreeMap String Json :=
  Map.delete key o

// ─── Tests: parser ───

@[test]
def test_empty_object : Bool :=
  match Json.parse "{}" {
   ok o => Json.beq o (object BTreeMap.empty),
   err e => false,
  }

@[test]
def test_parse_null : Bool :=
  match Json.parse "null" {
    ok j => Json.beq j null,
    err _ => false
  }

@[test]
def test_parse_true : Bool :=
  match Json.parse "true" {
    ok j => Json.beq j (bool true),
    err _ => false
  }

@[test]
def test_parse_false : Bool :=
  match Json.parse "false" {
    ok j => Json.beq j (bool false),
    err _ => false
  }

@[test]
def test_parse_integer : Bool :=
  match Json.parse "42" {
    ok j => Json.beq j (num (int 42)),
    err _ => false
  }

@[test]
def test_parse_negative_integer : Bool :=
  match Json.parse "-42" {
    ok j => Json.beq j (num (int (neg_i64 42))),
    err _ => false
  }

@[test]
def test_parse_string : Bool :=
  match Json.parse "\"hello\"" {
    ok j => Json.beq j (str "hello"),
    err _ => false
  }

@[test]
def test_parse_string_empty : Bool :=
  match Json.parse "\"\"" {
    ok j => Json.beq j (str ""),
    err _ => false
  }

@[test]
def test_parse_string_with_escapes : Bool :=
  match Json.parse "\"a\\nb\\tc\\\"d\"" {
    ok j => Json.beq j (str "a\nb\tc\"d"),
    err _ => false
  }

@[test]
def test_parse_empty_array : Bool :=
  match Json.parse "[]" {
    ok j => Json.beq j (array List.empty),
    err _ => false
  }

@[test]
def test_parse_array_simple : Bool :=
  match Json.parse "[1,2,3]" {
    ok j => Json.beq j (array [num (int 1), num (int 2), num (int 3)]),
    err _ => false
  }

@[test]
def test_parse_object_simple : Bool :=
  match Json.parse "{\"a\":1}" {
    ok j => Json.beq j (object (Map.insert "a" (num (int 1)) BTreeMap.empty)),
    err _ => false
  }

@[test]
def test_parse_nested_structures : Bool :=
  match Json.parse "{\"a\":[1,2],\"b\":{\"c\":true}}" {
    ok j =>
      let inner := Map.insert "c" (bool true) BTreeMap.empty in
      let expected := Map.insert "a" (array [num (int 1), num (int 2)])
        (Map.insert "b" (object inner) BTreeMap.empty) in
      Json.beq j (object expected),
    err _ => false
  }

@[test]
def test_parse_with_whitespace : Bool :=
  match Json.parse " { \"a\" : [ 1 , 2 ] } " {
    ok j => Json.beq j (object (Map.insert "a" (array [num (int 1), num (int 2)]) BTreeMap.empty)),
    err _ => false
  }

// ─── Tests: serializer ───

@[test]
def test_serialize_null : Bool :=
  Json.to_string null == "null"

@[test]
def test_serialize_bool : Bool :=
  Json.to_string (bool true) == "true" && Json.to_string (bool false) == "false"

@[test]
def test_serialize_integer : Bool :=
  Json.to_string (num (int 42)) == "42"

@[test]
def test_serialize_negative_integer : Bool :=
  Json.to_string (num (int (neg_i64 42))) == "-42"

@[test]
def test_serialize_string : Bool :=
  Json.to_string (str "hello") == "\"hello\""

@[test]
def test_serialize_string_empty : Bool :=
  Json.to_string (str "") == "\"\""

@[test]
def test_serialize_string_with_escapes : Bool :=
  Json.to_string (str "a\nb\tc\"d") == "\"a\\nb\\tc\\\"d\""

@[test]
def test_serialize_empty_array : Bool :=
  Json.to_string (array List.empty) == "[]"

@[test]
def test_serialize_array : Bool :=
  Json.to_string (array [num (int 1), num (int 2), num (int 3)]) == "[1,2,3]"

@[test]
def test_serialize_empty_object : Bool :=
  Json.to_string (object BTreeMap.empty) == "{}"

@[test]
def test_serialize_object : Bool :=
  Json.to_string (object (Map.insert "a" (num (int 1)) BTreeMap.empty)) == "{\"a\":1}"

// ─── Tests: round-trip ───

@[test]
def test_roundtrip_null : Bool :=
  match Json.parse (Json.to_string null) {
    ok j => Json.beq j null,
    err _ => false
  }

@[test]
def test_roundtrip_bool : Bool :=
  match Json.parse (Json.to_string (bool true)) {
    ok j => Json.beq j (bool true),
    err _ => false
  }

@[test]
def test_roundtrip_integer : Bool :=
  match Json.parse (Json.to_string (num (int (neg_i64 7)))) {
    ok j => Json.beq j (num (int (neg_i64 7))),
    err _ => false
  }

@[test]
def test_roundtrip_string : Bool :=
  match Json.parse (Json.to_string (str "hi\nthere")) {
    ok j => Json.beq j (str "hi\nthere"),
    err _ => false
  }

@[test]
def test_roundtrip_array : Bool :=
  let value := array [num (int 1), str "two", bool true, null] in
  match Json.parse (Json.to_string value) {
    ok j => Json.beq j value,
    err _ => false
  }

@[test]
def test_roundtrip_object : Bool :=
  let value := object (Map.insert "a" (num (int 1)) (Map.insert "b" (str "two") BTreeMap.empty)) in
  match Json.parse (Json.to_string value) {
    ok j => Json.beq j value,
    err _ => false
  }

@[test]
def test_roundtrip_nested : Bool :=
  let inner := Map.insert "c" (array [num (int 1), num (int 2)]) BTreeMap.empty in
  let value := object (Map.insert "a" (object inner) (Map.insert "b" null BTreeMap.empty)) in
  match Json.parse (Json.to_string value) {
    ok j => Json.beq j value,
    err _ => false
  }

// ─── Tests: helpers ───

@[test]
def test_escape_string : Bool :=
  Json.escape_string "a\"b\\c" == "a\\\"b\\\\c"

@[test]
def test_list_intercalate : Bool :=
  List.intercalate "," ["a", "b", "c"] == "a,b,c" &&
  List.intercalate "," (List.empty : List String) == "" &&
  List.intercalate "," ["only"] == "only"

@[test]
def test_json_type_checkers : Bool :=
  Json.is_null null &&
  Json.is_bool (bool true) &&
  Json.is_num (num (int 1)) &&
  Json.is_str (str "a") &&
  Json.is_array (array List.empty) &&
  Json.is_object (object BTreeMap.empty) &&
  Bool.not (Json.is_null (bool true))

@[test]
def test_json_accessors : Bool :=
  match Json.get_str (str "a") {
    ok s => s == "a",
    err _ => false
  } &&
  match Json.get_str (bool true) {
    ok _ => false,
    err _ => true
  }

/// Compare an Option Json against an expected value without relying on the
/// generic `BEq (Option A)` instance (see the note on Json.array_beq above).
def json_option_eq (opt : Option Json) (expected : Json) : Bool :=
  match opt {
    some j => Json.beq j expected,
    none => false
  }

def json_option_is_none (opt : Option Json) : Bool :=
  match opt {
    some _ => false,
    none => true
  }

@[test]
def test_json_object_manipulation : Bool :=
  let o1 := Json.object_set "a" (num (int 1)) BTreeMap.empty in
  let o2 := Json.object_set "b" (num (int 2)) o1 in
  let o3 := Json.object_delete "a" o2 in
  json_option_eq (Json.object_get "a" o1) (num (int 1)) &&
  json_option_is_none (Json.object_get "a" o3) &&
  json_option_eq (Json.object_get "b" o3) (num (int 2))
