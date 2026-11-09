/// Params-reader tests: what a method's params say, and what a malformed one says.
///
/// THE WRONG-TYPE CASES ARE THE POINT. Reading a field that is present and correct is
/// not where a param reader breaks; it breaks on the input a real client sends when
/// it is confused -- a version as a string, a `textDocument` that is not an object,
/// an array where an element was expected -- and the failure it must not have is a
/// crash. A server that dies on one of these dies the first time a user types
/// something surprising, and it dies on a NOTIFICATION, where there is no reply to
/// deliver and nobody to tell. So every case below whose answer is `<none>` is a case
/// where the server goes on running and logs.
///
/// EVERY FIXTURE IS A NAMED DEF AND EVERY FIXTURE IS PINNED BY `lp_roundtrips`, and
/// the guard is the most important thing here rather than the last thing. Almost
/// every expectation in this file is `<none>`, and `lp_json` answers `null` for text
/// that does not parse -- which reads as `<none>` for all of them. So a fixture with a
/// missing brace does not fail a test, it turns the test into a test of the absent
/// case, which PASSES. This file shipped that shape of bug in a sibling file before
/// the guard was written; naming the fixtures once and asserting each parses back to
/// itself byte for byte is what makes the typo loud.
///
/// The guard is an EXACT round trip, which means it also requires each fixture's keys
/// to be in wire order -- `Json.to_string` walks a `BTreeMap`, so `{"b":1,"a":2}`
/// round-trips to the sorted spelling and fails the guard for that reason instead.
///
/// Fixtures are parsed from JSON TEXT rather than built with the constructors,
/// because the text is what a client actually sends -- a fixture built from
/// `Json.make_object` could be well-formed in a way no client's bytes ever are, and
/// the parse path is the one being exercised.
///
/// Field reads go through the typed accessor defs below (`lp_*`), never inline in a
/// `#[test]` def, per this repo's recorded `#[test]` plus struct-field codegen
/// hazard. The `lp_` prefix is collision-avoiding: whole-program scope is shared with
/// every other mote's tests, and a sibling test file's helper of the same name is a
/// documented miscompile.
use json::json {Json}
use lsp::params {
    lsp_param_i64, lsp_param_index, lsp_param_nested, lsp_param_nested_i64, lsp_param_nested_str,
    lsp_param_str, lsp_param_str_list,
}
use toolkit::jsonrpc {rpc_field, rpc_object}

// --- Fixture plumbing ---

/// Parse a fixture, or `null`. See the file doc: `null` is why `lp_roundtrips` exists.
def lp_json (s : String) : Json :=
    match Json.parse s {
        Result.err _e => Json.make_null,
        Result.ok j => j,
    }

/// THE GUARD: the fixture parses, and parses to exactly the text written.
def lp_roundtrips (s : String) : Bool := String.beq (Json.to_string (lp_json s)) s

def lp_str (o : Option String) : String :=
    match o {
        Option.none => "<none>",
        Option.some s => s,
    }

def lp_i64 (o : Option I64) : String :=
    match o {
        Option.none => "<none>",
        Option.some n => I64.to_string n,
    }

/// A node rendered back to its wire text, so a test can compare one read against an
/// exact string instead of matching the constructor it happens to be.
def lp_node (o : Option Json) : String :=
    match o {
        Option.none => "<none>",
        Option.some j => Json.to_string j,
    }

/// The list joined with `|` and NO leading separator, so an empty list and a
/// one-element list holding the empty string are different renderings.
def lp_list (xs : List String) : String := lp_join xs ""

#[partial]
def lp_join (xs : List String) (acc : String) : String :=
    match xs {
        List.empty => acc,
        List.cons x rest =>
            if String.is_empty acc
            then lp_join rest x
            else lp_join rest (String.concat acc (String.concat "|" x)),
    }

// --- Fixtures: params that are objects but not the shape a method wants ---

def lp_f_absent : String := "{}"

/// The whole params node as a scalar, an array, or an explicit null. A request that
/// omitted params sends none of these -- `rpc_params` answers `Option.none` for that
/// and the handler decides -- so these are the shapes a client produces when it is
/// confused rather than shapes it produces when it is terse.
def lp_f_null : String := "null"

def lp_f_array_params : String := "[1,2]"

def lp_f_uri_only : String := "{\"uri\":\"file:///a.mo\"}"

def lp_f_uri_int : String := "{\"uri\":7}"

def lp_f_uri_null : String := "{\"uri\":null}"

def lp_f_uri_array : String := "{\"uri\":[\"a\"]}"

def lp_f_uri_object : String := "{\"uri\":{\"a\":1}}"

def lp_f_version_int : String := "{\"version\":7}"

def lp_f_version_str : String := "{\"version\":\"3\"}"

/// A float, as TEXT -- and it is deliberately NOT in the round-trip guard below,
/// because it does not round-trip. `Json`'s parser never produces a `float` and fails
/// the whole document on one (`json.mo:42-45`: float parsing "needs an I64/String ->
/// F64 native conversion that doesn't exist yet"), so this fixture parses to `null`
/// no matter how well formed it is. It is kept as a fixture because that behaviour is
/// worth pinning -- see `test_the_parser_rejects_a_float_outright` -- but the honest
/// place to test the integer READER's float rejection is a node built by hand, which
/// is what `lp_version_float_node` is.
def lp_f_version_float : String := "{\"version\":1.5}"

def lp_f_doc_ok : String := "{\"textDocument\":{\"uri\":\"file:///a.mo\",\"version\":3}}"

def lp_f_doc_str : String := "{\"textDocument\":\"a\"}"

def lp_f_doc_empty : String := "{\"textDocument\":{}}"

def lp_f_doc_array : String := "{\"textDocument\":[{\"uri\":\"a\"}]}"

def lp_f_changes : String := "{\"contentChanges\":[{\"text\":\"first\"},{\"text\":\"second\"}]}"

def lp_f_changes_object : String := "{\"contentChanges\":{}}"

def lp_f_changes_str : String := "{\"contentChanges\":\"text\"}"

def lp_f_changes_one : String := "{\"contentChanges\":[1]}"

def lp_f_encodings : String := "{\"positionEncodings\":[\"utf-16\",\"utf-8\"]}"

/// Non-strings inside the list, including a `null` that a JavaScript client produces
/// by serializing an array with a hole in it.
def lp_f_encodings_mixed : String := "{\"positionEncodings\":[\"utf-8\",7,null,\"utf-16\"]}"

def lp_f_encodings_str : String := "{\"positionEncodings\":\"utf-8\"}"

def lp_f_encodings_empty : String := "{\"positionEncodings\":[]}"

def lp_f_encodings_ints : String := "{\"positionEncodings\":[1,2]}"

#[test]
def test_every_fixture_is_the_json_it_looks_like : Bool :=
    lp_roundtrips lp_f_absent
        && lp_roundtrips lp_f_null
        && lp_roundtrips lp_f_array_params
        && lp_roundtrips lp_f_uri_only
        && lp_roundtrips lp_f_uri_int
        && lp_roundtrips lp_f_uri_null
        && lp_roundtrips lp_f_uri_array
        && lp_roundtrips lp_f_uri_object
        && lp_roundtrips lp_f_version_int
        && lp_roundtrips lp_f_version_str
        && lp_roundtrips lp_f_doc_ok
        && lp_roundtrips lp_f_doc_str
        && lp_roundtrips lp_f_doc_empty
        && lp_roundtrips lp_f_doc_array
        && lp_roundtrips lp_f_changes
        && lp_roundtrips lp_f_changes_object
        && lp_roundtrips lp_f_changes_str
        && lp_roundtrips lp_f_changes_one
        && lp_roundtrips lp_f_encodings
        && lp_roundtrips lp_f_encodings_mixed
        && lp_roundtrips lp_f_encodings_str
        && lp_roundtrips lp_f_encodings_empty
        && lp_roundtrips lp_f_encodings_ints

// --- Key-level reads ---

/// A string field, at the top level.
#[test]
def test_a_top_level_string_field_is_read : Bool :=
    String.beq (lp_str (lsp_param_str "uri" (lp_json lp_f_uri_only))) "file:///a.mo"

/// An integer field, at the top level.
#[test]
def test_a_top_level_integer_field_is_read : Bool :=
    String.beq (lp_i64 (lsp_param_i64 "version" (lp_json lp_f_version_int))) "7"

/// A field that is not there, in the three shapes that means: a key the object does
/// not have, no object at all, and an array.
#[test]
def test_an_absent_field_is_absent : Bool :=
    String.beq (lp_str (lsp_param_str "uri" (lp_json lp_f_absent))) "<none>"
        && String.beq (lp_str (lsp_param_str "uri" (lp_json lp_f_null))) "<none>"
        && String.beq (lp_str (lsp_param_str "uri" (lp_json lp_f_array_params))) "<none>"
        && String.beq (lp_i64 (lsp_param_i64 "version" (lp_json lp_f_absent))) "<none>"

/// A field that is present and is the WRONG TYPE is absent, not an error and not a
/// coerced value. The version-as-a-string case is the one a real client produces --
/// a JavaScript number that was stringified somewhere earlier -- and the alternative
/// to refusing it is a version the client never sent, which makes the client discard
/// every diagnostic set this server publishes.
///
/// A `null` field is absent and not "the null value": the specification writes
/// `version` as nullable, and null there means the client has no number for it, which
/// is the absent case, not a number this reader can hand on.
#[test]
def test_a_field_of_the_wrong_type_is_absent : Bool :=
    String.beq (lp_i64 (lsp_param_i64 "version" (lp_json lp_f_version_str))) "<none>"
        && String.beq (lp_str (lsp_param_str "uri" (lp_json lp_f_uri_int))) "<none>"
        && String.beq (lp_str (lsp_param_str "uri" (lp_json lp_f_uri_null))) "<none>"
        && String.beq (lp_str (lsp_param_str "uri" (lp_json lp_f_uri_array))) "<none>"
        && String.beq (lp_str (lsp_param_str "uri" (lp_json lp_f_uri_object))) "<none>"

/// A number that is not an integer is not an integer version. `Json.get_num_i64`
/// rejects a float rather than truncating it, and for this one field that is the
/// difference between a version the client sent and one this server made up.
///
/// THE NODE IS BUILT BY HAND, because the parser cannot make one. This test used to
/// feed the fixture text `{"version":1.5}` and pass -- for the wrong reason: the
/// PARSER failed, so the reader was handed `null` and never saw a float at all. The
/// round-trip guard is what surfaced it. `Json.make_num_float` is the only way to
/// reach `Json.number_to_i64`'s `err "expected integer"` arm (`json.mo:668-672`), so
/// this is the test of the reader, and the test below is the test of the parser.
#[test]
def test_a_float_is_not_an_integer_field : Bool :=
    String.beq (lp_i64 (lsp_param_i64 "version" lp_version_float_node)) "<none>"
        && String.beq (lp_i64 (lsp_param_i64 "version" (lp_json lp_f_version_int))) "7"

/// Named empty list rather than a bare `List.empty` in argument position, whose
/// element type would have to be inferred from the callee.
def lp_no_fields : List (Pair String Json) := List.empty

/// `{"version":1.5}`, constructed rather than parsed.
def lp_version_float_node : Json :=
    rpc_object (List.cons (Pair.pair "version" (Json.make_num_float 1.5)) lp_no_fields)

/// THE PARSER'S HALF, pinned as observed behaviour rather than fixed.
///
/// `Json.parse` answers `null` for the whole document on any float, so a client that
/// puts a float ANYWHERE in its params makes the entire message unreadable -- not
/// just that field. For this server that is tolerable, because every number the
/// protocol sends it is an integer and a client that sends floats is speaking a
/// dialect nothing here reads; but it is not something to discover from a bug report,
/// so it is asserted. If `Json`'s parser ever grows float support this test flips,
/// which is the point: the arm it describes is a gap in `lang`, not a decision here.
#[test]
def test_the_parser_rejects_a_float_outright : Bool :=
    String.beq (lp_node (Option.some (lp_json lp_f_version_float))) "null"

// --- Nested reads ---

/// The shape almost every method in this protocol has: an object field naming the
/// document, with the interesting values inside it. Both the node and the two typed
/// reads are checked, because they are three entry points over one path.
#[test]
def test_a_nested_field_is_read_at_both_levels : Bool :=
    let p : Json := lp_json lp_f_doc_ok in
    String.beq (lp_str (lsp_param_nested_str "textDocument" "uri" p)) "file:///a.mo"
        && String.beq (lp_i64 (lsp_param_nested_i64 "textDocument" "version" p)) "3"
        && String.beq (lp_node (lsp_param_nested "textDocument" "uri" p)) "\"file:///a.mo\""

/// BOTH levels must be objects for a nested read to answer, and the outer being
/// wrong is the case worth pinning: a `textDocument` sent as a string is not a struct
/// that happens to be missing `uri`, it is a malformed request. An array of objects is
/// not an object either -- a reader that unwrapped a one-element list would answer
/// here, and the value it answered with would be a document the client did not name.
#[test]
def test_nesting_requires_both_levels_to_be_objects : Bool :=
    String.beq (lp_str (lsp_param_nested_str "textDocument" "uri" (lp_json lp_f_doc_str))) "<none>"
        && String.beq (lp_str (lsp_param_nested_str "textDocument" "uri" (lp_json lp_f_absent))) "<none>"
        && String.beq (lp_str (lsp_param_nested_str "textDocument" "uri" (lp_json lp_f_doc_empty))) "<none>"
        && String.beq (lp_str (lsp_param_nested_str "textDocument" "uri" (lp_json lp_f_doc_array))) "<none>"

// --- Array reads ---

/// Array elements by index, which is `contentChanges[0]` and nothing else.
#[test]
def test_an_array_element_is_read_by_index : Bool :=
    let p : Json := lp_json lp_f_changes in
    String.beq (lp_node (lsp_param_index 0 (rpc_field "contentChanges" p))) "{\"text\":\"first\"}"
        && String.beq (lp_node (lsp_param_index 1 (rpc_field "contentChanges" p))) "{\"text\":\"second\"}"
        && String.beq (lp_node (lsp_param_index 2 (rpc_field "contentChanges" p))) "<none>"

/// An index into something that is not an array, or is not there, answers nothing --
/// including index 0, which a reader that treated "one element or a scalar" as
/// equivalent would answer with the scalar itself. A negative index answers nothing
/// too, which is what keeps the walk to the end of the list from being a wrap: the
/// index only ever decreases towards zero, and zero never arrives.
#[test]
def test_an_index_into_a_non_array_answers_nothing : Bool :=
    String.beq (lp_node (lsp_param_index 0 (rpc_field "contentChanges" (lp_json lp_f_changes_object)))) "<none>"
        && String.beq (lp_node (lsp_param_index 0 (rpc_field "contentChanges" (lp_json lp_f_changes_str)))) "<none>"
        && String.beq (lp_node (lsp_param_index 0 (rpc_field "contentChanges" (lp_json lp_f_absent)))) "<none>"
        && String.beq (lp_node (lsp_param_index (0 - 1) (rpc_field "contentChanges" (lp_json lp_f_changes_one)))) "<none>"

// --- String lists ---

/// The one list-valued field this server reads: the encodings a client offers.
#[test]
def test_a_string_list_keeps_its_strings_in_order : Bool :=
    String.beq (lp_list (lsp_param_str_list "positionEncodings" (lp_json lp_f_encodings))) "utf-16|utf-8"

/// Non-strings are dropped rather than failing the read, and the strings around them
/// keep their order. Dropping loses a choice; failing would lose every choice.
#[test]
def test_a_string_list_drops_what_is_not_a_string : Bool :=
    String.beq (lp_list (lsp_param_str_list "positionEncodings" (lp_json lp_f_encodings_mixed))) "utf-8|utf-16"

/// An absent list, a non-array, an empty list, and a list of nothing this reader can
/// use are all the empty list -- the caller's default is what turns that into a
/// decision, and this reader does not make it.
#[test]
def test_an_absent_string_list_is_empty : Bool :=
    String.beq (lp_list (lsp_param_str_list "positionEncodings" (lp_json lp_f_absent))) ""
        && String.beq (lp_list (lsp_param_str_list "positionEncodings" (lp_json lp_f_encodings_str))) ""
        && String.beq (lp_list (lsp_param_str_list "positionEncodings" (lp_json lp_f_encodings_empty))) ""
        && String.beq (lp_list (lsp_param_str_list "positionEncodings" (lp_json lp_f_encodings_ints))) ""
