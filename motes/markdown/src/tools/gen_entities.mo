// Regenerate src/entities.mo from the WHATWG named-entity list.
//
//   monad run motes/markdown/src/tools/gen_entities.mo -- \
//       --entities /tmp/mdgen/entities.json --out motes/markdown/src/entities.mo
//
// Add `--check` to verify the committed file is current instead of writing.
// Input: https://html.spec.whatwg.org/entities.json (not vendored).
//
// Two things differ from the Python tool this replaces, both silent data
// bugs there: names are ordered by the entity name with `&`/`;` stripped
// (`;` sorts after the digits, which put `emsp13` before `emsp`), and each
// value comes from the entry's `codepoints` array (motes/json does not
// combine UTF-16 surrogate pairs, so an astral entity's `characters`
// decodes to U+FFFD pairs).

use gen::io {Gen.arg, Gen.banner, Gen.flag, Gen.write_or_check}
use gen::tree {Gen.emit, Leaf, Spec, leaf, spec}
use lang::construct {Vis, apps, con, con_app, def_text, global, i64, if_, str, var}
use lang::types {Param}
use json::json {
    Json, Json.ParseError, Json.get_array, Json.get_num, Json.get_num_i64,
    Json.get_object, Json.object_get, Json.parse,
}
use lib::scan {Markdown.utf8_of_codepoint}
use std::io {IO.println, IO.read_file}
use std::list {List.filter_map, List.length, List.sort_by}
use std::map {BTreeMap, BTreeMap.to_list}
use std::path {Path}
use std::stream {StreamError}

def url : String := "https://html.spec.whatwg.org/entities.json"

def main (args : List String) : IO I64 :=
    match Gen.arg args "--entities" {
        Option.some entities => with_out args entities,
        Option.none => usage,
    }

def with_out (args : List String) (entities : String) : IO I64 :=
    match Gen.arg args "--out" {
        Option.some out => do {
            let raw <- IO.read_file (Path.path entities);
            let code <- generate raw out (Gen.flag args "--check");
            return code
        },
        Option.none => usage,
    }

def usage : IO I64 := do {
    let _printed <- IO.println
        "usage: gen_entities --entities <entities.json> --out <entities.mo> [--check]";
    return 2
}

def generate (raw : Result StreamError String) (out : String) (check : Bool) : IO I64 :=
    match raw {
        Result.err e => fail_with (String.concat "cannot read the input: " e.message),
        Result.ok text => after_render (render text) out check,
    }

def after_render (rendered : Result String String) (out : String) (check : Bool) : IO I64 :=
    match rendered {
        Result.err message => fail_with message,
        Result.ok source => Gen.write_or_check check out source,
    }

def fail_with (message : String) : IO I64 := do {
    let _printed <- IO.println message;
    return 1
}

// --- Pure generation ---

def render (input : String) : Result String String :=
    match Json.parse input {
        Result.err e => Result.err (String.concat "entities.json did not parse: "
            (Json.ParseError.to_string e)),
        Result.ok doc => after_parse (Json.get_object doc),
    }

def after_parse (parsed : Result String (BTreeMap String Json)) : Result String String :=
    match parsed {
        Result.err message => Result.err message,
        Result.ok entries => Result.ok (render_source entries),
    }

def render_source (entries : BTreeMap String Json) : String :=
    let table : List (Pair String String) := entity_pairs (BTreeMap.to_list entries) in
    let count := List.length table in
    let tree := Gen.emit entity_spec (leaf_list table) in
    String.concat (Gen.banner tool (banner_notes count))
        (String.concat (entity_count_text count) tree)

/// The banner's own lines: where the data came from, its digest, and the
/// two ordering/decoding decisions a reader of the table would otherwise
/// have to rediscover.
def banner_notes (count : I64) : List String :=
    [ String.concat "Source: " url,
      String.concat (I64.to_string count) " semicolon-terminated CommonMark entities.",
      "",
      "Names are ordered by the entity name with `&` and `;` stripped, not by",
      "the raw JSON key: `;` sorts after the digits, which put `emsp13` before",
      "`emsp`.",
      "Values come from each entry's `codepoints` array, not `characters`:",
      "motes/json does not combine UTF-16 surrogate pairs, so an astral",
      "entity's `characters` decodes to U+FFFD pairs." ]

def tool : String := "motes/markdown/src/tools/gen_entities.mo"

/// The `&name;` entries as (stripped name, value), sorted by name. Only the
/// semicolon-terminated names are CommonMark entities.
def entity_pairs (entries : List (Pair String Json)) : List (Pair String String) :=
    List.sort_by pair_name_lt (List.filter_map strip_entry entries)

def pair_name_lt (a : Pair String String) (b : Pair String String) : Bool :=
    String.lt a.first b.first

/// One raw `&name;` key as (name, value), or none when the key has no
/// terminator and so is not a CommonMark entity.
#[partial]
def strip_entry (entry : Pair String Json) : Option (Pair String String) :=
    match entry {
        Pair.pair key value =>
            if String.ends_with key ";"
            then Option.some (Pair.pair (strip_amp_semicolon key) (entry_value value))
            else Option.none,
    }

def strip_amp_semicolon (key : String) : String :=
    String.slice key 1 (I64.sub (String.length key) 2)

def entry_value (entry : Json) : String :=
    entry_fields (Json.get_object entry)

def entry_fields (fields : Result String (BTreeMap String Json)) : String :=
    match fields {
        Result.err _ => "",
        Result.ok o => codepoints_text (Json.object_get "codepoints" o),
    }

def codepoints_text (cps : Option Json) : String :=
    match cps {
        Option.none => "",
        Option.some j => codepoint_array (Json.get_array j),
    }

def codepoint_array (items : Result String (List Json)) : String :=
    match items {
        Result.err _ => "",
        Result.ok xs => String.concat_list (List.map codepoint_text xs),
    }

def codepoint_text (j : Json) : String :=
    codepoint_of (Json.get_num_i64 (Json.get_num j))

def codepoint_of (n : Result String I64) : String :=
    match n {
        Result.ok cp => Markdown.utf8_of_codepoint cp,
        Result.err _ => "",
    }

#[partial]
def leaf_list (table : List (Pair String String)) : List Leaf :=
    match table {
        List.empty => List.empty,
        List.cons hd tl => List.cons (entity_leaf hd) (leaf_list tl),
    }

def entity_leaf (entry : Pair String String) : Leaf :=
    leaf (str entry.first)
        (if_ (apps (global "String.beq") [var 0 "name", str entry.first])
            (con_app "Option" "some" [str entry.second])
            (con "Option" "none"))

def entity_spec : Spec :=
    spec "Markdown.entity_lookup" "name" (global "String")
        (apps (global "Option") [global "String"])
        "String.lt" (con "Option" "none")

def entity_count_text (count : I64) : String :=
    String.concat (def_text [] Vis.vis_public "Markdown.entity_count"
        (List.empty : List Param) (global "I64") (i64 count)) "\n"
