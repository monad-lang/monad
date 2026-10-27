/// YAML reading and writing: a `Yaml` value type, a core-schema resolver,
/// a block printer and a flow printer.
///
/// SCOPE (YAML 1.2 core schema, "config subset"): block mappings and
/// sequences (nested, compact `- key: value`, indentless sequences), one-line
/// flow `[...]`/`{...}`, `#` comments, plain / single-quoted / double-quoted
/// scalars, block scalars `|`/`>` with chomping, and one document with an
/// optional `---`/`...`. Anchors, aliases, tags, directives, complex keys,
/// multi-document input, multi-line flow, multi-line plain/quoted scalars and
/// explicit block-scalar indents are EXPLICIT parse errors, never a silent
/// misparse -- the policy `motes/toml` states for its own subset.
///
/// Mappings are `BTreeMap String Yaml`, so printing sorts keys. `null` is
/// the empty document. Strings never print as block scalars: newlines and
/// control bytes are escaped inside double quotes.
use init::string {}
use init::number {}
use std::map {Map, BTreeMap, BTreeMap.to_list, empty}
use std::list {Show, List.intercalate}
use std::parse {Parse.i64, Parse.f64}

// ─── Types ───

/// A parse failure, positioned at a 1-based line and column.
pub struct Yaml.ParseError {
    line : I64,
    column : I64,
    message : String,
}

pub def Yaml.ParseError.to_string (e : Yaml.ParseError) : String :=
    String.concat "line " (String.concat (I64.to_string e.line)
        (String.concat ", column " (String.concat (I64.to_string e.column)
            (String.concat ": " e.message))))

/// A YAML value. `mapping`, not `map`: `HashMap` already declares a
/// constructor named `map`, and constructors are registered corpus-wide.
pub type Yaml {
    null,
    bool (b : Bool),
    int (i : I64),
    float (f : F64),
    str (s : String),
    seq (xs : List Yaml),
    mapping (m : BTreeMap String Yaml),
}

def Yaml.mk_error (line : I64) (column : I64) (message : String) : Yaml.ParseError :=
    let e : Yaml.ParseError := { line := line, column := column, message := message } in e

// Bare constructor names in EXPRESSION position need the `open`; patterns
// resolve without it. `motes/json/src/json.mo` does the same for `Json`.
open Yaml {null, bool, int, float, str, seq, mapping}

// ─── Parser scaffolding ───

/// One source line: its 1-based number, how many leading spaces it has, and
/// the line's text AFTER that indentation. `text` is RAW -- comments are
/// stripped on demand, because block-scalar content must keep `#`.
struct Yaml.Line {
    number : I64,
    indent : I64,
    text : String,
}

/// A block parse result: the value plus the lines it did not consume. A
/// dedicated type rather than `Result e (Pair (List Line) A)`, because the
/// checker does not handle two different type variables nested that way.
type Yaml.Parsed A {
    y_ok (rest : List Yaml.Line) (value : A),
    y_err (error : Yaml.ParseError),
}

type Yaml.Chomp {
    y_strip,
    y_clip,
    y_keep,
}

struct Yaml.BlockHeader {
    folded : Bool,
    chomp : Yaml.Chomp,
}

/// A flow-parsed value and the unconsumed suffix.
struct Yaml.Flow {
    rest : String,
    value : Yaml,
}

struct Yaml.FlowKey {
    rest : String,
    key : String,
}

/// A quoted scalar's content and the suffix after its closing quote.
struct Yaml.Quoted {
    rest : String,
    text : String,
}

/// A block scalar's consumed source lines (already de-indented) and the
/// lines after it.
struct Yaml.BlockBody {
    rest : List Yaml.Line,
    lines : List String,
}

open Yaml.Parsed {y_ok, y_err}
open Yaml.Chomp {y_strip, y_clip, y_keep}

def Yaml.mk_line (number : I64) (indent : I64) (text : String) : Yaml.Line :=
    let l : Yaml.Line := { number := number, indent := indent, text := text } in l

def Yaml.mk_header (folded : Bool) (chomp : Yaml.Chomp) : Yaml.BlockHeader :=
    let h : Yaml.BlockHeader := { folded := folded, chomp := chomp } in h

def Yaml.mk_flow (rest : String) (value : Yaml) : Yaml.Flow :=
    let f : Yaml.Flow := { rest := rest, value := value } in f

def Yaml.mk_key (rest : String) (key : String) : Yaml.FlowKey :=
    let k : Yaml.FlowKey := { rest := rest, key := key } in k

def Yaml.mk_block_body (rest : List Yaml.Line) (lines : List String) : Yaml.BlockBody :=
    let b : Yaml.BlockBody := { rest := rest, lines := lines } in b

// ─── Equality (hand-rolled; generic BEq does not dispatch reliably) ───

#[partial]
def Yaml.seq_beq (a : List Yaml) (b : List Yaml) : Bool :=
    match a {
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false,
        },
        List.cons ha ta => match b {
            List.empty => false,
            List.cons hb tb => Bool.and (Yaml.beq ha hb) (Yaml.seq_beq ta tb),
        },
    }

def Yaml.pair_beq (a : Pair String Yaml) (b : Pair String Yaml) : Bool :=
    match a {
        Pair.pair ka va => match b {
            Pair.pair kb vb => Bool.and (String.beq ka kb) (Yaml.beq va vb),
        },
    }

#[partial]
def Yaml.pairs_beq (a : List (Pair String Yaml)) (b : List (Pair String Yaml)) : Bool :=
    match a {
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false,
        },
        List.cons pa ta => match b {
            List.empty => false,
            List.cons pb tb => Bool.and (Yaml.pair_beq pa pb) (Yaml.pairs_beq ta tb),
        },
    }

/// `BTreeMap.to_list` hides the structural relation from the termination
/// checker; the pair walk itself is structural, so `#[terminating]` is the
/// honest annotation (not `#[partial]`).
#[terminating]
def Yaml.mapping_beq (a : BTreeMap String Yaml) (b : BTreeMap String Yaml) : Bool :=
    Yaml.pairs_beq (BTreeMap.to_list a) (BTreeMap.to_list b)

pub def Yaml.beq (a : Yaml) (b : Yaml) : Bool :=
    match a {
        null => match b {
            null => true,
            _ => false,
        },
        bool ba => match b {
            bool bb => ba == bb,
            _ => false,
        },
        int ia => match b {
            int ib => I64.beq ia ib,
            _ => false,
        },
        float fa => match b {
            float fb => F64.beq fa fb,
            _ => false,
        },
        str sa => match b {
            str sb => String.beq sa sb,
            _ => false,
        },
        seq xa => match b {
            seq xb => Yaml.seq_beq xa xb,
            _ => false,
        },
        mapping ma => match b {
            mapping mb => Yaml.mapping_beq ma mb,
            _ => false,
        },
    }

pub instance BEq Yaml {
    def beq (a b : Yaml) : Bool := Yaml.beq a b
}

// ─── Construction and access ───

pub def Yaml.make_null : Yaml := null
pub def Yaml.make_bool (b : Bool) : Yaml := bool b
pub def Yaml.make_int (i : I64) : Yaml := int i
pub def Yaml.make_float (f : F64) : Yaml := float f
pub def Yaml.make_str (s : String) : Yaml := str s
pub def Yaml.make_seq (xs : List Yaml) : Yaml := seq xs
pub def Yaml.make_mapping (m : BTreeMap String Yaml) : Yaml := mapping m

#[partial]
def Yaml.mapping_pairs_insert (pairs : List (Pair String Yaml)) (acc : BTreeMap String Yaml) : BTreeMap String Yaml :=
    match pairs {
        List.empty => acc,
        List.cons p rest =>
            match p {
                Pair.pair k v => Yaml.mapping_pairs_insert rest (Map.insert k v acc),
            },
    }

pub def Yaml.make_mapping_pairs (pairs : List (Pair String Yaml)) : Yaml :=
    mapping (Yaml.mapping_pairs_insert pairs BTreeMap.empty)

pub def Yaml.mapping_get (key : String) (m : BTreeMap String Yaml) : Option Yaml :=
    Map.lookup key m

pub def Yaml.get_bool (y : Yaml) : Result String Bool :=
    match y {
        bool b => Result.ok b,
        _ => Result.err "expected bool",
    }

pub def Yaml.get_int (y : Yaml) : Result String I64 :=
    match y {
        int i => Result.ok i,
        _ => Result.err "expected integer",
    }

pub def Yaml.get_float (y : Yaml) : Result String F64 :=
    match y {
        float f => Result.ok f,
        _ => Result.err "expected float",
    }

pub def Yaml.get_str (y : Yaml) : Result String String :=
    match y {
        str s => Result.ok s,
        _ => Result.err "expected string",
    }

pub def Yaml.get_seq (y : Yaml) : Result String (List Yaml) :=
    match y {
        seq xs => Result.ok xs,
        _ => Result.err "expected sequence",
    }

pub def Yaml.get_mapping (y : Yaml) : Result String (BTreeMap String Yaml) :=
    match y {
        mapping m => Result.ok m,
        _ => Result.err "expected mapping",
    }

// ─── Core-schema scalar resolution ───

def Yaml.is_null_text (s : String) : Bool :=
    String.beq s "" || String.beq s "~" || String.beq s "null" ||
    String.beq s "Null" || String.beq s "NULL"

def Yaml.is_true_text (s : String) : Bool :=
    String.beq s "true" || String.beq s "True" || String.beq s "TRUE"

def Yaml.is_false_text (s : String) : Bool :=
    String.beq s "false" || String.beq s "False" || String.beq s "FALSE"

def Yaml.is_inf_text (s : String) : Bool :=
    String.beq s ".inf" || String.beq s ".Inf" || String.beq s ".INF"

def Yaml.is_neg_inf_text (s : String) : Bool :=
    String.beq s "-.inf" || String.beq s "-.Inf" || String.beq s "-.INF"

def Yaml.is_nan_text (s : String) : Bool :=
    String.beq s ".nan" || String.beq s ".NaN" || String.beq s ".NAN"

/// The core-schema non-finite spellings. These are a scalar-resolution
/// concern, not part of `Parse.f64`'s grammar.
pub def Yaml.special_float (s : String) : Option F64 :=
    if Yaml.is_inf_text s then Option.some (1.0f64 / 0.0f64)
    else if Yaml.is_neg_inf_text s then Option.some (0.0f64 - (1.0f64 / 0.0f64))
    else if Yaml.is_nan_text s then Option.some (0.0f64 / 0.0f64)
    else Option.none

/// A cheap prefilter: only a token containing `.` or an exponent marker can
/// be a float. `Parse.f64` is still the authority.
def Yaml.looks_floaty (s : String) : Bool :=
    String.contains s "." || String.contains s "e" || String.contains s "E"

def Yaml.resolve_float_or_str (s : String) : Yaml :=
    if Yaml.looks_floaty s
    then
        match Parse.f64 s {
            Option.some f => float f,
            Option.none => str s,
        }
    else str s

def Yaml.resolve_number_or_str (s : String) : Yaml :=
    match Parse.i64 s {
        Option.some i => int i,
        Option.none => Yaml.resolve_float_or_str s,
    }

/// Resolve a plain (unquoted) scalar the way the YAML 1.2 core schema does:
/// `null`/`~`/empty, the six boolean spellings, the non-finite float
/// spellings, a decimal integer, a decimal float, else a string.
pub def Yaml.resolve_plain_text (s : String) : Yaml :=
    if Yaml.is_null_text s then null
    else if Yaml.is_true_text s then bool true
    else if Yaml.is_false_text s then bool false
    else
        match Yaml.special_float s {
            Option.some f => float f,
            Option.none => Yaml.resolve_number_or_str s,
        }

// ─── Quoting ───

#[partial]
def Yaml.contains_byte (bs : List U8) (b : U8) : Bool :=
    match bs {
        List.empty => false,
        List.cons h rest => if U8.beq h b then true else Yaml.contains_byte rest b,
    }

#[partial]
def Yaml.has_control_byte (bs : List U8) : Bool :=
    match bs {
        List.empty => false,
        List.cons h rest =>
            if U8.lt h 32u8 then true
            else if U8.beq h 127u8 then true
            else Yaml.has_control_byte rest,
    }

/// Bytes that force quoting anywhere in the scalar: `:`, `#`, `,`, `[`, `]`,
/// `{`, `}`, and also `"` and `\`. The separators can be misread as
/// structure; the quote and backslash are quoted so they take the explicit
/// escape path rather than depending on a reader's plain-scalar rules.
/// Over-quoting is safe.
#[partial]
def Yaml.has_separator_byte (bs : List U8) : Bool :=
    match bs {
        List.empty => false,
        List.cons h rest =>
            if U8.beq h 58u8 then true
            else if U8.beq h 35u8 then true
            else if U8.beq h 44u8 then true
            else if U8.beq h 91u8 then true
            else if U8.beq h 93u8 then true
            else if U8.beq h 123u8 then true
            else if U8.beq h 125u8 then true
            else if U8.beq h 34u8 then true
            else if U8.beq h 92u8 then true
            else Yaml.has_separator_byte rest,
    }

def Yaml.space_byte (b : U8) : Bool :=
    U8.beq b 32u8 || U8.beq b 9u8

def Yaml.starts_or_ends_space (s : String) : Bool :=
    let n : I64 := String.length s in
    if I64.gt n 0i64
    then
        match String.get s 0 {
            Option.none => false,
            Option.some first =>
                match String.get s (I64.sub n 1i64) {
                    Option.none => false,
                    Option.some last => Yaml.space_byte first || Yaml.space_byte last,
                },
        }
    else false

/// `- ? : , [ ] { } # & * ! | > ' " % @ ``
def Yaml.starts_with_indicator (s : String) : Bool :=
    match String.get s 0 {
        Option.none => false,
        Option.some b =>
            U8.beq b 45u8 || U8.beq b 63u8 || U8.beq b 58u8 || U8.beq b 44u8 ||
            U8.beq b 91u8 || U8.beq b 93u8 || U8.beq b 123u8 || U8.beq b 125u8 ||
            U8.beq b 35u8 || U8.beq b 38u8 || U8.beq b 42u8 || U8.beq b 33u8 ||
            U8.beq b 124u8 || U8.beq b 62u8 || U8.beq b 39u8 || U8.beq b 34u8 ||
            U8.beq b 37u8 || U8.beq b 64u8 || U8.beq b 96u8,
    }

/// YAML 1.1 boolean spellings. This parser resolves them as STRINGS (the
/// 1.2 core schema), but quoting them keeps the output unambiguous to a 1.1
/// consumer.
def Yaml.is_legacy_bool (s : String) : Bool :=
    String.beq s "yes" || String.beq s "Yes" || String.beq s "YES" ||
    String.beq s "no" || String.beq s "No" || String.beq s "NO" ||
    String.beq s "on" || String.beq s "On" || String.beq s "ON" ||
    String.beq s "off" || String.beq s "Off" || String.beq s "OFF"

/// `0x`/`0o`/`0b` prefixes are an explicit parse error (not in the 1.2 core
/// schema), so an unquoted string of that shape would not survive a read.
pub def Yaml.unsupported_numeric (s : String) : Bool :=
    String.starts_with "0x" s || String.starts_with "0o" s || String.starts_with "0b" s

def Yaml.resolves_to_non_string (s : String) : Bool :=
    match Yaml.resolve_plain_text s {
        str _ => false,
        _ => true,
    }

pub def Yaml.needs_quotes (s : String) : Bool :=
    if String.is_empty s then true
    else if Yaml.has_control_byte (String.to_list s) then true
    else if Yaml.starts_or_ends_space s then true
    else if Yaml.has_separator_byte (String.to_list s) then true
    else if Yaml.starts_with_indicator s then true
    else if Yaml.is_legacy_bool s then true
    else if Yaml.unsupported_numeric s then true
    else Yaml.resolves_to_non_string s

// ─── String escaping ───

/// One hex digit as its ASCII byte (`10` -> `a`).
def Yaml.hex_byte (n : U8) : U8 :=
    if U8.lt n 10u8 then U8.add n 48u8 else U8.add n 87u8

/// Append `\u00XX` to a REVERSED byte accumulator. The accumulator is
/// reversed, so bytes are consed in forward order and the whole list is
/// reversed once at the end.
def Yaml.control_escape_acc (b : U8) (acc : List U8) : List U8 :=
    let hi : U8 := U8.div b 16u8 in
    let lo : U8 := U8.sub b (U8.mul hi 16u8) in
    let a1 : List U8 := List.cons 92u8 acc in
    let a2 : List U8 := List.cons 117u8 a1 in
    let a3 : List U8 := List.cons 48u8 a2 in
    let a4 : List U8 := List.cons 48u8 a3 in
    let a5 : List U8 := List.cons (Yaml.hex_byte hi) a4 in
    List.cons (Yaml.hex_byte lo) a5

/// Append the two bytes `x`, `y` to a REVERSED byte accumulator. In a
/// reversed accumulator the second byte is the OUTER `cons`: `[y, x] ++ acc`
/// reverses to `out ++ [x, y]`.
def Yaml.escape_two (x : U8) (y : U8) (acc : List U8) : List U8 :=
    List.cons y (List.cons x acc)

/// Escape `"`, `\`, the named controls, and every other byte below 0x20 or
/// 0x7F as `\u00XX`. Non-ASCII UTF-8 bytes pass through unchanged.
#[partial]
def Yaml.escape_bytes (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => List.reverse acc,
        List.cons b rest =>
            if U8.beq b 34u8 then Yaml.escape_bytes rest (Yaml.escape_two 92u8 34u8 acc)
            else if U8.beq b 92u8 then Yaml.escape_bytes rest (Yaml.escape_two 92u8 92u8 acc)
            else if U8.beq b 10u8 then Yaml.escape_bytes rest (Yaml.escape_two 92u8 110u8 acc)
            else if U8.beq b 9u8 then Yaml.escape_bytes rest (Yaml.escape_two 92u8 116u8 acc)
            else if U8.beq b 13u8 then Yaml.escape_bytes rest (Yaml.escape_two 92u8 114u8 acc)
            else if U8.beq b 8u8 then Yaml.escape_bytes rest (Yaml.escape_two 92u8 98u8 acc)
            else if U8.beq b 12u8 then Yaml.escape_bytes rest (Yaml.escape_two 92u8 102u8 acc)
            else if U8.lt b 32u8 then Yaml.escape_bytes rest (Yaml.control_escape_acc b acc)
            else if U8.beq b 127u8 then Yaml.escape_bytes rest (Yaml.control_escape_acc b acc)
            else Yaml.escape_bytes rest (List.cons b acc),
    }

pub def Yaml.escape_string (s : String) : String :=
    String.from_list (Yaml.escape_bytes (String.to_list s) List.empty)

pub def Yaml.quote_string (s : String) : String :=
    String.concat "\"" (String.concat (Yaml.escape_string s) "\"")

pub def Yaml.scalar_string (s : String) : String :=
    if Yaml.needs_quotes s then Yaml.quote_string s else s

// ─── Scalar rendering ───

def Yaml.bool_text (b : Bool) : String :=
    if b then "true" else "false"

pub def Yaml.pos_inf : F64 := 1.0f64 / 0.0f64
pub def Yaml.neg_inf : F64 := 0.0f64 - (1.0f64 / 0.0f64)

def Yaml.is_nan (f : F64) : Bool := Bool.not (F64.beq f f)

/// The exact inverse of `resolve_plain_text` for floats. `F64.to_string`
/// prints `3.0` as "3" and never uses exponent form; the `.0` suffix keeps
/// the reader from resolving it as an integer. Non-finite values use the
/// core-schema spellings, which `F64.to_string`'s "inf"/"NaN" are not.
pub def Yaml.float_to_string (f : F64) : String :=
    if Yaml.is_nan f then ".nan"
    else if F64.beq f Yaml.pos_inf then ".inf"
    else if F64.beq f Yaml.neg_inf then "-.inf"
    else
        let s : String := F64.to_string f in
        if String.contains s "." then s
        else if String.contains s "e" then s
        else if String.contains s "E" then s
        else String.concat s ".0"

pub def Yaml.scalar_inline (y : Yaml) : String :=
    match y {
        null => "null",
        bool b => Yaml.bool_text b,
        int i => I64.to_string i,
        float f => Yaml.float_to_string f,
        str s => Yaml.scalar_string s,
        seq _ => "",
        mapping _ => "",
    }

/// A value rendered on its own line when it is a scalar -- and `[]`/`{}`
/// for an EMPTY collection, which is inline but not a scalar.
pub def Yaml.value_inline (y : Yaml) : String :=
    match y {
        seq _ => "[]",
        mapping _ => "{}",
        _ => Yaml.scalar_inline y,
    }

// ─── Block printer ───

def Yaml.spaces (n : I64) : String :=
    String.repeat " " n

/// A mapping/sequence value is laid out on its own lines only when it has
/// content; an empty one is `{}`/`[]` inline.
def Yaml.is_block_value (y : Yaml) : Bool :=
    match y {
        seq xs => Bool.not (List.is_empty xs),
        mapping m => Bool.not (List.is_empty (BTreeMap.to_list m)),
        _ => false,
    }

#[partial]
pub def Yaml.render_lines (y : Yaml) (indent : I64) : List String :=
    match y {
        seq xs => Yaml.render_seq_lines xs indent,
        mapping m => Yaml.render_mapping_lines (BTreeMap.to_list m) indent,
        _ => List.cons (String.concat (Yaml.spaces indent) (Yaml.scalar_inline y)) List.empty,
    }

/// An EMPTY collection prints as one inline line. The non-empty path is a
/// separate walk so its terminal case is `List.empty`, not a second `{}` --
/// a single recursive function cannot distinguish "no entries" from "the
/// end of the entries".
#[partial]
def Yaml.render_mapping_lines (pairs : List (Pair String Yaml)) (indent : I64) : List String :=
    if List.is_empty pairs
    then List.cons (String.concat (Yaml.spaces indent) "{}") List.empty
    else Yaml.render_mapping_entries pairs indent

#[partial]
def Yaml.render_mapping_entries (pairs : List (Pair String Yaml)) (indent : I64) : List String :=
    match pairs {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair k v =>
                    let key_line : String :=
                        String.concat (Yaml.spaces indent) (String.concat (Yaml.scalar_string k) ":") in
                    let rest_lines : List String := Yaml.render_mapping_entries rest indent in
                    if Yaml.is_block_value v
                    then List.append (List.cons key_line (Yaml.render_lines v (I64.add indent 2))) rest_lines
                    else List.cons (String.concat key_line (String.concat " " (Yaml.value_inline v))) rest_lines,
            },
    }

/// The compact sequence form: the item's first rendered line follows `- `,
/// and its remaining lines keep the `indent + 2` layout.
#[partial]
def Yaml.render_seq_lines (xs : List Yaml) (indent : I64) : List String :=
    if List.is_empty xs
    then List.cons (String.concat (Yaml.spaces indent) "[]") List.empty
    else Yaml.render_seq_items xs indent

#[partial]
def Yaml.render_seq_items (xs : List Yaml) (indent : I64) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons x rest =>
            let item_lines : List String := Yaml.render_lines x (I64.add indent 2) in
            let rest_lines : List String := Yaml.render_seq_items rest indent in
            List.append (Yaml.dash_lines item_lines indent) rest_lines,
    }

def Yaml.dash_lines (lines : List String) (indent : I64) : List String :=
    match lines {
        List.empty => List.empty,
        List.cons first rest =>
            let content : String := String.drop (I64.add indent 2) first in
            List.cons (String.concat (Yaml.spaces indent) (String.concat "- " content)) rest,
    }

pub def Yaml.to_string (y : Yaml) : String :=
    List.intercalate "\n" (Yaml.render_lines y 0)

// ─── Flow printer ───

def Yaml.join_flow (ss : List String) : String :=
    List.intercalate ", " ss

#[partial]
def Yaml.pair_flow (p : Pair String Yaml) : String :=
    match p {
        Pair.pair k v =>
            String.concat (Yaml.scalar_string k) (String.concat ": " (Yaml.to_string_flow v)),
    }

#[partial]
pub def Yaml.to_string_flow (y : Yaml) : String :=
    match y {
        seq xs =>
            String.concat "[" (String.concat (Yaml.join_flow (List.map Yaml.to_string_flow xs)) "]"),
        mapping m =>
            String.concat "{" (String.concat (Yaml.join_flow (List.map Yaml.pair_flow (BTreeMap.to_list m))) "}"),
        _ => Yaml.scalar_inline y,
    }

// ─── Line splitting and scanning ───

/// Split on `\n`, dropping one trailing `\r` per line (CRLF). Built over
/// bytes so no slice can land mid-character.
#[partial]
def Yaml.split_lines_bytes (bs : List U8) (cur : List U8) (acc : List String) : List String :=
    match bs {
        List.empty =>
            List.reverse (List.cons (Yaml.drop_trailing_cr (String.from_list (List.reverse cur))) acc),
        List.cons b rest =>
            if U8.beq b 10u8
            then
                Yaml.split_lines_bytes rest List.empty
                    (List.cons (Yaml.drop_trailing_cr (String.from_list (List.reverse cur))) acc)
            else Yaml.split_lines_bytes rest (List.cons b cur) acc,
    }

def Yaml.drop_trailing_cr (s : String) : String :=
    let n : I64 := String.length s in
    if I64.gt n 0i64
    then
        match String.get s (I64.sub n 1i64) {
            Option.some b => if U8.beq b 13u8 then String.slice s 0 (I64.sub n 1i64) else s,
            Option.none => s,
        }
    else s

pub def Yaml.split_lines (s : String) : List String :=
    Yaml.split_lines_bytes (String.to_list s) List.empty List.empty

/// Count leading spaces. A tab in indentation is an error: YAML forbids it
/// precisely because tab width is ambiguous.
#[partial]
def Yaml.count_indent (raw : String) (i : I64) : Result String I64 :=
    match String.get raw i {
        Option.none => Result.ok i,
        Option.some b =>
            if U8.beq b 32u8 then Yaml.count_indent raw (I64.add i 1i64)
            else if U8.beq b 9u8 then Result.err "tab in indentation"
            else Result.ok i,
    }

#[partial]
def Yaml.lines_of_raw (raw_lines : List String) (number : I64) (acc : List Yaml.Line) : Result Yaml.ParseError (List Yaml.Line) :=
    match raw_lines {
        List.empty => Result.ok (List.reverse acc),
        List.cons raw rest =>
            match Yaml.count_indent raw 0i64 {
                Result.err msg => Result.err (Yaml.mk_error number 1i64 msg),
                Result.ok indent => Yaml.lines_of_raw_ok raw rest number indent acc,
            },
    }

#[partial]
def Yaml.lines_of_raw_ok (raw : String) (rest : List String) (number : I64) (indent : I64) (acc : List Yaml.Line) : Result Yaml.ParseError (List Yaml.Line) :=
    let text : String := String.drop indent raw in
    let l : Yaml.Line := Yaml.mk_line number indent text in
    Yaml.lines_of_raw rest (I64.add number 1i64) (List.cons l acc)

// ─── Comments and blank lines ───

/// Cut a line at the first `#` that starts a comment: one at the start of
/// the text or preceded by a space/tab, outside quotes. `\` inside double
/// quotes and `''` inside single quotes do not terminate the quote state.
#[partial]
def Yaml.strip_comment_go (s : String) (i : I64) (in_single : Bool) (in_double : Bool) (prev_ws : Bool) : String :=
    match String.get s i {
        Option.none => s,
        Option.some b =>
            if in_double
            then
                if U8.beq b 92u8
                then Yaml.strip_comment_go s (I64.add i 2i64) in_single true false
                else if U8.beq b 34u8
                then Yaml.strip_comment_go s (I64.add i 1i64) in_single false false
                else Yaml.strip_comment_go s (I64.add i 1i64) in_single true false
            else if in_single
            then
                if U8.beq b 39u8
                then Yaml.strip_comment_go s (I64.add i 1i64) false in_double false
                else Yaml.strip_comment_go s (I64.add i 1i64) true in_double false
            else if U8.beq b 34u8
            then Yaml.strip_comment_go s (I64.add i 1i64) false true false
            else if U8.beq b 39u8
            then Yaml.strip_comment_go s (I64.add i 1i64) true false false
            else if Bool.and (U8.beq b 35u8) prev_ws
            then String.slice s 0 i
            else Yaml.strip_comment_go s (I64.add i 1i64) false false (Yaml.space_byte b),
    }

pub def Yaml.strip_comment (s : String) : String :=
    Yaml.strip_comment_go s 0i64 false false true

def Yaml.line_trimmed (l : Yaml.Line) : String :=
    String.trim (Yaml.strip_comment l.text)

def Yaml.line_is_blank (l : Yaml.Line) : Bool :=
    String.is_empty (String.trim l.text)

def Yaml.line_is_ignorable (l : Yaml.Line) : Bool :=
    String.is_empty (Yaml.line_trimmed l)

#[partial]
def Yaml.skip_ignorable (lines : List Yaml.Line) : List Yaml.Line :=
    match lines {
        List.empty => List.empty,
        List.cons l rest =>
            if Yaml.line_is_ignorable l then Yaml.skip_ignorable rest else lines,
    }

// ─── Quoted scalars ───

#[partial]
def Yaml.single_close (s : String) (i : I64) (acc : List U8) : Result String Yaml.Quoted :=
    let q : Yaml.Quoted := {
        rest := String.drop (I64.add i 1i64) s,
        text := String.from_list (List.reverse acc),
    } in
    Result.ok q

#[partial]
def Yaml.scan_single (s : String) (i : I64) (acc : List U8) : Result String Yaml.Quoted :=
    match String.get s i {
        Option.none => Result.err "unterminated single-quoted scalar",
        Option.some b =>
            if U8.beq b 39u8
            then
                match String.get s (I64.add i 1i64) {
                    Option.some b2 =>
                        if U8.beq b2 39u8
                        then Yaml.scan_single s (I64.add i 2i64) (List.cons 39u8 acc)
                        else Yaml.single_close s i acc,
                    // A quote at the very end of the text is the CLOSING
                    // quote, not an unterminated scalar.
                    Option.none => Yaml.single_close s i acc,
                }
            else Yaml.scan_single s (I64.add i 1i64) (List.cons b acc),
    }

/// One hex digit's value, a comparison chain -- there is no `U8 -> I64`
/// conversion in the language.
def Yaml.hex_digit (b : U8) : Option I64 :=
    if U8.beq b 48u8 then Option.some 0i64
    else if U8.beq b 49u8 then Option.some 1i64
    else if U8.beq b 50u8 then Option.some 2i64
    else if U8.beq b 51u8 then Option.some 3i64
    else if U8.beq b 52u8 then Option.some 4i64
    else if U8.beq b 53u8 then Option.some 5i64
    else if U8.beq b 54u8 then Option.some 6i64
    else if U8.beq b 55u8 then Option.some 7i64
    else if U8.beq b 56u8 then Option.some 8i64
    else if U8.beq b 57u8 then Option.some 9i64
    else if U8.beq b 97u8 then Option.some 10i64
    else if U8.beq b 98u8 then Option.some 11i64
    else if U8.beq b 99u8 then Option.some 12i64
    else if U8.beq b 100u8 then Option.some 13i64
    else if U8.beq b 101u8 then Option.some 14i64
    else if U8.beq b 102u8 then Option.some 15i64
    else if U8.beq b 65u8 then Option.some 10i64
    else if U8.beq b 66u8 then Option.some 11i64
    else if U8.beq b 67u8 then Option.some 12i64
    else if U8.beq b 68u8 then Option.some 13i64
    else if U8.beq b 69u8 then Option.some 14i64
    else if U8.beq b 70u8 then Option.some 15i64
    else Option.none

#[partial]
def Yaml.hex4_from (s : String) (i : I64) (k : I64) (acc : I64) : Option I64 :=
    if I64.gt k 3i64
    then Option.some acc
    else
        match String.get s (I64.add i k) {
            Option.none => Option.none,
            Option.some b =>
                match Yaml.hex_digit b {
                    Option.none => Option.none,
                    Option.some n => Yaml.hex4_from s i (I64.add k 1i64) (I64.add (I64.mul acc 16i64) n),
                },
        }

def Yaml.hex4 (s : String) (i : I64) : Option I64 :=
    Yaml.hex4_from s i 0i64 0i64

def Yaml.byte_of (n : I64) : U8 :=
    U32.to_u8 (I64.to_u32 n)

/// `\uXXXX`: this reader decodes the ASCII range only, which is the only
/// range the printer ever emits (`\u00XX` for control bytes). Anything above
/// U+007F is an explicit error rather than a wrong byte.
#[partial]
def Yaml.scan_unicode (s : String) (i : I64) (acc : List U8) : Result String Yaml.Quoted :=
    match Yaml.hex4 s i {
        Option.none => Result.err "invalid \\u escape",
        Option.some v =>
            if I64.gt v 127i64
            then Result.err "\\u escape above U+007F is not supported"
            else Yaml.scan_double s (I64.add i 4i64) (List.cons (Yaml.byte_of v) acc),
    }

#[partial]
def Yaml.scan_escape (s : String) (i : I64) (acc : List U8) : Result String Yaml.Quoted :=
    match String.get s i {
        Option.none => Result.err "unterminated escape in a double-quoted scalar",
        Option.some b =>
            if U8.beq b 110u8 then Yaml.scan_double s (I64.add i 1i64) (List.cons 10u8 acc)
            else if U8.beq b 116u8 then Yaml.scan_double s (I64.add i 1i64) (List.cons 9u8 acc)
            else if U8.beq b 114u8 then Yaml.scan_double s (I64.add i 1i64) (List.cons 13u8 acc)
            else if U8.beq b 98u8 then Yaml.scan_double s (I64.add i 1i64) (List.cons 8u8 acc)
            else if U8.beq b 102u8 then Yaml.scan_double s (I64.add i 1i64) (List.cons 12u8 acc)
            else if U8.beq b 34u8 then Yaml.scan_double s (I64.add i 1i64) (List.cons 34u8 acc)
            else if U8.beq b 92u8 then Yaml.scan_double s (I64.add i 1i64) (List.cons 92u8 acc)
            else if U8.beq b 47u8 then Yaml.scan_double s (I64.add i 1i64) (List.cons 47u8 acc)
            else if U8.beq b 117u8 then Yaml.scan_unicode s (I64.add i 1i64) acc
            else Result.err "unsupported escape in a double-quoted scalar",
    }

#[partial]
def Yaml.scan_double (s : String) (i : I64) (acc : List U8) : Result String Yaml.Quoted :=
    match String.get s i {
        Option.none => Result.err "unterminated double-quoted scalar",
        Option.some b =>
            if U8.beq b 34u8
            then
                let q : Yaml.Quoted := {
                    rest := String.drop (I64.add i 1i64) s,
                    text := String.from_list (List.reverse acc),
                } in
                Result.ok q
            else if U8.beq b 92u8
            then Yaml.scan_escape s (I64.add i 1i64) acc
            else Yaml.scan_double s (I64.add i 1i64) (List.cons b acc),
    }

// ─── Inline (single-line) values ───

def Yaml.finish_quoted (r : Result String Yaml.Quoted) : Result String Yaml :=
    match r {
        Result.err e => Result.err e,
        Result.ok q =>
            if String.is_empty (String.trim q.rest)
            then Result.ok (Yaml.str q.text)
            else Result.err "unexpected text after a quoted scalar",
    }

def Yaml.finish_key (r : Result String Yaml.Quoted) : Result String String :=
    match r {
        Result.err e => Result.err e,
        Result.ok q =>
            if String.is_empty (String.trim q.rest)
            then Result.ok q.text
            else Result.err "unexpected text after a quoted key",
    }

/// A plain scalar that begins with a YAML construct this subset does not
/// implement: anchors (`&`), aliases (`*`), tags (`!`), directives (`%`),
/// reserved indicators (`@`, `` ` ``), and complex keys (`?` alone or `? `).
/// Rejecting them is the difference between "unsupported" and "silently
/// treated as text".
def Yaml.unsupported_indicator (text : String) : Bool :=
    match String.get text 0 {
        Option.none => false,
        Option.some b =>
            U8.beq b 38u8 || U8.beq b 42u8 || U8.beq b 33u8 || U8.beq b 37u8 ||
            U8.beq b 64u8 || U8.beq b 96u8 ||
            Bool.and (U8.beq b 63u8) (Bool.or (String.beq text "?") (String.starts_with "? " text)),
    }

/// A mapping value's text is already comment-stripped and trimmed. A leading
/// quote or bracket decides the grammar; everything else is a plain scalar.
#[partial]
def Yaml.parse_inline_text (text : String) : Result String Yaml :=
    match String.get text 0 {
        Option.none => Result.ok Yaml.make_null,
        Option.some b =>
            if Bool.or (U8.beq b 91u8) (U8.beq b 123u8)
            then Yaml.parse_flow_text text
            else if U8.beq b 39u8
            then Yaml.finish_quoted (Yaml.scan_single text 1i64 List.empty)
            else if U8.beq b 34u8
            then Yaml.finish_quoted (Yaml.scan_double text 1i64 List.empty)
            else if Yaml.unsupported_numeric text
            then Result.err "unsupported numeric spelling (0x/0o/0b)"
            else if Yaml.unsupported_indicator text
            then Result.err "unsupported YAML construct (anchor, alias, tag, directive, or complex key)"
            else Result.ok (Yaml.resolve_plain_text text),
    }

/// A mapping key is always a STRING here (mappings are `BTreeMap String
/// Yaml`); plain key text is used verbatim, quoted keys are unquoted.
#[partial]
def Yaml.key_of_text (text : String) : Result String String :=
    match String.get text 0 {
        Option.none => Result.err "empty key",
        Option.some b =>
            if U8.beq b 39u8
            then Yaml.finish_key (Yaml.scan_single text 1i64 List.empty)
            else if U8.beq b 34u8
            then Yaml.finish_key (Yaml.scan_double text 1i64 List.empty)
            else if Yaml.unsupported_indicator text
            then Result.err "unsupported YAML construct (anchor, alias, tag, directive, or complex key)"
            else Result.ok text,
    }

// ─── Flow collections ───

#[partial]
def Yaml.flow_skip_ws (s : String) : String :=
    match String.get s 0 {
        Option.none => s,
        Option.some b =>
            if Yaml.space_byte b
            then Yaml.flow_skip_ws (String.drop 1 s)
            else s,
    }

/// A plain flow scalar ends at `,`, `]`, `}`, or `#`.
#[partial]
def Yaml.flow_plain_from (s : String) (i : I64) : Yaml.Flow :=
    match String.get s i {
        Option.none => Yaml.mk_flow (String.drop i s) (Yaml.resolve_plain_text (String.trim (String.slice s 0 i))),
        Option.some b =>
            if U8.beq b 44u8 || U8.beq b 93u8 || U8.beq b 125u8 || U8.beq b 35u8
            then Yaml.mk_flow (String.drop i s) (Yaml.resolve_plain_text (String.trim (String.slice s 0 i)))
            else Yaml.flow_plain_from s (I64.add i 1i64),
    }

#[partial]
def Yaml.flow_plain (s : String) : Result String Yaml.Flow :=
    Result.ok (Yaml.flow_plain_from s 0i64)

#[partial]
def Yaml.flow_value (s : String) : Result String Yaml.Flow :=
    let t : String := Yaml.flow_skip_ws s in
    match String.get t 0 {
        Option.none => Result.err "expected a flow value",
        Option.some b =>
            if U8.beq b 91u8 then Yaml.flow_seq t
            else if U8.beq b 123u8 then Yaml.flow_map t
            else if U8.beq b 39u8 then Yaml.flow_single t
            else if U8.beq b 34u8 then Yaml.flow_double t
            else Yaml.flow_plain t,
    }

#[partial]
def Yaml.flow_single (s : String) : Result String Yaml.Flow :=
    match Yaml.scan_single s 1i64 List.empty {
        Result.err e => Result.err e,
        Result.ok q => Result.ok (Yaml.mk_flow q.rest (Yaml.str q.text)),
    }

#[partial]
def Yaml.flow_double (s : String) : Result String Yaml.Flow :=
    match Yaml.scan_double s 1i64 List.empty {
        Result.err e => Result.err e,
        Result.ok q => Result.ok (Yaml.mk_flow q.rest (Yaml.str q.text)),
    }

#[partial]
def Yaml.flow_seq (s : String) : Result String Yaml.Flow :=
    Yaml.flow_seq_items (String.drop 1 s) List.empty

#[partial]
def Yaml.flow_seq_items (s : String) (acc : List Yaml) : Result String Yaml.Flow :=
    let t : String := Yaml.flow_skip_ws s in
    match String.get t 0 {
        Option.none => Result.err "unterminated flow sequence",
        Option.some b =>
            if U8.beq b 93u8
            then Result.ok (Yaml.mk_flow (String.drop 1 t) (Yaml.make_seq (List.reverse acc)))
            else Yaml.flow_seq_value t acc,
    }

#[partial]
def Yaml.flow_seq_value (t : String) (acc : List Yaml) : Result String Yaml.Flow :=
    match Yaml.flow_value t {
        Result.err e => Result.err e,
        Result.ok f => Yaml.flow_seq_after f (List.cons f.value acc),
    }

#[partial]
def Yaml.flow_seq_after (f : Yaml.Flow) (acc : List Yaml) : Result String Yaml.Flow :=
    let t : String := Yaml.flow_skip_ws f.rest in
    match String.get t 0 {
        Option.none => Result.err "unterminated flow sequence",
        Option.some b =>
            if U8.beq b 44u8
            then Yaml.flow_seq_items (String.drop 1 t) acc
            else if U8.beq b 93u8
            then Result.ok (Yaml.mk_flow (String.drop 1 t) (Yaml.make_seq (List.reverse acc)))
            else Result.err "expected ',' or ']' in a flow sequence",
    }

/// A plain flow key ends at `:`, `,`, `}`, or `#`.
#[partial]
def Yaml.flow_plain_key (s : String) (i : I64) : Yaml.FlowKey :=
    match String.get s i {
        Option.none => Yaml.mk_key (String.drop i s) (String.trim (String.slice s 0 i)),
        Option.some b =>
            if U8.beq b 58u8 || U8.beq b 44u8 || U8.beq b 125u8 || U8.beq b 35u8
            then Yaml.mk_key (String.drop i s) (String.trim (String.slice s 0 i))
            else Yaml.flow_plain_key s (I64.add i 1i64),
    }

#[partial]
def Yaml.flow_key_text (s : String) : Result String Yaml.FlowKey :=
    let t : String := Yaml.flow_skip_ws s in
    match String.get t 0 {
        Option.none => Result.err "expected a flow mapping key",
        Option.some b =>
            if U8.beq b 39u8
            then Yaml.flow_key_single (Yaml.scan_single t 1i64 List.empty)
            else if U8.beq b 34u8
            then Yaml.flow_key_double (Yaml.scan_double t 1i64 List.empty)
            else Result.ok (Yaml.flow_plain_key t 0i64),
    }

def Yaml.flow_key_single (r : Result String Yaml.Quoted) : Result String Yaml.FlowKey :=
    match r {
        Result.err e => Result.err e,
        Result.ok q => Result.ok (Yaml.mk_key (String.trim q.rest) q.text),
    }

def Yaml.flow_key_double (r : Result String Yaml.Quoted) : Result String Yaml.FlowKey :=
    match r {
        Result.err e => Result.err e,
        Result.ok q => Result.ok (Yaml.mk_key (String.trim q.rest) q.text),
    }

#[partial]
def Yaml.flow_map (s : String) : Result String Yaml.Flow :=
    Yaml.flow_map_items (String.drop 1 s) BTreeMap.empty

#[partial]
def Yaml.flow_map_items (s : String) (acc : BTreeMap String Yaml) : Result String Yaml.Flow :=
    let t : String := Yaml.flow_skip_ws s in
    match String.get t 0 {
        Option.none => Result.err "unterminated flow mapping",
        Option.some b =>
            if U8.beq b 125u8
            then Result.ok (Yaml.mk_flow (String.drop 1 t) (Yaml.make_mapping acc))
            else Yaml.flow_map_member t acc,
    }

#[partial]
def Yaml.flow_map_member (t : String) (acc : BTreeMap String Yaml) : Result String Yaml.Flow :=
    match Yaml.flow_key_text t {
        Result.err e => Result.err e,
        Result.ok k => Yaml.flow_map_after_key k acc,
    }

#[partial]
def Yaml.flow_map_after_key (k : Yaml.FlowKey) (acc : BTreeMap String Yaml) : Result String Yaml.Flow :=
    let after_colon : String := Yaml.flow_skip_ws k.rest in
    match String.get after_colon 0 {
        Option.none => Result.err "expected ':' in a flow mapping",
        Option.some b =>
            if U8.beq b 58u8
            then Yaml.flow_map_value (String.drop 1 after_colon) k.key acc
            else Result.err "expected ':' in a flow mapping",
    }

#[partial]
def Yaml.flow_map_value (s : String) (key : String) (acc : BTreeMap String Yaml) : Result String Yaml.Flow :=
    match Map.lookup key acc {
        Option.some _ => Result.err (String.concat "duplicate key: " key),
        Option.none => Yaml.flow_map_value_fresh s key acc,
    }

#[partial]
def Yaml.flow_map_value_fresh (s : String) (key : String) (acc : BTreeMap String Yaml) : Result String Yaml.Flow :=
    match Yaml.flow_value s {
        Result.err e => Result.err e,
        Result.ok f => Yaml.flow_map_after_value f (Map.insert key f.value acc),
    }

#[partial]
def Yaml.flow_map_after_value (f : Yaml.Flow) (acc : BTreeMap String Yaml) : Result String Yaml.Flow :=
    let t : String := Yaml.flow_skip_ws f.rest in
    match String.get t 0 {
        Option.none => Result.err "unterminated flow mapping",
        Option.some b =>
            if U8.beq b 44u8
            then Yaml.flow_map_items (String.drop 1 t) acc
            else if U8.beq b 125u8
            then Result.ok (Yaml.mk_flow (String.drop 1 t) (Yaml.make_mapping acc))
            else Result.err "expected ',' or '}' in a flow mapping",
    }

#[partial]
def Yaml.parse_flow_text (text : String) : Result String Yaml :=
    match Yaml.flow_value text {
        Result.err e => Result.err e,
        Result.ok f =>
            if String.is_empty (String.trim f.rest)
            then Result.ok f.value
            else Result.err "unexpected text after a flow collection",
    }

// ─── Block structure ───

def Yaml.is_seq_indicator (text : String) : Bool :=
    String.beq text "-" || String.starts_with "- " text

/// A block scalar header is `|` or `>`, optionally followed by `-`/`+`.
def Yaml.is_block_header (text : String) : Bool :=
    match String.get text 0 {
        Option.none => false,
        Option.some b => Bool.or (U8.beq b 124u8) (U8.beq b 62u8),
    }

def Yaml.block_header_rest (s : String) (folded : Bool) : Result String Yaml.BlockHeader :=
    let rest : String := String.drop 1 s in
    if String.is_empty rest
    then Result.ok (Yaml.mk_header folded y_clip)
    else if String.beq rest "-" then Result.ok (Yaml.mk_header folded y_strip)
    else if String.beq rest "+" then Result.ok (Yaml.mk_header folded y_keep)
    else Result.err "unsupported block scalar header (only |, > and -/+ chomping)"

#[partial]
def Yaml.parse_block_header (text : String) : Result String Yaml.BlockHeader :=
    match String.get text 0 {
        Option.none => Result.err "expected a block scalar header",
        Option.some b =>
            if U8.beq b 124u8 then Yaml.block_header_rest text false
            else if U8.beq b 62u8 then Yaml.block_header_rest text true
            else Result.err "expected a block scalar header",
    }

/// A `:` that separates a mapping key from its value: followed by a space,
/// a tab, or end of text -- and not inside a quote or a flow collection.
#[partial]
def Yaml.find_colon_go (s : String) (i : I64) (in_single : Bool) (in_double : Bool) (depth : I64) : Option I64 :=
    match String.get s i {
        Option.none => Option.none,
        Option.some b =>
            if in_double
            then
                if U8.beq b 92u8
                then Yaml.find_colon_go s (I64.add i 2i64) in_single true depth
                else if U8.beq b 34u8
                then Yaml.find_colon_go s (I64.add i 1i64) in_single false depth
                else Yaml.find_colon_go s (I64.add i 1i64) in_single true depth
            else if in_single
            then
                if U8.beq b 39u8
                then Yaml.find_colon_go s (I64.add i 1i64) false in_double depth
                else Yaml.find_colon_go s (I64.add i 1i64) true in_double depth
            else if U8.beq b 34u8
            then Yaml.find_colon_go s (I64.add i 1i64) false true depth
            else if U8.beq b 39u8
            then Yaml.find_colon_go s (I64.add i 1i64) true false depth
            else if U8.beq b 91u8 || U8.beq b 123u8
            then Yaml.find_colon_go s (I64.add i 1i64) in_single in_double (I64.add depth 1i64)
            else if U8.beq b 93u8 || U8.beq b 125u8
            then Yaml.find_colon_go s (I64.add i 1i64) in_single in_double (I64.sub depth 1i64)
            else if Bool.and (I64.beq depth 0i64) (U8.beq b 58u8)
            then
                if Yaml.colon_is_mapping_indicator s i
                then Option.some i
                else Yaml.find_colon_go s (I64.add i 1i64) in_single in_double depth
            else Yaml.find_colon_go s (I64.add i 1i64) in_single in_double depth,
    }

def Yaml.colon_is_mapping_indicator (s : String) (i : I64) : Bool :=
    match String.get s (I64.add i 1i64) {
        Option.none => true,
        Option.some b => Yaml.space_byte b,
    }

pub def Yaml.find_mapping_colon (s : String) : Option I64 :=
    Yaml.find_colon_go s 0i64 false false 0i64

// ─── Block scalars ───

#[partial]
def Yaml.find_content_indent (lines : List Yaml.Line) (parent_indent : I64) : I64 :=
    match lines {
        List.empty => I64.add parent_indent 1i64,
        List.cons l rest =>
            if Yaml.line_is_blank l
            then Yaml.find_content_indent rest parent_indent
            else if I64.gt l.indent parent_indent
            then l.indent
            else I64.add parent_indent 1i64,
    }

def Yaml.block_line_text (l : Yaml.Line) (content_indent : I64) : String :=
    String.concat (Yaml.spaces (I64.sub l.indent content_indent)) l.text

#[partial]
def Yaml.take_block_body (lines : List Yaml.Line) (parent_indent : I64) (content_indent : I64) (acc : List String) : Result String Yaml.BlockBody :=
    match lines {
        List.empty => Result.ok (Yaml.mk_block_body List.empty (List.reverse acc)),
        List.cons l rest =>
            if Yaml.line_is_blank l
            then Yaml.take_block_body rest parent_indent content_indent (List.cons "" acc)
            else if I64.gt l.indent parent_indent
            then
                if I64.lt l.indent content_indent
                then Result.err "block scalar line is less indented than its first content line"
                else Yaml.take_block_body rest parent_indent content_indent (List.cons (Yaml.block_line_text l content_indent) acc)
            else Result.ok (Yaml.mk_block_body lines (List.reverse acc)),
    }

#[partial]
def Yaml.drop_trailing_newlines (s : String) : String :=
    let n : I64 := String.length s in
    if I64.gt n 0i64
    then
        match String.get s (I64.sub n 1i64) {
            Option.some b =>
                if U8.beq b 10u8
                then Yaml.drop_trailing_newlines (String.slice s 0 (I64.sub n 1i64))
                else s,
            Option.none => s,
        }
    else s

/// Fold `>` lines: adjacent non-blank lines join with a space, each blank
/// line becomes a newline. A more-indented line is an explicit error (full
/// folding rules are out of scope).
#[partial]
def Yaml.fold_lines (lines : List String) (prev_text : Bool) (acc : String) : Result String String :=
    match lines {
        List.empty => Result.ok acc,
        List.cons line rest =>
            if String.is_empty line
            then Yaml.fold_lines rest false (String.concat acc "\n")
            else if String.starts_with " " line
            then Result.err "a more-indented line inside a folded block is not supported"
            else if prev_text
            then Yaml.fold_lines rest true (String.concat (String.concat acc " ") line)
            else Yaml.fold_lines rest true (String.concat acc line),
    }

def Yaml.apply_chomp (body : String) (chomp : Yaml.Chomp) : String :=
    if String.is_empty body
    then ""
    else
        match chomp {
            y_strip => Yaml.drop_trailing_newlines body,
            y_clip => String.concat (Yaml.drop_trailing_newlines body) "\n",
            // The assembled body already carries every trailing newline the
            // source had: the line splitter keeps a final empty segment when
            // the input ends with `\n`, and `fold_lines` turns blank lines
            // into newlines. Appending one here would add a newline the
            // source never contained.
            y_keep => body,
        }

def Yaml.assemble_block (lines : List String) (folded : Bool) (chomp : Yaml.Chomp) : Result String String :=
    let body : String :=
        if folded
        then ""
        else List.intercalate "\n" lines in
    if folded
    then
        match Yaml.fold_lines lines false "" {
            Result.err e => Result.err e,
            Result.ok folded_body => Result.ok (Yaml.apply_chomp folded_body chomp),
        }
    else Result.ok (Yaml.apply_chomp body chomp)

#[partial]
def Yaml.consume_block_scalar (l : Yaml.Line) (rest : List Yaml.Line) (parent_indent : I64) (header : Yaml.BlockHeader) : Yaml.Parsed Yaml :=
    let content_indent : I64 := Yaml.find_content_indent rest parent_indent in
    match Yaml.take_block_body rest parent_indent content_indent List.empty {
        Result.err msg => y_err (Yaml.mk_error l.number (I64.add l.indent 1i64) msg),
        Result.ok body => Yaml.assemble_consumed l header body,
    }

#[partial]
def Yaml.assemble_consumed (l : Yaml.Line) (header : Yaml.BlockHeader) (body : Yaml.BlockBody) : Yaml.Parsed Yaml :=
    match Yaml.assemble_block body.lines header.folded header.chomp {
        Result.err msg => y_err (Yaml.mk_error l.number (I64.add l.indent 1i64) msg),
        Result.ok text => y_ok body.rest (Yaml.str text),
    }

// ─── Block parsing ───

#[partial]
def Yaml.parse_inline_line (l : Yaml.Line) (rest : List Yaml.Line) : Yaml.Parsed Yaml :=
    match Yaml.parse_inline_text (Yaml.line_trimmed l) {
        Result.err msg => y_err (Yaml.mk_error l.number (I64.add l.indent 1i64) msg),
        Result.ok v => y_ok rest v,
    }

/// Parse a nested block whose lines must be deeper than `parent_indent`.
/// An empty mapping value additionally allows an INDENTLESS sequence, at
/// exactly `parent_indent` -- `key:` followed by `- a` is valid YAML.
#[partial]
def Yaml.parse_nested_block (lines : List Yaml.Line) (parent_indent : I64) (allow_indentless_seq : Bool) : Yaml.Parsed Yaml :=
    match Yaml.skip_ignorable lines {
        List.empty => y_ok List.empty Yaml.make_null,
        List.cons l rest =>
            if I64.gt l.indent parent_indent
            then Yaml.parse_block (List.cons l rest)
            else if Bool.and allow_indentless_seq (Bool.and (I64.beq l.indent parent_indent) (Yaml.is_seq_indicator l.text))
            then Yaml.parse_sequence (List.cons l rest) l.indent
            else y_ok (List.cons l rest) Yaml.make_null,
    }

#[partial]
def Yaml.parse_block (lines : List Yaml.Line) : Yaml.Parsed Yaml :=
    match Yaml.skip_ignorable lines {
        List.empty => y_ok List.empty Yaml.make_null,
        List.cons l rest =>
            if Yaml.is_seq_indicator l.text
            then Yaml.parse_sequence (List.cons l rest) l.indent
            else
                match Yaml.find_mapping_colon (Yaml.line_trimmed l) {
                    Option.some _ => Yaml.parse_mapping (List.cons l rest) l.indent,
                    Option.none => Yaml.parse_inline_line l rest,
                },
    }

#[partial]
def Yaml.parse_mapping (lines : List Yaml.Line) (indent : I64) : Yaml.Parsed Yaml :=
    Yaml.parse_mapping_entries lines indent BTreeMap.empty

#[partial]
def Yaml.parse_mapping_entries (lines : List Yaml.Line) (indent : I64) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    match lines {
        List.empty => y_ok List.empty (Yaml.make_mapping acc),
        List.cons l rest =>
            if Yaml.line_is_ignorable l
            then Yaml.parse_mapping_entries rest indent acc
            else if Bool.not (I64.beq l.indent indent)
            then y_ok lines (Yaml.make_mapping acc)
            else Yaml.parse_mapping_entry l rest indent acc,
    }

#[partial]
def Yaml.parse_mapping_entry (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    let stripped : String := Yaml.line_trimmed l in
    match Yaml.find_mapping_colon stripped {
        Option.none => y_ok (List.cons l rest) (Yaml.make_mapping acc),
        Option.some pos =>
            let key_text : String := String.trim (String.slice stripped 0 pos) in
            let value_text : String := String.trim (String.drop (I64.add pos 1i64) stripped) in
            Yaml.mapping_key l rest indent key_text value_text acc,
    }

#[partial]
def Yaml.mapping_key (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (key_text : String) (value_text : String) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    match Yaml.key_of_text key_text {
        Result.err msg => y_err (Yaml.mk_error l.number (I64.add l.indent 1i64) msg),
        Result.ok key => Yaml.mapping_with_key l rest indent key value_text acc,
    }

#[partial]
def Yaml.mapping_with_key (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (key : String) (value_text : String) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    match Map.lookup key acc {
        Option.some _ => y_err (Yaml.mk_error l.number (I64.add l.indent 1i64) (String.concat "duplicate key: " key)),
        Option.none =>
            if String.is_empty value_text
            then Yaml.mapping_nested l rest indent key acc
            else if Yaml.is_block_header value_text
            then Yaml.mapping_block_scalar l rest indent key value_text acc
            else Yaml.mapping_inline l rest indent key value_text acc,
    }

#[partial]
def Yaml.mapping_nested (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (key : String) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    match Yaml.parse_nested_block rest indent true {
        y_err e => y_err e,
        y_ok remaining v => Yaml.mapping_continue remaining indent key v acc,
    }

#[partial]
def Yaml.mapping_block_scalar (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (key : String) (value_text : String) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    match Yaml.parse_block_header value_text {
        Result.err msg => y_err (Yaml.mk_error l.number (I64.add l.indent 1i64) msg),
        Result.ok header => Yaml.mapping_block_with_header l rest indent key header acc,
    }

#[partial]
def Yaml.mapping_block_with_header (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (key : String) (header : Yaml.BlockHeader) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    match Yaml.consume_block_scalar l rest indent header {
        y_err e => y_err e,
        y_ok remaining v => Yaml.mapping_continue remaining indent key v acc,
    }

#[partial]
def Yaml.mapping_inline (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (key : String) (value_text : String) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    match Yaml.parse_inline_text value_text {
        Result.err msg => y_err (Yaml.mk_error l.number (I64.add l.indent 1i64) msg),
        Result.ok v => Yaml.mapping_continue rest indent key v acc,
    }

#[partial]
def Yaml.mapping_continue (remaining : List Yaml.Line) (indent : I64) (key : String) (v : Yaml) (acc : BTreeMap String Yaml) : Yaml.Parsed Yaml :=
    Yaml.parse_mapping_entries remaining indent (Map.insert key v acc)

#[partial]
def Yaml.parse_sequence (lines : List Yaml.Line) (indent : I64) : Yaml.Parsed Yaml :=
    Yaml.parse_sequence_items lines indent List.empty

#[partial]
def Yaml.parse_sequence_items (lines : List Yaml.Line) (indent : I64) (acc : List Yaml) : Yaml.Parsed Yaml :=
    match lines {
        List.empty => y_ok List.empty (Yaml.make_seq (List.reverse acc)),
        List.cons l rest =>
            if Yaml.line_is_ignorable l
            then Yaml.parse_sequence_items rest indent acc
            else if Bool.and (I64.beq l.indent indent) (Yaml.is_seq_indicator l.text)
            then Yaml.parse_sequence_item l rest indent acc
            else y_ok lines (Yaml.make_seq (List.reverse acc)),
    }

#[partial]
def Yaml.parse_sequence_item (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (acc : List Yaml) : Yaml.Parsed Yaml :=
    let text : String := String.trim (Yaml.strip_comment l.text) in
    if String.beq text "-"
    then Yaml.sequence_bare l rest indent acc
    else
        let content : String := String.trim (String.drop 2 text) in
        if Yaml.is_block_header content
        then Yaml.sequence_block_scalar l rest indent content acc
        else Yaml.sequence_synthetic l rest indent content acc

#[partial]
def Yaml.sequence_bare (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (acc : List Yaml) : Yaml.Parsed Yaml :=
    match Yaml.parse_nested_block rest indent false {
        y_err e => y_err e,
        y_ok remaining v => Yaml.parse_sequence_items remaining indent (List.cons v acc),
    }

#[partial]
def Yaml.sequence_block_scalar (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (content : String) (acc : List Yaml) : Yaml.Parsed Yaml :=
    match Yaml.parse_block_header content {
        Result.err msg => y_err (Yaml.mk_error l.number (I64.add l.indent 3i64) msg),
        Result.ok header => Yaml.sequence_block_with_header l rest indent header acc,
    }

#[partial]
def Yaml.sequence_block_with_header (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (header : Yaml.BlockHeader) (acc : List Yaml) : Yaml.Parsed Yaml :=
    match Yaml.consume_block_scalar l rest indent header {
        y_err e => y_err e,
        y_ok remaining v => Yaml.parse_sequence_items remaining indent (List.cons v acc),
    }

/// `- key: value` (or any non-empty item) is re-parsed as a block whose
/// first line is the remainder at the item's virtual indent, so the mapping
/// and sequence parsers are reused rather than duplicated.
#[partial]
def Yaml.sequence_synthetic (l : Yaml.Line) (rest : List Yaml.Line) (indent : I64) (content : String) (acc : List Yaml) : Yaml.Parsed Yaml :=
    let synthetic : Yaml.Line := Yaml.mk_line l.number (I64.add indent 2i64) content in
    match Yaml.parse_block (List.cons synthetic rest) {
        y_err e => y_err e,
        y_ok remaining v => Yaml.parse_sequence_items remaining indent (List.cons v acc),
    }

// ─── Document ───

def Yaml.is_doc_start (text : String) : Bool := String.beq text "---"
def Yaml.is_doc_end (text : String) : Bool := String.beq text "..."

#[partial]
def Yaml.finish_after_end (rest : List Yaml.Line) (v : Yaml) : Result Yaml.ParseError Yaml :=
    match rest {
        List.empty => Result.ok v,
        List.cons l _ => Result.err (Yaml.mk_error l.number 1i64 "unexpected content after '...'"),
    }

#[partial]
def Yaml.finish_document (rest : List Yaml.Line) (v : Yaml) : Result Yaml.ParseError Yaml :=
    match Yaml.skip_ignorable rest {
        List.empty => Result.ok v,
        List.cons l trailing =>
            let text : String := Yaml.line_trimmed l in
            if Yaml.is_doc_end text
            then Yaml.finish_after_end (Yaml.skip_ignorable trailing) v
            else if Yaml.is_doc_start text
            then Result.err (Yaml.mk_error l.number 1i64 "multiple documents are not supported")
            else Result.err (Yaml.mk_error l.number 1i64 "unexpected content after the document value"),
    }

#[partial]
def Yaml.parse_root (lines : List Yaml.Line) : Result Yaml.ParseError Yaml :=
    match Yaml.parse_block lines {
        y_err e => Result.err e,
        y_ok rest v => Yaml.finish_document rest v,
    }

#[partial]
def Yaml.check_doc_leader (l : Yaml.Line) : Result String Bool :=
    let text : String := Yaml.line_trimmed l in
    if String.starts_with "%" text
    then Result.err "directives are not supported"
    else if String.starts_with "---" text
    then
        if Yaml.is_doc_start text
        then Result.ok true
        else Result.err "a document start marker must stand alone"
    else if String.starts_with "..." text
    then
        if Yaml.is_doc_end text
        then Result.ok false
        else Result.err "a document end marker must stand alone"
    else Result.ok false

#[partial]
def Yaml.parse_document (lines : List Yaml.Line) : Result Yaml.ParseError Yaml :=
    match Yaml.skip_ignorable lines {
        List.empty => Result.ok Yaml.make_null,
        List.cons l rest =>
            match Yaml.check_doc_leader l {
                Result.err msg => Result.err (Yaml.mk_error l.number 1i64 msg),
                Result.ok started =>
                    if started then Yaml.parse_body rest else Yaml.parse_body (List.cons l rest),
            },
    }

#[partial]
def Yaml.parse_body (lines : List Yaml.Line) : Result Yaml.ParseError Yaml :=
    match Yaml.skip_ignorable lines {
        List.empty => Result.ok Yaml.make_null,
        List.cons l rest =>
            let text : String := Yaml.line_trimmed l in
            if Yaml.is_doc_end text
            then Yaml.finish_after_end (Yaml.skip_ignorable rest) Yaml.make_null
            else if Yaml.is_doc_start text || String.starts_with "%" text || String.starts_with "---" text
            then Result.err (Yaml.mk_error l.number 1i64 "multiple documents are not supported")
            else Yaml.parse_root (List.cons l rest),
    }

/// Parse one YAML document. An empty or comments-only document is `null`.
/// Anything this subset does not support is an ERROR, never a guess.
#[partial]
pub def Yaml.parse (s : String) : Result Yaml.ParseError Yaml :=
    match Yaml.lines_of_raw (Yaml.split_lines s) 1i64 List.empty {
        Result.err e => Result.err e,
        Result.ok lines => Yaml.parse_document lines,
    }

// ─── Show ───

pub instance Show Yaml {
    def show (y : Yaml) : String := Yaml.to_string y
}
