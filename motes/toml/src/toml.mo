/// TOML 1.0.0 parsing and serialization (the full grammar).
/// Structurally independent from lang/json.mo — no shared Serialize/Deserialize
/// classes (Phase 7 of the JSON plan was deliberately deferred; see
/// plans/bootstrapping/json-parser-serializer-plan.md). Own string-escape helpers,
/// own hand-rolled beq family. `intercalate`/`concat_list` come from
/// `std/list.mo`'s `List.intercalate` and `init/string.mo`'s `String.concat_all`,
/// which is safe because there is exactly one definition of each corpus-wide.
/// Supported grammar: the whole of TOML 1.0.0 — [table] and [[array.of.tables]]
/// headers with dotted and quoted keys, `key = value` with dotted and quoted
/// keys, basic and literal strings (single-line and multi-line, with the full
/// escape set including \uXXXX and \UXXXXXXXX), integers (decimal with `_`
/// grouping, 0x/0o/0b), floats (fractions, exponents, inf/nan), date-times
/// (offset, local date-time, local date and local time, preserved verbatim),
/// booleans, arrays (multi-line, nested, trailing commas) and inline tables
/// (dotted keys, nesting). Every "defined more than once" rule the spec states
/// is REPORTED as an error rather than silently misparsed, and a `#` inside a
/// quoted string is ordinary text — comment stripping happens at the line
/// level, after the value parser has consumed its string, never as a pre-pass
/// over the raw source.
/// Deliberate divergences from the spec, all documented here:
///   * a date-time's VALUE is its exact source spelling (a `String`), not a
///     normalized `Datetime` — it round-trips verbatim, which is what a config
///     reader needs; the spelling is validated on the way in;
///   * comment CONTENTS are not control-character-validated (a comment cannot
///     misparse structure, so a stray control byte in one is tolerated);
///   * inside an inline table, a dotted key may extend a table-valued key even
///     when that table was written as a nested inline table (`{a = {x = 1},
///     a.y = 2}`); the spec calls the latter an error, and the parsed `Value`
///     carries no kind information to tell the two apart;
///   * CRLF inside a multi-line string is normalized to LF (the toml-testsuite
///     direction).
// NOTE: a blank `///` line in this leading module doc-comment (used as a paragraph
// break) was found to break the following `use` imports entirely — every symbol
// they bring in resolves as "unbound variable" throughout the rest of the file, a
// previously-undocumented parser/module-loader bug. Worked around by keeping this
// header as one unbroken `///` block with no blank `///` lines; a genuinely blank
// (comment-free) line, like the one separating this NOTE from the header above, is
// fine. Confirmed via a minimal repro; worth fixing upstream in the parser.

// `BTreeMap`/`beq`/`empty`/`map`/`to_list` are all used throughout this
// file and are listed here like any other import; see std/map_tests.mo's
// note for the instance/dictionary-resolution claim that used to keep
// this import empty, and for why it no longer does.
use std::map {Map, BTreeMap, BTreeMap.to_list, empty}
use std::list {List.filter, List.intercalate, Show}
use std::parse {Parse.f64}
use init::string {}
use init::number {}
use parsec::core {
    ParseError, ParseResult, is_empty, parse_error_remaining
}
use parsec::char_preds {is_ident_char}
use parsec::combinators {
    alt, alt_fold, delimited_by, many0, map_parse, separated_by, tag, take_while,
    utf8_char_width,
}

open ParseResult {fail, success}
open Toml.Value {array, boolean, datetime, float, integer, string, table}
open Toml.Line {header, array_header, kv}
open Toml.PathStep {step_key, step_last}
open Toml.TableKind {kind_implicit, kind_explicit, kind_dotted, kind_inline}
open Toml.Doc {doc_table, doc_array, doc_scalar}
open Toml.Asm {asm_state, asm_error}

// ─── Types ───

/// TOML value type. `datetime` carries its exact source spelling: it
/// round-trips verbatim and is validated by the parser (see the module
/// header for why there is no normalized `Datetime`).
pub type Toml.Value {
    string (s : String),
    integer (n : I64),
    float (f : F64),
    boolean (b : Bool),
    datetime (s : String),
    array (a : List Toml.Value),
    table (t : BTreeMap String Toml.Value),
}

// NOTE: equality is hand-rolled (Toml.array_beq / Toml.table_beq) rather than via
// the generic `[BEq A] BEq (List A)` / `BEq (Option A)` instances and `==` — those
// don't dispatch correctly to a custom A's BEq instance at runtime (see the same
// note in lang/json.mo's Json.array_beq). Concrete BEq instances (I64/String/Bool)
// used below are fine. A NaN never equals itself here either — that is IEEE's own
// answer, and the round-trip tests compare nan by its RENDERING for that reason.
def Toml.beq (a b : Toml.Value) : Bool :=
    match a {
        string sa => match b { string sb => sa == sb, _ => false },
        integer na => match b { integer nb => na == nb, _ => false },
        float fa => match b { float fb => fa == fb, _ => false },
        boolean ba => match b { boolean bb => ba == bb, _ => false },
        datetime da => match b { datetime db => da == db, _ => false },
        array aa => match b { array ab => Toml.array_beq aa ab, _ => false },
        table ta => match b { table tb => Toml.table_beq ta tb, _ => false },
    }

#[partial]
def Toml.array_beq (a b : List Toml.Value) : Bool :=
    match a {
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false
        },
        List.cons xa ta => match b {
            List.empty => false,
            List.cons xb tb => Toml.beq xa xb && Toml.array_beq ta tb
        }
    }

def Toml.pair_beq (a b : Pair String Toml.Value) : Bool :=
    match a {
        Pair.pair ka va => match b {
            Pair.pair kb vb => String.beq ka kb && Toml.beq va vb
        }
    }

#[partial]
def Toml.pairs_beq (a b : List (Pair String Toml.Value)) : Bool :=
    match a {
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false
        },
        List.cons pa ta => match b {
            List.empty => false,
            List.cons pb tb => Toml.pair_beq pa pb && Toml.pairs_beq ta tb
        }
    }

#[partial]
def Toml.table_beq (a b : BTreeMap String Toml.Value) : Bool :=
    Toml.pairs_beq (BTreeMap.to_list a) (BTreeMap.to_list b)

pub instance BEq Toml.Value {
    def beq (a b : Toml.Value) : Bool := Toml.beq a b
}

pub instance BEq (BTreeMap String Toml.Value) {
    def beq (a b : BTreeMap String Toml.Value) : Bool := Toml.table_beq a b
}

/// TOML ParseError type
pub type Toml.ParseError {
    expected (e : String) (found : String),
    generic String,
}

/// The error as one line of text, for a caller's own diagnostic.
pub def Toml.ParseError.to_string (e : Toml.ParseError) : String :=
    match e {
        expected e f => "expected: " ++ e ++ " found: " ++ f,
        generic s => s
    }

/// Convert core ParseError to Toml.ParseError
def Toml.from_parse_error (e : ParseError) : Toml.ParseError :=
    match e {
        tag s _rem => Toml.ParseError.expected s "",
        custom s _rem => Toml.ParseError.generic s
    }

/// One assembled document line: a `[table]`/`[a.b.c]` header, an
/// `[[array.of.tables]]` header, or a `key = value` pair — headers and keys
/// as dotted paths (quoted segments already unquoted). Not the public API —
/// consumed by Toml.assemble.
type Toml.Line {
    header (path : List String),
    array_header (path : List String),
    kv (path : List String) (value : Toml.Value),
}

/// One step of the path addressing the table a header established — the
/// assembler's "current table". `step_last` names the LAST element of an
/// array of tables, which is where every `kv` after an `[[x]]` header goes.
type Toml.PathStep {
    step_key (k : String),
    step_last (k : String),
}

/// How a table came to exist. Every "defined more than once" rule in the
/// spec keys off this distinction, which is why the assembler carries a
/// kinded tree instead of inserting straight into `Toml.Value`s:
///   * `kind_implicit` — created as an intermediate of a HEADER path
///     (`[a.b]` creates `a`); a later header may promote or pass through it;
///   * `kind_explicit` — established by a header (or promoted); a second
///     header at the same path is the spec's "defined more than once";
///   * `kind_dotted` — created as an intermediate of a dotted KEY
///     (`a.b = 1` creates `a`); only other dotted keys may extend it;
///   * `kind_inline` — written as an inline table; immutable, per the spec.
type Toml.TableKind {
    kind_implicit,
    kind_explicit,
    kind_dotted,
    kind_inline,
}

/// The document under assembly. `doc_array` exists only for arrays of
/// tables created by `[[...]]` headers (always extendable); a static array
/// value — including one holding inline tables — is a `doc_scalar`, which
/// is what makes `[[a]]` after `a = [{x = 1}]` an error rather than an
/// append into a value the document already closed.
type Toml.Doc {
    doc_table (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind),
    doc_array (items : List Toml.Doc),
    doc_scalar (v : Toml.Value),
}

/// The assembler's state: the steps addressing the header's table, and the
/// document built so far — or the reason assembly stopped.
///
/// `asm_error` is TERMINAL: once a header or key is rejected there is no
/// well-defined place for the lines after it to go, so they are not
/// assembled rather than being silently attached to the previous header's
/// table.
type Toml.Asm {
    asm_state (steps : List Toml.PathStep) (root : Toml.Doc),
    asm_error (msg : String),
}

// ─── Parser: character- and byte-level helpers ───

/// Horizontal whitespace only (space/tab) — deliberately excludes newline, since
/// newlines are significant (line separators) in this line-oriented grammar.
def Toml.is_hspace (c : String) : Bool :=
    if String.beq " " c then true else String.beq "\t" c

def toml_ws (input : String) : ParseResult String :=
    take_while Toml.is_hspace input

def toml_comma (input : String) : ParseResult String :=
    delimited_by toml_ws (tag ",") toml_ws input

def toml_eq (input : String) : ParseResult String :=
    delimited_by toml_ws (tag "=") toml_ws input

/// One byte of `s` as an `I64`, or -1 past the end. The byte-level parsers
/// (numbers, date-times, escapes) all key off this rather than a
/// `String.slice` per position: one byte per comparison, no allocation.
def Toml.byte_at (s : String) (i : I64) : I64 :=
    match String.get s i {
        Option.some b => U8.to_i64 b,
        Option.none => -1
    }

/// An `I64` payload back to a byte (`String.from_list`'s input type).
def Toml.byte_of (n : I64) : U8 :=
    U32.to_u8 (I64.to_u32 n)

/// `s`'s bytes as a list, for the byte-fold validators.
def Toml.bytes_of (s : String) : List U8 :=
    String.to_list s

/// `s` split into one-character pieces, stepping by each character's whole
/// UTF-8 width — a one-byte step would split a multi-byte character and hand
/// the fold an empty piece that reads as end-of-input (the same trap
/// `lang/json.mo`'s string parsers document).
#[partial]
def Toml.string_chars (s : String) : List String :=
    if is_empty s
    then List.empty
    else
        let width : I64 := utf8_char_width s in
        List.cons (String.slice s 0 width) (Toml.string_chars (String.drop width s))

// ─── Parser: keys ───

/// Bare TOML key character: ASCII alphanumeric, underscore, or hyphen.
/// `is_ident_char` is ASCII-only, so a non-ASCII character stops the scan
/// and the key has to be quoted — exactly the spec's bare-key rule.
def Toml.is_key_char (c : String) : Bool :=
    if is_ident_char c then true else String.beq "-" c

def toml_bare_key_result (r : ParseResult String) : ParseResult String :=
    match r {
        success rem out => if is_empty out then fail (ParseError.custom "expected key" rem) else success rem out,
        fail e => fail e
    }

/// Parse a single bare key (one path segment — no dots). Non-empty.
def Toml.bare_key (input : String) : ParseResult String :=
    toml_bare_key_result (take_while Toml.is_key_char input)

/// A single-line basic string's TEXT (between the quotes).
#[partial]
def Toml.basic_string_text (input : String) : ParseResult String :=
    toml_basic_text_open (tag "\"" input)

#[partial]
def toml_basic_text_open (r : ParseResult String) : ParseResult String :=
    match r {
        success rem _ => toml_basic_text_body (Toml.basic_string_content rem),
        fail e => fail e
    }

#[partial]
def toml_basic_text_body (r : ParseResult (List String)) : ParseResult String :=
    match r {
        success rem chars => toml_basic_text_close (tag "\"" rem) chars,
        fail e => fail e
    }

#[partial]
def toml_basic_text_close (r : ParseResult String) (chars : List String) : ParseResult String :=
    match r {
        success rem _ => success rem (String.concat_list chars),
        fail e => fail e
    }

/// A single-line literal string's TEXT (between the quotes) — raw, no
/// escapes.
#[partial]
def Toml.literal_string_text (input : String) : ParseResult String :=
    toml_literal_text_open (tag "'" input)

#[partial]
def toml_literal_text_open (r : ParseResult String) : ParseResult String :=
    match r {
        success rem _ => toml_literal_text_body (Toml.literal_string_content rem),
        fail e => fail e
    }

#[partial]
def toml_literal_text_body (r : ParseResult (List String)) : ParseResult String :=
    match r {
        success rem chars => toml_literal_text_close (tag "'" rem) chars,
        fail e => fail e
    }

#[partial]
def toml_literal_text_close (r : ParseResult String) (chars : List String) : ParseResult String :=
    match r {
        success rem _ => success rem (String.concat_list chars),
        fail e => fail e
    }

/// A quoted key: a single-line basic or literal string used as a key
/// segment. Both spellings unescape to the same key, so `a` and `"a"`
/// collide — which is what TOML says, and what the assembler's duplicate
/// detection then reports.
#[partial]
def Toml.quoted_key (input : String) : ParseResult String :=
    alt Toml.basic_string_text Toml.literal_string_text input

/// One key segment: bare, or quoted. Quoted first — a bare key cannot
/// start with a quote, so the order only matters for the error message.
#[partial]
def Toml.key_segment (input : String) : ParseResult String :=
    alt Toml.quoted_key Toml.bare_key input

/// A dotted key path (`a.b."c d"`), segments separated by `.` with
/// optional whitespace around it. The empty quoted key `""` is a legal
/// segment; an empty BARE segment (`a..b`, `a.`) is an error reported
/// where it happens.
#[partial]
def Toml.dotted_path (input : String) : ParseResult (List String) :=
    toml_path_start (Toml.key_segment input)

#[partial]
def toml_path_start (r : ParseResult String) : ParseResult (List String) :=
    match r {
        success rem seg => toml_path_more rem [seg],
        fail e => fail e
    }

/// After a segment: a `.` (with whitespace around it) means another
/// segment MUST follow. No dot ends the path — trailing whitespace is
/// left for the caller, whose `=`/`]`/`}` parsers each expect it.
#[partial]
def toml_path_more (input : String) (acc : List String) : ParseResult (List String) :=
    match toml_path_dot input {
        success rem _ => toml_path_next (Toml.key_segment rem) acc,
        fail _ => success input acc
    }

/// The `.` between segments, with whitespace on both sides.
#[partial]
def toml_path_dot (input : String) : ParseResult String :=
    delimited_by toml_ws (tag ".") toml_ws input

#[partial]
def toml_path_next (r : ParseResult String) (acc : List String) : ParseResult (List String) :=
    match r {
        success rem seg => toml_path_more rem (List.append acc [seg]),
        fail e => fail e
    }

// ─── Parser: string escapes ───

/// An escape sequence at `input` (which starts with the backslash):
/// the single-byte spellings plus `\uXXXX` and `\UXXXXXXXX`, which decode
/// to real UTF-8. Surrogate halves and anything above U+10FFFF are
/// ERRORS, not U+FFFD — TOML forbids them outright.
#[partial]
def Toml.parse_escape (input : String) : ParseResult String :=
    toml_escape_open (tag "\\" input)

#[partial]
def toml_escape_open (r : ParseResult String) : ParseResult String :=
    match r {
        success rem _ => Toml.escape_at rem,
        fail e => fail e
    }

/// After the backslash: dispatch on the escape's letter.
#[partial]
def Toml.escape_at (rem : String) : ParseResult String :=
    if is_empty rem
    then fail (ParseError.custom "unterminated escape sequence" rem)
    else
        let b : I64 := Toml.byte_at rem 0 in
        if I64.beq b 34 then success (String.drop 1 rem) "\""
        else if I64.beq b 92 then success (String.drop 1 rem) "\\"
        else if I64.beq b 98 then success (String.drop 1 rem) "\b"
        else if I64.beq b 116 then success (String.drop 1 rem) "\t"
        else if I64.beq b 110 then success (String.drop 1 rem) "\n"
        else if I64.beq b 102 then success (String.drop 1 rem) "\f"
        else if I64.beq b 114 then success (String.drop 1 rem) "\r"
        else if I64.beq b 117 then Toml.unicode_escape 4 (String.drop 1 rem)
        else if I64.beq b 85 then Toml.unicode_escape 8 (String.drop 1 rem)
        else fail (ParseError.custom "invalid escape sequence" rem)

/// One hex digit's value, or `none`.
def Toml.hex_nibble (b : I64) : Option I64 :=
    if I64.beq b 48 then Option.some 0
    else if I64.beq b 49 then Option.some 1
    else if I64.beq b 50 then Option.some 2
    else if I64.beq b 51 then Option.some 3
    else if I64.beq b 52 then Option.some 4
    else if I64.beq b 53 then Option.some 5
    else if I64.beq b 54 then Option.some 6
    else if I64.beq b 55 then Option.some 7
    else if I64.beq b 56 then Option.some 8
    else if I64.beq b 57 then Option.some 9
    else if I64.beq b 97 then Option.some 10
    else if I64.beq b 98 then Option.some 11
    else if I64.beq b 99 then Option.some 12
    else if I64.beq b 100 then Option.some 13
    else if I64.beq b 101 then Option.some 14
    else if I64.beq b 102 then Option.some 15
    else if I64.beq b 65 then Option.some 10
    else if I64.beq b 66 then Option.some 11
    else if I64.beq b 67 then Option.some 12
    else if I64.beq b 68 then Option.some 13
    else if I64.beq b 69 then Option.some 14
    else if I64.beq b 70 then Option.some 15
    else Option.none

/// `n` hex digits of `s` folded into a code point, or `none`.
#[partial]
def Toml.codepoint_hex (s : String) (n : I64) (acc : I64) : Option I64 :=
    if I64.beq n 0
    then Option.some acc
    else if is_empty s
    then Option.none
    else
        match Toml.hex_nibble (Toml.byte_at s 0) {
            Option.some d => Toml.codepoint_hex (String.drop 1 s) (n - 1) (I64.add (I64.mul acc 16) d),
            Option.none => Option.none
        }

#[partial]
def Toml.unicode_escape (n : I64) (input : String) : ParseResult String :=
    toml_hex_value (Toml.codepoint_hex input n 0) input n

#[partial]
def toml_hex_value (r : Option I64) (input : String) (n : I64) : ParseResult String :=
    match r {
        Option.none => fail (ParseError.custom "invalid \\u escape" input),
        Option.some cp =>
            if Toml.codepoint_bad cp
            then fail (ParseError.custom "invalid unicode escape (surrogate or above U+10FFFF)" input)
            else success (String.drop n input) (Toml.utf8_of_codepoint cp)
    }

/// Surrogate halves and out-of-range code points.
def Toml.codepoint_bad (cp : I64) : Bool :=
    if I64.gt cp 1114111 then true
    else if I64.gt cp 55295 && I64.lt cp 57344 then true
    else false

/// A code point as its UTF-8 bytes (1 to 4). Only called on points
/// `unicode_escape` has validated.
def Toml.utf8_of_codepoint (cp : I64) : String :=
    if I64.lt cp 128
    then String.from_list [Toml.byte_of cp]
    else if I64.lt cp 2048
    then String.from_list [
        Toml.byte_of (I64.add 192 (I64.div cp 64)),
        Toml.byte_of (I64.add 128 (I64.sub cp (I64.mul 64 (I64.div cp 64))))]
    else if I64.lt cp 65536
    then String.from_list [
        Toml.byte_of (I64.add 224 (I64.div cp 4096)),
        Toml.byte_of (I64.add 128 (I64.sub (I64.div cp 64) (I64.mul 64 (I64.div cp 4096)))),
        Toml.byte_of (I64.add 128 (I64.sub cp (I64.mul 64 (I64.div cp 64))))]
    else String.from_list [
        Toml.byte_of (I64.add 240 (I64.div cp 262144)),
        Toml.byte_of (I64.add 128 (I64.sub (I64.div cp 4096) (I64.mul 64 (I64.div cp 262144)))),
        Toml.byte_of (I64.add 128 (I64.sub (I64.div cp 64) (I64.mul 64 (I64.div cp 4096)))),
        Toml.byte_of (I64.add 128 (I64.sub cp (I64.mul 64 (I64.div cp 64))))]

// ─── Parser: single-line strings ───

/// A raw byte a basic string may not contain: control bytes other than
/// tab, and DEL (0x7F). Only the LEAD byte of a multi-byte character is
/// tested — the width step keeps the fold on character boundaries.
def Toml.basic_string_byte_bad (b : I64) : Bool :=
    if I64.lt b 32 && Bool.not (I64.beq b 9) then true
    else I64.beq b 127

/// One character of a single-line basic string: an escape, or a plain
/// character that is not `"`, `\`, a raw control byte or DEL.
#[partial]
def Toml.basic_string_char (input : String) : ParseResult String :=
    if is_empty input
    then fail (ParseError.custom "expected string character" input)
    else
        let width : I64 := utf8_char_width input in
        let b : I64 := Toml.byte_at input 0 in
        if I64.beq b 34 then fail (ParseError.custom "closing quote" input)
        else if I64.beq b 92 then fail (ParseError.custom "escape sequence" input)
        else if Toml.basic_string_byte_bad b
        then fail (ParseError.custom "control character in string must be escaped" input)
        else success (String.drop width input) (String.slice input 0 width)

/// The characters of a single-line basic string, up to its closing `"`.
/// `many0` stops at the quote (the plain-character parser fails there),
/// which is what makes the closing `tag "\""` in `basic_string_text` see it.
#[partial]
def Toml.basic_string_content (input : String) : ParseResult (List String) :=
    many0 (alt Toml.parse_escape Toml.basic_string_char) input

/// One character of a literal string: anything except `'` and a raw
/// control byte (tab allowed). No escapes — that is the whole point of
/// the literal spelling.
#[partial]
def Toml.literal_string_char (input : String) : ParseResult String :=
    if is_empty input
    then fail (ParseError.custom "expected literal string character" input)
    else
        let width : I64 := utf8_char_width input in
        let b : I64 := Toml.byte_at input 0 in
        if I64.beq b 39 then fail (ParseError.custom "closing quote" input)
        else if Toml.basic_string_byte_bad b
        then fail (ParseError.custom "control character not allowed in a literal string" input)
        else success (String.drop width input) (String.slice input 0 width)

#[partial]
def Toml.literal_string_content (input : String) : ParseResult (List String) :=
    many0 Toml.literal_string_char input

// ─── Parser: multi-line strings ───

/// A `"""` multi-line basic string. The first newline after the opening
/// delimiter is trimmed; a `\` at the end of a line trims all following
/// whitespace and newlines; CRLF is normalized to LF; a run of n >= 3
/// quotes closes with n - 3 left as content.
#[partial]
def Toml.multiline_basic (input : String) : ParseResult Toml.Value :=
    toml_mlb_open (tag "\"\"\"" input)

#[partial]
def toml_mlb_open (r : ParseResult String) : ParseResult Toml.Value :=
    match r {
        success rem _ => Toml.mlb_value (Toml.mlb_loop (Toml.mlb_trim_leading rem) List.empty),
        fail e => fail e
    }

#[partial]
def Toml.mlb_value (r : ParseResult String) : ParseResult Toml.Value :=
    match r {
        success rem text => success rem (Toml.string_value text),
        fail e => fail e
    }

/// Drop the first newline if the content starts with one (LF or CRLF).
def Toml.mlb_trim_leading (s : String) : String :=
    if String.starts_with "\r\n" s then String.drop 2 s
    else if String.starts_with "\n" s then String.drop 1 s
    else s

/// The multi-line basic body loop. Accumulates pieces in REVERSE and joins
/// once at the end (`String.concat_list`), so the self-call is the whole
/// body of an arm — the same tail shape `many0` documents for the
/// per-character cost of a large payload.
#[partial]
def Toml.mlb_loop (input : String) (acc : List String) : ParseResult String :=
    if is_empty input
    then fail (ParseError.custom "unterminated multi-line string" input)
    else
        let b : I64 := Toml.byte_at input 0 in
        if I64.beq b 34
        then toml_mlb_quotes (Toml.quote_run "\"" input) acc
        else if I64.beq b 92
        then toml_mlb_esc (Toml.mlb_backslash input) acc
        else toml_mlb_plain (Toml.mlb_plain_char input) acc

/// How many `q` bytes start at `input` (0 or more), and what follows them.
/// The closing rule needs the whole run at once.
#[partial]
def Toml.quote_run (q : String) (input : String) : Pair I64 String :=
    Toml.quote_run_go q input 0

#[partial]
def Toml.quote_run_go (q : String) (s : String) (n : I64) : Pair I64 String :=
    if String.starts_with q s then Toml.quote_run_go q (String.drop 1 s) (n + 1)
    else Pair.pair n s

/// A run of n >= 3 quotes closes the string, leaving n - 3 as content; a
/// run of 1 or 2 is content and the loop continues.
#[partial]
def toml_mlb_quotes (run : Pair I64 String) (acc : List String) : ParseResult String :=
    match run {
        Pair.pair n rest =>
            if I64.lt n 3
            then Toml.mlb_loop rest (List.append (Toml.quote_pieces "\"" n) acc)
            else success rest (String.concat_list (List.reverse (List.append (Toml.quote_pieces "\"" (n - 3)) acc)))
    }

/// n copies of `q`, as pieces for the accumulator.
#[partial]
def Toml.quote_pieces (q : String) (n : I64) : List String :=
    if I64.lt n 1 then List.empty
    else List.cons q (Toml.quote_pieces q (n - 1))

/// A backslash in a multi-line basic string: a line-ending continuation
/// (whitespace up to a newline, then ALL whitespace including newlines
/// trimmed), or an ordinary escape. The continuation is only valid when
/// the backslash is the last non-whitespace character on its line —
/// `\ x` is an invalid escape, not a continuation.
#[partial]
def Toml.mlb_backslash (input : String) : ParseResult String :=
    toml_mlb_bs_open (tag "\\" input) input

#[partial]
def toml_mlb_bs_open (r : ParseResult String) (input : String) : ParseResult String :=
    match r {
        success rem _ =>
            if is_empty rem
            then fail (ParseError.custom "unterminated escape sequence" rem)
            else if Toml.mlb_ws_byte (Toml.byte_at rem 0)
            then toml_mlb_continuation rem
            else Toml.parse_escape input,
        fail e => fail e
    }

/// Whitespace-and-newline bytes the continuation may skip.
def Toml.mlb_ws_byte (b : I64) : Bool :=
    if I64.beq b 32 then true
    else if I64.beq b 9 then true
    else if I64.beq b 10 then true
    else I64.beq b 13

#[partial]
def toml_mlb_continuation (rem : String) : ParseResult String :=
    toml_mlb_cont_go (Toml.scan_bytes Toml.mlb_ws_byte rem)

#[partial]
def toml_mlb_cont_go (scanned : Pair String String) : ParseResult String :=
    match scanned {
        Pair.pair ws_text rest =>
            if String.contains ws_text "\n"
            then success rest ""
            else if is_empty rest
            then fail (ParseError.custom "unterminated multi-line string" rest)
            else fail (ParseError.custom "a backslash must be the last non-whitespace character on its line" rest)
    }

/// Scan bytes while `pred` holds; the matched text and the remainder.
#[partial]
def Toml.scan_bytes (pred : I64 -> Bool) (s : String) : Pair String String :=
    Toml.scan_bytes_go pred s s 0

#[partial]
def Toml.scan_bytes_go (pred : I64 -> Bool) (original : String) (s : String) (n : I64) : Pair String String :=
    if is_empty s
    then Pair.pair (String.slice original 0 n) s
    else if pred (Toml.byte_at s 0)
    then Toml.scan_bytes_go pred original (String.drop 1 s) (n + 1)
    else Pair.pair (String.slice original 0 n) s

#[partial]
def toml_mlb_esc (r : ParseResult String) (acc : List String) : ParseResult String :=
    match r {
        success rem piece => Toml.mlb_loop rem (List.cons piece acc),
        fail e => fail e
    }

/// One plain character: control bytes other than tab are rejected, CRLF
/// (and a lone CR, which is not a TOML newline) is normalized to one LF,
/// everything else passes one whole UTF-8 character at a time.
/// A raw byte a multi-line string's plain character may not contain:
/// the single-line rule minus LF, which a multi-line string is allowed
/// to contain raw (CR is intercepted separately and must be part of a
/// CRLF pair).
def Toml.mlb_byte_bad (b : I64) : Bool :=
    if I64.beq b 10 then false else Toml.basic_string_byte_bad b

#[partial]
def Toml.mlb_plain_char (input : String) : ParseResult String :=
    if is_empty input
    then fail (ParseError.custom "expected character" input)
    else
        let b : I64 := Toml.byte_at input 0 in
        if I64.beq b 13
        then toml_mlb_cr (String.drop 1 input)
        else if Toml.mlb_byte_bad b
        then fail (ParseError.custom "control character in string must be escaped" input)
        else
            let width : I64 := utf8_char_width input in
            success (String.drop width input) (String.slice input 0 width)

#[partial]
def toml_mlb_cr (rest : String) : ParseResult String :=
    if String.starts_with "\n" rest
    then success (String.drop 1 rest) "\n"
    else fail (ParseError.custom "a carriage return must be followed by a line feed" rest)

#[partial]
def toml_mlb_plain (r : ParseResult String) (acc : List String) : ParseResult String :=
    match r {
        success rem ch => Toml.mlb_loop rem (List.cons ch acc),
        fail e => fail e
    }

/// A `'''` multi-line literal string: no escapes, first newline trimmed,
/// CR/CRLF normalized to LF, `''` inside is content per the quote-run rule.
#[partial]
def Toml.multiline_literal (input : String) : ParseResult Toml.Value :=
    toml_mll_open (tag "'''" input)

#[partial]
def toml_mll_open (r : ParseResult String) : ParseResult Toml.Value :=
    match r {
        success rem _ => Toml.mll_value (Toml.mll_loop (Toml.mlb_trim_leading rem) List.empty),
        fail e => fail e
    }

#[partial]
def Toml.mll_value (r : ParseResult String) : ParseResult Toml.Value :=
    match r {
        success rem text => success rem (Toml.string_value text),
        fail e => fail e
    }

#[partial]
def Toml.mll_loop (input : String) (acc : List String) : ParseResult String :=
    if is_empty input
    then fail (ParseError.custom "unterminated multi-line literal string" input)
    else
        let b : I64 := Toml.byte_at input 0 in
        if I64.beq b 39
        then toml_mll_quotes (Toml.quote_run "'" input) acc
        else toml_mll_plain (Toml.mll_plain_char input) acc

/// One plain character of a multi-line literal string: same rules as the
/// basic one's plain character, minus the escape branch a literal string
/// cannot have.
#[partial]
def Toml.mll_plain_char (input : String) : ParseResult String :=
    if is_empty input
    then fail (ParseError.custom "expected character" input)
    else
        let b : I64 := Toml.byte_at input 0 in
        if I64.beq b 13
        then toml_mlb_cr (String.drop 1 input)
        else if Toml.mlb_byte_bad b
        then fail (ParseError.custom "control character not allowed in a literal string" input)
        else
            let width : I64 := utf8_char_width input in
            success (String.drop width input) (String.slice input 0 width)

#[partial]
def toml_mll_quotes (run : Pair I64 String) (acc : List String) : ParseResult String :=
    match run {
        Pair.pair n rest =>
            if I64.lt n 3
            then Toml.mll_loop rest (List.append (Toml.quote_pieces "'" n) acc)
            else success rest (String.concat_list (List.reverse (List.append (Toml.quote_pieces "'" (n - 3)) acc)))
    }

#[partial]
def toml_mll_plain (r : ParseResult String) (acc : List String) : ParseResult String :=
    match r {
        success rem ch => Toml.mll_loop rem (List.cons ch acc),
        fail e => fail e
    }

// ─── Parser: string values (all four kinds) ───

def Toml.string_value (s : String) : Toml.Value := string s

/// A single-line basic string as a value.
#[partial]
def Toml.basic_string_open (input : String) : ParseResult Toml.Value :=
    map_parse Toml.string_value Toml.basic_string_text input

/// A single-line literal string as a value.
#[partial]
def Toml.literal_string_open (input : String) : ParseResult Toml.Value :=
    map_parse Toml.string_value Toml.literal_string_text input

/// Any string value: multi-line basic, multi-line literal, single-line
/// basic, or single-line literal — longest delimiters first, so `"""` is
/// not read as an empty single-line string followed by junk.
#[partial]
def Toml.parse_string (input : String) : ParseResult Toml.Value :=
    alt_fold
        [Toml.multiline_basic,
            Toml.multiline_literal,
            Toml.basic_string_open,
            Toml.literal_string_open]
        input

// ─── Parser: integers ───

/// `i64::MAX` — the positive fold's overflow bound.
def Toml.i64_max : I64 := 9223372036854775807

/// A decimal digit byte.
def Toml.is_digit_byte (b : I64) : Bool :=
    if I64.lt b 48 then false else Bool.not (I64.gt b 57)

/// Decimal digits and `_` grouping, byte-wise. The GROUPING rules are
/// enforced after the scan: every `_` needs a digit on both sides.
def Toml.is_digit_or_underscore_byte (b : I64) : Bool :=
    if Toml.is_digit_byte b then true else I64.beq b 95

/// A hex digit byte.
def Toml.is_hex_digit_byte (b : I64) : Bool :=
    if Toml.is_digit_byte b then true
    else if I64.gt b 96 && I64.lt b 103 then true
    else I64.gt b 64 && I64.lt b 71

/// An octal digit byte.
def Toml.is_octal_digit_byte (b : I64) : Bool :=
    if I64.lt b 48 then false else Bool.not (I64.gt b 55)

/// A binary digit byte.
def Toml.is_binary_digit_byte (b : I64) : Bool :=
    if I64.lt b 48 then false else Bool.not (I64.gt b 49)

/// Strip `_` from digit text. The grouping rules have already been
/// validated by the caller.
#[partial]
def Toml.strip_underscores (s : String) : String :=
    String.concat_list (List.filter (fn (c : String) => Bool.not (String.beq "_" c)) (Toml.string_chars s))

/// Digit text must not have a `_` at the start, end, or doubled: every
/// `_` needs a digit on BOTH sides.
def Toml.underscores_ok (s : String) : Bool :=
    toml_us_go (Toml.bytes_of s) false

/// `prev_digit` is whether the previous byte was a DIGIT (not `_`).
#[partial]
def toml_us_go (bs : List U8) (prev_digit : Bool) : Bool :=
    match bs {
        List.empty => prev_digit,
        List.cons b rest =>
            if I64.beq (U8.to_i64 b) 95
            then prev_digit && toml_us_go_digit rest
            else toml_us_go rest true
    }

/// A `_` was just seen: the next byte must exist and be a digit. "Digit"
/// here is "not `_`" -- the caller's byte scan has already restricted
/// the text to that radix's digits, and a DECIMAL-only test would reject
/// the hex letters a `0x` literal legitimately contains.
#[partial]
def toml_us_go_digit (bs : List U8) : Bool :=
    match bs {
        List.empty => false,
        List.cons b rest =>
            if I64.beq (U8.to_i64 b) 95 then false else toml_us_go rest true
    }

/// One decimal digit character's value, or `none`.
def Toml.digit_value (c : String) : Option I64 :=
    if String.beq "0" c then Option.some 0
    else if String.beq "1" c then Option.some 1
    else if String.beq "2" c then Option.some 2
    else if String.beq "3" c then Option.some 3
    else if String.beq "4" c then Option.some 4
    else if String.beq "5" c then Option.some 5
    else if String.beq "6" c then Option.some 6
    else if String.beq "7" c then Option.some 7
    else if String.beq "8" c then Option.some 8
    else if String.beq "9" c then Option.some 9
    else Option.none

/// One hex digit character's value, or `none`.
def Toml.hex_digit_value (c : String) : Option I64 :=
    match Toml.digit_value c {
        Option.some d => Option.some d,
        Option.none => Toml.hex_digit_alpha c
    }

def Toml.hex_digit_alpha (c : String) : Option I64 :=
    if String.beq "a" c then Option.some 10
    else if String.beq "A" c then Option.some 10
    else if String.beq "b" c then Option.some 11
    else if String.beq "B" c then Option.some 11
    else if String.beq "c" c then Option.some 12
    else if String.beq "C" c then Option.some 12
    else if String.beq "d" c then Option.some 13
    else if String.beq "D" c then Option.some 13
    else if String.beq "e" c then Option.some 14
    else if String.beq "E" c then Option.some 14
    else if String.beq "f" c then Option.some 15
    else if String.beq "F" c then Option.some 15
    else Option.none

/// Fold digit characters into an `I64`, detecting overflow BEFORE the
/// multiply: `acc * base + d > max` is checked as
/// `acc > (max - d) / base`. The digit function is a parameter so decimal
/// and radix integers share one fold.
#[partial]
def Toml.digits_pos (digit_of : String -> Option I64) (base : I64) (cs : List String) (acc : I64) : Option I64 :=
    match cs {
        List.empty => Option.some acc,
        List.cons c rest =>
            match digit_of c {
                Option.some d =>
                    if I64.gt acc (I64.div (I64.sub Toml.i64_max d) base)
                    then Option.none
                    else Toml.digits_pos digit_of base rest (I64.add (I64.mul acc base) d),
                Option.none => Option.none
            }
    }

/// A signed integer: `+`/`-` then decimal digits with `_` grouping, or an
/// unsigned `0x`/`0o`/`0b` literal (a sign on a radix literal is an
/// error — the spec gives radix integers no sign production). Leading
/// zeros are rejected for decimal (`0` itself is fine). Overflow is an
/// error.
/// NOTE: this does NOT use parsec's `number` — that parser folds `_` as
/// the digit 9, so `1_0` read as 190. TOML says `1_0` is 10, and a strict
/// local scanner is the fix (see `test_parse_underscored_integer`, whose
/// `1_0` row failed before this was written).
#[partial]
def Toml.parse_integer (input : String) : ParseResult I64 :=
    toml_int_sign (Toml.byte_at input 0) input

#[partial]
def toml_int_sign (b : I64) (input : String) : ParseResult I64 :=
    if I64.beq b 43 then toml_int_body (String.drop 1 input) false
    else if I64.beq b 45 then toml_int_body (String.drop 1 input) true
    else toml_int_body input false

#[partial]
def toml_int_body (input : String) (neg : Bool) : ParseResult I64 :=
    if String.starts_with "0x" input
    then toml_int_radix (String.drop 2 input) neg 16 Toml.is_hex_digit_byte Toml.hex_digit_value
    else if String.starts_with "0o" input
    then toml_int_radix (String.drop 2 input) neg 8 Toml.is_octal_digit_byte Toml.hex_digit_value
    else if String.starts_with "0b" input
    then toml_int_radix (String.drop 2 input) neg 2 Toml.is_binary_digit_byte Toml.hex_digit_value
    else toml_int_decimal input neg

/// A radix-prefixed integer's digits. Leading zeros and `_` grouping are
/// both allowed here (the spec restricts only DECIMAL leading zeros);
/// the digits are folded as hex digits, which is a superset of every
/// radix's digit set once the byte predicate has done its own check.
#[partial]
def toml_int_radix (digits : String) (neg : Bool) (base : I64) (pred : I64 -> Bool) (digit_of : String -> Option I64) : ParseResult I64 :=
    if neg
    then fail (ParseError.custom "a sign is not allowed on a radix integer" digits)
    else
        match Toml.scan_bytes pred digits {
            Pair.pair text rest =>
                if is_empty text
                then fail (ParseError.custom "expected digits after the radix prefix" digits)
                else if Bool.not (Toml.underscores_ok text)
                then fail (ParseError.custom "underscores must be surrounded by digits" digits)
                else toml_int_radix_value (Toml.digits_pos digit_of base (Toml.string_chars (Toml.strip_underscores text)) 0) rest
        }

#[partial]
def toml_int_radix_value (r : Option I64) (rest : String) : ParseResult I64 :=
    match r {
        Option.none => fail (ParseError.custom "integer out of range" rest),
        Option.some n => success rest n
    }

/// Decimal digits with `_` grouping. `unsigned-dec-int` is a single digit
/// or a nonzero digit followed by more — so a leading zero is only legal
/// when it is the whole number.
#[partial]
def toml_int_decimal (input : String) (neg : Bool) : ParseResult I64 :=
    match Toml.scan_bytes Toml.is_digit_or_underscore_byte input {
        Pair.pair text rest =>
            if is_empty text
            then fail (ParseError.custom "expected digits" input)
            else if Bool.not (Toml.underscores_ok text)
            then fail (ParseError.custom "underscores must be surrounded by digits" input)
            else if Toml.decimal_leading_zero text
            then fail (ParseError.custom "leading zeros are not allowed" input)
            else
                let digits : String := Toml.strip_underscores text in
                if neg && Toml.is_i64_min_magnitude digits
                then success rest Toml.i64_min
                else toml_int_dec_value (Toml.digits_pos Toml.digit_value 10 (Toml.string_chars digits) 0) neg rest
    }

/// A leading zero followed by anything at all (`01`, `00`, `0_1`) — the
/// spec's single-digit-only rule for a leading `0`.
def Toml.decimal_leading_zero (text : String) : Bool :=
    if String.starts_with "0" text
    then Bool.not (String.beq text "0")
    else false

/// The most-negative I64, built rather than spelled: the literal
/// `-9223372036854775808` has no positive counterpart for the parser's
/// range check to accept.
def Toml.i64_min : I64 := I64.sub (I64.neg Toml.i64_max) 1

#[partial]
def toml_int_dec_value (r : Option I64) (neg : Bool) (rest : String) : ParseResult I64 :=
    match r {
        Option.none => fail (ParseError.custom "integer out of range" rest),
        Option.some mag =>
            if neg
            then success rest (I64.neg mag)
            else success rest mag
    }

/// The magnitude of `i64_min`, compared as TEXT: the number itself (2^63)
/// is one past what an I64 can hold, so the digit fold overflows on it --
/// which is why `toml_int_decimal` checks this BEFORE folding.
def Toml.is_i64_min_magnitude (digits : String) : Bool :=
    String.beq digits "9223372036854775808"

def Toml.integer_value (n : I64) : Toml.Value := integer n

#[partial]
def Toml.parse_integer_value (input : String) : ParseResult Toml.Value :=
    map_parse Toml.integer_value Toml.parse_integer input

// ─── Parser: floats ───

/// A float: a decimal integer part, an optional `.` fraction and an
/// optional exponent — at least one of fraction/exponent present — or
/// `inf`/`nan` with an optional sign. `_` grouping is allowed in the
/// integer, fraction and exponent digits; leading zeros follow the
/// integer part's decimal rule.
#[partial]
def Toml.parse_float (input : String) : ParseResult F64 :=
    toml_float_kind (Toml.byte_at input 0) input

#[partial]
def toml_float_kind (b : I64) (input : String) : ParseResult F64 :=
    if I64.beq b 43 || I64.beq b 45
    then toml_float_signed (String.drop 1 input) (I64.beq b 45)
    else if String.starts_with "inf" input
    then success (String.drop 3 input) (1.0f64 / 0.0f64)
    else if String.starts_with "nan" input
    then success (String.drop 3 input) (Toml.nan_value)
    else toml_float_body input false

/// `+inf`/`-inf`/`+nan`/`-nan`, or a signed number.
#[partial]
def toml_float_signed (input : String) (neg : Bool) : ParseResult F64 :=
    if String.starts_with "inf" input
    then toml_float_inf neg (String.drop 3 input)
    else if String.starts_with "nan" input
    then success (String.drop 3 input) (Toml.nan_value)
    else toml_float_body input neg

#[partial]
def toml_float_inf (neg : Bool) (rest : String) : ParseResult F64 :=
    if neg
    then success rest (0.0f64 - (1.0f64 / 0.0f64))
    else success rest (1.0f64 / 0.0f64)

/// The NaN both backends agree on.
def Toml.nan_value : F64 := 0.0f64 / 0.0f64

/// The unsigned number body: integer part, then `.`/exponent as found.
#[partial]
def toml_float_body (input : String) (neg : Bool) : ParseResult F64 :=
    match Toml.scan_bytes Toml.is_digit_or_underscore_byte input {
        Pair.pair int_text rest =>
            if is_empty int_text
            then fail (ParseError.custom "expected float" input)
            else if Bool.not (Toml.underscores_ok int_text)
            then fail (ParseError.custom "underscores must be surrounded by digits" input)
            else if Toml.decimal_leading_zero int_text
            then fail (ParseError.custom "leading zeros are not allowed" input)
            else toml_float_after_int int_text rest neg
    }

#[partial]
def toml_float_after_int (int_text : String) (rest : String) (neg : Bool) : ParseResult F64 :=
    if String.starts_with "." rest
    then toml_float_frac int_text (String.drop 1 rest) neg
    else if String.starts_with "e" rest || String.starts_with "E" rest
    then toml_float_exp int_text "" rest neg
    else fail (ParseError.custom "a float needs a fraction or an exponent" rest)

/// The fraction digits after the `.`: at least one (leading zeros fine —
/// the fraction's own ABNF is zero-prefixable).
#[partial]
def toml_float_frac (int_text : String) (after_dot : String) (neg : Bool) : ParseResult F64 :=
    match Toml.scan_bytes Toml.is_digit_or_underscore_byte after_dot {
        Pair.pair frac_text rest =>
            if is_empty frac_text
            then fail (ParseError.custom "expected fraction digits" after_dot)
            else if Bool.not (Toml.underscores_ok frac_text)
            then fail (ParseError.custom "underscores must be surrounded by digits" after_dot)
            else toml_float_frac_rest int_text frac_text rest neg
    }

#[partial]
def toml_float_frac_rest (int_text : String) (frac_text : String) (rest : String) (neg : Bool) : ParseResult F64 :=
    if String.starts_with "e" rest || String.starts_with "E" rest
    then toml_float_exp int_text frac_text rest neg
    else toml_float_assemble int_text frac_text "0" false neg rest

/// The exponent after `e`/`E`: optional sign, then digits (leading zeros
/// allowed — the exponent's ABNF is plain digits).
#[partial]
def toml_float_exp (int_text : String) (frac_text : String) (rest : String) (neg : Bool) : ParseResult F64 :=
    toml_float_exp_body (String.drop 1 rest) int_text frac_text neg rest

/// The exponent's own sign is tracked separately and re-attached in
/// `toml_float_assemble` -- dropping it read `-2E-2` as -200.0.
#[partial]
def toml_float_exp_body (exp_input : String) (int_text : String) (frac_text : String) (neg : Bool) (orig : String) : ParseResult F64 :=
    let b : I64 := Toml.byte_at exp_input 0 in
    let exp_neg : Bool := I64.beq b 45 in
    let after_sign : String :=
        if I64.beq b 43 || I64.beq b 45 then String.drop 1 exp_input else exp_input in
    match Toml.scan_bytes Toml.is_digit_or_underscore_byte after_sign {
        Pair.pair exp_text rest =>
            if is_empty exp_text
            then fail (ParseError.custom "expected exponent digits" orig)
            else if Bool.not (Toml.underscores_ok exp_text)
            then fail (ParseError.custom "underscores must be surrounded by digits" orig)
            else toml_float_assemble int_text frac_text exp_text exp_neg neg rest
    }

/// Assemble the float from its parts via `Parse.f64` — the pure, portable,
/// correctly-rounded decimal parser (`std/parse.mo`). The sign is folded
/// back in by prefixing `-`, and the exponent (if any) by re-attaching
/// `e<digits>`, which is a spelling `Parse.f64` accepts.
#[partial]
def toml_float_assemble (int_text : String) (frac_text : String) (exp_text : String) (exp_neg : Bool) (neg : Bool) (rest : String) : ParseResult F64 :=
    let body : String := String.concat (Toml.strip_underscores int_text)
        (if is_empty frac_text then "" else String.concat "." (Toml.strip_underscores frac_text)) in
    let with_exp : String :=
        if is_empty exp_text
        then body
        else String.concat body (String.concat (if exp_neg then "e-" else "e") (Toml.strip_underscores exp_text)) in
    let signed : String := if neg then String.concat "-" with_exp else with_exp in
    match Parse.f64 signed {
        Option.some v => success rest v,
        Option.none => fail (ParseError.custom "invalid float" rest)
    }

def Toml.float_value (f : F64) : Toml.Value := float f

#[partial]
def Toml.parse_float_value (input : String) : ParseResult Toml.Value :=
    map_parse Toml.float_value Toml.parse_float input

// ─── Parser: date-times ───

/// A date-time, validated and preserved verbatim. All four kinds: offset
/// date-time (`1979-05-27T07:32:00Z`), local date-time, local date and
/// local time. `T`/`t`/space delimit date and time; `Z`/`z` or
/// `+`/`-`HH:MM is the offset. Secfrac allowed; leap seconds (second 60)
/// allowed; a space delimiter falls back to the bare date when no valid
/// time follows it (so `1979-05-27 # comment` is a date, not an error).
#[partial]
def Toml.parse_datetime (input : String) : ParseResult Toml.Value :=
    toml_dt_result (Toml.dt_scan input) input

/// The scan: a date-led one first, then a bare local time.
#[partial]
def Toml.dt_scan (input : String) : Option String :=
    match Toml.dt_scan_date input {
        Option.some text => Option.some text,
        Option.none => Toml.dt_time_part input 0
    }

#[partial]
def toml_dt_result (r : Option String) (input : String) : ParseResult Toml.Value :=
    match r {
        Option.none => fail (ParseError.custom "not a date-time" input),
        Option.some text => success (String.drop (String.length text) input) (datetime text)
    }

/// n digits at `input` starting at `start`, or `none` — the fixed-width
/// fields. Reads past the end see byte -1, which is never a digit.
#[partial]
def Toml.dt_digits (input : String) (start : I64) (n : I64) : Option I64 :=
    toml_dt_digits_go input start n 0

#[partial]
def toml_dt_digits_go (s : String) (i : I64) (n : I64) (acc : I64) : Option I64 :=
    if I64.beq n 0
    then Option.some acc
    else if Toml.is_digit_byte (Toml.byte_at s i)
    then toml_dt_digits_go s (i + 1) (n - 1) (I64.add (I64.mul acc 10) (I64.sub (Toml.byte_at s i) 48))
    else Option.none

/// The date `YYYY-MM-DD` at `input`, if a valid date-time starts there.
#[partial]
def Toml.dt_scan_date (input : String) : Option String :=
    match Toml.dt_digits input 0 4 {
        Option.none => Option.none,
        Option.some y =>
            if Bool.not (I64.beq (Toml.byte_at input 4) 45) then Option.none
            else match Toml.dt_digits input 5 2 {
                Option.none => Option.none,
                Option.some mo =>
                    if Bool.not (I64.beq (Toml.byte_at input 7) 45) then Option.none
                    else match Toml.dt_digits input 8 2 {
                        Option.none => Option.none,
                        Option.some d =>
                            if Bool.not (Toml.date_ok y mo d) then Option.none
                            else toml_dt_delim (Toml.byte_at input 10) input
                    }
            }
    }

/// Month 1-12 and a day valid for it (leap years included).
def Toml.date_ok (y : I64) (mo : I64) (d : I64) : Bool :=
    if I64.lt mo 1 || I64.gt mo 12 then false
    else if I64.lt d 1 then false
    else Bool.not (I64.gt d (Toml.days_in_month y mo))

#[partial]
def Toml.days_in_month (y : I64) (mo : I64) : I64 :=
    if I64.beq mo 2
    then if Toml.leap_year y then 29 else 28
    else if I64.beq mo 4 || I64.beq mo 6 || I64.beq mo 9 || I64.beq mo 11 then 30 else 31

/// The remainder of a / b for the non-negative years a date may carry,
/// spelled without a  native: a - (a / b) * b.
def Toml.rem (a : I64) (b : I64) : I64 :=
    I64.sub a (I64.mul (I64.div a b) b)

def Toml.leap_year (y : I64) : Bool :=
    if I64.beq (Toml.rem y 4) 0 && Bool.not (I64.beq (Toml.rem y 100) 0) then true
    else I64.beq (Toml.rem y 400) 0

/// After a valid date: `T`/`t` REQUIRES a time; a space tries one and
/// falls back to the bare date; anything else is the bare date.
#[partial]
def toml_dt_delim (b : I64) (input : String) : Option String :=
    if I64.beq b 84 || I64.beq b 116
    then Toml.dt_time_part input 11
    else if I64.beq b 32
    then toml_dt_space_time input
    else Option.some (String.slice input 0 10)

#[partial]
def toml_dt_space_time (input : String) : Option String :=
    match Toml.dt_time_part input 11 {
        Option.some text => Option.some text,
        Option.none => Option.some (String.slice input 0 10)
    }

/// The time `HH:MM:SS` starting at `i`.
#[partial]
def Toml.dt_time_part (input : String) (i : I64) : Option String :=
    match Toml.dt_digits input i 2 {
        Option.none => Option.none,
        Option.some hh =>
            if Bool.not (I64.beq (Toml.byte_at input (i + 2)) 58) then Option.none
            else match Toml.dt_digits input (i + 3) 2 {
                Option.none => Option.none,
                Option.some mi =>
                    if Bool.not (I64.beq (Toml.byte_at input (i + 5)) 58) then Option.none
                    else match Toml.dt_digits input (i + 6) 2 {
                        Option.none => Option.none,
                        Option.some ss =>
                            if Bool.not (Toml.time_ok hh mi ss) then Option.none
                            else toml_dt_after_seconds input (i + 8)
                    }
            }
    }

/// Hour 0-23, minute 0-59, second 0-60 (the leap-second allowance).
def Toml.time_ok (hh : I64) (mi : I64) (ss : I64) : Bool :=
    if I64.lt hh 0 || I64.gt hh 23 then false
    else if I64.lt mi 0 || I64.gt mi 59 then false
    else Bool.not (I64.lt ss 0 || I64.gt ss 60)

/// After the seconds: an optional secfrac, then offset-or-end.
#[partial]
def toml_dt_after_seconds (input : String) (i : I64) : Option String :=
    if I64.beq (Toml.byte_at input i) 46
    then toml_dt_frac_digits input (i + 1) (i + 1)
    else toml_dt_offset (Toml.byte_at input i) input i

/// Secfrac digits: at least one.
#[partial]
def toml_dt_frac_digits (input : String) (start : I64) (i : I64) : Option String :=
    if Toml.is_digit_byte (Toml.byte_at input i)
    then toml_dt_frac_digits input start (i + 1)
    else if I64.beq i start then Option.none
    else toml_dt_offset (Toml.byte_at input i) input i

/// The offset: `Z`/`z`, `+HH:MM`/`-HH:MM`, or nothing (local).
#[partial]
def toml_dt_offset (b : I64) (input : String) (i : I64) : Option String :=
    if I64.beq b 90 || I64.beq b 122
    then Option.some (String.slice input 0 (i + 1))
    else if I64.beq b 43 || I64.beq b 45
    then toml_dt_offset_digits input i
    else Option.some (String.slice input 0 i)

#[partial]
def toml_dt_offset_digits (input : String) (i : I64) : Option String :=
    match Toml.dt_digits input (i + 1) 2 {
        Option.none => Option.none,
        Option.some oh =>
            if Bool.not (I64.beq (Toml.byte_at input (i + 3)) 58) then Option.none
            else match Toml.dt_digits input (i + 4) 2 {
                Option.none => Option.none,
                Option.some om =>
                    if Bool.not (Toml.offset_ok oh om) then Option.none
                    else Option.some (String.slice input 0 (i + 6))
            }
    }

/// Offset hour 0-23, minute 0-59.
def Toml.offset_ok (oh : I64) (om : I64) : Bool :=
    if I64.lt oh 0 || I64.gt oh 23 then false
    else Bool.not (I64.lt om 0 || I64.gt om 59)

// ─── Parser: booleans ───

def toml_parse_true_result (r : ParseResult String) : ParseResult Toml.Value :=
    match r {
        success rem _ => success rem (boolean true),
        fail e => fail e
    }

def Toml.parse_true (input : String) : ParseResult Toml.Value :=
    toml_parse_true_result (tag "true" input)

def toml_parse_false_result (r : ParseResult String) : ParseResult Toml.Value :=
    match r {
        success rem _ => success rem (boolean false),
        fail e => fail e
    }

def Toml.parse_false (input : String) : ParseResult Toml.Value :=
    toml_parse_false_result (tag "false" input)

/// Parse boolean values (true or false)
def Toml.parse_bool (input : String) : ParseResult Toml.Value :=
    alt Toml.parse_true Toml.parse_false input

// ─── Parser: arrays ───

/// Whitespace INSIDE an array: horizontal space, newlines, and whole
/// comment lines. Outside an array a newline ends the item; between
/// `[` and `]` TOML explicitly allows an array to span lines, which is
/// how this repo's own root `mote.toml` writes `[workspace] members`.
#[partial]
def toml_array_ws (input : String) : ParseResult String :=
    toml_array_ws_go input

#[partial]
def toml_array_ws_go (input : String) : ParseResult String :=
    match take_while Toml.is_array_space input {
        success rem1 _ =>
            if String.starts_with "#" rem1
            then
                match take_while Toml.is_not_newline rem1 {
                    success rem2 _ => toml_array_ws_go rem2,
                    fail e => fail e,
                }
            else success rem1 "",
        fail e => fail e,
    }

/// Space, tab, CR or LF -- the character class that may appear between
/// an array's own brackets.
def Toml.is_array_space (c : String) : Bool :=
    if Toml.is_hspace c then true
    else if String.beq "\n" c then true
    else String.beq "\r" c

def Toml.is_not_newline (c : String) : Bool :=
    Bool.not (String.beq "\n" c)

/// A comma inside an array, with newlines and comments allowed on both
/// sides of it.
#[partial]
def toml_array_comma (input : String) : ParseResult String :=
    delimited_by toml_array_ws (tag ",") toml_array_ws input

/// The array body: comma-separated values (ANY value — nested arrays are
/// part of TOML 1.0), with an optional trailing comma — but ONLY after at
/// least one element (`[,]` is an error, and parsed as `[]` before the
/// trailing-comma check gained its non-empty guard).
#[partial]
def toml_parse_array_body (input : String) : ParseResult (List Toml.Value) :=
    delimited_by toml_array_ws (separated_by toml_array_comma Toml.parse_value) toml_array_ws input

#[partial]
def Toml.parse_array (input : String) : ParseResult Toml.Value :=
    toml_parse_array_result (delimited_by (tag "[") toml_parse_array_trailing (tag "]") input)

/// The array body plus an optional trailing comma (and whatever blanks
/// or comments follow it) before the closing bracket.
#[partial]
def toml_parse_array_trailing (input : String) : ParseResult (List Toml.Value) :=
    match toml_parse_array_body input {
        success rem elems =>
            if List.is_empty elems
            then success rem elems
            else if String.starts_with "," rem
            then
                match toml_array_ws (String.drop 1 rem) {
                    success rem2 _ => success rem2 elems,
                    fail e => fail e,
                }
            else success rem elems,
        fail e => fail e
    }

def toml_parse_array_result (r : ParseResult (List Toml.Value)) : ParseResult Toml.Value :=
    match r {
        success rem elems => success rem (array elems),
        fail e => fail e
    }

// ─── Parser: inline tables ───

/// The body of an inline table: comma-separated `key = value` pairs,
/// with NO trailing comma and NO newline between the braces — except
/// inside a value (a nested multi-line array or string), which the value
/// parsers handle themselves.
///
/// The no-trailing-comma rule is hand-rolled rather than written with
/// `separated_by` because that combinator CONSUMES a separator it then
/// finds nothing after, so `{ a = 1, }` parsed and `tag "}"` never saw
/// the dangling comma. TOML allows a trailing comma in an ARRAY (this
/// parser does too, deliberately -- the repo's own root manifest
/// writes one) and forbids it in an inline table.
#[partial]
def toml_parse_inline_body (input : String) : ParseResult (List (Pair (List String) Toml.Value)) :=
    toml_inline_body_start (toml_ws input)

#[partial]
def toml_inline_body_start (r : ParseResult String) : ParseResult (List (Pair (List String) Toml.Value)) :=
    match r {
        success rem _ => toml_inline_body_first (Toml.parse_kv rem) rem,
        fail e => fail e
    }

/// No pair at all is the empty inline table (`{}`), not a failure.
#[partial]
def toml_inline_body_first (r : ParseResult (Pair (List String) Toml.Value)) (input : String) : ParseResult (List (Pair (List String) Toml.Value)) :=
    match r {
        success rem p => toml_inline_body_more rem [p],
        fail _ => toml_inline_body_end input List.empty
    }

/// After a pair: a comma means another pair MUST follow. A newline
/// before the `}` is an error (the spec's single-line rule).
#[partial]
def toml_inline_body_more (input : String) (acc : List (Pair (List String) Toml.Value)) : ParseResult (List (Pair (List String) Toml.Value)) :=
    if String.starts_with "\n" input || String.starts_with "\r" input
    then fail (ParseError.custom "a newline is not allowed inside an inline table" input)
    else match toml_comma input {
        success rem _ => toml_inline_body_next (Toml.parse_kv rem) acc,
        fail _ => toml_inline_body_end input acc
    }

#[partial]
def toml_inline_body_next (r : ParseResult (Pair (List String) Toml.Value)) (acc : List (Pair (List String) Toml.Value)) : ParseResult (List (Pair (List String) Toml.Value)) :=
    match r {
        success rem p => toml_inline_body_more rem (List.append acc [p]),
        fail e => fail e
    }

/// Strip the horizontal space before the closing brace.
#[partial]
def toml_inline_body_end (input : String) (acc : List (Pair (List String) Toml.Value)) : ParseResult (List (Pair (List String) Toml.Value)) :=
    match toml_ws input {
        success rem _ => success rem acc,
        fail e => fail e
    }

/// Parse an inline table (`{ path = "../x" }`, `{}`) — the dependency
/// spelling `mote.toml` uses everywhere outside this repo.
#[partial]
def Toml.parse_inline_table (input : String) : ParseResult Toml.Value :=
    toml_inline_table_result (delimited_by (tag "{") toml_parse_inline_body (tag "}") input)

#[partial]
def toml_inline_table_result (r : ParseResult (List (Pair (List String) Toml.Value))) : ParseResult Toml.Value :=
    match r {
        success rem pairs => toml_inline_table_built (Toml.inline_table_of_pairs pairs) rem,
        fail e => fail e
    }

#[partial]
def toml_inline_table_built (r : Result String (BTreeMap String Toml.Value)) (rem : String) : ParseResult Toml.Value :=
    match r {
        Result.err e => fail (ParseError.custom e rem),
        Result.ok t => success rem (table t)
    }

/// Fold the inline table's pairs into a table, nesting dotted paths and
/// rejecting duplicate keys.
#[partial]
def Toml.inline_table_of_pairs (pairs : List (Pair (List String) Toml.Value)) : Result String (BTreeMap String Toml.Value) :=
    Toml.inline_pairs_go pairs BTreeMap.empty

#[partial]
def Toml.inline_pairs_go (pairs : List (Pair (List String) Toml.Value)) (acc : BTreeMap String Toml.Value) : Result String (BTreeMap String Toml.Value) :=
    match pairs {
        List.empty => Result.ok acc,
        List.cons p rest =>
            match p {
                Pair.pair path v =>
                    match Toml.inline_insert path v acc {
                        Option.none => Result.err (Toml.inline_duplicate_error (Toml.path_head path)),
                        Option.some acc2 => Toml.inline_pairs_go rest acc2,
                    }
            }
    }

/// The first segment of a path, for error messages.
def Toml.path_head (path : List String) : String :=
    match path {
        List.empty => "",
        List.cons k _ => k
    }

/// Insert `value` at `path` within `t`, creating intermediate tables for
/// dotted keys and rejecting a duplicate key. `none` = the conflict.
#[partial]
def Toml.inline_insert (path : List String) (value : Toml.Value) (t : BTreeMap String Toml.Value) : Option (BTreeMap String Toml.Value) :=
    match path {
        List.empty => Option.none,
        List.cons k rest =>
            if List.is_empty rest
            then
                match Map.lookup k t {
                    Option.some _ => Option.none,
                    Option.none => Option.some (Map.insert k value t),
                }
            else
                match Map.lookup k t {
                    Option.none => Toml.inline_insert_fresh k rest value t,
                    Option.some existing => Toml.inline_insert_merge k rest value existing t,
                }
    }

/// The intermediate is absent: nest the rest of the path into a fresh
/// table under `k`.
#[partial]
def Toml.inline_insert_fresh (k : String) (rest : List String) (value : Toml.Value) (t : BTreeMap String Toml.Value) : Option (BTreeMap String Toml.Value) :=
    match Toml.inline_insert rest value BTreeMap.empty {
        Option.none => Option.none,
        Option.some sub => Option.some (Map.insert k (table sub) t),
    }

/// The intermediate exists: a dotted key may extend a table-valued key
/// (see the module header for the one divergence this allows); anything
/// else is a conflict.
#[partial]
def Toml.inline_insert_merge (k : String) (rest : List String) (value : Toml.Value) (existing : Toml.Value) (t : BTreeMap String Toml.Value) : Option (BTreeMap String Toml.Value) :=
    match existing {
        table sub =>
            match Toml.inline_insert rest value sub {
                Option.none => Option.none,
                Option.some sub2 => Option.some (Map.insert k (table sub2) t),
            },
        _ => Option.none
    }

// ─── Parser: values ───

/// Parse any TOML value that can appear on the right-hand side of
/// `key = value`. The date-time comes before the number parsers so
/// `1979-05-27` is not read as the integer 1979 followed by garbage, and
/// the string parsers come before it so a quoted value never reaches the
/// number grammar.
#[partial]
def Toml.parse_value (input : String) : ParseResult Toml.Value :=
    alt_fold
        [Toml.parse_bool,
            Toml.parse_string,
            Toml.parse_datetime,
            Toml.parse_float_value,
            Toml.parse_array,
            Toml.parse_inline_table,
            Toml.parse_integer_value]
        input

// ─── Parser: key-value pairs ───

/// Parse a `key = value` pair, the key as a dotted/quoted path. Used by
/// both document lines and inline-table bodies.
///
/// `#[partial]` here and on the helpers below it: an inline table's body
/// is a list of these pairs, so `parse_kv -> toml_kv_key -> toml_kv_eq ->
/// Toml.parse_value -> Toml.parse_inline_table -> toml_parse_inline_body
/// -> parse_kv` is a real cycle. It terminates on input length -- every
/// step through it has consumed at least the `{` -- which is not a
/// structural subterm relation the checker can see, the same reason
/// every combinator in `lang/src/parser/` carries the attribute.
#[partial]
def Toml.parse_kv (input : String) : ParseResult (Pair (List String) Toml.Value) :=
    toml_kv_key (Toml.dotted_path input)

#[partial]
def toml_kv_key (r : ParseResult (List String)) : ParseResult (Pair (List String) Toml.Value) :=
    match r {
        success rem path => toml_kv_eq rem path,
        fail e => fail e
    }

#[partial]
def toml_kv_eq (rem : String) (path : List String) : ParseResult (Pair (List String) Toml.Value) :=
    toml_kv_after_eq (toml_eq rem) path

#[partial]
def toml_kv_after_eq (r : ParseResult String) (path : List String) : ParseResult (Pair (List String) Toml.Value) :=
    match r {
        success rem _ => toml_kv_value (Toml.parse_value rem) path,
        fail e => fail e
    }

#[partial]
def toml_kv_value (r : ParseResult Toml.Value) (path : List String) : ParseResult (Pair (List String) Toml.Value) :=
    match r {
        success rem v => success rem (Pair.pair path v),
        fail e => fail e
    }

// ─── Parser: lines (headers / key-value pairs) ───

/// A header's dotted path, with the whitespace a `[ a . b ]` spelling
/// puts around it.
#[partial]
def Toml.header_path (input : String) : ParseResult (List String) :=
    toml_header_path (toml_ws input)

#[partial]
def toml_header_path (r : ParseResult String) : ParseResult (List String) :=
    match r {
        success rem _ => toml_header_path_end (Toml.dotted_path rem),
        fail e => fail e
    }

#[partial]
def toml_header_path_end (r : ParseResult (List String)) : ParseResult (List String) :=
    match r {
        success rem path => toml_header_ws_end (toml_ws rem) path,
        fail e => fail e
    }

#[partial]
def toml_header_ws_end (r : ParseResult String) (path : List String) : ParseResult (List String) :=
    match r {
        success rem _ => success rem path,
        fail e => fail e
    }

/// Parse a `[table]` / `[a.b.c]` table header, returning the dotted path.
#[partial]
def Toml.parse_header (input : String) : ParseResult (List String) :=
    delimited_by (tag "[") Toml.header_path (tag "]") input

def toml_line_of_header (path : List String) : Toml.Line := header path

#[partial]
def Toml.parse_header_line (input : String) : ParseResult Toml.Line :=
    map_parse toml_line_of_header Toml.parse_header input

/// Parse an `[[array.of.tables]]` header, returning the dotted path.
#[partial]
def Toml.parse_array_header (input : String) : ParseResult (List String) :=
    delimited_by (tag "[[") Toml.header_path (tag "]]") input

def toml_line_of_array_header (path : List String) : Toml.Line := array_header path

#[partial]
def Toml.parse_array_header_line (input : String) : ParseResult Toml.Line :=
    map_parse toml_line_of_array_header Toml.parse_array_header input

def toml_line_of_kv (p : Pair (List String) Toml.Value) : Toml.Line :=
    match p { Pair.pair path v => kv path v }

#[partial]
def Toml.parse_kv_line (input : String) : ParseResult Toml.Line :=
    map_parse toml_line_of_kv Toml.parse_kv input

/// Parse one document line's content (either a header or a kv pair) — does not
/// itself handle blank lines or the trailing newline; see Toml.parse_one_line.
/// `[[x]]` is tried before `[x]`. It would win anyway -- the plain header's
/// key parser fails on the second `[` -- but ordering it first is what
/// makes `alt_fold` report the array header's own error for a malformed
/// `[[x]` rather than the plain header's confusing one.
#[partial]
def Toml.parse_line (input : String) : ParseResult Toml.Line :=
    alt_fold [Toml.parse_array_header_line, Toml.parse_header_line, Toml.parse_kv_line] input

// ─── Parser: document (blank-line skipping, one line at a time) ───

/// Everything from a `#` to the end of the line is a comment. Only ever reached
/// once the line's own content has been consumed (or on a line that starts with
/// `#`), so a `#` inside a quoted value was already eaten by the string parser
/// and never looks like a comment here.
def toml_is_not_newline (c : String) : Bool :=
    not (String.beq "\n" c)

def toml_drop_comment_result (r : ParseResult String) : String :=
    match r {
        success rem _ => rem,
        fail _ => ""
    }

/// Consume a `#` comment's text, leaving the line terminator (if any) in
/// place for the caller's own end-of-line handling.
def toml_drop_comment (rem : String) : String :=
    toml_drop_comment_result (take_while toml_is_not_newline rem)

/// The end of a line: EOF, LF, or CRLF — with a trailing comment
/// consumed first. A lone CR is not a TOML newline and falls through to
/// the "expected newline" error.
#[partial]
def toml_one_line_eol (rem : String) (line : Toml.Line) : ParseResult (Option Toml.Line) :=
    if is_empty rem then success rem (Option.some line)
    else if String.starts_with "\n" rem then success (String.drop 1 rem) (Option.some line)
    else if String.starts_with "\r\n" rem then success (String.drop 2 rem) (Option.some line)
    else if String.starts_with "#" rem then toml_one_line_eol (toml_drop_comment rem) line
    else fail (ParseError.custom "expected newline after line" rem)

def toml_one_line_trailing_ws (r : ParseResult String) (line : Toml.Line) : ParseResult (Option Toml.Line) :=
    match r {
        success rem _ => toml_one_line_eol rem line,
        fail e => fail e
    }

def toml_one_line_after_value (rem : String) (line : Toml.Line) : ParseResult (Option Toml.Line) :=
    toml_one_line_trailing_ws (toml_ws rem) line

def toml_one_line_parse_result (r : ParseResult Toml.Line) : ParseResult (Option Toml.Line) :=
    match r {
        success rem2 line => toml_one_line_after_value rem2 line,
        fail e => fail e
    }

def toml_one_line_parse (rem : String) : ParseResult (Option Toml.Line) :=
    toml_one_line_parse_result (Toml.parse_line rem)

/// A blank (whitespace-only) line, or EOF right after leading whitespace,
/// produces `None` and is skipped — otherwise the line is parsed and must be
/// followed by a newline or EOF. CRLF counts as the line terminator.
// NOTE: `is_empty rem` here must FAIL, not succeed — many0 (used by Toml.document
// below) has no zero-consumption guard, so a parser that succeeds without
// consuming input on an already-empty remainder loops forever. Failing here lets
// many0 stop naturally via its own `fail _ => success input List.empty` branch.
def toml_one_line_check_blank (rem : String) : ParseResult (Option Toml.Line) :=
    if is_empty rem then fail (ParseError.custom "no more lines" rem)
    else if String.starts_with "\n" rem then success (String.drop 1 rem) Option.none
    else if String.starts_with "\r\n" rem then success (String.drop 2 rem) Option.none
    else if String.starts_with "#" rem then toml_comment_line (toml_drop_comment rem)
    else toml_one_line_parse rem

/// A whole-line comment yields no `Toml.Line`, exactly like a blank line.
def toml_comment_line (rem : String) : ParseResult (Option Toml.Line) :=
    if String.starts_with "\n" rem then success (String.drop 1 rem) Option.none
    else if String.starts_with "\r\n" rem then success (String.drop 2 rem) Option.none
    else success rem Option.none

def toml_one_line_hws (r : ParseResult String) : ParseResult (Option Toml.Line) :=
    match r {
        success rem _ => toml_one_line_check_blank rem,
        fail e => fail e
    }

/// Attempt to parse (and consume, including its trailing newline) exactly one
/// document line, returning `None` for a blank line.
def Toml.parse_one_line (input : String) : ParseResult (Option Toml.Line) :=
    toml_one_line_hws (toml_ws input)

def Toml.filter_some (opts : List (Option Toml.Line)) : List Toml.Line :=
    match opts {
        List.empty => List.empty,
        List.cons o rest => toml_filter_some_one o rest
    }

#[partial]
def toml_filter_some_one (o : Option Toml.Line) (rest : List (Option Toml.Line)) : List Toml.Line :=
    match o {
        some l => List.cons l (Toml.filter_some rest),
        none => Toml.filter_some rest
    }

/// Parse the whole document into a flat list of lines (blank lines dropped).
/// Anything that isn't a valid blank/header/kv line is left unconsumed — the
/// caller (Toml.parse) turns leftover input into a parse error.
def Toml.document (input : String) : ParseResult (List Toml.Line) :=
    map_parse Toml.filter_some (many0 Toml.parse_one_line) input

// ─── Document assembly: lines -> kinded tree -> nested table ───

/// Apply a `[table]` header: walk `path` creating implicit tables,
/// promote or create the target as explicit, and return the new tree
/// plus the steps addressing the target.
#[partial]
def Toml.apply_header (path : List String) (root : Toml.Doc) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match path {
        List.empty => Result.err "a header must name a key",
        List.cons k rest =>
            if List.is_empty rest
            then Toml.header_final k root
            else Toml.header_step k rest root
    }

/// One intermediate segment of a header path — shared by `[table]` and
/// `[[array]]` headers, whose intermediate rules are the same.
#[partial]
def Toml.header_step (k : String) (rest : List String) (root : Toml.Doc) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match root {
        doc_table entries kind =>
            match Map.lookup k entries {
                Option.none => Toml.header_create k rest entries kind,
                Option.some child => Toml.header_descend k rest child entries kind,
            },
        _ => Result.err "a header path may not descend through a non-table"
    }

/// The intermediate segment is absent: create an implicit table and
/// continue the walk inside it.
#[partial]
def Toml.header_create (k : String) (rest : List String) (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match Toml.apply_header rest (doc_table BTreeMap.empty kind_implicit) {
        Result.err e => Result.err e,
        Result.ok pr =>
            match pr {
                Pair.pair inner_steps inner =>
                    Result.ok (Pair.pair (List.cons (step_key k) inner_steps) (doc_table (Map.insert k inner entries) kind)),
            },
    }

/// The intermediate segment exists: pass through a header/dotted table,
/// descend into an open array of tables' LAST element (the
/// `[[fruit]]`-then-`[fruit.physical]` case), or report the conflict.
#[partial]
def Toml.header_descend (k : String) (rest : List String) (child : Toml.Doc) (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match child {
        doc_table _ ck =>
            if Toml.kind_is_inline ck
            then Result.err (Toml.inline_immutable_error k)
            else
                match Toml.apply_header rest child {
                    Result.err e => Result.err e,
                    Result.ok pr =>
                        match pr {
                            Pair.pair inner_steps inner =>
                                Result.ok (Pair.pair (List.cons (step_key k) inner_steps) (doc_table (Map.insert k inner entries) kind)),
                        },
                },
        doc_array items =>
            match Toml.apply_header_in_last rest items {
                Result.err e => Result.err (Toml.array_descend_prefix k e),
                Result.ok pr =>
                    match pr {
                        Pair.pair inner_steps items2 =>
                            Result.ok (Pair.pair (List.cons (step_last k) inner_steps) (doc_table (Map.insert k (doc_array items2) entries) kind)),
                    },
            },
        doc_scalar _ => Result.err (Toml.scalar_descend_error k)
    }

/// Apply `path` inside the LAST element of `items` (an open array of
/// tables), rebuilding the list.
#[partial]
def Toml.apply_header_in_last (path : List String) (items : List Toml.Doc) : Result String (Pair (List Toml.PathStep) (List Toml.Doc)) :=
    match items {
        List.empty => Result.err "an array of tables cannot be empty here",
        List.cons x rest =>
            if List.is_empty rest
            then
                match Toml.apply_header path x {
                    Result.err e => Result.err e,
                    Result.ok pr =>
                        match pr {
                            Pair.pair inner_steps x2 => Result.ok (Pair.pair inner_steps (List.cons x2 rest)),
                        },
                }
            else
                match Toml.apply_header_in_last path rest {
                    Result.err e => Result.err e,
                    Result.ok pr =>
                        match pr {
                            Pair.pair inner_steps rest2 => Result.ok (Pair.pair inner_steps (List.cons x rest2)),
                        },
                }
    }

/// The header's final segment: create the table, or promote an implicit
/// one — anything already there is the spec's "defined more than once".
#[partial]
def Toml.header_final (k : String) (root : Toml.Doc) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match root {
        doc_table entries kind =>
            match Map.lookup k entries {
                Option.none =>
                    Result.ok (Pair.pair [step_key k] (doc_table (Map.insert k (doc_table BTreeMap.empty kind_explicit) entries) kind)),
                Option.some child => Toml.header_final_existing k child entries kind,
            },
        _ => Result.err "a header path may not descend through a non-table"
    }

#[partial]
def Toml.header_final_existing (k : String) (child : Toml.Doc) (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match child {
        doc_table c_entries c_kind =>
            if Toml.kind_is_inline c_kind
            then Result.err (Toml.inline_immutable_error k)
            else if Toml.kind_is_implicit c_kind
            then Result.ok (Pair.pair [step_key k] (doc_table (Map.insert k (doc_table c_entries kind_explicit) entries) kind))
            else if Toml.kind_is_dotted c_kind
            then Result.err (Toml.dotted_redefined_error k)
            else Result.err (Toml.header_redefined_error k),
        doc_array _ => Result.err (Toml.header_over_array_error k),
        doc_scalar _ => Result.err (Toml.scalar_descend_error k)
    }

/// Apply an `[[array.of.tables]]` header: the same intermediate walk, a
/// final segment that appends a fresh table to an open array (or creates
/// one).
#[partial]
def Toml.apply_array_header (path : List String) (root : Toml.Doc) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match path {
        List.empty => Result.err "a header must name a key",
        List.cons k rest =>
            if List.is_empty rest
            then Toml.array_header_final k root
            else Toml.array_header_step k rest root
    }

/// The intermediate walk for an `[[a.b]]` header: same rules as
/// `header_step`, but the recursion keeps ARRAY semantics for the final
/// segment -- routing it through `apply_header` instead gave the last
/// segment table semantics, so `[[a.b]]` created a TABLE at `a.b` and a
/// second header errored as "already defined".
#[partial]
def Toml.array_header_step (k : String) (rest : List String) (root : Toml.Doc) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match root {
        doc_table entries kind =>
            match Map.lookup k entries {
                Option.none => Toml.array_header_create k rest entries kind,
                Option.some child => Toml.array_header_descend k rest child entries kind,
            },
        _ => Result.err "a header path may not descend through a non-table"
    }

#[partial]
def Toml.array_header_create (k : String) (rest : List String) (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match Toml.apply_array_header rest (doc_table BTreeMap.empty kind_implicit) {
        Result.err e => Result.err e,
        Result.ok pr =>
            match pr {
                Pair.pair inner_steps inner =>
                    Result.ok (Pair.pair (List.cons (step_key k) inner_steps) (doc_table (Map.insert k inner entries) kind)),
            },
    }

#[partial]
def Toml.array_header_descend (k : String) (rest : List String) (child : Toml.Doc) (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match child {
        doc_table _ ck =>
            if Toml.kind_is_inline ck
            then Result.err (Toml.inline_immutable_error k)
            else
                match Toml.apply_array_header rest child {
                    Result.err e => Result.err e,
                    Result.ok pr =>
                        match pr {
                            Pair.pair inner_steps inner =>
                                Result.ok (Pair.pair (List.cons (step_key k) inner_steps) (doc_table (Map.insert k inner entries) kind)),
                        },
                },
        doc_array items =>
            match Toml.apply_array_header_in_last rest items {
                Result.err e => Result.err (Toml.array_descend_prefix k e),
                Result.ok pr =>
                    match pr {
                        Pair.pair inner_steps items2 =>
                            Result.ok (Pair.pair (List.cons (step_last k) inner_steps) (doc_table (Map.insert k (doc_array items2) entries) kind)),
                    },
            },
        doc_scalar _ => Result.err (Toml.scalar_descend_error k)
    }

/// Apply an `[[array]]` header's rest-path inside the LAST element of an
/// open array of tables (`[[a.b]]` after `[[a]]` extends `a`'s last
/// element with an array at `b`).
#[partial]
def Toml.apply_array_header_in_last (path : List String) (items : List Toml.Doc) : Result String (Pair (List Toml.PathStep) (List Toml.Doc)) :=
    match items {
        List.empty => Result.err "an array of tables cannot be empty here",
        List.cons x rest =>
            if List.is_empty rest
            then
                match Toml.apply_array_header path x {
                    Result.err e => Result.err e,
                    Result.ok pr =>
                        match pr {
                            Pair.pair inner_steps x2 => Result.ok (Pair.pair inner_steps (List.cons x2 rest)),
                        },
                }
            else
                match Toml.apply_array_header_in_last path rest {
                    Result.err e => Result.err e,
                    Result.ok pr =>
                        match pr {
                            Pair.pair inner_steps rest2 => Result.ok (Pair.pair inner_steps (List.cons x rest2)),
                        },
                }
    }

#[partial]
def Toml.array_header_final (k : String) (root : Toml.Doc) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match root {
        doc_table entries kind =>
            match Map.lookup k entries {
                Option.none =>
                    Result.ok (Pair.pair [step_last k] (doc_table (Map.insert k (doc_array [doc_table BTreeMap.empty kind_explicit]) entries) kind)),
                Option.some child => Toml.array_header_final_existing k child entries kind,
            },
        _ => Result.err "a header path may not descend through a non-table"
    }

#[partial]
def Toml.array_header_final_existing (k : String) (child : Toml.Doc) (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind) : Result String (Pair (List Toml.PathStep) Toml.Doc) :=
    match child {
        doc_array items =>
            Result.ok (Pair.pair [step_last k] (doc_table (Map.insert k (doc_array (List.append items [doc_table BTreeMap.empty kind_explicit])) entries) kind)),
        doc_table _ _ => Result.err (Toml.array_over_table_error k),
        doc_scalar _ => Result.err (Toml.scalar_descend_error k)
    }

/// Insert a `key = value` pair at the table `steps` addresses (the last
/// header's target), `path` being the pair's own dotted key.
#[partial]
def Toml.insert_kv (steps : List Toml.PathStep) (path : List String) (value : Toml.Value) (root : Toml.Doc) : Result String Toml.Doc :=
    match steps {
        List.empty => Toml.kv_insert_here path value root,
        List.cons s rest => Toml.kv_step s rest path value root
    }

/// One step down the current-table path. These steps were produced by a
/// successful header application, so a miss here is a defensive error.
#[partial]
def Toml.kv_step (s : Toml.PathStep) (rest : List Toml.PathStep) (path : List String) (value : Toml.Value) (root : Toml.Doc) : Result String Toml.Doc :=
    match root {
        doc_table entries kind =>
            match s {
                step_key k =>
                    match Map.lookup k entries {
                        Option.none => Result.err (Toml.lost_current_error k),
                        Option.some child =>
                            match Toml.insert_kv rest path value child {
                                Result.err e => Result.err e,
                                Result.ok child2 => Result.ok (doc_table (Map.insert k child2 entries) kind),
                            },
                    },
                step_last k =>
                    match Map.lookup k entries {
                        Option.none => Result.err (Toml.lost_current_error k),
                        Option.some child =>
                            match child {
                                doc_array items =>
                                    match Toml.insert_kv_in_last rest path value items {
                                        Result.err e => Result.err e,
                                        Result.ok items2 => Result.ok (doc_table (Map.insert k (doc_array items2) entries) kind),
                                    },
                                _ => Result.err (Toml.lost_current_error k),
                            },
                    },
            },
        _ => Result.err (Toml.lost_current_error "")
    }

/// Continue the insertion inside the LAST element of an open array.
#[partial]
def Toml.insert_kv_in_last (steps : List Toml.PathStep) (path : List String) (value : Toml.Value) (items : List Toml.Doc) : Result String (List Toml.Doc) :=
    match items {
        List.empty => Result.err "an array of tables cannot be empty here",
        List.cons x rest =>
            if List.is_empty rest
            then
                match Toml.insert_kv steps path value x {
                    Result.err e => Result.err e,
                    Result.ok x2 => Result.ok (List.cons x2 rest),
                }
            else
                match Toml.insert_kv_in_last steps path value rest {
                    Result.err e => Result.err e,
                    Result.ok rest2 => Result.ok (List.cons x rest2),
                }
    }

/// Insert `path = value` into the current table itself.
#[partial]
def Toml.kv_insert_here (path : List String) (value : Toml.Value) (root : Toml.Doc) : Result String Toml.Doc :=
    match root {
        doc_table entries kind =>
            match path {
                List.empty => Result.err "a key must be named",
                List.cons k rest =>
                    if List.is_empty rest
                    then Toml.kv_final k value entries kind
                    else Toml.kv_step_path k rest value entries kind,
            },
        _ => Result.err "a key-value pair appeared outside a table"
    }

/// The pair's final key: it must be absent. A duplicate is reported
/// rather than last-wins — the spec forbids it outright.
#[partial]
def Toml.kv_final (k : String) (value : Toml.Value) (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind) : Result String Toml.Doc :=
    match Map.lookup k entries {
        Option.some _ => Result.err (Toml.duplicate_key_error k),
        Option.none => Result.ok (doc_table (Map.insert k (Toml.value_to_doc value) entries) kind),
    }

/// A dotted key's intermediate: it may be absent (created `kind_dotted`)
/// or an existing dotted table — passing through a header-created,
/// inline or scalar key is the spec's "using dotted keys to redefine
/// tables already defined in [table] form is not allowed".
#[partial]
def Toml.kv_step_path (k : String) (rest : List String) (value : Toml.Value) (entries : BTreeMap String Toml.Doc) (kind : Toml.TableKind) : Result String Toml.Doc :=
    match Map.lookup k entries {
        Option.none =>
            match Toml.kv_insert_here rest value (doc_table BTreeMap.empty kind_dotted) {
                Result.err e => Result.err e,
                Result.ok inner => Result.ok (doc_table (Map.insert k inner entries) kind),
            },
        Option.some child =>
            match child {
                doc_table _ ck =>
                    if Toml.kind_is_dotted ck
                    then
                        match Toml.kv_insert_here rest value child {
                            Result.err e => Result.err e,
                            Result.ok child2 => Result.ok (doc_table (Map.insert k child2 entries) kind),
                        }
                    else Result.err (Toml.dotted_conflict_error k),
                _ => Result.err (Toml.dotted_conflict_error k)
            },
    }

/// A value's doc form: an inline TABLE is an immutable doc table; every
/// other value (static arrays included) is a scalar.
#[partial]
def Toml.value_to_doc (v : Toml.Value) : Toml.Doc :=
    match v {
        table t => doc_table (Toml.value_table_to_doc t) kind_inline,
        _ => doc_scalar v
    }

/// A parsed inline table's entries as doc entries (each nested table is
/// itself inline/immutable).
#[partial]
def Toml.value_table_to_doc (t : BTreeMap String Toml.Value) : BTreeMap String Toml.Doc :=
    Toml.value_table_go (BTreeMap.to_list t) BTreeMap.empty

#[partial]
def Toml.value_table_go (pairs : List (Pair String Toml.Value)) (acc : BTreeMap String Toml.Doc) : BTreeMap String Toml.Doc :=
    match pairs {
        List.empty => acc,
        List.cons p rest =>
            match p {
                Pair.pair k v => Toml.value_table_go rest (Map.insert k (Toml.value_to_doc v) acc),
            }
    }

/// The finished tree as a public value.
#[partial]
def Toml.doc_to_value (d : Toml.Doc) : Toml.Value :=
    match d {
        doc_table entries _ => table (Toml.doc_table_to_value entries),
        doc_array items => array (Toml.doc_items_to_values items),
        doc_scalar v => v
    }

#[partial]
def Toml.doc_table_to_value (entries : BTreeMap String Toml.Doc) : BTreeMap String Toml.Value :=
    Toml.doc_entries_go (BTreeMap.to_list entries) BTreeMap.empty

#[partial]
def Toml.doc_entries_go (pairs : List (Pair String Toml.Doc)) (acc : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
    match pairs {
        List.empty => acc,
        List.cons p rest =>
            match p {
                Pair.pair k d => Toml.doc_entries_go rest (Map.insert k (Toml.doc_to_value d) acc),
            }
    }

#[partial]
def Toml.doc_items_to_values (items : List Toml.Doc) : List Toml.Value :=
    match items {
        List.empty => List.empty,
        List.cons x rest => List.cons (Toml.doc_to_value x) (Toml.doc_items_to_values rest),
    }

/// The finished document's root entries as the public table.
def Toml.doc_root_table (root : Toml.Doc) : BTreeMap String Toml.Value :=
    match Toml.doc_to_value root {
        table t => t,
        _ => BTreeMap.empty
    }

def Toml.kind_is_implicit (k : Toml.TableKind) : Bool :=
    match k { kind_implicit => true, _ => false }

def Toml.kind_is_dotted (k : Toml.TableKind) : Bool :=
    match k { kind_dotted => true, _ => false }

def Toml.kind_is_inline (k : Toml.TableKind) : Bool :=
    match k { kind_inline => true, _ => false }

// ─── Assembly error messages ───

def Toml.inline_immutable_error (k : String) : String :=
    String.concat "the inline table at `" (String.concat k "` cannot be modified or extended")

def Toml.header_redefined_error (k : String) : String :=
    String.concat "the table at `" (String.concat k "` is already defined")

def Toml.dotted_redefined_error (k : String) : String :=
    String.concat "the dotted-key table at `" (String.concat k "` cannot be redefined by a header")

def Toml.header_over_array_error (k : String) : String :=
    String.concat "[[" (String.concat k "]] is already an array of tables; a [table] header cannot extend it")

def Toml.array_over_table_error (k : String) : String :=
    String.concat "[" (String.concat k "] is already a table; an [[array]] header cannot extend it")

def Toml.scalar_descend_error (k : String) : String :=
    String.concat "the key `" (String.concat k "` already has a value, not a table")

def Toml.dotted_conflict_error (k : String) : String :=
    String.concat "the dotted key `" (String.concat k "` conflicts with an existing key")

def Toml.duplicate_key_error (k : String) : String :=
    String.concat "duplicate key: `" (String.concat k "`")

def Toml.lost_current_error (k : String) : String :=
    String.concat "the current table at `" (String.concat k "` vanished mid-document")

def Toml.inline_duplicate_error (k : String) : String :=
    String.concat "duplicate key in inline table: `" (String.concat k "`")

def Toml.array_descend_prefix (k : String) (e : String) : String :=
    String.concat "descending into the array of tables `" (String.concat (String.concat k "`: ") e)

// ─── The line fold ───

def Toml.fold_line (acc : Toml.Asm) (line : Toml.Line) : Toml.Asm :=
    match acc {
        asm_error m => asm_error m,
        asm_state steps root =>
            match line {
                header path => Toml.fold_header steps root path,
                array_header path => Toml.fold_array_header steps root path,
                kv path value => Toml.fold_kv steps root path value,
            }
    }

def Toml.fold_header (steps : List Toml.PathStep) (root : Toml.Doc) (path : List String) : Toml.Asm :=
    match Toml.apply_header path root {
        Result.err e => asm_error e,
        Result.ok pr =>
            match pr {
                Pair.pair steps2 root2 => asm_state steps2 root2,
            },
    }

def Toml.fold_array_header (steps : List Toml.PathStep) (root : Toml.Doc) (path : List String) : Toml.Asm :=
    match Toml.apply_array_header path root {
        Result.err e => asm_error e,
        Result.ok pr =>
            match pr {
                Pair.pair steps2 root2 => asm_state steps2 root2,
            },
    }

def Toml.fold_kv (steps : List Toml.PathStep) (root : Toml.Doc) (path : List String) (value : Toml.Value) : Toml.Asm :=
    match Toml.insert_kv steps path value root {
        Result.err e => asm_error e,
        Result.ok root2 => asm_state steps root2,
    }

#[partial]
def Toml.fold_lines (acc : Toml.Asm) (lines : List Toml.Line) : Toml.Asm :=
    match lines {
        List.empty => acc,
        List.cons l rest => Toml.fold_lines (Toml.fold_line acc l) rest
    }

/// Assemble the parsed lines into the root table, or the reason the
/// document's table structure is invalid.
def Toml.assemble (lines : List Toml.Line) : Result String (BTreeMap String Toml.Value) :=
    match Toml.fold_lines (asm_state List.empty (doc_table BTreeMap.empty kind_explicit)) lines {
        asm_error m => Result.err m,
        asm_state _ root => Result.ok (Toml.doc_root_table root)
    }

// ─── Parser: top-level ───

/// The UTF-8 BOM, which a Windows-authored document may carry and the
/// spec says to ignore.
def Toml.bom : String := String.from_list [239u8, 187u8, 191u8]

def Toml.strip_bom (s : String) : String :=
    if String.starts_with Toml.bom s then String.drop 3 s else s

def Toml.assemble_result (r : Result String (BTreeMap String Toml.Value)) : Result Toml.ParseError (BTreeMap String Toml.Value) :=
    match r {
        Result.err e => err (Toml.ParseError.generic e),
        Result.ok t => ok t
    }

/// Main parse function: parse a full TOML document into its root table.
#[partial]
pub def Toml.parse (s : String) : Result Toml.ParseError (BTreeMap String Toml.Value) :=
    match Toml.document (Toml.strip_bom s) {
        success rem lines =>
            if is_empty rem
            then Toml.assemble_result (Toml.assemble lines)
            else err (Toml.ParseError.generic "unexpected trailing input"),
        fail e => err (Toml.from_parse_error e)
    }

// ─── Serializer ───

/// One hex digit (0-15) as a byte.
def Toml.hex_digit_byte (n : U8) : U8 :=
    if U8.lt n 10u8 then U8.add n 48u8 else U8.add n 87u8

/// A raw control byte (or DEL) as `\u00XX`: the parser rejects those
/// unescaped, so passing one through would break the round trip.
def Toml.control_escape (b : U8) : String :=
    let hi : U8 := U8.div b 16u8 in
    let lo : U8 := U8.sub b (U8.mul hi 16u8) in
    String.concat "\\u00" (String.from_list [Toml.hex_digit_byte hi, Toml.hex_digit_byte lo])

#[partial]
def Toml.escape_char (c : String) : String :=
    if String.beq "\"" c then "\\\""
    else if String.beq "\\" c then "\\\\"
    else if String.beq "\b" c then "\\b"
    else if String.beq "\t" c then "\\t"
    else if String.beq "\n" c then "\\n"
    else if String.beq "\f" c then "\\f"
    else if String.beq "\r" c then "\\r"
    else Toml.escape_other c

/// The catch-all: a single raw control byte (or DEL) becomes `\u00XX`;
/// every other character — all multi-byte UTF-8 included — passes
/// through.
def Toml.escape_other (c : String) : String :=
    match String.to_list c {
        List.cons b rest => Toml.escape_other_byte b rest c,
        List.empty => c,
    }

def Toml.escape_other_byte (b : U8) (rest : List U8) (c : String) : String :=
    match rest {
        List.empty =>
            if U8.lt b 32u8 then Toml.control_escape b
            else if U8.beq b 127u8 then Toml.control_escape b
            else c,
        List.cons _ _ => c,
    }

/// Escape a string for a basic-string rendering. Accumulates pieces in
/// reverse and joins once, stepping one WHOLE UTF-8 character at a time
/// — a one-byte step would split a multi-byte character and silently
/// truncate the output (the same defect `lang/json.mo`'s escape_string
/// documents).
#[partial]
def Toml.escape_string (input : String) : String :=
    String.concat_list (Toml.escape_pieces input List.empty)

#[partial]
def Toml.escape_pieces (input : String) (acc : List String) : List String :=
    match String.get input 0 {
        Option.none => List.reverse acc,
        Option.some _ =>
            let width : I64 := utf8_char_width input in
            let ch : String := String.slice input 0 width in
            Toml.escape_pieces (String.drop width input) (List.cons (Toml.escape_char ch) acc),
    }

def Toml.string_to_string (s : String) : String :=
    String.concat "\"" (String.concat (Toml.escape_string s) "\"")

def Toml.bool_to_string (b : Bool) : String :=
    if b then "true" else "false"

/// A float's TOML spelling. `F64.to_string` renders 3.0 as "3" (an
/// INTEGER on re-read), NaN as "NaN", and never an exponent — so the
/// rendering is post-processed: the non-finite spellings are remapped,
/// and a finite rendering with no `.`/`e`/`E` gains a `.0`.
def Toml.float_to_string (f : F64) : String :=
    let s : String := F64.to_string f in
    if String.beq s "inf" then "inf"
    else if String.beq s "-inf" then "-inf"
    else if String.beq s "NaN" then "nan"
    else if String.contains s "." then s
    else if String.contains s "e" then s
    else if String.contains s "E" then s
    else String.concat s ".0"

/// A key's TOML spelling: bare when non-empty and every character is a
/// bare-key character, else a quoted basic string — so keys with
/// spaces, dots or quotes in them round-trip.
#[partial]
def Toml.key_to_string (k : String) : String :=
    if Toml.key_is_bare k then k else Toml.string_to_string k

def Toml.key_is_bare (k : String) : Bool :=
    Bool.not (String.is_empty k) && Toml.all_bare_chars (Toml.string_chars k)

#[partial]
def Toml.all_bare_chars (cs : List String) : Bool :=
    match cs {
        List.empty => true,
        List.cons c rest => if Toml.is_key_char c then Toml.all_bare_chars rest else false
    }

/// Serialize any value to its inline spelling. A `table` renders as an inline
/// table (`{ k = v }`), which is reached two ways: as an element of an array,
/// and as an entry of an `[[x]]` element (`Toml.render_array_elem` renders ALL
/// of an element's entries inline, since a nested `[x.y]` header under an array
/// element is the one thing the parser refuses).
///
/// Public so a writer that owns its own key ORDER (build/src/lock.mo renders
/// `mote.lock` name-first, where `Toml.to_string` walks keys sorted) still
/// gets this module's escaping, and so reads back what it wrote.
#[partial]
pub def Toml.value_to_string (v : Toml.Value) : String :=
    match v {
        string s => Toml.string_to_string s,
        integer n => I64.to_string n,
        float f => Toml.float_to_string f,
        boolean b => Toml.bool_to_string b,
        datetime s => s,
        array a => Toml.array_to_string a,
        table t => Toml.inline_table_to_string t
    }

/// `{ a = 1, b = "x" }`, or `{}` for an empty one -- spelled without inner
/// padding so the empty case does not render as `{  }`.
#[partial]
def Toml.inline_table_to_string (t : BTreeMap String Toml.Value) : String :=
    toml_inline_table_body (BTreeMap.to_list t)

#[partial]
def toml_inline_table_body (pairs : List (Pair String Toml.Value)) : String :=
    if List.is_empty pairs
    then "{}"
    else String.concat "{ " (String.concat (List.intercalate ", " (List.map Toml.kv_line_to_string pairs)) " }")

#[partial]
def Toml.array_to_string (a : List Toml.Value) : String :=
    String.concat "[" (String.concat (List.intercalate "," (List.map Toml.value_to_string a)) "]")

def Toml.is_table (v : Toml.Value) : Bool :=
    match v { table _ => true, _ => false }

/// A NON-EMPTY array whose every element is a table -- the shape `[[k]]`
/// headers produce, and the shape they must be rendered back as if a
/// `mote.lock` is to round-trip through the spelling it was written in.
///
/// An EMPTY array is deliberately not one of these: it carries no evidence
/// that it was ever an array of tables, and `[]` is the honest rendering.
def Toml.is_table_array (v : Toml.Value) : Bool :=
    match v {
        array a => toml_all_tables a,
        _ => false
    }

#[partial]
def toml_all_tables (a : List Toml.Value) : Bool :=
    match a {
        List.empty => false,
        List.cons x tl => if Toml.is_table x then toml_all_tables_rest tl else false
    }

/// The same walk, except an empty REST means "every element so far was a
/// table" rather than "the array was empty". Two defs because the empty list
/// answers differently at the head than in the tail.
#[partial]
def toml_all_tables_rest (a : List Toml.Value) : Bool :=
    match a {
        List.empty => true,
        List.cons x tl => if Toml.is_table x then toml_all_tables_rest tl else false
    }

def Toml.pair_is_scalar (p : Pair String Toml.Value) : Bool :=
    match p { Pair.pair _ v => toml_is_inline_value v }

def toml_is_inline_value (v : Toml.Value) : Bool :=
    if Toml.is_table v then false else Bool.not (Toml.is_table_array v)

def Toml.pair_is_table (p : Pair String Toml.Value) : Bool :=
    match p { Pair.pair _ v => Toml.is_table v }

def Toml.pair_is_table_array (p : Pair String Toml.Value) : Bool :=
    match p { Pair.pair _ v => Toml.is_table_array v }

def Toml.scalar_entries (pairs : List (Pair String Toml.Value)) : List (Pair String Toml.Value) :=
    List.filter Toml.pair_is_scalar pairs

def Toml.table_entries (pairs : List (Pair String Toml.Value)) : List (Pair String Toml.Value) :=
    List.filter Toml.pair_is_table pairs

def Toml.table_array_entries (pairs : List (Pair String Toml.Value)) : List (Pair String Toml.Value) :=
    List.filter Toml.pair_is_table_array pairs

def Toml.kv_line_to_string (p : Pair String Toml.Value) : String :=
    match p { Pair.pair k v => String.concat (Toml.key_to_string k) (String.concat " = " (Toml.value_to_string v)) }

def Toml.render_header (path : List String) : String :=
    if List.is_empty path
    then ""
    else String.concat "[" (String.concat (List.intercalate "." (List.map Toml.key_to_string path)) "]\n")

def Toml.render_array_header (path : List String) : String :=
    if List.is_empty path
    then ""
    else String.concat "[[" (String.concat (List.intercalate "." (List.map Toml.key_to_string path)) "]]\n")

def Toml.render_body (header_str : String) (scalars : List (Pair String Toml.Value)) : String :=
    if List.is_empty scalars
    then header_str
    else String.concat header_str (String.concat (List.intercalate "\n" (List.map Toml.kv_line_to_string scalars)) "\n")

/// Serialize one table (and everything nested under it) at `path` — root-level
/// scalar/array keys first, then a depth-first walk of nested tables emitting
/// `[dotted.path]` headers followed by their own scalar keys.
#[partial]
def Toml.render_table (path : List String) (t : BTreeMap String Toml.Value) : String :=
    let pairs := BTreeMap.to_list t in
    let scalars := Toml.scalar_entries pairs in
    let tables := Toml.table_entries pairs in
    let table_arrays := Toml.table_array_entries pairs in
    let body := Toml.render_body (Toml.render_header path) scalars in
    String.concat body (String.concat (Toml.render_tables path tables) (Toml.render_table_arrays path table_arrays))

/// `[[k]]` sections, one per element. Emitted after this table's `[k]`
/// sub-sections so that every header's own keys stay under it -- the order
/// between the two classes is free, but it has to be fixed to round-trip.
#[partial]
def Toml.render_table_arrays (path : List String) (entries : List (Pair String Toml.Value)) : String :=
    match entries {
        List.empty => "",
        List.cons p rest => String.concat (Toml.render_one_table_array path p) (Toml.render_table_arrays path rest)
    }

#[partial]
def Toml.render_one_table_array (path : List String) (p : Pair String Toml.Value) : String :=
    match p {
        Pair.pair k v => Toml.render_array_elems (List.append path [k]) (toml_array_value v)
    }

#[partial]
def Toml.render_array_elems (path : List String) (elems : List Toml.Value) : String :=
    match elems {
        List.empty => "",
        List.cons e rest => String.concat (Toml.render_array_elem path e) (Toml.render_array_elems path rest)
    }

/// One `[[path]]` element. ALL of its entries render inline, sub-tables
/// included, because a `[path.sub]` header under an array element is exactly
/// what the assembler refuses to read back.
#[partial]
def Toml.render_array_elem (path : List String) (e : Toml.Value) : String :=
    match e {
        table t => Toml.render_body (Toml.render_array_header path) (BTreeMap.to_list t),
        _ => ""
    }

#[partial]
def Toml.render_tables (path : List String) (tables : List (Pair String Toml.Value)) : String :=
    match tables {
        List.empty => "",
        List.cons p rest => String.concat (Toml.render_one_table path p) (Toml.render_tables path rest)
    }

#[partial]
def Toml.render_one_table (path : List String) (p : Pair String Toml.Value) : String :=
    match p {
        Pair.pair k v => Toml.render_one_table_value (List.append path [k]) v
    }

#[partial]
def Toml.render_one_table_value (path : List String) (v : Toml.Value) : String :=
    match v {
        table t => Toml.render_table path t,
        _ => ""
    }

/// Serialize a root table to a full TOML document.
#[partial]
pub def Toml.to_string (root : BTreeMap String Toml.Value) : String :=
    Toml.render_table List.empty root

// ─── Show instance ───

pub instance Show Toml.Value {
    def show (v : Toml.Value) : String := Toml.value_to_string v
}

// ─── Construction helpers ───

pub def Toml.make_string (s : String) : Toml.Value := string s
pub def Toml.make_integer (n : I64) : Toml.Value := integer n
pub def Toml.make_float (f : F64) : Toml.Value := float f
pub def Toml.make_boolean (b : Bool) : Toml.Value := boolean b
pub def Toml.make_datetime (s : String) : Toml.Value := datetime s
pub def Toml.make_array (a : List Toml.Value) : Toml.Value := array a
pub def Toml.make_table (t : BTreeMap String Toml.Value) : Toml.Value := table t

// ─── Type checkers ───

def Toml.is_string (v : Toml.Value) : Bool :=
    match v { string _ => true, _ => false }

def Toml.is_integer (v : Toml.Value) : Bool :=
    match v { integer _ => true, _ => false }

def Toml.is_float (v : Toml.Value) : Bool :=
    match v { float _ => true, _ => false }

def Toml.is_boolean (v : Toml.Value) : Bool :=
    match v { boolean _ => true, _ => false }

def Toml.is_datetime (v : Toml.Value) : Bool :=
    match v { datetime _ => true, _ => false }

def Toml.is_array (v : Toml.Value) : Bool :=
    match v { array _ => true, _ => false }

// (Toml.is_table is defined above, in the Serializer section, where it's first needed.)

// ─── Accessors ───

pub def Toml.get_string (v : Toml.Value) : Result String String :=
    match v { string s => ok s, _ => err "expected string" }

pub def Toml.get_integer (v : Toml.Value) : Result String I64 :=
    match v { integer n => ok n, _ => err "expected integer" }

pub def Toml.get_float (v : Toml.Value) : Result String F64 :=
    match v { float f => ok f, _ => err "expected float" }

pub def Toml.get_boolean (v : Toml.Value) : Result String Bool :=
    match v { boolean b => ok b, _ => err "expected boolean" }

pub def Toml.get_datetime (v : Toml.Value) : Result String String :=
    match v { datetime s => ok s, _ => err "expected datetime" }

pub def Toml.get_array (v : Toml.Value) : Result String (List Toml.Value) :=
    match v { array a => ok a, _ => err "expected array" }

pub def Toml.get_table (v : Toml.Value) : Result String (BTreeMap String Toml.Value) :=
    match v { table t => ok t, _ => err "expected table" }

// ─── Table manipulation ───

pub def Toml.table_get (key : String) (t : BTreeMap String Toml.Value) : Option Toml.Value :=
    Map.lookup key t

def Toml.table_set (key : String) (value : Toml.Value) (t : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
    Map.insert key value t

def Toml.table_delete (key : String) (t : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
    Map.delete key t

/// The table currently at `key`, or empty when the key is absent or holds
/// something else. The assembler's lookup helper, kept for callers walking
/// a parsed document.
def Toml.sub_table (key : String) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
    toml_sub_table_lookup (Map.lookup key root)

def toml_sub_table_lookup (found : Option Toml.Value) : BTreeMap String Toml.Value :=
    match found {
        some v => toml_sub_table_value v,
        none => BTreeMap.empty
    }

def toml_sub_table_value (v : Toml.Value) : BTreeMap String Toml.Value :=
    match v {
        table t => t,
        _ => BTreeMap.empty
    }

/// The array currently at `key`, or empty when the key is absent or holds
/// something else. The array counterpart of `Toml.sub_table`.
pub def Toml.array_at (key : String) (root : BTreeMap String Toml.Value) : List Toml.Value :=
    toml_array_at_lookup (Map.lookup key root)

def toml_array_at_lookup (found : Option Toml.Value) : List Toml.Value :=
    match found {
        some v => toml_array_value v,
        none => List.empty
    }

def toml_array_value (v : Toml.Value) : List Toml.Value :=
    match v {
        array a => a,
        _ => List.empty
    }

// ─── Tests: parser — scalars ───

#[test]
def test_parse_string_kv : Bool :=
    match Toml.parse "name = \"example\"" {
        ok t => toml_table_lookup_eq "name" t (string "example"),
        err _ => false
    }

#[test]
def test_parse_integer_kv : Bool :=
    match Toml.parse "n = 42" {
        ok t => toml_table_lookup_eq "n" t (integer 42),
        err _ => false
    }

#[test]
def test_parse_negative_integer_kv : Bool :=
    match Toml.parse "n = -42" {
        ok t => toml_table_lookup_eq "n" t (integer (I64.neg 42)),
        err _ => false
    }

#[test]
def test_parse_bool_kv : Bool :=
    match Toml.parse "a = true\nb = false" {
        ok t => toml_table_lookup_eq "a" t (boolean true) && toml_table_lookup_eq "b" t (boolean false),
        err _ => false
    }

#[test]
def test_parse_string_with_escapes : Bool :=
    match Toml.parse "s = \"a\\nb\\tc\\\"d\"" {
        ok t => toml_table_lookup_eq "s" t (string "a\nb\tc\"d"),
        err _ => false
    }

def toml_table_lookup_eq (key : String) (t : BTreeMap String Toml.Value) (expected : Toml.Value) : Bool :=
    match Map.lookup key t {
        some v => Toml.beq v expected,
        none => false
    }

def toml_table_lookup_missing (key : String) (t : BTreeMap String Toml.Value) : Bool :=
    match Map.lookup key t {
        some _ => false,
        none => true
    }

// ─── Tests: parser — integers (full grammar) ───

#[test]
def test_parse_plus_signed_integer : Bool :=
    match Toml.parse "n = +42" {
        ok t => toml_table_lookup_eq "n" t (integer 42),
        err _ => false
    }

#[test]
def test_parse_zero : Bool :=
    match Toml.parse "n = 0" {
        ok t => toml_table_lookup_eq "n" t (integer 0),
        err _ => false
    }

#[test]
def test_parse_negative_zero : Bool :=
    match Toml.parse "n = -0" {
        ok t => toml_table_lookup_eq "n" t (integer 0),
        err _ => false
    }

/// `_` grouping, including the `1_0` row that parsec's `number` read as
/// 190 (its digit fold treats `_` as the digit 9).
#[test]
def test_parse_underscored_integer : Bool :=
    match Toml.parse "a = 1_000\nb = 1_0\nc = 1_2_3" {
        ok t =>
            toml_table_lookup_eq "a" t (integer 1000)
            && toml_table_lookup_eq "b" t (integer 10)
            && toml_table_lookup_eq "c" t (integer 123),
        err _ => false
    }

#[test]
def test_parse_hex_integer : Bool :=
    match Toml.parse "n = 0xDEADBEEF" {
        ok t => toml_table_lookup_eq "n" t (integer 3735928559),
        err _ => false
    }

#[test]
def test_parse_hex_lowercase_and_leading_zeros : Bool :=
    match Toml.parse "n = 0xdeadBEEF\nm = 0x00000001" {
        ok t => toml_table_lookup_eq "n" t (integer 3735928559) && toml_table_lookup_eq "m" t (integer 1),
        err _ => false
    }

#[test]
def test_parse_octal_integer : Bool :=
    match Toml.parse "n = 0o755" {
        ok t => toml_table_lookup_eq "n" t (integer 493),
        err _ => false
    }

#[test]
def test_parse_binary_integer : Bool :=
    match Toml.parse "n = 0b1101" {
        ok t => toml_table_lookup_eq "n" t (integer 13),
        err _ => false
    }

#[test]
def test_parse_i64_min : Bool :=
    match Toml.parse "n = -9223372036854775808" {
        ok t => toml_table_lookup_eq "n" t (integer (I64.sub (I64.neg 9223372036854775807) 1)),
        err _ => false
    }

#[test]
def test_parse_i64_max : Bool :=
    match Toml.parse "n = 9223372036854775807" {
        ok t => toml_table_lookup_eq "n" t (integer 9223372036854775807),
        err _ => false
    }

#[test]
def test_parse_integer_overflow_is_error : Bool :=
    match Toml.parse "n = 9223372036854775808" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_leading_zero_is_error : Bool :=
    match Toml.parse "n = 01" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_signed_radix_is_error : Bool :=
    match Toml.parse "n = -0x1" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_bare_underscore_is_error : Bool :=
    match Toml.parse "n = _1" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_trailing_underscore_is_error : Bool :=
    match Toml.parse "n = 1_" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_double_underscore_is_error : Bool :=
    match Toml.parse "n = 1__0" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_empty_radix_is_error : Bool :=
    match Toml.parse "n = 0x" {
        ok _ => false,
        err _ => true
    }

// ─── Tests: parser — floats ───

/// A float parses to its VALUE now — this used to be the explicit
/// "floats are unsupported" error row.
#[test]
def test_parse_float : Bool :=
    match Toml.parse "x = 1.5" {
        ok t => toml_table_lookup_eq "x" t (float 1.5f64),
        err _ => false
    }

#[test]
def test_parse_float_pi : Bool :=
    match Toml.parse "x = 3.14" {
        ok t => toml_table_lookup_eq "x" t (float 3.14f64),
        err _ => false
    }

#[test]
def test_parse_float_exponent : Bool :=
    match Toml.parse "a = 1e6\nb = 5e+22\nc = -2E-2\nd = 1e06" {
        ok t =>
            toml_table_lookup_eq "a" t (float 1000000.0f64)
            && toml_table_lookup_eq "b" t (float 50000000000000000000000.0f64)
            && toml_table_lookup_eq "c" t (float (-0.02f64))
            && toml_table_lookup_eq "d" t (float 1000000.0f64),
        err _ => false
    }

#[test]
def test_parse_float_underscored : Bool :=
    match Toml.parse "x = 1_000.5" {
        ok t => toml_table_lookup_eq "x" t (float 1000.5f64),
        err _ => false
    }

#[test]
def test_parse_float_inf : Bool :=
    match Toml.parse "a = inf\nb = -inf\nc = +inf" {
        ok t =>
            toml_table_lookup_eq "a" t (float (1.0f64 / 0.0f64))
            && toml_table_lookup_eq "b" t (float (0.0f64 - (1.0f64 / 0.0f64)))
            && toml_table_lookup_eq "c" t (float (1.0f64 / 0.0f64)),
        err _ => false
    }

/// NaN never equals itself (IEEE), so the assertion is on the RENDERING —
/// the same reason `Toml.beq` documents.
#[test]
def test_parse_float_nan : Bool :=
    match Toml.parse "a = nan\nb = +nan\nc = -nan" {
        ok t =>
            match Toml.table_get "a" t {
                some v => match Toml.get_float v {
                    ok f => match Toml.table_get "b" t {
                        some v2 => match Toml.get_float v2 {
                            ok f2 => F64.to_string f == "NaN" && F64.to_string f2 == "NaN",
                            err _ => false,
                        },
                        none => false,
                    },
                    err _ => false,
                },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_float_no_fraction_or_exponent_is_error : Bool :=
    match Toml.parse "x = 1." {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_float_leading_dot_is_error : Bool :=
    match Toml.parse "x = .5" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_float_empty_exponent_is_error : Bool :=
    match Toml.parse "x = 1e" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_float_trailing_underscore_is_error : Bool :=
    match Toml.parse "x = 1.0_" {
        ok _ => false,
        err _ => true
    }

// ─── Tests: parser — date-times ───

/// Offset date-time, preserved verbatim (the value IS the spelling).
#[test]
def test_parse_datetime_offset_z : Bool :=
    match Toml.parse "odt = 1979-05-27T07:32:00Z" {
        ok t => toml_table_lookup_eq "odt" t (datetime "1979-05-27T07:32:00Z"),
        err _ => false
    }

#[test]
def test_parse_datetime_offset_numeric : Bool :=
    match Toml.parse "odt = 1979-05-27T00:32:00-07:00" {
        ok t => toml_table_lookup_eq "odt" t (datetime "1979-05-27T00:32:00-07:00"),
        err _ => false
    }

#[test]
def test_parse_datetime_lowercase_t_and_z : Bool :=
    match Toml.parse "odt = 1979-05-27t07:32:00z" {
        ok t => toml_table_lookup_eq "odt" t (datetime "1979-05-27t07:32:00z"),
        err _ => false
    }

#[test]
def test_parse_datetime_space_delimiter : Bool :=
    match Toml.parse "odt = 1979-05-27 07:32:00Z" {
        ok t => toml_table_lookup_eq "odt" t (datetime "1979-05-27 07:32:00Z"),
        err _ => false
    }

#[test]
def test_parse_datetime_secfrac : Bool :=
    match Toml.parse "odt = 1979-05-27T00:32:00.999999-07:00" {
        ok t => toml_table_lookup_eq "odt" t (datetime "1979-05-27T00:32:00.999999-07:00"),
        err _ => false
    }

#[test]
def test_parse_local_datetime : Bool :=
    match Toml.parse "ldt = 1979-05-27T07:32:00" {
        ok t => toml_table_lookup_eq "ldt" t (datetime "1979-05-27T07:32:00"),
        err _ => false
    }

#[test]
def test_parse_local_date : Bool :=
    match Toml.parse "ld = 1979-05-27" {
        ok t => toml_table_lookup_eq "ld" t (datetime "1979-05-27"),
        err _ => false
    }

#[test]
def test_parse_local_date_with_trailing_comment : Bool :=
    match Toml.parse "ld = 1979-05-27 # a comment" {
        ok t => toml_table_lookup_eq "ld" t (datetime "1979-05-27"),
        err _ => false
    }

#[test]
def test_parse_local_time : Bool :=
    match Toml.parse "lt = 07:32:00" {
        ok t => toml_table_lookup_eq "lt" t (datetime "07:32:00"),
        err _ => false
    }

#[test]
def test_parse_local_time_secfrac : Bool :=
    match Toml.parse "lt = 00:32:00.999999" {
        ok t => toml_table_lookup_eq "lt" t (datetime "00:32:00.999999"),
        err _ => false
    }

#[test]
def test_parse_leap_second : Bool :=
    match Toml.parse "odt = 1979-05-27T07:32:60Z" {
        ok t => toml_table_lookup_eq "odt" t (datetime "1979-05-27T07:32:60Z"),
        err _ => false
    }

#[test]
def test_parse_leap_day : Bool :=
    match Toml.parse "d = 2020-02-29" {
        ok t => toml_table_lookup_eq "d" t (datetime "2020-02-29"),
        err _ => false
    }

#[test]
def test_parse_non_leap_day_is_error : Bool :=
    match Toml.parse "d = 2019-02-29" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_bad_month_is_error : Bool :=
    match Toml.parse "d = 1979-13-01" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_hour_24_is_error : Bool :=
    match Toml.parse "lt = 24:00:00" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_bad_offset_is_error : Bool :=
    match Toml.parse "odt = 1979-05-27T07:32:00+25:00" {
        ok _ => false,
        err _ => true
    }

/// A `1979`-shaped value is an INTEGER, not a truncated date — the
/// date-time scan fails (no `-` follows) and the integer parser takes it.
#[test]
def test_parse_year_alone_is_an_integer : Bool :=
    match Toml.parse "y = 1979" {
        ok t => toml_table_lookup_eq "y" t (integer 1979),
        err _ => false
    }

// ─── Tests: parser — strings (all four kinds) ───

#[test]
def test_parse_literal_string : Bool :=
    match Toml.parse "s = 'no escapes \\n here'" {
        ok t => toml_table_lookup_eq "s" t (string "no escapes \\n here"),
        err _ => false
    }

#[test]
def test_parse_empty_strings : Bool :=
    match Toml.parse "a = ''\nb = \"\"" {
        ok t => toml_table_lookup_eq "a" t (string "") && toml_table_lookup_eq "b" t (string ""),
        err _ => false
    }

#[test]
def test_parse_multiline_basic_first_newline_trimmed : Bool :=
    match Toml.parse "s = \"\"\"\nline one\nline two\"\"\"" {
        ok t => toml_table_lookup_eq "s" t (string "line one\nline two"),
        err _ => false
    }

#[test]
def test_parse_multiline_basic_no_leading_newline : Bool :=
    match Toml.parse "s = \"\"\"line one\nline two\"\"\"" {
        ok t => toml_table_lookup_eq "s" t (string "line one\nline two"),
        err _ => false
    }

#[test]
def test_parse_multiline_basic_empty : Bool :=
    match Toml.parse "s = \"\"\"\"\"\"" {
        ok t => toml_table_lookup_eq "s" t (string ""),
        err _ => false
    }

/// The quote-run rule: 4 quotes at the end are 1 content quote + close.
#[test]
def test_parse_multiline_basic_quoted_content : Bool :=
    match Toml.parse "s = \"\"\"Here are two quotation marks: \"\". Simple enough.\"\"\"" {
        ok t => toml_table_lookup_eq "s" t (string "Here are two quotation marks: \"\". Simple enough."),
        err _ => false
    }

#[test]
def test_parse_multiline_basic_escapes : Bool :=
    match Toml.parse "s = \"\"\"a\\tb\\nc\"\"\"" {
        ok t => toml_table_lookup_eq "s" t (string "a\tb\nc"),
        err _ => false
    }

/// A `\` at the end of a line trims all whitespace through the next
/// non-whitespace character.
#[test]
def test_parse_multiline_basic_line_ending_backslash : Bool :=
    match Toml.parse "s = \"\"\"\\\n  trimmed \\\n  away\"\"\"" {
        ok t => toml_table_lookup_eq "s" t (string "trimmed away"),
        err _ => false
    }

/// A backslash followed by anything but whitespace-or-newline is an
/// ordinary escape; `\ x` is an invalid escape, not a continuation.
#[test]
def test_parse_multiline_basic_bad_continuation_is_error : Bool :=
    match Toml.parse "s = \"\"\"\\ x\"\"\"" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_multiline_literal : Bool :=
    match Toml.parse "s = '''\nno \\n escapes\nhere'''" {
        ok t => toml_table_lookup_eq "s" t (string "no \\n escapes\nhere"),
        err _ => false
    }

/// The literal quote-run rule: `''` inside is content.
#[test]
def test_parse_multiline_literal_quoted_content : Bool :=
    match Toml.parse "s = '''Here are two quotation marks: ''. Simple enough.'''" {
        ok t => toml_table_lookup_eq "s" t (string "Here are two quotation marks: ''. Simple enough."),
        err _ => false
    }

#[test]
def test_parse_multiline_literal_empty : Bool :=
    match Toml.parse "s = ''''''" {
        ok t => toml_table_lookup_eq "s" t (string ""),
        err _ => false
    }

#[test]
def test_parse_crlf_multiline_normalized : Bool :=
    match Toml.parse "s = \"\"\"\r\nline one\r\nline two\"\"\"" {
        ok t => toml_table_lookup_eq "s" t (string "line one\nline two"),
        err _ => false
    }

/// `\uXXXX` decodes to real UTF-8.
#[test]
def test_parse_unicode_escape : Bool :=
    match Toml.parse "s = \"\\u00e9\"" {
        ok t => toml_table_lookup_eq "s" t (string "é"),
        err _ => false
    }

/// `\U0001F600` is a 4-byte code point.
#[test]
def test_parse_wide_unicode_escape : Bool :=
    match Toml.parse "s = \"\\U0001F600\"" {
        ok t => match Toml.table_get "s" t {
            some v => match Toml.get_string v {
                ok s => String.length s == 4,
                err _ => false,
            },
            none => false,
        },
        err _ => false
    }

#[test]
def test_parse_surrogate_escape_is_error : Bool :=
    match Toml.parse "s = \"\\uD800\"" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_out_of_range_escape_is_error : Bool :=
    match Toml.parse "s = \"\\U00110000\"" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_invalid_escape_is_error : Bool :=
    match Toml.parse "s = \"\\x\"" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_short_unicode_escape_is_error : Bool :=
    match Toml.parse "s = \"\\u12\"" {
        ok _ => false,
        err _ => true
    }

/// Multi-byte UTF-8 in a plain string, unquoted and unescaped.
#[test]
def test_parse_multibyte_string : Bool :=
    match Toml.parse "s = \"café — naïve\"" {
        ok t => toml_table_lookup_eq "s" t (string "café — naïve"),
        err _ => false
    }

// ─── Tests: parser — keys ───

#[test]
def test_parse_quoted_key : Bool :=
    match Toml.parse "\"key with spaces\" = 1" {
        ok t => toml_table_lookup_eq "key with spaces" t (integer 1),
        err _ => false
    }

#[test]
def test_parse_literal_quoted_key : Bool :=
    match Toml.parse "'literal key' = 1" {
        ok t => toml_table_lookup_eq "literal key" t (integer 1),
        err _ => false
    }

#[test]
def test_parse_empty_quoted_key : Bool :=
    match Toml.parse "\"\" = 1" {
        ok t => toml_table_lookup_eq "" t (integer 1),
        err _ => false
    }

/// A carried-over row from main's own quoted-key commit (`24a5357d`):
/// the key lives in a NESTED table and holds a hyphen, which is what a
/// keymap row looks like (`"A-j" = "move_char_down"`).
#[test]
def test_parse_quoted_hyphenated_key_in_nested_table : Bool :=
    match Toml.parse "[keys.normal]\n\"A-j\" = \"move_char_down\"\n" {
        ok t =>
            match Toml.table_get "keys" t {
                some v =>
                    match v {
                        table sub =>
                            match Toml.table_get "normal" sub {
                                some inner =>
                                    match inner {
                                        table rows =>
                                            toml_table_lookup_eq "A-j" rows (string "move_char_down"),
                                        _ => false
                                    },
                                none => false
                            },
                        _ => false
                    },
                none => false
            },
        err _ => false
    }

/// Quoted and bare keys co-exist in one table -- a config may spell either
/// form, and a file that mixed them must not lose the rows it did not quote.
#[test]
def test_parse_quoted_and_bare_keys : Bool :=
    match Toml.parse "plain = \"a\"\n\"C-x\" = \"b\"\n" {
        ok t =>
            toml_table_lookup_eq "plain" t (string "a")
                && toml_table_lookup_eq "C-x" t (string "b"),
        err _ => false
    }

/// A quoted key may hold punctuation a bare key cannot -- here a
/// parenthesis, which the value parser must not mistake for structure.
#[test]
def test_parse_quoted_key_with_punctuation : Bool :=
    match Toml.parse "\"m-i-(\" = \"match_inside\"\n" {
        ok t => toml_table_lookup_eq "m-i-(" t (string "match_inside"),
        err _ => false
    }

/// A dotted key outside a header now parses — this used to be the
/// explicit "dotted keys are unsupported" error row.
#[test]
def test_parse_dotted_key : Bool :=
    match Toml.parse "a.b = 1" {
        ok t =>
            match Toml.table_get "a" t {
                some v => match v {
                    table sub => toml_table_lookup_eq "b" sub (integer 1),
                    _ => false,
                },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_dotted_key_three_levels : Bool :=
    match Toml.parse "a.b.c = 1" {
        ok t =>
            match Toml.table_get "a" t {
                some a_v => match a_v {
                    table a_t =>
                        match Toml.table_get "b" a_t {
                            some b_v => match b_v {
                                table b_t => toml_table_lookup_eq "c" b_t (integer 1),
                                _ => false,
                            },
                            none => false,
                        },
                    _ => false,
                },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_dotted_key_whitespace_around_dot : Bool :=
    match Toml.parse "a . b = 1" {
        ok t =>
            match Toml.table_get "a" t {
                some v => match v {
                    table sub => toml_table_lookup_eq "b" sub (integer 1),
                    _ => false,
                },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_quoted_key_in_header : Bool :=
    match Toml.parse "[\"table with spaces\"]\nx = 1" {
        ok t =>
            match Toml.table_get "table with spaces" t {
                some v => match v { table sub => toml_table_lookup_eq "x" sub (integer 1), _ => false },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_whitespace_in_header : Bool :=
    match Toml.parse "[ a . b ]\nx = 1" {
        ok t =>
            match Toml.table_get "a" t {
                some v => match v {
                    table a_t =>
                        match Toml.table_get "b" a_t {
                            some b_v => match b_v { table b_t => toml_table_lookup_eq "x" b_t (integer 1), _ => false },
                            none => false,
                        },
                    _ => false,
                },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_empty_header_is_error : Bool :=
    match Toml.parse "[]\nx = 1" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_double_dot_in_key_is_error : Bool :=
    match Toml.parse "a..b = 1" {
        ok _ => false,
        err _ => true
    }

/// `a` and `"a"` are the same key, so defining both is a duplicate.
#[test]
def test_parse_bare_and_quoted_same_key_is_duplicate : Bool :=
    match Toml.parse "a = 1\n\"a\" = 2" {
        ok _ => false,
        err _ => true
    }

// ─── Tests: parser — arrays ───

#[test]
def test_parse_int_array : Bool :=
    match Toml.parse "xs = [1, 2, 3]" {
        ok t => toml_table_lookup_eq "xs" t (array [integer 1, integer 2, integer 3]),
        err _ => false
    }

#[test]
def test_parse_string_array : Bool :=
    match Toml.parse "members = [\"core\", \"cli\", \"wasm\"]" {
        ok t => toml_table_lookup_eq "members" t (array [string "core", string "cli", string "wasm"]),
        err _ => false
    }

#[test]
def test_parse_empty_array : Bool :=
    match Toml.parse "xs = []" {
        ok t => toml_table_lookup_eq "xs" t (array List.empty),
        err _ => false
    }

/// Nested arrays are part of TOML 1.0 — this used to be the explicit
/// "nested arrays are unsupported" error row.
#[test]
def test_parse_nested_array : Bool :=
    match Toml.parse "xs = [[1, 2], [3, 4]]" {
        ok t => toml_table_lookup_eq "xs" t (array [array [integer 1, integer 2], array [integer 3, integer 4]]),
        err _ => false
    }

#[test]
def test_parse_mixed_array : Bool :=
    match Toml.parse "xs = [1, \"two\", 3.5, true, 1979-05-27]" {
        ok t => toml_table_lookup_eq "xs" t (array [
            integer 1, string "two", float 3.5f64, boolean true, datetime "1979-05-27"]),
        err _ => false
    }

/// `[,]` is an error, and parsed as `[]` before the trailing-comma
/// check gained its non-empty guard.
#[test]
def test_parse_array_leading_comma_is_error : Bool :=
    match Toml.parse "xs = [,]" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_array_of_arrays_with_newlines : Bool :=
    match Toml.parse "xs = [\n  [1, 2],\n  [3, 4],\n]" {
        ok t => toml_table_lookup_eq "xs" t (array [array [integer 1, integer 2], array [integer 3, integer 4]]),
        err _ => false
    }

// ─── Tests: parser — headers ───

#[test]
def test_parse_single_header : Bool :=
    match Toml.parse "[mote]\nname = \"example\"" {
        ok t =>
            match Map.lookup "mote" t {
                some v => match v { table sub => toml_table_lookup_eq "name" sub (string "example"), _ => false },
                none => false
            },
        err _ => false
    }

#[test]
def test_parse_dotted_header : Bool :=
    match Toml.parse "[workspace.package]\nversion = \"0.1.2\"" {
        ok t =>
            match Toml.table_get "workspace" t {
                some v => toml_check_nested_package v,
                none => false
            },
        err _ => false
    }

def toml_check_nested_package (v : Toml.Value) : Bool :=
    match v {
        table sub =>
            match Toml.table_get "package" sub {
                some pv => match pv { table pkg => toml_table_lookup_eq "version" pkg (string "0.1.2"), _ => false },
                none => false
            },
        _ => false
    }

#[test]
def test_parse_empty_table_header : Bool :=
    match Toml.parse "[dependencies]" {
        ok t =>
            match Toml.table_get "dependencies" t {
                some v => match v { table sub => List.is_empty (BTreeMap.to_list sub), _ => false },
                none => false
            },
        err _ => false
    }

#[test]
def test_parse_array_of_tables_one_element : Bool :=
    match Toml.parse "[[products]]\nname = \"a\"\n" {
        ok t => toml_products_names t == ["a"],
        err _ => false
    }

#[test]
def test_parse_array_of_tables_two_elements : Bool :=
    match Toml.parse "[[products]]\nname = \"a\"\n\n[[products]]\nname = \"b\"\n" {
        ok t => toml_products_names t == ["a", "b"],
        err _ => false
    }

/// A DOTTED array-of-tables header: the elements live at `a.b`.
#[test]
def test_nested_array_of_tables : Bool :=
    match Toml.parse "[[a.b]]\nname = \"x\"\n\n[[a.b]]\nname = \"y\"\n" {
        ok t => toml_nested_names t == ["x", "y"],
        err _ => false
    }

#[partial]
def toml_nested_names (t : BTreeMap String Toml.Value) : List String :=
    toml_names_of_array (toml_array_in "b" (Map.lookup "a" t))

#[partial]
def toml_array_in (inner : String) (found : Option Toml.Value) : List Toml.Value :=
    match found {
        some v => toml_array_in_value inner v,
        none => List.empty
    }

def toml_array_in_value (inner : String) (v : Toml.Value) : List Toml.Value :=
    match v {
        table sub => Toml.array_at inner sub,
        _ => List.empty
    }

/// The `name` of every element of the root's `products` array, so the
/// array-of-tables tests can assert on a plain `List String`.
#[partial]
def toml_products_names (t : BTreeMap String Toml.Value) : List String :=
    toml_names_of_array (Toml.array_at "products" t)

#[partial]
def toml_names_of_array (elems : List Toml.Value) : List String :=
    match elems {
        List.empty => List.empty,
        List.cons e rest => List.append (toml_name_of_elem e) (toml_names_of_array rest)
    }

#[partial]
def toml_name_of_elem (e : Toml.Value) : List String :=
    match e {
        table sub => toml_name_of_table (Map.lookup "name" sub),
        _ => List.empty
    }

def toml_name_of_table (found : Option Toml.Value) : List String :=
    match found {
        some v => toml_name_of_value v,
        none => List.empty
    }

def toml_name_of_value (v : Toml.Value) : List String :=
    match v {
        string s => [s],
        _ => List.empty
    }

/// An `[[x]]` element keeps its OWN keys -- the second element's `version`
/// must not land in the first, which is the whole point of `step_last`.
#[test]
def test_array_of_tables_elements_do_not_share_keys : Bool :=
    match Toml.parse "[[mote]]\nname = \"a\"\nversion = \"1\"\n\n[[mote]]\nname = \"b\"\n" {
        ok t => toml_elem_keys t == ["name", "version", "name"],
        err _ => false
    }

#[partial]
def toml_elem_keys (t : BTreeMap String Toml.Value) : List String :=
    toml_keys_of_elems (Toml.array_at "mote" t)

#[partial]
def toml_keys_of_elems (elems : List Toml.Value) : List String :=
    match elems {
        List.empty => List.empty,
        List.cons e rest => List.append (toml_keys_of_elem e) (toml_keys_of_elems rest)
    }

#[partial]
def toml_keys_of_elem (e : Toml.Value) : List String :=
    match e {
        table sub => toml_pair_keys (BTreeMap.to_list sub),
        _ => List.empty
    }

#[partial]
def toml_pair_keys (pairs : List (Pair String Toml.Value)) : List String :=
    match pairs {
        List.empty => List.empty,
        List.cons p rest => List.append (toml_pair_key p) (toml_pair_keys rest)
    }

def toml_pair_key (p : Pair String Toml.Value) : List String :=
    match p { Pair.pair k _ => [k] }

// ─── Tests: parser — comments ───

#[test]
def test_parse_whole_line_comment : Bool :=
    match Toml.parse "# the mote's own name\nname = \"example\"" {
        ok t => toml_table_lookup_eq "name" t (string "example"),
        err _ => false
    }

#[test]
def test_parse_trailing_comment : Bool :=
    match Toml.parse "name = \"example\" # trailing\nversion = \"0.1.0\"" {
        ok t =>
            if toml_table_lookup_eq "name" t (string "example")
            then toml_table_lookup_eq "version" t (string "0.1.0")
            else false,
        err _ => false
    }

#[test]
def test_parse_comment_after_header : Bool :=
    match Toml.parse "[mote] # who we are\nname = \"example\"" {
        ok t =>
            match Map.lookup "mote" t {
                some v => match v { table sub => toml_table_lookup_eq "name" sub (string "example"), _ => false },
                none => false
            },
        err _ => false
    }

/// A `#` inside a quoted value is ordinary text, not a comment -- the string
/// parser consumes it before the line ever looks for a comment.
#[test]
def test_parse_hash_inside_string_is_not_a_comment : Bool :=
    match Toml.parse "colour = \"#ff00ff\"" {
        ok t => toml_table_lookup_eq "colour" t (string "#ff00ff"),
        err _ => false
    }

#[test]
def test_parse_comment_only_document : Bool :=
    match Toml.parse "# nothing but a comment\n" {
        ok t => Toml.table_beq t BTreeMap.empty,
        err _ => false
    }

// ─── Tests: CRLF documents ───

#[test]
def test_parse_crlf_document : Bool :=
    match Toml.parse "a = 1\r\nb = 2\r\n" {
        ok t => toml_table_lookup_eq "a" t (integer 1) && toml_table_lookup_eq "b" t (integer 2),
        err _ => false
    }

#[test]
def test_parse_crlf_headers_and_comments : Bool :=
    match Toml.parse "# a comment\r\n[mote]\r\nname = \"x\"\r\n" {
        ok t =>
            match Toml.table_get "mote" t {
                some v => match v { table sub => toml_table_lookup_eq "name" sub (string "x"), _ => false },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_bom_stripped : Bool :=
    match Toml.parse (String.concat (String.from_list [239u8, 187u8, 191u8]) "a = 1") {
        ok t => toml_table_lookup_eq "a" t (integer 1),
        err _ => false
    }

// ─── Tests: inline tables ───

#[test]
def test_parse_inline_table : Bool :=
    match Toml.parse "dep = { path = \"../std\" }\n" {
        ok t => toml_inline_path_is t "../std",
        err _ => false
    }

#[test]
def test_parse_empty_inline_table : Bool :=
    match Toml.parse "dep = {}\n" {
        ok t => toml_dep_is_empty_table t,
        err _ => false
    }

#[test]
def test_parse_inline_table_two_keys : Bool :=
    match Toml.parse "dep = { git = \"u\", tag = \"v1\" }\n" {
        ok t => toml_inline_keys t == ["git", "tag"],
        err _ => false
    }

#[test]
def test_parse_inline_table_dotted_key : Bool :=
    match Toml.parse "p = { a.b = 1 }\n" {
        ok t =>
            match Toml.table_get "p" t {
                some v => match v {
                    table p_t =>
                        match Toml.table_get "a" p_t {
                            some a_v => match a_v {
                                table a_t => toml_table_lookup_eq "b" a_t (integer 1),
                                _ => false,
                            },
                            none => false,
                        },
                    _ => false,
                },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_inline_table_quoted_key : Bool :=
    match Toml.parse "p = { \"a b\" = 1 }\n" {
        ok t =>
            match Toml.table_get "p" t {
                some v => match v { table p_t => toml_table_lookup_eq "a b" p_t (integer 1), _ => false },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_inline_table_nested : Bool :=
    match Toml.parse "p = { a = { b = 1 } }\n" {
        ok t =>
            match Toml.table_get "p" t {
                some v => match v {
                    table p_t =>
                        match Toml.table_get "a" p_t {
                            some a_v => match a_v {
                                table a_t => toml_table_lookup_eq "b" a_t (integer 1),
                                _ => false,
                            },
                            none => false,
                        },
                    _ => false,
                },
                none => false,
            },
        err _ => false
    }

/// A multi-line array inside a single-line inline table: the newline is
/// inside a VALUE, which the spec allows.
#[test]
def test_parse_inline_table_with_multiline_array : Bool :=
    match Toml.parse "p = { xs = [\n  1,\n  2,\n] }\n" {
        ok t =>
            match Toml.table_get "p" t {
                some v => match v { table p_t => toml_table_lookup_eq "xs" p_t (array [integer 1, integer 2]), _ => false },
                none => false,
            },
        err _ => false
    }

#[test]
def test_parse_inline_table_duplicate_key_is_error : Bool :=
    match Toml.parse "p = { a = 1, a = 2 }\n" {
        ok _ => false,
        err _ => true
    }

/// A newline inside an inline table is a parse error, not a misparse: the
/// body uses the HORIZONTAL-only whitespace parser precisely so this fails.
#[test]
def test_inline_table_may_not_span_lines : Bool :=
    match Toml.parse "dep = { path =\n\"../std\" }\n" {
        ok _ => false,
        err _ => true
    }

/// TOML forbids a trailing comma in an inline table (unlike an array, where
/// this parser accepts one because the repo's own root manifest writes it).
#[test]
def test_inline_table_rejects_a_trailing_comma : Bool :=
    match Toml.parse "dep = { path = \"../std\", }\n" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_parse_inline_table_inside_an_array : Bool :=
    match Toml.parse "xs = [{ a = 1 }, { b = 2 }]\n" {
        ok t => toml_keys_of_elems (Toml.array_at "xs" t) == ["a", "b"],
        err _ => false
    }

#[partial]
def toml_inline_path_is (t : BTreeMap String Toml.Value) (want : String) : Bool :=
    toml_name_of_value_eq (toml_lookup_in "dep" "path" t) want

#[partial]
def toml_inline_keys (t : BTreeMap String Toml.Value) : List String :=
    toml_keys_of_table (Map.lookup "dep" t)

#[partial]
def toml_keys_of_table (found : Option Toml.Value) : List String :=
    match found {
        some v => toml_keys_of_elem v,
        none => List.empty
    }

#[partial]
def toml_dep_is_empty_table (t : BTreeMap String Toml.Value) : Bool :=
    List.is_empty (toml_keys_of_table (Map.lookup "dep" t))

#[partial]
def toml_lookup_in (outer : String) (inner : String) (t : BTreeMap String Toml.Value) : Option Toml.Value :=
    toml_lookup_inner inner (Map.lookup outer t)

#[partial]
def toml_lookup_inner (inner : String) (found : Option Toml.Value) : Option Toml.Value :=
    match found {
        some v => toml_lookup_inner_value inner v,
        none => Option.none
    }

def toml_lookup_inner_value (inner : String) (v : Toml.Value) : Option Toml.Value :=
    match v {
        table sub => Map.lookup inner sub,
        _ => Option.none
    }

def toml_name_of_value_eq (found : Option Toml.Value) (want : String) : Bool :=
    match found {
        some v => toml_value_string_eq v want,
        none => false
    }

def toml_value_string_eq (v : Toml.Value) (want : String) : Bool :=
    match v {
        string s => String.beq s want,
        _ => false
    }

// ─── Tests: table-definition rules (reported, never misparsed) ───

/// A header may now DESCEND into an array of tables, addressing its LAST
/// element -- this used to be the explicit "unsupported" error row, and is
/// the spec's own `[[fruit]]` / `[fruit.physical]` example.
#[test]
def test_header_descends_into_the_last_array_element : Bool :=
    match Toml.parse "[[fruit]]\nname = \"apple\"\n\n[fruit.physical]\ncolor = \"red\"\n" {
        ok t =>
            match Toml.array_at "fruit" t {
                List.cons e _ =>
                    match e {
                        table elem =>
                            toml_table_lookup_eq "name" elem (string "apple")
                            && (match Toml.table_get "physical" elem {
                                some v => match v { table p => toml_table_lookup_eq "color" p (string "red"), _ => false },
                                none => false,
                            }),
                        _ => false,
                    },
                List.empty => false,
            },
        err _ => false
    }

/// The second `[fruit.physical]` after two `[[fruit]]` headers lands in
/// element 2, not element 1.
#[test]
def test_header_descends_into_the_second_element : Bool :=
    match Toml.parse "[[fruit]]\nname = \"apple\"\n\n[[fruit]]\nname = \"banana\"\n\n[fruit.physical]\ncolor = \"yellow\"\n" {
        ok t =>
            match Toml.array_at "fruit" t {
                List.cons _ rest =>
                    match rest {
                        List.cons e _ =>
                            match e {
                                table elem =>
                                    match Toml.table_get "physical" elem {
                                        some v => match v { table p => toml_table_lookup_eq "color" p (string "yellow"), _ => false },
                                        none => false,
                                    },
                                _ => false,
                            },
                        List.empty => false,
                    },
                List.empty => false,
            },
        err _ => false
    }

#[test]
def test_plain_header_conflicting_with_an_array_is_an_error : Bool :=
    match Toml.parse "[[mote]]\nname = \"a\"\n\n[mote]\nx = 1\n" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_array_header_conflicting_with_a_table_is_an_error : Bool :=
    match Toml.parse "[mote]\nname = \"a\"\n\n[[mote]]\nx = 1\n" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_header_through_a_scalar_is_an_error : Bool :=
    match Toml.parse "a = 1\n\n[a.b]\nx = 1\n" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_header_defined_twice_is_an_error : Bool :=
    match Toml.parse "[a]\nx = 1\n\n[a]\ny = 2\n" {
        ok _ => false,
        err _ => true
    }

/// Out-of-order definition: `[a.b]` creates `a` implicitly, and a later
/// `[a]` PROMOTES it rather than reporting a duplicate.
#[test]
def test_later_header_promotes_an_implicit_table : Bool :=
    match Toml.parse "[a.b]\nx = 1\n\n[a]\ny = 2\n" {
        ok t =>
            match Toml.table_get "a" t {
                some v => match v {
                    table a_t => toml_table_lookup_eq "y" a_t (integer 2),
                    _ => false,
                },
                none => false,
            },
        err _ => false
    }

/// A re-entered SHORTER header must not erase what the longer one built.
#[test]
def test_reentering_a_shorter_header_keeps_the_nested_table : Bool :=
    match Toml.parse "[a.b]\nx = 1\n\n[a]\ny = 2\n" {
        ok t => toml_a_keys t == ["b", "y"],
        err _ => false
    }

#[partial]
def toml_a_keys (t : BTreeMap String Toml.Value) : List String :=
    toml_keys_of_table (Map.lookup "a" t)

/// A dotted key and a header may not define the same table -- the spec's
/// own "dotted keys redefine [table] form" example.
#[test]
def test_dotted_key_cannot_redefine_a_header_table : Bool :=
    match Toml.parse "[a]\nb.c = 1\n[a.b]\nd = 2\n" {
        ok _ => false,
        err _ => true
    }

/// The spec's positive example: a dotted key creates `a.b`, and a later
/// header may add to `b` -- but not re-define `a.b` itself.
#[test]
def test_dotted_key_then_deeper_header : Bool :=
    match Toml.parse "a.b.c = 1\n[a.b.d]\ne = 2\n" {
        ok t =>
            match Toml.table_get "a" t {
                some v => match v {
                    table a_t =>
                        match Toml.table_get "b" a_t {
                            some b_v => match b_v {
                                table b_t =>
                                    toml_table_lookup_eq "c" b_t (integer 1)
                                    && (match Toml.table_get "d" b_t {
                                        some d_v => match d_v { table d_t => toml_table_lookup_eq "e" d_t (integer 2), _ => false },
                                        none => false,
                                    }),
                                _ => false,
                            },
                            none => false,
                        },
                    _ => false,
                },
                none => false,
            },
        err _ => false
    }

#[test]
def test_header_cannot_redefine_a_dotted_table : Bool :=
    match Toml.parse "a.b = 1\n[a]\nc = 2\n" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_dotted_key_conflicting_with_a_scalar_is_an_error : Bool :=
    match Toml.parse "a = 1\na.b = 2\n" {
        ok _ => false,
        err _ => true
    }

#[test]
def test_duplicate_key_is_an_error : Bool :=
    match Toml.parse "a = 1\na = 2\n" {
        ok _ => false,
        err _ => true
    }

/// Inline tables are immutable: a header cannot extend one.
#[test]
def test_inline_table_cannot_be_extended_by_a_header : Bool :=
    match Toml.parse "a = { x = 1 }\n\n[a.b]\ny = 2\n" {
        ok _ => false,
        err _ => true
    }

/// ...and a `kv` cannot add a key to one.
#[test]
def test_inline_table_cannot_be_extended_by_a_key : Bool :=
    match Toml.parse "a = { x = 1 }\n\na.y = 2\n" {
        ok _ => false,
        err _ => true
    }

/// ...and a second `[[a]]` cannot append to a static array of inline tables.
#[test]
def test_static_array_of_inline_tables_cannot_be_appended : Bool :=
    match Toml.parse "a = [{ x = 1 }]\n\n[[a]]\ny = 2\n" {
        ok _ => false,
        err _ => true
    }

// ─── Tests: real fixtures ───

/// Verbatim contents of motes/example/mote.toml.
def mote_toml_fixture : String :=
    "[mote]\nname = \"example\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n[dependencies]\n"

#[test]
def test_parse_mote_fixture : Bool :=
    match Toml.parse mote_toml_fixture {
        ok t =>
            match Toml.table_get "mote" t {
                some v => toml_check_mote_table v,
                none => false
            } &&
            match Toml.table_get "dependencies" t {
                some v => match v { table sub => List.is_empty (BTreeMap.to_list sub), _ => false },
                none => false
            },
        err _ => false
    }

def toml_check_mote_table (v : Toml.Value) : Bool :=
    match v {
        table sub =>
            toml_table_lookup_eq "name" sub (string "example") &&
            toml_table_lookup_eq "version" sub (string "0.1.0") &&
            toml_table_lookup_eq "edition" sub (string "2026"),
        _ => false
    }

/// Verbatim shape of a workspace member's manifest (lang/mote.toml): comments,
/// a [lib] target, and dependencies as SUB-TABLE headers.
def member_mote_toml_fixture : String :=
    "# The self-hosted compiler, as a library.\n\n[mote]\nname = \"lang\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n[lib]\npath = \"src/lib.mo\"\n\n[dependencies.init]\npath = \"../init\"\n\n[dependencies.std]\npath = \"../std\"\n"

#[test]
def test_parse_member_mote_fixture : Bool :=
    match Toml.parse member_mote_toml_fixture {
        ok t =>
            toml_check_member_mote (Toml.table_get "mote" t) &&
            toml_check_member_lib (Toml.table_get "lib" t) &&
            toml_check_member_deps (Toml.table_get "dependencies" t),
        err _ => false
    }

def toml_check_member_mote (found : Option Toml.Value) : Bool :=
    match found {
        some v => match v {
            table sub =>
                toml_table_lookup_eq "name" sub (string "lang") &&
                toml_table_lookup_eq "version" sub (string "0.1.0") &&
                toml_table_lookup_eq "edition" sub (string "2026"),
            _ => false
        },
        none => false
    }

def toml_check_member_lib (found : Option Toml.Value) : Bool :=
    match found {
        some v => match v {
            table sub => toml_table_lookup_eq "path" sub (string "src/lib.mo"),
            _ => false
        },
        none => false
    }

/// Each dependency is its own sub-table, so `dependencies.init.path` is the
/// declared source location.
def toml_check_member_deps (found : Option Toml.Value) : Bool :=
    match found {
        some v => match v {
            table deps =>
                toml_check_dep_path (Toml.table_get "init" deps) "../init" &&
                toml_check_dep_path (Toml.table_get "std" deps) "../std",
            _ => false
        },
        none => false
    }

def toml_check_dep_path (found : Option Toml.Value) (expected : String) : Bool :=
    match found {
        some v => match v {
            table dep => toml_table_lookup_eq "path" dep (string expected),
            _ => false
        },
        none => false
    }

#[test]
def test_roundtrip_member_mote_fixture : Bool :=
    match Toml.parse member_mote_toml_fixture {
        ok t =>
            match Toml.parse (Toml.to_string t) {
                ok t2 => Toml.table_beq t t2,
                err _ => false
            },
        err _ => false
    }

/// Modeled after root Cargo.toml's [workspace] / [workspace.package] sections:
/// a multi-key table, an array-of-strings (members), and a nested dotted header.
def cargo_workspace_toml_fixture : String :=
    "[workspace]\nmembers = [\"core\", \"cli\", \"wasm\"]\n\n[workspace.package]\nversion = \"0.1.2\"\nedition = \"2024\"\nlicense = \"ASL2\"\n"

#[test]
def test_parse_cargo_workspace_fixture : Bool :=
    match Toml.parse cargo_workspace_toml_fixture {
        ok t =>
            match Toml.table_get "workspace" t {
                some v => toml_check_workspace_table v,
                none => false
            },
        err _ => false
    }

def toml_check_workspace_table (v : Toml.Value) : Bool :=
    match v {
        table ws =>
            toml_table_lookup_eq "members" ws (array [string "core", string "cli", string "wasm"]) &&
            toml_check_workspace_package (Toml.table_get "package" ws),
        _ => false
    }

def toml_check_workspace_package (found : Option Toml.Value) : Bool :=
    match found {
        some v => match v {
            table pkg =>
                toml_table_lookup_eq "version" pkg (string "0.1.2") &&
                toml_table_lookup_eq "edition" pkg (string "2024") &&
                toml_table_lookup_eq "license" pkg (string "ASL2"),
            _ => false
        },
        none => false
    }

// ─── Tests: serializer ───

#[test]
def test_serialize_scalars : Bool :=
    Toml.value_to_string (string "hi") == "\"hi\"" &&
    Toml.value_to_string (integer 42) == "42" &&
    Toml.value_to_string (integer (I64.neg 7)) == "-7" &&
    Toml.value_to_string (boolean true) == "true" &&
    Toml.value_to_string (boolean false) == "false"

#[test]
def test_serialize_array : Bool :=
    Toml.value_to_string (array [integer 1, integer 2, integer 3]) == "[1,2,3]"

#[test]
def test_serialize_root_kv : Bool :=
    Toml.to_string (Map.insert "name" (string "example") BTreeMap.empty) == "name = \"example\"\n"

#[test]
def test_serialize_nested_table : Bool :=
    let inner := Map.insert "name" (string "example") BTreeMap.empty in
    let root := Map.insert "mote" (table inner) BTreeMap.empty in
    Toml.to_string root == "[mote]\nname = \"example\"\n"

#[test]
def test_serialize_empty_table : Bool :=
    let root := Map.insert "dependencies" (table BTreeMap.empty) BTreeMap.empty in
    Toml.to_string root == "[dependencies]\n"

#[test]
def test_serialize_inline_table_in_an_array : Bool :=
    let one := Map.insert "a" (integer 1) BTreeMap.empty in
    Toml.value_to_string (array [table one]) == "[{ a = 1 }]"

#[test]
def test_serialize_empty_inline_table : Bool :=
    Toml.value_to_string (table BTreeMap.empty) == "{}"

/// A non-empty array of tables renders as `[[k]]` sections, which is what
/// makes a `mote.lock` come back out in the spelling it went in as.
#[test]
def test_serialize_array_of_tables : Bool :=
    let a := Map.insert "name" (string "a") BTreeMap.empty in
    let b := Map.insert "name" (string "b") BTreeMap.empty in
    let root := Map.insert "mote" (array [table a, table b]) BTreeMap.empty in
    Toml.to_string root == "[[mote]]\nname = \"a\"\n[[mote]]\nname = \"b\"\n"

/// An EMPTY array is not a table array and must stay an ordinary `[]`.
#[test]
def test_serialize_empty_array_is_not_a_table_array : Bool :=
    Toml.to_string (Map.insert "xs" (array List.empty) BTreeMap.empty) == "xs = []\n"

/// `F64.to_string` renders 3.0 as "3", which re-reads as an INTEGER; the
/// float arm appends `.0`.
#[test]
def test_serialize_float_gains_a_point_zero : Bool :=
    Toml.value_to_string (float 3.0f64) == "3.0" &&
    Toml.value_to_string (float 1.0f64) == "1.0" &&
    Toml.value_to_string (float 0.5f64) == "0.5" &&
    Toml.value_to_string (float (-2.5f64)) == "-2.5"

#[test]
def test_serialize_float_nonfinite_spellings : Bool :=
    Toml.value_to_string (float (1.0f64 / 0.0f64)) == "inf" &&
    Toml.value_to_string (float (0.0f64 - (1.0f64 / 0.0f64))) == "-inf" &&
    Toml.value_to_string (float (0.0f64 / 0.0f64)) == "nan"

/// Keys that are not bare-key-shaped are quoted, so they round-trip.
#[test]
def test_serialize_quoted_key : Bool :=
    Toml.key_to_string "a b" == "\"a b\"" &&
    Toml.key_to_string "" == "\"\"" &&
    Toml.key_to_string "a.b" == "\"a.b\"" &&
    Toml.key_to_string "bare_key-1" == "bare_key-1"

/// A datetime renders verbatim, which is the point of preserving the
/// source spelling.
#[test]
def test_serialize_datetime_verbatim : Bool :=
    Toml.value_to_string (datetime "1979-05-27T07:32:00Z") == "1979-05-27T07:32:00Z" &&
    Toml.value_to_string (datetime "07:32:00") == "07:32:00"

/// A control byte in a string is escaped, because the parser rejects one
/// unescaped -- passing it through would break the round trip.
#[test]
def test_serialize_control_byte_escaped : Bool :=
    Toml.value_to_string (string (String.from_list [97u8, 1u8, 98u8])) == "\"a\\u0001b\""

#[test]
def test_serialize_del_escaped : Bool :=
    Toml.value_to_string (string (String.from_list [97u8, 127u8, 98u8])) == "\"a\\u007fb\""

/// Multi-byte UTF-8 passes through unescaped.
#[test]
def test_serialize_multibyte_passthrough : Bool :=
    Toml.value_to_string (string "café") == "\"café\""

// ─── Tests: round-trip ───

#[test]
def test_roundtrip_mote_fixture : Bool :=
    match Toml.parse mote_toml_fixture {
        ok t1 =>
            match Toml.parse (Toml.to_string t1) {
                ok t2 => Toml.table_beq t1 t2,
                err _ => false
            },
        err _ => false
    }

#[test]
def test_roundtrip_cargo_workspace_fixture : Bool :=
    match Toml.parse cargo_workspace_toml_fixture {
        ok t1 =>
            match Toml.parse (Toml.to_string t1) {
                ok t2 => Toml.table_beq t1 t2,
                err _ => false
            },
        err _ => false
    }

#[test]
def test_roundtrip_array : Bool :=
    let root := Map.insert "xs" (array [integer 1, integer 2, integer 3]) BTreeMap.empty in
    match Toml.parse (Toml.to_string root) {
        ok t => Toml.table_beq root t,
        err _ => false
    }

/// The whole point of the two features together: a `mote.lock`-shaped
/// document survives parse -> to_string -> parse with the same values.
#[test]
def test_round_trip_lockfile_shape : Bool :=
    let src := "version = 1\n\n[[mote]]\nname = \"http\"\nsource = \"git+u#r\"\n\n[[mote]]\nname = \"json\"\nsource = \"git+v#s\"\n" in
    match Toml.parse src {
        ok t => toml_round_trips_to_same_names t,
        err _ => false
    }

#[partial]
def toml_round_trips_to_same_names (t : BTreeMap String Toml.Value) : Bool :=
    match Toml.parse (Toml.to_string t) {
        ok t2 => toml_elem_keys t2 == ["name", "source", "name", "source"] && toml_mote_names t2 == ["http", "json"],
        err _ => false
    }

#[partial]
def toml_mote_names (t : BTreeMap String Toml.Value) : List String :=
    toml_names_of_array (Toml.array_at "mote" t)

/// An inline dependency table round-trips too -- this is the spelling every
/// `mote.toml` outside this repo uses.
#[test]
def test_round_trip_inline_dependency : Bool :=
    match Toml.parse "[dependencies]\nstd = { path = \"../std\" }\n" {
        ok t => toml_inline_dep_round_trips t,
        err _ => false
    }

#[partial]
def toml_inline_dep_round_trips (t : BTreeMap String Toml.Value) : Bool :=
    match Toml.parse (Toml.to_string t) {
        ok t2 => toml_name_of_value_eq (toml_lookup_in "std" "path" (toml_sub_table_value_of (Map.lookup "dependencies" t2))) "../std",
        err _ => false
    }

def toml_sub_table_value_of (found : Option Toml.Value) : BTreeMap String Toml.Value :=
    toml_sub_table_lookup found

/// A float round-trips through its serialized spelling.
#[test]
def test_round_trip_float : Bool :=
    let root := Map.insert "x" (float 3.14f64) BTreeMap.empty in
    match Toml.parse (Toml.to_string root) {
        ok t => toml_table_lookup_eq "x" t (float 3.14f64),
        err _ => false
    }

/// A whole-value float round-trip: inf, -inf and a plain fraction.
#[test]
def test_round_trip_float_document : Bool :=
    match Toml.parse "a = 1.5\nb = inf\nc = -inf\n" {
        ok t =>
            match Toml.parse (Toml.to_string t) {
                ok t2 =>
                    toml_table_lookup_eq "a" t2 (float 1.5f64)
                    && toml_table_lookup_eq "b" t2 (float (1.0f64 / 0.0f64))
                    && toml_table_lookup_eq "c" t2 (float (0.0f64 - (1.0f64 / 0.0f64))),
                err _ => false,
            },
        err _ => false
    }

/// A datetime round-trips verbatim.
#[test]
def test_round_trip_datetime : Bool :=
    match Toml.parse "odt = 1979-05-27T07:32:00Z\nld = 1979-05-27\nlt = 07:32:00\n" {
        ok t =>
            match Toml.parse (Toml.to_string t) {
                ok t2 =>
                    toml_table_lookup_eq "odt" t2 (datetime "1979-05-27T07:32:00Z")
                    && toml_table_lookup_eq "ld" t2 (datetime "1979-05-27")
                    && toml_table_lookup_eq "lt" t2 (datetime "07:32:00"),
                err _ => false,
            },
        err _ => false
    }

/// A multi-line string round-trips (rendered as an escaped single-line
/// string, which is value-equal).
#[test]
def test_round_trip_multiline_string : Bool :=
    match Toml.parse "s = \"\"\"\nline one\nline two\"\"\"" {
        ok t =>
            match Toml.parse (Toml.to_string t) {
                ok t2 => toml_table_lookup_eq "s" t2 (string "line one\nline two"),
                err _ => false,
            },
        err _ => false
    }

/// A quoted key round-trips through the serializer's quoting.
#[test]
def test_round_trip_quoted_key : Bool :=
    match Toml.parse "\"a b\" = 1\n" {
        ok t =>
            match Toml.parse (Toml.to_string t) {
                ok t2 => toml_table_lookup_eq "a b" t2 (integer 1),
                err _ => false,
            },
        err _ => false
    }

/// A nested array round-trips.
#[test]
def test_round_trip_nested_array : Bool :=
    match Toml.parse "xs = [[1, 2], [3, 4]]\n" {
        ok t =>
            match Toml.parse (Toml.to_string t) {
                ok t2 => toml_table_lookup_eq "xs" t2 (array [array [integer 1, integer 2], array [integer 3, integer 4]]),
                err _ => false,
            },
        err _ => false
    }

/// A dotted key round-trips (rendered as a sub-table header, which is
/// value-equal).
#[test]
def test_round_trip_dotted_key : Bool :=
    match Toml.parse "a.b = 1\n" {
        ok t =>
            match Toml.parse (Toml.to_string t) {
                ok t2 => Toml.table_beq t t2,
                err _ => false,
            },
        err _ => false
    }

// ─── Tests: multi-line arrays ──────────────────────────────────────────────
//
// TOML allows an array to span lines between its brackets. This repo's
// own root `mote.toml` writes `[workspace] members` that way, so before
// these the self-hosted reader could not parse the workspace manifest at
// all.

#[test]
def test_parse_multiline_array : Bool :=
    match Toml.parse "members = [\n  \"init\",\n  \"std\"\n]" {
        ok t => toml_table_lookup_eq "members" t (array [string "init", string "std"]),
        err _ => false
    }

#[test]
def test_parse_multiline_array_trailing_comma : Bool :=
    match Toml.parse "members = [\n  \"init\",\n  \"std\",\n]" {
        ok t => toml_table_lookup_eq "members" t (array [string "init", string "std"]),
        err _ => false
    }

#[test]
def test_parse_multiline_array_with_comment : Bool :=
    match Toml.parse "members = [\n  # the compiler itself\n  \"lang\",\n  \"cli\",\n]" {
        ok t => toml_table_lookup_eq "members" t (array [string "lang", string "cli"]),
        err _ => false
    }

#[test]
def test_parse_single_line_array_still_works : Bool :=
    match Toml.parse "xs = [1, 2, 3]" {
        ok t => toml_table_lookup_eq "xs" t (array [integer 1, integer 2, integer 3]),
        err _ => false
    }

#[test]
def test_parse_single_line_array_trailing_comma : Bool :=
    match Toml.parse "xs = [1, 2,]" {
        ok t => toml_table_lookup_eq "xs" t (array [integer 1, integer 2]),
        err _ => false
    }

// A newline still ENDS an ordinary key/value line -- the array-aware
// whitespace must apply only between brackets, or every key would
// swallow the next line.
#[test]
def test_newline_still_separates_plain_values : Bool :=
    match Toml.parse "a = 1\nb = 2" {
        ok t => toml_table_lookup_eq "a" t (integer 1) && toml_table_lookup_eq "b" t (integer 2),
        err _ => false
    }

#[test]
def test_parse_multiline_array_after_header : Bool :=
    match Toml.parse "[workspace]\nmembers = [\n  \"init\",\n  \"motes/*\",\n]\n" {
        ok t =>
            match Toml.table_get "workspace" t {
                some v => toml_check_workspace_members v,
                none => false
            },
        err _ => false
    }

def toml_check_workspace_members (v : Toml.Value) : Bool :=
    match v {
        table sub => toml_table_lookup_eq "members" sub (array [string "init", string "motes/*"]),
        _ => false
    }

// ─── Tests: helpers ───

#[test]
def test_toml_type_checkers : Bool :=
    Toml.is_string (string "a") &&
    Toml.is_integer (integer 1) &&
    Toml.is_float (float 1.5f64) &&
    Toml.is_boolean (boolean true) &&
    Toml.is_datetime (datetime "1979-05-27") &&
    Toml.is_array (array List.empty) &&
    Toml.is_table (table BTreeMap.empty) &&
    Bool.not (Toml.is_string (integer 1))

#[test]
def test_toml_accessors : Bool :=
    match Toml.get_string (string "a") {
        ok s => s == "a",
        err _ => false
    } &&
    match Toml.get_string (boolean true) {
        ok _ => false,
        err _ => true
    } &&
    match Toml.get_float (float 1.5f64) {
        ok f => f == 1.5f64,
        err _ => false
    } &&
    match Toml.get_datetime (datetime "07:32:00") {
        ok s => s == "07:32:00",
        err _ => false
    }

#[test]
def test_toml_table_manipulation : Bool :=
    let t1 := Toml.table_set "a" (integer 1) BTreeMap.empty in
    let t2 := Toml.table_set "b" (integer 2) t1 in
    let t3 := Toml.table_delete "a" t2 in
    toml_table_lookup_eq "a" t1 (integer 1) &&
    toml_table_lookup_missing "a" t3 &&
    toml_table_lookup_eq "b" t3 (integer 2)

#[test]
def test_make_helpers : Bool :=
    Toml.beq (Toml.make_string "a") (string "a") &&
    Toml.beq (Toml.make_integer 1) (integer 1) &&
    Toml.beq (Toml.make_boolean true) (boolean true) &&
    Toml.beq (Toml.make_datetime "1979-05-27") (datetime "1979-05-27") &&
    match Toml.get_float (Toml.make_float 2.5f64) {
        ok f => f == 2.5f64,
        err _ => false
    }
