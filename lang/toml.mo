/// TOML parsing and serialization (MVP subset)
/// Structurally independent from lang/json.mo — no shared Serialize/Deserialize
/// classes (Phase 7 of the JSON plan was deliberately deferred; see
/// plans/bootstrapping/json-parser-serializer-plan.md). Own string-escape helpers,
/// own hand-rolled beq family, own `intercalate` — all namespaced under `Toml.`/
/// `toml_` rather than reusing json.mo's bare `List.intercalate`/`String.concat_list`/
/// `neg_i64` globals, since both files may be loaded in the same test sweep
/// (`cargo run -- test lang/`) and top-level names are not file-scoped.
/// Supported grammar (MVP, per plan): `[table]` / `[dotted.nested.table]` headers
/// (including empty tables), `key = value`, double-quoted strings with the escape
/// subset `\" \\ \n \t \r`, integers, booleans, and single-line arrays of scalars.
/// Explicitly unsupported (parse error, not silent misparse): floats, dates/times,
/// multi-line/literal strings, inline tables, arrays-of-tables (`[[x]]`), dotted
/// keys outside headers, and `#` comments.
// NOTE: a blank `///` line in this leading module doc-comment (used as a paragraph
// break) was found to break the following `use` imports entirely — every symbol
// they bring in resolves as "unbound variable" throughout the rest of the file, a
// previously-undocumented parser/module-loader bug. Worked around by keeping this
// header as one unbroken `///` block with no blank `///` lines; a genuinely blank
// (comment-free) line, like the one separating this NOTE from the header above, is
// fine. Confirmed via a minimal repro; worth fixing upstream in the parser.

use std.map
use std.list
use init.string
use init.number
use lang.parser.core
use lang.parser.char_preds
use lang.parser.combinators
use lang.parser.number

open ParseResult
open Toml.Value

// ─── Types ───

/// TOML value type. `array` only ever holds scalars per the MVP grammar (the
/// parser never produces nested arrays/tables inside an array), but the type
/// itself doesn't enforce that.
type Toml.Value {
  string (s : String),
  integer (n : I64),
  boolean (b : Bool),
  array (a : List Toml.Value),
  table (t : BTreeMap String Toml.Value),
}

// NOTE: equality is hand-rolled (Toml.array_beq / Toml.table_beq) rather than via
// the generic `[BEq A] BEq (List A)` / `BEq (Option A)` instances and `==` — those
// don't dispatch correctly to a custom A's BEq instance at runtime (see the same
// note in lang/json.mo's Json.array_beq). Concrete BEq instances (I64/String/Bool)
// used below are fine.
def Toml.beq (a b : Toml.Value) : Bool :=
  match a {
    string sa => match b { string sb => sa == sb, _ => false },
    integer na => match b { integer nb => na == nb, _ => false },
    boolean ba => match b { boolean bb => ba == bb, _ => false },
    array aa => match b { array ab => Toml.array_beq aa ab, _ => false },
    table ta => match b { table tb => Toml.table_beq ta tb, _ => false },
  }

@[partial]
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

@[partial]
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

@[partial]
def Toml.table_beq (a b : BTreeMap String Toml.Value) : Bool :=
  Toml.pairs_beq (BTreeMap.to_list a) (BTreeMap.to_list b)

instance BEq Toml.Value {
  def beq (a b : Toml.Value) : Bool := Toml.beq a b
}

instance BEq (BTreeMap String Toml.Value) {
  def beq (a b : BTreeMap String Toml.Value) : Bool := Toml.table_beq a b
}

/// TOML ParseError type
type Toml.ParseError {
  expected (e : String) (found : String),
  generic String,
}

def Toml.ParseError.to_string (e : Toml.ParseError) : String :=
  match e {
    expected e f => "expected: " ++ e ++ " found: " ++ f,
    generic s => s
  }

/// Convert core ParseError to Toml.ParseError
def Toml.from_parse_error (e : ParseError) : Toml.ParseError :=
  match e {
    tag s => Toml.ParseError.expected s "",
    custom s => Toml.ParseError.generic s
  }

/// One assembled document line: either a `[table]`/`[a.b.c]` header (as a dotted
/// path) or a `key = value` pair. Not the public API — consumed by Toml.assemble.
type Toml.Line {
  header (path : List String),
  kv (key : String) (value : Toml.Value),
}

open Toml.Line

// ─── Parser: helpers ───

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

/// Bare TOML key character: alphanumeric, underscore, or hyphen. Quoted keys are
/// not supported (MVP).
def Toml.is_key_char (c : String) : Bool :=
  if is_ident_char c then true else String.beq "-" c

def toml_bare_key_result (r : ParseResult String) : ParseResult String :=
  match r {
    success rem out => if is_empty out then fail (ParseError.custom "expected key") else success rem out,
    fail e => fail e
  }

/// Parse a single bare key (one path segment — no dots).
def Toml.bare_key (input : String) : ParseResult String :=
  toml_bare_key_result (take_while Toml.is_key_char input)

/// Parse a dotted key path (`a.b.c`), used for table headers. A plain `[a]`
/// header parses as a one-element path.
def Toml.dotted_path (input : String) : ParseResult (List String) :=
  separated_by (tag ".") Toml.bare_key input

// ─── Parser: scalar values ───

/// Parse a single character that is not a quote, backslash, or raw newline
/// (single-line strings only — no multi-line strings in the MVP grammar).
def toml_string_char_ok (input : String) (ch : String) : ParseResult String :=
  if is_toml_string_char ch then success (String.drop 1 input) ch
  else fail (ParseError.custom "invalid string character")

def is_toml_string_char (c : String) : Bool :=
  if String.beq "\"" c then false
  else if String.beq "\\" c then false
  else if String.beq "\n" c then false
  else true

def Toml.parse_string_char (input : String) : ParseResult String :=
  if is_empty input
  then fail (ParseError.custom "expected string character")
  else toml_string_char_ok input (String.slice input 0 1)

/// Named escape sequences supported: `\" \\ \n \t \r` (a subset of JSON's set —
/// no `\/`, no `\b`/`\f`, no `\uXXXX`, per the MVP grammar).
def toml_match_escape (s : String) : String :=
  if String.beq "\\\"" s then "\""
  else if String.beq "\\\\" s then "\\"
  else if String.beq "\\n" s then "\n"
  else if String.beq "\\t" s then "\t"
  else if String.beq "\\r" s then "\r"
  else s

def toml_parse_escape_result (r : ParseResult String) : ParseResult String :=
  match r {
    success rem out => success rem (toml_match_escape out),
    fail e => fail e
  }

def Toml.parse_escape (input : String) : ParseResult String :=
  toml_parse_escape_result (alt_fold
    [tag "\\\"",
     tag "\\\\",
     tag "\\n",
     tag "\\t",
     tag "\\r"]
    input)

def Toml.parse_string_content (input : String) : ParseResult (List String) :=
  many0 (alt Toml.parse_escape Toml.parse_string_char) input

@[partial]
def toml_concat_list_body (hd : String) (tl : List String) : String :=
  String.concat hd (Toml.concat_list tl)

def Toml.concat_list (ss : List String) : String :=
  match ss {
    List.empty => "",
    List.cons hd tl => toml_concat_list_body hd tl
  }

def toml_parse_string_close (r : ParseResult String) (s : String) : ParseResult Toml.Value :=
  match r {
    success rem _ => success rem (string s),
    fail e => fail e
  }

@[partial]
def toml_parse_string_content_result (r : ParseResult (List String)) : ParseResult Toml.Value :=
  match r {
    success rem chars => toml_parse_string_close (tag "\"" rem) (Toml.concat_list chars),
    fail e => fail e
  }

@[partial]
def toml_parse_string_open (r : ParseResult String) : ParseResult Toml.Value :=
  match r {
    success rem _ => toml_parse_string_content_result (Toml.parse_string_content rem),
    fail e => fail e
  }

/// Parse a TOML string
def Toml.parse_string (input : String) : ParseResult Toml.Value :=
  toml_parse_string_open (tag "\"" input)

def Toml.neg_i64 (n : I64) : I64 := 0 - n

def toml_parse_integer_negative (r : ParseResult I64) : ParseResult I64 :=
  match r {
    success rem n => success rem (Toml.neg_i64 n),
    fail _ => fail (ParseError.custom "expected digits after -")
  }

@[partial]
def toml_parse_integer_result (r : ParseResult String) (orig : String) : ParseResult I64 :=
  match r {
    success rem _ => toml_parse_integer_negative (number rem),
    fail _ => number orig
  }

/// Parse a signed integer. Note: this happily parses the integer prefix of a
/// float literal (e.g. "1" out of "1.5") — the trailing ".5" is what causes the
/// enclosing kv/array parse to fail overall (floats are unsupported; see the
/// explicit-parse-error tests below for why this still surfaces as a real error
/// rather than a silent misparse).
def Toml.parse_integer (input : String) : ParseResult I64 :=
  toml_parse_integer_result (tag "-" input) input

def toml_integer_value (n : I64) : Toml.Value := integer n

def Toml.parse_integer_value (input : String) : ParseResult Toml.Value :=
  map_parse toml_integer_value Toml.parse_integer input

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

/// A single-line array element — scalars only (bool/string/integer), never an
/// array or table, per the MVP grammar.
def Toml.parse_scalar (input : String) : ParseResult Toml.Value :=
  alt_fold [Toml.parse_bool, Toml.parse_string, Toml.parse_integer_value] input

def toml_parse_array_result (r : ParseResult (List Toml.Value)) : ParseResult Toml.Value :=
  match r {
    success rem elems => success rem (array elems),
    fail e => fail e
  }

@[partial]
def toml_parse_array_body (input : String) : ParseResult (List Toml.Value) :=
  delimited_by toml_ws (separated_by toml_comma Toml.parse_scalar) toml_ws input

/// Parse a single-line array of scalars, e.g. `["a", "b"]` or `[1, 2, 3]`.
@[partial]
def Toml.parse_array (input : String) : ParseResult Toml.Value :=
  toml_parse_array_result (delimited_by (tag "[") toml_parse_array_body (tag "]") input)

/// Parse any TOML value that can appear on the right-hand side of `key = value`.
@[partial]
def Toml.parse_value (input : String) : ParseResult Toml.Value :=
  alt_fold [Toml.parse_bool, Toml.parse_string, Toml.parse_array, Toml.parse_integer_value] input

// ─── Parser: lines (headers / key-value pairs) ───

/// Parse a `[table]` / `[a.b.c]` table header, returning the dotted path.
def Toml.parse_header (input : String) : ParseResult (List String) :=
  delimited_by (tag "[") Toml.dotted_path (tag "]") input

def toml_line_of_header (path : List String) : Toml.Line := header path

def Toml.parse_header_line (input : String) : ParseResult Toml.Line :=
  map_parse toml_line_of_header Toml.parse_header input

def toml_parse_kv_value (r : ParseResult Toml.Value) (key : String) : ParseResult (Pair String Toml.Value) :=
  match r {
    success rem v => success rem (Pair.pair key v),
    fail e => fail e
  }

def toml_kv_after_eq (r : ParseResult String) (key : String) : ParseResult (Pair String Toml.Value) :=
  match r {
    success rem _ => toml_parse_kv_value (Toml.parse_value rem) key,
    fail e => fail e
  }

def toml_kv_eq (rem : String) (key : String) : ParseResult (Pair String Toml.Value) :=
  toml_kv_after_eq (toml_eq rem) key

def toml_kv_key (r : ParseResult String) : ParseResult (Pair String Toml.Value) :=
  match r {
    success rem key => toml_kv_eq rem key,
    fail e => fail e
  }

/// Parse a `key = value` pair. Note: `key` is always a single bare segment — a
/// dotted key like `a.b = 1` is NOT supported outside table headers (MVP scope).
def Toml.parse_kv (input : String) : ParseResult (Pair String Toml.Value) :=
  toml_kv_key (Toml.bare_key input)

def toml_line_of_kv (p : Pair String Toml.Value) : Toml.Line :=
  match p { Pair.pair k v => kv k v }

def Toml.parse_kv_line (input : String) : ParseResult Toml.Line :=
  map_parse toml_line_of_kv Toml.parse_kv input

/// Parse one document line's content (either a header or a kv pair) — does not
/// itself handle blank lines or the trailing newline; see Toml.parse_one_line.
def Toml.parse_line (input : String) : ParseResult Toml.Line :=
  alt Toml.parse_header_line Toml.parse_kv_line input

// ─── Parser: document (blank-line skipping, one line at a time) ───

def toml_one_line_eol (rem : String) (line : Toml.Line) : ParseResult (Option Toml.Line) :=
  if is_empty rem then success rem (Option.some line)
  else if String.starts_with "\n" rem then success (String.drop 1 rem) (Option.some line)
  else fail (ParseError.custom "expected newline after line")

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
/// followed by a newline or EOF.
// NOTE: `is_empty rem` here must FAIL, not succeed — many0 (used by Toml.document
// below) has no zero-consumption guard, so a parser that succeeds without
// consuming input on an already-empty remainder loops forever. Failing here lets
// many0 stop naturally via its own `fail _ => success input List.empty` branch.
def toml_one_line_check_blank (rem : String) : ParseResult (Option Toml.Line) :=
  if is_empty rem then fail (ParseError.custom "no more lines")
  else if String.starts_with "\n" rem then success (String.drop 1 rem) Option.none
  else toml_one_line_parse rem

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

@[partial]
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

// ─── Document assembly: lines -> nested table ───

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

/// Insert `value` at `path` within `root`, creating any missing intermediate
/// tables along the way (path-copying: existing sibling keys are preserved).
def Toml.insert_at_path (path : List String) (value : Toml.Value) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match path {
    List.empty => root,
    List.cons key rest => toml_insert_at_path_step key rest value root
  }

@[partial]
def toml_insert_at_path_step (key : String) (rest : List String) (value : Toml.Value) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match rest {
    List.empty => Map.insert key value root,
    List.cons _ _ =>
      let sub := Toml.sub_table key root in
      Map.insert key (table (Toml.insert_at_path rest value sub)) root
  }

def Toml.fold_line_body (path : List String) (root : BTreeMap String Toml.Value) (line : Toml.Line) : Pair (List String) (BTreeMap String Toml.Value) :=
  match line {
    header new_path => Pair.pair new_path (Toml.insert_at_path new_path (table BTreeMap.empty) root),
    kv key value => Pair.pair path (Toml.insert_at_path (List.append path [key]) value root)
  }

def Toml.fold_line (acc : Pair (List String) (BTreeMap String Toml.Value)) (line : Toml.Line) : Pair (List String) (BTreeMap String Toml.Value) :=
  match acc {
    Pair.pair path root => Toml.fold_line_body path root line
  }

@[partial]
def Toml.fold_lines (acc : Pair (List String) (BTreeMap String Toml.Value)) (lines : List Toml.Line) : Pair (List String) (BTreeMap String Toml.Value) :=
  match lines {
    List.empty => acc,
    List.cons l rest => Toml.fold_lines (Toml.fold_line acc l) rest
  }

def Toml.assemble_result (p : Pair (List String) (BTreeMap String Toml.Value)) : BTreeMap String Toml.Value :=
  match p { Pair.pair _ root => root }

def Toml.assemble (lines : List Toml.Line) : BTreeMap String Toml.Value :=
  Toml.assemble_result (Toml.fold_lines (Pair.pair List.empty BTreeMap.empty) lines)

// ─── Parser: top-level ───

/// Main parse function: parse a full TOML document into its root table.
@[partial]
def Toml.parse (s : String) : Result Toml.ParseError (BTreeMap String Toml.Value) :=
  match Toml.document s {
    success rem lines =>
      if is_empty rem
      then ok (Toml.assemble lines)
      else err (Toml.ParseError.generic "unexpected trailing input"),
    fail e => err (Toml.from_parse_error e)
  }

// ─── Serializer ───

@[partial]
def Toml.escape_char (c : String) : String :=
  if String.beq "\"" c then "\\\""
  else if String.beq "\\" c then "\\\\"
  else if String.beq "\n" c then "\\n"
  else if String.beq "\t" c then "\\t"
  else if String.beq "\r" c then "\\r"
  else c

@[partial]
def Toml.escape_string (input : String) : String :=
  if is_empty input
  then ""
  else
    let ch := String.slice input 0 1 in
    String.concat (Toml.escape_char ch) (Toml.escape_string (String.drop 1 input))

def Toml.string_to_string (s : String) : String :=
  String.concat "\"" (String.concat (Toml.escape_string s) "\"")

def Toml.bool_to_string (b : Bool) : String :=
  if b then "true" else "false"

@[partial]
def Toml.intercalate_rest (sep : String) (acc : String) (xs : List String) : String :=
  match xs {
    List.empty => acc,
    List.cons hd tl => Toml.intercalate_rest sep (String.concat acc (String.concat sep hd)) tl
  }

def Toml.intercalate (sep : String) (xs : List String) : String :=
  match xs {
    List.empty => "",
    List.cons hd tl => Toml.intercalate_rest sep hd tl
  }

/// Serialize a scalar or array value. NOTE: not meant to be called on a `table`
/// (tables are only ever emitted as `[header]` sections by Toml.render_table) —
/// returns "" defensively if it is.
@[partial]
def Toml.value_to_string (v : Toml.Value) : String :=
  match v {
    string s => Toml.string_to_string s,
    integer n => I64.to_string n,
    boolean b => Toml.bool_to_string b,
    array a => Toml.array_to_string a,
    table _ => ""
  }

@[partial]
def Toml.array_to_string (a : List Toml.Value) : String :=
  String.concat "[" (String.concat (Toml.intercalate "," (List.map Toml.value_to_string a)) "]")

def Toml.is_table (v : Toml.Value) : Bool :=
  match v { table _ => true, _ => false }

def Toml.pair_is_scalar (p : Pair String Toml.Value) : Bool :=
  match p { Pair.pair _ v => Bool.not (Toml.is_table v) }

def Toml.pair_is_table (p : Pair String Toml.Value) : Bool :=
  match p { Pair.pair _ v => Toml.is_table v }

def Toml.scalar_entries (pairs : List (Pair String Toml.Value)) : List (Pair String Toml.Value) :=
  List.filter Toml.pair_is_scalar pairs

def Toml.table_entries (pairs : List (Pair String Toml.Value)) : List (Pair String Toml.Value) :=
  List.filter Toml.pair_is_table pairs

def Toml.kv_line_to_string (p : Pair String Toml.Value) : String :=
  match p { Pair.pair k v => String.concat k (String.concat " = " (Toml.value_to_string v)) }

def Toml.render_header (path : List String) : String :=
  if List.is_empty path
  then ""
  else String.concat "[" (String.concat (Toml.intercalate "." path) "]\n")

def Toml.render_body (header_str : String) (scalars : List (Pair String Toml.Value)) : String :=
  if List.is_empty scalars
  then header_str
  else String.concat header_str (String.concat (Toml.intercalate "\n" (List.map Toml.kv_line_to_string scalars)) "\n")

/// Serialize one table (and everything nested under it) at `path` — root-level
/// scalar/array keys first, then a depth-first walk of nested tables emitting
/// `[dotted.path]` headers followed by their own scalar keys.
@[partial]
def Toml.render_table (path : List String) (t : BTreeMap String Toml.Value) : String :=
  let pairs := BTreeMap.to_list t in
  let scalars := Toml.scalar_entries pairs in
  let tables := Toml.table_entries pairs in
  let body := Toml.render_body (Toml.render_header path) scalars in
  String.concat body (Toml.render_tables path tables)

@[partial]
def Toml.render_tables (path : List String) (tables : List (Pair String Toml.Value)) : String :=
  match tables {
    List.empty => "",
    List.cons p rest => String.concat (Toml.render_one_table path p) (Toml.render_tables path rest)
  }

@[partial]
def Toml.render_one_table (path : List String) (p : Pair String Toml.Value) : String :=
  match p {
    Pair.pair k v => Toml.render_one_table_value (List.append path [k]) v
  }

@[partial]
def Toml.render_one_table_value (path : List String) (v : Toml.Value) : String :=
  match v {
    table t => Toml.render_table path t,
    _ => ""
  }

/// Serialize a root table to a full TOML document.
@[partial]
def Toml.to_string (root : BTreeMap String Toml.Value) : String :=
  Toml.render_table List.empty root

// ─── Show instance ───

instance Show Toml.Value {
  def show (v : Toml.Value) : String := Toml.value_to_string v
}

// ─── Construction helpers ───

def Toml.make_string (s : String) : Toml.Value := string s
def Toml.make_integer (n : I64) : Toml.Value := integer n
def Toml.make_boolean (b : Bool) : Toml.Value := boolean b
def Toml.make_array (a : List Toml.Value) : Toml.Value := array a
def Toml.make_table (t : BTreeMap String Toml.Value) : Toml.Value := table t

// ─── Type checkers ───

def Toml.is_string (v : Toml.Value) : Bool :=
  match v { string _ => true, _ => false }

def Toml.is_integer (v : Toml.Value) : Bool :=
  match v { integer _ => true, _ => false }

def Toml.is_boolean (v : Toml.Value) : Bool :=
  match v { boolean _ => true, _ => false }

def Toml.is_array (v : Toml.Value) : Bool :=
  match v { array _ => true, _ => false }

// (Toml.is_table is defined above, in the Serializer section, where it's first needed.)

// ─── Accessors ───

def Toml.get_string (v : Toml.Value) : Result String String :=
  match v { string s => ok s, _ => err "expected string" }

def Toml.get_integer (v : Toml.Value) : Result String I64 :=
  match v { integer n => ok n, _ => err "expected integer" }

def Toml.get_boolean (v : Toml.Value) : Result String Bool :=
  match v { boolean b => ok b, _ => err "expected boolean" }

def Toml.get_array (v : Toml.Value) : Result String (List Toml.Value) :=
  match v { array a => ok a, _ => err "expected array" }

def Toml.get_table (v : Toml.Value) : Result String (BTreeMap String Toml.Value) :=
  match v { table t => ok t, _ => err "expected table" }

// ─── Table manipulation ───

def Toml.table_get (key : String) (t : BTreeMap String Toml.Value) : Option Toml.Value :=
  Map.lookup key t

def Toml.table_set (key : String) (value : Toml.Value) (t : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  Map.insert key value t

def Toml.table_delete (key : String) (t : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  Map.delete key t

// ─── Tests: parser — scalars ───

@[test]
def test_parse_string_kv : Bool :=
  match Toml.parse "name = \"example\"" {
    ok t => toml_table_lookup_eq "name" t (string "example"),
    err _ => false
  }

@[test]
def test_parse_integer_kv : Bool :=
  match Toml.parse "n = 42" {
    ok t => toml_table_lookup_eq "n" t (integer 42),
    err _ => false
  }

@[test]
def test_parse_negative_integer_kv : Bool :=
  match Toml.parse "n = -42" {
    ok t => toml_table_lookup_eq "n" t (integer (Toml.neg_i64 42)),
    err _ => false
  }

@[test]
def test_parse_bool_kv : Bool :=
  match Toml.parse "a = true\nb = false" {
    ok t => toml_table_lookup_eq "a" t (boolean true) && toml_table_lookup_eq "b" t (boolean false),
    err _ => false
  }

@[test]
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

// ─── Tests: parser — arrays ───

@[test]
def test_parse_int_array : Bool :=
  match Toml.parse "xs = [1, 2, 3]" {
    ok t => toml_table_lookup_eq "xs" t (array [integer 1, integer 2, integer 3]),
    err _ => false
  }

@[test]
def test_parse_string_array : Bool :=
  match Toml.parse "members = [\"core\", \"cli\", \"wasm\"]" {
    ok t => toml_table_lookup_eq "members" t (array [string "core", string "cli", string "wasm"]),
    err _ => false
  }

@[test]
def test_parse_empty_array : Bool :=
  match Toml.parse "xs = []" {
    ok t => toml_table_lookup_eq "xs" t (array List.empty),
    err _ => false
  }

// ─── Tests: parser — headers ───

@[test]
def test_parse_single_header : Bool :=
  match Toml.parse "[mote]\nname = \"example\"" {
    ok t =>
      match Map.lookup "mote" t {
        some v => match v { table sub => toml_table_lookup_eq "name" sub (string "example"), _ => false },
        none => false
      },
    err _ => false
  }

@[test]
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

@[test]
def test_parse_empty_table_header : Bool :=
  match Toml.parse "[dependencies]" {
    ok t =>
      match Toml.table_get "dependencies" t {
        some v => match v { table sub => List.is_empty (BTreeMap.to_list sub), _ => false },
        none => false
      },
    err _ => false
  }

// ─── Tests: parser — explicit unsupported grammar (parse errors) ───

@[test]
def test_parse_float_is_error : Bool :=
  match Toml.parse "x = 1.5" {
    ok _ => false,
    err _ => true
  }

@[test]
def test_parse_array_of_tables_is_error : Bool :=
  match Toml.parse "[[products]]\nname = \"a\"" {
    ok _ => false,
    err _ => true
  }

@[test]
def test_parse_dotted_key_outside_header_is_error : Bool :=
  match Toml.parse "a.b = 1" {
    ok _ => false,
    err _ => true
  }

// ─── Tests: real fixtures ───

/// Verbatim contents of motes/example/mote.toml.
def mote_toml_fixture : String :=
  "[mote]\nname = \"example\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n[dependencies]\n"

@[test]
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

/// Modeled after root Cargo.toml's [workspace] / [workspace.package] sections:
/// a multi-key table, an array-of-strings (members), and a nested dotted header.
def cargo_workspace_toml_fixture : String :=
  "[workspace]\nmembers = [\"core\", \"cli\", \"wasm\"]\n\n[workspace.package]\nversion = \"0.1.2\"\nedition = \"2024\"\nlicense = \"ASL2\"\n"

@[test]
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

@[test]
def test_serialize_scalars : Bool :=
  Toml.value_to_string (string "hi") == "\"hi\"" &&
  Toml.value_to_string (integer 42) == "42" &&
  Toml.value_to_string (integer (Toml.neg_i64 7)) == "-7" &&
  Toml.value_to_string (boolean true) == "true" &&
  Toml.value_to_string (boolean false) == "false"

@[test]
def test_serialize_array : Bool :=
  Toml.value_to_string (array [integer 1, integer 2, integer 3]) == "[1,2,3]"

@[test]
def test_serialize_root_kv : Bool :=
  Toml.to_string (Map.insert "name" (string "example") BTreeMap.empty) == "name = \"example\"\n"

@[test]
def test_serialize_nested_table : Bool :=
  let inner := Map.insert "name" (string "example") BTreeMap.empty in
  let root := Map.insert "mote" (table inner) BTreeMap.empty in
  Toml.to_string root == "[mote]\nname = \"example\"\n"

@[test]
def test_serialize_empty_table : Bool :=
  let root := Map.insert "dependencies" (table BTreeMap.empty) BTreeMap.empty in
  Toml.to_string root == "[dependencies]\n"

// ─── Tests: round-trip ───

@[test]
def test_roundtrip_mote_fixture : Bool :=
  match Toml.parse mote_toml_fixture {
    ok t1 =>
      match Toml.parse (Toml.to_string t1) {
        ok t2 => Toml.table_beq t1 t2,
        err _ => false
      },
    err _ => false
  }

@[test]
def test_roundtrip_cargo_workspace_fixture : Bool :=
  match Toml.parse cargo_workspace_toml_fixture {
    ok t1 =>
      match Toml.parse (Toml.to_string t1) {
        ok t2 => Toml.table_beq t1 t2,
        err _ => false
      },
    err _ => false
  }

@[test]
def test_roundtrip_array : Bool :=
  let root := Map.insert "xs" (array [integer 1, integer 2, integer 3]) BTreeMap.empty in
  match Toml.parse (Toml.to_string root) {
    ok t => Toml.table_beq root t,
    err _ => false
  }

// ─── Tests: helpers ───

@[test]
def test_toml_type_checkers : Bool :=
  Toml.is_string (string "a") &&
  Toml.is_integer (integer 1) &&
  Toml.is_boolean (boolean true) &&
  Toml.is_array (array List.empty) &&
  Toml.is_table (table BTreeMap.empty) &&
  Bool.not (Toml.is_string (integer 1))

@[test]
def test_toml_accessors : Bool :=
  match Toml.get_string (string "a") {
    ok s => s == "a",
    err _ => false
  } &&
  match Toml.get_string (boolean true) {
    ok _ => false,
    err _ => true
  }

@[test]
def test_toml_table_manipulation : Bool :=
  let t1 := Toml.table_set "a" (integer 1) BTreeMap.empty in
  let t2 := Toml.table_set "b" (integer 2) t1 in
  let t3 := Toml.table_delete "a" t2 in
  toml_table_lookup_eq "a" t1 (integer 1) &&
  toml_table_lookup_missing "a" t3 &&
  toml_table_lookup_eq "b" t3 (integer 2)
