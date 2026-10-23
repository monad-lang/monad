/// TOML parsing and serialization (MVP subset)
/// Structurally independent from lang/json.mo — no shared Serialize/Deserialize
/// classes (Phase 7 of the JSON plan was deliberately deferred; see
/// plans/bootstrapping/json-parser-serializer-plan.md). Own string-escape helpers,
/// own hand-rolled beq family. `intercalate`/`concat_list` USED to be
/// duplicated here under `Toml.`/`toml_` names (top-level names are not
/// file-scoped, so sharing json.mo's bare globals would have collided);
/// both now come from `std/list.mo`'s `List.intercalate` and
/// `init/string.mo`'s `String.concat_all`, which is safe because there is
/// exactly one definition of each corpus-wide.
/// Supported grammar: `[table]` / `[dotted.nested.table]` headers (including empty
/// tables), `[[array.of.tables]]` headers, `key = value`, double-quoted strings with
/// the escape subset `\" \\ \n \t \r`, integers, booleans, single-line arrays whose
/// elements are scalars or inline tables, inline tables (`{ path = "../x" }`), and
/// `#` comments (whole-line or trailing). A `#` inside a quoted string is ordinary
/// text -- comment stripping happens at the line level, after the value parser has
/// consumed its string, never as a pre-pass over the raw source.
/// Explicitly unsupported (parse error, not silent misparse): floats, dates/times,
/// multi-line/literal strings, and dotted keys outside headers. One restriction on
/// arrays-of-tables: a header may not DESCEND into one (`[[mote]]` then
/// `[mote.modules]`, which full TOML reads as the last element's sub-table). That is
/// reported as an error rather than misparsed -- see `Toml.header_conflict`.
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
use init::string {}
use init::number {}
use parsec::core {
  ParseError, ParseResult, is_empty, parse_error_remaining
}
use parsec::char_preds {is_ident_char}
use parsec::combinators {
  alt, alt_fold, delimited_by, many0, map_parse, separated_by, tag, take_while,
}
use parsec::number {number}

open ParseResult {fail, success}
open Toml.Value {array, boolean, integer, string, table}

// ─── Types ───

/// TOML value type. The parser produces `array` elements that are scalars or
/// inline `table`s -- never a nested `array` -- but the type itself doesn't
/// enforce that, and the serializer renders whatever it is handed.
pub type Toml.Value {
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

def Toml.ParseError.to_string (e : Toml.ParseError) : String :=
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
/// `[[array.of.tables]]` header, or a `key = value` pair -- headers as dotted
/// paths. Not the public API — consumed by Toml.assemble.
type Toml.Line {
  header (path : List String),
  array_header (path : List String),
  kv (key : String) (value : Toml.Value),
}

open Toml.Line {header, array_header, kv}

/// One step of an insertion path into the document being assembled.
///
/// A plain `[a.b]` header's path is all `step_key`, and that is what the
/// assembler used to carry (a bare `List String`). `[[mote]]` is what needs
/// more: the `kv` lines following it belong to the LAST element of the array
/// at `mote`, which no list of keys can name. `step_last` names it.
///
/// `step_last` only ever appears as the FINAL step of the path a header
/// establishes, never as the final step of the path a `kv` line inserts at --
/// that one always ends in a `step_key` for the key itself.
type Toml.PathStep {
  step_key (k : String),
  step_last (k : String),
}

open Toml.PathStep {step_key, step_last}

/// The assembler's state: the header path currently in effect, and the document
/// built so far -- or the reason assembly stopped.
///
/// `asm_error` is TERMINAL: once a header has been rejected there is no
/// well-defined place for the lines after it to go, so they are not assembled
/// rather than being silently attached to the previous header's table. This is
/// the error channel `Toml.assemble` lacked, and it is why it now returns a
/// `Result` -- a conflicting header used to overwrite whatever was there.
type Toml.Asm {
  asm_state (steps : List Toml.PathStep) (root : BTreeMap String Toml.Value),
  asm_error (msg : String),
}

open Toml.Asm {asm_state, asm_error}

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
    success rem out => if is_empty out then fail (ParseError.custom "expected key" rem) else success rem out,
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
  else fail (ParseError.custom "invalid string character" input)

def is_toml_string_char (c : String) : Bool :=
  if String.beq "\"" c then false
  else if String.beq "\\" c then false
  else if String.beq "\n" c then false
  else true

def Toml.parse_string_char (input : String) : ParseResult String :=
  if is_empty input
  then fail (ParseError.custom "expected string character" input)
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

#[partial]
def toml_parse_string_close (r : ParseResult String) (s : String) : ParseResult Toml.Value :=
  match r {
    success rem _ => success rem (string s),
    fail e => fail e
  }

#[partial]
def toml_parse_string_content_result (r : ParseResult (List String)) : ParseResult Toml.Value :=
  match r {
    success rem chars => toml_parse_string_close (tag "\"" rem) (String.concat_list chars),
    fail e => fail e
  }

#[partial]
def toml_parse_string_open (r : ParseResult String) : ParseResult Toml.Value :=
  match r {
    success rem _ => toml_parse_string_content_result (Toml.parse_string_content rem),
    fail e => fail e
  }

/// Parse a TOML string
def Toml.parse_string (input : String) : ParseResult Toml.Value :=
  toml_parse_string_open (tag "\"" input)


def toml_parse_integer_negative (r : ParseResult I64) : ParseResult I64 :=
  match r {
    success rem n => success rem (I64.neg n),
    fail e => fail (ParseError.custom "expected digits after -" (parse_error_remaining e))
  }

#[partial]
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

/// A scalar value: bool, string or integer. Never an array or a table.
///
/// Used to be described as "an array element"; `Toml.parse_array_element` is
/// that now, and it is this plus an inline table.
def Toml.parse_scalar (input : String) : ParseResult Toml.Value :=
  alt_fold [Toml.parse_bool, Toml.parse_string, Toml.parse_integer_value] input

def toml_parse_array_result (r : ParseResult (List Toml.Value)) : ParseResult Toml.Value :=
  match r {
    success rem elems => success rem (array elems),
    fail e => fail e
  }

/// Whitespace INSIDE an array: horizontal space, newlines, and whole
/// comment lines. Outside an array a newline ends the item
/// (`toml_ws`/`Toml.is_hspace` stop at one, and must keep doing so --
/// the line parser relies on it); between `[` and `]` TOML explicitly
/// allows an array to span lines, which is how this repo's own root
/// `mote.toml` writes `[workspace] members`. Without this the whole
/// manifest failed to parse.
#[partial]
def toml_array_ws (input : String) : ParseResult String :=
  toml_array_ws_go input

/// One pass of "skip blanks, then skip a comment if one starts here",
/// repeated until neither consumes anything. Two-phase rather than one
/// character class because a comment runs to end-of-line and so cannot
/// be expressed as a predicate on a single character.
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

/// One array element: a scalar or an inline table. NOT a nested array --
/// that stays out of the grammar, and an attempt at one is a parse error
/// rather than a misparse.
///
/// Inline tables belong here for a reason beyond completeness: without them
/// `Toml.to_string` could emit a document `Toml.parse` rejects, because the
/// serializer renders a `table` inside an `array` as `{ … }` and had nothing
/// on the reading side to match. Round-tripping is the contract.
#[partial]
def Toml.parse_array_element (input : String) : ParseResult Toml.Value :=
  alt Toml.parse_scalar Toml.parse_inline_table input

#[partial]
def toml_parse_array_body (input : String) : ParseResult (List Toml.Value) :=
  delimited_by toml_array_ws (separated_by toml_array_comma Toml.parse_array_element) toml_array_ws input

/// Parse an array of scalars, on one line (`["a", "b"]`, `[1, 2, 3]`) or
/// spread across several with an optional trailing comma and comments,
/// as this repo's own root `mote.toml` writes its workspace members.
///
/// The trailing comma falls out of the grammar rather than needing a
/// case of its own: `separated_by` stops after the last element it can
/// parse, and the `toml_array_ws` before `]` then consumes the dangling
/// comma's surrounding blanks -- so the body is followed by an optional
/// comma and more whitespace before the bracket.
#[partial]
def Toml.parse_array (input : String) : ParseResult Toml.Value :=
  toml_parse_array_result (delimited_by (tag "[") toml_parse_array_trailing (tag "]") input)

/// The array body plus an optional trailing comma (and whatever blanks
/// or comments follow it) before the closing bracket.
#[partial]
def toml_parse_array_trailing (input : String) : ParseResult (List Toml.Value) :=
  match toml_parse_array_body input {
    success rem elems =>
      if String.starts_with "," rem
      then
        match toml_array_ws (String.drop 1 rem) {
          success rem2 _ => success rem2 elems,
          fail e => fail e,
        }
      else success rem elems,
    fail e => fail e,
  }

/// Build a table from inline-table pairs. A repeated key takes the LAST
/// occurrence, which is what `Map.insert` folding left-to-right gives; TOML
/// forbids the duplicate outright, and rejecting it would need a second pass
/// this parser does not otherwise need.
#[partial]
def Toml.table_of_pairs (pairs : List (Pair String Toml.Value)) : BTreeMap String Toml.Value :=
  Toml.table_of_pairs_go pairs BTreeMap.empty

#[partial]
def Toml.table_of_pairs_go (pairs : List (Pair String Toml.Value)) (acc : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match pairs {
    List.empty => acc,
    List.cons p rest => Toml.table_of_pairs_go rest (Toml.table_of_pairs_one p acc)
  }

def Toml.table_of_pairs_one (p : Pair String Toml.Value) (acc : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match p { Pair.pair k v => Map.insert k v acc }

def toml_inline_table_of_pairs (pairs : List (Pair String Toml.Value)) : Toml.Value :=
  table (Toml.table_of_pairs pairs)

/// The body of an inline table: comma-separated `key = value` pairs, with NO
/// trailing comma.
///
/// Two spec rules live here, and only one of them is free.
///
/// FREE: an inline table may not span lines. `toml_comma`/`toml_ws` are
/// HORIZONTAL-only, so a newline inside the braces simply fails -- the array
/// parser's `toml_array_ws` (which eats newlines and whole comment lines)
/// would have permitted it silently.
///
/// NOT FREE: no trailing comma. This is hand-rolled rather than written with
/// `separated_by` because that combinator CONSUMES a separator it then finds
/// nothing after (`separated_by_loop`'s success arm returns the
/// POST-separator remainder), so `{ a = 1, }` parsed and `tag "}"` never saw
/// the dangling comma. Caught by
/// `test_inline_table_rejects_a_trailing_comma`, which failed before this was
/// written by hand. It matters because TOML allows a trailing comma in an
/// ARRAY (this parser does too, deliberately -- the repo's own root manifest
/// writes one) and forbids it in an inline table, and the Rust host reads
/// manifests with the strict `toml` crate: a manifest this reader accepted
/// and `monad-rs` rejected would be a divergence between the two front ends.
#[partial]
def toml_parse_inline_body (input : String) : ParseResult (List (Pair String Toml.Value)) :=
  toml_inline_body_start (toml_ws input)

#[partial]
def toml_inline_body_start (r : ParseResult String) : ParseResult (List (Pair String Toml.Value)) :=
  match r {
    success rem _ => toml_inline_body_first (Toml.parse_kv rem) rem,
    fail e => fail e
  }

/// No pair at all is the empty inline table (`{}`), not a failure.
#[partial]
def toml_inline_body_first (r : ParseResult (Pair String Toml.Value)) (input : String) : ParseResult (List (Pair String Toml.Value)) :=
  match r {
    success rem p => toml_inline_body_more rem [p],
    fail _ => toml_inline_body_end input List.empty
  }

/// After a pair: a comma means another pair MUST follow. Anything else ends
/// the body. That implication is the entire no-trailing-comma rule.
#[partial]
def toml_inline_body_more (input : String) (acc : List (Pair String Toml.Value)) : ParseResult (List (Pair String Toml.Value)) :=
  match toml_comma input {
    success rem _ => toml_inline_body_next (Toml.parse_kv rem) acc,
    fail _ => toml_inline_body_end input acc
  }

#[partial]
def toml_inline_body_next (r : ParseResult (Pair String Toml.Value)) (acc : List (Pair String Toml.Value)) : ParseResult (List (Pair String Toml.Value)) :=
  match r {
    success rem p => toml_inline_body_more rem (List.append acc [p]),
    fail e => fail e
  }

/// Strip the horizontal space before the closing brace. `toml_comma` failed
/// without consuming anything (`delimited_by` restores its input), so that
/// space is still there and `tag "}"` would fail on it.
#[partial]
def toml_inline_body_end (input : String) (acc : List (Pair String Toml.Value)) : ParseResult (List (Pair String Toml.Value)) :=
  match toml_ws input {
    success rem _ => success rem acc,
    fail e => fail e
  }

/// Parse an inline table (`{ path = "../std" }`, `{}`) -- the dependency
/// spelling `mote.toml` uses everywhere outside this repo, and the reason
/// every manifest in THIS repo is written with sub-table headers instead.
#[partial]
def Toml.parse_inline_table (input : String) : ParseResult Toml.Value :=
  map_parse toml_inline_table_of_pairs (delimited_by (tag "{") toml_parse_inline_body (tag "}")) input

/// Parse any TOML value that can appear on the right-hand side of `key = value`.
#[partial]
def Toml.parse_value (input : String) : ParseResult Toml.Value :=
  alt_fold [Toml.parse_bool, Toml.parse_string, Toml.parse_array, Toml.parse_inline_table, Toml.parse_integer_value] input

// ─── Parser: lines (headers / key-value pairs) ───

/// Parse a `[table]` / `[a.b.c]` table header, returning the dotted path.
def Toml.parse_header (input : String) : ParseResult (List String) :=
  delimited_by (tag "[") Toml.dotted_path (tag "]") input

def toml_line_of_header (path : List String) : Toml.Line := header path

def Toml.parse_header_line (input : String) : ParseResult Toml.Line :=
  map_parse toml_line_of_header Toml.parse_header input

/// Parse an `[[array.of.tables]]` header, returning the dotted path.
def Toml.parse_array_header (input : String) : ParseResult (List String) :=
  delimited_by (tag "[[") Toml.dotted_path (tag "]]") input

def toml_line_of_array_header (path : List String) : Toml.Line := array_header path

def Toml.parse_array_header_line (input : String) : ParseResult Toml.Line :=
  map_parse toml_line_of_array_header Toml.parse_array_header input

def toml_parse_kv_value (r : ParseResult Toml.Value) (key : String) : ParseResult (Pair String Toml.Value) :=
  match r {
    success rem v => success rem (Pair.pair key v),
    fail e => fail e
  }

#[partial]
def toml_kv_after_eq (r : ParseResult String) (key : String) : ParseResult (Pair String Toml.Value) :=
  match r {
    success rem _ => toml_parse_kv_value (Toml.parse_value rem) key,
    fail e => fail e
  }

#[partial]
def toml_kv_eq (rem : String) (key : String) : ParseResult (Pair String Toml.Value) :=
  toml_kv_after_eq (toml_eq rem) key

#[partial]
def toml_kv_key (r : ParseResult String) : ParseResult (Pair String Toml.Value) :=
  match r {
    success rem key => toml_kv_eq rem key,
    fail e => fail e
  }

/// Parse a `key = value` pair. Note: `key` is always a single bare segment — a
/// dotted key like `a.b = 1` is NOT supported outside table headers (MVP scope).
///
/// `#[partial]` here and on the three helpers below it: an inline table's body
/// is a list of these pairs, so `parse_kv -> toml_kv_key -> toml_kv_eq ->
/// toml_kv_after_eq -> Toml.parse_value -> Toml.parse_inline_table ->
/// toml_parse_inline_body -> parse_kv` is a real cycle. It terminates on input
/// length -- every step through it has consumed at least the `{` -- which is
/// not a structural subterm relation the checker can see, the same reason
/// every combinator in `lang/src/parser/` carries the attribute.
#[partial]
def Toml.parse_kv (input : String) : ParseResult (Pair String Toml.Value) :=
  toml_kv_key (Toml.bare_key input)

def toml_line_of_kv (p : Pair String Toml.Value) : Toml.Line :=
  match p { Pair.pair k v => kv k v }

def Toml.parse_kv_line (input : String) : ParseResult Toml.Line :=
  map_parse toml_line_of_kv Toml.parse_kv input

/// Parse one document line's content (either a header or a kv pair) — does not
/// itself handle blank lines or the trailing newline; see Toml.parse_one_line.
/// `[[x]]` is tried before `[x]`. It would win anyway -- the plain header's
/// `Toml.bare_key` fails on the second `[` -- but ordering it first is what
/// makes `alt_fold` report the array header's own error for a malformed
/// `[[x]` rather than the plain header's confusing one.
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

/// Consume a `#` comment's text, leaving the newline (if any) in place for the
/// caller's own end-of-line handling.
def toml_drop_comment (rem : String) : String :=
  toml_drop_comment_result (take_while toml_is_not_newline rem)

#[partial]
def toml_one_line_eol (rem : String) (line : Toml.Line) : ParseResult (Option Toml.Line) :=
  if is_empty rem then success rem (Option.some line)
  else if String.starts_with "\n" rem then success (String.drop 1 rem) (Option.some line)
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
/// followed by a newline or EOF.
// NOTE: `is_empty rem` here must FAIL, not succeed — many0 (used by Toml.document
// below) has no zero-consumption guard, so a parser that succeeds without
// consuming input on an already-empty remainder loops forever. Failing here lets
// many0 stop naturally via its own `fail _ => success input List.empty` branch.
def toml_one_line_check_blank (rem : String) : ParseResult (Option Toml.Line) :=
  if is_empty rem then fail (ParseError.custom "no more lines" rem)
  else if String.starts_with "\n" rem then success (String.drop 1 rem) Option.none
  else if String.starts_with "#" rem then toml_comment_line (toml_drop_comment rem)
  else toml_one_line_parse rem

/// A whole-line comment yields no `Toml.Line`, exactly like a blank line.
def toml_comment_line (rem : String) : ParseResult (Option Toml.Line) :=
  if String.starts_with "\n" rem then success (String.drop 1 rem) Option.none
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

/// Insert `value` at `steps` within `root`, creating any missing intermediate
/// tables along the way (path-copying: existing sibling keys are preserved).
///
/// Was `Toml.insert_at_path` over a `List String`; it takes `Toml.PathStep`s
/// now so that a `step_last` can direct the insertion into the last element of
/// an array of tables, which is where every `kv` after an `[[x]]` header goes.
def Toml.insert_at_steps (steps : List Toml.PathStep) (value : Toml.Value) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match steps {
    List.empty => root,
    List.cons s rest => toml_insert_step s rest value root
  }

#[partial]
def toml_insert_step (s : Toml.PathStep) (rest : List Toml.PathStep) (value : Toml.Value) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match s {
    step_key k => toml_insert_key_step k rest value root,
    step_last k => toml_insert_last_step k rest value root
  }

#[partial]
def toml_insert_key_step (key : String) (rest : List Toml.PathStep) (value : Toml.Value) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match rest {
    List.empty => Map.insert key value root,
    List.cons _ _ =>
      let sub := Toml.sub_table key root in
      Map.insert key (table (Toml.insert_at_steps rest value sub)) root
  }

/// Descend into the LAST element of the array of tables at `key`.
///
/// An empty array here cannot happen through the assembler: `step_last k` is
/// only ever produced by an `[[k]]` header, and that header pushes an element
/// before the path is adopted. The empty case is a genuine no-op rather than
/// an error -- there is nothing to report to, and inventing an element would
/// fabricate a document section nobody wrote. It has to be guarded explicitly
/// to BE a no-op: writing the empty result back would replace whatever `key`
/// held with `[]`, which is destructive in exactly the case the guard says
/// cannot arise.
#[partial]
def toml_insert_last_step (key : String) (rest : List Toml.PathStep) (value : Toml.Value) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  toml_insert_last_into (Toml.array_at key root) key rest value root

#[partial]
def toml_insert_last_into (elems : List Toml.Value) (key : String) (rest : List Toml.PathStep) (value : Toml.Value) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  if List.is_empty elems
  then root
  else Map.insert key (array (toml_update_last elems rest value)) root

#[partial]
def toml_update_last (elems : List Toml.Value) (rest : List Toml.PathStep) (value : Toml.Value) : List Toml.Value :=
  match elems {
    List.empty => List.empty,
    List.cons e tl =>
      if List.is_empty tl
      then [table (Toml.insert_at_steps rest value (toml_sub_table_value e))]
      else List.cons e (toml_update_last tl rest value)
  }

/// Every segment as a plain table key -- a `[a.b]` header's insertion path.
#[partial]
def Toml.key_steps (path : List String) : List Toml.PathStep :=
  match path {
    List.empty => List.empty,
    List.cons k rest => List.cons (step_key k) (Toml.key_steps rest)
  }

/// The same, except the LAST segment addresses an array's last element --
/// an `[[a.b]]` header's insertion path.
#[partial]
def Toml.array_steps (path : List String) : List Toml.PathStep :=
  match path {
    List.empty => List.empty,
    List.cons k rest =>
      if List.is_empty rest
      then [step_last k]
      else List.cons (step_key k) (Toml.array_steps rest)
  }

/// The table currently at `path`, or empty when absent.
///
/// A header re-inserts the table it FINDS rather than an empty one, which is
/// what stops `[a.b]` … `[a]` from erasing `b`. The old assembler wrote
/// `table BTreeMap.empty` unconditionally and silently dropped everything
/// already under the shorter path; no manifest in the corpus writes headers
/// in that order, which is why it went unnoticed.
#[partial]
def Toml.table_at_path (path : List String) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match path {
    List.empty => root,
    List.cons k rest => Toml.table_at_path rest (Toml.sub_table k root)
  }

/// Why a header cannot be applied to the document assembled so far, or
/// `none` when it can.
///
/// Every answer here is a case full TOML defines and this parser does not
/// implement, reported rather than silently misparsed -- the same contract
/// the grammar note at the head of this file states for floats and
/// multi-line strings.
#[partial]
def Toml.header_conflict (path : List String) (is_array : Bool) (root : BTreeMap String Toml.Value) : Option String :=
  match path {
    List.empty => Option.none,
    List.cons k rest => toml_header_conflict_step k rest is_array root
  }

#[partial]
def toml_header_conflict_step (k : String) (rest : List String) (is_array : Bool) (root : BTreeMap String Toml.Value) : Option String :=
  match rest {
    List.empty => toml_header_conflict_final k is_array (Map.lookup k root),
    List.cons _ _ => toml_header_conflict_descend k rest is_array (Map.lookup k root)
  }

def toml_header_conflict_final (k : String) (is_array : Bool) (found : Option Toml.Value) : Option String :=
  match found {
    none => Option.none,
    some v => toml_header_conflict_final_value k is_array v
  }

#[partial]
def toml_header_conflict_final_value (k : String) (is_array : Bool) (v : Toml.Value) : Option String :=
  match v {
    table _ =>
      if is_array
      then Option.some (String.concat "[[" (String.concat k "]] conflicts with the table already defined at that key"))
      else Option.none,
    array _ =>
      if is_array
      then Option.none
      else Option.some (String.concat "[" (String.concat k "] conflicts with the array of tables already defined at that key")),
    _ => Option.some (String.concat "header key " (String.concat k " is already an ordinary value, not a table"))
  }

#[partial]
def toml_header_conflict_descend (k : String) (rest : List String) (is_array : Bool) (found : Option Toml.Value) : Option String :=
  match found {
    none => Toml.header_conflict rest is_array BTreeMap.empty,
    some v => toml_header_conflict_descend_value k rest is_array v
  }

#[partial]
def toml_header_conflict_descend_value (k : String) (rest : List String) (is_array : Bool) (v : Toml.Value) : Option String :=
  match v {
    table t => Toml.header_conflict rest is_array t,
    array _ => Option.some (String.concat "a header may not descend into the array of tables " (String.concat k " (unsupported; write the value as an inline table instead)")),
    _ => Option.some (String.concat "header key " (String.concat k " is an ordinary value, not a table"))
  }

/// Append a fresh empty table to the array of tables at `path`, creating the
/// array if this is the first `[[path]]` header.
#[partial]
def Toml.push_array_table (path : List String) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match path {
    List.empty => root,
    List.cons k rest => toml_push_array_step k rest root
  }

#[partial]
def toml_push_array_step (k : String) (rest : List String) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
  match rest {
    List.empty => Map.insert k (array (List.append (Toml.array_at k root) [table BTreeMap.empty])) root,
    List.cons _ _ => Map.insert k (table (Toml.push_array_table rest (Toml.sub_table k root))) root
  }

def Toml.apply_header (new_path : List String) (root : BTreeMap String Toml.Value) : Toml.Asm :=
  toml_apply_header_checked new_path root (Toml.header_conflict new_path false root)

#[partial]
def toml_apply_header_checked (new_path : List String) (root : BTreeMap String Toml.Value) (conflict : Option String) : Toml.Asm :=
  match conflict {
    some m => asm_error m,
    none =>
      let steps := Toml.key_steps new_path in
      asm_state steps (Toml.insert_at_steps steps (table (Toml.table_at_path new_path root)) root)
  }

def Toml.apply_array_header (new_path : List String) (root : BTreeMap String Toml.Value) : Toml.Asm :=
  toml_apply_array_header_checked new_path root (Toml.header_conflict new_path true root)

#[partial]
def toml_apply_array_header_checked (new_path : List String) (root : BTreeMap String Toml.Value) (conflict : Option String) : Toml.Asm :=
  match conflict {
    some m => asm_error m,
    none => asm_state (Toml.array_steps new_path) (Toml.push_array_table new_path root)
  }

def Toml.fold_line_body (steps : List Toml.PathStep) (root : BTreeMap String Toml.Value) (line : Toml.Line) : Toml.Asm :=
  match line {
    header new_path => Toml.apply_header new_path root,
    array_header new_path => Toml.apply_array_header new_path root,
    kv key value => asm_state steps (Toml.insert_at_steps (List.append steps [step_key key]) value root)
  }

def Toml.fold_line (acc : Toml.Asm) (line : Toml.Line) : Toml.Asm :=
  match acc {
    asm_state steps root => Toml.fold_line_body steps root line,
    asm_error m => asm_error m
  }

#[partial]
def Toml.fold_lines (acc : Toml.Asm) (lines : List Toml.Line) : Toml.Asm :=
  match lines {
    List.empty => acc,
    List.cons l rest => Toml.fold_lines (Toml.fold_line acc l) rest
  }

def Toml.assemble_result (a : Toml.Asm) : Result Toml.ParseError (BTreeMap String Toml.Value) :=
  match a {
    asm_state _ root => ok root,
    asm_error m => err (Toml.ParseError.generic m)
  }

def Toml.assemble (lines : List Toml.Line) : Result Toml.ParseError (BTreeMap String Toml.Value) :=
  Toml.assemble_result (Toml.fold_lines (asm_state List.empty BTreeMap.empty) lines)

// ─── Parser: top-level ───

/// Main parse function: parse a full TOML document into its root table.
#[partial]
pub def Toml.parse (s : String) : Result Toml.ParseError (BTreeMap String Toml.Value) :=
  match Toml.document s {
    success rem lines =>
      if is_empty rem
      then Toml.assemble lines
      else err (Toml.ParseError.generic "unexpected trailing input"),
    fail e => err (Toml.from_parse_error e)
  }

// ─── Serializer ───

#[partial]
def Toml.escape_char (c : String) : String :=
  if String.beq "\"" c then "\\\""
  else if String.beq "\\" c then "\\\\"
  else if String.beq "\n" c then "\\n"
  else if String.beq "\t" c then "\\t"
  else if String.beq "\r" c then "\\r"
  else c

#[partial]
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

/// Serialize any value to its inline spelling. A `table` renders as an inline
/// table (`{ k = v }`), which is reached two ways: as an element of an array,
/// and as an entry of an `[[x]]` element (`Toml.render_array_elem` renders ALL
/// of an element's entries inline, since a nested `[x.y]` header under an array
/// element is the one thing the parser refuses).
///
/// This arm used to return `""` — a table value inside an array serialized to
/// nothing at all, which is silent data loss and unparseable output. The parser
/// gained `Toml.parse_array_element` in the same change so the two agree.
#[partial]
def Toml.value_to_string (v : Toml.Value) : String :=
  match v {
    string s => Toml.string_to_string s,
    integer n => I64.to_string n,
    boolean b => Toml.bool_to_string b,
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
  match p { Pair.pair k v => String.concat k (String.concat " = " (Toml.value_to_string v)) }

def Toml.render_header (path : List String) : String :=
  if List.is_empty path
  then ""
  else String.concat "[" (String.concat (List.intercalate "." path) "]\n")

def Toml.render_array_header (path : List String) : String :=
  if List.is_empty path
  then ""
  else String.concat "[[" (String.concat (List.intercalate "." path) "]]\n")

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
/// what `Toml.header_conflict` refuses to read back.
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
def Toml.to_string (root : BTreeMap String Toml.Value) : String :=
  Toml.render_table List.empty root

// ─── Show instance ───

pub instance Show Toml.Value {
  def show (v : Toml.Value) : String := Toml.value_to_string v
}

// ─── Construction helpers ───

pub def Toml.make_string (s : String) : Toml.Value := string s
pub def Toml.make_integer (n : I64) : Toml.Value := integer n
pub def Toml.make_boolean (b : Bool) : Toml.Value := boolean b
pub def Toml.make_array (a : List Toml.Value) : Toml.Value := array a
pub def Toml.make_table (t : BTreeMap String Toml.Value) : Toml.Value := table t

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

pub def Toml.get_string (v : Toml.Value) : Result String String :=
  match v { string s => ok s, _ => err "expected string" }

pub def Toml.get_integer (v : Toml.Value) : Result String I64 :=
  match v { integer n => ok n, _ => err "expected integer" }

pub def Toml.get_boolean (v : Toml.Value) : Result String Bool :=
  match v { boolean b => ok b, _ => err "expected boolean" }

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

// ─── Tests: parser — explicit unsupported grammar (parse errors) ───

#[test]
def test_parse_float_is_error : Bool :=
  match Toml.parse "x = 1.5" {
    ok _ => false,
    err _ => true
  }

// `[[products]]` and `{ … }` used to live in this section as
// "is an error" tests. Both are supported now; the assertions below are the
// same two documents, read for their VALUE rather than for their rejection.

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

/// A DOTTED array-of-tables header: the elements live at `a.b`, and the
/// steps a following `kv` uses are `[step_key "a", step_last "b"]`.
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

// ─── Tests: header conflicts (reported, never misparsed) ───

/// The one array-of-tables case full TOML defines and this parser does not:
/// `[mote.modules]` after `[[mote]]` means the LAST element's sub-table.
#[test]
def test_header_may_not_descend_into_an_array_of_tables : Bool :=
  match Toml.parse "[[mote]]\nname = \"a\"\n\n[mote.modules]\nx = 1\n" {
    ok _ => false,
    err _ => true
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

/// A re-entered SHORTER header must not erase what the longer one built.
/// This assembled to `a = {}` before the rewrite -- silent data loss.
#[test]
def test_reentering_a_shorter_header_keeps_the_nested_table : Bool :=
  match Toml.parse "[a.b]\nx = 1\n\n[a]\ny = 2\n" {
    ok t => toml_a_keys t == ["b", "y"],
    err _ => false
  }

#[partial]
def toml_a_keys (t : BTreeMap String Toml.Value) : List String :=
  toml_keys_of_table (Map.lookup "a" t)

#[test]
def test_parse_dotted_key_outside_header_is_error : Bool :=
  match Toml.parse "a.b = 1" {
    ok _ => false,
    err _ => true
  }

/// A nested array stays out of the grammar: an array element is a scalar or
/// an inline table, and nothing else.
#[test]
def test_parse_nested_array_is_error : Bool :=
  match Toml.parse "xs = [[1, 2]]" {
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
/// a [lib] target, and dependencies as SUB-TABLE headers rather than inline
/// tables -- which is exactly why the repo's manifests are written that way,
/// since this parser has headers and not inline tables.
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

// ─── Tests: helpers ───

#[test]
def test_toml_type_checkers : Bool :=
  Toml.is_string (string "a") &&
  Toml.is_integer (integer 1) &&
  Toml.is_boolean (boolean true) &&
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
  }

#[test]
def test_toml_table_manipulation : Bool :=
  let t1 := Toml.table_set "a" (integer 1) BTreeMap.empty in
  let t2 := Toml.table_set "b" (integer 2) t1 in
  let t3 := Toml.table_delete "a" t2 in
  toml_table_lookup_eq "a" t1 (integer 1) &&
  toml_table_lookup_missing "a" t3 &&
  toml_table_lookup_eq "b" t3 (integer 2)

// ─── Multi-line arrays ──────────────────────────────────────────────
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
