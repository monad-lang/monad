// Raw string literals: `r"..."`, `r#"..."#`, `r##"..."##`, ...
//
// Raw strings take their body verbatim -- no `\`-escape processing -- so
// backslash-heavy text (regex, JSON, Windows paths, source code) can be
// written exactly as it should appear. The closing delimiter is `"` followed
// by the same number of `#` as the opener, so by picking a large enough hash
// count any content can be embedded.
//
// Usage: monad test examples/raw_strings.mo

use io {}
open IO {println}

/// A regex with backslashes and a literal `"` -- no doubling required. Uses
/// `r#"..."#` (n=1) so the inner `"` doesn't close the string.
def regex : String := r#"\w+\s*"\s*\w+"#

/// A JSON snippet embedded verbatim (uses `r#"..."#` so the inner `"` is free).
def json_snippet : String := r#"{"name": "monad", "version": "0.1"}"#

/// A Windows path -- backslashes are literal, not escapes.
def win_path : String := r"C:\Users\monad\src\main.mo"

/// Hash-count escalation: to embed the literal text `"##` (a quote and two
/// hashes) in a raw string, use `n = 3` so `"##` (only two hashes) is not a
/// closer -- the closer needs exactly three.
def with_double_hashes : String := r###"a "## b"###

#[test]
def test_regex_verbatim : Bool :=
  // The raw body is the literal characters `\w+\s*"\s*\w+`.
  String.beq regex "\\w+\\s*\"\\s*\\w+"

#[test]
def test_json_snippet : Bool :=
  String.beq json_snippet "{\"name\": \"monad\", \"version\": \"0.1\"}"

#[test]
def test_windows_path : Bool :=
  String.beq win_path "C:\\Users\\monad\\src\\main.mo"

#[test]
def test_hash_escalation : Bool :=
  // Body is `a "## b` (a space, a quote, two hashes, a space, b).
  String.beq with_double_hashes "a \"## b"

#[test]
def test_raw_equals_escaped : Bool :=
  // A raw string with a backslash-n equals an ordinary string that has to
  // double the backslash: `r"\n"` == "\\n".
  String.beq r"\n" "\\n"

#[test]
def test_raw_n0_closes_at_first_quote : Bool :=
  // `r"done"` (n=0) is the raw string `done` -- the first `"` closes it.
  String.beq r"done" "done"

#[test]
def test_raw_n1_keeps_inner_quote : Bool :=
  // `r#"a"b"#` (n=1) keeps the inner `"` in the body -> body `a"b`.
  String.beq r#"a"b"# "a\"b"

def main : IO Unit {
  println regex;
  println json_snippet;
  println win_path;
  println with_double_hashes
}