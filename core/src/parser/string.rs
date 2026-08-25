use nom::branch::alt;
use nom::bytes::streaming::{is_not, take_while_m_n};
use nom::character::anychar;
use nom::character::streaming::{char, multispace1};
use nom::combinator::{complete, map, map_opt, map_res, value, verify};
use nom::error::{FromExternalError, ParseError};
use nom::multi::fold;
use nom::sequence::{delimited, preceded};
use nom::{IResult, Parser};

// parser combinators are constructed from the bottom up:
// first we write parsers for the smallest elements (escaped characters),
// then combine them into larger parsers.

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
fn parse_unicode<'a, E>(input: &'a str) -> IResult<&'a str, char, E>
where
  E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  // `take_while_m_n` parses between `m` and `n` bytes (inclusive) that match
  // a predicate. `parse_hex` here parses between 1 and 6 hexadecimal numerals.
  let parse_hex = take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit());

  // `preceded` takes a prefix parser, and if it succeeds, returns the result
  // of the body parser. In this case, it parses u{XXXX}.
  let parse_delimited_hex = preceded(
    char('u'),
    // `delimited` is like `preceded`, but it parses both a prefix and a suffix.
    // It returns the result of the middle parser. In this case, it parses
    // {XXXX}, where XXXX is 1 to 6 hex numerals, and returns XXXX
    delimited(char('{'), parse_hex, char('}')),
  );

  // `map_res` takes the result of a parser and applies a function that returns
  // a Result. In this case we take the hex bytes from parse_hex and attempt to
  // convert them to a u32.
  let parse_u32 = map_res(parse_delimited_hex, move |hex| u32::from_str_radix(hex, 16));

  // map_opt is like map_res, but it takes an Option instead of a Result. If
  // the function returns None, map_opt returns an error. In this case, because
  // not all u32 values are valid unicode code points, we have to fallibly
  // convert to char with from_u32.
  map_opt(parse_u32, std::char::from_u32).parse(input)
}

/// Parse an escaped character: \n, \t, \r, \u{00AC}, etc.
fn parse_escaped_char<'a, E>(input: &'a str) -> IResult<&'a str, char, E>
where
  E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  preceded(
    char('\\'),
    // `alt` tries each parser in sequence, returning the result of
    // the first successful match
    alt((
      parse_unicode,
      // The `value` parser returns a fixed value (the first argument) if its
      // parser (the second argument) succeeds. In these cases, it looks for
      // the marker characters (n, r, t, etc) and returns the matching
      // character (\n, \r, \t, etc).
      value('\n', char('n')),
      value('\r', char('r')),
      value('\t', char('t')),
      value('\u{08}', char('b')),
      value('\u{0C}', char('f')),
      value('\\', char('\\')),
      value('/', char('/')),
      value('"', char('"')),
      value('\'', char('\'')),
    )),
  )
  .parse(input)
}

/// Parse a backslash, followed by any amount of whitespace. This is used later
/// to discard any escaped whitespace.
fn parse_escaped_whitespace<'a, E: ParseError<&'a str>>(
  input: &'a str,
) -> IResult<&'a str, &'a str, E> {
  preceded(char('\\'), multispace1).parse(input)
}

/// Parse a non-empty block of text that doesn't include \ or "
fn parse_literal<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
  // `is_not` parses a string of 0 or more characters that aren't one of the
  // given characters.
  let not_quote_slash = is_not("\"\\");

  // `verify` runs a parser, then runs a verification function on the output of
  // the parser. The verification function accepts out output only if it
  // returns true. In this case, we want to ensure that the output of is_not
  // is non-empty.
  verify(not_quote_slash, |s: &str| !s.is_empty()).parse(input)
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringFragment<'a> {
  Literal(&'a str),
  EscapedChar(char),
  EscapedWS,
}

/// Combine parse_literal, parse_escaped_whitespace, and parse_escaped_char
/// into a StringFragment.
fn parse_fragment<'a, E>(input: &'a str) -> IResult<&'a str, StringFragment<'a>, E>
where
  E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  alt((
    // The `map` combinator runs a parser, then applies a function to the output
    // of that parser.
    map(parse_literal, StringFragment::Literal),
    map(parse_escaped_char, StringFragment::EscapedChar),
    value(StringFragment::EscapedWS, parse_escaped_whitespace),
  ))
  .parse(input)
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
pub fn parse_char_literal<'a, E>(input: &'a str) -> IResult<&'a str, char, E>
where
  E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  complete(delimited(
    char('\''),
    alt((parse_escaped_char, anychar)),
    char('\''),
  ))
  .parse_complete(input)
}

#[test]
fn test_parse_char() {
  assert!(parse_char_literal::<()>("''").is_err());
  assert!(parse_char_literal::<()>("'\'").is_err());
  assert!(parse_char_literal::<()>("\'").is_err());
  assert!(parse_char_literal::<()>("'").is_err());
  assert_eq!(parse_char_literal::<()>("'a'").unwrap().1, 'a');
  assert!(parse_char_literal::<()>("'aa'").is_err());
  assert_eq!(parse_char_literal::<()>("'\"'").unwrap().1, '"');
  assert_eq!(parse_char_literal::<()>("'\\''").unwrap().1, '\'');
  assert_eq!(parse_char_literal::<()>("'\\t''").unwrap().1, '\t');
  assert_eq!(parse_char_literal::<()>("'\\n''").unwrap().1, '\n');
}

/// Parse a Rust-style raw string literal: `r"..."`, `r#"..."#`, `r##"..."##`, ...
///
/// The opener is `r`, then `n` (>= 0) `#` characters, then `"`. The body is
/// taken verbatim — no `\`-escape processing at all. The closer is the first
/// `"` in the body that is followed by at least `n` `#` characters: exactly
/// `n` of them are consumed as the closing delimiter and any extra `#` beyond
/// `n` are left in the remaining input (matching `rustc`'s lexer exactly —
/// see `rustc_lexer::Cursor::raw_string_unvalidated`, which caps the closing
/// hash count at `n_start_hashes`). A `"` followed by fewer than `n` `#` is
/// not a closer and the body continues past it.
///
/// On success returns the decoded `String` body (a single owned allocation —
/// cheaper than the escaped-string path since there is no per-character
/// escape resolution). Produces the same `Literal::Str` value an ordinary
/// string literal would, so downstream stages need no changes.
///
/// Fails fast (so a bare identifier `r`, `regex`, or `r#` not followed by `"`
/// falls through to the identifier parser) when the input does not begin with
/// `r"` or `r#"`.
pub fn parse_raw_string_literal<'a, E>(input: &'a str) -> IResult<&'a str, String, E>
where
  E: ParseError<&'a str>,
{
  // Must start with 'r'.
  if !input.as_bytes().first().is_some_and(|b| *b == b'r') {
    return Err(nom::Err::Error(E::from_error_kind(
      input,
      nom::error::ErrorKind::Char,
    )));
  }
  let after_r = &input[1..];

  // Count opening '#' characters (n).
  let bytes = after_r.as_bytes();
  let mut n: usize = 0;
  while n < bytes.len() && bytes[n] == b'#' {
    n += 1;
  }
  let after_hashes = &after_r[n..];

  // Opening '"' must follow the hashes.
  if !after_hashes.as_bytes().first().is_some_and(|b| *b == b'"') {
    return Err(nom::Err::Error(E::from_error_kind(
      input,
      nom::error::ErrorKind::Char,
    )));
  }
  let body_input = &after_hashes[1..];

  // Scan for the closer: the first '"' followed by at least n '#'. Consume
  // exactly n of the trailing '#' (extra ones stay in the remainder, matching
  // rustc). A '"' followed by fewer than n '#' is not a closer — keep scanning.
  // `"` (0x22) and `#` (0x23) are ASCII and never appear as UTF-8 continuation
  // bytes (those are 0x80..0xBF), so a byte-level scan is sound even though the
  // body may contain multi-byte characters.
  let body_bytes = body_input.as_bytes();
  let mut i = 0;
  while i < body_bytes.len() {
    if body_bytes[i] == b'"' {
      // Count trailing '#' after this '"', capped at n.
      let mut cnt = 0;
      let mut j = i + 1;
      while j < body_bytes.len() && body_bytes[j] == b'#' && cnt < n {
        cnt += 1;
        j += 1;
      }
      if cnt == n {
        // Closer found: body is body_input[..i], remainder starts after the
        // consumed '"' + n '#'.
        let body = &body_input[..i];
        let rest = &body_input[j..];
        return Ok((rest, body.to_string()));
      }
    }
    i += 1;
  }

  // No closer before EOF.
  Err(nom::Err::Error(E::from_error_kind(
    input,
    nom::error::ErrorKind::Tag,
  )))
}

#[test]
fn test_parse_raw_string() {
  // Build a raw-string source from a hash count and a body, so the test
  // inputs are unambiguous (no raw-string-in-raw-string escaping traps).
  let hashes = |n: usize| std::iter::repeat('#').take(n).collect::<String>();
  let raw = |n: usize, body: &str| format!("r{}\"{}\"{}", hashes(n), body, hashes(n));

  // n = 0: any '"' closes.
  let s = raw(0, "hello");
  let (rest, body) = parse_raw_string_literal::<()>(&s).unwrap();
  assert_eq!(body, "hello");
  assert_eq!(rest, "");

  // Backslashes are verbatim — no escape processing.
  let s = raw(0, r"\n\t");
  let (rest, body) = parse_raw_string_literal::<()>(&s).unwrap();
  assert_eq!(body, r"\n\t"); // backslash, n, backslash, t
  assert_eq!(rest, "");

  // n = 1: the user's example — `r#" blab""" "#`.
  let s = raw(1, " blab\"\"\" ");
  let (rest, body) = parse_raw_string_literal::<()>(&s).unwrap();
  assert_eq!(body, " blab\"\"\" "); // space, blab, three quotes, space
  assert_eq!(rest, "");

  // n = 1: a '"' followed by fewer than 1 '#' is not a closer.
  // `r#"a"b"#` -> body `a"b`, closer is the final `"#`.
  let s = raw(1, "a\"b");
  let (rest, body) = parse_raw_string_literal::<()>(&s).unwrap();
  assert_eq!(body, "a\"b");
  assert_eq!(rest, "");

  // n = 2: embeds '"#' (one hash, fewer than n) in the body.
  let s = raw(2, "a\"#b");
  let (rest, body) = parse_raw_string_literal::<()>(&s).unwrap();
  assert_eq!(body, "a\"#b");
  assert_eq!(rest, "");

  // n = 3: embeds '"##' and '"#' in the body.
  let s = raw(3, "x\"##\"y\"#z");
  let (rest, body) = parse_raw_string_literal::<()>(&s).unwrap();
  assert_eq!(body, "x\"##\"y\"#z");
  assert_eq!(rest, "");

  // Extra '#' beyond n are left in the remainder (rustc caps closing
  // hashes at n_start_hashes). Build `r##"a"###b"##` by hand: body `a` is
  // closed by the first `"` + 2 of the 3 trailing `#`, leaving `#b"##`.
  let src = String::from("r##\"a\"###b\"##");
  let (rest, body) = parse_raw_string_literal::<()>(&src).unwrap();
  assert_eq!(body, "a");
  assert_eq!(rest, "#b\"##");

  // Multi-line body: newlines are literal content.
  let s = raw(0, "line1\nline2");
  let (rest, body) = parse_raw_string_literal::<()>(&s).unwrap();
  assert_eq!(body, "line1\nline2");
  assert_eq!(rest, "");

  // Failures — must backtrack cleanly so the identifier parser handles these.
  assert!(parse_raw_string_literal::<()>("hello").is_err()); // no leading 'r'
  assert!(parse_raw_string_literal::<()>("r").is_err()); // 'r' but no '"'
  assert!(parse_raw_string_literal::<()>("r#").is_err()); // 'r#' but no '"'
  assert!(parse_raw_string_literal::<()>("rx").is_err()); // 'r' not followed by '"'/'#'
  // n=0, no closing '"' (built by hand, not via `raw` which always closes).
  assert!(parse_raw_string_literal::<()>("r\"unterminated").is_err());
  // n=1, no '"#' closer.
  assert!(parse_raw_string_literal::<()>("r#\"unterminated").is_err());
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
pub fn parse_string_literal<'a, E>(input: &'a str) -> IResult<&'a str, String, E>
where
  E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  // fold is the equivalent of iterator::fold. It runs a parser in a loop,
  // and for each output value, calls a folding function on each output value.
  let build_string = fold(
    0..,
    // Our parser function – parses a single string fragment
    parse_fragment,
    // Our init value, an empty string
    String::new,
    // Our folding function. For each fragment, append the fragment to the
    // string.
    |mut string, fragment| {
      match fragment {
        StringFragment::Literal(s) => string.push_str(s),
        StringFragment::EscapedChar(c) => string.push(c),
        StringFragment::EscapedWS => {}
      }
      string
    },
  );

  // Finally, parse the string. Note that, if `build_string` could accept a raw
  // " character, the closing delimiter " would never match. When using
  // `delimited` with a looping parser (like fold), be sure that the
  // loop won't accidentally match your closing delimiter!
  complete(delimited(char('"'), build_string, char('"'))).parse_complete(input)
}
