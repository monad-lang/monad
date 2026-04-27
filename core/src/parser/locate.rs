use core::slice;
use nom::{
  AsBytes, Compare, CompareResult, FindSubstring, FindToken, IResult, Input, Offset, ParseTo,
  Parser, error::ParseError,
};
use std::{
  borrow::Borrow,
  fmt::{self, Display, Formatter},
  hash::{Hash, Hasher},
  str::FromStr,
};

/// Parser info
#[derive(Debug, Clone, PartialEq)]
pub struct Info<X> {
  /// The offset represents the position of the fragment relatively to
  /// the input of the parser. It starts at offset 0.
  pub offset: usize,

  /// Offset relative to the start of a line
  pub line_offset: usize,

  /// The line number of the fragment relatively to the input of the
  /// parser. It starts at line 1.
  pub line: u32,
  /// Extra information that can be embedded by the user.
  /// Example: the parsed file name
  pub extra: X,
}

impl<X> std::ops::Deref for Info<X> {
  type Target = X;

  fn deref(&self) -> &Self::Target {
    &self.extra
  }
}

impl<X: Default> Default for Info<X> {
  fn default() -> Self {
    Self {
      offset: Default::default(),
      line: Default::default(),
      extra: Default::default(),
      line_offset: Default::default(),
    }
  }
}

impl<X> Info<X> {
  /// The offset represents the position of the fragment relatively to
  /// the input of the parser. It starts at offset 0.
  pub fn location_offset(&self) -> usize {
    self.offset
  }

  /// The line number of the fragment relatively to the input of the
  /// parser. It starts at line 1.
  pub fn location_line(&self) -> u32 {
    self.line
  }
  pub fn map_extra<U, F: FnOnce(X) -> U>(self, f: F) -> Info<U> {
    Info {
      offset: self.offset,
      line_offset: self.line_offset,
      line: self.line,
      extra: f(self.extra),
    }
  }
}
/// A LocatedSpan is a set of meta information about the location of a token, including extra
/// information.
///
/// The `LocatedSpan` structure can be used as an input of the nom parsers.
/// It implements all the necessary traits for `LocatedSpan<&str,X>` and `LocatedSpan<&[u8],X>`
#[derive(Debug, Clone)]
pub struct LocatedSpan<T, X = ()> {
  /// The fragment that is spanned.
  /// The fragment represents a part of the input of the parser.
  fragment: T,
  pub info: Info<X>,
}

impl<T, X> core::ops::Deref for LocatedSpan<T, X> {
  type Target = T;
  fn deref(&self) -> &Self::Target {
    &self.fragment
  }
}
impl<X> From<LocatedSpan<&str, X>> for LocatedSpan<String, X> {
  fn from(value: LocatedSpan<&str, X>) -> Self {
    LocatedSpan {
      info: value.info,
      fragment: value.fragment.into(),
    }
  }
}
impl<X> Borrow<str> for LocatedSpan<&str, X> {
  fn borrow(&self) -> &str {
    self.as_ref()
  }
}

impl<T, U, X> core::convert::AsRef<U> for LocatedSpan<&T, X>
where
  T: ?Sized + core::convert::AsRef<U>,
  U: ?Sized,
{
  fn as_ref(&self) -> &U {
    self.fragment.as_ref()
  }
}

impl<T> LocatedSpan<T, ()> {
  /// Create a span for a particular input with default `offset` and
  /// `line` values and empty extra data.
  /// You can compute the column through the `get_column` or `get_utf8_column`
  /// methods.
  ///
  /// `offset` starts at 0, `line` starts at 1, and `column` starts at 1.
  ///
  /// Do not use this constructor in parser functions; `nom` and
  /// `nom_locate` assume span offsets are relative to the beginning of the
  /// same input. In these cases, you probably want to use the
  /// `nom::traits::Slice` trait instead.
  pub fn new(program: T) -> LocatedSpan<T, ()> {
    LocatedSpan {
      info: Info {
        offset: 0,
        line_offset: 1,
        line: 1,
        extra: (),
      },
      fragment: program,
    }
  }
}

impl<T, X> LocatedSpan<T, X> {
  pub fn extra(&self) -> &X {
    &self.info.extra
  }

  pub fn get_line(&self) -> u32 {
    self.info.line
  }

  pub fn location_line(&self) -> u32 {
    self.info.line
  }

  pub fn location_offset(&self) -> usize {
    self.info.offset
  }

  /// Create a span for a particular input with default `offset` and
  /// `line` values. You can compute the column through the `get_column` or `get_utf8_column`
  /// methods.
  ///
  /// `offset` starts at 0, `line` starts at 1, and `column` starts at 1.
  ///
  /// Do not use this constructor in parser functions; `nom` and
  /// `nom_locate` assume span offsets are relative to the beginning of the
  /// same input. In these cases, you probably want to use the
  /// `nom::traits::Slice` trait instead.
  ///
  pub fn new_extra(program: T, extra: X) -> LocatedSpan<T, X> {
    LocatedSpan {
      info: Info {
        offset: 0,
        line_offset: 1,
        line: 1,
        extra,
      },
      fragment: program,
    }
  }

  /// Similar to `new_extra`, but allows overriding offset and line.
  /// This is unsafe, because giving an offset too large may result in
  /// undefined behavior, as some methods move back along the fragment
  /// assuming any negative index within the offset is valid.
  pub unsafe fn new_from_raw_offset(
    offset: usize,
    line_offset: usize,
    line: u32,
    fragment: T,
    extra: X,
  ) -> LocatedSpan<T, X> {
    LocatedSpan {
      info: Info {
        offset,
        line_offset,
        line,
        extra,
      },
      fragment,
    }
  }

  /// The fragment that is spanned.
  /// The fragment represents a part of the input of the parser.
  pub fn fragment(&self) -> &T {
    &self.fragment
  }

  /// Transform the extra inside into another type
  ///
  /// # Example of use
  /// ```
  /// # use monad_core::parser::locate::LocatedSpan;
  /// # extern crate nom;
  ///
  /// use nom::{
  ///   IResult, AsChar, Parser,
  ///   combinator::{recognize, map_res},
  ///   sequence::terminated,
  ///   character::complete::{char, one_of},
  ///   bytes::complete::{tag, take_while1},
  /// };
  ///
  /// fn decimal(input: LocatedSpan<&str>) -> IResult<LocatedSpan<&str>, LocatedSpan<&str>> {
  ///   recognize(
  ///        take_while1(|c: char| c.is_dec_digit() || c == '_')
  ///   ).parse(input)
  /// }
  ///
  /// fn main() {
  ///     use nom::Parser;
  /// let span = LocatedSpan::new("$10");
  ///     // matches the $ and then matches the decimal number afterwards,
  ///     // converting it into a `u8` and putting that value in the span
  ///     let (_, (_, n)) = (
  ///         tag("$"),
  ///         map_res(
  ///             decimal,
  ///             |x| x.fragment().parse::<u8>().map(|n| x.map_extra(|_| n))
  ///         )
  ///     ).parse(span).unwrap();
  ///     assert_eq!(n.info.extra, 10);
  /// }
  /// ```
  pub fn map_extra<U, F: FnOnce(X) -> U>(self, f: F) -> LocatedSpan<T, U> {
    LocatedSpan {
      info: self.info.map_extra(f),
      fragment: self.fragment,
    }
  }

  /// Takes ownership of the fragment without (re)borrowing it.
  ///
  /// # Example of use
  /// ```
  /// use nom::{
  ///     IResult,
  ///     bytes::complete::{take_till, tag},
  ///     combinator::rest,
  /// };
  /// use monad_core::parser::locate::LocatedSpan;
  ///
  /// fn parse_pair<'a>(input: LocatedSpan<&'a str>) -> IResult<LocatedSpan<&'a str>, (&'a str, &'a str)> {
  ///     let (input, key) = take_till(|c| c == '=')(input)?;
  ///     let (input, _) = tag("=")(input)?;
  ///     let (input, value) = rest(input)?;
  ///
  ///     Ok((input, (key.into_fragment(), value.into_fragment())))
  /// }
  ///
  /// fn main() {
  ///     let span = LocatedSpan::new("key=value");
  ///     let (_, pair) = parse_pair(span).unwrap();
  ///     assert_eq!(pair, ("key", "value"));
  /// }
  /// ```
  pub fn into_fragment(self) -> T {
    self.fragment
  }

  /// Takes ownership of the fragment and extra data without (re)borrowing them.
  pub fn into_fragment_and_extra(self) -> (T, X) {
    (self.fragment, self.info.extra)
  }
}

impl<A: Compare<B>, B: Into<LocatedSpan<B>>, X> Compare<B> for LocatedSpan<A, X> {
  #[inline(always)]
  fn compare(&self, t: B) -> CompareResult {
    self.fragment.compare(t.into().fragment)
  }

  #[inline(always)]
  fn compare_no_case(&self, t: B) -> CompareResult {
    self.fragment.compare_no_case(t.into().fragment)
  }
}

impl<Fragment: FindToken<Token>, Token, X> FindToken<Token> for LocatedSpan<Fragment, X> {
  fn find_token(&self, token: Token) -> bool {
    self.fragment.find_token(token)
  }
}

impl<T, U, X> FindSubstring<U> for LocatedSpan<T, X>
where
  T: FindSubstring<U>,
{
  #[inline]
  fn find_substring(&self, substr: U) -> Option<usize> {
    self.fragment.find_substring(substr)
  }
}

impl<T: Hash, X> Hash for LocatedSpan<T, X> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.info.offset.hash(state);
    self.info.line.hash(state);
    self.fragment.hash(state);
  }
}

impl<T: AsBytes, X: Default> From<T> for LocatedSpan<T, X> {
  fn from(i: T) -> Self {
    Self::new_extra(i, X::default())
  }
}

impl<T: AsBytes + PartialEq, X: PartialEq> PartialEq for LocatedSpan<T, X> {
  fn eq(&self, other: &Self) -> bool {
    self.info == other.info && self.fragment == other.fragment
  }
}

impl<T: AsBytes + Eq, X: PartialEq> Eq for LocatedSpan<T, X> {}

impl<T: AsBytes, X> AsBytes for LocatedSpan<T, X> {
  fn as_bytes(&self) -> &[u8] {
    self.fragment.as_bytes()
  }
}

/// Rough upper bound: number of `\n` + 1 (the first line).  This is cheap
/// and only used to pre‑allocate the vector capacity.
fn estimate_lines(bytes: &[u8]) -> usize {
  bytes.iter().filter(|&&b| b == b'\n').count() + 1
}

fn line_starts<T: AsBytes>(source: &T) -> Vec<usize> {
  let bytes = source.as_bytes();

  let mut starts = Vec::with_capacity(estimate_lines(bytes));

  for (i, &b) in bytes.iter().enumerate() {
    if b == b'\n' {
      // i is the index of the newline; the next byte begins the next line.
      // Guard against a trailing newline that would otherwise push an out‑of‑range offset.
      if i < bytes.len() {
        starts.push(i + 1);
      }
    }
  }

  starts
}

impl<T: AsBytes, X> LocatedSpan<T, X> {
  // Attempt to get the "original" data slice back, by extending
  // self.fragment backwards by self.offset.
  // Note that any bytes truncated from after self.fragment will not
  // be recovered.
  fn get_unoffsetted_slice(&self) -> &[u8] {
    let self_bytes = self.fragment.as_bytes();
    let self_ptr = self_bytes.as_ptr();
    unsafe {
      assert!(
        self.info.offset <= isize::max_value() as usize,
        "offset is too big"
      );
      let orig_input_ptr = self_ptr.offset(-(self.info.offset as isize));
      slice::from_raw_parts(orig_input_ptr, self.info.offset + self_bytes.len())
    }
  }

  fn get_columns_and_bytes_before(&self) -> (usize, &[u8]) {
    let before_self = &self.get_unoffsetted_slice()[..self.info.offset];

    let column = match line_starts(&before_self).last() {
      None => self.info.offset + 1,
      Some(pos) => self.info.offset - pos,
    };

    (column, &before_self[self.info.offset - (column - 1)..])
  }

  pub fn get_line_beginning(&self) -> &[u8] {
    let column0 = self.get_column() - 1;
    let the_line = &self.get_unoffsetted_slice()[self.info.offset - column0..];
    let rest = &the_line[column0..];
    match line_starts(&rest).last() {
      None => the_line,
      Some(pos) => &the_line[..column0 + pos],
    }
  }

  /// Return the column index, assuming 1 byte = 1 column.
  ///
  /// Use it for ascii text, or use get_utf8_column for UTF8.
  ///
  pub fn get_column(&self) -> usize {
    self.get_columns_and_bytes_before().0
  }

  pub fn get_utf8_column(&self) -> usize {
    let before_self = self.get_columns_and_bytes_before().1;
    let s = std::str::from_utf8(before_self).unwrap_or("");
    s.chars().count() + 1
  }

  // Helper for `Input::take()` and `Input::take_from()` implementations.
  fn slice_by(&self, next_fragment: T) -> Self
  where
    T: AsBytes + Input + Offset,
    X: Clone,
  {
    let consumed_len = self.fragment.offset(&next_fragment);
    if consumed_len == 0 {
      return Self {
        info: Info {
          line: self.info.line,
          offset: self.info.offset,
          line_offset: self.info.line_offset,
          extra: self.info.extra.clone(),
        },
        fragment: next_fragment,
      };
    }

    let consumed = self.fragment.take(consumed_len);

    let next_offset = self.info.offset + consumed_len;

    let line_starts = line_starts(&consumed);
    let line_offset = line_starts
      .last()
      .map(|line_start| consumed_len - line_start + 1)
      .unwrap_or(self.info.line_offset + consumed_len);
    let number_of_lines = line_starts.len() as u32;
    let next_line = self.info.line + number_of_lines;

    Self {
      info: Info {
        line: next_line,
        line_offset,
        offset: next_offset,
        extra: self.info.extra.clone(),
      },
      fragment: next_fragment,
    }
  }
}

impl<T, X> Input for LocatedSpan<T, X>
where
  T: AsBytes + Input + Offset,
  X: Clone,
{
  type Item = <T as Input>::Item;
  type Iter = <T as Input>::Iter;
  type IterIndices = <T as Input>::IterIndices;

  #[inline]
  fn input_len(&self) -> usize {
    self.fragment.input_len()
  }

  #[inline]
  fn take(&self, index: usize) -> Self {
    self.slice_by(self.fragment.take(index))
  }

  #[inline]
  fn take_from(&self, index: usize) -> Self {
    self.slice_by(self.fragment.take_from(index))
  }

  #[inline]
  fn take_split(&self, index: usize) -> (Self, Self) {
    (self.take_from(index), self.take(index))
  }

  #[inline]
  fn position<P>(&self, predicate: P) -> Option<usize>
  where
    P: Fn(Self::Item) -> bool,
  {
    self.fragment.position(predicate)
  }

  #[inline]
  fn iter_elements(&self) -> Self::Iter {
    self.fragment.iter_elements()
  }

  #[inline]
  fn iter_indices(&self) -> Self::IterIndices {
    self.fragment.iter_indices()
  }

  #[inline]
  fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
    self.fragment.slice_index(count)
  }
}

impl<R: FromStr, T, X> ParseTo<R> for LocatedSpan<T, X>
where
  T: ParseTo<R>,
{
  #[inline]
  fn parse_to(&self) -> Option<R> {
    self.fragment.parse_to()
  }
}

impl<T, X> Offset for LocatedSpan<T, X> {
  fn offset(&self, second: &Self) -> usize {
    let fst = self.info.offset;
    let snd = second.info.offset;

    snd - fst
  }
}

impl<T: ToString, X> Display for LocatedSpan<T, X> {
  fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
    fmt.write_str(&self.fragment.to_string())
  }
}

/// Capture the position of the current fragment
#[macro_export]
macro_rules! position {
  ($input:expr,) => {
    tag!($input, "")
  };
}

/// Capture the position of the current fragment
pub fn info<T, E, X: Clone>(s: LocatedSpan<T, X>) -> IResult<LocatedSpan<T, X>, Info<X>, E>
where
  E: ParseError<LocatedSpan<T, X>>,
  T: Input + Offset + AsBytes,
{
  nom::bytes::complete::take(0usize)
    .map(|s: LocatedSpan<T, X>| s.info)
    .parse(s)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn works_with_str() {
    let txt = "first\nsecond\nthird";
    let starts = line_starts(&txt);
    assert_eq!(starts, vec![6, 13]); // "first".len()+1, etc.
  }

  #[test]
  fn works_with_vec_u8() {
    let data = b"a\nbb\nccc";
    let starts = line_starts(&data);
    assert_eq!(starts, vec![2, 5]);
  }

  #[test]
  fn trailing_newline_handled() {
    let txt = "line1\nline2\n";
    let starts = line_starts(&txt);
    // The trailing newline does NOT produce an extra empty line entry.
    assert_eq!(starts, vec![6, 12]);
  }
}
