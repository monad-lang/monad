use std::cmp::Ordering;

use nom::{
  Input,
  error::{ContextError, ErrorKind},
};

#[derive(PartialEq, Debug, Clone)]
pub enum ParseErrorKind {
  Native(String),
  Nom(ErrorKind),
}

impl ParseErrorKind {
  pub fn is_nom_err(&self) -> bool {
    matches!(self, Self::Nom(_))
  }
}

#[derive(PartialEq, Debug, Clone)]
pub struct ParseError<I> {
  pub input: I,
  pub expected: Option<String>,
  pub errors: Vec<ParseErrorKind>,
}

impl<I> ParseError<I> {
  pub fn new(input: I, error: ParseErrorKind) -> Self {
    ParseError {
      input,
      expected: None,
      errors: vec![error],
    }
  }
  pub fn map_input<R>(self, f: impl FnOnce(I) -> R) -> ParseError<R> {
    ParseError {
      input: f(self.input),
      expected: self.expected,
      errors: self.errors,
    }
  }
}

impl<I> nom::error::ParseError<I> for ParseError<I>
where
  I: Input,
  I: Clone,
{
  fn from_error_kind(input: I, kind: ErrorKind) -> Self {
    ParseError::new(input, ParseErrorKind::Nom(kind))
  }

  fn append(input: I, kind: ErrorKind, mut other: Self) -> Self {
    match input.input_len().cmp(&other.input.input_len()) {
      Ordering::Less => ParseError::new(input, ParseErrorKind::Nom(kind)),
      Ordering::Equal => {
        other.errors.push(ParseErrorKind::Nom(kind));
        other
      }
      Ordering::Greater => other,
    }
  }

  fn or(self, mut other: Self) -> Self {
    match self.input.input_len().cmp(&other.input.input_len()) {
      Ordering::Less => self,
      Ordering::Equal => {
        for x in self.errors {
          other.errors.push(x);
        }
        other
      }
      Ordering::Greater => other,
    }
  }
}

impl<I> ContextError<I> for ParseError<I>
where
  I: Input,
  I: Clone,
{
  fn add_context(input: I, ctx: &'static str, other: Self) -> Self {
    match input.input_len().cmp(&other.input.input_len()) {
      Ordering::Less => ParseError {
        input,
        expected: Some(ctx.into()),
        errors: vec![],
      },
      Ordering::Equal => match other.expected {
        None => ParseError {
          input,
          expected: Some(ctx.into()),
          errors: other.errors,
        },
        _ => other,
      },
      Ordering::Greater => other,
    }
  }
}

impl<I1, I2: From<I1>> From<nom::error::Error<I1>> for ParseError<I2> {
  fn from(e: nom::error::Error<I1>) -> Self {
    ParseError::new(e.input.into(), ParseErrorKind::Nom(e.code))
  }
}
