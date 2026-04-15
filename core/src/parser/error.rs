use std::cmp::Ordering;

use nom::{
  Input,
  error::{ContextError, ErrorKind},
};

use crate::parser::locate::LocatedSpan;

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

pub type OwnedError = ParseError<LocatedSpan<String>>;

pub fn get_error_line_column(source: &str, error: &OwnedError) -> (usize, usize) {
  let offset = error.input.info.offset;
  let line_num = error.input.info.line as usize;

  let prefix = &source[..offset.min(source.len())];
  let column = prefix.chars().rev().take_while(|&c| c != '\n').count() + 1;

  (line_num, column)
}

pub fn display_parse_error(
  source: &str,
  error: &OwnedError,
  f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
  let (line_num, column) = get_error_line_column(source, error);

  let source_lines: Vec<&str> = source.lines().collect();
  let total_lines = source_lines.len();

  writeln!(f, "error: parse error")?;

  if line_num == 0 || line_num > total_lines {
    writeln!(f, "  --> :{}:{}", line_num, column)?;
    return Ok(());
  }

  writeln!(f, "  --> :{}:{}", line_num, column)?;

  let start_line = if line_num > 1 { line_num - 1 } else { 1 };
  let end_line = if line_num < total_lines {
    line_num + 1
  } else {
    total_lines
  };

  for i in start_line..=end_line {
    if i > total_lines {
      break;
    }
    let line_content = source_lines.get(i - 1).unwrap_or(&"");
    let marker = if i == line_num { " |" } else { "  " };
    writeln!(f, "{}{}", marker, line_content)?;

    if i == line_num {
      let caret_indent = " ".repeat(column);
      writeln!(
        f,
        "{}{}^ error here",
        caret_indent,
        if i == line_num { "^" } else { "-" }
      )?;
    }
  }

  if let Some(ctx) = &error.expected {
    writeln!(f, "  = expected: {}", ctx)?;
  }

  if !error.errors.is_empty() {
    for err in &error.errors {
      match err {
        ParseErrorKind::Native(msg) => {
          writeln!(f, "  = {}", msg)?;
        }
        ParseErrorKind::Nom(kind) => {
          writeln!(f, "  = unexpected: {:?}", kind)?;
        }
      }
    }
  }

  Ok(())
}

#[derive(Clone, Debug)]
pub struct ParseFileError {
  pub source: String,
  pub error: OwnedError,
}

impl std::fmt::Display for ParseFileError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    display_parse_error(&self.source, &self.error, f)
  }
}

#[derive(Clone, Debug)]
pub struct ParseTermError {
  pub source: String,
  pub error: OwnedError,
}

impl std::fmt::Display for ParseTermError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    display_parse_error(&self.source, &self.error, f)
  }
}

#[derive(Clone, Debug)]
pub struct ReplParserError {
  pub source: String,
  pub error: OwnedError,
}
impl std::fmt::Display for ReplParserError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    display_parse_error(&self.source, &self.error, f)
  }
}
