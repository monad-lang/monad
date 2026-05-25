use std::cmp::Ordering;

use nom::{
  Input,
  error::{ContextError, ErrorKind},
};

use crate::diag::{self, Diagnostic, Severity, SubDiagnostic};
use crate::parser::locate::LocatedSpan;
use crate::term::{Location, SourceRange};

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
  pub kind: ParseErrorKind,
}

impl<I> ParseError<I> {
  pub fn new(input: I, error: ParseErrorKind) -> Self {
    ParseError {
      input,
      expected: None,
      kind: error,
    }
  }
  pub fn map_input<R>(self, f: impl FnOnce(I) -> R) -> ParseError<R> {
    ParseError {
      input: f(self.input),
      expected: self.expected,
      kind: self.kind,
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

  fn append(input: I, kind: ErrorKind, other: Self) -> Self {
    match input.input_len().cmp(&other.input.input_len()) {
      Ordering::Less => ParseError::new(input, ParseErrorKind::Nom(kind)),
      Ordering::Equal => {
        // other.kind.push(ParseErrorKind::Nom(kind));
        other
      }
      Ordering::Greater => other,
    }
  }

  fn or(self, other: Self) -> Self {
    match self.input.input_len().cmp(&other.input.input_len()) {
      Ordering::Less => self,
      Ordering::Equal => other,
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
        kind: other.kind,
      },
      Ordering::Equal => match other.expected {
        None => ParseError {
          input,
          expected: Some(ctx.into()),
          kind: other.kind,
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

fn describe_nom_error(kind: &ErrorKind) -> &'static str {
  match kind {
    ErrorKind::Tag => "unexpected token",
    ErrorKind::Char => "unexpected character",
    ErrorKind::Alpha => "unexpected letter",
    ErrorKind::Digit => "unexpected digit",
    ErrorKind::Eof => "unexpected end of file",
    _ => "syntax error",
  }
}

pub fn parse_error_to_diagnostic(
  source: &str,
  error: &OwnedError,
  path: Option<&std::path::PathBuf>,
) -> Diagnostic {
  let (line_num, column) = get_error_line_column(source, error);

  let mut sub_diagnostics: Vec<SubDiagnostic> = Vec::new();
  if let Some(ctx) = &error.expected {
    sub_diagnostics.push(SubDiagnostic {
      severity: Severity::Note,
      message: format!("expected: {ctx}"),
    });
  }
  let msg = match &error.kind {
    ParseErrorKind::Native(msg) => msg.clone(),
    ParseErrorKind::Nom(kind) => describe_nom_error(kind).to_string(),
  };
  sub_diagnostics.push(SubDiagnostic {
    severity: Severity::Note,
    message: msg,
  });

  let location = if line_num > 0 {
    Some(SourceRange::new(
      Location {
        line: line_num as u32,
        column,
      },
      Location {
        line: line_num as u32,
        column,
      },
    ))
  } else {
    None
  };

  Diagnostic {
    severity: Severity::Error,
    message: "parse error".to_string(),
    location,
    path: path.cloned(),
    sub_diagnostics,
    suggestions: vec![],
    context_name: None,
  }
}

pub fn display_source_context(
  source: &str,
  path: Option<&str>,
  line_num: usize,
  column: usize,
  f: &mut impl std::fmt::Write,
) -> std::fmt::Result {
  let source_lines: Vec<&str> = source.lines().collect();
  let total_lines = source_lines.len();

  match path {
    Some(path) => writeln!(f, "  --> {}:{}:{}", path, line_num, column)?,
    None => writeln!(f, "  --> :{}:{}", line_num, column)?,
  }

  if line_num == 0 || line_num > total_lines {
    return Ok(());
  }

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

    if i == line_num && column > 0 {
      let indent = " ".repeat(column.saturating_sub(1));
      writeln!(f, "{}^---", indent)?;
    }
  }

  Ok(())
}

pub fn display_parse_error(
  source: &str,
  error: &OwnedError,
  f: &mut impl std::fmt::Write,
) -> std::fmt::Result {
  let diag = parse_error_to_diagnostic(source, error, None);
  write!(f, "{}", diag::render_diagnostic(&diag, Some(source), false))
}

#[derive(Clone, Debug)]
pub struct ParseFileError {
  pub source: String,
  pub error: OwnedError,
  pub path: Option<std::path::PathBuf>,
}

impl std::fmt::Display for ParseFileError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let diag = parse_error_to_diagnostic(&self.source, &self.error, self.path.as_ref());
    write!(
      f,
      "{}",
      diag::render_diagnostic(&diag, Some(&self.source), false)
    )
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
