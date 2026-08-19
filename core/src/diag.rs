use std::fmt::Write;
use std::path::PathBuf;

use crate::term::{ModulePath, SourceRange};

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
  Error,
  Warning,
  Note,
  Help,
}

impl Severity {
  fn label(&self) -> &'static str {
    match self {
      Severity::Error => "error",
      Severity::Warning => "warning",
      Severity::Note => "note",
      Severity::Help => "help",
    }
  }
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct SubDiagnostic {
  pub severity: Severity,
  pub message: String,
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct Suggestion {
  pub message: String,
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct Diagnostic {
  pub severity: Severity,
  pub message: String,
  pub location: Option<SourceRange>,
  pub path: Option<PathBuf>,
  pub module_path: Option<ModulePath>,
  pub sub_diagnostics: Vec<SubDiagnostic>,
  pub suggestions: Vec<Suggestion>,
  pub context_name: Option<String>,
}

impl Default for Diagnostic {
  fn default() -> Self {
    Diagnostic {
      severity: Severity::Error,
      message: String::new(),
      location: None,
      path: None,
      module_path: None,
      sub_diagnostics: Vec::new(),
      suggestions: Vec::new(),
      context_name: None,
    }
  }
}

struct Colorizer {
  use_colors: bool,
}

impl Colorizer {
  fn error(&self) -> &str {
    if self.use_colors { "\x1b[1;31m" } else { "" }
  }
  fn warning(&self) -> &str {
    if self.use_colors { "\x1b[1;33m" } else { "" }
  }
  fn note(&self) -> &str {
    if self.use_colors { "\x1b[1;36m" } else { "" }
  }
  fn help(&self) -> &str {
    if self.use_colors { "\x1b[1;32m" } else { "" }
  }
  fn reset(&self) -> &str {
    if self.use_colors { "\x1b[0m" } else { "" }
  }
  fn bold(&self) -> &str {
    if self.use_colors { "\x1b[1m" } else { "" }
  }
}

pub fn render_diagnostic(diag: &Diagnostic, source: Option<&str>, use_colors: bool) -> String {
  let mut output = String::new();
  let _ = render_impl(diag, source, use_colors, &mut output);
  output
}

pub fn render_diagnostics(diags: &[Diagnostic], source: Option<&str>, use_colors: bool) -> String {
  let mut output = String::new();
  for (i, diag) in diags.iter().enumerate() {
    if i > 0 {
      let _ = writeln!(output);
    }
    let _ = render_impl(diag, source, use_colors, &mut output);
  }
  output
}

fn render_impl(
  diag: &Diagnostic,
  source: Option<&str>,
  use_colors: bool,
  f: &mut impl std::fmt::Write,
) -> std::fmt::Result {
  let c = Colorizer { use_colors };

  if let Some(name) = &diag.context_name {
    writeln!(f, "{}In {}:{}", c.bold(), name, c.reset())?;
  }

  let severity_color = match diag.severity {
    Severity::Error => c.error(),
    Severity::Warning => c.warning(),
    Severity::Note => c.note(),
    Severity::Help => c.help(),
  };
  write!(
    f,
    "{}{}{}: ",
    severity_color,
    c.bold(),
    diag.severity.label()
  )?;
  write!(f, "{}{}", diag.message, c.reset())?;

  if let Some(loc) = &diag.location {
    if loc.start.line > 0 {
      write!(f, " at {}:{}", loc.start.line, loc.start.column)?;
    }
  }
  writeln!(f)?;

  if let Some(loc) = &diag.location {
    let line_num = loc.start.line as usize;
    let column = loc.start.column;

    if let Some(path) = &diag.path {
      writeln!(f, "  --> {}:{}:{}", path.display(), line_num, column)?;
    } else {
      writeln!(f, "  --> :{}:{}", line_num, column)?;
    }

    if let Some(source) = source {
      write_source_context(source, line_num, column, use_colors, f)?;
    }
  }

  for sub in &diag.sub_diagnostics {
    let color = match sub.severity {
      Severity::Error => c.error(),
      Severity::Warning => c.warning(),
      Severity::Note => c.note(),
      Severity::Help => c.help(),
    };
    writeln!(
      f,
      "  = {}: {}{}{}",
      sub.severity.label(),
      color,
      sub.message,
      c.reset()
    )?;
  }

  for suggestion in &diag.suggestions {
    writeln!(
      f,
      "{}help:{} {}{}",
      c.help(),
      c.reset(),
      c.bold(),
      suggestion.message,
    )?;
    write!(f, "{}", c.reset())?;
  }

  Ok(())
}

fn write_source_context(
  source: &str,
  line_num: usize,
  column: usize,
  use_colors: bool,
  f: &mut impl std::fmt::Write,
) -> std::fmt::Result {
  let c = Colorizer { use_colors };
  let source_lines: Vec<&str> = source.lines().collect();
  let total_lines = source_lines.len();

  if line_num == 0 || line_num > total_lines {
    return Ok(());
  }

  let start_line = if line_num > 1 { line_num - 1 } else { 1 };
  let end_line = if line_num < total_lines {
    line_num + 1
  } else {
    total_lines
  };

  // Gutter width is the width of the widest line number actually shown,
  // with a minimum of 3 (matches rustc-style alignment and keeps small
  // files looking the same as before). Every displayed line -- the error
  // line and its context neighbors alike -- uses this same width, so the
  // `|` separators all line up in one column. The caret line then indents
  // by `width + 3` spaces (the number field plus the literal `" | "`) to
  // land under the first character of the source line's content.
  let width = end_line.to_string().len().max(3);

  for i in start_line..=end_line {
    if i > total_lines {
      break;
    }
    let line_content = source_lines.get(i - 1).unwrap_or(&"");

    if i == line_num {
      writeln!(
        f,
        "{}{:>width$} | {}{}",
        c.bold(),
        i,
        line_content,
        c.reset()
      )?;
      if column > 0 {
        let indent = " ".repeat(column.saturating_sub(1));
        writeln!(
          f,
          "{}{}{}{}^---{}",
          " ".repeat(width + 3),
          indent,
          c.error(),
          c.bold(),
          c.reset()
        )?;
      }
    } else {
      writeln!(f, "{:>width$} | {}", i, line_content)?;
    }
  }

  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn render(source: &str, line_num: usize, column: usize) -> String {
    let mut out = String::new();
    write_source_context(source, line_num, column, false, &mut out).unwrap();
    out
  }

  #[test]
  fn gutter_aligns_error_line_with_context_lines() {
    let out = render("def add (a : I64 (b : I64) : I64 :=\n    a + b\n", 1, 28);
    let lines: Vec<&str> = out.lines().collect();
    // Error line and its "N | " gutter.
    assert_eq!(lines[0], "  1 | def add (a : I64 (b : I64) : I64 :=");
    // Caret aligned under column 28 of the content above (6-char prefix:
    // 3-wide number field + " | ", then 27 spaces before the caret).
    assert_eq!(lines[1], format!("{}{}^---", " ".repeat(6), " ".repeat(27)));
    // Context line below uses the exact same gutter width as the error
    // line -- no stray extra indent.
    assert_eq!(lines[2], "  2 |     a + b");
  }

  #[test]
  fn gutter_width_grows_for_four_digit_line_numbers() {
    let mut source = String::new();
    for i in 1..=1001 {
      source.push_str(&format!("line{}\n", i));
    }
    let out = render(&source, 1000, 1);
    let lines: Vec<&str> = out.lines().collect();
    // end_line is 1001 (4 digits), so every gutter -- including the
    // 3-digit-wide "999" context line -- pads out to width 4.
    assert_eq!(lines[0], " 999 | line999");
    assert_eq!(lines[1], "1000 | line1000");
    assert_eq!(lines[3], "1001 | line1001");
  }
}
