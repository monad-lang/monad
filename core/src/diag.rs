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

  for i in start_line..=end_line {
    if i > total_lines {
      break;
    }
    let line_content = source_lines.get(i - 1).unwrap_or(&"");

    if i == line_num {
      writeln!(f, "{}{:>3} | {}{}", c.bold(), i, line_content, c.reset())?;
      if column > 0 {
        let indent = " ".repeat(column.saturating_sub(1));
        writeln!(
          f,
          "    {}{}{}^---{}",
          indent,
          c.error(),
          c.bold(),
          c.reset()
        )?;
      }
    } else {
      writeln!(f, "   {:>3} | {}", i, line_content)?;
    }
  }

  Ok(())
}
