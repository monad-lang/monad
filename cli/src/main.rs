mod lsp;

use std::path::{Path, PathBuf};

use clap::{Parser, Subcommand};
use monad_core::{
  SymbolInfo, SymbolKind, check_files,
  diag::{Diagnostic, Severity, render_diagnostics},
  eval::EvalOptions,
  organize_imports_for_files, run, run_tests, symbols_for_files,
  term::mote::{Manifest, Resolver},
};

#[cfg(feature = "repl")]
use monad_core::repl;

#[derive(Subcommand, Debug)]
enum Commands {
  Repl {
    #[arg(short, long, default_value_t = false)]
    debug: bool,
    #[arg(long, default_value_t = false)]
    benchmark: bool,
    #[arg(long, default_value_t = false, overrides_with = "no_color")]
    color: bool,
    #[arg(long = "no-color", default_value_t = false)]
    no_color: bool,
    #[arg(long)]
    max_depth: Option<u64>,
  },

  Run {
    #[arg(value_name = "FILE")]
    input: PathBuf,
    #[arg(short, long, default_value_t = false)]
    debug: bool,
    #[arg(long, default_value_t = false)]
    benchmark: bool,
    #[arg(value_name = "ARGS", trailing_var_arg = true)]
    args: Vec<String>,
    #[arg(long, default_value_t = false, overrides_with = "no_color")]
    color: bool,
    #[arg(long = "no-color", default_value_t = false)]
    no_color: bool,
    #[arg(long)]
    max_depth: Option<u64>,
    #[arg(short = 'p', long = "mote-path", value_name = "DIR")]
    mote_path: Vec<PathBuf>,
    #[arg(long = "manifest-path", value_name = "PATH")]
    manifest_path: Option<PathBuf>,
  },

  Test {
    #[arg(value_name = "PATHS", num_args = 1..)]
    inputs: Vec<PathBuf>,
    #[arg(short, long, default_value_t = false)]
    debug: bool,
    #[arg(long, default_value_t = false)]
    benchmark: bool,
    #[arg(long, default_value_t = false, overrides_with = "no_color")]
    color: bool,
    #[arg(long = "no-color", default_value_t = false)]
    no_color: bool,
    #[arg(long)]
    max_depth: Option<u64>,
    #[arg(long)]
    timeout: Option<f64>,
    #[arg(short = 'j', long)]
    jobs: Option<usize>,
    #[arg(long, default_value_t = false)]
    sequential: bool,
    #[arg(short = 'p', long = "mote-path", value_name = "DIR")]
    mote_path: Vec<PathBuf>,
    #[arg(long = "manifest-path", value_name = "PATH")]
    manifest_path: Option<PathBuf>,
  },

  Check {
    /// Files or directories to check. Directories are scanned recursively
    /// for `.mo` files. Defaults to the current directory if omitted.
    #[arg(value_name = "PATHS")]
    inputs: Vec<PathBuf>,
    /// Emit machine-readable JSON (for editor/agent integrations) instead
    /// of the default human-readable text report.
    #[arg(long, default_value_t = false)]
    json: bool,
    #[arg(long, default_value_t = false, overrides_with = "no_color")]
    color: bool,
    #[arg(long = "no-color", default_value_t = false)]
    no_color: bool,
    #[arg(short = 'p', long = "mote-path", value_name = "DIR")]
    mote_path: Vec<PathBuf>,
    #[arg(long = "manifest-path", value_name = "PATH")]
    manifest_path: Option<PathBuf>,
  },

  Symbols {
    /// Files or directories to index. Directories are scanned recursively
    /// for `.mo` files. Defaults to the current directory if omitted.
    #[arg(value_name = "PATHS")]
    inputs: Vec<PathBuf>,
    /// Emit machine-readable JSON instead of a plain text listing.
    #[arg(long, default_value_t = false)]
    json: bool,
    #[arg(short = 'p', long = "mote-path", value_name = "DIR")]
    mote_path: Vec<PathBuf>,
    #[arg(long = "manifest-path", value_name = "PATH")]
    manifest_path: Option<PathBuf>,
  },

  /// Type signature (and, for a def, its full type) of the identifier at
  /// a position. LINE/COL are 1-indexed, matching the positions already
  /// shown in `check`'s own diagnostics (e.g. "at 3:1").
  Hover {
    #[arg(value_name = "FILE")]
    file: PathBuf,
    #[arg(value_name = "LINE")]
    line: u32,
    #[arg(value_name = "COL")]
    col: usize,
    #[arg(long, default_value_t = false)]
    json: bool,
    #[arg(short = 'p', long = "mote-path", value_name = "DIR")]
    mote_path: Vec<PathBuf>,
    #[arg(long = "manifest-path", value_name = "PATH")]
    manifest_path: Option<PathBuf>,
  },

  /// Where the identifier at a position is defined. LINE/COL are
  /// 1-indexed, same convention as `hover`/`check`.
  Definition {
    #[arg(value_name = "FILE")]
    file: PathBuf,
    #[arg(value_name = "LINE")]
    line: u32,
    #[arg(value_name = "COL")]
    col: usize,
    #[arg(long, default_value_t = false)]
    json: bool,
    #[arg(short = 'p', long = "mote-path", value_name = "DIR")]
    mote_path: Vec<PathBuf>,
    #[arg(long = "manifest-path", value_name = "PATH")]
    manifest_path: Option<PathBuf>,
  },

  /// Rewrite bare `use Module`/`open Module` declarations to explicit
  /// `use/open Module {name1, name2}` (minimal name list — only what the
  /// file actually references) and `@[...]` attributes to `#[...]`.
  /// Prints a diff by default; pass `--write` to apply it.
  OrganizeImports {
    /// Files or directories to convert. Directories are scanned
    /// recursively for `.mo` files. Defaults to the current directory if
    /// omitted.
    #[arg(value_name = "PATHS")]
    inputs: Vec<PathBuf>,
    /// Apply the rewrite to disk. Without this flag, only a diff is
    /// printed and nothing is written.
    #[arg(long, default_value_t = false)]
    write: bool,
    #[arg(short = 'p', long = "mote-path", value_name = "DIR")]
    mote_path: Vec<PathBuf>,
    #[arg(long = "manifest-path", value_name = "PATH")]
    manifest_path: Option<PathBuf>,
  },

  /// Start the LSP server (stdio JSON-RPC). Diagnostics and navigation
  /// (hover/definition/documentSymbol) only — no completions, rename,
  /// semantic tokens, or code actions yet (see `lsp` module docs).
  Lsp {
    #[arg(short = 'p', long = "mote-path", value_name = "DIR")]
    mote_path: Vec<PathBuf>,
    #[arg(long = "manifest-path", value_name = "PATH")]
    manifest_path: Option<PathBuf>,
  },
}

#[derive(Debug, Parser)]
#[command(
  name = "monad",
  version,
  about = "Monad language interpreter and compiler"
)]
struct Cli {
  #[command(subcommand)]
  command: Commands,
}

fn augment_mote_paths(mote_path: &mut Vec<PathBuf>, manifest_path: Option<&PathBuf>) {
  let (manifest, project_root) = if let Some(mp) = manifest_path {
    let root = mp.parent().map(|p| p.to_path_buf());
    (Manifest::parse(mp).ok(), root)
  } else {
    std::env::current_dir()
      .ok()
      .and_then(|cwd| Manifest::discover(&cwd))
      .map(|(path, m)| {
        let root = path.parent().map(|p| p.to_path_buf());
        (Some(m), root)
      })
      .unwrap_or((None, None))
  };

  if let (Some(manifest), Some(root)) = (manifest, project_root) {
    let src_dir = root.join("src");
    if src_dir.is_dir() && !mote_path.contains(&src_dir) {
      mote_path.push(src_dir);
    }

    match Resolver::resolve(&manifest, &root, None) {
      Ok(resolved) => {
        for mote in &resolved.motes {
          if let Some(source_path) = &mote.source_path {
            let dep_src_dir = source_path.join("src");
            if dep_src_dir.is_dir() && !mote_path.contains(&dep_src_dir) {
              mote_path.push(dep_src_dir);
            }
          }
        }
      }
      Err(e) => {
        eprintln!("warning: failed to resolve dependencies: {e}");
      }
    }
  }
}

// --- `check --json` wire format -------------------------------------------
//
// A deliberately separate, hand-written shape from `monad_core::diag`'s
// internal `Diagnostic` (1-indexed `Location`, Rust field names) — this is
// the CLI's own translation to the LSP-conventional shape (0-indexed
// `Position`, `uri`, camelCase `filesChecked`) agent/editor tooling
// expects, matching the "structured CLI tools" shape from
// `plans/library-ideas/language-server.md`. Converting here (not in
// `core`) keeps `monad-core` itself unaware of LSP conventions.

#[derive(serde::Serialize)]
pub(crate) struct JsonPosition {
  pub(crate) line: u32,
  pub(crate) character: usize,
}

#[derive(serde::Serialize)]
pub(crate) struct JsonRange {
  pub(crate) start: JsonPosition,
  pub(crate) end: JsonPosition,
}

#[derive(serde::Serialize)]
struct JsonDiagnostic {
  range: JsonRange,
  severity: String,
  message: String,
}

#[derive(serde::Serialize)]
struct JsonFileReport {
  uri: String,
  diagnostics: Vec<JsonDiagnostic>,
}

#[derive(serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct JsonSummary {
  errors: usize,
  warnings: usize,
  files_checked: usize,
}

#[derive(serde::Serialize)]
struct JsonCheckReport {
  files: Vec<JsonFileReport>,
  summary: JsonSummary,
}

/// LSP `Position` is 0-indexed; `core`'s `Location` is 1-indexed (see its
/// doc comment) — converts at this one boundary, `saturating_sub` so a
/// (should-never-happen) `0` line/column from a `SourceRange::default()`
/// placeholder can't underflow instead of panicking.
pub(crate) fn to_json_position(loc: &monad_core::term::Location) -> JsonPosition {
  JsonPosition {
    line: loc.line.saturating_sub(1),
    character: loc.column.saturating_sub(1),
  }
}

/// `SourceRange` -> `JsonRange`, falling back to `0:0-0:0` when there's no
/// location at all (an internal-error diagnostic with nothing to point
/// at) rather than making every caller handle the `None` case itself.
pub(crate) fn location_to_json_range(loc: Option<&monad_core::term::SourceRange>) -> JsonRange {
  match loc {
    Some(loc) => JsonRange {
      start: to_json_position(&loc.start),
      end: to_json_position(&loc.end),
    },
    None => JsonRange {
      start: JsonPosition {
        line: 0,
        character: 0,
      },
      end: JsonPosition {
        line: 0,
        character: 0,
      },
    },
  }
}

fn to_json_diagnostic(diag: &Diagnostic) -> JsonDiagnostic {
  let range = location_to_json_range(diag.location.as_ref());
  JsonDiagnostic {
    range,
    severity: match diag.severity {
      Severity::Error => "error",
      Severity::Warning => "warning",
      Severity::Note => "note",
      Severity::Help => "help",
    }
    .to_string(),
    message: diag.message.clone(),
  }
}

pub(crate) fn path_to_uri(path: &std::path::Path) -> String {
  let abs = std::path::absolute(path).unwrap_or_else(|_| path.to_path_buf());
  format!("file://{}", abs.display())
}

fn run_check(inputs: Vec<PathBuf>, json: bool, use_colors: bool, mote_path: Vec<PathBuf>) -> ! {
  let results = match check_files(inputs, mote_path) {
    Ok(results) => results,
    Err(e) => {
      eprintln!("error: {e}");
      std::process::exit(2);
    }
  };

  let mut error_count = 0usize;
  let mut warning_count = 0usize;
  for result in &results {
    for d in &result.diagnostics {
      match d.severity {
        Severity::Error => error_count += 1,
        Severity::Warning => warning_count += 1,
        _ => {}
      }
    }
  }

  if json {
    let report = JsonCheckReport {
      files: results
        .iter()
        .map(|r| JsonFileReport {
          uri: path_to_uri(&r.path),
          diagnostics: r.diagnostics.iter().map(to_json_diagnostic).collect(),
        })
        .collect(),
      summary: JsonSummary {
        errors: error_count,
        warnings: warning_count,
        files_checked: results.len(),
      },
    };
    match serde_json::to_string_pretty(&report) {
      Ok(s) => println!("{s}"),
      Err(e) => {
        eprintln!("error: failed to serialize report: {e}");
        std::process::exit(2);
      }
    }
  } else {
    for result in &results {
      if !result.diagnostics.is_empty() {
        print!(
          "{}",
          render_diagnostics(&result.diagnostics, None, use_colors)
        );
      }
    }
    println!(
      "{} file(s) checked, {} error(s), {} warning(s)",
      results.len(),
      error_count,
      warning_count
    );
  }

  std::process::exit(if error_count > 0 { 1 } else { 0 });
}

/// Print a minimal line-level diff between `old` and `new` — every edit
/// this tool makes is confined to a single `use`/`open`/attribute line, so
/// a full unified-diff algorithm isn't needed: walk both files' lines in
/// lockstep and report wherever they differ.
fn print_line_diff(path: &Path, old: &str, new: &str) {
  println!("--- {}", path.display());
  let old_lines: Vec<&str> = old.lines().collect();
  let new_lines: Vec<&str> = new.lines().collect();
  for (i, (o, n)) in old_lines.iter().zip(new_lines.iter()).enumerate() {
    if o != n {
      println!("  {}:", i + 1);
      println!("  - {o}");
      println!("  + {n}");
    }
  }
}

fn run_organize_imports(
  inputs: Vec<PathBuf>,
  write: bool,
  mote_path: Vec<PathBuf>,
) -> Result<(), String> {
  let results = organize_imports_for_files(inputs, mote_path)?;

  let mut changed = 0usize;
  let mut errors = 0usize;
  for result in &results {
    if let Some(e) = &result.error {
      eprintln!("error: {}: {e}", result.path.display());
      errors += 1;
      continue;
    }
    let Some(new_source) = &result.new_source else {
      continue;
    };
    changed += 1;
    let old_source = std::fs::read_to_string(&result.path).map_err(|e| format!("{e}"))?;
    print_line_diff(&result.path, &old_source, new_source);
    if write {
      std::fs::write(&result.path, new_source).map_err(|e| format!("{e}"))?;
    }
  }

  if write {
    println!("{changed} file(s) rewritten, {errors} error(s)");
  } else {
    println!("{changed} file(s) would be rewritten, {errors} error(s) (pass --write to apply)");
  }

  if errors > 0 {
    return Err(format!("{errors} file(s) failed to load"));
  }
  Ok(())
}

#[derive(serde::Serialize)]
struct JsonSymbol {
  name: String,
  kind: SymbolKind,
  range: JsonRange,
  #[serde(skip_serializing_if = "Option::is_none")]
  detail: Option<String>,
}

#[derive(serde::Serialize)]
struct JsonSymbolFile {
  uri: String,
  symbols: Vec<JsonSymbol>,
}

pub(crate) fn symbol_kind_label(kind: SymbolKind) -> &'static str {
  match kind {
    SymbolKind::Function => "function",
    SymbolKind::Struct => "struct",
    SymbolKind::Class => "class",
    SymbolKind::Enum => "enum",
    SymbolKind::Instance => "instance",
  }
}

fn run_symbols(inputs: Vec<PathBuf>, json: bool, mote_path: Vec<PathBuf>) -> ! {
  let results = match symbols_for_files(inputs, mote_path) {
    Ok(results) => results,
    Err(e) => {
      eprintln!("error: {e}");
      std::process::exit(2);
    }
  };

  if json {
    let files: Vec<JsonSymbolFile> = results
      .iter()
      .map(|r| JsonSymbolFile {
        uri: path_to_uri(&r.path),
        symbols: r
          .symbols
          .iter()
          .map(|s| JsonSymbol {
            name: s.name.clone(),
            kind: s.kind,
            range: location_to_json_range(s.location.as_ref()),
            detail: s.detail.clone(),
          })
          .collect(),
      })
      .collect();
    match serde_json::to_string_pretty(&files) {
      Ok(s) => println!("{s}"),
      Err(e) => {
        eprintln!("error: failed to serialize symbols: {e}");
        std::process::exit(2);
      }
    }
  } else {
    for result in &results {
      println!("{}", result.path.display());
      for symbol in &result.symbols {
        let loc = symbol
          .location
          .as_ref()
          .map(|l| format!("{}:{}", l.start.line, l.start.column))
          .unwrap_or_else(|| "?".to_string());
        println!(
          "  {} {} ({loc})",
          symbol_kind_label(symbol.kind),
          symbol.name
        );
      }
    }
  }

  std::process::exit(0);
}

// --- `hover`/`definition` --------------------------------------------------
//
// Deliberately name-based, not a walk of the checked term tree to the exact
// sub-expression under the cursor: `identifier_at` extracts the token
// touching the cursor by a plain text scan, then both commands look it up
// by NAME in the target file's own symbol index (`symbols_for_files`) —
// same scope as `symbols --json`, single-file only, no cross-file `use`
// resolution and no scope-awareness (a local variable shadowing a
// same-named top-level def resolves to the top-level one). Getting exact
// sub-expression resolution and cross-file `use`-aware lookup right needs
// walking the checked (pre-raise) `CoreTerm` — `raise_core` intentionally
// discards `Ctx` when producing the final `Term` (see its own doc comment),
// so that's a larger, separately-scoped follow-up, not attempted here.

/// The identifier/path token touching 1-indexed `(line, col)` in `source`
/// — e.g. `"add"`, `"List.map"` — plus its own 1-indexed `(start_col,
/// end_col)` span on that line, for reporting a precise hover range.
/// Identifier characters: alphanumeric, `_`, `.` (Monad's path
/// separator), `'` (allowed in identifiers, e.g. `x'`). Returns `None` if
/// the position isn't on an identifier character at all.
pub(crate) fn identifier_at(source: &str, line: u32, col: usize) -> Option<(String, usize, usize)> {
  let line_text = source.lines().nth((line as usize).checked_sub(1)?)?;
  let chars: Vec<char> = line_text.chars().collect();
  let idx = col.checked_sub(1)?;
  if idx >= chars.len() {
    return None;
  }
  let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '.' || c == '\'';
  if !is_ident(chars[idx]) {
    return None;
  }
  let mut start = idx;
  while start > 0 && is_ident(chars[start - 1]) {
    start -= 1;
  }
  let mut end = idx;
  while end + 1 < chars.len() && is_ident(chars[end + 1]) {
    end += 1;
  }
  let name: String = chars[start..=end].iter().collect();
  Some((name, start + 1, end + 2))
}

/// Match `name` against an already-computed symbol list — exact match
/// first (the common case: cursor on a bare `add`), then "declared name
/// ends with `.name`" as a fallback for a qualified reference (`List.map`
/// typed at the call site resolving to a symbol whose own recorded name
/// already includes a module prefix). Pure lookup, no I/O — shared by the
/// disk-based CLI path (`find_symbol_in_file`) and the LSP server's
/// in-memory-buffer path (`lsp::hover`/`lsp::definition`, which computes
/// its own symbol list via `symbols_from_source` instead of reading the
/// file back off disk).
pub(crate) fn find_symbol_by_name<'a>(
  symbols: &'a [SymbolInfo],
  name: &str,
) -> Option<&'a SymbolInfo> {
  symbols.iter().find(|s| s.name == name).or_else(|| {
    symbols
      .iter()
      .find(|s| s.name.ends_with(&format!(".{name}")))
  })
}

/// Disk-reading convenience wrapper: compute `file`'s own symbol index
/// (via `symbols_for_files`, same as the `symbols` command) and look
/// `name` up in it.
fn find_symbol_in_file(file: &Path, name: &str, mote_path: Vec<PathBuf>) -> Option<SymbolInfo> {
  let results = symbols_for_files(vec![file.to_path_buf()], mote_path).ok()?;
  let symbols = results.into_iter().find(|r| r.path == file)?.symbols;
  find_symbol_by_name(&symbols, name).cloned()
}

#[derive(serde::Serialize)]
struct JsonHover {
  contents: String,
  kind: String,
  range: JsonRange,
}

#[derive(serde::Serialize)]
struct JsonLocation {
  uri: String,
  range: JsonRange,
}

fn run_hover(
  file: PathBuf,
  line: u32,
  col: usize,
  json: bool,
  mote_path: Vec<PathBuf>,
) -> Result<(), String> {
  let source = std::fs::read_to_string(&file).map_err(|e| format!("{e}"))?;
  let found = identifier_at(&source, line, col).and_then(|(name, start_col, end_col)| {
    find_symbol_in_file(&file, &name, mote_path).map(|sym| (sym, start_col, end_col))
  });

  match found {
    None => {
      if json {
        println!("null");
      } else {
        println!("(no symbol found at {line}:{col})");
      }
    }
    Some((sym, start_col, end_col)) => {
      let contents = sym
        .detail
        .clone()
        .unwrap_or_else(|| format!("{} {}", symbol_kind_label(sym.kind), sym.name));
      if json {
        let hover = JsonHover {
          contents,
          kind: symbol_kind_label(sym.kind).to_string(),
          range: JsonRange {
            start: JsonPosition {
              line: line.saturating_sub(1),
              character: start_col.saturating_sub(1),
            },
            end: JsonPosition {
              line: line.saturating_sub(1),
              character: end_col.saturating_sub(1),
            },
          },
        };
        let s = serde_json::to_string_pretty(&hover)
          .map_err(|e| format!("failed to serialize hover: {e}"))?;
        println!("{s}");
      } else {
        println!("{contents}");
      }
    }
  }
  Ok(())
}

fn run_definition(
  file: PathBuf,
  line: u32,
  col: usize,
  json: bool,
  mote_path: Vec<PathBuf>,
) -> Result<(), String> {
  let source = std::fs::read_to_string(&file).map_err(|e| format!("{e}"))?;
  let found = identifier_at(&source, line, col)
    .and_then(|(name, _, _)| find_symbol_in_file(&file, &name, mote_path));

  match found {
    None => {
      if json {
        println!("null");
      } else {
        println!("(no definition found at {line}:{col})");
      }
    }
    Some(sym) => {
      if json {
        let loc = JsonLocation {
          uri: path_to_uri(&file),
          range: location_to_json_range(sym.location.as_ref()),
        };
        let s = serde_json::to_string_pretty(&loc)
          .map_err(|e| format!("failed to serialize location: {e}"))?;
        println!("{s}");
      } else {
        match &sym.location {
          Some(loc) => println!("{}:{}:{}", file.display(), loc.start.line, loc.start.column),
          None => println!("{} (no location)", file.display()),
        }
      }
    }
  }
  Ok(())
}

fn main() -> Result<(), String> {
  let cli = Cli::parse();
  execute(cli.command)
}

fn execute(command: Commands) -> Result<(), String> {
  match command {
    #[cfg(feature = "repl")]
    Commands::Repl {
      debug,
      benchmark,
      color,
      no_color,
      max_depth,
    } => {
      let use_colors = color && !no_color;
      repl(EvalOptions {
        debug,
        benchmark,
        use_colors,
        max_recursion_depth: max_depth,
      })
      .map_err(|e| e.to_string())
    }
    #[cfg(not(feature = "repl"))]
    Commands::Repl { .. } => {
      Err("REPL support was not compiled in. Install with repl feature enabled.".into())
    }
    Commands::Run {
      input,
      debug,
      benchmark,
      args,
      color,
      no_color,
      max_depth,
      mut mote_path,
      manifest_path,
    } => {
      let use_colors = color && !no_color;
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      let result = run(
        input,
        args,
        EvalOptions {
          debug,
          benchmark,
          use_colors,
          max_recursion_depth: max_depth,
        },
        mote_path,
      );
      match result {
        Ok(_) => (),
        Err(ref e) => {
          eprintln!("error: {e}")
        }
      }
      result
    }
    Commands::Test {
      inputs,
      debug,
      benchmark,
      color,
      no_color,
      max_depth,
      timeout,
      jobs,
      sequential,
      mut mote_path,
      manifest_path,
    } => {
      let use_colors = color && !no_color;
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      let num_threads = if sequential {
        1
      } else {
        jobs.unwrap_or_else(|| {
          std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
        })
      };
      let result = run_tests(
        inputs,
        EvalOptions {
          debug,
          benchmark,
          use_colors,
          max_recursion_depth: max_depth,
        },
        num_threads,
        timeout.map(|s| std::time::Duration::from_secs_f64(s)),
        mote_path,
      );
      match result {
        Ok(_) => (),
        Err(ref e) => {
          eprintln!("error: {e}")
        }
      }
      result
    }
    Commands::Check {
      inputs,
      json,
      color,
      no_color,
      mut mote_path,
      manifest_path,
    } => {
      let use_colors = color && !no_color;
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      // `run_check` always exits the process itself (it needs a 3-way
      // 0/1/2 exit code — success/errors-found/internal-failure — that
      // `execute`'s shared `Result<(), String>` return convention, used
      // by every other command, can't distinguish).
      run_check(inputs, json, use_colors, mote_path)
    }
    Commands::Symbols {
      inputs,
      json,
      mut mote_path,
      manifest_path,
    } => {
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      run_symbols(inputs, json, mote_path)
    }
    Commands::Hover {
      file,
      line,
      col,
      json,
      mut mote_path,
      manifest_path,
    } => {
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      let result = run_hover(file, line, col, json, mote_path);
      if let Err(ref e) = result {
        eprintln!("error: {e}");
      }
      result
    }
    Commands::Definition {
      file,
      line,
      col,
      json,
      mut mote_path,
      manifest_path,
    } => {
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      let result = run_definition(file, line, col, json, mote_path);
      if let Err(ref e) = result {
        eprintln!("error: {e}");
      }
      result
    }
    Commands::OrganizeImports {
      inputs,
      write,
      mut mote_path,
      manifest_path,
    } => {
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      let result = run_organize_imports(inputs, write, mote_path);
      if let Err(ref e) = result {
        eprintln!("error: {e}");
      }
      result
    }
    Commands::Lsp {
      mut mote_path,
      manifest_path,
    } => {
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      let result = lsp::run(mote_path);
      if let Err(ref e) = result {
        eprintln!("error: {e}");
      }
      result
    }
  }
}
