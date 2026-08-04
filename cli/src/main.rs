use std::path::PathBuf;

use clap::{Parser, Subcommand};
use monad_core::{
  check_files,
  diag::{Diagnostic, Severity, render_diagnostics},
  eval::EvalOptions,
  run, run_tests,
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
struct JsonPosition {
  line: u32,
  character: usize,
}

#[derive(serde::Serialize)]
struct JsonRange {
  start: JsonPosition,
  end: JsonPosition,
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
fn to_json_position(loc: &monad_core::term::Location) -> JsonPosition {
  JsonPosition {
    line: loc.line.saturating_sub(1),
    character: loc.column.saturating_sub(1),
  }
}

fn to_json_diagnostic(diag: &Diagnostic) -> JsonDiagnostic {
  let range = match &diag.location {
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
  };
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

fn path_to_uri(path: &std::path::Path) -> String {
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
  }
}
