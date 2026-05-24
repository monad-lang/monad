use std::path::PathBuf;

use clap::{Parser, Subcommand};
use monad_core::{eval::EvalOptions, run, run_tests, term::mote::Manifest};

#[cfg(feature = "repl")]
use monad_core::repl;

#[cfg(feature = "llvm")]
use monad_llvm_codegen::{CompileOptions, OutputKind, compile};

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

  #[cfg(feature = "llvm")]
  Compile {
    #[arg(value_name = "FILE")]
    input: PathBuf,
    #[arg(short, long, default_value = ".")]
    output_dir: PathBuf,
    #[arg(long)]
    output_name: Option<String>,
    #[arg(long, default_value = "exe")]
    output_kind: String,
    #[arg(long, default_value_t = false)]
    keep_intermediates: bool,
    #[arg(short, long, default_value_t = false)]
    debug: bool,
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

  if manifest.is_some() {
    if let Some(root) = project_root {
      let src_dir = root.join("src");
      if src_dir.is_dir() && !mote_path.contains(&src_dir) {
        mote_path.push(src_dir);
      }
    }
  }
}

fn main() -> Result<(), String> {
  let cli = Cli::parse();

  match cli.command {
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
    #[cfg(feature = "llvm")]
    Commands::Compile {
      input,
      output_dir,
      output_name,
      output_kind,
      keep_intermediates,
      debug,
      mut mote_path,
      manifest_path,
    } => {
      augment_mote_paths(&mut mote_path, manifest_path.as_ref());
      let output_kind = match output_kind.as_str() {
        "exe" => OutputKind::Executable,
        "shared" | "so" => OutputKind::SharedObject,
        _ => {
          return Err(format!(
            "Unknown output kind: {output_kind}. Use 'exe' or 'shared'."
          ));
        }
      };

      let name = output_name.unwrap_or_else(|| {
        input
          .file_stem()
          .and_then(|s| s.to_str())
          .unwrap_or("output")
          .to_string()
      });

      let options = CompileOptions {
        output_dir,
        output_name: name,
        output_kind,
        keep_intermediates,
      };

      let result = compile(&input, options);
      match &result {
        Ok(r) => {
          if debug {
            println!("Step 1: LLVM IR generated -> {}", r.ir_path.display());
            println!(
              "Step 2: Object file compiled -> {}",
              r.object_path.display()
            );
            println!(
              "Step 3: Runtime compiled -> {}",
              r.runtime_object_path.display()
            );
            println!("Step 4: Linked -> {}", r.output_path.display());
          }
          println!("Output: {}", r.output_path.display());
        }
        Err(e) => {
          eprintln!("error: {e}")
        }
      }
      result.map(|_| ())
    }
  }
}
