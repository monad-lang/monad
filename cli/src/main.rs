use std::path::PathBuf;

use clap::{Parser, Subcommand};
use monad_core::{eval::EvalOptions, run, run_tests};

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
    } => {
      let use_colors = color && !no_color;
      let result = run(
        input,
        args,
        EvalOptions {
          debug,
          benchmark,
          use_colors,
          max_recursion_depth: max_depth,
        },
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
    } => {
      let use_colors = color && !no_color;
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
    } => {
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
