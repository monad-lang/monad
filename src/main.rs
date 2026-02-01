use std::path::PathBuf;

use clap::{Parser, Subcommand};
use monad::{eval::EvalOptions, repl, run};

#[derive(Subcommand, Debug)]
enum Commands {
  Repl {
    #[arg(short, long, default_value_t = false)]
    debug: bool,
  },

  Run {
    /// Path to the input file
    #[arg(value_name = "FILE")]
    input: PathBuf,
    #[arg(short, long, default_value_t = false)]
    debug: bool,
    #[arg(value_name = "ARGS")]
    args: Vec<String>,
  },
}

/// Simple CLI that reads a file and prints its contents (or basic stats).
#[derive(Debug, Parser)]
#[command(name = "file-reader", version, about = "Read a file from disk")]
struct Cli {
  #[command(subcommand)]
  command: Commands,
}

fn main() -> Result<(), String> {
  let cli = Cli::parse();

  match cli.command {
    Commands::Repl { debug } => repl(EvalOptions { debug }).map_err(|e| format!("{e}")),
    Commands::Run { input, debug, args } => {
      run(input, args, EvalOptions { debug }).map_err(|e| format!("{e}"))
    }
  }
}
