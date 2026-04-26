use std::path::PathBuf;

use clap::{Parser, Subcommand};
use monad_core::{eval::EvalOptions, run};

#[cfg(feature = "repl")]
use monad_core::repl;

#[derive(Subcommand, Debug)]
enum Commands {
  Repl {
    #[arg(short, long, default_value_t = false)]
    debug: bool,
  },

  Run {
    #[arg(value_name = "FILE")]
    input: PathBuf,
    #[arg(short, long, default_value_t = false)]
    debug: bool,
    #[arg(value_name = "ARGS", trailing_var_arg = true)]
    args: Vec<String>,
  },
}

#[derive(Debug, Parser)]
#[command(name = "monad", version, about = "Monad language interpreter")]
struct Cli {
  #[command(subcommand)]
  command: Commands,
}

fn main() -> Result<(), String> {
  let cli = Cli::parse();

  match cli.command {
    #[cfg(feature = "repl")]
    Commands::Repl { debug } => repl(EvalOptions { debug }).map_err(|e| format!("{e}")),
    #[cfg(not(feature = "repl"))]
    Commands::Repl { .. } => {
      Err("REPL support was not compiled in. Install with repl feature enabled.".into())
    }
    Commands::Run { input, debug, args } => {
      let result = run(input, args, EvalOptions { debug });
      match result {
        Ok(_) => (),
        Err(ref e) => {
          println!("error: {e}")
        }
      }
      result
    }
  }
}
