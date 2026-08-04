//! Scratch driver for Phase 8 parity checking -- not a real example,
//! just a quick way to run `run_parity_tests` against arbitrary paths
//! from the command line and see a summary. Usage: `cargo run --release
//! -p monad-core --example parity_check -- init`.

use std::path::PathBuf;

fn main() {
  let args: Vec<String> = std::env::args().skip(1).collect();
  let inputs: Vec<PathBuf> = if args.is_empty() {
    vec![PathBuf::from("init")]
  } else {
    args.iter().map(PathBuf::from).collect()
  };

  match monad_core::core_parity::run_parity_tests(inputs, vec![]) {
    Ok(summary) => {
      let total = summary.results.len();
      let mismatches: Vec<_> = summary.mismatches().collect();
      println!("{total} tests discovered, {} mismatches", mismatches.len());
      for r in &mismatches {
        println!(
          "MISMATCH {}: tree_walker={:?} core_eval={:?}",
          r.path, r.tree_walker, r.core_eval
        );
      }
      if mismatches.is_empty() {
        println!("all {total} tests agree between tree-walker and core-eval");
      }
    }
    Err(e) => {
      println!("run_parity_tests failed: {e}");
    }
  }
}
