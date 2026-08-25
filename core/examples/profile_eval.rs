//! Standalone profiling harness for the `force_global` eval hot path.
//!
//! Does the parse + check + lower setup ONCE (so it is amortized to ~0
//! under a sampling profiler), then runs `force_global` with a fresh
//! `GlobalCache` `ITERATIONS` times so the eval loop dominates the
//! instruction count. Run under `valgrind --tool=callgrind` for a clean
//! eval-only profile, e.g.:
//!
//!   cargo build --release --example profile_eval
//!   valgrind --tool=callgrind --callgrind-out-file=/tmp/cg.out \
//!     ./target/release/examples/profile_eval

use monad_core::core_check_module::check_all_modules_capturing_core;
use monad_core::core_eval::force_global;
use monad_core::core_value::{GlobalCache, GlobalTable, NativeTable};
use monad_core::lower_core_ir::{LoweredProgram, lower_program};
use monad_core::term::module::{
  default_modules, init_package_sources, load_decls_from_text_with_path,
};
use monad_core::term::{ModulePath, mpt};

const WORKLOAD: &str = r#"
use init

#[terminating]
def fib (n : I64) : I64 :=
    if n == 0
    then 0
    else if n == 1
    then 1
    else (fib (n - 1)) + (fib (n - 2))

def main : I64 := fib 26
"#;

const ITERATIONS: usize = 20;

fn main() {
  let path = ModulePath::top("'bench");
  let loaded = default_modules().expect("default_modules");
  let decls = load_decls_from_text_with_path(WORKLOAD, &Default::default()).expect("parse");
  let mut modules: Vec<_> = init_package_sources()
    .expect("init_package_sources")
    .into_iter()
    .map(|(p, text)| {
      let d = load_decls_from_text_with_path(&text, &Default::default())
        .unwrap_or_else(|e| panic!("parse {p}: {e}"));
      (p, d)
    })
    .collect();
  modules.push((path.clone(), decls));

  let program = check_all_modules_capturing_core(&modules, &loaded).expect("check");
  let lowered: LoweredProgram = lower_program(&program).expect("lower");
  let main_idx = lowered.index_of(&mpt("main")).expect("main not found");

  let mut acc: i64 = 0;
  for _ in 0..ITERATIONS {
    let natives = NativeTable::from_lowered(&lowered);
    let globals = GlobalTable::new(lowered.globals.clone());
    let mut cache = GlobalCache::new(globals.len());
    let v = force_global(main_idx, &globals, &natives, &mut cache).expect("core eval error");
    // Touch the result so the loop isn't optimized away.
    if let monad_core::core_value::Value::Lit(monad_core::core_ir::IrLit::Num(n, _)) = v {
      acc = acc.wrapping_add(n);
    }
  }
  eprintln!("profile_eval done; acc = {acc}");
}
