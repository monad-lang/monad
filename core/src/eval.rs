pub mod constraint;
pub mod derive_cli;
#[cfg(test)]
pub mod derive_cli_test;
pub mod macro_expand;
#[cfg(test)]
pub mod macro_test;
pub mod termination;
pub mod r#type;

/// Options shared by every entry point that runs a Monad program (`run`,
/// `repl`, the LSP/MCP servers, the wasm crate) — debug/benchmark toggles,
/// color output, and a recursion-depth cap. Historically also threaded
/// through the tree-walking evaluator's own `eval`/`eval_inner` (removed —
/// see `plans/implementations/core-term-closure-evaluator.md`); kept here,
/// at this same `crate::eval::EvalOptions` path, purely because every one
/// of those call sites already imports it from here and there is no
/// reason to move a plain data struct just because the evaluator that used
/// to live alongside it is gone.
#[derive(Clone, PartialEq, Default)]
pub struct EvalOptions {
  pub debug: bool,
  pub benchmark: bool,
  pub use_colors: bool,
  pub max_recursion_depth: Option<u64>,
}
