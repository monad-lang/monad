// The shared evaluator's library root.
//
// `run` is the pure recipe: import it directly from the wasm engine
// (`use eval::run {...}`), never through this hub, so `file`/`session` and
// their filesystem natives stay out of the reachable graph.
//
// `file` is `monad eval`'s filesystem entry; `session` is the REPL state
// machine. Both are for native callers.
pub use lib::run {
    EvalCheck, EvalFailure, EvalOptions, EvalStage, EvalSuccess, EvalTarget,
    Eval.check_elaborated, Eval.run_elaborated, Eval.run_sources, Eval.type_of,
}
pub use lib::file {Eval.run_file}
pub use lib::session {
    EvalInput, EvalResponse, EvalSession,
    Eval.classify, Eval.new_session, Eval.step,
}
