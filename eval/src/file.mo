// `monad eval`'s entry point: the filesystem main module, the shared
// recipe, and the legacy text vocabulary `cli` and weaver's `monad_eval`
// tool print. Kept in its own module (not `lib::run`) so the wasm engine
// never reaches the disk loader: `/try` imports `eval::run` directly.

use lang::mote {Mote.affine_mode_of_path}
use lang::module {elaborate_loaded_modules}
use lang::types {Identifier, ModulePath}
use std::list {List.intercalate}
use lib::run {EvalFailure, EvalOptions, EvalStage, EvalTarget, Eval.run_elaborated}

/// Evaluate a source file's root `main`; `Ok` is the text to print
/// (warnings included), `Err` is the staged failure with its diagnostics.
/// Byte-for-byte the vocabulary `lang::eval_run` printed before the
/// evaluator moved here, including the warning prefix on failures.
pub def Eval.run_file (file_path : String) (verbose : Bool) : IO (Result String String) := do {
    let em_r <- elaborate_loaded_modules file_path false verbose;
    match em_r {
        Result.err e =>
            IO.pure (Result.err
                (String.concat "FAILED at stage: load (could not load dependencies: "
                    (String.concat e ")"))),
        Result.ok em => do {
            let mode <- Mote.affine_mode_of_path file_path;
            let options : EvalOptions :=
                { fuel := -1, depth_limit := -1, affine := mode, label := file_path,
                  verbose := verbose, want_type := false, require_entry := false };
            let target : EvalTarget :=
                { root := "main", context_path := ModulePath.mk [Identifier.id "main"] };
            let r <- Eval.run_elaborated em options target;
            match r {
                Result.ok s =>
                    IO.pure (Result.ok
                        (with_warnings s.warnings (String.concat "Eval result " s.debug_text))),
                Result.err e =>
                    IO.pure (Result.err (with_warnings e.warnings (legacy_failure e))),
            }
        },
    }
}

/// The staged failure lines `monad eval` has always printed.
def legacy_failure (e : EvalFailure) : String :=
    match e.stage {
        EvalStage.eval_stage_typecheck =>
            String.concat "FAILED at stage: typecheck (target file did not typecheck cleanly)\n"
                e.message,
        EvalStage.eval_stage_elaborate => wrapped "elaborate" e.message,
        EvalStage.eval_stage_lower => wrapped "lower" e.message,
        EvalStage.eval_stage_eval => wrapped "eval" e.message,
        EvalStage.eval_stage_load => wrapped "load" e.message,
        _ => wrapped "lower" e.message,
    }

def wrapped (stage : String) (message : String) : String :=
    String.concat "FAILED at stage: "
        (String.concat stage (String.concat " (" (String.concat message ")")))

/// Prefix each warning with `warning: ` and prepend the block, matching
/// `lang::eval_run`'s `with_warnings`.
def with_warnings (warnings : List String) (text : String) : String :=
    match warnings {
        List.empty => text,
        List.cons _ _ =>
            String.concat
                (List.intercalate "\n"
                    (List.map (fn (w : String) => String.concat "warning: " w) warnings))
                (String.concat "\n" text),
    }
