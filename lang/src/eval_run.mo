/// The `monad eval` pipeline, as a library: load + elaborate, type-check
/// the target, lower its `main` to CoreIr, and run it on the interpreter.
/// `cli`'s eval command and weaver's `monad_eval` tool both call this --
/// one pipeline, one error vocabulary.
///
/// Pure programs only: `basic_native_table` covers I64 and String ops,
/// nothing else, so IO/println and the rest fail with `ce_unknown_native`.
use lang::types {
    Decl, Identifier, LocalScope, ModulePath, NamePath, id,
    module_path_to_string_colon, show_identifier, show_module_path,
}
use lang::module {
    CheckDiagnostics, ElaboratedModules, check_module_with_scope_path,
    elaborate_loaded_modules, elaborate_module_decls_reporting, best_effort_decls,
}
use lang::codegen::decls {filter_reachable_decls}
use lang::codegen::emit {validate_reachable_elaborated}
use lang::lower_core_ir {lower_ctx_from_decls, lower_root, LowerError}
use lang::core_ir {CoreIr}
use lang::core_eval {eval, basic_native_table}
use lang::core_value {GlobalTable, Env, global_cache_new, global_table_len}
use lang::typecheck::meta_eval {show_value_debug, show_core_eval_error_debug}
use std::list {List.intercalate}

/// Evaluate a source file's `main`; `Ok` is the text to print (warnings
/// included), `Err` is the staged failure with its diagnostics.
pub def EvalRun.run_file (file_path : String) (verbose : Bool) : IO (Result String String) := do {
    let em_r <- elaborate_loaded_modules file_path false verbose;
    match em_r {
        Result.err e => IO.pure (Result.err (String.concat "FAILED at stage: load (could not load dependencies: " (String.concat e ")"))),
        Result.ok em => EvalRun.check_and_eval em file_path verbose,
    }
}

pub def EvalRun.check_and_eval (em : ElaboratedModules) (file_path : String) (verbose : Bool) : IO (Result String String) := do {
    let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
    let checked <- check_module_with_scope_path em.scope em.target_decls empty_locs file_path verbose;
    let warns : List String := CheckDiagnostics.warnings checked;
    let diags : List String := CheckDiagnostics.errors checked;
    match diags {
        List.cons _ _ =>
            IO.pure (Result.err (String.concat "FAILED at stage: typecheck (target file did not typecheck cleanly)\n"
                (List.intercalate "\n" diags))),
        List.empty => do {
            let r <- EvalRun.lower_and_eval em;
            return (with_warnings warns r)
        },
    }
}

def with_warnings (warns : List String) (r : Result String String) : Result String String :=
    match warns {
        List.empty => r,
        List.cons _ _ =>
            let pre : String := String.concat
                (List.intercalate "\n" (List.map (fn (w : String) => String.concat "warning: " w) warns)) "\n" in
            match r {
                Result.ok s => Result.ok (String.concat pre s),
                Result.err e => Result.err (String.concat pre e),
            },
    }

#[partial]
pub def EvalRun.lower_and_eval (em : ElaboratedModules) : IO (Result String String) := do {
    // The "elaborate + dispatch" recipe the codegen pipeline uses: the
    // raw elaborated graph still carries syntactic class-method calls.
    // `_reporting`, not `_best_effort`: these decls are about to be
    // LOWERED and evaluated, so a reachable decl that failed to
    // elaborate must not be silently kept -- the same hard gate the
    // compile and test-driver pipelines run. The reachable closure is
    // rooted at the bare "main" the lowerer itself uses below.
    let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
    let elab_report := elaborate_module_decls_reporting em.scope em.elaborated_decls empty_locs;
    let dispatched : List Decl := best_effort_decls elab_report;
    let reachable : List Decl := filter_reachable_decls ["main"] dispatched;
    match validate_reachable_elaborated elab_report reachable {
        Result.err e =>
            IO.pure (Result.err (String.concat "FAILED at stage: elaborate ("
                (String.concat e ")"))),
        Result.ok _ => EvalRun.lower_dispatched dispatched,
    }
}

/// `lower_and_eval`'s lowering tail, split out so the gate above adds one
/// match level without deepening this def's match/do nest (the 4-deep
/// bare-match chain in one do-block arm is the shape `lang/parser.mo`
/// fails to parse).
#[partial]
pub def EvalRun.lower_dispatched (dispatched : List Decl) : IO (Result String String) := do {
    // `lower_root` roots at a DEF name, not a module name; the graph is
    // from BEFORE `qualify_modules`, so the name is still bare.
    let root_mp : ModulePath := ModulePath.mk [Identifier.id "main"];
    let root_np : NamePath := NamePath.mk [Identifier.id "main"];
    let ctx := lower_ctx_from_decls root_mp dispatched;
    match lower_root ctx root_np {
        Result.err e =>
            IO.pure (Result.err (String.concat "FAILED at stage: lower ("
                (String.concat (EvalRun.show_lower_error e) ")"))),
        Result.ok pr =>
            match pr {
                Pair.pair ir globals => EvalRun.eval_lowered ir globals,
            },
    }
}

#[partial]
pub def EvalRun.eval_lowered (ir : CoreIr) (globals : GlobalTable) : IO (Result String String) :=
    match eval ir Env.env_nil globals basic_native_table (global_cache_new (global_table_len globals)) {
        Pair.pair r _ =>
            match r {
                Result.ok v => IO.pure (Result.ok (String.concat "Eval result " (show_value_debug v))),
                Result.err e =>
                    IO.pure (Result.err (String.concat "FAILED at stage: eval ("
                        (String.concat (show_core_eval_error_debug e) ")"))),
            },
    }

/// Every `LowerError` variant: a missing arm is a runtime crash exactly
/// when the diagnosis matters most.
#[partial]
pub def EvalRun.show_lower_error (e : LowerError) : String :=
    match e {
        LowerError.le_unresolved_name name => String.concat "unresolved name " (show_identifier name),
        LowerError.le_unresolved_module_path path => String.concat "unresolved module path " (module_path_to_string_colon path),
        LowerError.le_unknown_inductive path => String.concat "unknown inductive " (show_module_path path),
        LowerError.le_unknown_constructor path => String.concat "unknown constructor " (show_module_path path),
        LowerError.le_unknown_native name => String.concat "unknown native " (show_identifier name),
        LowerError.le_type_level_term => "type-level term reached lowering",
        LowerError.le_con_hole_before_filled_arg => "constructor hole before a filled arg",
        LowerError.le_struct_lit_survived => "struct literal reached lowering un-desugared (give the literal an explicit `: StructName` annotation, or bind it to an annotated local)",
        LowerError.le_float_literal_unsupported => "float literals are not supported by `monad eval` (the eval IR cannot carry one yet); `monad test` and `monad build` compile them correctly",
        LowerError.le_unresolved_macro_artifact => "an unresolved macro-template variable or quote reached lowering",
        LowerError.le_elim_not_lowered => "a dependent match/if reached meta-eval lowering with no lowering rule yet",
        LowerError.le_in_def path inner => String.concat "in def " (String.concat (show_module_path path) (String.concat ": " (EvalRun.show_lower_error inner))),
    }
