// The one evaluator recipe, shared by `monad eval`, the browser REPL's
// engine, and `monad repl`: typecheck the target, elaborate and dispatch
// it, lower its root def, and run the result on `lang::core_eval`.
//
// Only the loader and the policy vary between callers. The loader hands
// this module an `ElaboratedModules` (the disk loader in `Eval.run_file`,
// the supplied-source loader in `Eval.run_sources`); the policy is the
// fuel/depth budget, the affine mode, the diagnostics label, the entry
// name, and whether the type-directed renderings are wanted.
//
// No filesystem entry point lives here. `motes/try_engine` imports THIS
// module directly (never bare `eval`), which keeps `Eval.run_file` and the
// REPL session -- and therefore every gated IO native -- out of the wasm
// reachable graph.

use lang::types {
    AffineMode, Decl, Def, Identifier, LocalScope, ModulePath, NamePath, Scope, Term,
    show_name_path,
}
use lang::module {
    CheckDiagnostics, ElaboratedModules, LoadedModules, ModuleInfo, ModuleSource,
    best_effort_decls, check_module_with_scope_classified, elaborate_loaded_modules_pure,
    elaborate_module_decls_reporting, load_modules_from_sources,
}
use lang::codegen::decls {filter_reachable_decls}
use lang::codegen::emit {validate_reachable_elaborated}
use lang::core_eval {CoreEvalError, basic_native_table, eval}
use lang::core_ir {CoreIr}
use lang::core_value {Env, GlobalTable, Value, global_cache_new_fueled, global_table_len}
use lang::lower_core_ir {lower_ctx_from_decls, lower_root, show_lower_error}
use lang::repl::value_format {format_type, format_value}
use lang::typecheck::infer {empty_locals, type_check}
use lang::typecheck::meta_eval {show_core_eval_error_debug, show_value_debug}

/// Where a failure stopped. `entry_missing`/`entry_params` exist only for
/// `require_entry` callers (/try and the REPL); `monad eval` lets a missing
/// `main` surface as a lower-stage error, exactly as it always has.
pub type EvalStage {
    eval_stage_load,
    eval_stage_entry_missing,
    eval_stage_entry_params,
    eval_stage_typecheck,
    eval_stage_elaborate,
    eval_stage_lower,
    eval_stage_eval,
}

pub struct EvalOptions {
    fuel : I64,          // -1 unlimited
    depth_limit : I64,   // -1 unlimited
    affine : AffineMode,
    label : String,      // diagnostics path ("scratchpad.mo", "repl.mo", ...)
    verbose : Bool,
    want_type : Bool,    // compute the type-directed value/type renderings
    require_entry : Bool // friendly no-entry / parameter errors
}

pub struct EvalTarget {
    root : String,               // "main", or the REPL's "__repl_expr_<n>"
    context_path : ModulePath    // the lowerer's root module
}

pub struct EvalCheck {
    errors : List String,
    warnings : List String
}

pub struct EvalFailure {
    stage : EvalStage,
    message : String,
    eval_error : Option CoreEvalError,
    warnings : List String
}

pub struct EvalSuccess {
    value_text : String,   // format_value (want_type only)
    type_text : String,    // format_type (want_type only)
    debug_text : String,   // show_value_debug
    warnings : List String
}

// --- Failure constructors ---------------------------------------------

def stage_error (stage : EvalStage) (message : String) (warnings : List String) : EvalFailure :=
    { stage := stage, message := message, eval_error := Option.none, warnings := warnings }

def typecheck_error (message : String) (warnings : List String) : EvalFailure :=
    stage_error EvalStage.eval_stage_typecheck message warnings

def entry_error (stage : EvalStage) (root : String) (warnings : List String) : EvalFailure :=
    let message : String :=
        match stage {
            EvalStage.eval_stage_entry_missing =>
                String.concat "no `" (String.concat root "` definition"),
            _ => String.concat "`" (String.concat root "` must take no parameters"),
        }
    in
    stage_error stage message warnings

def eval_error_of (e : CoreEvalError) (warnings : List String) : EvalFailure :=
    { stage := EvalStage.eval_stage_eval,
      message := show_core_eval_error_debug e,
      eval_error := Option.some e,
      warnings := warnings }

// --- Checking ---------------------------------------------------------

/// Typecheck the target module. Split out because the REPL's declaration
/// step needs exactly this (no lowering, no evaluation) to decide whether
/// an entry joins the session.
pub def Eval.check_elaborated (em : ElaboratedModules) (affine : AffineMode)
    (label : String) (verbose : Bool) : IO EvalCheck := do {
    let locals : LocalScope := empty_locals;
    let diags <- check_module_with_scope_classified affine em.scope em.target_decls
                    locals (Option.some label) verbose;
    let out : EvalCheck :=
        { errors := CheckDiagnostics.errors diags,
          warnings := CheckDiagnostics.warnings diags };
    return out
}

// --- The shared recipe ------------------------------------------------

pub def Eval.run_elaborated (em : ElaboratedModules) (o : EvalOptions)
    (t : EvalTarget) : IO (Result EvalFailure EvalSuccess) :=
    match o {
        { fuel, depth_limit, affine, label, verbose, want_type, require_entry } =>
            run_target em fuel depth_limit affine label verbose want_type require_entry t,
    }

def run_target (em : ElaboratedModules) (fuel : I64) (depth_limit : I64)
    (affine : AffineMode) (label : String) (verbose : Bool) (want_type : Bool)
    (require_entry : Bool) (t : EvalTarget) : IO (Result EvalFailure EvalSuccess) :=
    match t {
        { root, context_path } =>
            run_checked em fuel depth_limit affine label verbose want_type require_entry root context_path,
    }

def run_checked (em : ElaboratedModules) (fuel : I64) (depth_limit : I64)
    (affine : AffineMode) (label : String) (verbose : Bool) (want_type : Bool)
    (require_entry : Bool) (root : String) (context_path : ModulePath)
    : IO (Result EvalFailure EvalSuccess) := do {
    let checked <- Eval.check_elaborated em affine label verbose;
    match checked.errors {
        List.cons first rest =>
            IO.pure (Result.err
                (typecheck_error (join_lines (List.cons first rest)) checked.warnings)),
        List.empty =>
            if require_entry
            then require_root em fuel depth_limit want_type root context_path checked.warnings
            else dispatch em fuel depth_limit want_type root context_path Term.hole checked.warnings,
    }
}

def require_root (em : ElaboratedModules) (fuel : I64) (depth_limit : I64)
    (want_type : Bool) (root : String) (context_path : ModulePath)
    (warnings : List String) : IO (Result EvalFailure EvalSuccess) :=
    match find_root em.target_decls root {
        Option.none =>
            IO.pure (Result.err
                (entry_error EvalStage.eval_stage_entry_missing root warnings)),
        Option.some d =>
            if List.is_empty d.params
            then dispatch em fuel depth_limit want_type root context_path
                    (root_type em.scope d) warnings
            else IO.pure (Result.err
                (entry_error EvalStage.eval_stage_entry_params root warnings)),
    }

/// The elaborate-and-dispatch step every backend runs before lowering: the
/// raw elaborated graph still carries syntactic class-method calls, so it
/// is re-elaborated in reporting mode and the reachable closure from the
/// root is validated. Same recipe as the compile pipeline.
#[partial]
def dispatch (em : ElaboratedModules) (fuel : I64) (depth_limit : I64)
    (want_type : Bool) (root : String) (context_path : ModulePath) (typ : Term)
    (warnings : List String) : IO (Result EvalFailure EvalSuccess) := do {
    let empty_locs : LocalScope := empty_locals;
    let report := elaborate_module_decls_reporting em.scope em.elaborated_decls empty_locs;
    let dispatched : List Decl := best_effort_decls report;
    let reachable : List Decl := filter_reachable_decls [root] dispatched;
    match validate_reachable_elaborated report reachable {
        Result.err e =>
            IO.pure (Result.err
                (stage_error EvalStage.eval_stage_elaborate e warnings)),
        Result.ok _ =>
            lower em.scope dispatched fuel depth_limit want_type root context_path typ warnings,
    }
}

#[partial]
def lower (scope : Scope) (dispatched : List Decl) (fuel : I64) (depth_limit : I64)
    (want_type : Bool) (root : String) (context_path : ModulePath) (typ : Term)
    (warnings : List String) : IO (Result EvalFailure EvalSuccess) :=
    let root_np : NamePath := NamePath.mk [Identifier.id root]
    in
    let ctx := lower_ctx_from_decls context_path dispatched
    in
    match lower_root ctx root_np {
        Result.err e =>
            IO.pure (Result.err
                (stage_error EvalStage.eval_stage_lower (show_lower_error e) warnings)),
        Result.ok pr => evaluate scope fuel depth_limit want_type typ warnings pr,
    }

#[partial]
def evaluate (scope : Scope) (fuel : I64) (depth_limit : I64) (want_type : Bool)
    (typ : Term) (warnings : List String) (pr : Pair CoreIr GlobalTable)
    : IO (Result EvalFailure EvalSuccess) :=
    match pr {
        Pair.pair ir globals =>
            eval_ir scope ir globals fuel depth_limit want_type typ warnings,
    }

#[partial]
def eval_ir (scope : Scope) (ir : CoreIr) (globals : GlobalTable) (fuel : I64)
    (depth_limit : I64) (want_type : Bool) (typ : Term) (warnings : List String)
    : IO (Result EvalFailure EvalSuccess) :=
    match eval ir Env.env_nil globals basic_native_table
            (global_cache_new_fueled (global_table_len globals) fuel depth_limit) {
        Pair.pair r _ =>
            match r {
                Result.ok v => IO.pure (render_success scope v typ want_type warnings),
                Result.err e => IO.pure (Result.err (eval_error_of e warnings)),
            },
    }

// --- Rendering the success --------------------------------------------

/// Struct literals live in their own declared-return-type defs; a bare
/// literal in a return/`if` position is the documented codegen pitfall.
def success_typed (scope : Scope) (typ : Term) (v : Value)
    (warnings : List String) : EvalSuccess :=
    { value_text := format_value scope typ v,
      type_text := format_type scope typ,
      debug_text := show_value_debug v,
      warnings := warnings }

def success_debug (v : Value) (warnings : List String) : EvalSuccess :=
    { value_text := "",
      type_text := "",
      debug_text := show_value_debug v,
      warnings := warnings }

def render_success (scope : Scope) (v : Value) (typ : Term) (want_type : Bool)
    (warnings : List String) : Result EvalFailure EvalSuccess :=
    if want_type
    then Result.ok (success_typed scope typ v warnings)
    else Result.ok (success_debug v warnings)

// --- Type-only path (the REPL's `:type`) -------------------------------

pub def Eval.type_of (em : ElaboratedModules) (o : EvalOptions) (t : EvalTarget)
    : IO (Result EvalFailure String) :=
    match o {
        { affine, label, verbose, .. } =>
            type_of_target em affine label verbose t,
    }

def type_of_target (em : ElaboratedModules) (affine : AffineMode)
    (label : String) (verbose : Bool) (t : EvalTarget)
    : IO (Result EvalFailure String) :=
    match t {
        { root, .. } =>
            do {
                let checked <- Eval.check_elaborated em affine label verbose;
                match checked.errors {
                    List.cons first rest =>
                        IO.pure (Result.err
                            (typecheck_error (join_lines (List.cons first rest))
                                checked.warnings)),
                    List.empty =>
                        IO.pure (type_of_root em.scope em.target_decls root),
                }
            },
    }

def type_of_root (scope : Scope) (decls : List Decl) (root : String)
    : Result EvalFailure String :=
    match find_root decls root {
        Option.none =>
            Result.err (entry_error EvalStage.eval_stage_entry_missing root List.empty),
        Option.some d =>
            Result.ok (format_type scope (root_type scope d)),
    }

// --- The supplied-source entry (/try) --------------------------------

/// The whole pipeline for a module set the caller already holds: the
/// standard source-list loader, the pure elaboration, then the shared
/// recipe. This is what /try calls; `monad eval` uses `Eval.run_file`.
pub def Eval.run_sources (main : ModuleInfo) (seeds : List ModulePath)
    (sources : List ModuleSource) (reject : ModulePath -> Option String)
    (o : EvalOptions) (t : EvalTarget) : IO (Result EvalFailure EvalSuccess) :=
    match load_modules_from_sources main seeds sources reject {
        Result.err e =>
            IO.pure (Result.err (stage_error EvalStage.eval_stage_load e List.empty)),
        Result.ok loaded =>
            match elaborate_loaded_modules_pure loaded false {
                Result.err e =>
                    IO.pure (Result.err (stage_error EvalStage.eval_stage_load e List.empty)),
                Result.ok em => Eval.run_elaborated em o t,
            },
    }

// --- Root lookup and its type -----------------------------------------

def find_root (decls : List Decl) (root : String) : Option Def :=
    match decls {
        List.empty => Option.none,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    if String.beq (show_name_path def_.name) root
                    then Option.some def_
                    else find_root rest root,
                _ => find_root rest root,
            },
    }

/// The type the root was checked against, or the inferred one when it was
/// declared `: _`. `elaborate_def_with_scope` deliberately leaves `Def.typ`
/// unchanged, so a hole is re-inferred here for display only.
def root_type (scope : Scope) (d : Def) : Term :=
    match d.typ {
        Term.hole =>
            match type_check d.term Term.hole scope List.empty empty_locals {
                Result.ok tt => tt.typ,
                Result.err _ => Term.hole,
            },
        _ => d.typ,
    }

def join_lines (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest =>
            match rest {
                List.empty => x,
                List.cons _ _ => String.concat x (String.concat "\n" (join_lines rest)),
            },
    }
