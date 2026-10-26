/// The /try engine's presentation adapter: source in, rendered result out.
///
/// The evaluator itself is `eval::run` (the shared mote): the standard
/// source-list loader, the pure elaboration, and the same
/// typecheck/elaborate/lower/evaluate recipe `monad eval` and `monad repl`
/// use. What stays here is /try's own policy -- the size gate, the
/// `std`/`lib::` rejection messages, the browser's fuel and depth budget,
/// the status codes the worker maps to names, and the 8 KiB clipping.
///
/// Status codes (the worker maps them to names):
///   0 ok, 1 parse, 2 type/load, 3 lower, 4 eval, 5 fuel, 6 internal, 7 size.

use lang::core_eval {CoreEvalError}
use lang::module {
  ModuleInfo, ModuleSource, init_module_path, make_module_info,
  make_module_source, prelude_module_path, try_parse_decls_strict
}
use lang::types {AffineMode, Decl, Identifier, ModulePath, show_module_path}
use lib::sources {SourceModule}
use eval::run {
  EvalFailure, EvalOptions, EvalStage, EvalSuccess, EvalTarget, Eval.run_sources
}

pub struct Outcome {
    status : I64,
    value : String,
    typ : String,
    error : String,
    notes : String
}

pub def max_source : I64 := 262144

/// The UI reads a result through a 64 KiB scratch buffer, so the engine
/// caps every rendered string well below it -- and cuts on a UTF-8
/// boundary, so a truncated value never ends in U+FFFD.
pub def max_result_bytes : I64 := 8192

pub def eval_fuel : I64 := 2000000

/// The web profile's stack cannot take much more than this; a clean
/// `ce_recursion_too_deep` beats a wasm trap.
pub def eval_depth : I64 := 200

def scratch_module_path : ModulePath := ModulePath.mk [Identifier.id "Scratch"]

def no_main_message : String :=
    "no `main` definition: a /try program must define `main`, e.g. `def main : I64 := 2 + 3`"

def params_message : String := "`main` must take no parameters"

def fuel_message : String :=
    "evaluation stopped at the step limit (2,000,000); the program may loop forever"

def depth_message : String := "the program recursed more than 200 calls deep"

def too_large_message : String :=
    "the program is larger than 256 KiB; /try is a scratchpad, not a build service"

def std_message : String :=
    "`std` and IO are not available in the browser REPL (the ambient prelude only)"

def lib_message : String :=
    "`use lib::` is a mote's self-reference; name a module explicitly (e.g. `use init::list`)"

def unknown_native_message : String := "this operation is not available in the browser REPL"

def outcome_ok (value : String) (typ : String) (notes : String) : Outcome :=
    { status := 0, value := clip value, typ := typ, error := "", notes := clip notes }

def outcome_error (status : I64) (message : String) : Outcome :=
    { status := status, value := "", typ := "", error := clip message, notes := "" }

def clip (s : String) : String :=
    if Bool.not (I64.lt max_result_bytes (String.length s))
    then s
    else String.concat (utf8_prefix s max_result_bytes) "…"

/// The longest prefix of at most `max` bytes that ends between codepoints:
/// step back over continuation bytes (0b10xxxxxx).
#[terminating]
def utf8_prefix (s : String) (max : I64) : String :=
    String.slice s 0 (back_to_boundary s max)

#[terminating]
def back_to_boundary (s : String) (n : I64) : I64 :=
    if Bool.not (I64.lt 0 n) then 0
    else
        match String.get s (I64.sub n 1) {
            Option.some b =>
                if U8.lt b 128u8 then n
                else if U8.lt b 192u8 then back_to_boundary s (I64.sub n 1)
                else n,
            Option.none => 0,
        }

/// `sources` are the served `.mo` files the page handed over (see
/// `lib::sources`); the program is checked against exactly those, so the
/// prelude is whatever the site ships rather than a copy inside the module.
pub def run_source (sources : List SourceModule) (source : String) : IO Outcome :=
    if I64.gt (String.length source) max_source
    then IO.pure (outcome_error 7 too_large_message)
    else match try_parse_decls_strict source (Option.some "scratchpad.mo") {
        Result.err e => IO.pure (outcome_error 1 e),
        Result.ok decls => run_parsed sources decls,
    }

def run_parsed (sources : List SourceModule) (decls : List Decl) : IO Outcome := do {
    let main : ModuleInfo := make_module_info scratch_module_path "scratchpad.mo" decls;
    let module_sources : List ModuleSource := to_sources sources List.empty;
    let options : EvalOptions :=
        { fuel := eval_fuel, depth_limit := eval_depth, affine := AffineMode.affine_warn,
          label := "scratchpad.mo", verbose := false, want_type := true,
          require_entry := true };
    let target : EvalTarget :=
        { root := "main", context_path := scratch_module_path };
    let r <- Eval.run_sources main [prelude_module_path, init_module_path]
                module_sources reject_module options target;
    match r {
        Result.ok success => IO.pure (outcome_of_success success),
        Result.err failure => IO.pure (outcome_of_failure failure),
    }
}

/// The page supplies modules by their identity; `ModuleSource` carries the
/// same identity plus the owning mote the `lib` rewrite needs.
#[terminating]
def to_sources (mods : List SourceModule) (acc : List ModuleSource) : List ModuleSource :=
    match mods {
        List.empty => List.reverse acc,
        List.cons m rest =>
            let source : ModuleSource :=
                make_module_source (path_of m.segments) m.mote m.file_path m.source
            in
            to_sources rest (List.cons source acc),
    }

def path_of (segs : List String) : ModulePath := ModulePath.mk (ids_of segs)

def ids_of (segs : List String) : List Identifier :=
    match segs {
        List.empty => List.empty,
        List.cons s rest => List.cons (Identifier.id s) (ids_of rest),
    }

/// The rejections the browser REPL adds to the standard loader. It runs
/// before lookup, so the message is /try's, not a generic
/// `unresolved module`. (The loader only serves `init`'s modules, and is
/// seeded with `prelude`/`init`.)
def reject_module (mp : ModulePath) : Option String :=
    let path : String := show_module_path mp
    in
    if is_std_path path
    then Option.some std_message
    else if is_lib_path path
    then Option.some lib_message
    else Option.none

def is_std_path (path : String) : Bool :=
    Bool.or (String.beq path "std") (String.starts_with "std." path)

def is_lib_path (path : String) : Bool :=
    Bool.or (String.beq path "lib") (String.starts_with "lib." path)

def outcome_of_success (s : EvalSuccess) : Outcome :=
    outcome_ok s.value_text s.type_text (join_lines s.warnings)

def outcome_of_failure (f : EvalFailure) : Outcome :=
    match f.stage {
        EvalStage.eval_stage_load => outcome_error 2 f.message,
        EvalStage.eval_stage_entry_missing => outcome_error 2 no_main_message,
        EvalStage.eval_stage_entry_params => outcome_error 2 params_message,
        EvalStage.eval_stage_typecheck => outcome_error 2 f.message,
        EvalStage.eval_stage_elaborate => outcome_error 3 f.message,
        EvalStage.eval_stage_lower => outcome_error 3 f.message,
        EvalStage.eval_stage_eval => outcome_of_eval_failure f,
    }

/// The eval-stage causes get /try's sentences (and the fuel status the
/// worker maps to its own message); anything else falls back to the
/// debug rendering the shared runner put in `message`.
def outcome_of_eval_failure (f : EvalFailure) : Outcome :=
    match f.eval_error {
        Option.none => outcome_error 4 f.message,
        Option.some e => core_eval_failure e f.message,
    }

def core_eval_failure (e : CoreEvalError) (fallback : String) : Outcome :=
    match e {
        CoreEvalError.ce_out_of_fuel => outcome_error 5 fuel_message,
        CoreEvalError.ce_recursion_too_deep => outcome_error 4 depth_message,
        CoreEvalError.ce_unknown_native _ => outcome_error 4 unknown_native_message,
        CoreEvalError.ce_not_a_function _ _ =>
            outcome_error 4 "a value was used as a function; the checker accepted a call whose callee is not a function",
        CoreEvalError.ce_not_a_constructor _ =>
            outcome_error 4 "a match scrutinee was not a constructor value",
        CoreEvalError.ce_non_exhaustive_match _ _ =>
            outcome_error 4 "a match had no arm for the value it received",
        CoreEvalError.ce_native_arg_error msg =>
            outcome_error 4 (String.concat "invalid argument to a primitive: " msg),
        _ => outcome_error 4 fallback,
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
