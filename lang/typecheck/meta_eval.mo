/// Real evaluation of a meta-`def` (a `TypeInfo -> List Decl` function,
/// e.g. `std/derive.mo`'s `derive_lens_meta`) against a `Value` argument
/// -- the self-hosted analogue of `core/src/eval/meta_compile.rs`'s
/// `MetaEvalContext` (Rust).
///
/// Unlike the Rust reference, this needs no type-check as a
/// prerequisite: `lang/core_eval.mo` (the closure-based `CoreIr`
/// evaluator) and `lang/lower_core_ir.mo` (`Term` -> `CoreIr` lowering)
/// already exist, are already tested end-to-end
/// (`lang/tests/core_eval_lang_tests.mo`'s own `lower_and_run`), and
/// build straight from a raw `List Decl` (`lower_ctx_from_decls`) --
/// this module just drives that existing machinery directly, mirroring
/// `lower_and_run`'s exact shape.
///
/// **Caller's responsibility, not this module's:** `dispatched_decls`
/// must already be a decl list where every class-method call site
/// (`==`, `BEq.beq`, `Bool.and`, ...) has been resolved to a concrete,
/// directly-callable function -- `lower_core_ir.mo`'s free-variable
/// resolution has no concept of typeclass dictionaries. The caller
/// (`lang/typecheck/macro_queue.mo`'s `expand_decls_graph`) is
/// responsible for running `elaborate_module_decls_best_effort` +
/// `resolve_class_calls_decls` (the same "prepare for real execution"
/// pipeline `lang/codegen/test_driver.mo` already runs before compiling
/// a test driver) before ever calling `meta_eval_invoke`.
use lang.core_eval {CoreEvalError, apply, basic_native_table, eval}
use lang.core_ir {CoreIr, IrLit}
use lang.core_value {GlobalCache, GlobalTable, Value, global_cache_new, global_table_len}
use lang.lower_core_ir {LowerCtx, LowerError, lower_ctx_from_decls, lower_root}
use lang.types {Decl, Identifier, ModulePath}

def show_lower_error_debug (e : LowerError) : String :=
    match e {
        LowerError.le_unresolved_name id_ => String.concat "le_unresolved_name " (id_str id_),
        LowerError.le_unresolved_module_path mp => String.concat "le_unresolved_module_path " (show_module_path_ mp),
        LowerError.le_unknown_inductive mp => String.concat "le_unknown_inductive " (show_module_path_ mp),
        LowerError.le_unknown_constructor mp => String.concat "le_unknown_constructor " (show_module_path_ mp),
        LowerError.le_unknown_native id_ => String.concat "le_unknown_native " (id_str id_),
        LowerError.le_type_level_term => "le_type_level_term",
        LowerError.le_con_hole_before_filled_arg => "le_con_hole_before_filled_arg",
        LowerError.le_in_def path inner => String.concat "in " (String.concat (show_module_path_ path) (String.concat ": " (show_lower_error_debug inner))),
    }

/// Evaluate `meta_def_name` (a top-level `def` in `dispatched_decls`
/// with a `TypeInfo -> List Decl` shape) for real, applied to `arg`
/// (typically a `TypeInfo` `Value` built by
/// `lang/typecheck/meta_reflect.mo`'s `build_type_info_value`), and
/// return its result `Value` (typically a `List Decl` value, ready for
/// `meta_reflect.reify_decls_value_to_decls`).
def meta_eval_invoke (dispatched_decls : List Decl) (meta_def_name : ModulePath) (arg : Value) : Result String Value :=
    let ctx : LowerCtx := lower_ctx_from_decls meta_eval_root dispatched_decls in
    match lower_root ctx meta_def_name {
        Result.err e => Result.err (String.concat "meta_eval_invoke: failed to lower " (String.concat (show_module_path_ meta_def_name) (String.concat ": " (show_lower_error_debug e)))),
        Result.ok pr =>
            match pr {
                Pair.pair ir globals =>
                    match run_to_value ir globals {
                        Result.err e => Result.err e,
                        Result.ok f => apply_to_value f arg globals,
                    },
            },
    }

/// A stand-in root path for `lower_ctx_from_decls` -- only used to seed
/// `Scope.module_id` (irrelevant to name RESOLUTION, which is always by
/// full path, see `lang/scope.mo`'s `scope_resolve_name`), never
/// resolved against directly.
def meta_eval_root : ModulePath := ModulePath.mp (List.cons (Identifier.id "__meta_eval__") List.empty)

def show_module_path_ (mp : ModulePath) : String :=
    match mp { ModulePath.mp ids => join_ids ids }

#[partial]
def join_ids (ids : List Identifier) : String :=
    match ids {
        List.empty => "",
        List.cons hd rest =>
            match rest {
                List.empty => id_str hd,
                List.cons _ _ => String.concat (id_str hd) (String.concat "." (join_ids rest)),
            },
    }

def id_str (id : Identifier) : String := match id { Identifier.id s => s }

def run_to_value (ir : CoreIr) (globals : GlobalTable) : Result String Value :=
    match force_global_ir ir globals {
        Pair.pair r _cache =>
            match r {
                Result.ok v => Result.ok v,
                Result.err e => Result.err (String.concat "meta_eval_invoke: evaluation of the meta-def's own body failed: " (show_core_eval_error_debug e)),
            },
    }

/// `lower_root`'s own `ir` is the meta-def's BODY (a lambda, since every
/// current meta-def takes exactly one `TypeInfo` param) -- reduce it to
/// a `Value` (a closure) via the plain evaluator, same as
/// `lang/tests/core_eval_lang_tests.mo`'s `run_lowered`.
def force_global_ir (ir : CoreIr) (globals : GlobalTable) : Pair (Result CoreEvalError Value) GlobalCache :=
    eval ir Env.env_nil globals basic_native_table (global_cache_new (global_table_len globals))

def apply_to_value (f : Value) (arg : Value) (globals : GlobalTable) : Result String Value :=
    match apply f arg globals basic_native_table (global_cache_new (global_table_len globals)) {
        Pair.pair r _cache =>
            match r {
                Result.ok v => Result.ok v,
                Result.err e => Result.err (String.concat "meta_eval_invoke: applying the meta-def to its TypeInfo argument failed: " (show_core_eval_error_debug e)),
            },
    }

def show_value_debug (v : Value) : String :=
    match v {
        Value.v_lit l => show_irlit_debug l,
        Value.v_con tag args => String.concat "v_con#" (String.concat (I64.to_string tag) (String.concat "/" (I64.to_string (List.length args)))),
        Value.v_closure _ _ => "v_closure",
        Value.v_partial_ntv nid args => String.concat "v_partial_ntv#" (String.concat (I64.to_string nid) (String.concat "/" (I64.to_string (List.length args)))),
    }

def show_irlit_debug (l : IrLit) : String :=
    match l {
        IrLit.ir_str s => String.concat "\"" (String.concat s "\""),
        IrLit.ir_num n _ => I64.to_string n,
        IrLit.ir_char _ => "<char>",
        IrLit.ir_float _ _ => "<float>",
        IrLit.ir_sort lvl => String.concat "Sort " (I64.to_string lvl),
    }

def show_core_eval_error_debug (e : CoreEvalError) : String :=
    match e {
        CoreEvalError.ce_unbound_local idx => String.concat "ce_unbound_local " (I64.to_string idx),
        CoreEvalError.ce_unknown_global idx => String.concat "ce_unknown_global " (I64.to_string idx),
        CoreEvalError.ce_unresolved_global path => String.concat "ce_unresolved_global " (show_module_path_ path),
        CoreEvalError.ce_not_a_function v arg => String.concat "ce_not_a_function " (String.concat (show_value_debug v) (String.concat " applied to arg " (show_value_debug arg))),
        CoreEvalError.ce_not_a_constructor v => String.concat "ce_not_a_constructor " (show_value_debug v),
        CoreEvalError.ce_case_index_out_of_bounds tag => String.concat "ce_case_index_out_of_bounds " (I64.to_string tag),
        CoreEvalError.ce_arity_mismatch expected got => String.concat "ce_arity_mismatch expected=" (String.concat (I64.to_string expected) (String.concat " got=" (I64.to_string got))),
        CoreEvalError.ce_cycle idx => String.concat "ce_cycle " (I64.to_string idx),
        CoreEvalError.ce_unknown_native native_id => String.concat "ce_unknown_native " (I64.to_string native_id),
        CoreEvalError.ce_native_arg_error msg => String.concat "ce_native_arg_error " msg,
        CoreEvalError.ce_non_exhaustive_match inductive ctor => String.concat "ce_non_exhaustive_match " (String.concat (show_module_path_ inductive) (String.concat "." (id_str ctor))),
    }

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Decl` fixtures, same convention as
// `lang/tests/core_eval_lang_tests.mo`'s own `lower_and_run`-driven
// tests -- proves `meta_eval_invoke` actually drives the real
// lower+eval+apply pipeline end to end, not just that it typechecks.

def sentinel_ : I64 := -1

def mp1 (s : String) : ModulePath := ModulePath.mp (List.cons (Identifier.id s) List.empty)

def named_ (s : String) : DebugName := DebugName.named (Identifier.id s)

def free_var_ (s : String) : Term := Term.var sentinel_ (named_ s)

def num_ (n : I64) : Term := Term.lit (Literal.num n NumSuffix.i64)

def def_decl_ (name : String) (term : Term) : Decl :=
    Decl.def_d (Def.mk (mp1 name) Term.hole term List.empty List.empty Visibility.package_private)

def value_num_is (v : Value) (expected : I64) : Bool :=
    match v {
        Value.v_lit l => irlit_num_is l expected,
        _ => false,
    }

def irlit_num_is (l : IrLit) (expected : I64) : Bool :=
    match l {
        IrLit.ir_num n _ => I64.beq n expected,
        _ => false,
    }

/// `def const_answer (x : Hole) : I64 := 42` -- ignores its argument
/// entirely, proving the basic lower+eval+apply plumbing works even
/// when the meta-def never touches `arg`.
def const_answer_term : Term := Term.lam (named_ "x") Term.hole (num_ 42)
def const_answer_decls : List Decl := List.cons (def_decl_ "const_answer" const_answer_term) List.empty

#[test]
def test_meta_eval_invoke_ignores_arg_returns_literal : Bool :=
    match meta_eval_invoke const_answer_decls (mp1 "const_answer") (Value.v_lit (IrLit.ir_num 0 NumSuffix.i64)) {
        Result.err _ => false,
        Result.ok v => value_num_is v 42,
    }

/// `def add_one (n : I64) : I64 := i64_add n 1` -- actually uses `arg`,
/// proving `apply` really threads the supplied `Value` through, not
/// just that a constant body evaluates.
def add_one_term : Term :=
    Term.lam (named_ "n") Term.hole (Term.ntv (Native.mk (Identifier.id "i64_add") 2 (List.cons (Option.some (Term.var 0 (named_ "n"))) (List.cons (Option.some (num_ 1)) List.empty))))
def add_one_decls : List Decl := List.cons (def_decl_ "add_one" add_one_term) List.empty

#[test]
def test_meta_eval_invoke_applies_arg_through_native : Bool :=
    match meta_eval_invoke add_one_decls (mp1 "add_one") (Value.v_lit (IrLit.ir_num 41 NumSuffix.i64)) {
        Result.err _ => false,
        Result.ok v => value_num_is v 42,
    }

/// A meta-def that itself calls ANOTHER, transitively-reachable def
/// (`double`) -- proves the whole-graph worklist (`process_pending`,
/// `lang/lower_core_ir.mo`) really resolves multi-hop references, not
/// just a single def in isolation (the shape every real
/// `std/derive.mo` meta-def actually needs: `derive_lens_meta` calls
/// `lens_decls_for_ctor` calls `lens_field_decl` calls ...).
def double_term : Term :=
    Term.lam (named_ "n") Term.hole (Term.ntv (Native.mk (Identifier.id "i64_add") 2 (List.cons (Option.some (Term.var 0 (named_ "n"))) (List.cons (Option.some (Term.var 0 (named_ "n"))) List.empty))))
def quadruple_term : Term :=
    Term.lam (named_ "n") Term.hole (Term.app (free_var_ "double") (Term.app (free_var_ "double") (Term.var 0 (named_ "n"))))
def quadruple_decls : List Decl :=
    List.cons (def_decl_ "double" double_term) (List.cons (def_decl_ "quadruple" quadruple_term) List.empty)

#[test]
def test_meta_eval_invoke_resolves_transitive_dependency : Bool :=
    match meta_eval_invoke quadruple_decls (mp1 "quadruple") (Value.v_lit (IrLit.ir_num 5 NumSuffix.i64)) {
        Result.err _ => false,
        Result.ok v => value_num_is v 20,
    }

#[test]
def test_meta_eval_invoke_unknown_def_name_errs : Bool :=
    match meta_eval_invoke const_answer_decls (mp1 "does_not_exist") (Value.v_lit (IrLit.ir_num 0 NumSuffix.i64)) {
        Result.err _ => true,
        Result.ok _ => false,
    }
