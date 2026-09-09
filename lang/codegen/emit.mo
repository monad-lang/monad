use io {IO}
use std.bench {now, report, report_since, since}
// `str_map_*` below is a `std.map` `HashMap String V`. Empty import:
// naming any of `std.map`'s `Map`-class-instance exports explicitly hits
// a pre-existing latent instance/dictionary-resolution bug (same
// workaround `lang/scope.mo`'s own `modpath_map_*`/`use std.map {}` doc
// comment documents, and `std/map_tests.mo`/`bench/scope_lookup.mo`
// already use) -- everything remains available regardless via the same
// always-on mechanism that lets any top-level type/def resolve without
// being explicitly `use`d.
use std.map {}
use std.list {intercalate}
use lang.types {
  Con, DebugName, Decl, Def, Identifier, InductConstructor, Inductive, Literal,
  LoadedModules, LocalScope, Location, MatchCase, ModulePath, Native, Operator,
  Multiplicity, Param, Scope, ScopeData, Struct, StructField, StructLitField,
  Term, TypeConstraint, UseFilter, UseItem, Visibility, sentinel,
  show_identifier, show_module_path,
  app, con, ctx, def_d, forall, hole, id, if_, inductive_d, lam,
  lit, match_, mc, mk, mp, name, named, ntv, num, operator,
  param_many, pi, str, type_, unnamed, var,
}
use lang.codegen.ir {
  DbgLoc, LLVMBasicBlock, LLVMDeclaration, LLVMFunction, LLVMGlobal, LLVMInstruction,
  LLVMModule, LLVMType, LLVMValue, NativeOp, ParamPair, PhiPair, add, alloc_closure,
  alloc_constructor, assign, bitcast, bool_, branch, call, comment, emit_module,
  fn_, gep, global_, i64_, i8_, icmp_eq, icmp_ne, icmp_sgt, icmp_slt, int32_, int_,
  jump, llvm_symbol_ref, load, mk, mul, native_op, op_add, op_eq,
  op_file_exists, op_gt, op_lt,
  op_mul, op_ne, op_print_str, op_read_file, op_sdiv, op_sub, op_write_file,
  parm_, phi, ptr, ptrtoint, ret, sdiv, show_llvm_type, sub, trunc, var_, void_val, zext,
}
use lang.codegen.runtime {runtime_native_functions}
use lang.codegen.validate {
  validate_all_call_targets_defined, validate_no_colliding_def_symbols,
  validate_no_undesugared_struct_lits, validate_no_unwired_natives,
}
use lang.codegen.ctors {
  build_constructor_arity_map, build_constructor_tag_map, constructor_arity,
  constructor_tag, is_constructor_var,
}
use lang.codegen.natives {
  NativeWrapKind, lookup_native, lookup_native_any, native_attr_target_name,
  native_op_table, native_runtime_fn_name, runtime_declarations,
}
use lang.codegen.decls {
  build_def_name_map, collect_all_decls_from_modules, def_name_str, extract_defs,
  extract_inductives, filter_reachable_decls, reachable_defs_from,
}
use lang.codegen.tco {apply_self_tco}
use lang.codegen.qualify {qtest_def, qualified_def_name_str, qualify_modules}
use lang.codegen.free_names {collect_referenced_names, free_names_of_term}
use lang.codegen.ctx {
  CodegenCtx, CtxStrPair, LocalBinding, build_arity_table,
  collect_db_params, ctx_bind_local, ctx_lookup_arity, ctx_lookup_ctor_arity,
  ctx_lookup_ctor_tag, ctx_lookup_local, ctx_reset_locals, ctx_restore_locals,
  dbg_loc_of_location, empty_ctx, fresh_label, fresh_temp,
  lookup_binding, mk,
}
use lang.codegen.symbols {
  bare_modpath, def_symbol_name, ends_with_main, extract_base_name,
  mangle_identifiers, module_path_to_str, ref_symbol_name,
  replace_dots_with_underscores, string_find_last, symbol_identifier,
  unqualify_def_name,
}
use lang.codegen.util {
  dedup_idents, dedup_idents_go, dedup_strs, dedup_strs_go, drop_last_instr,
  ident_in_list, identifier_eq, join_semicolon_msgs,
  list_contains_str, rev_vals, str_map_empty, str_map_insert, str_map_lookup,
}
use lang.module {
  LoadedModules, ModuleInfo, bench_step, elaborate_module_decls_best_effort,
  get_loaded_all, get_loaded_main, mk, resolve_open_aliases_in_modules,
}
use lang.scope {
  add_constraint_dict_params_decls, alias_map_empty, alias_map_insert,
  alias_map_lookup, build_scope_from_decls, collect_classes, collect_open_aliases,
  modpath_eq,
  resolve_open_alias_decls,
  collect_infixes, promote_instance_defs, resolve_class_calls_decls,
  resolve_infix_decls, strip_all_leading_binders,
  validate_no_unresolved_class_calls,
}

open IO {println}
open LLVMType {i32_, i64_, i8_, ptr}
open LLVMValue {
  add, alloc_closure, alloc_constructor, bitcast, bool_, call, gep, global_,
  icmp_eq, icmp_ne, icmp_sgt, icmp_slt, int32_, int_, load, mul, native_op, parm_,
  phi, ptrtoint, sdiv, sub, trunc, var_, void_val, zext,
}

type CompileResult {
    ok (ctx : CodegenCtx) (instrs : List LLVMInstruction) (val : LLVMValue) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal),
}

#[partial]
def empty_arities : HashMap String I64 := str_map_empty

/// The `entry` text `alloc_closure` needs (see `LLVMValue.alloc_closure`'s
/// own IR emission, `lang/codegen/ir.mo`) to box a bare reference to
/// `llvm_name` as a callable value: every top-level def in this backend
/// is compiled with the uniform `(i64, i64, ..., i64) -> i64` signature
/// (`build_llvm_params_db`/`LLVMFunction.mk`), so this is always a
/// `bitcast` of that function's own address down to `i8*` -- e.g. for
/// `arity=2`: `"bitcast (i64 (i64, i64)* @foo to i8*)"`.
#[partial]
def global_fn_ptr_text (llvm_name : String) (arity : I64) : String :=
    let fn_ty := LLVMType.fn_ (repeat_type LLVMType.i64_ arity) LLVMType.i64_ in
    String.concat "bitcast (" (String.concat (show_llvm_type fn_ty)
        (String.concat "* " (String.concat (llvm_symbol_ref llvm_name) " to i8*)")))

#[partial]
def repeat_type (ty : LLVMType) (n : I64) : List LLVMType :=
    if I64.beq n 0 then List.empty else List.cons ty (repeat_type ty (n - 1))

/// A tiny forwarding function boxed INSTEAD of `real_name`'s own entry
/// point, whenever a top-level def (arity>0) is referenced as a
/// first-class VALUE (`Term.var`'s arity>0 branch, `compile_db_term_ir`,
/// above). `apply_closureN` (`runtime.c`) now uniformly passes its own
/// closure pointer as `entry`'s first arg to every closure it invokes
/// (needed for a REAL lifted lambda to read its own captures, see
/// `compile_db_lam_ir`) -- but `real_name`'s own compiled signature
/// (`(p0..p{arity-1}) -> i64`, no leading self param) is ALSO the exact
/// signature every ordinary DIRECT call to it elsewhere in the program
/// uses, so it cannot itself grow a leading self param without breaking
/// those calls. This shim absorbs the mismatch: same uniform (self,
/// p1..p_arity) signature `apply_closureN` expects, ignores self,
/// forwards its real params through to `real_name` unchanged. `real_name`
/// itself is completely untouched.
///
/// A shim is a pure, deterministic function of `(real_name, arity)`, so
/// every boxing call site for the same def produces a byte-identical
/// shim -- `dedup_funcs_by_name` (below) collapses the duplicates once
/// the whole module's functions are assembled, rather than tracking
/// "have I already emitted a shim for X" through `CodegenCtx` (which
/// would touch every one of the dozens of call sites that construct/
/// pattern-match it).
#[partial]
def build_closure_shim_func (shim_name : String) (real_name : String) (arity : I64) : LLVMFunction :=
    let self_pair := ParamPair.mk "p0" LLVMType.i64_ in
    let real_params := build_llvm_params_from_db_shifted arity 1 in
    let params := List.cons self_pair real_params in
    let fwd_args := shim_fwd_args arity 1 in
    let call_val := LLVMValue.call real_name LLVMType.i64_ fwd_args false in
    let call_instr := LLVMInstruction.assign "r" call_val in
    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ "r") in
    let entry_block := LLVMBasicBlock.mk "entry" (List.cons call_instr (List.cons ret_instr List.empty)) in
    LLVMFunction.mk shim_name params LLVMType.i64_ (List.cons entry_block List.empty) false Option.none

#[partial]
def build_llvm_params_from_db_shifted (n : I64) (start_idx : I64) : List ParamPair :=
    if I64.beq n 0 then List.empty
    else List.cons (ParamPair.mk (String.concat "p" (I64.to_string start_idx)) LLVMType.i64_)
        (build_llvm_params_from_db_shifted (n - 1) (start_idx + 1))

#[partial]
def shim_fwd_args (n : I64) (start_idx : I64) : List LLVMValue :=
    if I64.beq n 0 then List.empty
    else List.cons (LLVMValue.parm_ start_idx) (shim_fwd_args (n - 1) (start_idx + 1))

/// A forwarding shim for an arity>0 CONSTRUCTOR referenced as a bare
/// VALUE (`compile_db_term_ir`'s `Term.var` case, e.g. `List.map
/// Identifier.id ids`) rather than immediately, fully applied. Mirrors
/// `build_closure_shim_func` just above (the ordinary-def case) exactly
/// in shape -- same uniform (self, p1..p_arity) signature `apply_
/// closureN` expects -- but instead of forwarding to another function's
/// call, allocates a genuine tagged Constructor and sets each of its
/// `arity` fields from the shim's own forwarded args.
#[partial]
def build_constructor_closure_shim_func (shim_name : String) (tag : I64) (arity : I64) : LLVMFunction :=
    let self_pair := ParamPair.mk "p0" LLVMType.i64_ in
    let real_params := build_llvm_params_from_db_shifted arity 1 in
    let params := List.cons self_pair real_params in
    let alloc_val := LLVMValue.call "alloc_constructor" LLVMType.i64_
        (List.cons (LLVMValue.int_ tag) (List.cons (LLVMValue.int_ arity) List.empty)) false in
    let alloc_instr := LLVMInstruction.assign "obj" alloc_val in
    let set_instrs := build_ctor_shim_set_fields arity 1 in
    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ "obj") in
    let entry_instrs := List.cons alloc_instr (List.append set_instrs (List.cons ret_instr List.empty)) in
    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
    LLVMFunction.mk shim_name params LLVMType.i64_ (List.cons entry_block List.empty) false Option.none

/// `monad_set_field(obj, i-1, p_i)` for i in [1, n] -- fixed temp names
/// ("s1", "s2", ...) are safe here without `CodegenCtx`/`fresh_temp`
/// threading, same reasoning as `build_shim_env_gets`'s own doc comment
/// (a shim body is always one flat sequence, never nested/reentrant).
#[partial]
def build_ctor_shim_set_fields (n : I64) (idx : I64) : List LLVMInstruction :=
    if I64.gt idx n then List.empty
    else
        let set_temp := String.concat "s" (I64.to_string idx) in
        let set_call := LLVMValue.call "monad_set_field" LLVMType.i64_
            (List.cons (LLVMValue.var_ "obj") (List.cons (LLVMValue.int_ (idx - 1)) (List.cons (LLVMValue.parm_ idx) List.empty))) false in
        let set_instr := LLVMInstruction.assign set_temp set_call in
        List.cons set_instr (build_ctor_shim_set_fields n (idx + 1))

/// See `combine_direct_call_arity_checked`'s own under-application
/// branch for the bug this fixes: boxes a genuine closure for a direct
/// top-level function call site that supplied FEWER args than the
/// callee's real declared arity, instead of emitting an arity-mismatched
/// direct call. `real_arity - supplied` is always `> 0` here (the caller
/// only reaches this on `supplied < real_arity`).
#[partial]
def combine_partial_apply (ctx_a : CodegenCtx) (name : String) (arg_vals : List LLVMValue) (real_arity : I64) (combined : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) (last_val : LLVMValue) : CompileResult :=
    let supplied := List.length arg_vals in
    let remaining := real_arity - supplied in
    match fresh_temp ctx_a {
        CtxStrPair.mk ctx1 temp =>
            let shim_name := String.concat name (String.concat "_partial_shim_" (I64.to_string supplied)) in
            let shim_func := build_partial_apply_shim_func shim_name name supplied remaining in
            let entry_text := global_fn_ptr_text shim_name (remaining + 1) in
            let box_val := LLVMValue.alloc_closure entry_text remaining arg_vals in
            let box_instr := LLVMInstruction.assign temp box_val in
            match build_set_env_instrs (LLVMValue.var_ temp) arg_vals 0 ctx1 {
                { ctx := ctx2, instrs := set_instrs } =>
                    match compose_seq ({ instrs := combined, blocks := blocks, val := last_val }) ({ instrs := List.append (List.cons box_instr List.empty) set_instrs, blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                        { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                            CompileResult.ok ctx2 new_instrs (LLVMValue.var_ temp) new_blocks (List.cons shim_func funcs) globals,
                    },
            },
    }

/// A forwarding shim for a PARTIALLY-applied top-level def. Mirrors
/// `build_closure_shim_func` (the ZERO-supplied-args case) above,
/// generalized: `captured_count` values already supplied at the call
/// site are read back via `monad_closure_get_env` (populated separately
/// by `combine_partial_apply`'s own `build_set_env_instrs` call); the
/// shim's own params (`p1..p{remaining_arity}`, past the uniform leading
/// `self` `apply_closureN` always supplies) carry whatever args are
/// still missing. Forwards `real_name`'s full argument list -- captured
/// values first, then the newly-supplied ones -- in the same order the
/// original curried application would have.
#[partial]
def build_partial_apply_shim_func (shim_name : String) (real_name : String) (captured_count : I64) (remaining_arity : I64) : LLVMFunction :=
    let self_pair := ParamPair.mk "p0" LLVMType.i64_ in
    let real_params := build_llvm_params_from_db_shifted remaining_arity 1 in
    let params := List.cons self_pair real_params in
    let env_gets := build_shim_env_gets captured_count in
    let new_arg_vals := shim_fwd_args remaining_arity 1 in
    let fwd_args := List.append env_gets.vals new_arg_vals in
    let call_val := LLVMValue.call real_name LLVMType.i64_ fwd_args false in
    let call_instr := LLVMInstruction.assign "r" call_val in
    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ "r") in
    let entry_instrs := List.append env_gets.instrs (List.cons call_instr (List.cons ret_instr List.empty)) in
    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
    LLVMFunction.mk shim_name params LLVMType.i64_ (List.cons entry_block List.empty) false Option.none

struct ShimEnvGets {
    instrs : List LLVMInstruction,
    vals : List LLVMValue,
}

/// `monad_closure_get_env(p0, i)` for i in [0, n) -- reads a partial-
/// application shim's own captured args back out, in the order
/// `combine_partial_apply` populates them via `build_set_env_instrs`.
/// Fixed temp names ("e0", "e1", ...) are safe here without
/// `CodegenCtx`/`fresh_temp` threading -- a shim body is always one flat
/// sequence, never nested/reentrant (same reasoning as `build_closure_
/// shim_func`'s own fixed `"r"` return temp).
#[partial]
def build_shim_env_gets (n : I64) : ShimEnvGets := build_shim_env_gets_go n 0

#[partial]
def build_shim_env_gets_go (n : I64) (idx : I64) : ShimEnvGets :=
    if I64.beq idx n
    then { instrs := List.empty, vals := List.empty }
    else
        let temp := String.concat "e" (I64.to_string idx) in
        let get_call := LLVMValue.call "monad_closure_get_env" LLVMType.i64_
            (List.cons (LLVMValue.parm_ 0) (List.cons (LLVMValue.int_ idx) List.empty)) false in
        let get_instr := LLVMInstruction.assign temp get_call in
        match build_shim_env_gets_go n (idx + 1) {
            { instrs := rest_instrs, vals := rest_vals } =>
                { instrs := List.cons get_instr rest_instrs, vals := List.cons (LLVMValue.var_ temp) rest_vals },
        }

/// Same 3-tier lookup shape as `constructor_tag` (hardcoded builtin
/// table, full name then base name, then `c`'s own dynamically-built
/// table) but for a consumer that ALSO knows the constructor's field
/// count -- which is every alloc/dispatch site:
///
///   - match dispatch: the case's own positional binder count
///     (`build_match_chain` -- a well-typed arm binds one binder per
///     declared field),
///   - saturated allocation: the constructor application's own
///     compiled-argument count (`compile_con_ir`),
///   - the constructor wrappers: their declared param count
///     (`compile_db_inductive_constructors`).
///
/// The ctx tier keys `ctor_tags` by the COMPOSITE bare#arity key, so
/// two different types sharing a bare constructor name at DIFFERING
/// arities answer with different tags: a match arm for `Wide.mk a b c`
/// compares against Wide's own tag, a Slim value (same bare name, one
/// field) carries a different one, and the arm can never accept -- let
/// alone `monad_get_field` past -- a Slim allocation. That differing-
/// arity collision class is what cost the v29 rung-3 ladder rung
/// (283 constructors sharing one `mk` tag at seven arities; a
/// value-position reference sized its allocation from the last
/// claimant's arity and a neighbouring object's memory came back where
/// a `List` spine pointer belonged).
///
/// The final bare-name tier only exists for a bare name claimed at one
/// single arity (real tag) -- a name claimed at several arities carries
/// the -1 sentinel there, answered as 0 by `bare_ctor_tag`. Struct
/// `mk`s never enter the map at all (structs stay `Decl.struct_d`,
/// `extract_inductives` only matches `inductive_d`), so they take the
/// 0 fallback at BOTH alloc and dispatch -- consistently, exactly as
/// before.
#[partial]
def constructor_tag_at (c : CodegenCtx) (name : String) (arity : I64) : I64 :=
    let base_name := extract_base_name name in
    // Even the FULL-name tier needs the arity guard: `Con.mk`'s own
    // `name` field is the constructor's BARE name (`compile_con_ir`
    // passes it directly), so a user `Wide.ok` arrives here as plain
    // "ok" and matched the builtin outright -- before any of the tiers
    // below could see it. That is how the wrapper function and the
    // allocation site ended up disagreeing (tag 37 vs tag 10) for the
    // same constructor.
    match str_map_lookup name builtin_ctor_tags {
        Option.some tag => if builtin_arity_matches name arity then tag else constructor_tag_at_nonbuiltin c base_name arity,
        Option.none =>
            // The BARE-name builtin tier is consulted only after the
            // composite key, and only for a matching arity. A user type
            // may declare a constructor sharing a builtin's bare name --
            // `lang/codegen/emit.mo`'s own `CompileResult.ok` carries SIX
            // fields against builtin `Result.ok`'s one -- and answering
            // the builtin's tag there hands two incompatible layouts the
            // same tag, exactly the corruption the composite key exists
            // to prevent (this one cost a v30 rung: a `CompileResult`
            // allocated with 6 fields, read back as a 1-field
            // `Result.ok`, put a raw unboxed `1` where an `Identifier`'s
            // `char*` belonged -> SIGSEGV in `__strcmp_avx2` via
            // `Similar_Identifier_similar` <- `term_matches_carrier`).
            // The FULL-name tier above stays first and is unaffected:
            // "Result.ok" names the builtin unambiguously.
            match ctx_lookup_ctor_tag c (ctor_composite_key base_name arity) {
                Option.some tag => tag,
                Option.none =>
                    match str_map_lookup base_name builtin_ctor_tags {
                        Option.some tag =>
                            // Only when the builtin really has this
                            // arity; otherwise it is a different
                            // constructor that merely shares the name.
                            if builtin_arity_matches base_name arity then tag else bare_ctor_tag c base_name,
                        Option.none => bare_ctor_tag c base_name,
                    },
            },
    }

/// `constructor_tag_at`'s tiers with the builtin tables skipped -- what a
/// name that LOOKS builtin but has the wrong arity should consult
/// instead. Separate function only because the guard above needs it
/// before the tier chain below is reached.
#[partial]
def constructor_tag_at_nonbuiltin (c : CodegenCtx) (base_name : String) (arity : I64) : I64 :=
    match ctx_lookup_ctor_tag c (ctor_composite_key base_name arity) {
        Option.some tag => tag,
        Option.none => bare_ctor_tag c base_name,
    }

/// Whether `base_name` names a BUILTIN constructor that really declares
/// `arity` fields -- the guard that keeps `constructor_tag_at`'s
/// bare-name builtin tier from claiming a same-named user constructor of
/// a different shape. An unknown name answers `false`, so it falls
/// through to the ctx table rather than silently borrowing a builtin tag.
#[partial]
def builtin_arity_matches (base_name : String) (arity : I64) : Bool :=
    match str_map_lookup base_name builtin_ctor_arities {
        Option.some a => I64.beq a arity,
        Option.none => false,
    }

#[partial]
def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

#[partial]
def compile_native_val (op : NativeOp) (lhs : LLVMValue) (rhs : LLVMValue) : LLVMValue :=
    match op {
        NativeOp.op_add => LLVMValue.add lhs rhs,
        NativeOp.op_sub => LLVMValue.sub lhs rhs,
        NativeOp.op_mul => LLVMValue.mul lhs rhs,
        NativeOp.op_sdiv => LLVMValue.sdiv lhs rhs,
        NativeOp.op_eq => LLVMValue.icmp_eq lhs rhs,
        NativeOp.op_ne => LLVMValue.icmp_ne lhs rhs,
        NativeOp.op_lt => LLVMValue.icmp_slt lhs rhs,
        NativeOp.op_gt => LLVMValue.icmp_sgt lhs rhs,
    }

#[partial]
def i64_ne (a : I64) (b : I64) : Bool := not (a == b)

#[partial]
def fold_native_const (op : NativeOp) (n1 : I64) (n2 : I64) : LLVMValue :=
    match op {
        NativeOp.op_add => LLVMValue.int_ (n1 + n2),
        NativeOp.op_sub => LLVMValue.int_ (n1 - n2),
        NativeOp.op_mul => LLVMValue.int_ (n1 * n2),
        NativeOp.op_sdiv => LLVMValue.int_ (n1 / n2),
        NativeOp.op_eq => LLVMValue.bool_ (n1 == n2),
        NativeOp.op_ne => LLVMValue.bool_ (i64_ne n1 n2),
        NativeOp.op_lt => LLVMValue.bool_ (n1 < n2),
        NativeOp.op_gt => LLVMValue.bool_ (n1 > n2),
    }

/// Now total (no `#[partial]`): every `Literal` variant is handled,
/// including `struct_lit`/`struct_update` — see their own doc comment
/// below for why they're unreachable-in-practice placeholders rather
/// than real codegen, and `lang/typecheck/infer.mo`'s
/// `type_check_struct_lit`/`type_check_struct_update` for where the
/// REAL work happens (both desugar into `Term.con`, which
/// `compile_db_term_ir`/`compile_con_ir` above already handle).
def compile_lit_ir (c : CodegenCtx) (lit_ : Literal) : CompileResult := match lit_ {
    Literal.num n suffix => CompileResult.ok c List.empty (LLVMValue.int_ n) List.empty List.empty List.empty,
    // No LLVMValue float-constant variant exists yet (codegen has no
    // float support at all currently — a separate, unstarted piece of
    // work; see Literal.flt's doc comment in lang/types.mo). Emitting a
    // zero placeholder keeps this match total without pretending to
    // support something that isn't there yet; nothing in the corpus
    // reaches this arm today.
    Literal.flt text suffix => CompileResult.ok c List.empty (LLVMValue.int_ 0) List.empty List.empty List.empty,
    Literal.str s =>
        match fresh_label c "str" {
            CtxStrPair.mk ctx1 name =>
                // Add 1 to byte length for the null terminator \00 appended in the LLVM IR
                let byte_len := String.length s + 1 in
                let global := LLVMGlobal.mk name s byte_len true in
                match fresh_temp ctx1 {
                    CtxStrPair.mk ctx2 temp =>
                        // Normalize to i64 immediately, matching every
                        // COMPUTED String's own representation
                        // (`String.concat`/`monad_string_eq`/... are all
                        // i64-typed). Without this, a bare literal used
                        // directly as a `phi`/match-merge branch value
                        // (e.g. `if b then String.concat " " x else ""`)
                        // keeps its raw `ptr i8_` type while the OTHER
                        // branch is `i64`, and `llc` rejects the
                        // resulting phi outright ("global variable
                        // reference must have pointer type") -- `phi` is
                        // the one construct here with zero tolerance for
                        // this; ordinary calls already type each argument
                        // independently (`show_llvm_value_typed`) and
                        // tolerate it via `llc`'s own lenient callee-
                        // pointer-bitcast handling, so this is the only
                        // site that actually needs the cast. See
                        // plans/implementations/2026-08-28-string-value-
                        // representation-unification.md.
                        let cast_val := LLVMValue.ptrtoint (LLVMValue.global_ name) (ptr i8_) i64_ in
                        let cast_instr := LLVMInstruction.assign temp cast_val in
                        CompileResult.ok ctx2 (List.cons cast_instr List.empty) (LLVMValue.var_ temp) List.empty List.empty (List.cons global List.empty),
                },
        },
    Literal.if_ cond then_ else_ => compile_db_if_ir c cond then_ else_,
    Literal.match_ scrutinee cases => compile_match_ir c scrutinee cases,
    // `Literal.struct_lit`/`Literal.struct_update` are effectively
    // unreachable HERE: `lang/typecheck/infer.mo`'s
    // `type_check_struct_lit` ALWAYS desugars a struct literal into a
    // real `Term.con` (never leaves a `struct_lit` Literal behind), and
    // `type_check_struct_update` does the same for struct updates
    // except in the rare case where `base`'s type can't be resolved to
    // a registered struct at all — a placeholder is emitted here rather
    // than crashing on a non-exhaustive match (which is what used to
    // happen: this whole match was `#[partial]` and simply had no case
    // for either variant at all), matching `Literal.flt`'s own
    // "keep the match total, nothing in the corpus reaches this today"
    // convention just above.
    Literal.struct_lit _fields _type_name => CompileResult.ok c List.empty LLVMValue.void_val List.empty List.empty List.empty,
    Literal.struct_update _base _fields => CompileResult.ok c List.empty LLVMValue.void_val List.empty List.empty List.empty,
}

/// Compile a match expression to LLVM IR: compiles the scrutinee once,
/// reads its runtime tag (@monad_get_tag), and generates a chain of
/// tag-comparison blocks -- one per case except the last, which is
/// always the unconditional final branch (covers both an explicit `_`
/// wildcard last arm and a naturally-exhaustive case list with no
/// wildcard, uniformly, without needing to special-case the string "_").
/// Each case's own block binds its pattern's bound names to
/// @monad_get_field calls before compiling its body. Mirrors
/// compile_db_if_ir/build_db_if_blocks/build_merge_result's N=2 pattern,
/// generalized to N cases and reusing the same helpers (fresh_label,
/// build_branch_block, ends_with_terminator).
#[partial]
def compile_match_ir (c : CodegenCtx) (scrutinee : Term) (cases : List MatchCase) : CompileResult :=
    match cases {
        List.empty =>
            // No cases - return void
            CompileResult.ok c List.empty LLVMValue.void_val List.empty List.empty List.empty,
        List.cons _ _ =>
            match compile_db_term_ir c scrutinee {
                CompileResult.ok ctx_s instrs_s val_s blocks_s funcs_s globals_s =>
                    match fresh_temp ctx_s {
                        CtxStrPair.mk ctx_tag tag_temp =>
                            let tag_call := LLVMValue.call "monad_get_tag" LLVMType.i64_ (List.cons val_s List.empty) false in
                            let tag_instr := LLVMInstruction.assign tag_temp tag_call in
                            let tag_val := LLVMValue.var_ tag_temp in
                            match fresh_label ctx_tag "check" {
                                CtxStrPair.mk ctx_check first_check_label =>
                                    match fresh_label ctx_check "merge" {
                                        CtxStrPair.mk ctx_merge merge_label =>
                                            // `match (if p then a else b) { ... }`-shaped code: the
                                            // SCRUTINEE itself branching means `instrs_s` already ends
                                            // in a terminator -- splice via `compose_seq` instead of
                                            // blindly appending (see its own doc comment above
                                            // `ends_with_terminator`).
                                            let tag_and_jump := List.cons tag_instr (List.cons (LLVMInstruction.jump first_check_label) List.empty) in
                                            match compose_seq ({ instrs := instrs_s, blocks := blocks_s, val := val_s }) ({ instrs := tag_and_jump, blocks := List.empty, val := tag_val }) {
                                                { instrs := entry_instrs, blocks := blocks_s_spliced, val := _ } =>
                                                    match build_match_chain ctx_merge tag_val val_s cases merge_label first_check_label {
                                                        { ctx := ctx_chain, blocks := chain_blocks, funcs := chain_funcs, globals := chain_globals, phis := phi_pairs } =>
                                                            match fresh_temp ctx_chain {
                                                                CtxStrPair.mk ctx_final phi_temp =>
                                                                    let phi_instr := LLVMInstruction.assign phi_temp (LLVMValue.phi phi_pairs) in
                                                                    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ phi_temp) in
                                                                    let merge_block := LLVMBasicBlock.mk merge_label (List.cons phi_instr (List.cons ret_instr List.empty)) in
                                                                    let all_blocks := append_blocks blocks_s_spliced (List.cons merge_block chain_blocks) in
                                                                    let all_funcs := List.append funcs_s chain_funcs in
                                                                    let all_globals := List.append globals_s chain_globals in
                                                                    CompileResult.ok ctx_final entry_instrs (LLVMValue.var_ phi_temp) all_blocks all_funcs all_globals,
                                                            },
                                                    },
                                            },
                                    },
                            },
                    },
            },
    }

struct MatchChainResult {
    ctx : CodegenCtx,
    blocks : List LLVMBasicBlock,
    funcs : List LLVMFunction,
    globals : List LLVMGlobal,
    phis : List PhiPair,
}

/// Recursively builds the check/case block chain for every case in
/// order. `check_label` is the label already allocated for THIS case's
/// tag comparison (or, for the last case, its own block directly -- no
/// comparison needed there).
#[partial]
def build_match_chain (c : CodegenCtx) (tag_val : LLVMValue) (scrutinee_val : LLVMValue) (cases : List MatchCase) (merge_label : String) (check_label : String) : MatchChainResult :=
    match cases {
        List.empty =>
            { ctx := c, blocks := List.empty, funcs := List.empty, globals := List.empty, phis := List.empty },
        List.cons this_case rest =>
            match rest {
                List.empty =>
                    // Last (and possibly only) case -- unconditional,
                    // check_label IS this case's own block.
                    build_match_case_block c scrutinee_val this_case check_label merge_label,
                List.cons _ _ =>
                    match fresh_label c "case" {
                        CtxStrPair.mk ctx1 case_label =>
                            match fresh_label ctx1 "check" {
                                CtxStrPair.mk ctx2 next_check_label =>
                                    match fresh_temp ctx2 {
                                        CtxStrPair.mk ctx3 cmp_temp =>
                                            match this_case {
                                                MatchCase.mc name args _body _fp =>
                                                    // Composite bare#arity key: the case's
                                                    // own positional binder count IS the
                                                    // constructor's field count for a
                                                    // well-typed arm, and it is what
                                                    // disambiguates a bare name two
                                                    // different types both declare (see
                                                    // `constructor_tag_at`).
                                                    let tag_of_case := constructor_tag_at ctx3 (symbol_identifier name) (List.length args) in
                                                    let cmp_instr := LLVMInstruction.assign cmp_temp (LLVMValue.icmp_eq tag_val (LLVMValue.int_ tag_of_case)) in
                                                    let branch_instr := LLVMInstruction.branch (LLVMValue.var_ cmp_temp) case_label next_check_label in
                                                    let check_block := LLVMBasicBlock.mk check_label (List.cons cmp_instr (List.cons branch_instr List.empty)) in
                                                    match build_match_case_block ctx3 scrutinee_val this_case case_label merge_label {
                                                        { ctx := ctx4, blocks := case_blocks, funcs := case_funcs, globals := case_globals, phis := case_phis } =>
                                                            match build_match_chain ctx4 tag_val scrutinee_val rest merge_label next_check_label {
                                                                { ctx := ctx5, blocks := rest_blocks, funcs := rest_funcs, globals := rest_globals, phis := rest_phis } =>
                                                                    {
                                                                        ctx := ctx5,
                                                                        blocks := List.cons check_block (append_blocks case_blocks rest_blocks),
                                                                        funcs := List.append case_funcs rest_funcs,
                                                                        globals := List.append case_globals rest_globals,
                                                                        phis := List.append case_phis rest_phis,
                                                                    },
                                                            },
                                                    },
                                            },
                                    },
                            },
                    },
            },
    }

struct FieldBindResult {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
}

/// Binds every name in a case's pattern args, in order, to a
/// @monad_get_field call on the scrutinee -- e.g. `cons a tail` binds
/// `a` to field 0, `tail` to field 1, matching the order fields were
/// passed to the constructor at allocation time (compile_con_ir's
/// compile_ntv_args processes constructor args in the same order).
#[partial]
def bind_match_fields (c : CodegenCtx) (scrutinee_val : LLVMValue) (args : List Identifier) (idx : I64) : FieldBindResult :=
    match args {
        List.empty => { ctx := c, instrs := List.empty },
        List.cons name rest =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 temp =>
                    let field_call := LLVMValue.call "monad_get_field" LLVMType.i64_ (List.cons scrutinee_val (List.cons (LLVMValue.int_ idx) List.empty)) false in
                    let field_instr := LLVMInstruction.assign temp field_call in
                    let ctx2 := ctx_bind_local ctx1 name (LLVMValue.var_ temp) in
                    match bind_match_fields ctx2 scrutinee_val rest (idx + 1) {
                        { ctx := ctx3, instrs := rest_instrs } =>
                            { ctx := ctx3, instrs := List.cons field_instr rest_instrs },
                    },
            },
    }

struct RetargetResult {
    blocks : List LLVMBasicBlock,
    label : String,
}

/// Finds the block among `blocks` ending in `ret <target_val>` and
/// rewrites it to `br label <merge_label>` instead, returning that
/// block's own label alongside the rewritten list -- the terminal-
/// block-rewriting half of `splice_into_terminal_block` (which only
/// ever REPLACES that `ret` with more instructions plus a new `ret`,
/// never with a plain `br`), needed by `build_match_case_block` below.
#[partial]
def retarget_terminal_ret (blocks : List LLVMBasicBlock) (target_val : LLVMValue) (merge_label : String) : Option RetargetResult :=
    match blocks {
        List.empty => Option.none,
        List.cons b rest =>
            match b {
                LLVMBasicBlock.mk label instrs =>
                    if block_ends_with_ret_of instrs target_val
                    then
                        let without_ret := drop_last_instr instrs in
                        let new_instrs := List.append without_ret (List.cons (LLVMInstruction.jump merge_label) List.empty) in
                        // Annotated local, never an inline literal in
                        // constructor-argument position -- see
                        // `load_module_with_info` (lang/module.mo) for
                        // the SIGSEGV this exact shape produced through
                        // this backend, and AGENTS.md's "known pitfall".
                        let retargeted : RetargetResult := { blocks := List.cons (LLVMBasicBlock.mk label new_instrs) rest, label := label } in
                        Option.some retargeted
                    else
                        match retarget_terminal_ret rest target_val merge_label {
                            Option.some result =>
                                let bubbled : RetargetResult := { blocks := List.cons b result.blocks, label := result.label } in
                                Option.some bubbled,
                            Option.none => Option.none,
                        },
            },
    }

/// Compiles a single case's body (after binding its fields) into its own
/// block. If the body's own instructions already end in a terminator
/// (e.g. the body is itself a nested if/match, or a general call whose
/// own args needed one, as `resolve_class_method`'s `Option.some ins =>
/// resolve_class_method_d4 ins.cls ...` does), that DOESN'T mean this
/// case never reaches the match's own merge block -- it means the
/// body's own deepest nested block currently `ret`s `bmr.val` directly
/// (correct only when THIS match is the enclosing function's own final
/// answer, exactly `compose_seq`'s own documented convention one level
/// up) and must be RETARGETED to `br label merge_label` instead, via
/// `retarget_terminal_ret`. An earlier version of this function instead
/// contributed NO phi entry at all whenever a case body was already
/// terminated, on the theory that it "never actually reaches the
/// match's merge block" -- confirmed wrong live via the full `lang/
/// main.mo` self-compile: malformed PHI nodes at `llc`'s own IR-
/// verification stage (a case whose value silently never reached the
/// merge, the same "wrong, early answer" failure mode `compose_seq`'s
/// own doc comment describes for a different call site, here never
/// migrated at all since this shape long predates `compose_seq`).
#[partial]
def build_match_case_block (c : CodegenCtx) (scrutinee_val : LLVMValue) (case_ : MatchCase) (case_label : String) (merge_label : String) : MatchChainResult :=
    match case_ {
        MatchCase.mc _name args body _fp =>
            match bind_match_fields c scrutinee_val args 0 {
                { ctx := c1, instrs := field_instrs } =>
                    match compile_db_term_ir c1 body {
                        CompileResult.ok ctx_r instrs_r val_r_raw blocks_r funcs_r globals_r =>
                            let raw_instrs := List.append field_instrs instrs_r in
                            let already_terminated := ends_with_terminator raw_instrs in
                            let bmr_raw := materialize_branch_val ctx_r body raw_instrs val_r_raw in
                            // Pop this arm's own pattern bindings before
                            // handing the ctx to the NEXT arm: `bind_
                            // match_fields` pushed one local per pattern
                            // variable, and `ctx_restore_locals` puts
                            // `c`'s own locals back while keeping the
                            // arm's updated fresh-name counters (exactly
                            // what it already does for a lifted lambda's
                            // body -- see its own doc comment). Without
                            // this, a later arm that references a name
                            // an EARLIER arm happened to bind (a field
                            // access like `result.label` binds `label`,
                            // colliding with the enclosing def's own
                            // `label` parameter) resolves to the earlier
                            // arm's temp instead of its own -- and that
                            // temp is defined in a block this arm isn't
                            // dominated by, so `llc` rejects the whole
                            // module ("Instruction does not dominate all
                            // uses!"). Confirmed live: this was the
                            // `lang/main.mo` self-compile's own failure
                            // in `resolve_branch_merge_info`, whose
                            // `Option.none` arm built its result from
                            // the `Option.some` arm's `result.label`/
                            // `result.blocks` temps rather than its own
                            // `label`/`blocks` parameters.
                            let bmr := { bmr_raw with ctx := ctx_restore_locals c bmr_raw.ctx } in
                            let case_block := build_branch_block case_label merge_label bmr.instrs in
                            if already_terminated
                            then
                                match retarget_terminal_ret blocks_r bmr.val merge_label {
                                    Option.some result =>
                                        { ctx := bmr.ctx, blocks := List.cons case_block result.blocks, funcs := funcs_r, globals := globals_r, phis := List.cons (PhiPair.mk bmr.val result.label) List.empty },
                                    // Shouldn't happen -- `splice_into_
                                    // terminal_block`'s own invariant
                                    // (a branching term's last block is
                                    // always closed with `ret <its own
                                    // val>`) applies here too. Fall back
                                    // to the prior (no-phi) behavior
                                    // rather than crash if it's ever
                                    // violated by something not yet
                                    // accounted for.
                                    Option.none =>
                                        { ctx := bmr.ctx, blocks := List.cons case_block blocks_r, funcs := funcs_r, globals := globals_r, phis := List.empty },
                                }
                            else
                                { ctx := bmr.ctx, blocks := List.cons case_block blocks_r, funcs := funcs_r, globals := globals_r, phis := List.cons (PhiPair.mk bmr.val case_label) List.empty },
                    },
            },
    }

/// `blocks`/`funcs`/`globals` used to be silently DISCARDED entirely
/// by `compile_ntv_args` (every caller received only `ctx`/`instrs`/
/// `vals`) -- meaning any native-call or constructor argument that
/// itself compiled to extra blocks (an `if`/`match`) lost them
/// completely: whatever `br`/`jump` targets its own entry `instrs`
/// referenced would be undefined in the final module. Now threaded
/// through properly, same as every other multi-arg accumulator in this
/// file.
///
/// `last_val` (the LAST arg's own compiled value, i.e. `compile_ntv_
/// args_go`'s own running `acc_val` after the final arg) was ALSO
/// silently discarded until now -- needed by callers (`compile_con_ir`/
/// `compile_ntv_ir`) to use `compose_seq` themselves when combining
/// THESE args' own `instrs`/`blocks` with the wrap-up code that
/// actually builds the call/constructor, exactly the same "prior_val"
/// requirement `wrap_io_value_native_result_go` already documents.
/// Without it, a constructor/native call whose LAST argument was itself
/// branching (an `if`/`match`) had its OWN alloc/set-field/call
/// instructions appended as dead code after that argument's own branch
/// instead of spliced into its merge block -- confirmed live via the
/// full `lang/main.mo` self-compile as malformed PHI nodes at `llc`'s
/// own IR-verification stage (`lang/typecheck/meta_reflect.mo`'s
/// `reify_e_bool`: `Term.var sentinel (DebugName.named (Identifier.id
/// (if b then "true" else "false")))` -- `Identifier.id`'s own `alloc_
/// constructor`/`monad_set_field` calls landed after the `if`'s branch,
/// unreachable, while the `if`'s own merge block's placeholder `ret`
/// became the constructor's wrong, early "value").
struct NtvArgs {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
    vals : List LLVMValue,
    blocks : List LLVMBasicBlock,
    funcs : List LLVMFunction,
    globals : List LLVMGlobal,
    last_val : LLVMValue,
}

/// Sequences each arg's own compiled fragment via `compose_seq_acc`
/// (see its own extended doc comment) instead
/// of blindly concatenating `instrs` -- a branching argument (an
/// `if`/`match` passed to a native call or constructor) used to have
/// every FOLLOWING arg's instructions silently become unreachable dead
/// code after its own branch, the exact same class of bug this whole
/// fix addresses everywhere else.
/// `acc_val` is the running "last-known value" `compose_seq` needs to
/// find the right terminal block to splice into on the NEXT arg, if
/// `acc_instrs` ends in a terminator because THIS arg turned out to be
/// branching -- irrelevant (never consulted) whenever `acc_instrs`
/// doesn't end in a terminator, i.e. `LLVMValue.void_val` is a safe
/// placeholder for the first call.
#[partial]
def compile_ntv_args_go (c : CodegenCtx) (args : List (Option Term)) (acc_instrs : List LLVMInstruction) (acc_blocks : List LLVMBasicBlock) (acc_funcs : List LLVMFunction) (acc_globals : List LLVMGlobal) (acc_vals : List LLVMValue) (acc_val : LLVMValue) : NtvArgs :=
    match args {
        List.cons opt_ rest =>
            match opt_ {
                Option.some term_ =>
                    match compile_db_term_ir c term_ {
                        CompileResult.ok ctx_t instrs val_raw blocks_t funcs_t globals_t =>
                            // See `materialize_void`'s own doc comment
                            // -- a native-call argument can't legally
                            // be `void` either.
                            match materialize_void ctx_t val_raw {
                                { ctx := ctx_tm, instrs := void_instrs, val := val_v } =>
                                    match materialize_native_bool_arg ctx_tm term_ val_v {
                                        { ctx := ctx_tb, instrs := bool_instrs, val := val } =>
                                            let instrs_m := List.append instrs (List.append void_instrs bool_instrs) in
                                            // `compose_seq_acc`, not `compose_seq`: a PURE arg
                                            // (literal/bare reference -- `triple_is_pure`)
                                            // must leave the accumulator untouched so
                                            // `acc_val` keeps identifying the block
                                            // execution is actually in (its own value
                                            // still reaches `acc_vals` below regardless).
                                            match compose_seq_acc ({ instrs := acc_instrs, blocks := acc_blocks, val := acc_val }) ({ instrs := instrs_m, blocks := blocks_t, val := val }) {
                                                { instrs := new_instrs, blocks := new_blocks, val := new_val } =>
                                                    compile_ntv_args_go ctx_tb rest
                                                        new_instrs new_blocks
                                                        (List.append acc_funcs funcs_t)
                                                        (List.append acc_globals globals_t)
                                                        (List.cons val acc_vals)
                                                        new_val,
                                            },
                                    },
                            },
                    },
                Option.none =>
                    compile_ntv_args_go c rest acc_instrs acc_blocks acc_funcs acc_globals acc_vals acc_val,
            },
        List.empty =>
            { ctx := c, instrs := acc_instrs, vals := rev_vals acc_vals List.empty, blocks := acc_blocks, funcs := acc_funcs, globals := acc_globals, last_val := acc_val },
    }

#[partial]
def compile_ntv_args (c : CodegenCtx) (args : List (Option Term)) (acc_instrs : List LLVMInstruction) (acc_vals : List LLVMValue) : NtvArgs :=
    compile_ntv_args_go c args acc_instrs List.empty List.empty List.empty acc_vals LLVMValue.void_val

struct MaterializedVal {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
    val : LLVMValue,
}

/// Substitutes a genuine heap-allocated Unit value for `LLVMValue.void_val`
/// wherever one is about to be used as a function-call ARGUMENT -- a real
/// call-argument position never accepts LLVM's own `void` type (only a
/// function's own RETURN type may be `void`). Mirrors the identical
/// `void_val -> alloc_constructor 0 List.empty` substitution
/// `compile_db_def_ir_body` already does for the analogous return-value
/// case (below) -- `Term.hole` (do-notation's own implicit trailing
/// `Monad.pure hole`, `desugar_do`, `lang/types.mo`) is the most common
/// source: it compiles to a bare `void_val` placeholder (there's no real
/// value to construct), and that placeholder used to flow straight into
/// `Monad.pure`'s own call argument list unchanged
/// (`compile_spine_args_go`/`compile_ntv_args_go`), producing invalid
/// LLVM (`call i64 @Monad_IO_pure(void void)`, confirmed via a real
/// `bootstrap compile lang/main.mo monad` failure) whenever a do-block's
/// LAST statement was a bare expression (not `return`/`let`) -- e.g.
/// `if verbose then do { ...; println (...) } else return unit` as its
/// own do-block's final statement, exactly the shape
/// `compile_loaded_modules_to_ir` (above) uses pervasively.
///
/// Safe to unconditionally append `mv_instrs` straight after whatever
/// instructions produced `v` (no `compose_seq`-style terminator-splicing
/// needed): every real call site that produces `LLVMValue.void_val`
/// (`Literal.struct_lit`/`struct_update`, `DebugName.unnamed`,
/// `Term.forall`/`Term.pi`/`Term.type_`/`Term.hole`) pairs it with
/// `List.empty` -- there's never a pending terminator to splice around
/// when `v` is actually `void_val`.
#[partial]
def materialize_void (c : CodegenCtx) (v : LLVMValue) : MaterializedVal := match v {
    LLVMValue.void_val =>
        match fresh_temp c {
            CtxStrPair.mk ctx1 temp =>
                let unit_val := LLVMValue.alloc_constructor 0 List.empty in
                let assign := LLVMInstruction.assign temp unit_val in
                { ctx := ctx1, instrs := (List.cons assign List.empty), val := (LLVMValue.var_ temp) },
        },
    _ => { ctx := c, instrs := List.empty, val := v },
}

/// A native boolean-comparison term (`I64.lt`/`.gt`/`.eq`/`.ne`, whatever
/// `term_is_native_bool_op` recognizes) compiles, via `emit_arith_instr`,
/// to a raw `icmp`-produced `i1` materialized into a `var_` temp --
/// deliberately left UNBOXED there so `ensure_i1_cond`'s "is this
/// condition already a genuine i1" fast path (keyed off this SAME
/// `term_is_native_bool_op` check on the SOURCE TERM, not the compiled
/// value -- this backend tracks no real per-register type, `llvm_value_
/// type (var_ x)` is hardcoded `i64_` regardless of what the register
/// actually holds) can use it directly as a branch condition with no
/// unboxing round-trip. That's correct for an `if`'s own condition, but
/// wrong the moment the SAME comparison is used as an ORDINARY VALUE --
/// a function-call argument, a constructor field, ... -- nothing
/// downstream can tell "this `var_` is secretly `i1`" apart from a
/// genuine `i64`, so the raw i1 register ends up passed to a callee
/// call verbatim, declared `i64` in the call's own text. Confirmed as a
/// real gap via `bootstrap compile lang/main.mo monad`'s own self-compile
/// (`lang/parser/diagnostic.mo`'s `line_end_after_go`, `not (a < b)`):
/// `call i64 @Bool_not(i64 %tN)` where `%tN` was actually declared `i1`
/// -- `llc: '%tN' defined with type 'i1' but expected 'i64'`.
///
/// Fixed by boxing into a genuine heap-allocated, tagged Bool object
/// whenever the ARGUMENT TERM (not the compiled value -- same
/// term-shape-based approach `ensure_i1_cond` already relies on) is a
/// native comparison: `zext` the raw `i1` to `i64` first (arithmetic on
/// it, like `NativeWrapKind.bool_result`'s existing `2 - raw` mapping
/// below, needs a real i64 operand -- `show_arith`'s `sub` rendering
/// hardcodes `i64` for both operands, and a genuinely `i1`-declared
/// register there would repeat this exact same mismatch one level down),
/// then map 1/0 -> Bool.true/false's own tags (1/2) the same way.
#[partial]
def materialize_native_bool_arg (c : CodegenCtx) (t : Term) (v : LLVMValue) : MaterializedVal :=
    if term_is_native_bool_op t
    then
        match fresh_temp c {
            CtxStrPair.mk ctx1 zext_temp =>
                match fresh_temp ctx1 {
                    CtxStrPair.mk ctx2 tag_temp =>
                        match fresh_temp ctx2 {
                            CtxStrPair.mk ctx3 con_temp =>
                                let zext_instr := LLVMInstruction.assign zext_temp (LLVMValue.zext v LLVMType.i1_ LLVMType.i64_) in
                                let tag_val := LLVMValue.sub (LLVMValue.int_ 2) (LLVMValue.var_ zext_temp) in
                                let tag_instr := LLVMInstruction.assign tag_temp tag_val in
                                let con_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (List.cons (LLVMValue.var_ tag_temp) (List.cons (LLVMValue.int_ 0) List.empty)) false in
                                let con_instr := LLVMInstruction.assign con_temp con_val in
                                { ctx := ctx3, instrs := (List.cons zext_instr (List.cons tag_instr (List.cons con_instr List.empty))), val := (LLVMValue.var_ con_temp) },
                        },
                },
        }
    else { ctx := c, instrs := List.empty, val := v }

struct BranchMaterializeResult {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
    val : LLVMValue,
}

/// A `then`/`else` branch (`build_db_if_blocks`) or `match` case body
/// (`build_match_case_block`) whose value is about to become a `phi`
/// operand needs the SAME materialization call-argument positions
/// already get (`materialize_void`/`materialize_native_bool_arg` above)
/// -- a phi is just as intolerant of a raw `void_val` or a secretly-`i1`
/// native-comparison result as a call argument is, and this codebase's
/// own PhiPair construction (`build_merge_result`/`build_match_case_
/// block`) used `then_val`/`else_val`/`val_r` completely unmaterialized
/// until this fix. Confirmed as a real gap via `bootstrap compile
/// lang/main.mo monad`'s own self-compile (`line_col_scan_direct`,
/// `lang/parser/diagnostic.mo`): an `if`'s `then` branch compiling to a
/// bare `void_val` (a `Term.hole`-shaped body) merged against the `else`
/// branch's real `i64` result -- `llc: void type only allowed for
/// function results`, the exact same class of error the string-literal-
/// vs-computed-string phi fix addressed, just for `void` instead of a
/// pointer.
///
/// Skips materialization entirely when `raw_instrs` already ends in a
/// terminator (the branch is itself a nested if/match that returns
/// directly and never reaches the enclosing merge block at all --
/// `build_match_case_block`'s own prior doc comment already documents
/// this shape for match arms; the same reasoning applies to `if`
/// branches) -- `raw_val` is irrelevant there (no phi entry is
/// contributed for it either way), and appending instructions after an
/// already-real terminator would itself be the "dead code after
/// terminator" bug class this file's `compose_seq` exists to avoid
/// elsewhere.
#[partial]
def materialize_branch_val (c : CodegenCtx) (term_ : Term) (raw_instrs : List LLVMInstruction) (raw_val : LLVMValue) : BranchMaterializeResult :=
    if ends_with_terminator raw_instrs
    then { ctx := c, instrs := raw_instrs, val := raw_val }
    else
        match materialize_void c raw_val {
            { ctx := c1, instrs := void_instrs, val := val_v } =>
                match materialize_native_bool_arg c1 term_ val_v {
                    { ctx := c2, instrs := bool_instrs, val := val } =>
                        { ctx := c2, instrs := List.append raw_instrs (List.append void_instrs bool_instrs), val := val },
                },
        }

#[partial]
def compile_ntv_ir (c : CodegenCtx) (native : Native) : CompileResult :=
    match native {
        Native.mk name num_args args =>
            let name_str := symbol_identifier name in
            let llvm_name := extract_base_name name_str in
            let fn_name := String.concat "monad_" llvm_name in
            match compile_ntv_args c args List.empty List.empty {
                { ctx := ctx_args, instrs := all_instrs, vals := all_vals, blocks := all_blocks, funcs := all_funcs, globals := all_globals, last_val := args_last_val } =>
                    match fresh_temp ctx_args {
                        CtxStrPair.mk ctx_t temp =>
                            let call_val := LLVMValue.call fn_name LLVMType.i64_ all_vals false in
                            let assign_instr := LLVMInstruction.assign temp call_val in
                            // Args' own instrs must run BEFORE the call
                            // that consumes their values, not after --
                            // `List.cons assign_instr all_instrs`
                            // (prepending) used to put the call FIRST,
                            // silently using not-yet-computed argument
                            // registers whenever an arg actually needed
                            // real instructions to compute (anything
                            // beyond a bare literal/local-var reference
                            // -- confirmed as the source of the
                            // `call i64 @monad_print_str(void void)`
                            // corruption seen while chasing the
                            // separate let/if-argument bug this file's
                            // `compose_seq` now also fixes).
                            //
                            // `compose_seq` (not a blind append) -- see
                            // `NtvArgs.last_val`'s own doc comment: if
                            // the LAST arg was itself branching,
                            // `all_instrs` already ends in a real
                            // terminator, and this call's own assign
                            // instr must be spliced into that arg's own
                            // merge block, not appended after its branch.
                            match compose_seq ({ instrs := all_instrs, blocks := all_blocks, val := args_last_val }) ({ instrs := (List.cons assign_instr List.empty), blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                                { instrs := final_instrs, blocks := final_blocks, val := final_val } =>
                                    CompileResult.ok ctx_t final_instrs final_val final_blocks all_funcs all_globals,
                            },
                    },
            },
    }

#[partial]
def compile_con_ir (c : CodegenCtx) (con : Con) : CompileResult :=
    match con {
        Con.mk name typ_name num_args args =>
            match compile_ntv_args c args List.empty List.empty {
                { ctx := ctx_args, instrs := all_instrs, vals := all_vals, blocks := all_blocks, funcs := all_funcs, globals := all_globals, last_val := args_last_val } =>
                    match fresh_temp ctx_args {
                        CtxStrPair.mk ctx_t temp =>
                            // Call the @alloc_constructor runtime function
                            // alloc_constructor takes (tag, field_count) and allocates space for fields
                            // The tag is determined by the constructor name AND this
                            // application's own compiled-arg count -- the composite
                            // key that keeps same-named constructors of different
                            // types distinguishable at match dispatch (see
                            // `constructor_tag_at`).
                            let tag_val := constructor_tag_at c (symbol_identifier name) (List.length all_vals) in
                            let alloc_val := LLVMValue.alloc_constructor tag_val all_vals in
                            let assign_instr := LLVMInstruction.assign temp alloc_val in
                            // alloc_constructor only ALLOCATES the fields
                            // array -- it has no way to accept field
                            // values itself, so every argument needs its
                            // own @monad_set_field call to actually write
                            // it into the object (previously missing
                            // entirely: any constructor with 1+ arguments,
                            // e.g. `some 42`, allocated a correctly
                            // tagged/sized-but-uninitialized object).
                            match build_set_field_instrs (LLVMValue.var_ temp) all_vals 0 ctx_t {
                                { ctx := ctx_set, instrs := set_instrs } =>
                                    // `compose_seq` (not a blind append) --
                                    // see `NtvArgs.last_val`'s own doc
                                    // comment: if the LAST arg was itself
                                    // branching, `all_instrs` already ends
                                    // in a real terminator, and this
                                    // constructor's own alloc/set-field
                                    // instrs must be spliced into that
                                    // arg's own merge block, not appended
                                    // after its branch.
                                    match compose_seq ({ instrs := all_instrs, blocks := all_blocks, val := args_last_val }) ({ instrs := (List.cons assign_instr set_instrs), blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                                        { instrs := final_instrs, blocks := final_blocks, val := final_val } =>
                                            CompileResult.ok ctx_set final_instrs final_val final_blocks all_funcs all_globals,
                                    },
                            },
                    },
            },
    }

struct SetFieldResult {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
}

/// One @monad_set_field call per already-compiled argument value, in
/// order -- the write half of constructor field storage (monad_get_field
/// is the read half, used by match dispatch).
#[partial]
def build_set_field_instrs (obj_val : LLVMValue) (vals : List LLVMValue) (idx : I64) (c : CodegenCtx) : SetFieldResult :=
    match vals {
        List.empty => { ctx := c, instrs := List.empty },
        List.cons v rest =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 temp =>
                    let set_call := LLVMValue.call "monad_set_field" LLVMType.i64_ (List.cons obj_val (List.cons (LLVMValue.int_ idx) (List.cons v List.empty))) false in
                    let set_instr := LLVMInstruction.assign temp set_call in
                    match build_set_field_instrs obj_val rest (idx + 1) ctx1 {
                        { ctx := ctx2, instrs := rest_instrs } =>
                            { ctx := ctx2, instrs := (List.cons set_instr rest_instrs) },
                    },
            },
    }

struct IfLabels {
    ctx_after : CodegenCtx,
    then_label : String,
    else_label : String,
    merge_label : String,
}

#[partial]
def build_if_labels (c : CodegenCtx) : IfLabels :=
    match fresh_label c "then" {
        CtxStrPair.mk ctx1 tl =>
            match fresh_label ctx1 "else" {
                CtxStrPair.mk ctx2 el =>
                    match fresh_label ctx2 "merge" {
                        CtxStrPair.mk ctx3 ml =>
                            { ctx_after := ctx3, then_label := tl, else_label := el, merge_label := ml }
                    },
            },
    }

#[partial]
def build_branch_block (label : String) (merge_label : String) (instrs : List LLVMInstruction) : LLVMBasicBlock :=
    if ends_with_terminator instrs
    then LLVMBasicBlock.mk label instrs
    else LLVMBasicBlock.mk label (List.append instrs (List.cons (LLVMInstruction.jump merge_label) List.empty))

#[partial]
def ends_with_terminator (instrs : List LLVMInstruction) : Bool := match instrs {
    List.empty => false,
    List.cons hd tl => match tl {
        List.empty => is_terminator_instr hd,
        List.cons x y => ends_with_terminator tl,
    },
}

#[partial]
def is_terminator_instr (instr : LLVMInstruction) : Bool := match instr {
    LLVMInstruction.branch a b c => true,
    LLVMInstruction.jump a => true,
    LLVMInstruction.ret a => true,
    LLVMInstruction.assign a b => false,
    LLVMInstruction.store _a _pty _b => false,
    LLVMInstruction.comment a => false,
    // NOT a terminator. Also why a marker must never sit last in a list:
    // `ends_with_terminator` reads only the final element.
    LLVMInstruction.loc_marker _loc => false,
}

// ─── Safe sequential composition (fixes a real "dropped continuation"
// codegen bug) ──────────────────────────────────────────────────────
//
// Every "combine a sub-expression's compiled result into a bigger
// context" call site in this file used to just concatenate the two
// instruction lists directly (`List.append a_instrs b_instrs`),
// assuming `a_instrs` was always safe to keep appending to. That's
// true for an ordinary computation (arithmetic, a call, a constructor
// alloc) but WRONG whenever `a` is itself an `if`/`match`: its own
// returned `instrs` field ends in a real branch (the condition-check
// `br`), and its actual VALUE lives in a `merge`/case block sitting in
// `blocks`, closed with its own `ret <val>` — a convention that's only
// correct when that `if`/`match` IS the enclosing function's own final
// answer (compile_db_def_ir's own doc comment already documents relying
// on exactly this). Appending `b_instrs` straight after `a_instrs` puts
// it AFTER that branch — unreachable, dead code — while the merge
// block's own `ret <val>` becomes the function's REAL, wrong, early
// answer, silently skipping `b_instrs` entirely.
//
// Confirmed via a minimal repro (not specific to any one call site
// above): `let x := (if true then 1 else 2) in helper x` used to
// compile AND RUN successfully, but returned 1, not `helper(1) = 2` —
// `helper` was never actually called. (`let x := v in body` desugars
// to `(fn x => body) v`, so this hits exactly the "argument is a
// branching sub-expression" combine sites below.)
//
// `compose_seq a b` is the fix: sequences `b` after `a`, correctly
// splicing `b` into `a`'s own merge/case block (identified by searching
// `a`'s own `blocks` for the one ending in `ret <a's val>`) instead of
// blindly appending, whenever `a`'s own `instrs` already ends in a
// terminator. Recursively correct even for a "branching sub-expression
// feeding into ANOTHER branching sub-expression" chain (`b` itself
// ending in a terminator too) — see `splice_into_terminal_block`'s own
// doc comment for how. Degrades to the original plain-concatenation
// behavior whenever `a` isn't itself branching, i.e. the overwhelming
// majority of real code — this changes nothing about ordinary,
// non-branching compilation.
struct Triple {
    instrs : List LLVMInstruction,
    blocks : List LLVMBasicBlock,
    val : LLVMValue,
}

#[partial]
def compose_seq (a : Triple) (b : Triple) : Triple := match a {
    { instrs := a_instrs, blocks := a_blocks, val := a_val } => match b {
        { instrs := b_instrs, blocks := b_blocks, val := b_val } =>
            if ends_with_terminator a_instrs then
                match splice_into_terminal_block a_blocks a_val b_instrs b_val {
                    Option.some rewritten =>
                        { instrs := a_instrs, blocks := append_blocks rewritten b_blocks, val := b_val }
                    // Couldn't find a's own terminal block (shouldn't
                    // happen given compile_db_if_ir/compile_match_ir's
                    // own invariant that a branching term's LAST
                    // appended block is always closed with `ret <its
                    // own reported val>` — but stay total/safe rather
                    // than crash if that invariant is ever violated by
                    // something not yet accounted for here).
                    Option.none =>
                        { instrs := List.append a_instrs b_instrs, blocks := append_blocks a_blocks b_blocks, val := b_val }
                }
            else
                { instrs := List.append a_instrs b_instrs, blocks := append_blocks a_blocks b_blocks, val := b_val }
    },
}

/// True when a compiled fragment contributes NO code at all -- no
/// instructions and no blocks: a literal, a bare parameter/global/
/// function reference, or a const-folded native op. Such a fragment
/// moves execution nowhere, so at ACCUMULATION call sites (argument
/// lists, native operands -- `compose_seq_acc` below) it must not
/// perturb the running splice-target token; see `compose_seq_acc`'s
/// own doc comment for the corruption composing it anyway causes.
#[partial]
def triple_is_pure (t : Triple) : Bool := match t {
    { instrs := i_s, blocks := b_s, val := _v_s } => match i_s {
        List.empty => match b_s {
            List.empty => true,
            List.cons _ _ => false,
        },
        List.cons _ _ => false,
    },
}

/// `compose_seq` for ACCUMULATION call sites -- argument lists
/// (`compile_ntv_args_go`/`compile_spine_args_go`), native operands
/// (`compile_native_app_db`), callee-with-spine
/// (`compile_general_db_call`) -- where `b`'s own value is NOT the
/// expression's semantic result, only a token threaded onward as the
/// NEXT compose step's splice-target identifier. A pure `b` (see
/// `triple_is_pure`) contributes no code and moves execution nowhere,
/// so here it must be a complete NO-OP returning `a` UNCHANGED
/// (`a.val` still identifies the block execution is actually in).
/// Plain `compose_seq` would instead splice into `a`'s terminal block
/// and rewrite its `ret <a.val>` to `ret <b.val>` -- destroying the
/// previous argument's computed value (its phi) AND, whenever `b.val`
/// is a literal, leaving a token `llvm_value_eq` deliberately never
/// matches (see its own doc comment), so every FOLLOWING compose
/// step degrades into dead code flat-appended after the branch while
/// the corrupted `ret <literal>` silently stays the function's real
/// early return. Exact mechanism behind `{ x with f := x.f + 1 }`
/// miscompiling to `ret i64 1` (the literal `1` operand of the `+`,
/// following the projected-field match) and v29's
/// `module_info_cache_insert`/`module_info_cache_hit` SIGSEGVs.
/// NOT a drop-in replacement everywhere: where `b`'s value IS the
/// expression's own result (a let's body in
/// `try_compile_let_beta_db`, a def body), the pure-`b` ret rewrite
/// is load-bearing -- those callers keep plain `compose_seq`.
#[partial]
def compose_seq_acc (a : Triple) (b : Triple) : Triple :=
    if triple_is_pure b then a else compose_seq a b

/// Finds the block among `blocks` that ends in `ret <target_val>`
/// (structurally — same SSA temp/global name, `llvm_value_eq`) and
/// rewrites it in place (preserving its own label, so every existing
/// `br`/`jump` INTO that block from elsewhere still resolves): drops
/// its own trailing `ret`, appends `extra_instrs`, then re-closes with
/// a fresh `ret <extra_val>` — UNLESS `extra_instrs` itself already
/// ends in a terminator (it's itself a branching sub-expression), in
/// which case nothing more is appended: `extra_instrs`'s own nested
/// structure already closes correctly with `ret <extra_val>` somewhere
/// inside its own blocks (which `compose_seq` appends alongside), and
/// adding another `ret` here would just make THAT unreachable too —
/// this is what makes chained/nested branching sub-expressions compose
/// correctly, not just a single level.
#[partial]
def splice_into_terminal_block (blocks : List LLVMBasicBlock) (target_val : LLVMValue) (extra_instrs : List LLVMInstruction) (extra_val : LLVMValue) : Option (List LLVMBasicBlock) := match blocks {
    List.empty => Option.none,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk label instrs =>
                if block_ends_with_ret_of instrs target_val then
                    let without_ret := drop_last_instr instrs in
                    let merged := List.append without_ret extra_instrs in
                    let new_instrs :=
                        if ends_with_terminator extra_instrs
                        then merged
                        else List.append merged (List.cons (LLVMInstruction.ret extra_val) List.empty) in
                    Option.some (List.cons (LLVMBasicBlock.mk label new_instrs) rest)
                else
                    match splice_into_terminal_block rest target_val extra_instrs extra_val {
                        Option.some rewritten => Option.some (List.cons b rewritten),
                        Option.none => Option.none,
                    },
        },
}

#[partial]
def block_ends_with_ret_of (instrs : List LLVMInstruction) (target_val : LLVMValue) : Bool := match instrs {
    List.empty => false,
    List.cons i rest => match rest {
        List.empty => instr_is_ret_of i target_val,
        List.cons _ _ => block_ends_with_ret_of rest target_val,
    },
}

#[partial]
def instr_is_ret_of (i : LLVMInstruction) (target_val : LLVMValue) : Bool := match i {
    LLVMInstruction.ret v => llvm_value_eq v target_val,
    LLVMInstruction.branch a b c => false,
    LLVMInstruction.jump a => false,
    LLVMInstruction.assign a b => false,
    LLVMInstruction.store _a _pty _b => false,
    LLVMInstruction.comment a => false,
    LLVMInstruction.loc_marker _loc => false,
}

/// Structural equality over every ATOMIC `LLVMValue` variant that
/// uniquely, unambiguously identifies ONE logical value within a single
/// function's compilation -- these are the variants that can plausibly
/// appear as a `Triple.val`/"running composed result" threaded through
/// `compose_seq`'s repeated splice-target search
/// (`splice_into_terminal_block`/`retarget_terminal_ret`). NOT just
/// `var_` (a branching sub-expression's own fresh SSA phi/call temp,
/// `compile_db_if_ir`/`build_merge_result`'s own `fresh_temp`-allocated
/// result). A bare, unrebound function-parameter reference compiles to
/// `LLVMValue.parm_`, not `var_` -- confirmed as a real gap via a minimal
/// standalone repro isomorphic to `build_db_if_blocks`'s own call to
/// `build_merge_result` (a chained dot-access match immediately followed
/// by a bare parameter, immediately followed by more dot-access matches,
/// all as sibling call arguments): once a `parm_` value got spliced into
/// a block's `ret` as the running composed value, the NEXT `compose_seq`
/// step's search for that exact `parm_` value always returned `false`
/// (old code's wildcard `_ => false` for any non-`var_` pair, even two
/// structurally-identical ones), so `splice_into_terminal_block` could
/// never find that block again -- silently falling back to flat
/// concatenation instead of splicing, corrupting every subsequent
/// argument's control flow into unreachable, unlabeled dead code and
/// leaving the earlier block permanently `ret`ing the stale value instead
/// of its real continuation. `global_`/`fn_ref` are the same shape
/// (`idx`/`name` uniquely picks out one specific parameter/global/
/// function within this compilation) so get the same treatment.
///
/// Deliberately NOT extended to `int_`/`int32_`/`bool_`/`void_val`: a
/// bare literal is NOT a unique identifier the way a parameter index or
/// global/function name is -- two UNRELATED branches within the same
/// accumulated `blocks` list can each legitimately `ret` the identical
/// literal (e.g. two different arms both happening to return `0`, or two
/// different Unit-typed computations both `ret`ing `void_val`) without
/// being "the same running composed value" `compose_seq` is trying to
/// splice into. Treating those as equal would make `splice_into_terminal_
/// block` match the WRONG (coincidentally-identical-valued but logically
/// unrelated) block, so those four variants were dropped from an earlier,
/// broader version of this function on principle -- NOT because doing so
/// was confirmed to fix a live bug (a runtime crash surfaced once the
/// self-compile got far enough to actually RUN the resulting binary --
/// `strlen` segfaulting on a garbage `String` -- persisted identically
/// with or without the literal cases, so it has a different, not yet
/// root-caused source; still worth keeping this function narrow to its
/// PROVEN-necessary variants regardless). Every compound/expression
/// variant (`call`,
/// `add`, `icmp_eq`, `phi`, ...) still falls through to `false` via the
/// wildcard -- none of those should ever legitimately appear as a splice
/// target either (a `Triple.val` is always some atomic identifier, never
/// a live unassigned expression).
#[partial]
def llvm_value_eq (a : LLVMValue) (b : LLVMValue) : Bool := match a {
    LLVMValue.var_ na => match b {
        LLVMValue.var_ nb => String.beq na nb,
        _ => false,
    },
    LLVMValue.parm_ ia => match b {
        LLVMValue.parm_ ib => I64.beq ia ib,
        _ => false,
    },
    LLVMValue.global_ na => match b {
        LLVMValue.global_ nb => String.beq na nb,
        _ => false,
    },
    LLVMValue.fn_ref na => match b {
        LLVMValue.fn_ref nb => String.beq na nb,
        _ => false,
    },
    _ => false,
}

// ─── Free-variable computation for closure capture ─────────────────────
//
// A lifted lambda (`compile_db_lam_ir`, below) is compiled into a
// brand-new, independent top-level LLVM function -- so any name its
// body references that isn't its own parameter must be explicitly
// CAPTURED (read out of its own closure instance's env array at
// runtime, see `monad_closure_get_env`/`monad_closure_set_env`,
// `lang/codegen/runtime.c`) rather than referenced directly, which
// would produce a dangling cross-function SSA reference (`llc: use of
// undefined value`) the moment it referred to anything bound in the
// ENCLOSING function. `free_names_of_term` computes exactly the set of
// names a `Term` references that are NOT bound somewhere inside that
// same `Term` (i.e. its free variables), given the names already bound
// by the ENCLOSING scope at the point this `Term` appears (`bound`,
// threaded through and grown at each binder). Name-based throughout
// (matches `ctx_lookup_local`'s own name-based, not de-Bruijn-index-
// based, scoping convention -- `compile_db_term_ir`'s `Term.var` case
// never consults `idx` at all).
//
// Deliberately a separate, shadow-AWARE family from
// `collect_referenced_names` (below, in the reachability-analysis
// section) -- that one collects EVERY name a `Term` references,
// including ones that are actually locally bound (e.g. a lambda's own
// parameter, or an inner match arm's own binder), which is exactly
// right for its own purpose (a conservative reachability
// over-approximation) but wrong here: capturing a name that's actually
// bound INSIDE the lambda's own body, not free at all, would shadow the
// real (inner) binding with a stale captured value.
/// Intersects a raw free-name list against the CURRENT `CodegenCtx`'s
/// actual locals -- only names that resolve to a real LOCAL binding
/// here are genuine capture candidates. A name that's free in the body
/// but resolves to `Option.none` here is a global/constructor/def
/// reference, correctly excluded (left to the existing global-lookup
/// path inside the lifted function, unchanged).
#[partial]
def build_capture_list (c : CodegenCtx) (names : List Identifier) : List LocalBinding := match names {
    List.empty => List.empty,
    List.cons n rest =>
        match ctx_lookup_local c n {
            Option.some val =>
                let binding : LocalBinding := LocalBinding.mk n val in
                List.cons binding (build_capture_list c rest),
            Option.none => build_capture_list c rest,
        },
}

#[partial]
def captures_to_vals (captures : List LocalBinding) : List LLVMValue := match captures {
    List.empty => List.empty,
    List.cons cap rest =>
        match cap {
            LocalBinding.mk _cname cval => List.cons cval (captures_to_vals rest),
        },
}

struct GetEnvResult {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
}

/// Binds each captured name, in order, to a fresh
/// `@monad_closure_get_env` call reading from THIS closure instance's
/// own env array (`self = parm_ 0`, the lifted function's own new
/// leading param -- see `compile_db_lam_ir`'s own doc comment) -- the
/// read half mirroring `build_set_env_instrs` below. Order MUST match
/// `build_set_env_instrs`'s/`captures_to_vals`'s own iteration order --
/// both are driven by the SAME `captures` list, built once, so this
/// holds by construction.
#[partial]
def build_get_env_instrs (c : CodegenCtx) (captures : List LocalBinding) (idx : I64) : GetEnvResult := match captures {
    // The trailing comma here is LOAD-BEARING, not style -- without it,
    // this case's body (`{ ctx := c, instrs := List.empty }`) is a
    // struct literal whose last field value is a bare identifier
    // (`List.empty`), and the expression parser's application-chain
    // continuation (`expr_climb_rest`, lang/parser.mo) doesn't stop at
    // the newline: it keeps parsing further atoms as more curried args,
    // swallowing the NEXT case's own constructor name and bound pattern
    // names (`List.cons cap rest`) as if they were extra arguments to
    // this case's body. That corrupted the match's own case list with a
    // wrong/empty constructor name -- see `plans/implementations/
    // 2026-08-30-match-case-comma-parser-bug.md` for the full
    // root-cause writeup. `match_case_name`'s own `dotted_identifier`
    // call now fails loudly instead of silently accepting the resulting
    // empty name (see that same doc), but the actual fix here is this
    // comma: never omit the trailing comma after a match case whose body
    // ends in a bare identifier/call (anything that could itself be a
    // curried application head).
    List.empty => { ctx := c, instrs := List.empty },
    List.cons cap rest =>
        match cap {
            LocalBinding.mk cname _cval =>
                match fresh_temp c {
                    CtxStrPair.mk ctx1 temp =>
                        let get_call := LLVMValue.call "monad_closure_get_env" LLVMType.i64_
                            (List.cons (LLVMValue.parm_ 0) (List.cons (LLVMValue.int_ idx) List.empty)) false in
                        let get_instr := LLVMInstruction.assign temp get_call in
                        let ctx2 := ctx_bind_local ctx1 cname (LLVMValue.var_ temp) in
                        match build_get_env_instrs ctx2 rest (idx + 1) {
                            { ctx := ctx3, instrs := rest_instrs } => { ctx := ctx3, instrs := List.cons get_instr rest_instrs },
                        },
                },
        },
}

struct SetEnvResult {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
}

/// One `@monad_closure_set_env` call per captured value, in order --
/// mirrors `build_set_field_instrs` (above) exactly, just against the
/// closure's own distinct env-array layout (`monad_closure_set_env`,
/// `lang/codegen/runtime.c`).
#[partial]
def build_set_env_instrs (obj_val : LLVMValue) (vals : List LLVMValue) (idx : I64) (c : CodegenCtx) : SetEnvResult := match vals {
    // See `build_get_env_instrs`'s own doc comment above -- this trailing
    // comma is load-bearing for the exact same reason (bare-identifier
    // struct-literal field value + no comma corrupts the NEXT case's own
    // constructor name via the expression parser's application-chain
    // continuation).
    List.empty => { ctx := c, instrs := List.empty },
    List.cons v rest =>
        match fresh_temp c {
            CtxStrPair.mk ctx1 temp =>
                let set_call := LLVMValue.call "monad_closure_set_env" LLVMType.i64_
                    (List.cons obj_val (List.cons (LLVMValue.int_ idx) (List.cons v List.empty))) false in
                let set_instr := LLVMInstruction.assign temp set_call in
                match build_set_env_instrs obj_val rest (idx + 1) ctx1 {
                    { ctx := ctx2, instrs := rest_instrs } => { ctx := ctx2, instrs := List.cons set_instr rest_instrs },
                },
        },
}

// This is reached ONLY for a genuinely NESTED `Term.lam` appearing in
// VALUE position -- a top-level def's own OUTER, param-introducing
// lambdas never reach here (`compile_db_def_ir` peels those off first
// via `strip_db_lams`/`collect_db_params`, building the LLVMFunction's
// params directly), and a lambda immediately APPLIED as a beta-redex
// (`(\x -> body) arg`, i.e. a `let`) is special-cased earlier by
// `compile_db_app_ir`, before its head ever reaches the general
// `Term.lam` dispatch here. So every lambda this function lifts is one
// some OTHER call's argument (or a stored/returned value) will apply
// dynamically via `apply_closureN` -- e.g. every do-notation
// continuation passed as `Monad.bind`'s own second argument, whose
// compiled instance body (`match a { io a => f a }`) applies its `f`
// parameter exactly that way. Returning a bare `LLVMValue.fn_ref` (a
// raw code pointer, not a `Closure*`) used to leave that call reading
// `((Closure*)fn_ptr)->entry` off the LIFTED FUNCTION'S OWN machine
// code as if it were a heap-allocated `Closure` struct -- confirmed as
// a real gap via direct repro (a do-block whose bind continuation
// segfaulted inside `apply_closure1`, called with the raw lambda
// symbol instead of a boxed closure). Box it via `alloc_closure`
// instead, mirroring the identical, already-correct fix for a NAMED
// global def referenced as a first-class value (`compile_db_term_ir`'s
// own `Term.var`/arity>0 case, just above).
///
/// **Free-variable capture** (see the `free_names_of_term`/
/// `build_capture_list`/`build_get_env_instrs`/`build_set_env_instrs`
/// family, just above): this lambda's body may reference names bound
/// in its ENCLOSING function's own scope (e.g. an earlier do-notation
/// statement's bound name) -- since the lambda is lifted into a
/// genuinely separate top-level LLVM function, those references can't
/// resolve to the outer function's own registers (`llc` correctly
/// rejects that as `use of undefined value`). Instead: compute the
/// body's free names, capture their CURRENT values into the closure's
/// own env array at allocation time (`monad_closure_set_env`), and
/// prepend `monad_closure_get_env` reads at the top of the lifted
/// function's own body to rebind them locally before compiling `body`
/// for real. The lifted function gains a new leading `self` parameter
/// (`p0`, the closure pointer itself) so it can identify which closure
/// INSTANCE it's running as (`apply_closureN`, `runtime.c`, now
/// uniformly passes it) -- the lambda's own real parameter shifts to
/// `p1`.
/// Compile a located term: record the position, compile the term under it,
/// and PREPEND a marker so every instruction the term produced carries it.
///
/// Prepend, never append. `ends_with_terminator` inspects an instruction
/// list's LAST element and `drop_last_instr` (`lang/codegen/util.mo`) drops
/// it blindly, so a marker sitting at the end of a list would be read as a
/// terminator or silently discarded. Prepending holds that invariant by
/// construction rather than by remembering it.
///
/// `current_loc` is restored to the caller's on the way out: a location is
/// scoped to the term it was written on, and leaking it outward would
/// attribute a sibling's instructions to this term's line.
#[partial]
def compile_located_term_ir (c : CodegenCtx) (loc : Location) (inner : Term) : CompileResult :=
    match compile_db_term_ir { c with current_loc := dbg_loc_of_location loc } inner {
        CompileResult.ok c2 instrs val blocks funcs globals =>
            CompileResult.ok { c2 with current_loc := c.current_loc }
                (prepend_loc_marker loc instrs)
                val blocks funcs globals,
    }

/// A marker is only worth emitting if the term produced instructions to
/// attribute to it -- one before an empty list would end up at the END of
/// whatever list it is spliced into, which is the shape the prepend rule
/// exists to avoid.
#[partial]
def prepend_loc_marker (loc : Location) (instrs : List LLVMInstruction) : List LLVMInstruction :=
    match instrs {
        List.empty => List.empty,
        List.cons _ _ => prepend_loc_marker_go (dbg_loc_of_location loc) instrs,
    }

#[partial]
def prepend_loc_marker_go (d : Option DbgLoc) (instrs : List LLVMInstruction) : List LLVMInstruction :=
    match d {
        Option.some dl => List.cons (LLVMInstruction.loc_marker dl) instrs,
        Option.none => instrs,
    }

#[partial]
def compile_db_lam_ir (c : CodegenCtx) (dbg : DebugName) (typ : Term) (body : Term) : CompileResult :=
    match fresh_label c "lambda" {
        CtxStrPair.mk ctx1 lam_name =>
            let name : Identifier := match dbg {
                named id => id,
                unnamed => Identifier.id "x",
            } in
            // Free vars of body, excluding the lambda's own param;
            // intersected against what's a REAL local at THIS call
            // site (the ENCLOSING function's own ctx, `ctx1`) -- see
            // `free_names_of_term`/`build_capture_list`'s own doc
            // comments.
            let raw_free := dedup_idents (free_names_of_term (List.cons name List.empty) body) in
            let captures := build_capture_list ctx1 raw_free in
            let capture_vals := captures_to_vals captures in

            // Fresh, EMPTY-locals ctx for the lifted function's own
            // body -- must NOT carry the outer function's locals
            // forward (see `ctx_reset_locals`'s own doc comment, the
            // actual fix). `p0` = self (the closure pointer), `p1` =
            // the lambda's own real formal param -- shifted by one
            // from before.
            let ctx_inner0 := ctx_reset_locals ctx1 in
            let ctx_inner1 := ctx_bind_local ctx_inner0 name (LLVMValue.parm_ 1) in
            match build_get_env_instrs ctx_inner1 captures 0 {
                { ctx := ctx_inner2, instrs := get_env_instrs } =>
                    match compile_db_term_ir ctx_inner2 body {
                        CompileResult.ok ctx2_raw instrs_r val_r blocks_r funcs_r globals_r =>
                            // `ctx2_raw`'s own `locals` is still the
                            // lifted function's reset-and-rebuilt list
                            // (only its own param + captures) -- restore
                            // the ENCLOSING function's original locals
                            // (`c`, this call's own starting ctx) before
                            // handing control back to it, carrying
                            // forward only `ctx2_raw`'s updated
                            // `next_temp`/`next_label` counters. See
                            // `ctx_restore_locals`'s own doc comment --
                            // this is a real, distinct bug from the one
                            // `ctx_reset_locals` fixes: without this, a
                            // SECOND lifted lambda compiled later in the
                            // SAME enclosing function's body silently
                            // loses every local the first one's own
                            // reset ctx never had.
                            let ctx2 := ctx_restore_locals c ctx2_raw in
                            let body_instrs := List.append get_env_instrs instrs_r in
                            // Only append the body's own `ret` when the
                            // entry block does not ALREADY end in a
                            // terminator. A lifted lambda whose body is
                            // an `if`/`match` compiles its entry
                            // instructions down to a `br` into its own
                            // branch blocks, and `val_r` is then produced
                            // by a phi in the merge block those branches
                            // reach -- appending a `ret val_r` here emits
                            // an instruction AFTER the terminator that
                            // references a value defined in a LATER
                            // block. LLVM silently drops unreachable
                            // trailing instructions rather than
                            // rejecting them, so `llc` accepted the
                            // module and the bug surfaced only at
                            // runtime, as a corrupt value crossing a
                            // do-block `Monad_IO_bind` boundary
                            // (confirmed live: `elaborate_loaded_modules`
                            // segfaulted in `flatten_module_decls` on the
                            // `loaded` it received). 66 such blocks in
                            // one self-compiled binary. Same guard
                            // `build_match_case_block` already applies to
                            // a match arm's own instructions.
                            let entry_instrs :=
                                if ends_with_terminator body_instrs
                                then body_instrs
                                else List.append body_instrs (List.cons (LLVMInstruction.ret val_r) List.empty) in
                            let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                            let self_pair := ParamPair.mk "p0" LLVMType.i64_ in
                            let lam_pair := ParamPair.mk "p1" LLVMType.i64_ in
                            let lam_params := List.cons self_pair (List.cons lam_pair List.empty) in
                            let lam_func := LLVMFunction.mk lam_name lam_params LLVMType.i64_ (List.cons entry_block blocks_r) false Option.none in
                            match fresh_temp ctx2 {
                                CtxStrPair.mk ctx_box temp =>
                                    // `2` here is `lam_func`'s own real
                                    // LLVM param count (self + 1 real
                                    // param) -- controls the bitcast's
                                    // function-TYPE text
                                    // (`global_fn_ptr_text`'s own
                                    // `arity` param feeds
                                    // `repeat_type`). NOT the same
                                    // number as `alloc_closure`'s own
                                    // `1` just below (the LOGICAL/
                                    // apply-arity `apply_closureN`'s
                                    // own dispatch is keyed on) -- the
                                    // two genuinely diverge now that
                                    // every lifted function gains a
                                    // leading `self` param.
                                    let entry_text := global_fn_ptr_text lam_name 2 in
                                    let box_val := LLVMValue.alloc_closure entry_text 1 capture_vals in
                                    let box_instr := LLVMInstruction.assign temp box_val in
                                    match build_set_env_instrs (LLVMValue.var_ temp) capture_vals 0 ctx_box {
                                        { ctx := ctx_set, instrs := set_env_instrs } =>
                                            let all_instrs := List.cons box_instr set_env_instrs in
                                            CompileResult.ok ctx_set all_instrs (LLVMValue.var_ temp) List.empty (List.cons lam_func funcs_r) globals_r,
                                    },
                            },
                    },
            },
    }

#[partial]
def compile_db_if_ir (c : CodegenCtx) (cond : Term) (then_ : Term) (else_ : Term) : CompileResult :=
    match compile_db_term_ir c cond {
        CompileResult.ok ctx_cond cond_instrs cond_val blocks_cond funcs_cond globals_cond =>
            match ensure_i1_cond ctx_cond cond_instrs blocks_cond cond_val cond {
                { ctx := ctx_bool, instrs := instrs_bool, blocks := blocks_bool, val := bool_val } =>
                    match build_if_labels ctx_bool {
                        { ctx_after := ctx_branches, then_label := then_label, else_label := else_label, merge_label := merge_label } =>
                            let branch_instr := LLVMInstruction.branch bool_val then_label else_label in
                            // `if (if p then true else false) then ...`
                            // -- a branching COND itself -- means
                            // `instrs_bool` might already end in a
                            // terminator; splice via `compose_seq`
                            // instead of blindly appending (see its own
                            // doc comment above `ends_with_terminator`).
                            match compose_seq ({ instrs := instrs_bool, blocks := blocks_bool, val := bool_val }) ({ instrs := (List.cons branch_instr List.empty), blocks := List.empty, val := bool_val }) {
                                { instrs := entry_instrs, blocks := blocks_bool_spliced, val := _ } =>
                                    build_db_if_blocks ctx_branches then_label else_label merge_label then_ else_ entry_instrs blocks_bool_spliced funcs_cond globals_cond,
                            },
                    },
            },
    }

struct BoolCondResult {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
    blocks : List LLVMBasicBlock,
    val : LLVMValue,
}

/// LLVM's `br i1 <cond>` requires a genuine i1 value. Native comparison
/// applications (I64_eq/I64_lt/I64_gt/I64_ne) already compile to a real
/// i1 (an `icmp` instruction's own SSA result), safe to use as-is. Any
/// OTHER Bool-valued condition -- a call to a def like `List.is_empty`,
/// a bare `true`/`false` reference, anything routed through the general
/// `compile_db_term_ir` path -- compiles to a heap-allocated, tagged
/// Bool value (this codegen's uniform i64-everywhere convention for
/// calls -- see constructor_tag), and using that i64 pointer value
/// directly as an i1 is a genuine LLVM type mismatch ('%tN defined with
/// type i64 but expected i1') -- hit the first time any program's `if`
/// condition was anything other than a direct native comparison, e.g.
/// `List.last`'s `if List.is_empty tail then ... else ...`
/// (init/prelude.mo). Needs unboxing instead: read its runtime tag and
/// compare against Bool.true's tag to get a genuine i1.
/// `blocks`/`cond_val` -- threaded through (`blocks` used to be dropped
/// entirely by this function's own caller, `compile_db_if_ir`, before
/// this fix) so a branching `cond_term` splices correctly via
/// `compose_seq` instead of blindly appending the tag-check
/// instructions after an already-terminated `instrs`.
#[partial]
def ensure_i1_cond (c : CodegenCtx) (instrs : List LLVMInstruction) (blocks : List LLVMBasicBlock) (cond_val : LLVMValue) (cond_term : Term) : BoolCondResult :=
    if term_is_native_bool_op cond_term
    then { ctx := c, instrs := instrs, blocks := blocks, val := cond_val }
    else
        match fresh_temp c {
            CtxStrPair.mk ctx1 tag_temp =>
                let tag_call := LLVMValue.call "monad_get_tag" LLVMType.i64_ (List.cons cond_val List.empty) false in
                let tag_instr := LLVMInstruction.assign tag_temp tag_call in
                match fresh_temp ctx1 {
                    CtxStrPair.mk ctx2 bool_temp =>
                        let bool_true_tag := constructor_tag c "true" in
                        let cmp_instr := LLVMInstruction.assign bool_temp (LLVMValue.icmp_eq (LLVMValue.var_ tag_temp) (LLVMValue.int_ bool_true_tag)) in
                        let extra := List.cons tag_instr (List.cons cmp_instr List.empty) in
                        match compose_seq ({ instrs := instrs, blocks := blocks, val := cond_val }) ({ instrs := extra, blocks := List.empty, val := (LLVMValue.var_ bool_temp) }) {
                            { instrs := new_instrs, blocks := new_blocks, val := new_val } =>
                                { ctx := ctx2, instrs := new_instrs, blocks := new_blocks, val := new_val }
                        },
                },
        }

/// Dispatches through `lookup_native_any` (above), NOT a private,
/// narrower name-matching copy -- `is_native_bool_op_name`'s own prior
/// body compared `extract_base_name (symbol_identifier id)` (bare-only,
/// e.g. `"lt"` for `I64.lt`) against underscore-mangled strings
/// (`"I64_lt"`), which can never match: the exact same dotted-vs-
/// mangled-name mismatch class of bug `lookup_native_any`'s own doc
/// comment documents fixing for `try_compile_inline_native_db` (never
/// applied here). Confirmed as a real, previously-undiagnosed bug via a
/// direct repro (`if I64.lt a b then ... else ...`, non-constant so
/// constant-folding doesn't hide it): `term_is_native_bool_op` always
/// returned `false` for a DOTTED comparison (the only form real parsed
/// source ever produces), so `ensure_i1_cond` always took its "needs
/// unboxing" path even for a condition that already compiled to a
/// genuine `icmp`-produced `i1` -- `llc: '%tN' defined with type 'i1'
/// but expected 'i64'` the moment `monad_get_tag` tried to treat that
/// `i1` as a boxed pointer. This is exactly the shape the self-hosted
/// PARSER's own `furthest_error` (`lang/parser/combinators.mo`) uses
/// (`if I64.lt (String.length ...) (String.length ...) then ...`),
/// which blocked `bootstrap compile lang/main.mo monad`'s own
/// self-compile (`lang/main.mo` depends on the parser).
/// `term_peel` at the entry, not a shape match on `t` directly: since
/// stage 6 locates EVERY module's decls under debug, a dep module's
/// def body is routinely `Term.ctx _ (I64.beq a b)` -- e.g.
/// `number::BEq_I64_beq`, whose unboxed tail this probe exists to
/// catch. Matching the wrapper silently answered `false` and shipped a
/// raw `i1` `ret` (`llc: '%t11' defined with type 'i1' but expected
/// 'i64'`), which is exactly the silent-stop-matching failure mode
/// `term_peel`'s own doc comment warns about.
#[partial]
def term_is_native_bool_op (t : Term) : Bool := match term_peel t {
    Term.app fun_ _arg =>
        match fun_ {
            Term.app fun2 _arg2 =>
                match fun2 {
                    Term.var _idx dbg =>
                        match dbg {
                            DebugName.named id => is_native_bool_op_name (symbol_identifier id),
                            DebugName.unnamed => false,
                        },
                    _ => false,
                },
            _ => false,
        },
    _ => false,
}

/// `name` is a raw (possibly dotted, e.g. `"I64.lt"`) identifier
/// string -- routes through `lookup_native_any` (above), which already
/// tries both the underscore-mangled and bare-extracted forms, rather
/// than re-deriving that normalization here. Only `op_eq`/`op_lt`/
/// `op_gt`/`op_ne` produce a genuine `icmp`-shaped `i1` (`op_add`/
/// `op_sub`/`op_mul`/`op_sdiv` are I64-valued, not Bool-valued, and
/// never appear as an `if`'s own condition; the IO/string ops
/// `lookup_native_any` also resolves are irrelevant here too) -- see
/// `term_is_native_bool_op`'s own doc comment for the bug this fixes.
#[partial]
def is_native_bool_op_name (name : String) : Bool := match lookup_native_any name {
    Option.some op =>
        match op {
            NativeOp.op_eq => true,
            NativeOp.op_lt => true,
            NativeOp.op_gt => true,
            NativeOp.op_ne => true,
            _ => false,
        },
    Option.none => false,
}

#[partial]
def build_db_if_blocks (ctx : CodegenCtx) (then_label : String) (else_label : String) (merge_label : String) (then_ : Term) (else_ : Term) (entry_instrs : List LLVMInstruction) (entry_blocks : List LLVMBasicBlock) (entry_funcs : List LLVMFunction) (entry_globals : List LLVMGlobal) : CompileResult :=
    match compile_db_term_ir ctx then_ {
        CompileResult.ok ctx_then then_instrs_raw then_val_raw blocks_then funcs_then globals_then =>
            // A branch whose OWN instructions already end in a real
            // terminator (a nested if/match that itself returns
            // directly) never actually reaches `merge_label` at all --
            // `build_branch_block` correctly leaves its own terminator
            // alone rather than appending a `jump merge_label`, but
            // `build_merge_result` used to unconditionally build a
            // 2-entry phi keyed on `then_label`/`else_label` regardless,
            // producing a real, non-predecessor phi edge -- confirmed
            // via a direct repro (`lang/parser/position.mo`'s
            // `line_col_scan_direct`, chained/nested ifs): `llc`'s
            // verifier rejects it ("PHINode should have one entry for
            // each predecessor of its parent basic block!" /
            // "Instruction does not dominate all uses!"). Mirrors
            // `build_match_case_block`'s own already-established handling
            // of the identical shape for match arms.
            let then_reaches := not (ends_with_terminator then_instrs_raw) in
            let then_bmr := materialize_branch_val ctx_then then_ then_instrs_raw then_val_raw in
            let then_block := build_branch_block then_label merge_label then_bmr.instrs in
            match compile_db_term_ir then_bmr.ctx else_ {
                CompileResult.ok ctx_else else_instrs_raw else_val_raw blocks_else funcs_else globals_else =>
                    let else_reaches := not (ends_with_terminator else_instrs_raw) in
                    let else_bmr := materialize_branch_val ctx_else else_ else_instrs_raw else_val_raw in
                    let else_block := build_branch_block else_label merge_label else_bmr.instrs in
                    build_merge_result {
                        ctx_else := else_bmr.ctx,
                        merge_label := merge_label,
                        then_reaches := then_reaches,
                        then_val := then_bmr.val,
                        then_label := then_label,
                        else_reaches := else_reaches,
                        else_val := else_bmr.val,
                        else_label := else_label,
                        entry_instrs := entry_instrs,
                        entry_blocks := entry_blocks,
                        entry_funcs := entry_funcs,
                        entry_globals := entry_globals,
                        blocks_then := blocks_then,
                        blocks_else := blocks_else,
                        funcs_then := funcs_then,
                        funcs_else := funcs_else,
                        globals_then := globals_then,
                        globals_else := globals_else,
                        then_block := then_block,
                        else_block := else_block,
                    },
            },
    }

/// Builds `merge_label`'s own `PhiPair` list from whichever of
/// `then`/`else` actually reach it -- see `build_db_if_blocks`'s own
/// doc comment for why a branch might not.
#[partial]
def build_merge_phi_pairs (then_reaches : Bool) (then_val : LLVMValue) (then_label : String) (else_reaches : Bool) (else_val : LLVMValue) (else_label : String) : List PhiPair :=
    let then_pairs := if then_reaches then List.cons (PhiPair.mk then_val then_label) List.empty else List.empty in
    if else_reaches then List.cons (PhiPair.mk else_val else_label) then_pairs else then_pairs

/// `reaches`/`val`/`label`/`blocks` for ONE side (then or else) after
/// accounting for `retarget_terminal_ret` -- see `build_merge_result`'s
/// own doc comment for why a branch not directly reaching
/// `merge_label` doesn't mean it never reaches it at all.
struct BranchMergeInfo {
    reaches : Bool,
    label : String,
    blocks : List LLVMBasicBlock,
}

#[partial]
def resolve_branch_merge_info (reaches : Bool) (val : LLVMValue) (label : String) (blocks : List LLVMBasicBlock) (merge_label : String) : BranchMergeInfo :=
    if reaches
    then { reaches := true, label := label, blocks := blocks }
    else
        match retarget_terminal_ret blocks val merge_label {
            Option.some result => { reaches := true, label := result.label, blocks := result.blocks },
            // Shouldn't happen -- see `build_match_case_block`'s own
            // identical fallback.
            Option.none => { reaches := false, label := label, blocks := blocks },
        }

/// `then_reaches`/`else_reaches` being `false` means that side's own
/// compiled instructions already end in a real terminator (a nested
/// if/match, or a general call whose own args needed one) -- NOT that
/// it never reaches `merge_label` at all: its own deepest nested block
/// currently `ret`s its own value directly (correct only when THIS
/// if-expression is the enclosing function's own final answer, exactly
/// `compose_seq`'s own documented convention one level up) and must be
/// RETARGETED to `br label merge_label` instead, via `retarget_terminal_
/// ret` (`resolve_branch_merge_info`). An earlier version of this
/// function instead contributed NO phi entry at all for such a branch,
/// on the theory that it "never actually reaches `merge_label`" --
/// confirmed wrong live via the full `lang/main.mo` self-compile:
/// malformed PHI nodes at `llc`'s own IR-verification stage. Mirrors
/// `build_match_case_block`'s own identical fix for match arms.
#[partial]
def build_merge_result (ctx_else : CodegenCtx) (merge_label : String) (then_reaches : Bool) (then_val : LLVMValue) (then_label : String) (else_reaches : Bool) (else_val : LLVMValue) (else_label : String) (entry_instrs : List LLVMInstruction) (entry_blocks : List LLVMBasicBlock) (entry_funcs : List LLVMFunction) (entry_globals : List LLVMGlobal) (blocks_then : List LLVMBasicBlock) (blocks_else : List LLVMBasicBlock) (funcs_then : List LLVMFunction) (funcs_else : List LLVMFunction) (globals_then : List LLVMGlobal) (globals_else : List LLVMGlobal) (then_block : LLVMBasicBlock) (else_block : LLVMBasicBlock) : CompileResult :=
    match fresh_temp ctx_else {
        CtxStrPair.mk ctx_phi phi_temp =>
            let then_info := resolve_branch_merge_info then_reaches then_val then_label blocks_then merge_label in
            let else_info := resolve_branch_merge_info else_reaches else_val else_label blocks_else merge_label in
            let pairs := build_merge_phi_pairs then_info.reaches then_val then_info.label else_info.reaches else_val else_info.label in
            let merge_instrs := match pairs {
                // Neither branch reaches `merge_label` -- both diverge
                // via their own nested control flow, so this block is
                // genuinely dead code and no real value ever flows into
                // it. `ret` a harmless placeholder instead of emitting
                // an operand-less `phi` (invalid IR) -- mirrors
                // `phi_pairs_type`'s own "empty pairs" fallback.
                List.empty => List.cons (LLVMInstruction.ret (LLVMValue.int_ 0)) List.empty,
                List.cons _ _ =>
                    let phi_instr := LLVMInstruction.assign phi_temp (LLVMValue.phi pairs) in
                    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ phi_temp) in
                    List.cons phi_instr (List.cons ret_instr List.empty),
            } in
            let merge_block := LLVMBasicBlock.mk merge_label merge_instrs in
            let all_blocks := List.cons then_block (List.cons else_block (List.cons merge_block (append_blocks (append_blocks entry_blocks then_info.blocks) else_info.blocks))) in
            let all_funcs := List.append (List.append entry_funcs funcs_then) funcs_else in
            let all_globals := List.append (List.append entry_globals globals_then) globals_else in
            let result_val := match pairs {
                List.empty => LLVMValue.int_ 0,
                List.cons _ _ => LLVMValue.var_ phi_temp,
            } in
            CompileResult.ok ctx_phi entry_instrs result_val all_blocks all_funcs all_globals,
    }

#[partial]
def compile_db_term_ir (c : CodegenCtx) (term_ : Term) : CompileResult := match term_ {
    Term.lit val => compile_lit_ir c val,
    Term.var idx dbg =>
        match dbg {
            DebugName.named id =>
                match ctx_lookup_local c id {
                    Option.some val => CompileResult.ok c List.empty val List.empty List.empty List.empty,
                    Option.none =>
                        // Check if this is a constructor reference --
                        // guarded by `ctx_lookup_arity` too, not just
                        // `is_constructor_var`'s own bare-name-only
                        // lookup, for the same reason `try_compile_
                        // constructor_app_db`'s own identical guard
                        // exists (see its doc comment): a real top-level
                        // function can share its bare name with an
                        // unrelated constructor (e.g. `lang/parser/
                        // combinators.mo`'s `def tag` vs `ParseError`'s
                        // `tag` constructor), and a genuine constructor
                        // is never ALSO a real def, so this cannot
                        // false-negative on any real constructor.
                        let name := symbol_identifier id in
                        let llvm_name := ref_symbol_name id in
                        let also_a_real_fn := match ctx_lookup_arity c llvm_name {
                            Option.some _ => true,
                            Option.none => false,
                        } in
                        if is_constructor_var c name && Bool.not also_a_real_fn then
                            let tag_val := constructor_tag c name in
                            let ctor_arity := constructor_arity c name in
                            if I64.beq ctor_arity 0 then
                                // Compile as alloc_constructor with 0
                                // fields. Must use THIS constructor's own
                                // tag (e.g. `none` = 3), not a hardcoded 0
                                // (`Unit.unit`'s tag) -- a hardcoded tag
                                // made every bare 0-arg constructor
                                // reference indistinguishable from
                                // Unit.unit during match dispatch.
                                match fresh_temp c {
                                    CtxStrPair.mk ctx_t temp =>
                                        let alloc_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (List.cons (LLVMValue.int_ tag_val) (List.cons (LLVMValue.int_ 0) List.empty)) false in
                                        let assign_instr := LLVMInstruction.assign temp alloc_val in
                                        CompileResult.ok ctx_t (List.cons assign_instr List.empty) (LLVMValue.var_ temp) List.empty List.empty List.empty,
                                }
                            else
                                // A bare, unapplied reference to an
                                // arity>0 constructor (e.g. `List.map
                                // Identifier.id ids`, `List.map Option.
                                // some xs`) -- the constructor ITSELF is
                                // a first-class value here, not a
                                // saturated application (that shape goes
                                // through `try_compile_constructor_app_
                                // db` instead, never reaching this bare-
                                // Term.var case at all). The `ctor_arity
                                // == 0` branch above would allocate a
                                // 0-field object regardless of the real
                                // field count -- correct only for a
                                // genuinely nullary constructor. Boxes a
                                // genuine closure instead, mirroring the
                                // ordinary "arity>0 def referenced as a
                                // value" case just below
                                // (`build_closure_shim_func`), generalized
                                // for a constructor: `build_constructor_
                                // closure_shim_func`'s shim allocates a
                                // real tagged Constructor and sets each
                                // field from its own forwarded args,
                                // rather than forwarding to another
                                // function. Confirmed as a real gap via a
                                // live self-compiled binary's own SIGSEGV
                                // (jumping to a garbage function pointer
                                // inside `List.map`'s `apply_closure1`,
                                // traced to `ids_to_module_path`'s own
                                // `List.map Identifier.id ids`).
                                match fresh_temp c {
                                    CtxStrPair.mk ctx_t temp =>
                                        let shim_name := String.concat llvm_name "_ctor_closure_shim" in
                                        let shim_func := build_constructor_closure_shim_func shim_name tag_val ctor_arity in
                                        let entry_text := global_fn_ptr_text shim_name (ctor_arity + 1) in
                                        let box_val := LLVMValue.alloc_closure entry_text ctor_arity List.empty in
                                        let assign_instr := LLVMInstruction.assign temp box_val in
                                        CompileResult.ok ctx_t (List.cons assign_instr List.empty) (LLVMValue.var_ temp) List.empty (List.cons shim_func List.empty) List.empty,
                                }
                        else
                            // A bare reference to a global (non-local,
                            // non-constructor) name, in VALUE position --
                            // i.e. reached here rather than being
                            // special-cased by `compile_general_db_call`'s
                            // own bypass for the CALLEE position (see that
                            // function's own doc comment). A 0-arity
                            // top-level `def` compiles to a real LLVM
                            // function taking no arguments -- referencing
                            // it as a VALUE means "the result of calling
                            // it", so this must emit an actual 0-arg call,
                            // not a bare `%llvm_name` SSA reference (no
                            // such register is ever assigned otherwise --
                            // confirmed as a real bug via a minimal
                            // standalone repro, `def five : I64 := 5` /
                            // `def main : I64 := five`, which previously
                            // failed `llc` outright with "use of undefined
                            // value '%five'").
                            //
                            // An arity>0 def referenced this way means
                            // something different: "the function itself,
                            // as a first-class value" (stored, passed,
                            // boxed into a struct field -- e.g. a Phase 2
                            // dictionary's own method fields, see
                            // plans/bootstrapping/self-hosted-compiler.md).
                            // Eager-0-arg-calling it here would be
                            // invalid LLVM (an arg-count mismatch against
                            // its real declared signature) -- box it via
                            // `alloc_closure` instead (Phase 0 of that
                            // same plan), producing a genuine callable
                            // value `compile_general_db_call`'s callee
                            // dispatch (below) can later call through
                            // indirectly via `apply_closureN`.
                            match ctx_lookup_arity c llvm_name {
                                Option.some arity =>
                                    if I64.beq arity 0 then
                                        match fresh_temp c {
                                            CtxStrPair.mk ctx_t temp =>
                                                let call_val := LLVMValue.call llvm_name LLVMType.i64_ List.empty false in
                                                let assign_instr := LLVMInstruction.assign temp call_val in
                                                CompileResult.ok ctx_t (List.cons assign_instr List.empty) (LLVMValue.var_ temp) List.empty List.empty List.empty,
                                        }
                                    else
                                        // `apply_closureN` (runtime.c)
                                        // now uniformly passes ITS OWN
                                        // closure pointer as `entry`'s
                                        // leading arg to every closure
                                        // it invokes (needed for a REAL
                                        // lifted lambda,
                                        // `compile_db_lam_ir`, to read
                                        // its own captures) -- but
                                        // `llvm_name`'s own compiled
                                        // signature (`(p0..p{arity-1})
                                        // -> i64`, no leading self
                                        // param) is ALSO the exact
                                        // signature every ordinary
                                        // DIRECT call to it elsewhere in
                                        // the program uses, so it can't
                                        // itself grow a leading self
                                        // param without breaking those.
                                        // Box a tiny forwarding SHIM
                                        // instead of `llvm_name`'s own
                                        // entry point -- conforms to the
                                        // uniform (self, p1..p_arity)
                                        // convention `apply_closureN`
                                        // expects, ignores self,
                                        // forwards through unchanged
                                        // (`build_closure_shim_func`,
                                        // below). `llvm_name` itself is
                                        // completely untouched. `env`
                                        // stays empty -- this case
                                        // genuinely has zero captures,
                                        // it's a reference to a global.
                                        match fresh_temp c {
                                            CtxStrPair.mk ctx_t temp =>
                                                let shim_name := String.concat llvm_name "_closure_shim" in
                                                let shim_func := build_closure_shim_func shim_name llvm_name arity in
                                                let entry_text := global_fn_ptr_text shim_name (arity + 1) in
                                                let box_val := LLVMValue.alloc_closure entry_text arity List.empty in
                                                let assign_instr := LLVMInstruction.assign temp box_val in
                                                CompileResult.ok ctx_t (List.cons assign_instr List.empty) (LLVMValue.var_ temp) List.empty (List.cons shim_func List.empty) List.empty,
                                        },
                                // No arity known for this name (module
                                // compiled via `empty_ctx empty_arities`,
                                // or a genuinely unreachable/unresolved
                                // reference) -- fall back to the original,
                                // pre-Phase-0 eager-0-arg-call behavior.
                                // Correct for 0-arity defs; no worse than
                                // before Phase 0 for anything else.
                                Option.none =>
                                    match fresh_temp c {
                                        CtxStrPair.mk ctx_t temp =>
                                            let call_val := LLVMValue.call llvm_name LLVMType.i64_ List.empty false in
                                            let assign_instr := LLVMInstruction.assign temp call_val in
                                            CompileResult.ok ctx_t (List.cons assign_instr List.empty) (LLVMValue.var_ temp) List.empty List.empty List.empty,
                                    },
                            },
                },
            DebugName.unnamed =>
                CompileResult.ok c List.empty LLVMValue.void_val List.empty List.empty List.empty,
        },
    Term.lam dbg typ body => compile_db_lam_ir c dbg typ body,
    Term.app fun arg => compile_db_app_ir c fun arg,
    Term.ntv native => compile_ntv_ir c native,
    Term.con constr => compile_con_ir c constr,
    Term.forall dbg kind body => CompileResult.ok c List.empty LLVMValue.void_val List.empty List.empty List.empty,
    Term.pi arg ret => CompileResult.ok c List.empty LLVMValue.void_val List.empty List.empty List.empty,
    Term.type_ universe => CompileResult.ok c List.empty LLVMValue.void_val List.empty List.empty List.empty,
    Term.hole => CompileResult.ok c List.empty LLVMValue.void_val List.empty List.empty List.empty,
    Term.ctx loc inner => compile_located_term_ir c loc inner,
}

#[partial]
def compile_db_app_ir (c : CodegenCtx) (fun : Term) (arg : Term) : CompileResult :=
    // Check `let`-shaped beta-redexes FIRST -- `fun` here is a bare
    // `Term.lam`, a shape none of the other three cases below ever
    // match (they all key off `fun`/its own head being `Term.var`), so
    // ordering relative to them doesn't matter for correctness. It's
    // checked first purely because it's the single most common call
    // shape in real code (see its own doc comment).
    match try_compile_let_beta_db c fun arg {
        Option.some result => result,
        Option.none =>
            // Check if this is a constructor application
            match try_compile_constructor_app_db c fun arg {
                Option.some result => result,
                Option.none =>
                    match try_compile_inline_native_db c fun arg {
                        Option.some result => result,
                        Option.none => compile_general_db_call c fun arg,
                    },
            },
    }

/// `let x := arg in body` (`lang/parser.mo`'s `let_term_body`) desugars
/// to literally `Term.app (Term.lam x _ body) arg` -- NOT a distinct
/// `Term.let_` AST node, so every `let` in the entire corpus is,
/// structurally, an immediately-applied lambda. Before this case
/// existed, `compile_db_app_ir` had no way to tell "immediately-applied"
/// apart from "stored/passed/returned as a first-class value" and
/// treated BOTH the same way: compiling `fun` via `compile_db_term_ir`
/// (`Term.lam`'s case) always LIFTS it to a brand-new independent
/// top-level LLVM function (`compile_db_lam_ir`, a single-parameter
/// function whose only local binding is that one parameter).
///
/// For a genuinely first-class lambda (stored in a variable, passed to
/// `List.map`, ...) that's the right (if still capture-incomplete --
/// see `compile_db_lam_ir`'s own doc comment) shape. But for a `let`,
/// it's actively wrong: lifting throws away every binding already in
/// scope in the CURRENT function, so a chain of lets --
/// `let a := 2 in let b := 3 in I64.add a b` -- lifts `b`'s continuation
/// into its OWN fresh function whose only parameter is named `p0`, and
/// since `ctx_bind_local` merely PREPENDS the new binding onto whatever
/// bindings the surrounding context (wrongly) carried forward, `a`
/// (bound to the OUTER lifted function's own `p0`) and `b` (bound to
/// the INNER one's `p0`) both end up resolving to the exact same LLVM
/// value `%p0` inside `b`'s function body -- `I64.add a b` silently
/// compiles as `add i64 %p0, %p0`. Confirmed via a real compile-and-run
/// repro (returned 6, not 5) before this fix, and via the classic
/// `llc: use of undefined value '%lambda_N'` failure for chains that
/// reference a still-outer-outer local no longer in scope at all once
/// lifted.
///
/// The fix: recognize this exact shape and DON'T lift at all -- this is
/// a plain beta-reduction, not a real closure. Compile `arg`, bind the
/// lambda's own parameter name directly to `arg`'s resulting value in
/// the CURRENT context (exactly what an ordinary `let` should do), and
/// keep compiling `body` inline in the SAME function. No new function,
/// no lost bindings, no capture problem -- because nothing is captured
/// across a function boundary at all.
#[partial]
def try_compile_let_beta_db (c : CodegenCtx) (fun : Term) (arg : Term) : Option CompileResult :=
    match fun {
        Term.lam dbg _typ body =>
            let name : Identifier := match dbg {
                named id => id,
                unnamed => Identifier.id "_",
            } in
            match compile_db_term_ir c arg {
                CompileResult.ok ctx1 instrs1 val1_raw blocks1 funcs1 globals1 =>
                    // `arg` may be a native boolean comparison
                    // (`I64.lt`/etc) -- box it into a genuine tagged
                    // Bool object HERE, at the let-binding site, same as
                    // `materialize_native_bool_arg`'s own doc comment
                    // (`compile_spine_args_go`/`compile_ntv_args_go`
                    // above): once bound to `name`, every LATER reference
                    // is just `Term.var name`, which loses the "this came
                    // from a native comparison" term-shape signal
                    // `ensure_i1_cond`/this same check needs -- so a
                    // let-bound comparison's raw `i1` must be boxed NOW,
                    // not deferred to whichever later use-site happens to
                    // re-derive it (most of them can't). Confirmed as a
                    // real gap via `bootstrap compile lang/main.mo
                    // monad`'s own self-compile (`render_source_context`,
                    // `lang/parser/diagnostic.mo`): a `let`-bound
                    // comparison reused as a LATER `if`'s own condition
                    // hit `ensure_i1_cond`'s "needs unboxing" branch
                    // (correctly, since `Term.var name` isn't itself a
                    // native-op application) and called `monad_get_tag`
                    // on a still-raw `i1` -- `llc: '%tN' defined with
                    // type 'i1' but expected 'i64'`. Safe to append
                    // `bool_instrs` directly (no `compose_seq` splicing
                    // needed): a native comparison never itself compiles
                    // to a branch/multiple blocks, so `instrs1` never
                    // ends in a terminator whenever `bool_instrs` is
                    // non-empty.
                    match materialize_native_bool_arg ctx1 arg val1_raw {
                        { ctx := ctx1b, instrs := bool_instrs, val := val1 } =>
                            let instrs1m := List.append instrs1 bool_instrs in
                            let ctx_bound := ctx_bind_local ctx1b name val1 in
                            match compile_db_term_ir ctx_bound body {
                                CompileResult.ok ctx2 instrs2_raw val2_raw blocks2 funcs2 globals2 =>
                                    // `body` (the let's own continuation)
                                    // needs the same materialization as
                                    // `arg` above -- confirmed via a real
                                    // repro (`lang/parser/position.mo`'s
                                    // `combine_line_col_scan`: `let
                                    // trailing := (if ...) in { struct
                                    // literal using trailing }`). The
                                    // struct literal is a SEPARATE,
                                    // already-filed bug (doesn't desugar
                                    // to `Term.con` here, `implementations/
                                    // 2026-08-29-struct-literal-not-
                                    // desugared-in-branch-position.md`),
                                    // but its `void_val` reaches THIS
                                    // exact site (a let's own body/
                                    // continuation) and `compose_seq`
                                    // splices it straight into the
                                    // `if`-expr's own dangling `ret %tN`
                                    // (from compiling `arg`) unmaterialized
                                    // -- `ret void` where `i64` is
                                    // expected. `materialize_branch_val`'s
                                    // own "skip if already terminated"
                                    // guard means this is a no-op whenever
                                    // `body` is itself branching (its own
                                    // `instrs2_raw` already ends in a
                                    // terminator then).
                                    match materialize_branch_val ctx2 body instrs2_raw val2_raw {
                                        { ctx := ctx2m, instrs := instrs2, val := val2 } =>
                                            match compose_seq ({ instrs := instrs1m, blocks := blocks1, val := val1 }) ({ instrs := instrs2, blocks := blocks2, val := val2 }) {
                                                { instrs := combined, blocks := all_blocks, val := last_val } =>
                                                    Option.some (CompileResult.ok ctx2m combined last_val all_blocks (List.append funcs1 funcs2) (List.append globals1 globals2)),
                                            },
                                    },
                            },
                    },
            },
        _ => Option.none,
    }

/// Detects a fully-applied constructor call of ANY arity by flattening
/// the WHOLE application spine (`Term.app fun arg` as a unit, not just
/// `fun`/`arg` in isolation) and checking whether its ultimate HEAD is a
/// known constructor -- generalizes the previous single-arg-only version
/// (which only matched when `fun` was directly `Term.var`, so a 2+-arg
/// constructor call's outer `Term.app` -- `fun` itself another `Term.app`
/// -- never matched at all and fell through to `compile_general_db_call`'s
/// ordinary-function-call path, producing `llc: use of undefined value
/// '@Foo_bar'` for any constructor with 2+ fields, INCLUDING builtins
/// like `List.cons`, not just user-defined types). Safe to flatten the
/// full spine here: `compile_db_app_ir` (this function's own caller) is
/// only ever invoked once per ORIGINAL, outermost `Term.app` node in the
/// term tree (`compile_db_term_ir`'s own top-down dispatch) --
/// `compile_general_db_call`'s own internal spine-flattening never
/// re-enters this "try" chain on an inner node, so there's no risk of
/// this matching a PARTIAL sub-application twice.
/// See `implementations/2026-08-29-user-defined-constructor-codegen-gap.md`.
/// `is_constructor_var`'s own bare-name-only lookup (needed for match-arm
/// dispatch, which really can only ever supply a bare constructor name --
/// see its own doc comment) can't distinguish an ordinary top-level
/// FUNCTION from a data constructor of some unrelated type that happens
/// to share the same bare name -- e.g. `lang/parser/combinators.mo`'s own
/// `def tag (s : String) (input : String) : ParseResult String` versus
/// `lang/parser/core.mo`'s `ParseError`'s `tag (expected) (remaining)`
/// constructor: same bare name, same arity. Reusing that table here to
/// decide "is this call spine's head actually a constructor?" silently
/// miscompiled EVERY call to the real `tag` function throughout
/// `lang/parser.mo`/`combinators.mo` into `alloc_constructor`-ing a bare
/// `ParseError.tag` object instead -- confirmed via a minimal standalone
/// repro (a same-named 2-arg function alongside a same-named 2-arg
/// constructor) and via the real self-compiled binary's own crash
/// (`String_length` segfaulting on a garbage pointer, deep in
/// `furthest_error`/`alt_fold`'s recursion, the moment the resulting
/// binary tried to parse anything -- `llc`'s IR verifier can't catch
/// this, the miscompiled IR is structurally valid, just semantically
/// wrong). A genuine constructor is never ALSO a real top-level def, so
/// checking `ctx_lookup_arity` (keyed the same way an ordinary function
/// call's own callee name resolution already is, `compile_db_term_ir`'s
/// `Term.var` case just above) and preferring the function-call
/// interpretation whenever it's present cannot false-negative on any
/// real constructor call, and directly resolves this class of collision
/// without touching the parser's own source.
#[partial]
def try_compile_constructor_app_db (c : CodegenCtx) (fun : Term) (arg : Term) : Option CompileResult :=
    match flatten_app_spine (Term.app fun arg) {
        { head, args } =>
            match head {
                Term.var idx dbg =>
                    match dbg {
                        DebugName.named id =>
                            let name := symbol_identifier id in
                            let llvm_name := ref_symbol_name id in
                            let looks_like_ctor := is_constructor_var c name in
                            let also_a_real_fn := match ctx_lookup_arity c llvm_name {
                                Option.some _ => true,
                                Option.none => false,
                            } in
                            if looks_like_ctor && Bool.not also_a_real_fn
                            then
                                let base_name := extract_base_name name in
                                let con := Con.mk (Identifier.id base_name) (ModulePath.mp List.empty) (List.length args) (wrap_some_list args) in
                                Option.some (compile_con_ir c con)
                            else Option.none,
                        DebugName.unnamed => Option.none,
                    },
                _ => Option.none,
            },
    }

#[partial]
def wrap_some_list (xs : List Term) : List (Option Term) := match xs {
    List.empty => List.empty,
    List.cons x rest => List.cons (Option.some x) (wrap_some_list rest),
}

#[partial]
def try_compile_inline_native_db (c : CodegenCtx) (fun : Term) (arg : Term) : Option CompileResult :=
    match fun {
        Term.app fun2 arg2 =>
            match fun2 {
                Term.var idx dbg =>
                    match dbg {
                        DebugName.named id =>
                            let name := symbol_identifier id in
                            match lookup_native_any name {
                                Option.some op =>
                                    Option.some (compile_native_app_db c op arg2 arg),
                                Option.none => Option.none,
                            },
                        DebugName.unnamed => Option.none,
                    },
                _ => Option.none,
            },
        Term.var idx dbg =>
            match dbg {
                DebugName.named id =>
                    let name := symbol_identifier id in
                    match lookup_native_any name {
                        Option.some op =>
                            Option.some (compile_native_app_unary_db c op arg),
                        Option.none => Option.none,
                    },
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

// `print_str`/`write_file` are declared `void` on the C side
// (`lang/codegen/runtime.c`) -- their LLVM `declare` says so (`mk_decl
// "monad_print_str" ... "void"`), but every native CALL here is always
// emitted `i64`-typed (`LLVMType.i64_`) regardless, so the call itself
// produces an i64 "result" that's really just whatever garbage the C
// ABI happened to leave in the return register, not a real value.
// Harmless as long as nothing reads it -- but a native call used as a
// do-notation statement's own VALUE (e.g. `println x; return unit`
// desugars to `Monad.bind (println x) (\_ -> Monad.pure unit)`) feeds
// that garbage straight into `bind`'s own first argument, which
// `Monad_IO_bind` then treats as a real tagged pointer
// (`monad_get_tag`/`monad_get_field`) -- confirmed as a real gap via a
// direct repro (a do-block whose first statement is a bare `println`
// call): compiled clean, segfaulted on the very first line, before
// printing anything.
//
// Fixed narrowly, without touching the (apparently llc-tolerated)
// call-type mismatch itself: `println`/`write_file`'s REAL declared
// type is `IO Unit`, i.e. a properly tagged `IO.io Unit` constructor
// value (one field, holding the `Unit` value) -- exactly the shape
// `Monad_IO_pure`'s own generated body builds (`alloc_constructor` at
// `constructor_tag "IO.io"` + one `monad_set_field`). A first attempt
// at this fix used a BARE `Unit` value instead (via the already-
// generated `monad_ctor_Unit_unit`) -- that alone doesn't crash
// (`monad_get_tag` on it "works", it just reads the WRONG tag), but
// `Monad_IO_bind`'s `monad_get_field(%p0, 0)` then reads past a
// 0-field `Unit` object's empty `[0 x i8*]` fields array, a real
// out-of-bounds read -- exactly the observed segfault. Reusing
// `compile_con_ir`'s own `alloc_constructor`/`build_set_field_instrs`
// helpers here (rather than hand-rolling the wrap) keeps this in sync
// with however a real `IO.io _` constructor literal compiles elsewhere.
#[partial]
def is_void_native (op : NativeOp) : Bool :=
    match op {
        NativeOp.op_print_str => true,
        NativeOp.op_write_file => true,
        _ => false,
    }

/// Every native op whose Monad-level declared type is `IO _`
/// (`init/io.mo`) -- `op_print_str`/`op_read_file`/`op_write_file`/
/// `op_file_exists` -- needs its raw call result wrapped in a real
/// `IO.io`-tagged constructor before it can be used as an `IO` value
/// (do-notation's `<-`, `Monad_IO_bind`, ...). The 8 arithmetic/comparison
/// ops and `op_i64_to_string` (`I64 -> String`, genuinely pure, no `IO` in
/// its type at all) do not.
///
/// `is_void_native` (above) was previously the ONLY signal used to decide
/// this, conflating "the C function is declared `void`" with "the Monad
/// type is `IO _`" -- true for `print_str`/`write_file` (both void AND
/// `IO Unit`), but `read_file`/`file_exists` are `IO _`-returning WITHOUT
/// being C-`void` (`monad_read_file`/`monad_file_exists` return a real
/// `char*`). Their raw call result was used AS-IS wherever an `IO` value
/// was expected -- `Monad_IO_bind`'s own generated body calls
/// `monad_get_field(io_val, 0)` on it, misreading the raw string pointer
/// as if it were a tagged constructor object. Confirmed via a direct
/// repro (`let s <- IO.read_file path; IO.println s; ...`): compiled and
/// linked cleanly, segfaulted at runtime the moment `s` was used for
/// anything beyond being bound-and-ignored -- silent as long as the bound
/// value was never touched.
#[partial]
def needs_io_wrap (op : NativeOp) : Bool :=
    match op {
        NativeOp.op_print_str => true,
        NativeOp.op_read_file => true,
        NativeOp.op_write_file => true,
        NativeOp.op_file_exists => true,
        NativeOp.op_is_dir => true,
        // `String.hash : String -> U64` is pure (init/string.mo) -- no
        // `IO` in its type at all, same as `op_i64_to_string`.
        NativeOp.op_string_hash => false,
        _ => false,
    }

/// `IO.file_exists`/`IO.is_dir` (`monad_file_exists`/`monad_is_dir`,
/// `runtime.c`) use a "truthy pointer" C convention -- a non-null
/// pointer for true, `NULL` for false -- not a genuine tagged `Bool`.
/// Left as-is, `wrap_io_value_native_result_go` stores that raw pointer
/// directly as `IO.io`'s field, so any `if` that later consumes it
/// (through a `do`-block bind, never as a bare comparison term, so
/// `term_is_native_bool_op`'s fast path never applies) calls
/// `monad_get_tag` on it and reads garbage header bytes at that address
/// instead of a real tag -- the branch then always reads false.
/// Confirmed live: `IO.is_dir (Path.path "/tmp")` printed "false" once
/// compiled and run (correct under the tree-walking interpreter).
#[partial]
def native_op_returns_truthy_ptr (op : NativeOp) : Bool := match op {
    NativeOp.op_file_exists => true,
    NativeOp.op_is_dir => true,
    _ => false,
}

/// Fixes the gap `native_op_returns_truthy_ptr`'s doc comment
/// describes, the same way `materialize_native_bool_arg` fixes the
/// sibling i1-vs-value gap: `icmp_ne` the raw pointer against 0 first
/// to get a genuine i1, then reuse its zext + `2 - raw` tag mapping to
/// build a real heap `Bool` constructor.
#[partial]
def materialize_truthy_ptr_as_bool (c : CodegenCtx) (raw_val : LLVMValue) : MaterializedVal :=
    match fresh_temp c {
        CtxStrPair.mk ctx0 cmp_temp =>
            match fresh_temp ctx0 {
                CtxStrPair.mk ctx1 zext_temp =>
                    match fresh_temp ctx1 {
                        CtxStrPair.mk ctx2 tag_temp =>
                            match fresh_temp ctx2 {
                                CtxStrPair.mk ctx3 con_temp =>
                                    let cmp_instr := LLVMInstruction.assign cmp_temp (LLVMValue.icmp_ne raw_val (LLVMValue.int_ 0)) in
                                    let zext_instr := LLVMInstruction.assign zext_temp (LLVMValue.zext (LLVMValue.var_ cmp_temp) LLVMType.i1_ LLVMType.i64_) in
                                    let tag_val := LLVMValue.sub (LLVMValue.int_ 2) (LLVMValue.var_ zext_temp) in
                                    let tag_instr := LLVMInstruction.assign tag_temp tag_val in
                                    let con_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (List.cons (LLVMValue.var_ tag_temp) (List.cons (LLVMValue.int_ 0) List.empty)) false in
                                    let con_instr := LLVMInstruction.assign con_temp con_val in
                                    { ctx := ctx3, instrs := (List.cons cmp_instr (List.cons zext_instr (List.cons tag_instr (List.cons con_instr List.empty)))), val := (LLVMValue.var_ con_temp) },
                            },
                    },
            },
    }

#[partial]
def compile_native_app_unary_db (c : CodegenCtx) (op : NativeOp) (arg : Term) : CompileResult :=
    match compile_db_term_ir c arg {
        CompileResult.ok ctx1 instrs1 val1 blocks1 funcs1 globals1 =>
            // For unary native operations like print_str, call the runtime function
            match fresh_temp ctx1 {
                CtxStrPair.mk ctx_t temp =>
                    let fn_name := native_op_to_fn_name op in
                    let call_val := LLVMValue.call fn_name LLVMType.i64_ (List.cons val1 List.empty) false in
                    let assign_instr := LLVMInstruction.assign temp call_val in
                    // `println (if p then "a" else "b")`-shaped code:
                    // `arg` itself branching means `instrs1` already
                    // ends in a terminator -- splice via `compose_seq`
                    // instead of blindly appending (see its own doc
                    // comment above `ends_with_terminator`).
                    match compose_seq ({ instrs := instrs1, blocks := blocks1, val := val1 }) ({ instrs := (List.cons assign_instr List.empty), blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                        { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                            if is_void_native op then
                                wrap_void_native_result ctx_t (LLVMValue.var_ temp) new_instrs new_blocks funcs1 globals1
                            else if needs_io_wrap op then
                                if native_op_returns_truthy_ptr op then
                                    match materialize_truthy_ptr_as_bool ctx_t (LLVMValue.var_ temp) {
                                        { ctx := ctx_b, instrs := bool_instrs, val := bool_val } =>
                                            wrap_io_value_native_result ctx_b (LLVMValue.var_ temp) bool_instrs new_instrs new_blocks funcs1 globals1 bool_val,
                                    }
                                else
                                    wrap_io_value_native_result ctx_t (LLVMValue.var_ temp) List.empty new_instrs new_blocks funcs1 globals1 (LLVMValue.var_ temp)
                            else
                                CompileResult.ok ctx_t new_instrs (LLVMValue.var_ temp) new_blocks funcs1 globals1,
                    },
            },
    }

/// Builds the tail every void native's result needs: an inner `Unit`
/// value (`monad_ctor_Unit_unit`), then wrapped as `IO.io Unit` --
/// mirrors `compile_con_ir`'s own `alloc_constructor` +
/// `build_set_field_instrs` pair, just with an already-computed field
/// value instead of one still needing its own `compile_db_term_ir` call.
///
/// `prior_val` -- the raw native call's OWN result value (`temp` at
/// every call site below) -- is required, not optional: whenever the
/// native's ARGUMENT was itself branching (`println (if p then "a" else
/// "b")`), `prior_instrs`/`prior_blocks` already end in a real
/// terminator (`compose_seq`'s own convention -- see its doc comment),
/// and the ONLY way to correctly append more code is `compose_seq`
/// again, which needs `prior_val` to find the right terminal block to
/// splice into. Naively `List.append`-ing the wrap code onto
/// `prior_instrs` used to put it right after that terminator instead --
/// unreachable dead code, with the branching arg's own placeholder `ret`
/// becoming the function's real, early, wrong answer. Confirmed live:
/// `let is_d <- IO.is_dir p; IO.println (a ++ (if is_d then .. else
/// ..)); let exists <- IO.file_exists p2; IO.println ...` -- compiled
/// and run, printed only the first line and exited 0, silently dropping
/// every statement after the `if`-using `println` (its own `Monad_IO_
/// bind`-to-the-next-statement code landed in the WRONG, unreachable
/// block). Same root cause class `compose_seq`'s own doc comment
/// documents for its original bug, one level up: these two wrap
/// functions were never updated to use it themselves.
#[partial]
def wrap_void_native_result (ctx : CodegenCtx) (prior_val : LLVMValue) (prior_instrs : List LLVMInstruction) (prior_blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) : CompileResult :=
    match fresh_temp ctx {
        CtxStrPair.mk ctx_unit temp_unit =>
            let unit_call := LLVMValue.call "monad_ctor_Unit_unit" LLVMType.i64_ List.empty false in
            let unit_instr := LLVMInstruction.assign temp_unit unit_call in
            let unit_val := LLVMValue.var_ temp_unit in
            wrap_io_value_native_result_go ctx_unit unit_val (List.cons unit_instr List.empty) prior_val prior_instrs prior_blocks funcs globals,
    }

/// Non-void sibling of `wrap_void_native_result`: wraps an ALREADY-
/// COMPUTED value (`inner_val`, e.g. `read_file`'s real `char*`-as-`i64`
/// result) as `IO.io inner_val`, instead of always synthesizing a fresh
/// `Unit`. See `needs_io_wrap`'s own doc comment for why this is needed,
/// and `wrap_void_native_result`'s own doc comment for why `prior_val`
/// is required and `extra_pre_instrs` (empty except at the truthy-
/// pointer-to-`Bool` call site above, which must run its own
/// materialization instructions BEFORE the `IO.io` alloc) comes before
/// `prior_instrs`/`prior_blocks` positionally to match.
#[partial]
def wrap_io_value_native_result (ctx : CodegenCtx) (prior_val : LLVMValue) (extra_pre_instrs : List LLVMInstruction) (prior_instrs : List LLVMInstruction) (prior_blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) (inner_val : LLVMValue) : CompileResult :=
    wrap_io_value_native_result_go ctx inner_val extra_pre_instrs prior_val prior_instrs prior_blocks funcs globals

/// Shared tail for both wrap helpers above: `pre_instrs` computes
/// `inner_val` (empty when it's already computed), then both allocate the
/// `IO.io` constructor and set its one field -- all spliced via
/// `compose_seq` (matched against `prior_val`) rather than a raw
/// `List.append`, per `wrap_void_native_result`'s own doc comment.
#[partial]
def wrap_io_value_native_result_go (ctx : CodegenCtx) (inner_val : LLVMValue) (pre_instrs : List LLVMInstruction) (prior_val : LLVMValue) (prior_instrs : List LLVMInstruction) (prior_blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) : CompileResult :=
    match fresh_temp ctx {
        CtxStrPair.mk ctx_io temp_io =>
            let alloc_val := LLVMValue.alloc_constructor (constructor_tag ctx "IO.io") (List.cons inner_val List.empty) in
            let alloc_instr := LLVMInstruction.assign temp_io alloc_val in
            match build_set_field_instrs (LLVMValue.var_ temp_io) (List.cons inner_val List.empty) 0 ctx_io {
                { ctx := ctx_set, instrs := set_instrs } =>
                    let wrap_instrs := List.append pre_instrs (List.cons alloc_instr set_instrs) in
                    match compose_seq ({ instrs := prior_instrs, blocks := prior_blocks, val := prior_val }) ({ instrs := wrap_instrs, blocks := List.empty, val := (LLVMValue.var_ temp_io) }) {
                        { instrs := all_instrs, blocks := all_blocks, val := final_val } =>
                            CompileResult.ok ctx_set all_instrs final_val all_blocks funcs globals,
                    },
            },
    }

#[partial]
def native_op_to_fn_name (op : NativeOp) : String := match op {
    NativeOp.op_add => "I64_add",
    NativeOp.op_sub => "I64_sub",
    NativeOp.op_mul => "I64_mul",
    NativeOp.op_sdiv => "I64_div",
    NativeOp.op_eq => "I64_eq",
    NativeOp.op_lt => "I64_lt",
    NativeOp.op_gt => "I64_gt",
    NativeOp.op_ne => "I64_ne",
    NativeOp.op_print_str => "monad_print_str",
    NativeOp.op_read_file => "monad_read_file",
    NativeOp.op_write_file => "monad_write_file",
    NativeOp.op_file_exists => "monad_file_exists",
    NativeOp.op_is_dir => "monad_is_dir",
    NativeOp.op_string_hash => "monad_string_hash",
    NativeOp.op_i64_to_string => "monad_i64_to_string",
}

/// `compile_native_app_db` is reached for ANY 2-arg saturated call whose
/// head resolves via `lookup_native_any` -- not just the 8 arithmetic/
/// comparison ops. `NativeOp.op_write_file` is the one IO op with arity 2
/// (`IO.write_file path content`, `init/io.mo`), so a real call like
/// `lang/main.mo`'s own `link_ir`'s `IO.write_file ir_path ir_text` reaches
/// here too -- `compile_native_val`/`fold_native_const` (only 8 arms, no IO
/// ops) used to be called UNCONDITIONALLY, panicking the Rust host
/// interpreter with a non-exhaustive match on `NativeOp.op_write_file`
/// (confirmed blocking `bootstrap compile lang/main.mo monad`'s self-
/// compile -- see `implementations/2026-08-29-native-io-op-non-exhaustive-
/// match-crash.md`). Route non-arithmetic ops to `emit_native_call2_instr`
/// instead, which calls the real runtime function.
#[partial]
def is_arith_native_op (op : NativeOp) : Bool := match op {
    NativeOp.op_add => true,
    NativeOp.op_sub => true,
    NativeOp.op_mul => true,
    NativeOp.op_sdiv => true,
    NativeOp.op_eq => true,
    NativeOp.op_ne => true,
    NativeOp.op_lt => true,
    NativeOp.op_gt => true,
    NativeOp.op_print_str => false,
    NativeOp.op_read_file => false,
    NativeOp.op_write_file => false,
    NativeOp.op_file_exists => false,
    NativeOp.op_is_dir => false,
    NativeOp.op_string_hash => false,
    NativeOp.op_i64_to_string => false,
}

/// `arg2`'s own compiled fragment (`instrs2`/`blocks2`/...) used to be
/// combined with `arg`'s via blind `List.append instrs2 instrs1`,
/// with `blocks`/`funcs`/`globals` from BOTH operands silently
/// DISCARDED entirely (`_ _ _` on both matches) -- i.e. this had the
/// same "dropped continuation" bug as every other combine site in this
/// file (see `compose_seq`'s own doc comment) AND an even more basic
/// one: any branching operand's own `then`/`else`/`merge` blocks were
/// thrown away outright, not merely misplaced. `a + (if p then 1 else
/// 2)`-shaped code -- and, since `==`/`<`/`>` are native ops too,
/// ordinary boolean comparisons wrapping a conditional -- hit this.
#[partial]
def compile_native_app_db (c : CodegenCtx) (op : NativeOp) (arg2 : Term) (arg : Term) : CompileResult :=
    match compile_db_term_ir c arg2 {
        CompileResult.ok ctx2 instrs2 val2 blocks2 funcs2 globals2 =>
            match compile_db_term_ir ctx2 arg {
                CompileResult.ok ctx1 instrs1 val1 blocks1 funcs1 globals1 =>
                    // `compose_seq_acc`: a PURE second operand (a literal --
                    // `triple_is_pure`) must keep `val2` as the running
                    // splice-target token; composing it anyway would rewrite a
                    // branching FIRST operand's terminal block to
                    // `ret <literal>` and strand the native op itself as dead
                    // code after its branch (`llvm_value_eq` refuses literal
                    // splice targets).
                    match compose_seq_acc ({ instrs := instrs2, blocks := blocks2, val := val2 }) ({ instrs := instrs1, blocks := blocks1, val := val1 }) {
                        { instrs := combined, blocks := all_blocks, val := last_val } =>
                            let all_funcs := List.append funcs2 funcs1 in
                            let all_globals := List.append globals2 globals1 in
                            if not (is_arith_native_op op) then
                                emit_native_call2_instr ctx1 op val2 val1 combined all_blocks all_funcs all_globals last_val
                            else
                            match extract_lit_from_val val2 {
                                Option.some n1 =>
                                    match extract_lit_from_val val1 {
                                        Option.some n2 =>
                                            CompileResult.ok ctx1 combined (fold_native_const op n1 n2) all_blocks all_funcs all_globals,
                                        Option.none =>
                                            emit_arith_instr ctx1 op val2 val1 combined all_blocks all_funcs all_globals last_val,
                                    },
                                Option.none =>
                                    emit_arith_instr ctx1 op val2 val1 combined all_blocks all_funcs all_globals last_val,
                            },
                    },
            },
    }

struct AppSpine {
    head : Term,
    args : List Term,
}

/// Walks a left-nested `Term.app` chain (`f a b c` desugars to
/// `App (App (App f a) b) c`) down to its non-App head, collecting
/// arguments in left-to-right call order. Needed so a multi-argument
/// call to a top-level def (which `compile_db_def_ir` already uncurries
/// into ONE N-ary LLVM function -- see its `collect_db_params`/
/// `strip_db_lams`) compiles to ONE call with every argument, instead of
/// one (wrong, single-argument) call per nested `Term.app`.
#[partial]
def flatten_app_spine (t : Term) : AppSpine :=
    flatten_app_spine_go t List.empty

#[partial]
def flatten_app_spine_go (t : Term) (acc : List Term) : AppSpine :=
    // Peels, for the same reason `flatten_call_spine_go` (`lang/scope.mo`)
    // does: an early-terminated spine emits the wrong call shape.
    match term_peel t {
        Term.app fun_ arg_ => flatten_app_spine_go fun_ (List.cons arg_ acc),
        _ => { head := term_peel t, args := acc },
    }

/// `last_val` is the running "last-known value" from `compose_seq`'s
/// own accumulation (see `compile_spine_args_go`) -- exposed so THIS
/// spine's own caller (`compile_general_db_call`) can keep correctly
/// splicing after it too, instead of losing track once the args are
/// fully combined.
struct SpineArgs {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
    blocks : List LLVMBasicBlock,
    funcs : List LLVMFunction,
    globals : List LLVMGlobal,
    vals : List LLVMValue,
    last_val : LLVMValue,
}

#[partial]
def compile_spine_args (c : CodegenCtx) (terms : List Term) : SpineArgs :=
    compile_spine_args_go c terms List.empty List.empty List.empty List.empty List.empty LLVMValue.void_val

/// Compile every argument term in a flattened spine, in order,
/// threading the ctx/instrs/blocks/funcs/globals accumulation through
/// each one -- same pattern `compile_ntv_args_go` uses for native calls,
/// just over a plain `List Term` (no `Option` wrapping needed).
///
/// Accumulator-style, sequencing each arg via `compose_seq_acc` (see
/// its own doc comment) instead of blindly
/// concatenating instrs -- this USED to combine the first arg's own
/// instrs with the WHOLE recursively-combined rest of the spine as one
/// flat step, which had no single value to splice against whenever the
/// REST covered more than one arg (a multi-arg spine has no one
/// "value"), so a branching arg followed by more arguments silently
/// dropped everything after it -- the exact bug `let x := (if/match) in
/// f x y z` hits (`let`s desugar to an application spine).
#[partial]
def compile_spine_args_go (c : CodegenCtx) (terms : List Term) (acc_instrs : List LLVMInstruction) (acc_blocks : List LLVMBasicBlock) (acc_funcs : List LLVMFunction) (acc_globals : List LLVMGlobal) (acc_vals : List LLVMValue) (acc_val : LLVMValue) : SpineArgs :=
    match terms {
        // Trailing comma load-bearing -- see `build_get_env_instrs`'s
        // doc comment (lang/codegen/emit.mo) for why.
        List.empty => { ctx := c, instrs := acc_instrs, blocks := acc_blocks, funcs := acc_funcs, globals := acc_globals, vals := (rev_vals acc_vals List.empty), last_val := acc_val },
        List.cons t rest =>
            match compile_db_term_ir c t {
                CompileResult.ok ctx1 instrs1 val1_raw blocks1 funcs1 globals1 =>
                    // `val1_raw` may be `LLVMValue.void_val` (e.g. `t`
                    // is `Term.hole`, do-notation's own implicit
                    // trailing `Monad.pure hole`) -- an ARGUMENT
                    // position can never legally be LLVM's own `void`
                    // (only a function's own return type may be
                    // `void`), so materialize a real Unit value first
                    // (see `materialize_void`'s own doc comment).
                    match materialize_void ctx1 val1_raw {
                        { ctx := ctx1m, instrs := void_instrs, val := val1_v } =>
                            match materialize_native_bool_arg ctx1m t val1_v {
                                { ctx := ctx1b, instrs := bool_instrs, val := val1 } =>
                                    let instrs1m := List.append instrs1 (List.append void_instrs bool_instrs) in
                                    // `compose_seq_acc` for the same reason as
                                    // `compile_ntv_args_go` above: a PURE arg
                                    // (literal/bare reference -- `triple_is_pure`)
                                    // must leave the accumulator untouched so
                                    // `acc_val` keeps identifying the block
                                    // execution is actually in (its own value
                                    // still reaches `acc_vals` below regardless).
                                    match compose_seq_acc ({ instrs := acc_instrs, blocks := acc_blocks, val := acc_val }) ({ instrs := instrs1m, blocks := blocks1, val := val1 }) {
                                        { instrs := new_instrs, blocks := new_blocks, val := new_val } =>
                                            compile_spine_args_go ctx1b rest
                                                new_instrs new_blocks
                                                (List.append acc_funcs funcs1)
                                                (List.append acc_globals globals1)
                                                (List.cons val1 acc_vals)
                                                new_val,
                                    },
                            },
                    },
            },
    }

/// Compiles a call spine's own `head` (the function being applied,
/// after `flatten_app_spine`) -- deliberately NOT the same as plain
/// `compile_db_term_ir`, which (as of the fix documented on its own
/// `Term.var` case above) now emits a real 0-arg CALL for a bare
/// global-name reference in ordinary VALUE position. `head` is a
/// CALLEE position: `compile_general_db_call`'s own caller (below)
/// needs the bare `LLVMValue.var_ <name>` shape back, unevaluated, so
/// it can build ONE outer call carrying all of `args` — calling `head`
/// itself first (0 args) and THEN trying to apply the result to
/// `args` would be wrong. Mirrors the exact bare-name-extraction shape
/// `try_compile_constructor_app_db`/`try_compile_inline_native_db`
/// already use for the same reason, generalized to the "plain
/// function, no constructor/native match" case those two don't cover.
#[partial]
def compile_call_head (c : CodegenCtx) (head : Term) : CompileResult :=
    match head {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id =>
                    match ctx_lookup_local c id {
                        Option.some _ => compile_db_term_ir c head,
                        Option.none =>
                            let name := symbol_identifier id in
                            let llvm_name := ref_symbol_name id in
                            // IS reachable: `try_compile_constructor_app_
                            // db` bails out to `Option.none` (falling
                            // through to here, via `compile_general_db_
                            // call`) whenever `is_constructor_var` is
                            // true but `ctx_lookup_arity` shows the SAME
                            // bare name is ALSO a real top-level def --
                            // see that function's own doc comment for
                            // why (a function/constructor bare-name
                            // collision). This check must stay in sync
                            // with that one: without the SAME `ctx_
                            // lookup_arity` guard here, a real function
                            // reaching this fallback would still get
                            // misclassified as a constructor right here
                            // instead, one level down.
                            let also_a_real_fn := match ctx_lookup_arity c llvm_name {
                                Option.some _ => true,
                                Option.none => false,
                            } in
                            if is_constructor_var c name && Bool.not also_a_real_fn
                            then compile_db_term_ir c head
                            else
                                // `fn_ref`, not `var_` -- this IS a
                                // statically-known callable global
                                // function name (not a local SSA
                                // register that merely happens to hold
                                // a runtime value) -- see `fn_ref`'s own
                                // doc comment, `lang/codegen/ir.mo`.
                                CompileResult.ok c List.empty (LLVMValue.fn_ref llvm_name) List.empty List.empty List.empty,
                    },
                DebugName.unnamed => compile_db_term_ir c head,
            },
        _ => compile_db_term_ir c head,
    }

#[partial]
def compile_general_db_call (c : CodegenCtx) (fun : Term) (arg : Term) : CompileResult :=
    match flatten_app_spine (Term.app fun arg) {
        { head, args } =>
            match compile_call_head c head {
                CompileResult.ok ctx_h_raw instrs_h_raw val_h_raw blocks_h funcs_h globals_h =>
                    // `head` -- a COMPUTED callee (a struct/dictionary
                    // field extraction, a branching expression, ...) --
                    // can compile to a raw `void_val`/native-`i1`, same as
                    // any other call-argument or branch-merge position
                    // (`materialize_branch_val`'s own doc comment). Left
                    // unmaterialized here, `combine_indirect_call` passed
                    // it straight through as `apply_closureN`'s own first
                    // argument -- `llc: void type only allowed for
                    // function results`, `call i64 @apply_closure3(void
                    // void, ...)`. Confirmed blocking `bootstrap compile
                    // lang/main.mo monad`'s self-compile once it got past
                    // the write_file/user-defined-constructor fixes.
                    match materialize_branch_val ctx_h_raw head instrs_h_raw val_h_raw {
                        { ctx := ctx_h, instrs := instrs_h, val := val_h } =>
                    match compile_spine_args ctx_h args {
                        { ctx := ctx_a, instrs := instrs_a, blocks := blocks_a, funcs := funcs_a, globals := globals_a, vals := vals_a, last_val := last_val_a } =>
                            // `compose_seq_acc`: an all-PURE spine (every
                            // argument a literal/bare reference --
                            // `triple_is_pure`) must keep `val_h` as the
                            // running splice-target token; composing it anyway
                            // would rewrite a BRANCHING callee's terminal
                            // block to `ret <last literal>` and strand the
                            // call itself as dead code after its branch.
                            match compose_seq_acc ({ instrs := instrs_h, blocks := blocks_h, val := val_h }) ({ instrs := instrs_a, blocks := blocks_a, val := last_val_a }) {
                                { instrs := combined, blocks := all_blocks, val := combined_val } =>
                                    let all_funcs := List.append funcs_h funcs_a in
                                    let all_globals := List.append globals_h globals_a in
                                    // Dispatch on `val_h` itself (WHICH
                                    // function to call), not
                                    // `combined_val` (compose_seq's own
                                    // "last known value", used only for
                                    // splicing purposes below).
                                    match val_h {
                                        // Only `fn_ref` -- produced
                                        // exclusively by `compile_call_head`'s
                                        // own bare-global-name-in-callee-
                                        // position bypass -- means the
                                        // callee is a statically-known
                                        // global function; see its own
                                        // doc comment (`lang/codegen/ir.mo`)
                                        // for why `var_` (an SSA local
                                        // register that may itself hold a
                                        // runtime closure value) must NOT
                                        // be treated the same way.
                                        LLVMValue.fn_ref name =>
                                            combine_direct_call_arity_checked ctx_a name vals_a combined all_blocks all_funcs all_globals combined_val,
                                        // Any other shape (`var_`, `parm_`,
                                        // or a computed value -- a struct/
                                        // dictionary field extraction, a
                                        // local holding a boxed function
                                        // value, ...) means the callee
                                        // isn't a statically-known global
                                        // name -- go through a real
                                        // indirect call (Phase 0 of
                                        // plans/bootstrapping/self-hosted-compiler.md's
                                        // dictionary-passing plan) instead
                                        // of silently producing `void_val`.
                                        _ =>
                                            combine_indirect_call ctx_a val_h vals_a combined all_blocks all_funcs all_globals combined_val,
                                    },
                            },
                    },
                    },
            },
    }

/// `arg_vals` holds every argument in the flattened call spine, in
/// order -- emits ONE call carrying all of them (see `flatten_app_spine`).
/// `last_val` is `compose_seq`'s own running "last-known value" from
/// combining the callee + every argument (`compile_general_db_call`) --
/// needed so the CALL instruction itself gets correctly spliced into a
/// branching callee/argument's own terminal block too, instead of just
/// everything BEFORE it.
#[partial]
def combine_direct_call (ctx_a : CodegenCtx) (name : String) (arg_vals : List LLVMValue) (combined : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) (last_val : LLVMValue) : CompileResult :=
    match fresh_temp ctx_a {
        CtxStrPair.mk ctx_t temp =>
            let call_instr := LLVMInstruction.assign temp
                (LLVMValue.call name LLVMType.i64_ arg_vals false) in
            match compose_seq ({ instrs := combined, blocks := blocks, val := last_val }) ({ instrs := (List.cons call_instr List.empty), blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                    CompileResult.ok ctx_t new_instrs (LLVMValue.var_ temp) new_blocks funcs globals,
            },
    }

/// `flatten_app_spine`'s own arg count is driven purely by the SOURCE
/// TERM's `Term.app` spine -- for an ordinary top-level def this always
/// matches the def's own REAL compiled arity (`collect_db_params`/
/// `build_arity_table`, both "count leading `Term.lam`s"), since both are
/// driven by the same source-level lambda chain. It does NOT match for a
/// def whose first param is `destructured` (`({ x, y } : T) (extra) :=
/// ...`, `lang/parser.mo`'s `lam_parsed_params_loop`): the desugared term
/// is only ONE leading `Term.lam` (the struct param) followed by a
/// `Literal.match_` whose case body holds the REST of the curried chain
/// as NESTED `Term.lam`s -- so the def's own compiled arity is 1
/// regardless of how many more params it logically has, while a call
/// site applying ALL of them (`use_it r_in 3`) still flattens to a
/// 2-arg spine. `combine_direct_call`'s blind `call @name(all_args)`
/// then emits an LLVM call with more args than `name`'s declared
/// signature -- confirmed via a minimal repro to silently return the
/// wrong (garbage-looking, boxed-closure-as-if-it-were-a-plain-i64)
/// value rather than fail to link, discovered chasing `elaborate_def_
/// with_scope`'s identically-shaped `({ name, typ, term := body, ... } :
/// Def) (scope) (locals)` once the `@body` unresolved-capture bug
/// (`lang/typecheck/infer.mo`'s `type_check_field_pattern_case`) was
/// fixed and self-compile progressed far enough to actually call it.
/// Splits the flattened args at the callee's REAL arity (when known and
/// smaller than the spine) -- the first `real_arity` go into one direct
/// call, matching `name`'s true declared signature; everything past that
/// applies one arg at a time (`apply_extra_args_one_by_one`) against the
/// direct call's own result, which -- per `lam_parsed_params_loop`'s own
/// desugaring -- is exactly a boxed closure expecting the NEXT curried
/// param, mirroring how `compile_call_head`'s "arity>0 def referenced as
/// a value" case already boxes a shim for the identical currying shape.
/// Falls through to the original unconditional behavior whenever arity
/// is unknown or already matches/exceeds the spine (the overwhelming
/// common case) -- this only changes behavior for genuine over-
/// application of an under-arity compiled function.
#[partial]
def combine_direct_call_arity_checked (ctx_a : CodegenCtx) (name : String) (arg_vals : List LLVMValue) (combined : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) (last_val : LLVMValue) : CompileResult :=
    match ctx_lookup_arity ctx_a name {
        Option.some real_arity =>
            let supplied := List.length arg_vals in
            if I64.gt supplied real_arity then
                let direct_args := take_vals real_arity arg_vals in
                let extra_args := drop_vals real_arity arg_vals in
                match combine_direct_call ctx_a name direct_args combined blocks funcs globals last_val {
                    CompileResult.ok ctx_d instrs_d val_d blocks_d funcs_d globals_d =>
                        apply_extra_args_one_by_one ctx_d val_d extra_args instrs_d blocks_d funcs_d globals_d,
                }
            else if I64.lt supplied real_arity then
                // UNDER-application: a genuine partial application of a
                // direct top-level function reference (e.g. `load_scope_
                // entry ""`, passed as `load_dependency_entries`'s own
                // `loader` param by `lang/module.mo`'s since-deleted
                // `build_prelude_init_base`, later invoked via
                // `apply_closure1`). Previously
                // fell through to the `else` branch below unconditionally
                // -- `combine_direct_call` blindly emits `call @name(<all
                // supplied args>)` with FEWER arguments than `name`'s own
                // real declared LLVM signature. This is invalid IR (an
                // arg-count mismatch against the callee's own signature),
                // but this project's own `link_ir` step passes clang
                // `-disable-llvm-verifier`, so it links and runs anyway
                // -- the missing parameter register(s) inside `name` just
                // read whatever an EARLIER, unrelated call happened to
                // leave there, silently corrupting execution instead of
                // failing to compile. Confirmed as the real cause of a
                // live self-compile SIGSEGV inside `monad_get_tag`
                // (traced through `build_prelude_init_base` ->
                // `load_scope_entry ""` -> `module_path_to_file`: the
                // leftover register held a stale `List ModulePath`
                // instead of the missing `mp : ModulePath` argument) via
                // a minimal direct repro (a 2-arg def partially applied
                // to 1 arg and called through an intermediate function,
                // SIGSEGVs before this fix). Boxes a genuine closure
                // instead -- mirrors `compile_db_term_ir`'s own "arity>0
                // def referenced as a bare value" case (`Term.var`, ZERO
                // supplied args) and `build_closure_shim_func` just
                // above, generalized to `supplied > 0`: the already-
                // supplied args become the closure's own captures
                // (`build_set_env_instrs`, same as any other closure with
                // real captures), and its own declared arity is only the
                // REMAINING (`real_arity - supplied`) args still needed.
                combine_partial_apply ctx_a name arg_vals real_arity combined blocks funcs globals last_val
            else
                combine_direct_call ctx_a name arg_vals combined blocks funcs globals last_val,
        Option.none =>
            combine_direct_call ctx_a name arg_vals combined blocks funcs globals last_val,
    }

/// First `n` values, or the whole list if it has fewer than `n`.
#[partial]
def take_vals (n : I64) (xs : List LLVMValue) : List LLVMValue :=
    if I64.lt n 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons v rest => List.cons v (take_vals (n - 1) rest),
    }

/// Everything after the first `n` values.
#[partial]
def drop_vals (n : I64) (xs : List LLVMValue) : List LLVMValue :=
    if I64.lt n 1 then xs
    else match xs {
        List.empty => List.empty,
        List.cons _v rest => drop_vals (n - 1) rest,
    }

/// Applies each of `extra_args`, one at a time, to the running callee
/// value -- see `combine_direct_call_arity_checked`'s own doc comment.
/// Each step is a single-arg `combine_indirect_call` (its own trampoline
/// name is `apply_closure<List.length arg_vals>`, so passing exactly one
/// arg per step always picks `apply_closure1`, matching how each
/// remaining curried param was lifted as its OWN separate one-param
/// closure, never fused with its siblings).
#[partial]
def apply_extra_args_one_by_one (ctx : CodegenCtx) (callee_val : LLVMValue) (extra_args : List LLVMValue) (instrs : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) : CompileResult :=
    match extra_args {
        List.empty => CompileResult.ok ctx instrs callee_val blocks funcs globals,
        List.cons arg rest =>
            let one_arg : List LLVMValue := List.cons arg List.empty in
            match combine_indirect_call ctx callee_val one_arg instrs blocks funcs globals callee_val {
                CompileResult.ok ctx2 instrs2 val2 blocks2 funcs2 globals2 =>
                    apply_extra_args_one_by_one ctx2 val2 rest instrs2 blocks2 funcs2 globals2,
            },
    }

/// Indirect calls -- through a `parm_`-shaped value (a function passed
/// in as an argument) or any other computed callee value (a struct/
/// dictionary field extraction, a local bound to a boxed function value,
/// ...) that isn't a statically-known global name -- go through a
/// fixed-arity `apply_closureN` runtime trampoline (`runtime.c`, N =
/// this call's own real arg count), keyed off the SAME boxed-closure
/// representation `Term.var`'s value-position case now produces for an
/// arity>0 global reference (`compile_db_term_ir`, `alloc_closure`) --
/// Phase 0 of plans/bootstrapping/self-hosted-compiler.md's
/// dictionary-passing plan. This is the "fuller closure-application
/// scheme" a previous version of this function's own doc comment called
/// for and deferred (it used to call a single-argument `apply_fun`
/// trampoline that was never actually defined in `runtime.c` -- always
/// broken, never reachable from any real call graph until now).
/// `callee_val` is `val_h` from `compile_general_db_call` -- the
/// compiled callee itself, passed as `apply_closureN`'s own first
/// argument (a previous version of this function ignored `val_h`
/// entirely and mis-called `apply_fun` with only the first ordinary
/// arg, never the callee -- confirmed broken by inspection, never
/// exercised). `last_val` -- see `combine_direct_call`'s own doc comment.
#[partial]
def combine_indirect_call (ctx_a : CodegenCtx) (callee_val : LLVMValue) (arg_vals : List LLVMValue) (combined : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) (last_val : LLVMValue) : CompileResult :=
    let trampoline_name := String.concat "apply_closure" (I64.to_string (List.length arg_vals)) in
    match fresh_temp ctx_a {
        CtxStrPair.mk ctx_t temp =>
            let call_instr := LLVMInstruction.assign temp
                (LLVMValue.call trampoline_name LLVMType.i64_ (List.cons callee_val arg_vals) false) in
            match compose_seq ({ instrs := combined, blocks := blocks, val := last_val }) ({ instrs := (List.cons call_instr List.empty), blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                    CompileResult.ok ctx_t new_instrs (LLVMValue.var_ temp) new_blocks funcs globals,
            },
    }

/// `blocks`/`funcs`/`globals`/`last_val` -- see `compile_native_app_db`'s
/// own doc comment: threaded through (no longer discarded), and
/// `last_val` lets the arithmetic instruction itself be correctly
/// spliced into a branching operand's own terminal block via
/// `compose_seq`, instead of blindly appended after it.
#[partial]
def emit_arith_instr (c : CodegenCtx) (op : NativeOp) (lhs : LLVMValue) (rhs : LLVMValue) (instrs : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) (last_val : LLVMValue) : CompileResult :=
    match fresh_temp c {
        CtxStrPair.mk new_ctx temp =>
            let arith_val := compile_native_val op lhs rhs in
            let arith_instr := LLVMInstruction.assign temp arith_val in
            match compose_seq ({ instrs := instrs, blocks := blocks, val := last_val }) ({ instrs := (List.cons arith_instr List.empty), blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                    CompileResult.ok new_ctx new_instrs (LLVMValue.var_ temp) new_blocks funcs globals,
            },
    }

/// Non-arithmetic sibling of `emit_arith_instr` for `compile_native_app_db`
/// (see its own doc comment for why): `arg1_val`/`arg2_val` are the two
/// already-compiled operand values in call order (`arg1_val` first).
///
/// `NativeOp.op_write_file` needs special handling: `monad_write_file`'s
/// real C signature is `(path, data, len)` (`lang/codegen/runtime.c`), but
/// the mo-level call (`IO.write_file path content`, `init/io.mo`) only
/// supplies 2 args -- `len` must be computed here via `monad_string_length`
/// first, or the runtime call reads a garbage length from an unset
/// register and `fwrite`s garbage. Every other non-arithmetic op that
/// could reach this path is a plain 2-arg runtime call (none do today --
/// the remaining IO ops are all arity-1, handled by
/// `compile_native_app_unary_db` -- kept generic rather than crashing).
#[partial]
def emit_native_call2_instr (c : CodegenCtx) (op : NativeOp) (arg1_val : LLVMValue) (arg2_val : LLVMValue) (instrs : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) (last_val : LLVMValue) : CompileResult :=
    match op {
        NativeOp.op_write_file =>
            match fresh_temp c {
                CtxStrPair.mk ctx_len temp_len =>
                    let len_call := LLVMValue.call "monad_string_length" LLVMType.i64_ (List.cons arg2_val List.empty) false in
                    let len_instr := LLVMInstruction.assign temp_len len_call in
                    match fresh_temp ctx_len {
                        CtxStrPair.mk new_ctx temp =>
                            let write_call := LLVMValue.call "monad_write_file" LLVMType.i64_ (List.cons arg1_val (List.cons arg2_val (List.cons (LLVMValue.var_ temp_len) List.empty))) false in
                            let write_instr := LLVMInstruction.assign temp write_call in
                            match compose_seq ({ instrs := instrs, blocks := blocks, val := last_val }) ({ instrs := (List.cons len_instr (List.cons write_instr List.empty)), blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                                { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                                    wrap_void_native_result new_ctx (LLVMValue.var_ temp) new_instrs new_blocks funcs globals,
                            },
                    },
            },
        _ =>
            match fresh_temp c {
                CtxStrPair.mk new_ctx temp =>
                    let fn_name := native_op_to_fn_name op in
                    let call_val := LLVMValue.call fn_name LLVMType.i64_ (List.cons arg1_val (List.cons arg2_val List.empty)) false in
                    let call_instr := LLVMInstruction.assign temp call_val in
                    match compose_seq ({ instrs := instrs, blocks := blocks, val := last_val }) ({ instrs := (List.cons call_instr List.empty), blocks := List.empty, val := (LLVMValue.var_ temp) }) {
                        { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                            if is_void_native op then
                                wrap_void_native_result new_ctx (LLVMValue.var_ temp) new_instrs new_blocks funcs globals
                            else if needs_io_wrap op then
                                wrap_io_value_native_result new_ctx (LLVMValue.var_ temp) List.empty new_instrs new_blocks funcs globals (LLVMValue.var_ temp)
                            else
                                CompileResult.ok new_ctx new_instrs (LLVMValue.var_ temp) new_blocks funcs globals,
                    },
            },
    }

#[partial]
def extract_lit_from_val (val : LLVMValue) : Option I64 := match val {
    LLVMValue.int_ n => Option.some n,
    LLVMValue.int32_ n => Option.none,
    LLVMValue.bool_ b => Option.none,
    LLVMValue.void_val => Option.none,
    LLVMValue.var_ name => Option.none,
    LLVMValue.parm_ idx => Option.none,
    LLVMValue.global_ name => Option.none,
    LLVMValue.fn_ref name => Option.none,
    LLVMValue.call fn_name ret_ty args tail => Option.none,
    LLVMValue.add lhs rhs => Option.none,
    LLVMValue.sub lhs rhs => Option.none,
    LLVMValue.mul lhs rhs => Option.none,
    LLVMValue.sdiv lhs rhs => Option.none,
    LLVMValue.udiv lhs rhs => Option.none,
    LLVMValue.urem lhs rhs => Option.none,
    LLVMValue.icmp_eq lhs rhs => Option.none,
    LLVMValue.icmp_ne lhs rhs => Option.none,
    LLVMValue.icmp_slt lhs rhs => Option.none,
    LLVMValue.icmp_sgt lhs rhs => Option.none,
    LLVMValue.icmp_ult lhs rhs => Option.none,
    LLVMValue.icmp_ugt lhs rhs => Option.none,
    LLVMValue.zext val from_ty to_ty => Option.none,
    LLVMValue.trunc val from_ty to_ty => Option.none,
    LLVMValue.ptrtoint val from_ty to_ty => Option.none,
    LLVMValue.inttoptr val from_ty to_ty => Option.none,
    LLVMValue.phi pairs => Option.none,
    LLVMValue.gep base indices => Option.none,
    LLVMValue.load _ty _pty ptr => Option.none,
    LLVMValue.bitcast val ty => Option.none,
    LLVMValue.alloc_closure entry arity env_size => Option.none,
    LLVMValue.alloc_constructor tag field_count => Option.none,
    LLVMValue.native_op op args => Option.none,
}

#[partial]
def append_blocks (a : List LLVMBasicBlock) (b : List LLVMBasicBlock) : List LLVMBasicBlock := match a {
    List.empty => b,
    List.cons hd tl => List.cons hd (append_blocks tl b),
}

#[partial]
def param_name_db (p : Param) : Identifier := match p {
    Param.mk name typ_ mult default _attrs => name,
}

struct DefResult {
    ctx : CodegenCtx,
    funcs : List LLVMFunction,
    globals : List LLVMGlobal,
}

#[partial]
def build_llvm_params_db (params : List Param) : List ParamPair :=
    build_llvm_params_from_db params 0

#[partial]
def build_llvm_params_from_db (params : List Param) (idx : I64) : List ParamPair := match params {
    List.empty => List.empty,
    List.cons p rest =>
        let pp := ParamPair.mk (String.concat "p" (I64.to_string idx)) LLVMType.i64_ in
        List.cons pp (build_llvm_params_from_db rest (idx + 1)),
}

/// Whether `t`'s head (after peeling any `Term.app` spine, matching
/// `lang/typecheck/infer.mo`'s own `type_head_name` convention) is
/// literally named `IO` — i.e. `t` is (an application of) the `IO`
/// type, e.g. `IO I64`.
///
/// `t` here is a `Def`'s FULL `typ` field, not just the bare
/// return-type expression after `:` — `lang/parser.mo`'s
/// `build_param_pi_chain` (its own doc comment explains why) folds
/// every param's type into `typ` as a `Term.pi` chain, so
/// `def main (args : List String) : IO I64 := ...` has `typ` shaped
/// `Term.pi <List String> (IO I64 application)`, `Term.pi`-headed, not
/// `Term.app`/`Term.var`-headed. Strip those leading binders first
/// (`strip_all_leading_binders`, `lang.scope` — the same helper
/// `full_return_carrier`/`resolve_class_calls_decls_go` already use for
/// this exact "get a def's return-type carrier out of a full
/// param-including typ" problem) or this silently returns `false` for
/// any `main` with an explicit parameter, i.e. every realistic Monad
/// `main` — confirmed as a real, previously-undiagnosed bug: with this
/// check wrongly `false`, `main`'s returned `IO.io` pointer never gets
/// unwrapped (see `unwrap_io_return_blocks` below), so the raw boxed
/// pointer reaches the C runtime's plain-`int` `main()` and the process
/// exits a garbage code with no output at all.
#[partial]
def emit_type_head_is_io (t : Term) : Bool :=
    emit_type_head_is_io_go (strip_all_leading_binders t)

#[partial]
def emit_type_head_is_io_go (t : Term) : Bool := match t {
    Term.var _idx dbg => match dbg {
        DebugName.named id_ => String.beq (symbol_identifier id_) "IO",
        DebugName.unnamed => false,
    },
    Term.app f _arg => emit_type_head_is_io_go f,
    _ => false,
}

/// Fixes a genuine, previously-undiagnosed native-codegen bug: a `main`
/// declared `IO _` (e.g. `def main : IO I64 := IO.io 5`) used to have
/// its RAW returned pointer (a boxed `IO.io` constructor VALUE, from
/// `init/io.mo`'s `type IO A { io A }`) returned straight to the C
/// runtime's `int main() { return (int)main_monad(args); }`, which
/// casts it directly to `int` with no unwrapping at all — the process's
/// actual exit code ends up being whatever the low byte of a heap
/// pointer happens to be, not the `I64` the program's own source
/// intended. Confirmed fixed end-to-end (real `compile` + run, not just
/// IR-text inspection): `def main : IO I64 := IO.io 5` now genuinely
/// exits 5.
///
/// Fixed here, not in `runtime.c`: the C runtime has no way to tell a
/// raw returned `i64` apart from a boxed pointer (this runtime doesn't
/// tag scalars vs. pointers) — only codegen still has the STATIC type
/// (`typ`, this Def's own declared return type) needed to know which
/// case applies, and only for `main` specifically (an ordinary function
/// returning `IO T` to another Monad function is fine exactly as
/// compiled today — `IO`'s own `bind`/`pure` instance already knows how
/// to unwrap it; it's specifically the boundary into the plain-`int`
/// C `main` that needs this).
///
/// **Does NOT fix `{ ... }` do-notation bodies** — `def main : IO I64 {
/// return 5 }` (do-block sugar, as opposed to an ordinary expression)
/// is a SEPARATE, deeper, still-open gap: do-notation doesn't compile
/// its actual value to real IR at all, falling through to a meaningless
/// zero-field placeholder constructor regardless of this fix (confirmed
/// via the same real compile+run: exits 0, not 5, because `main`'s
/// whole body silently became `alloc_constructor(tag=0, fields=0)`
/// rather than anything derived from `return 5`). This is exactly the
/// pre-existing gap `lang/codegen/test_driver.mo`'s own doc comment
/// already flags ("do-notation/IO-typed main was apparently never
/// exercised through the compile-then-run path... worth its own future
/// investigation, but out of scope to fix generally here") — this fix
/// addresses the pointer-cast half of that comment's original garbled-
/// exit-code symptom, not the do-notation-codegen half.
///
/// Rewrites EVERY block that ends in a bare `ret v` (a function's body
/// can compile to several such blocks — one per branch of a top-level
/// `if`/`match`, see `compile_db_if_ir`/`compile_match_ir` — not just
/// one) to first call the runtime's own `monad_get_field(v, 0)` (field
/// 0 of a 1-field `IO.io` constructor is its payload) and return THAT
/// instead of the raw constructor pointer.
#[partial]
def unwrap_io_return_blocks (blocks : List LLVMBasicBlock) (idx : I64) : List LLVMBasicBlock := match blocks {
    List.empty => List.empty,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk label instrs =>
                let temp_name := String.concat "__io_unwrap" (I64.to_string idx) in
                let new_instrs := unwrap_io_return_instrs instrs temp_name in
                List.cons (LLVMBasicBlock.mk label new_instrs) (unwrap_io_return_blocks rest (I64.add idx 1)),
        },
}

/// Rewrites the LAST instruction in `instrs`, only if it's a bare
/// `LLVMInstruction.ret v` — every other instruction (and any block
/// that ends in `jump`/`branch` instead of `ret`, i.e. isn't itself a
/// return point) passes through unchanged.
#[partial]
def unwrap_io_return_instrs (instrs : List LLVMInstruction) (temp_name : String) : List LLVMInstruction := match instrs {
    List.empty => List.empty,
    List.cons i rest =>
        match rest {
            List.empty =>
                match i {
                    LLVMInstruction.ret v =>
                        let field_args := List.cons v (List.cons (LLVMValue.int_ 0) List.empty) in
                        let get_call := LLVMValue.call "monad_get_field" LLVMType.i64_ field_args false in
                        let assign := LLVMInstruction.assign temp_name get_call in
                        List.cons assign (List.cons (LLVMInstruction.ret (LLVMValue.var_ temp_name)) List.empty),
                    _ => List.cons i List.empty,
                },
            List.cons _ _ => List.cons i (unwrap_io_return_instrs rest temp_name),
        },
}

// ─── Self-recursive tail-call → loop rewrite (native stack-overflow
// safety) ───────────────────────────────────────────────────────────
//
// Monad's LLVM codegen had NO tail-call optimization at all: every call
// this backend emits (`combine_direct_call`/`combine_indirect_call`, ~34
// call-construction sites total) is an ordinary, non-tail LLVM `call`,
// even when the call is a function calling ITSELF as the literal last
// thing it does on some path (`remove_quotes_loop`, `replace_dots_loop`,
// `check_contains`, `build_arity_table_go`, ... -- every `*_loop`/`*_go`
// helper in this self-hosted compiler's own source). `ir.mo`'s
// `LLVMValue.call`'s own `tail : Bool` field already exists and `show_
// call` already renders it, but every call site hardwires it `false` --
// nothing anywhere detected tail position or self-recursion. The
// interpreted (Rust-host) execution path never hit this (`core_eval.rs`'s
// `eval()` is its own explicit trampoline, a `loop` over owned state, for
// exactly this reason), so it went undetected through this project's
// entire "0 errors"/"1368/1368"/"124/124" standard verification bar --
// only once the self-hosted compiler was compiled (not interpreted) and
// the resulting NATIVE binary actually ran deep enough to exercise one of
// these loops (once per character/def across this compiler's own ~50k-
// line source) did it manifest, as a native stack overflow (a SIGSEGV
// inside whatever ordinary function happened to be called next, once the
// C stack was exhausted -- `remove_quotes_loop` itself has a documented
// prior real repro of exactly this crash class, from an unrelated bug at
// the time). See plans/implementations/2026-08-31-self-tail-call-loop-
// rewrite.md for the full design writeup this implements.
//
// Fix (Lean-style, not relying on LLVM's own tail-call codegen or any
// `opt` pass -- this project's `llc` invocation runs neither): detect,
// per compiled `Def`, every call that is (a) a DIRECT, SATURATED
// (matching arity) call to that SAME Def's own compiled LLVM function
// name, and (b) in true tail position -- i.e. its result IS the value
// that ends up in the function's own terminal `ret`, possibly reached
// through a chain of `phi`s (a match/if's own merge). Rewrite each such
// call site into: update the function's own loop-carried "current
// parameter values" (materialized as fresh SSA vars fed by a `phi` at a
// new loop-header block, since LLVM function arguments are immutable
// single registers -- they can't be reassigned across a back-edge) and
// `br` back to that header, instead of making a real `call`. This runs as
// a POST-PASS over a Def's fully-composed block list, strictly after all
// of `compose_seq`/`splice_into_terminal_block`/`build_merge_result`/
// `retarget_terminal_ret`'s own work is done -- no interleaving with that
// machinery, so this can't affect (or be affected by) any of it.
//
// Deliberately SELF-recursion only (confirmed with the user before
// implementing): mutual tail recursion would need real LLVM
// `musttail` calls instead, which require the call to be immediately
// adjacent to its own `ret` -- incompatible with how this codebase's
// match/if compilation works today (a call's result always flows through
// a `phi`+merge, never a bare `ret <call>`). That's a materially riskier,
// separate follow-on, not implemented here -- code that used to rely on
// mutual tail loops (the parser's old `take_while_loop`/`take_while_check`
// pair, which blew the 8MB stack at ~11K input chars in compiled
// binaries) has instead been RESTRUCTURED to self-recursion
// (`lang/parser/combinators.mo`), which this pass handles.

// ─── Part 1: detection ──────────────────────────────────────────────

// ─── Part 2: rewrite ────────────────────────────────────────────────

/// A thin wrapper def: calls the native's own runtime function with
/// every one of `params` (positionally, `%p0`/`%p1`/... -- same naming
/// `build_llvm_params_db` already gives the function's own parameters),
/// then wraps its raw result per `kind` (see `NativeWrapKind`'s own doc
/// comment) before returning it.
#[partial]
def compile_native_def_wrapper_ir (c : CodegenCtx) (fn_name : String) (llvm_params : List ParamPair) (kind : NativeWrapKind) (params : List Param) : DefResult :=
    match kind {
        NativeWrapKind.passthrough rt_fn_name =>
            match fresh_temp c {
                CtxStrPair.mk ctx_t temp =>
                    let call_val := LLVMValue.call rt_fn_name LLVMType.i64_ (parm_values_for params) false in
                    let assign_instr := LLVMInstruction.assign temp call_val in
                    let entry_instrs := List.cons assign_instr (List.cons (LLVMInstruction.ret (LLVMValue.var_ temp)) List.empty) in
                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                    let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (List.cons entry_block List.empty) true Option.none in
                    { ctx := ctx_t, funcs := (List.cons native_func List.empty), globals := List.empty }
            },
        NativeWrapKind.bool_result rt_fn_name =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 raw_temp =>
                    match fresh_temp ctx1 {
                        CtxStrPair.mk ctx2 tag_temp =>
                            match fresh_temp ctx2 {
                                CtxStrPair.mk ctx3 con_temp =>
                                    let call_val := LLVMValue.call rt_fn_name LLVMType.i64_ (parm_values_for params) false in
                                    let raw_instr := LLVMInstruction.assign raw_temp call_val in
                                    // Bool.true/Bool.false are tags 1/2
                                    // (`constructor_tag`); raw_result is
                                    // 0 (false) or 1 (true) -- `2 -
                                    // raw_result` maps 1->1 (true),
                                    // 0->2 (false), avoiding a branch.
                                    let tag_val := LLVMValue.sub (LLVMValue.int_ 2) (LLVMValue.var_ raw_temp) in
                                    let tag_instr := LLVMInstruction.assign tag_temp tag_val in
                                    let con_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (List.cons (LLVMValue.var_ tag_temp) (List.cons (LLVMValue.int_ 0) List.empty)) false in
                                    let con_instr := LLVMInstruction.assign con_temp con_val in
                                    let entry_instrs := List.cons raw_instr (List.cons tag_instr (List.cons con_instr (List.cons (LLVMInstruction.ret (LLVMValue.var_ con_temp)) List.empty))) in
                                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                    let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (List.cons entry_block List.empty) true Option.none in
                                    { ctx := ctx3, funcs := (List.cons native_func List.empty), globals := List.empty }
                            },
                    },
            },
        NativeWrapKind.io_passthrough rt_fn_name =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 raw_temp =>
                    match fresh_temp ctx1 {
                        CtxStrPair.mk ctx2 io_temp =>
                            let call_val := LLVMValue.call rt_fn_name LLVMType.i64_ (parm_values_for params) false in
                            let raw_instr := LLVMInstruction.assign raw_temp call_val in
                            let alloc_val := LLVMValue.alloc_constructor (constructor_tag c "IO.io") (List.cons (LLVMValue.var_ raw_temp) List.empty) in
                            let alloc_instr := LLVMInstruction.assign io_temp alloc_val in
                            match build_set_field_instrs (LLVMValue.var_ io_temp) (List.cons (LLVMValue.var_ raw_temp) List.empty) 0 ctx2 {
                                { ctx := ctx_set, instrs := set_instrs } =>
                                    let entry_instrs := List.cons raw_instr (List.cons alloc_instr (List.append set_instrs (List.cons (LLVMInstruction.ret (LLVMValue.var_ io_temp)) List.empty))) in
                                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                    let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (List.cons entry_block List.empty) true Option.none in
                                    { ctx := ctx_set, funcs := (List.cons native_func List.empty), globals := List.empty }
                            },
                    },
            },
        NativeWrapKind.io_truthy_ptr_bool_result rt_fn_name =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 raw_temp =>
                    let call_val := LLVMValue.call rt_fn_name LLVMType.i64_ (parm_values_for params) false in
                    let raw_instr := LLVMInstruction.assign raw_temp call_val in
                    match materialize_truthy_ptr_as_bool ctx1 (LLVMValue.var_ raw_temp) {
                        { ctx := ctx2, instrs := bool_instrs, val := bool_val } =>
                            match fresh_temp ctx2 {
                                CtxStrPair.mk ctx3 io_temp =>
                                    let alloc_val := LLVMValue.alloc_constructor (constructor_tag c "IO.io") (List.cons bool_val List.empty) in
                                    let alloc_instr := LLVMInstruction.assign io_temp alloc_val in
                                    match build_set_field_instrs (LLVMValue.var_ io_temp) (List.cons bool_val List.empty) 0 ctx3 {
                                        { ctx := ctx_set, instrs := set_instrs } =>
                                            let entry_instrs := List.cons raw_instr (List.append bool_instrs (List.cons alloc_instr (List.append set_instrs (List.cons (LLVMInstruction.ret (LLVMValue.var_ io_temp)) List.empty)))) in
                                            let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                            let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (List.cons entry_block List.empty) true Option.none in
                                            { ctx := ctx_set, funcs := (List.cons native_func List.empty), globals := List.empty }
                                    },
                            },
                    },
            },
        NativeWrapKind.io_write_file rt_fn_name =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 len_temp =>
                    let len_call := LLVMValue.call "monad_string_length" LLVMType.i64_ (List.cons (LLVMValue.parm_ 1) List.empty) false in
                    let len_instr := LLVMInstruction.assign len_temp len_call in
                    match fresh_temp ctx1 {
                        CtxStrPair.mk ctx2 write_temp =>
                            let write_call := LLVMValue.call rt_fn_name LLVMType.i64_ (List.cons (LLVMValue.parm_ 0) (List.cons (LLVMValue.parm_ 1) (List.cons (LLVMValue.var_ len_temp) List.empty))) false in
                            let write_instr := LLVMInstruction.assign write_temp write_call in
                            match fresh_temp ctx2 {
                                CtxStrPair.mk ctx3 unit_temp =>
                                    let unit_call := LLVMValue.call "monad_ctor_Unit_unit" LLVMType.i64_ List.empty false in
                                    let unit_instr := LLVMInstruction.assign unit_temp unit_call in
                                    match fresh_temp ctx3 {
                                        CtxStrPair.mk ctx4 io_temp =>
                                            let alloc_val := LLVMValue.alloc_constructor (constructor_tag c "IO.io") (List.cons (LLVMValue.var_ unit_temp) List.empty) in
                                            let alloc_instr := LLVMInstruction.assign io_temp alloc_val in
                                            match build_set_field_instrs (LLVMValue.var_ io_temp) (List.cons (LLVMValue.var_ unit_temp) List.empty) 0 ctx4 {
                                                { ctx := ctx_set, instrs := set_instrs } =>
                                                    let entry_instrs := List.cons len_instr (List.cons write_instr (List.cons unit_instr (List.cons alloc_instr (List.append set_instrs (List.cons (LLVMInstruction.ret (LLVMValue.var_ io_temp)) List.empty))))) in
                                                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                                    let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (List.cons entry_block List.empty) true Option.none in
                                                    { ctx := ctx_set, funcs := (List.cons native_func List.empty), globals := List.empty }
                                            },
                                    },
                            },
                    },
            },
    }

#[partial]
def parm_values_for (params : List Param) : List LLVMValue := parm_values_for_go params 0

#[partial]
def parm_values_for_go (params : List Param) (idx : I64) : List LLVMValue :=
    match params {
        List.empty => List.empty,
        List.cons _ rest => List.cons (LLVMValue.parm_ idx) (parm_values_for_go rest (idx + 1)),
    }

struct TerminalBlocks {
    ctx : CodegenCtx,
    blocks : List LLVMBasicBlock,
}

/// A def body whose final value lives inside its own merge/case block
/// (the `compose_seq` convention: a branching sub-term's LAST appended
/// block is closed with `ret <its own reported val>`) never reaches the
/// boxing `materialize_branch_val` gives the plain-`ret` path -- with the
/// entry instruction list already ending in a terminator,
/// `compile_db_def_ir_body` keeps the blocks as-is and that block's own
/// `ret` is the function's REAL return. When the body is a native Bool
/// comparison (`I64.beq`/`.lt`/...) composed after a BRANCHING operand --
/// a struct field access: `lang.types::parse_span_is_unknown :=
/// I64.beq sp.start_rem -1` is the live self-compile case, its field
/// access building the `entry`/`check`/`merge` block chain -- the
/// comparison's `icmp` was spliced into that very block and it re-closed
/// with `ret <raw i1>`, the ONE value position
/// `materialize_native_bool_arg` never sees. `llc` rejects the function:
/// `'%tN' defined with type 'i1' but expected 'i64'` (same class as the
/// call-argument hole documented at `materialize_native_bool_arg` above;
/// that fix's own repro had a PURE operand, so it missed this
/// branching-operand combination).
///
/// Fix: when `already_terminated`, box the tail exactly as call arguments
/// and phi operands already are, splicing the boxing into the terminal
/// block so its own `ret` closes with the boxed Bool constructor instead.
/// A total no-op (ctx/blocks returned unchanged) whenever the body is not
/// a native comparison, and a safe fallback too when no block ends in
/// `ret <val>` (that would violate `compile_db_if_ir`/`compile_match_ir`'s
/// own closing invariant; kept non-crashing to match `compose_seq`'s
/// stance on the same impossibility).
///
/// Residual gap, noted not fixed: a body shaped
/// `let x := <branching> in I64.beq ...` reaches the same hole with a
/// let-shaped body `term_is_native_bool_op` answers `false` to. Nothing
/// in the corpus hits it today; fixing blind would mean guessing.
#[partial]
def materialize_terminal_ret (already_terminated : Bool) (ctx : CodegenCtx) (term_ : Term) (val : LLVMValue) (blocks : List LLVMBasicBlock) : TerminalBlocks :=
    if not already_terminated
    then { ctx := ctx, blocks := blocks }
    else
        match materialize_native_bool_arg ctx term_ val {
            { ctx := ctx1, instrs := box_instrs, val := boxed } =>
                match box_instrs {
                    List.empty => { ctx := ctx, blocks := blocks },
                    List.cons _ _ =>
                        match splice_into_terminal_block blocks val box_instrs boxed {
                            Option.some rewritten => { ctx := ctx1, blocks := rewritten },
                            Option.none => { ctx := ctx, blocks := blocks },
                        },
                },
        }

/// Compile a canonical Def (de Bruijn Term) to LLVM IR.
#[partial]
def compile_db_def_ir (c : CodegenCtx) (def_ : Def) : DefResult := match def_ {
    Def.mk name typ term_ constraints attrs _vis =>
        // Must match Term.var's call-site naming exactly -- both ends go
        // through the `def_symbol_name`/`ref_symbol_name` pair for
        // exactly that reason. The last time they diverged, a dotted
        // top-level name like "Option.get_or_default" defined itself as
        // LLVM function "Option.get_or_default" while every CALL to it
        // emitted "Option_get_or_default": an "undefined value" link
        // error the first time a real program called a dotted def name.
        // `validate_all_call_targets_defined` now catches that class
        // before `llc` ever sees it.
        let fn_name := def_symbol_name name in
        let params := collect_db_params term_ in
        let llvm_params := build_llvm_params_db params in
        match native_runtime_fn_name attrs {
            Option.some wrap_kind => compile_native_def_wrapper_ir c fn_name llvm_params wrap_kind params,
            Option.none => compile_db_def_ir_body c fn_name typ term_ params llvm_params,
        },
}

/// The def's OWN `!DISubprogram` location, from the position recorded on
/// its body's outermost term.
///
/// A decl-span entry would start at the declaration's ATTRIBUTES:
/// `factorial` would report line 3 (`#[terminating]`), not line 4
/// (`def factorial`). The body's wrapper position is the line a user
/// actually wants to land on, and it skips the attributes for free.
/// `strip_db_lams` (which produced `body`) keeps the wrapper on the
/// term it lands on -- see its own comment in
/// `lang/codegen/validate.mo` -- so this reads the position directly.
///
/// `Option.none` when the body carries no wrapper -- only possible when
/// its module's located parse failed outright (`locate_module_info`
/// keeps the plain decls): the function then gets no line info, which
/// is the same best-effort behavior the v1 name-keyed table's miss
/// path had.
#[partial]
def dbg_loc_of_body (body : Term) : Option DbgLoc :=
    match body {
        Term.ctx loc _ => dbg_loc_of_location loc,
        _ => Option.none,
    }

#[partial]
def compile_db_def_ir_body (c : CodegenCtx) (fn_name : String) (typ : Term) (term_ : Term) (params : List Param) (llvm_params : List ParamPair) : DefResult :=
        let body := strip_db_lams term_ in
        let c0 := bind_params_in_ctx_db c params in
        // See `unwrap_io_return_blocks`'s own doc comment: an `IO`-typed
        // `main` needs its returned value's payload unwrapped before it
        // reaches the C runtime's plain-`int`-returning `main()`.
        let needs_io_unwrap := ends_with_main fn_name && emit_type_head_is_io typ in
        match compile_db_term_ir c0 body {
            CompileResult.ok ctx_r instrs_r val_r blocks_r funcs_r globals_r =>
                match val_r {
                    LLVMValue.void_val =>
                        match fresh_temp ctx_r {
                            CtxStrPair.mk ctx_t temp =>
                                // Create a call to alloc_constructor with tag 0 (Unit) and 0 fields
                                // This ensures we return a proper i64 value that represents Unit
                                let zero_val := LLVMValue.int_ 0 in
                                let unit_val := LLVMValue.alloc_constructor 0 List.empty in
                                let assign := LLVMInstruction.assign temp unit_val in
                                let new_instrs := List.append instrs_r (List.cons assign List.empty) in
                                let entry_instrs := List.append new_instrs (List.cons (LLVMInstruction.ret (LLVMValue.var_ temp)) List.empty) in
                                let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                let all_blocks_raw := append_blocks (List.cons entry_block List.empty) blocks_r in
                                let tco := apply_self_tco ctx_t fn_name (List.length llvm_params) all_blocks_raw in
                                // `tco.ctx`/`tco.blocks` bound ONCE here,
                                // not inlined into each if/else arm below
                                // -- a struct field access is itself a
                                // branching (single-constructor-match-
                                // shaped) sub-term, and evaluating it a
                                // SECOND time inside a sibling arm of the
                                // very `if` that consumes it (rather than
                                // once, before the `if`) hit a genuine,
                                // separate compose_seq-splicing gap here
                                // (confirmed live via a real self-compile:
                                // `llc`'s verifier rejected the result --
                                // "PHINode should have one entry for each
                                // predecessor", dead code stranded after
                                // an unrelated terminator). Binding once
                                // avoids the whole class, matching how
                                // every other multi-field struct result in
                                // this file (`bmr.val`/`bmr.instrs`, ...)
                                // is already used.
                                let tco_ctx := tco.ctx in
                                let tco_blocks := tco.blocks in
                                let all_blocks := if needs_io_unwrap then unwrap_io_return_blocks tco_blocks 0 else tco_blocks in
                                let main_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ all_blocks true (dbg_loc_of_body body) in
                                { ctx := tco_ctx, funcs := (List.cons main_func funcs_r), globals := globals_r }
                        },
                    _ =>
                        // A def whose whole (stripped-of-params) body is
                        // itself an if/match (e.g. List.last, List.is_empty,
                        // Option.get_or_default -- each just one top-level
                        // match) compiles `instrs_r` already ending in its
                        // OWN terminator (a jump/branch into the if/match's
                        // own block chain, which itself ends in `ret`).
                        // Unconditionally appending another `ret val_r`
                        // after that would put two terminators in one
                        // block (invalid LLVM IR) and reference `val_r`
                        // (e.g. a match's phi temp) outside the block it's
                        // actually defined in. Only append `ret` when the
                        // body is a plain, non-branching computation.
                        //
                        // A body that's a BARE native comparison (e.g.
                        // `String.is_empty s := I64.beq (String.length s)
                        // 0`) needs the same boxing `materialize_branch_
                        // val`/`materialize_native_bool_arg` already give
                        // call arguments/let-bindings/if-branches -- `ret`,
                        // like `phi` and an ordinary call argument, doesn't
                        // tolerate a raw `i1` declared as `i64` either.
                        // Confirmed via a direct repro (`line_col_scan_
                        // direct`'s own `String.is_empty` call):
                        // `llc: '%tN' defined with type 'i1' but expected
                        // 'i64'` at the `ret i64 %tN` itself.
                        let already_terminated := ends_with_terminator instrs_r in
                        let bmr := materialize_branch_val ctx_r body instrs_r val_r in
                        // With the value living in a terminal block,
                        // `materialize_branch_val` above short-circuited
                        // and never boxed -- box that block's own `ret`
                        // instead (see `materialize_terminal_ret`'s doc
                        // comment for the raw-i1 hole this closes).
                        let tb := materialize_terminal_ret already_terminated bmr.ctx body val_r blocks_r in
                        let entry_instrs :=
                            if already_terminated
                            then instrs_r
                            else List.append bmr.instrs (List.cons (LLVMInstruction.ret bmr.val) List.empty) in
                        let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                        let all_blocks_raw := append_blocks (List.cons entry_block List.empty) tb.blocks in
                        let tco := apply_self_tco tb.ctx fn_name (List.length llvm_params) all_blocks_raw in
                        // See the `void_val` arm above for why `tco.ctx`/
                        // `tco.blocks` are bound once here rather than
                        // inlined into each `if`/else arm.
                        let tco_ctx := tco.ctx in
                        let tco_blocks := tco.blocks in
                        let all_blocks := if needs_io_unwrap then unwrap_io_return_blocks tco_blocks 0 else tco_blocks in
                        let main_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ all_blocks true (dbg_loc_of_body body) in
                        { ctx := tco_ctx, funcs := (List.cons main_func funcs_r), globals := globals_r }
                },
        }

/// Compile a list of canonical Defs to LLVM functions.
#[partial]
def compile_db_def_list (c : CodegenCtx) (defs : List Def) : DefResult := match defs {
    // Trailing comma load-bearing -- see `build_get_env_instrs`'s doc
    // comment above for why.
    List.empty => { ctx := c, funcs := List.empty, globals := List.empty },
    List.cons d rest =>
        match compile_db_def_ir c d {
            { ctx := ctx_d, funcs := funcs_d, globals := globals_d } =>
                match compile_db_def_list ctx_d rest {
                    { ctx := ctx_rest, funcs := funcs_rest, globals := globals_rest } =>
                        { ctx := ctx_rest, funcs := (List.append funcs_d funcs_rest), globals := (List.append globals_d globals_rest) }
                },
        },
}

/// Compile a list of canonical Defs to a complete LLVM module.
#[partial]
def compile_db_decls_ir (defs : List Def) : LLVMModule :=
    compile_db_decls_ir_with_debug defs Option.none List.empty

/// `compile_db_decls_ir`, with DWARF debug info (one location per
/// top-level def, from the `Term.ctx` wrapper on its body -- see
/// `dbg_loc_of_body`). A sibling function rather than new params on
/// `compile_db_decls_ir` itself: that function has ~90 existing
/// single-argument call sites across the test suite, all of which would
/// otherwise need updating for a feature they don't exercise.
/// `source_path` is the `.mo` file debug info is being generated for
/// (`Option.none` disables debug info entirely, matching plain
/// `compile_db_decls_ir` exactly); `debug_files` is the per-module file
/// table for `!DIFile` attribution (`LLVMModule.debug_files`).
#[partial]
def compile_db_decls_ir_with_debug (defs : List Def) (source_path : Option String) (debug_files : List (Pair String String)) : LLVMModule :=
    let arities := build_arity_table defs in
    match compile_db_def_list (empty_ctx arities str_map_empty str_map_empty) defs {
        { ctx := _, funcs := compiled_funcs, globals := compiled_globals } =>
            let funcs := ren_main_and_wrap compiled_funcs in
            LLVMModule.mk "x86_64-unknown-linux-gnu" compiled_globals funcs runtime_declarations source_path debug_files,
    }

/// Compile a list of Decl to a complete LLVM module.
/// Extracts def_d and inductive_d entries, compiles constructors and defs.
#[partial]
def compile_db_module (decl_list : List Decl) : LLVMModule :=
    compile_db_module_with_debug decl_list Option.none List.empty

/// `compile_db_module`, with DWARF debug info -- see
/// `compile_db_decls_ir_with_debug`'s own doc comment for why this is a
/// sibling function rather than new params on `compile_db_module`.
#[partial]
def compile_db_module_with_debug (decl_list : List Decl) (source_path : Option String) (debug_files : List (Pair String String)) : LLVMModule :=
    let defs := extract_defs decl_list in
    let inds := extract_inductives decl_list in
    let ctor_tags := build_constructor_tag_map inds in
    let ctor_arities := build_constructor_arity_map inds in
    let ctor_funcs := compile_db_inductive_decls inds ctor_tags in
    let arities := build_arity_table defs in
    match compile_db_def_list (empty_ctx arities ctor_tags ctor_arities) defs {
        { ctx := _, funcs := compiled_funcs, globals := compiled_globals } =>
            // Prepend the GENERATED runtime natives (`lang/codegen/
            // runtime.mo`) -- ordinary `define`s in this same module,
            // called by the native wrappers `native_runtime_fn_name`
            // wires. They deliberately carry no matching `declare` (see
            // `runtime_declarations`' own note on the redefinition
            // error that would cause).
            let all_funcs := List.append runtime_native_functions (List.append ctor_funcs compiled_funcs) in
            let funcs := ren_main_and_wrap all_funcs in
            LLVMModule.mk "x86_64-unknown-linux-gnu" compiled_globals funcs runtime_declarations source_path debug_files,
    }

/// Compile a list of canonical InductConstructors to LLVM constructor wrapper functions.
/// `ctor_tags` -- see `build_constructor_tag_map`'s own doc comment;
/// looked up by the constructor's composite bare#arity key (the
/// wrapper's own param count is the constructor's field count) -- falls
/// back to tag 0 for anything not found (shouldn't happen for a real
/// reachable inductive, since `ctor_tags` is built from this exact same
/// `List Inductive`; matches this file's other "absent from the table"
/// fallbacks, e.g. `ctx_lookup_arity`'s own doc comment).
#[partial]
def compile_db_inductive_constructors (type_name : String) (constructors : List InductConstructor) (ctor_tags : HashMap String I64) : List LLVMFunction := match constructors {
    List.empty => List.empty,
    List.cons c rest =>
        match c {
            InductConstructor.mk name params typ =>
                // `name` is only ever the constructor's own bare name
                // (e.g. "of_bytes"), not qualified with its enclosing
                // type -- two unrelated Inductives whose constructors
                // happen to share a name (common across a big prelude:
                // "of_bytes", "of_list", ...) previously compiled to the
                // exact same LLVM function name
                // ("monad_ctor_of_bytes"), an "invalid redefinition of
                // function" link error the moment more than one such
                // type was compiled into the same module (e.g. compiling
                // any real file, which always pulls in every loaded
                // module's declarations via compile_loaded_modules_to_ir,
                // not just the ones actually used).
                let name_str := module_path_to_str name in
                let qualified_name := type_name ++ "_" ++ name_str in
                let field_count := count_db_params params 0 in
                // Composite bare#arity key -- this wrapper's own param
                // count is exactly the constructor's field count, so the
                // tag embedded here agrees with what saturated
                // allocations and match dispatch compute for the same
                // constructor (see `constructor_tag_at`). The bare tier
                // underneath only answers a single-arity bare name; its
                // -1 ambiguity sentinel degrades to 0 (these wrappers
                // are vestigial -- nothing in codegen calls them -- so
                // the tag is documentation, kept consistent anyway).
                let tag := match str_map_lookup (ctor_composite_key name_str field_count) ctor_tags {
                    Option.some t => t,
                    Option.none =>
                        match str_map_lookup name_str ctor_tags {
                            Option.some t => if I64.gt t (-1) then t else 0,
                            Option.none => 0,
                        },
                } in
                let func := compile_constructor_decl qualified_name field_count tag in
                List.cons func (compile_db_inductive_constructors type_name rest ctor_tags)
        }
}

/// Compile a single canonical Inductive to LLVM constructor wrapper functions.
#[partial]
def compile_db_inductive (ind : Inductive) (ctor_tags : HashMap String I64) : List LLVMFunction := match ind {
    Inductive.mk name params typ constructors attrs _vis =>
        compile_db_inductive_constructors (module_path_to_str name) constructors ctor_tags
}

/// Compile a list of canonical Inductives to LLVM constructor wrapper functions.
#[partial]
def compile_db_inductive_decls (ind_decls : List Inductive) (ctor_tags : HashMap String I64) : List LLVMFunction := match ind_decls {
    List.empty => List.empty,
    List.cons ind rest =>
        let funcs := compile_db_inductive ind ctor_tags in
        List.append funcs (compile_db_inductive_decls rest ctor_tags)
}

/// Compile an inductive type constructor to an LLVM wrapper function.
/// Generates: define cc 9 i64 @monad_ctor_<name>(i64 %p0, i64 %p1, ...) {
///   entry:
///     %ctemp = alloc_constructor(%p0, %p1, ...)
///     ret i64 %ctemp
/// }
/// Matches Rust reference: llvm-codegen/src/codegen/constructors.rs:38-82
#[partial]
def compile_constructor_decl (con_name : String) (field_count : I64) (tag : I64) : LLVMFunction :=
    let params := build_constructor_params field_count in
    let fields := build_param_fields field_count in
    let alloc_val := LLVMValue.alloc_constructor tag fields in
    let assign_instr := LLVMInstruction.assign "ctemp" alloc_val in
    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ "ctemp") in
    let entry_block := LLVMBasicBlock.mk "entry" (List.cons assign_instr (List.cons ret_instr List.empty)) in
    let func_name := String.concat "monad_ctor_" con_name in
    LLVMFunction.mk func_name params LLVMType.i64_ (List.cons entry_block List.empty) true Option.none

#[partial]
def build_constructor_params (count : I64) : List ParamPair :=
    build_params_from count 0

#[partial]
def build_params_from (count : I64) (idx : I64) : List ParamPair :=
    if idx == count then List.empty
    else
        let name := String.concat "p" (I64.to_string idx) in
        List.cons (ParamPair.mk name LLVMType.i64_) (build_params_from count (idx + 1))

#[partial]
def build_param_fields (count : I64) : List LLVMValue :=
    build_fields_from count 0

#[partial]
def build_fields_from (count : I64) (idx : I64) : List LLVMValue :=
    if idx == count then List.empty
    else List.cons (LLVMValue.parm_ idx) (build_fields_from count (idx + 1))

/// Starts a fresh top-level def's own body with an EMPTY `locals` list
/// (`ctx_reset_locals`) before binding its params -- the SAME
/// cross-function-leak protection `compile_db_lam_ir` already has for a
/// lifted lambda's own body, just missing here at the TOP-LEVEL DEF
/// boundary. Without this, `locals` accumulates every param/match-field/
/// let-binding name from EVERY previously-compiled def in the same
/// `compile_db_def_list` pass, forever -- `ctx_lookup_local` is checked
/// BEFORE `is_constructor_var` in `compile_db_term_ir`'s `Term.var` arm,
/// so a later def whose body happens to reference an identifier with
/// the SAME NAME as some ancient, unrelated local (any single-letter
/// param name, or a constructor name like `none` that also happens to
/// be some earlier def's OWN pattern-bound field name) silently resolves
/// to that stale, cross-function SSA value instead of its own intended
/// meaning. Confirmed as a real, previously-undiagnosed bug via
/// `bootstrap compile lang/main.mo monad`'s own self-compile
/// (`init/lib.mo`'s `List.get`, ~1700 defs into the reachable set):
/// its own `empty => none` match arm resolved to a `%tN` SSA value left
/// over from an entirely different, much-earlier-compiled def
/// (`params_for_names_attrs`) -- `llc: use of undefined value '%tN'`
/// (a cross-function reference, always invalid). No `ctx_restore_locals`
/// counterpart needed here (unlike the lambda case): each top-level def
/// in `compile_db_def_list`'s sequence is independent, not nested inside
/// another's compilation, so there's no "outer" locals to restore
/// afterward -- the NEXT def's own `bind_params_in_ctx_db` call resets
/// again before adding its own params.
#[partial]
def bind_params_in_ctx_db (c : CodegenCtx) (params : List Param) : CodegenCtx :=
    bind_params_with_idx_db (ctx_reset_locals c) params 0

#[partial]
def bind_params_with_idx_db (c : CodegenCtx) (params : List Param) (idx : I64) : CodegenCtx := match params {
    List.empty => c,
    List.cons p rest =>
        let c1 := ctx_bind_local c (param_name_db p) (LLVMValue.parm_ idx) in
        bind_params_with_idx_db c1 rest (idx + 1),
}

/// Count the number of fields in a Param list.
#[partial]
def count_db_params (params : List Param) (n : I64) : I64 := match params {
    List.empty => n,
    List.cons p rest => count_db_params rest (n + 1),
}

/// Collapses functions with a duplicate NAME to their first occurrence
/// -- needed because `build_closure_shim_func` (above) is a pure,
/// deterministic function of `(real_name, arity)`, so every call site
/// that boxes the SAME top-level def as a first-class value emits a
/// byte-identical shim, which would otherwise be a duplicate LLVM
/// symbol definition (`llc`/`clang` link error). Run once, over the
/// WHOLE module's assembled function list, rather than tracking "have I
/// already emitted a shim for X" through `CodegenCtx` (which would
/// touch every one of the dozens of call sites that construct/pattern-
/// match it) -- the cost is a negligible amount of duplicate (never-
/// emitted-to-`.ll`) shim generation during compilation; shims are
/// single-block, 2-instruction functions, cheap to regenerate.
#[partial]
def dedup_funcs_by_name (funcs : List LLVMFunction) : List LLVMFunction :=
    dedup_funcs_by_name_go funcs List.empty

#[partial]
def dedup_funcs_by_name_go (funcs : List LLVMFunction) (seen : List String) : List LLVMFunction := match funcs {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            LLVMFunction.mk name params ret_ty blocks ghc_cc dbg_loc =>
                if list_contains_str seen name
                then dedup_funcs_by_name_go rest seen
                else List.cons f (dedup_funcs_by_name_go rest (List.cons name seen)),
        },
}

// --- Gate: no two definitions may share one LLVM symbol -------------
//
// `dedup_funcs_by_name` (below) exists to collapse byte-identical
// closure shims, and it cannot tell one of those from two genuinely
// different defs -- it keeps the first and drops the rest, silently.
// `build_def_name_map` does the same thing one stage earlier, keeping
// the last. Qualification makes a collision between two SOURCE defs
// impossible; this gate is what makes that a checked property rather
// than an argument, and it also catches the cases qualification does
// not cover on its own: a synthesized name clashing with a source one,
// or either clashing with a runtime symbol.
//
// Structurally identical definitions are rejected too. One of them is
// still being dropped, and "identical today" is not a property anything
// maintains.

// --- Gate: every called symbol must actually exist -----------------
//
// A reference that resolves to no `define`/`declare` is not caught
// anywhere in this pipeline: it renders happily into the `.ll` and dies
// at `llc` with `undefined value '@x'` -- at the END of a 15-25 minute
// self-compile, naming one symbol and no call site. Since every name
// this backend emits now goes through `def_symbol_name`/`ref_symbol_
// name`, a single mismatch between those two ends does exactly that,
// which makes this the difference between a seconds-long iteration and
// a half-hour one.

/// When the user's main has no params, add an `args` param so the C runtime
/// can pass the command-line argument list. If main already has params (e.g.,
/// `def main (args : List String) : I64`), keep them as-is.
#[partial]
def ren_main_and_wrap (funcs : List LLVMFunction) : List LLVMFunction :=
    rename_main (dedup_funcs_by_name funcs)

#[partial]
def has_main (funcs : List LLVMFunction) : Bool := match funcs {
    List.empty => false,
    List.cons f rest =>
        match f {
            LLVMFunction.mk name params ret_ty blocks ghc_cc dbg_loc =>
                if String.beq name "main" then true
                else has_main rest,
        },
}

/// When the user's main has no params, add an `args` param (List String from C runtime).
/// If main already has params (user wrote `def main (args : List String)`), keep them.
/// `dbg_loc` (main's own debug-info location, if any) is threaded through
/// unchanged into the renamed function -- the rename must not silently
/// drop it, since `main`/`main_monad` is exactly the function a user is
/// most likely to want a real source line for.
#[partial]
def rename_main (funcs : List LLVMFunction) : List LLVMFunction := match funcs {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            LLVMFunction.mk name params ret_ty blocks ghc_cc dbg_loc =>
                if String.beq name "main"
                then
                    let main_params := ensure_main_params params in
                    List.cons (LLVMFunction.mk "main_monad" main_params ret_ty blocks ghc_cc dbg_loc) (rename_main rest)
                else if ends_with_main name then
                    // For module-qualified main functions, always rename to just "main_monad"
                    // The runtime expects this exact name
                    let main_params := ensure_main_params params in
                    List.cons (LLVMFunction.mk "main_monad" main_params ret_ty blocks ghc_cc dbg_loc) (rename_main rest)
                else
                    List.cons f (rename_main rest),
        },
}

/// If main has no params, add a synthetic `args` param (List String from C runtime).
/// If main already has params (user wrote `def main (args : List String)`), keep them.
#[partial]
def ensure_main_params (params : List ParamPair) : List ParamPair := match params {
    List.empty => List.cons (ParamPair.mk "args" LLVMType.i64_) List.empty,
    List.cons x y => params,
}

// === De Bruijn (canonical) def compilation ===

#[test]
def test_runtime_decls_not_empty : Bool :=
    match runtime_declarations {
        List.empty => false,
        List.cons x y => true,
    }

/// `test_runtime_decls_i64_convention`'s data-level half: no
/// declaration's parameter or return type string is `i8*`. Walks the
/// `LLVMDeclaration` values directly rather than scanning rendered
/// text -- `emit_module`'s type-definitions block (`%Closure = type {
/// %Header, i8*, ... }`) and function bodies (`inttoptr ... to i8*`,
/// `load i8, i8* ...`) legitimately contain `i8*` and would make a
/// whole-module text scan false-positive.
#[partial]
def decls_have_no_i8_star (ds : List LLVMDeclaration) : Bool :=
    match ds {
        List.empty => true,
        List.cons d rest =>
            match d {
                LLVMDeclaration.mk _name params ret_ty =>
                    if String.beq ret_ty "i8*" then false
                    else if strs_have_no_i8_star params then decls_have_no_i8_star rest
                    else false,
            },
    }

#[partial]
def strs_have_no_i8_star (ss : List String) : Bool :=
    match ss {
        List.empty => true,
        List.cons s rest =>
            if String.beq s "i8*" then false else strs_have_no_i8_star rest,
    }

/// Every runtime declaration uses the i64 calling convention (see
/// `runtime_declarations`' own CONVENTION comment): the backend holds
/// Strings and pointers as raw i64 values, every emitter types its
/// calls `LLVMType.i64_`, and a declare typed any other way mismatches
/// every call site of that native in the emitted module. This used to
/// be live: 15 declares carried the C header's `i8*` shapes while the
/// module called them all as i64 (malformed IR that the current llc
/// 21.1.8 happens to silently accept; a stricter parser would reject
/// the whole module).
#[test]
def test_runtime_decls_i64_convention : Bool :=
    decls_have_no_i8_star runtime_declarations
        && check_contains (emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty List.empty runtime_declarations Option.none List.empty)) "declare void @monad_print_str(i64)"
        && check_contains (emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty List.empty runtime_declarations Option.none List.empty)) "declare i64 @monad_read_file(i64)"
        && check_contains (emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty List.empty runtime_declarations Option.none List.empty)) "declare i64 @monad_i64_to_string(i64)"

#[test]
def test_module_emit_has_header : Bool :=
    let text := emit_module (compile_db_decls_ir List.empty) in
    let prefix := String.slice text 0 12 in
    String.beq prefix "; ModuleID ="

#[test]
def test_empty_decls_module : Bool :=
    match (compile_db_decls_ir List.empty) {
        LLVMModule.mk triple globals funcs decl_list debug_source _files =>
            String.beq triple "x86_64-unknown-linux-gnu",
    }

#[test]
def test_compile_db_inductive_decls : Bool :=
    let some_name := ModulePath.mp (List.cons (Identifier.id "Some") List.empty) in
    let some_ctor := InductConstructor.mk some_name List.empty (Term.type_ 1) in
    let none_name := ModulePath.mp (List.cons (Identifier.id "None") List.empty) in
    let none_ctor := InductConstructor.mk none_name List.empty (Term.type_ 1) in
    let ctors := List.cons some_ctor (List.cons none_ctor List.empty) in
    let ind_name := ModulePath.mp (List.cons (Identifier.id "Option") List.empty) in
    let ind := Inductive.mk ind_name List.empty (Term.type_ 1) ctors empty_attrs Visibility.package_private in
    let funcs := compile_db_inductive_decls (List.cons ind List.empty) str_map_empty in
    let mod_ := LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty funcs List.empty Option.none List.empty in
    let text := emit_module mod_ in
    // Constructor function names are qualified with their enclosing
    // type ("Option_Some"/"Option_None"), not just the bare constructor
    // name -- otherwise two different Inductives whose constructors
    // happen to share a name collide as "invalid redefinition of
    // function" the moment both end up compiled into the same module
    // (see compile_db_inductive_constructors's doc comment).
    if check_contains text "monad_ctor_Option_Some"
    then check_contains text "monad_ctor_Option_None"
    else false

/// Regression test for the `string_find_last`/`extract_base_name`
/// off-by-length bug (see `extract_base_name`'s own doc comment):
/// `String.slice`'s third argument is a LENGTH, not an end index, so
/// `is_constructor_var`/`constructor_tag`'s dynamic-fallback tier
/// (`build_constructor_tag_map`) silently failed to strip a qualified
/// name's own type prefix, looking up "Option.Some" in a map keyed by
/// the bare "Some" and never finding it. Isolated from the whole self-
/// hosted parse/typecheck/elaborate pipeline (a hand-built `Inductive`,
/// like `test_compile_db_inductive_decls` above) so this test exercises
/// exactly the map-building + lookup mechanism, not elaboration.
#[test]
def test_ctor_tag_map_qualified_name_lookup : Bool :=
    let some_name := ModulePath.mp (List.cons (Identifier.id "Some") List.empty) in
    let some_ctor := InductConstructor.mk some_name List.empty (Term.type_ 1) in
    let none_name := ModulePath.mp (List.cons (Identifier.id "None") List.empty) in
    let none_ctor := InductConstructor.mk none_name List.empty (Term.type_ 1) in
    let ctors := List.cons some_ctor (List.cons none_ctor List.empty) in
    let ind_name := ModulePath.mp (List.cons (Identifier.id "Option") List.empty) in
    let ind := Inductive.mk ind_name List.empty (Term.type_ 1) ctors empty_attrs Visibility.package_private in
    let tag_map := build_constructor_tag_map (List.cons ind List.empty) in
    let c := empty_ctx empty_arities tag_map str_map_empty in
    is_constructor_var c "Option.Some" && is_constructor_var c "Option.None"

/// A hand-built single-field Param -- the fixture shape for the
/// composite-keying test below (see `point_ind` in lang/tests/infer_tests.mo
/// for the source of the pattern).
#[partial]
def unit_test_param (nm : String) : Param :=
    Param.mk (Identifier.id nm) (Term.type_ 1) Multiplicity.many Option.none List.empty

/// Composite tag keying (`build_constructor_tag_map` +
/// `constructor_tag_at`): two different types both declaring a `mk`
/// constructor at DIFFERING arities -- the v29 self-compiled binary's
/// 283-way `mk` collision scaled to a hand-built minimum -- must get
/// DISTINCT tags, both past the builtin range; the arity-unknown
/// qualified lookups ("Slim.mk"/"Wide.mk", how a value-position
/// reference is written) must agree with the arity-carrying composite
/// lookups; and the bare name, now claimed at two arities, must still
/// answer `is_constructor_var` (its bare entry is the -1 sentinel).
/// Isolated from the whole self-hosted pipeline like
/// `test_ctor_tag_map_qualified_name_lookup` above so this exercises
/// exactly the map-building + lookup mechanism.
#[test]
def test_ctor_tags_distinguish_same_name_differing_arity : Bool :=
    let slim_mk := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "mk") List.empty))
        (List.cons (unit_test_param "only") List.empty) (Term.type_ 1) in
    let slim := Inductive.mk (ModulePath.mp (List.cons (Identifier.id "Slim") List.empty))
        List.empty (Term.type_ 1) (List.cons slim_mk List.empty) empty_attrs Visibility.package_private in
    let wide_mk := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "mk") List.empty))
        (List.cons (unit_test_param "a") (List.cons (unit_test_param "b") (List.cons (unit_test_param "c") List.empty))) (Term.type_ 1) in
    let wide := Inductive.mk (ModulePath.mp (List.cons (Identifier.id "Wide") List.empty))
        List.empty (Term.type_ 1) (List.cons wide_mk List.empty) empty_attrs Visibility.package_private in
    let tag_map := build_constructor_tag_map (List.cons slim (List.cons wide List.empty)) in
    let arity_map := build_constructor_arity_map (List.cons slim (List.cons wide List.empty)) in
    let c := empty_ctx empty_arities tag_map arity_map in
    let slim_at := constructor_tag_at c "mk" 1 in
    let wide_at := constructor_tag_at c "mk" 3 in
    Bool.not (I64.beq slim_at wide_at)
        && I64.gt slim_at 15
        && I64.gt wide_at 15
        && I64.beq (constructor_tag c "Slim.mk") slim_at
        && I64.beq (constructor_tag c "Wide.mk") wide_at
        && I64.beq (constructor_arity c "Slim.mk") 1
        && I64.beq (constructor_arity c "Wide.mk") 3
        && is_constructor_var c "mk"

/// Regression tests for `native_runtime_fn_name`/`compile_native_def_wrapper_ir`:
/// a `#[native string_concat]`/`#[native string_eq]`-attributed def
/// (`String.concat`/`String.beq`'s own shape, init/string.mo) must
/// compile to a real call into its whitelisted runtime function, not
/// the generic hole-bodied-native fallback's `alloc_constructor(0, 0)`
/// "return Unit" stub (confirmed as a real gap: that stub was
/// `String.concat`'s own actual compiled body, silently discarding both
/// arguments and producing an empty/meaningless result at runtime).
#[partial]
def native_attr (target : String) : List Attribute :=
    List.cons (Attribute.mk (Identifier.id "native") (List.cons (AttrArg.ident (Identifier.id target)) List.empty)) List.empty

/// A 2-param, hole-bodied `#[native <target>]` def -- `lam_params`
/// (lang/parser.mo) always wraps even a hole body in one lambda per
/// param, so a REAL parsed native def's own body looks exactly like
/// this, not a bare `Term.hole`.
#[partial]
def native_def_fixture (name : String) (target : String) : Def :=
    let body := Term.lam (DebugName.named (Identifier.id "a")) Term.hole
        (Term.lam (DebugName.named (Identifier.id "b")) Term.hole Term.hole) in
    Def.mk (ModulePath.mp (List.cons (Identifier.id name) List.empty)) Term.hole body
        List.empty (native_attr target) Visibility.package_private

#[partial]
def compile_native_def_fixture_text (name : String) (target : String) : String :=
    match compile_db_def_ir (empty_ctx empty_arities str_map_empty str_map_empty) (native_def_fixture name target) {
        { ctx := _, funcs := funcs, globals := _ } =>
            emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty funcs List.empty Option.none List.empty),
    }

#[test]
def test_native_string_concat_calls_runtime_fn_not_unit_stub : Bool :=
    let text := compile_native_def_fixture_text "String.concat" "string_concat" in
    if check_contains text "call i64 @monad_string_concat"
    then not (check_contains text "call i64 @alloc_constructor(i64 0, i64 0)")
    else false

#[test]
def test_native_string_eq_wraps_raw_result_as_tagged_bool : Bool :=
    let text := compile_native_def_fixture_text "String.beq" "string_eq" in
    // Must call the real comparison AND allocate a genuine tagged
    // Constructor from its (dynamically computed) result -- NOT return
    // the raw 0/1 i64 directly, which crashes (monad_get_tag on a small
    // integer) the moment it's used as an ordinary Bool value rather
    // than an immediate if-condition.
    if check_contains text "call i64 @monad_string_eq"
    then check_contains text "call i64 @alloc_constructor"
    else false

#[test]
def test_native_unwhitelisted_native_still_gets_unit_stub : Bool :=
    // A native this backend doesn't implement must be completely
    // unaffected by the whitelist -- still the pre-existing stub
    // behavior at THIS level, not a call to a nonexistent runtime
    // function that would fail at link time.
    //
    // The example is a deliberately fictional native rather than a real
    // unimplemented one: every previous choice here
    // (string_slice/string_drop, then string_to_lowercase) eventually
    // got a real implementation and silently flipped this test to
    // failing for the wrong reason. A name no runtime will ever define
    // cannot rot that way.
    //
    // Reaching this stub is now a COMPILE ERROR one level up:
    // `validate_no_unwired_natives` rejects any such def that is
    // actually reachable, precisely because the stub miscompiles
    // silently (see that def's own doc comment). This test pins the
    // fallback the validator guards, which still has to behave sanely
    // for an UNREACHABLE native -- dead code the validator deliberately
    // does not block a compile over.
    let text := compile_native_def_fixture_text "String.no_such_op" "definitely_not_a_real_native" in
    if check_contains text "call i64 @alloc_constructor(i64 0, i64 0)"
    then not (check_contains text "@monad_definitely_not_a_real_native")
    else false

/// A single, unlocated `myfunc` fixture def -- used by the
/// `compile_db_decls_ir_with_debug` tests below.
#[partial]
def debug_fixture_def : Def :=
    Def.mk (ModulePath.mp (List.cons (Identifier.id "myfunc") List.empty)) (Term.type_ 1)
        (Term.lit (Literal.num 42 NumSuffix.i64)) List.empty empty_attrs Visibility.package_private

/// A def with a source position on an INNER term, as
/// `decls_parser_located` produces.
///
/// Two things this fixture's shape is deliberate about, both learned by
/// getting them wrong first:
///
///   - **The wrapper is on the body, and `strip_db_lams` must keep it.**
///     That helper peels wrappers to see THROUGH them to a binder, but
///     returns the final term wrapped -- `compile_db_def_ir_body` compiles
///     exactly that term, so peeling it there would silently discard the
///     body's own position. Getting this wrong is invisible: the def still
///     compiles and still carries the function-level location.
///   - **The located term is an `if`, not a literal.** A literal compiles to
///     a VALUE and emits no instructions, so there is nothing to attach a
///     position to and `prepend_loc_marker` correctly emits no marker. That
///     is exactly why `factorial`'s `then 1` produces no line-6 entry: the
///     constant is folded into a phi operand.
#[partial]
def located_fixture_def : Def :=
    Def.mk (ModulePath.mp (List.cons (Identifier.id "myfunc") List.empty)) (Term.type_ 1)
        (Term.ctx (Location.mk 40 9 7)
            (Term.lit (Literal.if_ (Term.lit (Literal.num 1 NumSuffix.i64))
                                   (Term.lit (Literal.num 2 NumSuffix.i64))
                                   (Term.lit (Literal.num 3 NumSuffix.i64)))))
        List.empty empty_attrs Visibility.package_private

/// `debug_fixture_def` with the position a located parse puts on the
/// body -- line 2, column 3, at offset 5.
#[partial]
def located_num_fixture_def : Def :=
    Def.mk (ModulePath.mp (List.cons (Identifier.id "myfunc") List.empty)) (Term.type_ 1)
        (Term.ctx (Location.mk 5 2 3) (Term.lit (Literal.num 42 NumSuffix.i64)))
        List.empty empty_attrs Visibility.package_private

#[test]
def test_compile_db_decls_ir_with_debug_emits_dbg : Bool :=
    let mod_ := compile_db_decls_ir_with_debug (List.cons located_fixture_def List.empty) (Option.some "hello.mo") List.empty in
    let text := emit_module mod_ in
    if check_contains text "!DICompileUnit"
    then (if check_contains text "!DISubprogram" then check_contains text "!dbg !" else false)
    else false

/// Exact-content regression: the body wrapper's captured `Location.mk
/// 5 2 3` (line 2, column 3) must land verbatim in the emitted
/// `!DILocation`, the function name in `!DISubprogram`, and the source
/// path (split into filename/directory by `llvm_split_path`) in `!DIFile`.
#[test]
def test_compile_db_decls_ir_with_debug_exact_content : Bool :=
    let mod_ := compile_db_decls_ir_with_debug (List.cons located_num_fixture_def List.empty) (Option.some "hello.mo") List.empty in
    let text := emit_module mod_ in
    if check_contains text "!DIFile(filename: \"hello.mo\", directory: \".\")"
    then (if check_contains text "name: \"myfunc\""
        then (if check_contains text "line: 2"
            then check_contains text "!DILocation(line: 2, column: 3, scope: !6)"
            else false)
        else false)
    else false

/// A located term emits a DISTINCT `!DILocation` and attaches it to the
/// instructions it produced, instead of everything sharing the function's
/// one location.
///
/// This is the assertion that separates "locations work" from "locations
/// are transparently doing nothing" -- the transparency oracle passes
/// either way, so it cannot be the only check.
///
/// The function's OWN location is the body wrapper's (line 9, column 7)
/// -- a decl-span entry would start at the attributes, while the wrapper
/// starts at the body -- and `dbg_loc_of_body` reads it directly. The
/// wrapper on the body's INNER `if` additionally produces per-instruction
/// markers, which is the distinct-location part this test asserts.
#[test]
def test_located_term_emits_its_own_dilocation : Bool :=
    let located : Def := located_fixture_def in
    let mod_ := compile_db_decls_ir_with_debug (List.cons located List.empty) (Option.some "hello.mo") List.empty in
    let text := emit_module mod_ in
    // The subprogram and its own location node both carry the BODY's
    // position.
    if check_contains text "line: 9, type: !4"
    then check_contains text "!DILocation(line: 9, column: 7, scope: !6)"
    else false

/// A location wrapped around a term that emits NO instructions must emit
/// no marker: one prepended to an empty list ends up at the END of
/// whatever list it is spliced into, where `ends_with_terminator` would
/// read it as a terminator and `drop_last_instr` would silently drop it.
#[test]
def test_located_empty_term_emits_no_marker : Bool :=
    let d : DbgLoc := DbgLoc.mk 9 7 in
    // `Term.hole` compiles to no instructions at all.
    match prepend_loc_marker (Location.mk 40 9 7) List.empty {
        List.empty => true,
        List.cons _ _ => false,
    }

/// The plain (non-`_with_debug`) entry point must emit BYTE-IDENTICAL
/// text (no debug metadata at all) whether or not this feature exists --
/// it always passes `Option.none`/`str_map_empty` through, so this is a
/// straightforward regression guard for that default.
#[test]
def test_compile_db_decls_ir_default_has_no_debug_info : Bool :=
    let mod_ := compile_db_decls_ir (List.cons debug_fixture_def List.empty) in
    let text := emit_module mod_ in
    not (check_contains text "!DICompileUnit")

/// A def whose body is a native Bool comparison over a BRANCHING
/// operand -- `I64.beq (if b then x else y) (-1)` -- the exact shape
/// that ended the bootstrap at `llc` (`lang.types::parse_span_is_unknown`,
/// whose real operand is a struct field access: that compiles as a
/// single-case match with the same entry/check/merge block chain this
/// `if` produces). The comparison's `icmp` gets spliced into the
/// operand's merge block, which `compose_seq` re-closes with
/// `ret <raw i1>`; the def's own entry list ends in the operand's
/// branch, so `already_terminated` is true and the plain-ret boxing
/// (`materialize_branch_val`) never runs.
#[partial]
def native_bool_over_branching_fixture_def : Def :=
    Def.mk (ModulePath.mp (List.cons (Identifier.id "spbeq") List.empty)) (Term.type_ 1)
        (Term.lam (DebugName.named (Identifier.id "b")) (Term.type_ 1)
            (Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1)
                (Term.lam (DebugName.named (Identifier.id "y")) (Term.type_ 1)
                    (Term.app
                        (Term.app (Term.var 3 (DebugName.named (Identifier.id "I64.beq")))
                            (Term.lit (Literal.if_
                                (Term.var 2 (DebugName.named (Identifier.id "b")))
                                (Term.var 1 (DebugName.named (Identifier.id "x")))
                                (Term.var 0 (DebugName.named (Identifier.id "y"))))))
                        (Term.lit (Literal.num (-1) NumSuffix.i64))))))
        List.empty empty_attrs Visibility.package_private

/// Regression: a Bool-returning def whose body is a native comparison
/// over a BRANCHING operand must box its tail value inside the terminal
/// block before that block's own `ret` -- otherwise the raw `i1` becomes
/// the function's real return and `llc` rejects the module
/// (`'%tN' defined with type 'i1' but expected 'i64'`, the live
/// self-compile failure). The `zext i1 ... to i64` is the boxing's first
/// instruction; without the fix the emitted module contains none at all.
#[test]
def test_native_bool_branching_tail_boxes_ret : Bool :=
    let mod_ := compile_db_decls_ir (List.cons native_bool_over_branching_fixture_def List.empty) in
    let text := emit_module mod_ in
    check_contains text "zext i1"

#[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text - 1)) needle

// === Multi-module compilation ===

/// Compile all loaded modules to a single LLVM module.
/// All declarations from all modules are compiled together with fully qualified names.
///
/// `verbose` (passed through from `compile_file`'s own `--verbose`/`-v`
/// flag) gates the per-stage progress printlns inside this function —
/// the module-count / def-count / reachable-count numbers were
/// unconditionally printed on every compile before, drowning real output
/// (`lang/main.mo`'s own compile-file progress markers, link failures,
/// the user's program output) in low-value noise.
#[partial]
def compile_loaded_modules_to_ir (loaded : LoadedModules) (verbose : Bool) : IO (Result String LLVMModule) :=
    compile_loaded_modules_to_ir_with_debug loaded verbose Option.none

/// One `(module path string, file path)` pair per loaded module -- the
/// `!DIFile` attribution table (`LLVMModule.debug_files`). Keyed by the
/// same `show_module_path` string a function name's `<module>::<def>`
/// prefix uses, which is what `lang.codegen.ir`'s `module_file_ref`
/// looks up. Built in module order so `!DIFile` id assignment is
/// reproducible run to run.
#[partial]
def module_file_pairs (mods : List ModuleInfo) (acc : List (Pair String String)) : List (Pair String String) := match mods {
    List.empty => acc,
    List.cons m rest => module_file_pairs rest (List.append acc (List.cons (Pair.pair (show_module_path m.path) m.file_path) List.empty)),
}

/// `compile_loaded_modules_to_ir`, with DWARF debug info (one location
/// per top-level def, from the `Term.ctx` wrapper on its body).
/// `source_path` is passed straight through to
/// `compile_db_module_with_debug` at the very end of this function --
/// everything else is identical to the plain version. A sibling
/// function (like `compile_db_decls_ir_with_debug`) rather than new
/// params on `compile_loaded_modules_to_ir` itself, so its existing
/// callers (`main.mo`, `test_closure_capture_e2e.mo`) don't need to
/// change for a feature they don't exercise.
#[partial]
def compile_loaded_modules_to_ir_with_debug (loaded : LoadedModules) (verbose : Bool) (source_path : Option String) : IO (Result String LLVMModule) := do {
    let total_start : I64 <- Bench.now;

    let all_mods := get_loaded_all loaded;

    // Per-function `!DIFile` attribution: one pair per loaded module.
    // Bound ONCE here, before the whole stage pipeline -- it only feeds
    // the final `compile_db_module_with_debug` call, but computing it
    // per-module list walk at the point of use would read structurally
    // like it belongs to a stage it doesn't.
    let debug_files : List (Pair String String) := module_file_pairs all_mods List.empty;

    // Debug: log loaded modules count
    let module_count := List.length all_mods;
    if verbose then println ("Loaded " ++ I64.to_string module_count ++ " modules") else return unit;

    // Stage 0b: resolve every `open`/`use`-brought bare-name alias
    // (`open IO {file_exists}`, `use std.io {file_exists}`) to its real,
    // fully qualified target -- MUST run per-module, on each module's
    // own `decl_list`, BEFORE `collect_all_decls_from_modules` flattens
    // everything into one global list just below. Applying this AFTER
    // flattening (an earlier version of this fix) let one module's own
    // alias shadow an unrelated LOCAL variable of the same bare name in
    // a completely different module -- see `lang.module`'s own
    // `resolve_open_aliases_in_module_info` doc comment for the
    // confirmed regression (`Reachable decl_list` collapsing from 1925
    // to 181) this fixes.
    let t_open_alias : I64 <- Bench.now;
    let aliased_mods := resolve_open_aliases_in_modules all_mods;
    if verbose then do {
        Bench.report_since "open_alias_resolve" t_open_alias;
        return unit
    } else return unit;

    // Stage 0c: give every source def its module-qualified name and
    // re-point every reference at the module that owns it. MUST run
    // here, before Stage 1 -- `ModuleInfo.path` is the only record of
    // which module a decl came from, and flattening discards it.
    let t_qualify : I64 <- Bench.now;
    match qualify_modules aliased_mods {
      Result.err e => do {
        if verbose then println ("FAILED at stage: qualify_modules (" ++ e ++ ")") else return unit;
        return (Result.err e)
      },
      Result.ok qualified_mods => do {
    if verbose then do {
        Bench.report_since "qualify_modules" t_qualify;
        return unit
    } else return unit;

    // Stage 1: collect all declarations (now each already carrying its
    // own module path, so the flat list is still collision-free)
    let t_collect : I64 <- Bench.now;
    let all_decls := collect_all_decls_from_modules qualified_mods List.empty;
    if verbose then do {
        let def_count := List.length all_decls;
        Bench.report_since "collect_decls" t_collect;
        println ("Total defs collected: " ++ I64.to_string def_count)
    } else return unit;

    // Stage 2: resolve every infix-operator reference (`+`, `==`, ...) to its
    // real registered target BEFORE reachability filtering -- see
    // lang.scope's own extended doc comment above `lookup_infix`/
    // `resolve_infix_decls` for why this can't happen at parse time.
    // Must run first, not after `filter_reachable_decls`: reachability
    // is computed by walking each Def's own body for names it calls
    // (`collect_referenced_names`) -- an UNRESOLVED operator var (named
    // "&&", not "Bool.and") makes that walk blind to the fact that
    // `Bool.and` is actually called at all, so `Bool.and` itself gets
    // filtered out as "unreachable" and codegen later emits a call to
    // a function that was never compiled into the module ("undefined
    // value '@Bool_and'" at link time) -- confirmed as a real bug via
    // a direct repro (`helper (true && false)`) while wiring this in.
    let t_infix : I64 <- Bench.now;
    let infixes := collect_infixes all_decls;
    let resolved_decls := resolve_infix_decls infixes all_decls;
    if verbose then do {
        Bench.report_since "infix_resolve" t_infix;
        return unit
    } else return unit;

    // Stage 3: dictionary-passing typeclass dispatch (see
    // plans/bootstrapping/self-hosted-compiler.md's Phases 2-4) -- same
    // "must run before reachability filtering" reasoning as infix
    // resolution just above: promotion (Phase 2) mints new top-level
    // defs (per-instance methods + dictionary values) that reachability
    // needs to see; constrained-def dict params (Phase 3) and call-site
    // resolution (Phase 4) rewrite `Class.method`-shaped references to
    // their real concrete/promoted targets, which reachability's own
    // name-based walk (`collect_referenced_names`) is blind to while
    // they're still unresolved class-method names. Order matters: Phase
    // 2 before 3 (Phase 3 reads a promoted method's own constraints,
    // which Phase 2 threads in from its owning Instance), Phase 3
    // before 4 (Phase 4 needs the dict PARAMETERS Phase 3 adds already
    // in place to know which locals are bound dicts).
    let t_dict : I64 <- Bench.now;
    let promoted_decls := promote_instance_defs resolved_decls;
    let dict_param_decls := add_constraint_dict_params_decls promoted_decls;
    if verbose then do {
        Bench.report_since "dict_dispatch" t_dict;
        return unit
    } else return unit;

    // Stage 4: try real dictionary-dispatch resolution via the type checker first
    // (`lang.typecheck.infer`'s `resolve_class_method`, using REAL
    // inferred types -- fixes the class of gap the syntactic
    // `resolve_class_calls_decls` pass below can't cover on its own; the
    // `Append_append` self-compile bug this whole plan exists to fix is
    // exactly that gap). `resolve_class_calls_decls` still always runs
    // afterward -- it's naturally idempotent on already-resolved calls
    // (`class_method_ref` no longer recognizes a rewritten reference as
    // `Class.method`-shaped) and covers what elaboration deliberately
    // doesn't (heterogeneous/multi-param classes, `instance_d` bodies
    // the checker's own per-decl walk never visits). If elaboration
    // fails ANYWHERE in the whole loaded graph (e.g. an unrelated,
    // pre-existing gap in a dependency having nothing to do with the
    // program actually being compiled), fall back to the original,
    // unelaborated decls -- this must never newly break a compile that
    // worked before this pass existed.
    //
    // Sub-timed with `bench_step` (`lang/module.mo`), the same helper
    // `elaborate_loaded_modules_cached` threads through its own pure
    // `let` chain. This phase was measured at 659182ms of a 969811ms
    // self-compile -- 68% of the whole thing -- behind ONE opaque
    // number, so which of these three operations owns it was unknown.
    // `bench_step`'s `forced` argument consumes each step's result so
    // the work lands inside its own span; the check that matters is
    // arithmetic (AGENTS.md item 25): these three must sum to the
    // `elaborate_class` total still printed below.
    let t_elab : I64 <- Bench.now;
    let target_mp : ModulePath := match get_loaded_main loaded { ModuleInfo.mk mp_ _ _ => mp_ };
    let scope_data : ScopeData := build_scope_from_decls target_mp dict_param_decls;
    let t_scope : I64 <- bench_step verbose "  elaborate_class: build_scope_from_decls" t_elab (List.length scope_data.classes);
    let scope : Scope := { module_id := target_mp, scope := scope_data, parent := Option.none };
    let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
    let elaborated := elaborate_module_decls_best_effort scope dict_param_decls empty_locs;
    let t_best_effort : I64 <- bench_step verbose "  elaborate_class: elaborate_module_decls_best_effort" t_scope (List.length elaborated);
    let dispatched_decls := resolve_class_calls_decls elaborated;
    let _t_dispatch : I64 <- bench_step verbose "  elaborate_class: resolve_class_calls_decls" t_best_effort (List.length dispatched_decls);
    if verbose then do {
        Bench.report_since "elaborate_class" t_elab;
        return unit
    } else return unit;

    // Stage 5: only compile Defs actually reachable (transitively) from `main` --
    // compiling the FULL 264-def loaded set unconditionally meant any
    // codegen bug anywhere in the whole standard library, reached or
    // not, blocked compiling any program at all. See
    // filter_reachable_decls's own doc comment.
    let t_reach : I64 <- Bench.now;
    // Bound to a local first: field access lowers only on a plain
    // identifier, not on a parenthesised call result.
    let main_mi : ModuleInfo := get_loaded_main loaded;
    let main_root : String := qualified_def_name_str main_mi.path (bare_modpath "main");
    let reachable_decls := filter_reachable_decls main_root dispatched_decls;
    if verbose then do {
        let reachable_count := List.length reachable_decls;
        Bench.report_since "filter_reachable" t_reach;
        println ("Reachable decl_list: " ++ I64.to_string reachable_count)
    } else return unit;

    // `resolve_class_calls_decls` can leave a `ClassName.method` call
    // unresolved with no matching instance (its own doc comment) -- check
    // the REACHABLE decls (not the full loaded graph: a bug in dead code
    // the program never uses must not block a compile that otherwise
    // works, see `validate_no_unresolved_class_calls`'s own doc comment
    // for the direct repro that found this the hard way) and fail here,
    // with a precise message, instead of proceeding to codegen/`llc` and
    // surfacing it many stages later as an undefined-symbol error.
    let dispatched_classes := collect_classes dispatched_decls;
    match validate_no_unresolved_class_calls dispatched_classes reachable_decls {
        Result.err e => do {
            if verbose then println ("FAILED at stage: resolve_class_calls_decls (" ++ e ++ ")") else return unit;
            return (Result.err e)
        },
        Result.ok _ =>
            // Same fail-fast reasoning as `validate_no_unresolved_class_calls`
            // just above, for the silent-"return Unit"-stub bug family --
            // a reachable bodyless `#[native X]` def wired nowhere would
            // otherwise compile to a stub only discovered as a runtime
            // SIGSEGV in the resulting binary (`String_to_list`'s v25
            // crash; see `validate_no_unwired_natives`'s own doc comment).
            match validate_no_unwired_natives reachable_decls {
                Result.err e => do {
                    if verbose then println ("FAILED at stage: validate_no_unwired_natives (" ++ e ++ ")") else return unit;
                    return (Result.err e)
                },
                Result.ok _ =>
                  // And once more for the OTHER silent-placeholder path
                  // codegen has: a struct literal that best-effort
                  // elaboration never desugared still compiles to
                  // `void_val` (see `validate_no_undesugared_struct_lits`).
                  match validate_no_undesugared_struct_lits reachable_decls {
                    Result.err e => do {
                        if verbose then println ("FAILED at stage: validate_no_undesugared_struct_lits (" ++ e ++ ")") else return unit;
                        return (Result.err e)
                    },
                    Result.ok _ =>
                      // And the collision gate: after qualification no two
                      // SOURCE defs can share a symbol, so anything this
                      // finds is a synthesized or runtime-symbol clash.
                      match validate_no_colliding_def_symbols reachable_decls {
                        Result.err e => do {
                            if verbose then println ("FAILED at stage: validate_no_colliding_def_symbols (" ++ e ++ ")") else return unit;
                            return (Result.err e)
                        },
                        Result.ok _ => do {
                    // Stage 6: compile the reachable, infix-resolved declarations to LLVM IR
                    let t_llvm : I64 <- Bench.now;
                    let mod_ := compile_db_module_with_debug reachable_decls source_path debug_files;
                    if verbose then do {
                        Bench.report_since "compile_db_module" t_llvm;
                        Bench.report_since "compile_loaded_modules_to_ir total" total_start;
                        return unit
                    } else return unit;

                    // Stage 7: the emitted module must not call a symbol
                    // nothing defines. Nothing else in this pipeline
                    // catches that -- it renders happily into the `.ll`
                    // and dies at `llc` as `undefined value '@x'`, at the
                    // END of a 15-25 minute self-compile, naming one
                    // symbol and no call site.
                    return (validate_all_call_targets_defined mod_)
                        },
                      },
                  },
            },
    }
      },
    }
}

// ─── Module-qualified symbols ────────────────────────────────────────
//
// Every top-level `def` is emitted under its module-qualified name
// (`lang.typecheck.infer.inductive_bare_name`), and every reference to
// one is re-pointed at the module that actually owns it.
//
// Without this the whole program is a single flat namespace -- Stage 1
// below flattens every module's decls with no prefixing, and both
// `build_def_name_map` (reachability) and `dedup_funcs_by_name` (shim
// collapsing) then silently keep exactly ONE of any same-named pair.
// 19 top-level names are declared by two or more non-test modules in
// this corpus; 16 are live in `lang/main.mo`'s own closure. One of them
// crashed the self-compiled compiler: `inductive_bare_name` exists in
// both `lang/typecheck/meta_reflect.mo` (`-> String`) and
// `lang/typecheck/infer.mo` (`-> Identifier`), the String one won, and
// `con_result_type` stored a raw `char*` into a `DebugName.named`
// slot -- read back later as an `Identifier` by
// `Similar_Identifier_similar`, whose single-constructor match reads
// field 0 with no tag check, giving `strcmp("List", 0x1)`.
// See AGENTS.md items 18/19, which name this exact fix as the
// principled one.

// ─── Tests: module-qualified symbols ────────────────────────────────
//
// These build `ModuleInfo`s by hand rather than going through the
// loader, so they exercise exactly the qualification pass -- the shape
// that matters is two modules and one shared name, which no real
// fixture file can express as compactly.

/// The gate behind the qualification: two defs on one symbol must fail
/// the build, not silently lose one.
#[test]
def test_collision_gate_rejects_two_defs_on_one_symbol : Bool :=
    let d1 := qtest_def "dup" "x" in
    let d2 := qtest_def "dup" "y" in
    match validate_no_colliding_def_symbols (List.cons d1 (List.cons d2 List.empty)) {
        Result.err _ => true,
        Result.ok _ => false,
    }

/// ...and it must not fire on a program that is actually fine.
#[test]
def test_collision_gate_accepts_distinct_symbols : Bool :=
    let d1 := qtest_def "a::dup" "x" in
    let d2 := qtest_def "b::dup" "y" in
    match validate_no_colliding_def_symbols (List.cons d1 (List.cons d2 List.empty)) {
        Result.err _ => false,
        Result.ok _ => true,
    }

/// A def landing on a runtime symbol is the same silent drop --
/// `compile_db_module_with_debug` puts the runtime natives FIRST, so the
/// runtime one wins and the real def disappears.
#[test]
def test_collision_gate_rejects_runtime_symbol_clash : Bool :=
    match validate_no_colliding_def_symbols (List.cons (qtest_def "monad_string_to_list" "x") List.empty) {
        Result.err _ => true,
        Result.ok _ => false,
    }
