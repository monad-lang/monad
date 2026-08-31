use io {IO}
use std.bench {now, report}
// `str_map_*` below is a `std.map` `HashMap String V`. Empty import:
// naming any of `std.map`'s `Map`-class-instance exports explicitly hits
// a pre-existing latent instance/dictionary-resolution bug (same
// workaround `lang/scope.mo`'s own `modpath_map_*`/`use std.map {}` doc
// comment documents, and `std/map_tests.mo`/`bench/scope_lookup.mo`
// already use) -- everything remains available regardless via the same
// always-on mechanism that lets any top-level type/def resolve without
// being explicitly `use`d.
use std.map {}
use lang.types {
  Con, DebugName, Decl, Def, Identifier, InductConstructor, Inductive, Literal,
  LoadedModules, LocalScope, MatchCase, ModulePath, Native, Operator,
  Param, Scope, ScopeData, StructLitField, Term,
  app, con, ctx, def_d, forall, hole, id, if_, inductive_d, join_identifiers, lam,
  lit, match_, mc, mk, mp, name, named, ntv, num, operator,
  param_many, pi, show_identifier, str, type_, unnamed, var,
}
use lang.codegen.ir {
  LLVMBasicBlock, LLVMDeclaration, LLVMFunction, LLVMGlobal, LLVMInstruction,
  LLVMModule, LLVMType, LLVMValue, NativeOp, ParamPair, PhiPair, add, alloc_closure,
  alloc_constructor, assign, bitcast, bool_, branch, call, comment, emit_module,
  fn_, gep, global_, i64_, i8_, icmp_eq, icmp_ne, icmp_sgt, icmp_slt, int32_, int_,
  jump, load, mk, mul, native_op, op_add, op_eq, op_file_exists, op_gt, op_lt,
  op_mul, op_ne, op_print_str, op_read_file, op_sdiv, op_sub, op_write_file,
  parm_, phi, ptr, ptrtoint, ret, sdiv, show_llvm_type, sub, trunc, var_, void_val, zext,
}
use lang.module {
  LoadedModules, ModuleInfo, elaborate_module_decls_best_effort, get_loaded_all,
  get_loaded_main, get_module_info_decls, mk, resolve_open_aliases_in_modules,
}
use lang.scope {
  add_constraint_dict_params_decls, build_scope_from_decls, collect_classes,
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

struct LocalBinding {
    name : Identifier,
    val : LLVMValue,
}

struct CodegenCtx {
    locals : List LocalBinding,
    next_temp : I64,
    next_label : I64,
    /// Each top-level def's own known arity (its param count, i.e. the
    /// number of leading `Term.lam`s in its body) keyed by the SAME
    /// `llvm_name` a bare `Term.var` reference to it would compute
    /// (`replace_dots_with_underscores` of its module path) -- built once
    /// per module compile (`build_arity_table`) so `Term.var`'s
    /// value-position case (Phase 0 of the dictionary-passing plan, see
    /// plans/bootstrapping/self-hosted-compiler.md) can tell an arity-0
    /// def (still an eager 0-arg call, unchanged) from an arity>0 def (now
    /// boxed via `alloc_closure` instead of miscompiling as a 0-arg call
    /// to a function that isn't one). A `HashMap` (not a `List`), mirroring
    /// `ctor_tags` -- looked up once per `Term.var` reference across a
    /// whole compile, the same shape that already made `ctor_tags`/
    /// `filter_reachable`'s HashMap conversions decisive wins.
    arities : HashMap String I64,
    ctor_tags : HashMap String I64,
}

type CompileResult {
    ok (ctx : CodegenCtx) (instrs : List LLVMInstruction) (val : LLVMValue) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal),
}

struct CtxStrPair {
    ctx : CodegenCtx,
    str : String,
}

#[partial]
def empty_bindings : List LocalBinding := List.empty

#[partial]
def empty_arities : HashMap String I64 := str_map_empty

/// `arities` -- see `CodegenCtx`'s own doc comment. Callers with a real
/// `List Def` in scope should build one via `build_arity_table` instead
/// of passing `empty_arities` (an empty table just means every bare
/// global reference falls back to today's eager-0-arg-call behavior --
/// correct only for genuinely 0-arity defs).
#[partial]
def empty_ctx (arities : HashMap String I64) (ctor_tags : HashMap String I64) : CodegenCtx :=
    { locals := empty_bindings, next_temp := 0, next_label := 0, arities := arities, ctor_tags := ctor_tags }

#[partial]
def fresh_temp (c : CodegenCtx) : CtxStrPair :=
    let name := String.concat "t" (I64.to_string c.next_temp) in
    let c2 : CodegenCtx := { c with next_temp := c.next_temp + 1 } in
    CtxStrPair.mk c2 name

#[partial]
def fresh_label (c : CodegenCtx) (prefix : String) : CtxStrPair :=
    let name := String.concat prefix (String.concat "_" (I64.to_string c.next_label)) in
    let c2 : CodegenCtx := { c with next_label := c.next_label + 1 } in
    CtxStrPair.mk c2 name

#[partial]
def ctx_bind_local (c : CodegenCtx) (name : Identifier) (val : LLVMValue) : CodegenCtx :=
    let binding : LocalBinding := LocalBinding.mk name val in
    { c with locals := List.cons binding c.locals }

#[partial]
def ctx_lookup_local (c : CodegenCtx) (name : Identifier) : Option LLVMValue := lookup_binding c.locals name

/// Looks up `name`'s constructor tag from `c`'s own dynamically-built
/// table (`build_constructor_tag_map`) -- the fallback `is_constructor_
/// var_dyn`/`constructor_tag_dyn` use for anything not in the hardcoded
/// builtin list.
#[partial]
def ctx_lookup_ctor_tag (c : CodegenCtx) (name : String) : Option I64 := str_map_lookup name c.ctor_tags

/// Rebuilds `c` with an EMPTY `locals` list, preserving `next_temp`/
/// `next_label`/`arities`. Used when entering a freshly-lifted
/// function's own body (`compile_db_lam_ir`) -- the OUTER function's
/// locals must not leak through as stale cross-function SSA references
/// (this is the closure-free-variable-capture fix's actual correctness
/// backbone, not just an optimization: `ctx_bind_local` alone only
/// PREPENDS to whatever locals list it's handed, it never resets one --
/// so without this, a lifted function's ctx still carries every binding
/// visible in its ENCLOSING function, and a free-variable reference
/// inside the lifted body would silently "succeed" via `ctx_lookup_local`
/// against a register — `parm_`/`var_` — that belongs to the outer
/// function and doesn't exist in the lifted one at all, which is
/// exactly the `llc: use of undefined value` bug this whole fix exists
/// for). Only the lambda's own param and its explicitly rebuilt
/// captures (`build_get_env_instrs`) should be visible inside.
#[partial]
def ctx_reset_locals (c : CodegenCtx) : CodegenCtx := { c with locals := empty_bindings }

/// The other half of `ctx_reset_locals`: after compiling a lifted
/// function's own body (`compile_db_lam_ir`) with a reset-and-rebuilt
/// `locals` list (the lambda's own param + its captures ONLY), the ctx
/// handed back to the ENCLOSING function's own ongoing compilation must
/// have its ORIGINAL locals restored -- `outer`'s own `locals`, i.e.
/// whatever was visible right before this lambda was compiled -- while
/// still carrying forward `inner`'s updated `next_temp`/`next_label`
/// counters (so the enclosing function's own subsequent fresh names
/// don't collide with names already used inside the lifted function).
/// Confirmed as a real, distinct bug via a direct repro: without this,
/// a SECOND lifted lambda compiled later in the SAME enclosing
/// function's body (e.g. a do-block's own trailing `pure hole`
/// continuation, itself its own `compile_db_lam_ir` call, compiled
/// right after an EARLIER nested do-block's own lambda already reset
/// the ctx) silently loses every local bound BEFORE that first lambda
/// (a `let n := 5` two statements up) -- its own free-variable capture
/// then finds `n` nowhere in `ctx_lookup_local` at all (not even as a
/// missed-capture bug; the outer LOCAL BINDING itself is gone from the
/// ctx by this point), so `n` gets treated as an unknown GLOBAL name
/// instead and silently miscompiles into a bogus 0-arg call
/// (`call i64 @n()`, `llc: use of undefined value '@n'`).
#[partial]
def ctx_restore_locals (outer : CodegenCtx) (inner : CodegenCtx) : CodegenCtx := { inner with locals := outer.locals }

/// Looks up a global's own known arity by its already-mangled
/// `llvm_name` (see `CodegenCtx.arities`'s doc comment). `Option.none`
/// for any name not in the table -- a name genuinely absent from the
/// compiled module's own def list (shouldn't happen for a real reachable
/// reference) as well as for a module compiled via `empty_ctx
/// empty_arities` (no table built) both fall back safely to the
/// pre-Phase-0 eager-0-arg-call behavior at the one call site that reads
/// this (`compile_db_term_ir`'s `Term.var` value-position case) --
/// correct for 0-arity defs, and no worse than before Phase 0 for
/// anything else. A direct `str_map_lookup` -- this table is built ONCE
/// per module compile and looked up once per `Term.var` reference across
/// the whole compiled program, the same shape `ctor_tags`/
/// `filter_reachable` already measured as a decisive HashMap win over a
/// `List`+linear-scan at this corpus's scale.
#[partial]
def ctx_lookup_arity (c : CodegenCtx) (llvm_name : String) : Option I64 := str_map_lookup llvm_name c.arities

/// Builds the arity table `empty_ctx` needs from a module's own `List
/// Def`, keyed by the exact same `llvm_name` `compile_db_def_ir` gives
/// each def's own compiled LLVM function (`replace_dots_with_underscores`
/// of its module path) -- callers (`compile_db_decls_ir`/
/// `compile_db_module`) always have the full `List Def` in scope before
/// compiling any of them, so this runs once per module compile, not per
/// reference.
#[partial]
def build_arity_table (defs : List Def) : HashMap String I64 := build_arity_table_go defs str_map_empty

#[partial]
def build_arity_table_go (defs : List Def) (acc : HashMap String I64) : HashMap String I64 := match defs {
    List.empty => acc,
    List.cons d rest =>
        match d {
            Def.mk name typ term_ constraints attrs _vis =>
                let llvm_name := replace_dots_with_underscores (module_path_to_str name) in
                let arity := List.length (collect_db_params term_) in
                build_arity_table_go rest (str_map_insert llvm_name arity acc),
        },
}

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
        (String.concat "* @" (String.concat llvm_name " to i8*)")))

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
    let params := cons_pair self_pair real_params in
    let fwd_args := shim_fwd_args arity 1 in
    let call_val := LLVMValue.call real_name LLVMType.i64_ fwd_args false in
    let call_instr := LLVMInstruction.assign "r" call_val in
    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ "r") in
    let entry_block := LLVMBasicBlock.mk "entry" (cons_instr call_instr (cons_instr ret_instr empty_instrs)) in
    LLVMFunction.mk shim_name params LLVMType.i64_ (cons_block entry_block empty_blocks) false

#[partial]
def build_llvm_params_from_db_shifted (n : I64) (start_idx : I64) : List ParamPair :=
    if I64.beq n 0 then empty_pairs
    else cons_pair (ParamPair.mk (String.concat "p" (I64.to_string start_idx)) LLVMType.i64_)
        (build_llvm_params_from_db_shifted (n - 1) (start_idx + 1))

#[partial]
def shim_fwd_args (n : I64) (start_idx : I64) : List LLVMValue :=
    if I64.beq n 0 then empty_vals
    else cons_val (LLVMValue.parm_ start_idx) (shim_fwd_args (n - 1) (start_idx + 1))

#[partial]
def lookup_binding (bindings : List LocalBinding) (name : Identifier) : Option LLVMValue := match bindings {
    List.empty => Option.none,
    List.cons b rest =>
        match b {
            { name := lname, val := lval } =>
                if identifier_eq lname name
                then Option.some lval
                else lookup_binding rest name,
        },
}

#[partial]
def identifier_eq (a : Identifier) (b : Identifier) : Bool := match a {
    Identifier.id as => match b {
        Identifier.id bs => String.beq as bs,
    },
}

/// A genuine, previously-undiscovered bug lived here (and in
/// `string_find_last_loop` below) until this session: `String.slice`'s
/// own signature (`init/string.mo`) is `(s, start, LEN)` -- a LENGTH,
/// not an end index -- but both call sites here passed `String.length
/// name` (the WHOLE string's own length, an end-index-shaped value) as
/// the LEN argument, silently reading past the intended suffix's real
/// length. Latent/unnoticed for a long time because `constructor_tag`'s
/// own "check qualified names first" tier (whole-string comparisons
/// against `"IO.io"`/`"Unit.unit"`/... ) never needed this "base name"
/// fallback tier to work correctly for any of the ~16 hardcoded
/// builtins; only surfaced once the new dynamic `ctor_tags` fallback
/// (`build_constructor_tag_map`) started relying on `extract_base_name`
/// actually stripping a qualifier correctly. Confirmed via an isolated
/// unit test bypassing the whole self-hosted pipeline: `extract_base_
/// name "Option.Some"` returned `"Option.Some"` unchanged (the `last_dot
/// > -1` branch's own slice never actually fired due to `string_find_
/// last`'s OWN identical bug below, so this line's fix matters once that
/// one is fixed too).
#[partial]
def extract_base_name (name : String) : String :=
    let last_dot := string_find_last name "." in
    if I64.gt last_dot (-1)
    then String.slice name (last_dot + 1) (String.length name - last_dot - 1)
    else name

/// The ~16 builtin constructors' tags (0-15), keyed by BOTH their
/// qualified ("IO.io") and base ("io") name forms -- built once, looked
/// up via `str_map_lookup` instead of a hand-rolled `if/else-if` chain.
/// Tags match the runtime's own assignment; left completely unchanged
/// from the original hardcoded chain this replaces -- zero risk to
/// already-working code, purely a readability/dispatch-mechanism change.
#[partial]
def builtin_ctor_tags : HashMap String I64 :=
    let m := str_map_empty in
    let m := str_map_insert "IO.io" 7 m in
    let m := str_map_insert "Unit.unit" 0 m in
    let m := str_map_insert "Bool.true" 1 m in
    let m := str_map_insert "Bool.false" 2 m in
    let m := str_map_insert "Option.none" 3 m in
    let m := str_map_insert "Option.some" 4 m in
    let m := str_map_insert "List.empty" 5 m in
    let m := str_map_insert "List.cons" 6 m in
    let m := str_map_insert "unit" 0 m in
    let m := str_map_insert "true" 1 m in
    let m := str_map_insert "false" 2 m in
    let m := str_map_insert "none" 3 m in
    let m := str_map_insert "some" 4 m in
    let m := str_map_insert "empty" 5 m in
    let m := str_map_insert "cons" 6 m in
    let m := str_map_insert "io" 7 m in
    let m := str_map_insert "trivial" 8 m in
    let m := str_map_insert "refl" 9 m in
    let m := str_map_insert "ok" 10 m in
    let m := str_map_insert "err" 11 m in
    let m := str_map_insert "zero" 12 m in
    let m := str_map_insert "succ" 13 m in
    let m := str_map_insert "nil" 14 m in
    let m := str_map_insert "pair" 15 m in
    m

/// Falls back to `c`'s own dynamically-built `ctor_tags` table
/// (`build_constructor_tag_map`) for anything not in `builtin_ctor_tags`
/// -- every user-defined inductive's constructor, and any BUILTIN
/// constructor referenced by its full dotted name in a shape
/// `builtin_ctor_tags` doesn't happen to enumerate.
#[partial]
def constructor_tag (c : CodegenCtx) (name : String) : I64 :=
    let base_name := extract_base_name name in
    match str_map_lookup name builtin_ctor_tags {
        Option.some tag => tag,
        Option.none =>
            match str_map_lookup base_name builtin_ctor_tags {
                Option.some tag => tag,
                Option.none =>
                    match ctx_lookup_ctor_tag c base_name {
                        Option.some tag => tag,
                        Option.none => 0,
                    },
            },
    }

/// Check if a variable name is a known constructor.
/// Handles both simple names ("unit", "true") and qualified names ("Unit.unit", "IO.io"),
/// falling back to `c`'s own dynamically-built `ctor_tags` table
/// (`build_constructor_tag_map`) for anything not in `builtin_ctor_tags`
/// -- see `constructor_tag`'s own doc comment.
#[partial]
def is_constructor_var (c : CodegenCtx) (name : String) : Bool :=
    let base_name := extract_base_name name in
    match str_map_lookup base_name builtin_ctor_tags {
        Option.some _ => true,
        Option.none =>
            match ctx_lookup_ctor_tag c base_name {
                Option.some _ => true,
                Option.none => false,
            },
    }

#[partial]
def show_identifier (id : Identifier) : String := match id {
    Identifier.id s => remove_quotes_from_identifier s,
}

#[partial]
def remove_quotes_from_identifier (s : String) : String := 
    remove_quotes_loop s ""

#[partial]
def remove_quotes_loop (s : String) (acc : String) : String := 
    if String.beq s "" then acc
    else
        let first_byte : U8 := match String.get s 0 {
            Option.some b => b,
            Option.none => 0u8
        } in
        let single_quote : U8 := 39u8 in
        if U8.beq first_byte single_quote then
            remove_quotes_loop (String.slice s 1 (String.length s)) acc
        else
            remove_quotes_loop (String.slice s 1 (String.length s)) (String.concat acc (String.slice s 0 1))

/// Find the last occurrence of a substring in a string, return its index or -1
#[partial]
def string_find_last (haystack : String) (needle : String) : I64 :=
    if String.beq needle "" then -1
    else if I64.gt (String.length needle) (String.length haystack) then -1
    else string_find_last_loop haystack needle (String.length haystack - String.length needle)

/// `String.slice`'s own third argument is a LENGTH (`init/string.mo`),
/// not an end index -- see `extract_base_name`'s own doc comment for
/// the full story on this bug (fixed alongside it here).
#[partial]
def string_find_last_loop (haystack : String) (needle : String) (start_idx : I64) : I64 :=
    if I64.lt start_idx 0 then -1
    else if String.beq (String.slice haystack start_idx (String.length needle)) needle then start_idx
    else string_find_last_loop haystack needle (start_idx - 1)

#[partial]
def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

#[partial]
def cons_val (v : LLVMValue) (vs : List LLVMValue) : List LLVMValue := List.cons v vs

#[partial]
def lookup_native (name : String) : Option NativeOp := str_map_lookup name native_op_table

/// `"I64_eq"` (no such identifier exists -- `I64.eq` doesn't typecheck,
/// "unknown variable") is deliberately NOT one of this table's keys: the
/// real, only I64 equality function throughout the whole corpus is
/// `I64.beq` (`init/number.mo`, the `BEq I64` instance's own method),
/// which mangles to `I64_beq`, never matching a hypothetical `"I64_eq"`
/// entry at all. Confirmed as a real, previously undiscovered gap via a
/// direct repro: `I64.beq` compiled to the generic "return Unit" stub
/// (`native_runtime_fn_name` has no entry for it either) both as a bare
/// call AND as an `if`'s own condition (`is_native_bool_op_name`/
/// `ensure_i1_cond` never recognized it as already-i1 either, same root
/// cause) -- every I64 equality check in real code silently miscompiled.
/// `I64.ne`/`"I64_ne"` has the same "no such identifier" shape
/// (`Bool.not (I64.beq a b)` is how real code expresses it, per this
/// session's own `materialize_native_bool_arg` fix) -- its `"I64_ne"` key
/// below is left as dead code, not touched here (nothing reaches it, out
/// of scope for this fix).
///
/// Deliberately NO bare "read_file"/"write_file"/"file_exists"/"is_dir"
/// keys (unlike "println", which keeps one): `std/io.mo`'s Path refactor
/// split each into a bodyless `#[native "X"]` primitive
/// (`IO.X_native`) plus a real-bodied `IO.X` wrapper (unwraps `Path` to
/// `String` first). `try_compile_inline_native_db` matches purely on
/// the CALLEE'S TEXTUAL NAME (`lookup_native_any`'s `extract_base_name`
/// strips the module qualifier, so `IO.X` and `IO.X_native` are
/// indistinguishable from a bare key "X") -- it does not check whether
/// that name actually resolves to the native-tagged def or to an
/// unrelated same-named wrapper. A bare "X" key here would silently
/// hijack every call to the WRAPPER `IO.X` too, skipping its `Path.to_
/// string` unwrap and passing the raw boxed `Path` constructor straight
/// to `monad_X`'s C implementation. Confirmed live: `IO.is_dir (Path.
/// path "/tmp")` read garbage past the `Path` object's header instead
/// of the real string, always false when compiled and run (correct
/// under the tree-walking interpreter, which doesn't go through this
/// codegen path at all -- invisible to `test`/`check`). `IO.write_file`/
/// `read_file`/`file_exists` have the identical wrapper/native name
/// collision and are called throughout `lang/main.mo`/`lang/module.mo`/
/// `lang/codegen/link.mo` -- this was silently corrupting the self-
/// compile's own compiled-and-run behavior. `IO.list_dir` was never
/// given a bare key at all and was never affected -- confirms the fix:
/// with no bare key, `IO.X_native`'s own call still dispatches
/// correctly (through a separate, properly-scoped attribute-based
/// mechanism unaffected by this table), while `IO.X`'s wrapper call
/// goes through ordinary compilation instead of being hijacked.
#[partial]
def native_op_table : HashMap String NativeOp :=
    let m := str_map_empty in
    let m := str_map_insert "I64_add" NativeOp.op_add m in
    let m := str_map_insert "I64_sub" NativeOp.op_sub m in
    let m := str_map_insert "I64_mul" NativeOp.op_mul m in
    let m := str_map_insert "I64_div" NativeOp.op_sdiv m in
    let m := str_map_insert "I64_beq" NativeOp.op_eq m in
    let m := str_map_insert "I64_lt" NativeOp.op_lt m in
    let m := str_map_insert "I64_gt" NativeOp.op_gt m in
    let m := str_map_insert "I64_ne" NativeOp.op_ne m in
    let m := str_map_insert "monad_print_str" NativeOp.op_print_str m in
    let m := str_map_insert "println" NativeOp.op_print_str m in
    let m := str_map_insert "monad_read_file" NativeOp.op_read_file m in
    let m := str_map_insert "monad_write_file" NativeOp.op_write_file m in
    let m := str_map_insert "monad_file_exists" NativeOp.op_file_exists m in
    let m := str_map_insert "monad_is_dir" NativeOp.op_is_dir m in
    let m := str_map_insert "monad_string_hash" NativeOp.op_string_hash m in
    let m := str_map_insert "I64_to_string" NativeOp.op_i64_to_string m in
    m

/// `lookup_native` needs its match arms in two different forms depending
/// on caller: dotted arithmetic ops (`I64.add`) are only registered
/// under their fully-qualified, underscore-mangled form ("I64_add", to
/// agree with `compile_db_def_ir`'s own `replace_dots_with_underscores`
/// naming for the real global -- not that this global is ever actually
/// called when this fast path fires, but the table's naming convention
/// still has to agree with it), while the IO natives are registered
/// under their bare unqualified form ("println", not "IO_println") since
/// they're called both qualified (`IO.println`) and via an `open`ed bare
/// name. `try_compile_inline_native_db` used to look up ONLY the
/// bare-extracted form (`extract_base_name "I64.add"` => "add"), which
/// can never match "I64_add" -- so this fast path silently never fired
/// for any dotted arithmetic call, falling through to a real call to the
/// named global. That's normally invisible (the global just does the
/// same arithmetic) EXCEPT `I64.add`/`I64.sub`/etc. are native-signature
/// defs with no `:=` body at all (`init/number.mo`) -- their "body" is
/// `Term.hole`, which `compile_db_def_ir` compiles as a bogus `Unit`
/// constructor stub. Confirmed via a direct repro
/// (`let a := 2 in let b := 3 in I64.add a b`, non-literal so constant
/// folding doesn't hide it): every dotted arithmetic call silently
/// returned a garbage heap pointer instead of computing anything. Try
/// the underscore-mangled form first (covers arithmetic), then the
/// bare-extracted form (covers IO), so both naming conventions work.
#[partial]
def lookup_native_any (name : String) : Option NativeOp :=
    match lookup_native (replace_dots_with_underscores name) {
        Option.some op => Option.some op,
        Option.none => lookup_native (extract_base_name name),
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

#[partial]
def empty_instrs : List LLVMInstruction := List.empty

/// Now total (no `#[partial]`): every `Literal` variant is handled,
/// including `struct_lit`/`struct_update` — see their own doc comment
/// below for why they're unreachable-in-practice placeholders rather
/// than real codegen, and `lang/typecheck/infer.mo`'s
/// `type_check_struct_lit`/`type_check_struct_update` for where the
/// REAL work happens (both desugar into `Term.con`, which
/// `compile_db_term_ir`/`compile_con_ir` above already handle).
def compile_lit_ir (c : CodegenCtx) (lit_ : Literal) : CompileResult := match lit_ {
    Literal.num n suffix => CompileResult.ok c empty_instrs (LLVMValue.int_ n) empty_blocks empty_funcs empty_globals_list,
    // No LLVMValue float-constant variant exists yet (codegen has no
    // float support at all currently — a separate, unstarted piece of
    // work; see Literal.flt's doc comment in lang/types.mo). Emitting a
    // zero placeholder keeps this match total without pretending to
    // support something that isn't there yet; nothing in the corpus
    // reaches this arm today.
    Literal.flt text suffix => CompileResult.ok c empty_instrs (LLVMValue.int_ 0) empty_blocks empty_funcs empty_globals_list,
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
                        CompileResult.ok ctx2 (cons_instr cast_instr empty_instrs) (LLVMValue.var_ temp) empty_blocks empty_funcs (cons_global global empty_globals_list),
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
    Literal.struct_lit _fields _type_name => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
    Literal.struct_update _base _fields => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
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
            CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
        List.cons _ _ =>
            match compile_db_term_ir c scrutinee {
                CompileResult.ok ctx_s instrs_s val_s blocks_s funcs_s globals_s =>
                    match fresh_temp ctx_s {
                        CtxStrPair.mk ctx_tag tag_temp =>
                            let tag_call := LLVMValue.call "monad_get_tag" LLVMType.i64_ (cons_val val_s empty_vals) false in
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
                                            let tag_and_jump := cons_instr tag_instr (cons_instr (LLVMInstruction.jump first_check_label) empty_instrs) in
                                            match compose_seq ({ instrs := instrs_s, blocks := blocks_s, val := val_s }) ({ instrs := tag_and_jump, blocks := empty_blocks, val := tag_val }) {
                                                { instrs := entry_instrs, blocks := blocks_s_spliced, val := _ } =>
                                                    match build_match_chain ctx_merge tag_val val_s cases merge_label first_check_label {
                                                        { ctx := ctx_chain, blocks := chain_blocks, funcs := chain_funcs, globals := chain_globals, phis := phi_pairs } =>
                                                            match fresh_temp ctx_chain {
                                                                CtxStrPair.mk ctx_final phi_temp =>
                                                                    let phi_instr := LLVMInstruction.assign phi_temp (LLVMValue.phi phi_pairs) in
                                                                    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ phi_temp) in
                                                                    let merge_block := LLVMBasicBlock.mk merge_label (cons_instr phi_instr (cons_instr ret_instr empty_instrs)) in
                                                                    let all_blocks := append_blocks blocks_s_spliced (cons_block merge_block chain_blocks) in
                                                                    let all_funcs := append_funcs funcs_s chain_funcs in
                                                                    let all_globals := append_globals globals_s chain_globals in
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
            { ctx := c, blocks := empty_blocks, funcs := empty_funcs, globals := empty_globals_list, phis := empty_phis },
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
                                                MatchCase.mc name _args _body _fp =>
                                                    let tag_of_case := constructor_tag ctx3 (show_identifier name) in
                                                    let cmp_instr := LLVMInstruction.assign cmp_temp (LLVMValue.icmp_eq tag_val (LLVMValue.int_ tag_of_case)) in
                                                    let branch_instr := LLVMInstruction.branch (LLVMValue.var_ cmp_temp) case_label next_check_label in
                                                    let check_block := LLVMBasicBlock.mk check_label (cons_instr cmp_instr (cons_instr branch_instr empty_instrs)) in
                                                    match build_match_case_block ctx3 scrutinee_val this_case case_label merge_label {
                                                        { ctx := ctx4, blocks := case_blocks, funcs := case_funcs, globals := case_globals, phis := case_phis } =>
                                                            match build_match_chain ctx4 tag_val scrutinee_val rest merge_label next_check_label {
                                                                { ctx := ctx5, blocks := rest_blocks, funcs := rest_funcs, globals := rest_globals, phis := rest_phis } =>
                                                                    {
                                                                        ctx := ctx5,
                                                                        blocks := cons_block check_block (append_blocks case_blocks rest_blocks),
                                                                        funcs := append_funcs case_funcs rest_funcs,
                                                                        globals := append_globals case_globals rest_globals,
                                                                        phis := append_phis case_phis rest_phis,
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
        List.empty => { ctx := c, instrs := empty_instrs },
        List.cons name rest =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 temp =>
                    let field_call := LLVMValue.call "monad_get_field" LLVMType.i64_ (cons_val scrutinee_val (cons_val (LLVMValue.int_ idx) empty_vals)) false in
                    let field_instr := LLVMInstruction.assign temp field_call in
                    let ctx2 := ctx_bind_local ctx1 name (LLVMValue.var_ temp) in
                    match bind_match_fields ctx2 scrutinee_val rest (idx + 1) {
                        { ctx := ctx3, instrs := rest_instrs } =>
                            { ctx := ctx3, instrs := cons_instr field_instr rest_instrs },
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
                        let new_instrs := append_instrs without_ret (cons_instr (LLVMInstruction.jump merge_label) empty_instrs) in
                        Option.some { blocks := List.cons (LLVMBasicBlock.mk label new_instrs) rest, label := label }
                    else
                        match retarget_terminal_ret rest target_val merge_label {
                            Option.some result => Option.some { blocks := List.cons b result.blocks, label := result.label },
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
                            let raw_instrs := append_instrs field_instrs instrs_r in
                            let already_terminated := ends_with_terminator raw_instrs in
                            let bmr := materialize_branch_val ctx_r body raw_instrs val_r_raw in
                            let case_block := build_branch_block case_label merge_label bmr.instrs in
                            if already_terminated
                            then
                                match retarget_terminal_ret blocks_r bmr.val merge_label {
                                    Option.some result =>
                                        { ctx := bmr.ctx, blocks := cons_block case_block result.blocks, funcs := funcs_r, globals := globals_r, phis := cons_phi (PhiPair.mk bmr.val result.label) empty_phis },
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
                                        { ctx := bmr.ctx, blocks := cons_block case_block blocks_r, funcs := funcs_r, globals := globals_r, phis := empty_phis },
                                }
                            else
                                { ctx := bmr.ctx, blocks := cons_block case_block blocks_r, funcs := funcs_r, globals := globals_r, phis := cons_phi (PhiPair.mk bmr.val case_label) empty_phis },
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

/// Sequences each arg's own compiled fragment via `compose_seq` (see
/// its own extended doc comment above `ends_with_terminator`) instead
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
                                            let instrs_m := append_instrs instrs (append_instrs void_instrs bool_instrs) in
                                            match compose_seq ({ instrs := acc_instrs, blocks := acc_blocks, val := acc_val }) ({ instrs := instrs_m, blocks := blocks_t, val := val }) {
                                                { instrs := new_instrs, blocks := new_blocks, val := new_val } =>
                                                    compile_ntv_args_go ctx_tb rest
                                                        new_instrs new_blocks
                                                        (append_funcs acc_funcs funcs_t)
                                                        (append_globals acc_globals globals_t)
                                                        (cons_val val acc_vals)
                                                        new_val,
                                            },
                                    },
                            },
                    },
                Option.none =>
                    compile_ntv_args_go c rest acc_instrs acc_blocks acc_funcs acc_globals acc_vals acc_val,
            },
        List.empty =>
            { ctx := c, instrs := acc_instrs, vals := rev_vals acc_vals empty_vals, blocks := acc_blocks, funcs := acc_funcs, globals := acc_globals, last_val := acc_val },
    }

#[partial]
def compile_ntv_args (c : CodegenCtx) (args : List (Option Term)) (acc_instrs : List LLVMInstruction) (acc_vals : List LLVMValue) : NtvArgs :=
    compile_ntv_args_go c args acc_instrs empty_blocks empty_funcs empty_globals_list acc_vals LLVMValue.void_val

#[partial]
def rev_vals (xs : List LLVMValue) (acc : List LLVMValue) : List LLVMValue := match xs {
    List.cons x rest => rev_vals rest (cons_val x acc),
    List.empty => acc,
}

struct MaterializedVal {
    ctx : CodegenCtx,
    instrs : List LLVMInstruction,
    val : LLVMValue,
}

/// Substitutes a genuine heap-allocated Unit value for `LLVMValue.void_val`
/// wherever one is about to be used as a function-call ARGUMENT -- a real
/// call-argument position never accepts LLVM's own `void` type (only a
/// function's own RETURN type may be `void`). Mirrors the identical
/// `void_val -> alloc_constructor 0 empty_vals` substitution
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
/// `empty_instrs` -- there's never a pending terminator to splice around
/// when `v` is actually `void_val`.
#[partial]
def materialize_void (c : CodegenCtx) (v : LLVMValue) : MaterializedVal := match v {
    LLVMValue.void_val =>
        match fresh_temp c {
            CtxStrPair.mk ctx1 temp =>
                let unit_val := LLVMValue.alloc_constructor 0 empty_vals in
                let assign := LLVMInstruction.assign temp unit_val in
                { ctx := ctx1, instrs := (cons_instr assign empty_instrs), val := (LLVMValue.var_ temp) },
        },
    _ => { ctx := c, instrs := empty_instrs, val := v },
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
                                let con_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (cons_val (LLVMValue.var_ tag_temp) (cons_val (LLVMValue.int_ 0) empty_vals)) false in
                                let con_instr := LLVMInstruction.assign con_temp con_val in
                                { ctx := ctx3, instrs := (cons_instr zext_instr (cons_instr tag_instr (cons_instr con_instr empty_instrs))), val := (LLVMValue.var_ con_temp) },
                        },
                },
        }
    else { ctx := c, instrs := empty_instrs, val := v }

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
                        { ctx := c2, instrs := append_instrs raw_instrs (append_instrs void_instrs bool_instrs), val := val },
                },
        }

#[partial]
def compile_ntv_ir (c : CodegenCtx) (native : Native) : CompileResult :=
    match native {
        Native.mk name num_args args =>
            let name_str := show_identifier name in
            let llvm_name := extract_base_name name_str in
            let fn_name := String.concat "monad_" llvm_name in
            match compile_ntv_args c args empty_instrs empty_vals {
                { ctx := ctx_args, instrs := all_instrs, vals := all_vals, blocks := all_blocks, funcs := all_funcs, globals := all_globals, last_val := args_last_val } =>
                    match fresh_temp ctx_args {
                        CtxStrPair.mk ctx_t temp =>
                            let call_val := LLVMValue.call fn_name LLVMType.i64_ all_vals false in
                            let assign_instr := LLVMInstruction.assign temp call_val in
                            // Args' own instrs must run BEFORE the call
                            // that consumes their values, not after --
                            // `cons_instr assign_instr all_instrs`
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
                            match compose_seq ({ instrs := all_instrs, blocks := all_blocks, val := args_last_val }) ({ instrs := (cons_instr assign_instr empty_instrs), blocks := empty_blocks, val := (LLVMValue.var_ temp) }) {
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
            match compile_ntv_args c args empty_instrs empty_vals {
                { ctx := ctx_args, instrs := all_instrs, vals := all_vals, blocks := all_blocks, funcs := all_funcs, globals := all_globals, last_val := args_last_val } =>
                    match fresh_temp ctx_args {
                        CtxStrPair.mk ctx_t temp =>
                            // Call the @alloc_constructor runtime function
                            // alloc_constructor takes (tag, field_count) and allocates space for fields
                            // The tag is determined by the constructor name
                            let tag_val := constructor_tag c (show_identifier name) in
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
                                    match compose_seq ({ instrs := all_instrs, blocks := all_blocks, val := args_last_val }) ({ instrs := (cons_instr assign_instr set_instrs), blocks := empty_blocks, val := (LLVMValue.var_ temp) }) {
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
        List.empty => { ctx := c, instrs := empty_instrs },
        List.cons v rest =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 temp =>
                    let set_call := LLVMValue.call "monad_set_field" LLVMType.i64_ (cons_val obj_val (cons_val (LLVMValue.int_ idx) (cons_val v empty_vals))) false in
                    let set_instr := LLVMInstruction.assign temp set_call in
                    match build_set_field_instrs obj_val rest (idx + 1) ctx1 {
                        { ctx := ctx2, instrs := rest_instrs } =>
                            { ctx := ctx2, instrs := (cons_instr set_instr rest_instrs) },
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
    else LLVMBasicBlock.mk label (append_instrs instrs (cons_instr (LLVMInstruction.jump merge_label) empty_instrs))

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
    LLVMInstruction.comment a => false,
}

// ─── Safe sequential composition (fixes a real "dropped continuation"
// codegen bug) ──────────────────────────────────────────────────────
//
// Every "combine a sub-expression's compiled result into a bigger
// context" call site in this file used to just concatenate the two
// instruction lists directly (`append_instrs a_instrs b_instrs`),
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
                        { instrs := append_instrs a_instrs b_instrs, blocks := append_blocks a_blocks b_blocks, val := b_val }
                }
            else
                { instrs := append_instrs a_instrs b_instrs, blocks := append_blocks a_blocks b_blocks, val := b_val }
    },
}

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
                    let merged := append_instrs without_ret extra_instrs in
                    let new_instrs :=
                        if ends_with_terminator extra_instrs
                        then merged
                        else append_instrs merged (cons_instr (LLVMInstruction.ret extra_val) empty_instrs) in
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
    LLVMInstruction.comment a => false,
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

#[partial]
def drop_last_instr (instrs : List LLVMInstruction) : List LLVMInstruction := match instrs {
    List.empty => List.empty,
    List.cons i rest => match rest {
        List.empty => List.empty,
        List.cons _ _ => List.cons i (drop_last_instr rest),
    },
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
#[partial]
def free_names_of_term (bound : List Identifier) (t : Term) : List Identifier := match t {
    Term.var _idx dbg => free_names_of_dbg bound dbg,
    Term.var_macro _idx dbg => free_names_of_dbg bound dbg,
    Term.lam dbg typ_ body_ =>
        List.append (free_names_of_term bound typ_)
            (free_names_of_term (add_bound_name bound dbg) body_),
    Term.forall dbg kind body_ =>
        List.append (free_names_of_term bound kind)
            (free_names_of_term (add_bound_name bound dbg) body_),
    Term.pi arg ret => List.append (free_names_of_term bound arg) (free_names_of_term bound ret),
    Term.app fun_ arg_ => List.append (free_names_of_term bound fun_) (free_names_of_term bound arg_),
    Term.lit lit_ => free_names_of_lit bound lit_,
    Term.ntv native => free_names_of_native bound native,
    Term.con c => free_names_of_con bound c,
    Term.type_ _universe => List.empty,
    Term.hole => List.empty,
    Term.quote_ inner => free_names_of_term bound inner,
}

#[partial]
def add_bound_name (bound : List Identifier) (dbg : DebugName) : List Identifier := match dbg {
    DebugName.named id_ => List.cons id_ bound,
    DebugName.unnamed => bound,
}

#[partial]
def free_names_of_dbg (bound : List Identifier) (dbg : DebugName) : List Identifier := match dbg {
    DebugName.named id_ => if ident_in_list bound id_ then List.empty else List.cons id_ List.empty,
    DebugName.unnamed => List.empty,
}

#[partial]
def free_names_of_lit (bound : List Identifier) (lit_ : Literal) : List Identifier := match lit_ {
    Literal.num _n _s => List.empty,
    Literal.flt _t _s => List.empty,
    Literal.str _s => List.empty,
    Literal.if_ cond then_ else_ =>
        List.append (free_names_of_term bound cond)
            (List.append (free_names_of_term bound then_) (free_names_of_term bound else_)),
    Literal.match_ scrutinee cases =>
        List.append (free_names_of_term bound scrutinee) (free_names_of_cases bound cases),
    Literal.struct_lit fields type_name =>
        List.append (free_names_of_struct_fields bound fields) (free_names_of_opt_term bound type_name),
    Literal.struct_update base fields =>
        List.append (free_names_of_term bound base) (free_names_of_struct_fields bound fields),
}

#[partial]
def free_names_of_opt_term (bound : List Identifier) (ot : Option Term) : List Identifier := match ot {
    Option.some t => free_names_of_term bound t,
    Option.none => List.empty,
}

#[partial]
def free_names_of_struct_fields (bound : List Identifier) (fields : List StructLitField) : List Identifier := match fields {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            StructLitField.mk _name value =>
                List.append (free_names_of_term bound value) (free_names_of_struct_fields bound rest),
        },
}

/// Each case's own `args` (and, defensively, its `field_pattern`
/// binders -- even though `field_pattern` isn't wired into codegen's
/// own match-arm binding yet, a separate pre-existing gap) shadow
/// `bound` inside that case's `body` ONLY, not its siblings.
#[partial]
def free_names_of_cases (bound : List Identifier) (cases : List MatchCase) : List Identifier := match cases {
    List.empty => List.empty,
    List.cons case_ rest =>
        match case_ {
            MatchCase.mc _name args body_ field_pattern =>
                let bound2 := add_field_pattern_bound (List.append args bound) field_pattern in
                List.append (free_names_of_term bound2 body_) (free_names_of_cases bound rest),
        },
}

#[partial]
def add_field_pattern_bound (bound : List Identifier) (fp : Option FieldPattern) : List Identifier := match fp {
    Option.some pat => match pat { FieldPattern.mk entries _rest => add_field_pattern_entries bound entries },
    Option.none => bound,
}

#[partial]
def add_field_pattern_entries (bound : List Identifier) (entries : List FieldPatternEntry) : List Identifier := match entries {
    List.empty => bound,
    List.cons e rest =>
        match e { FieldPatternEntry.mk _field binder => add_field_pattern_entries (List.cons binder bound) rest },
}

#[partial]
def free_names_of_native (bound : List Identifier) (n : Native) : List Identifier := match n {
    Native.mk _name _num_args args => free_names_of_opt_list bound args,
}

/// `c`'s own `name` is the constructor TAG, not a variable reference --
/// deliberately excluded (unlike `collect_referenced_names_con`, whose
/// reachability purpose needs it; free-var capture doesn't).
#[partial]
def free_names_of_con (bound : List Identifier) (c : Con) : List Identifier := match c {
    Con.mk _name _typ_name _num_args args => free_names_of_opt_list bound args,
}

#[partial]
def free_names_of_opt_list (bound : List Identifier) (args : List (Option Term)) : List Identifier := match args {
    List.empty => List.empty,
    List.cons opt_ rest =>
        match opt_ {
            Option.some t => List.append (free_names_of_term bound t) (free_names_of_opt_list bound rest),
            Option.none => free_names_of_opt_list bound rest,
        },
}

#[partial]
def ident_in_list (xs : List Identifier) (x : Identifier) : Bool := match xs {
    List.empty => false,
    List.cons y rest => if identifier_eq y x then true else ident_in_list rest x,
}

#[partial]
def dedup_idents (names : List Identifier) : List Identifier := dedup_idents_go names List.empty

#[partial]
def dedup_idents_go (names : List Identifier) (seen : List Identifier) : List Identifier := match names {
    List.empty => List.empty,
    List.cons n rest =>
        if ident_in_list seen n
        then dedup_idents_go rest seen
        else List.cons n (dedup_idents_go rest (List.cons n seen)),
}

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
    // this case's body (`{ ctx := c, instrs := empty_instrs }`) is a
    // struct literal whose last field value is a bare identifier
    // (`empty_instrs`), and the expression parser's application-chain
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
    List.empty => { ctx := c, instrs := empty_instrs },
    List.cons cap rest =>
        match cap {
            LocalBinding.mk cname _cval =>
                match fresh_temp c {
                    CtxStrPair.mk ctx1 temp =>
                        let get_call := LLVMValue.call "monad_closure_get_env" LLVMType.i64_
                            (cons_val (LLVMValue.parm_ 0) (cons_val (LLVMValue.int_ idx) empty_vals)) false in
                        let get_instr := LLVMInstruction.assign temp get_call in
                        let ctx2 := ctx_bind_local ctx1 cname (LLVMValue.var_ temp) in
                        match build_get_env_instrs ctx2 rest (idx + 1) {
                            { ctx := ctx3, instrs := rest_instrs } => { ctx := ctx3, instrs := cons_instr get_instr rest_instrs },
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
    List.empty => { ctx := c, instrs := empty_instrs },
    List.cons v rest =>
        match fresh_temp c {
            CtxStrPair.mk ctx1 temp =>
                let set_call := LLVMValue.call "monad_closure_set_env" LLVMType.i64_
                    (cons_val obj_val (cons_val (LLVMValue.int_ idx) (cons_val v empty_vals))) false in
                let set_instr := LLVMInstruction.assign temp set_call in
                match build_set_env_instrs obj_val rest (idx + 1) ctx1 {
                    { ctx := ctx2, instrs := rest_instrs } => { ctx := ctx2, instrs := cons_instr set_instr rest_instrs },
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
                            let body_instrs := append_instrs get_env_instrs instrs_r in
                            let entry_instrs := append_instrs body_instrs (cons_instr (LLVMInstruction.ret val_r) empty_instrs) in
                            let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                            let self_pair := ParamPair.mk "p0" LLVMType.i64_ in
                            let lam_pair := ParamPair.mk "p1" LLVMType.i64_ in
                            let lam_params := cons_pair self_pair (cons_pair lam_pair empty_pairs) in
                            let lam_func := LLVMFunction.mk lam_name lam_params LLVMType.i64_ (cons_block entry_block blocks_r) false in
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
                                            let all_instrs := cons_instr box_instr set_env_instrs in
                                            CompileResult.ok ctx_set all_instrs (LLVMValue.var_ temp) empty_blocks (cons_func lam_func funcs_r) globals_r,
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
                            match compose_seq ({ instrs := instrs_bool, blocks := blocks_bool, val := bool_val }) ({ instrs := (cons_instr branch_instr empty_instrs), blocks := empty_blocks, val := bool_val }) {
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
                let tag_call := LLVMValue.call "monad_get_tag" LLVMType.i64_ (cons_val cond_val empty_vals) false in
                let tag_instr := LLVMInstruction.assign tag_temp tag_call in
                match fresh_temp ctx1 {
                    CtxStrPair.mk ctx2 bool_temp =>
                        let bool_true_tag := constructor_tag c "true" in
                        let cmp_instr := LLVMInstruction.assign bool_temp (LLVMValue.icmp_eq (LLVMValue.var_ tag_temp) (LLVMValue.int_ bool_true_tag)) in
                        let extra := cons_instr tag_instr (cons_instr cmp_instr empty_instrs) in
                        match compose_seq ({ instrs := instrs, blocks := blocks, val := cond_val }) ({ instrs := extra, blocks := empty_blocks, val := (LLVMValue.var_ bool_temp) }) {
                            { instrs := new_instrs, blocks := new_blocks, val := new_val } =>
                                { ctx := ctx2, instrs := new_instrs, blocks := new_blocks, val := new_val }
                        },
                },
        }

/// Dispatches through `lookup_native_any` (above), NOT a private,
/// narrower name-matching copy -- `is_native_bool_op_name`'s own prior
/// body compared `extract_base_name (show_identifier id)` (bare-only,
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
#[partial]
def term_is_native_bool_op (t : Term) : Bool := match t {
    Term.app fun_ _arg =>
        match fun_ {
            Term.app fun2 _arg2 =>
                match fun2 {
                    Term.var _idx dbg =>
                        match dbg {
                            DebugName.named id => is_native_bool_op_name (show_identifier id),
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
                    build_merge_result else_bmr.ctx merge_label then_reaches then_bmr.val then_label else_reaches else_bmr.val else_label entry_instrs entry_blocks entry_funcs entry_globals blocks_then blocks_else funcs_then funcs_else globals_then globals_else then_block else_block,
            },
    }

/// Builds `merge_label`'s own `PhiPair` list from whichever of
/// `then`/`else` actually reach it -- see `build_db_if_blocks`'s own
/// doc comment for why a branch might not.
#[partial]
def build_merge_phi_pairs (then_reaches : Bool) (then_val : LLVMValue) (then_label : String) (else_reaches : Bool) (else_val : LLVMValue) (else_label : String) : List PhiPair :=
    let then_pairs := if then_reaches then cons_phi (PhiPair.mk then_val then_label) empty_phis else empty_phis in
    if else_reaches then cons_phi (PhiPair.mk else_val else_label) then_pairs else then_pairs

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
                List.empty => cons_instr (LLVMInstruction.ret (LLVMValue.int_ 0)) empty_instrs,
                List.cons _ _ =>
                    let phi_instr := LLVMInstruction.assign phi_temp (LLVMValue.phi pairs) in
                    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ phi_temp) in
                    cons_instr phi_instr (cons_instr ret_instr empty_instrs),
            } in
            let merge_block := LLVMBasicBlock.mk merge_label merge_instrs in
            let all_blocks := cons_block then_block (cons_block else_block (cons_block merge_block (append_blocks (append_blocks entry_blocks then_info.blocks) else_info.blocks))) in
            let all_funcs := append_funcs (append_funcs entry_funcs funcs_then) funcs_else in
            let all_globals := append_globals (append_globals entry_globals globals_then) globals_else in
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
                    Option.some val => CompileResult.ok c empty_instrs val empty_blocks empty_funcs empty_globals_list,
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
                        let name := show_identifier id in
                        let llvm_name := replace_dots_with_underscores name in
                        let also_a_real_fn := match ctx_lookup_arity c llvm_name {
                            Option.some _ => true,
                            Option.none => false,
                        } in
                        if is_constructor_var c name && Bool.not also_a_real_fn then
                            // Compile as alloc_constructor with 0 fields.
                            // Must use THIS constructor's own tag (e.g.
                            // `none` = 3), not a hardcoded 0 (`Unit.unit`'s
                            // tag) -- a hardcoded tag made every bare
                            // 0-arg constructor reference indistinguishable
                            // from Unit.unit during match dispatch.
                            match fresh_temp c {
                                CtxStrPair.mk ctx_t temp =>
                                    let tag_val := constructor_tag c name in
                                    let alloc_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (List.cons (LLVMValue.int_ tag_val) (List.cons (LLVMValue.int_ 0) List.empty)) false in
                                    let assign_instr := LLVMInstruction.assign temp alloc_val in
                                    CompileResult.ok ctx_t (cons_instr assign_instr empty_instrs) (LLVMValue.var_ temp) empty_blocks empty_funcs empty_globals_list,
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
                                                let call_val := LLVMValue.call llvm_name LLVMType.i64_ empty_vals false in
                                                let assign_instr := LLVMInstruction.assign temp call_val in
                                                CompileResult.ok ctx_t (cons_instr assign_instr empty_instrs) (LLVMValue.var_ temp) empty_blocks empty_funcs empty_globals_list,
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
                                                CompileResult.ok ctx_t (cons_instr assign_instr empty_instrs) (LLVMValue.var_ temp) empty_blocks (cons_func shim_func empty_funcs) empty_globals_list,
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
                                            let call_val := LLVMValue.call llvm_name LLVMType.i64_ empty_vals false in
                                            let assign_instr := LLVMInstruction.assign temp call_val in
                                            CompileResult.ok ctx_t (cons_instr assign_instr empty_instrs) (LLVMValue.var_ temp) empty_blocks empty_funcs empty_globals_list,
                                    },
                            },
                },
            DebugName.unnamed =>
                CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
        },
    Term.lam dbg typ body => compile_db_lam_ir c dbg typ body,
    Term.app fun arg => compile_db_app_ir c fun arg,
    Term.ntv native => compile_ntv_ir c native,
    Term.con constr => compile_con_ir c constr,
    Term.forall dbg kind body => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
    Term.pi arg ret => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
    Term.type_ universe => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
    Term.hole => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
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
                            let instrs1m := append_instrs instrs1 bool_instrs in
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
                                                    Option.some (CompileResult.ok ctx2m combined last_val all_blocks (append_funcs funcs1 funcs2) (append_globals globals1 globals2)),
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
                            let name := show_identifier id in
                            let llvm_name := replace_dots_with_underscores name in
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
                            let name := show_identifier id in
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
                    let name := show_identifier id in
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
                                    let con_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (cons_val (LLVMValue.var_ tag_temp) (cons_val (LLVMValue.int_ 0) empty_vals)) false in
                                    let con_instr := LLVMInstruction.assign con_temp con_val in
                                    { ctx := ctx3, instrs := (cons_instr cmp_instr (cons_instr zext_instr (cons_instr tag_instr (cons_instr con_instr empty_instrs)))), val := (LLVMValue.var_ con_temp) },
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
                    let call_val := LLVMValue.call fn_name LLVMType.i64_ (cons_val val1 empty_vals) false in
                    let assign_instr := LLVMInstruction.assign temp call_val in
                    // `println (if p then "a" else "b")`-shaped code:
                    // `arg` itself branching means `instrs1` already
                    // ends in a terminator -- splice via `compose_seq`
                    // instead of blindly appending (see its own doc
                    // comment above `ends_with_terminator`).
                    match compose_seq ({ instrs := instrs1, blocks := blocks1, val := val1 }) ({ instrs := (cons_instr assign_instr empty_instrs), blocks := empty_blocks, val := (LLVMValue.var_ temp) }) {
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
                                    wrap_io_value_native_result ctx_t (LLVMValue.var_ temp) empty_instrs new_instrs new_blocks funcs1 globals1 (LLVMValue.var_ temp)
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
/// splice into. Naively `append_instrs`-ing the wrap code onto
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
            let unit_call := LLVMValue.call "monad_ctor_Unit_unit" LLVMType.i64_ empty_vals false in
            let unit_instr := LLVMInstruction.assign temp_unit unit_call in
            let unit_val := LLVMValue.var_ temp_unit in
            wrap_io_value_native_result_go ctx_unit unit_val (cons_instr unit_instr empty_instrs) prior_val prior_instrs prior_blocks funcs globals,
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
/// `append_instrs`, per `wrap_void_native_result`'s own doc comment.
#[partial]
def wrap_io_value_native_result_go (ctx : CodegenCtx) (inner_val : LLVMValue) (pre_instrs : List LLVMInstruction) (prior_val : LLVMValue) (prior_instrs : List LLVMInstruction) (prior_blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) : CompileResult :=
    match fresh_temp ctx {
        CtxStrPair.mk ctx_io temp_io =>
            let alloc_val := LLVMValue.alloc_constructor (constructor_tag ctx "IO.io") (List.cons inner_val List.empty) in
            let alloc_instr := LLVMInstruction.assign temp_io alloc_val in
            match build_set_field_instrs (LLVMValue.var_ temp_io) (List.cons inner_val List.empty) 0 ctx_io {
                { ctx := ctx_set, instrs := set_instrs } =>
                    let wrap_instrs := append_instrs pre_instrs (cons_instr alloc_instr set_instrs) in
                    match compose_seq ({ instrs := prior_instrs, blocks := prior_blocks, val := prior_val }) ({ instrs := wrap_instrs, blocks := empty_blocks, val := (LLVMValue.var_ temp_io) }) {
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
/// combined with `arg`'s via blind `append_instrs instrs2 instrs1`,
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
                    match compose_seq ({ instrs := instrs2, blocks := blocks2, val := val2 }) ({ instrs := instrs1, blocks := blocks1, val := val1 }) {
                        { instrs := combined, blocks := all_blocks, val := last_val } =>
                            let all_funcs := append_funcs funcs2 funcs1 in
                            let all_globals := append_globals globals2 globals1 in
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
    match t {
        Term.app fun_ arg_ => flatten_app_spine_go fun_ (List.cons arg_ acc),
        _ => { head := t, args := acc },
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
    compile_spine_args_go c terms empty_instrs empty_blocks empty_funcs empty_globals_list empty_vals LLVMValue.void_val

/// Compile every argument term in a flattened spine, in order,
/// threading the ctx/instrs/blocks/funcs/globals accumulation through
/// each one -- same pattern `compile_ntv_args_go` uses for native calls,
/// just over a plain `List Term` (no `Option` wrapping needed).
///
/// Accumulator-style, sequencing each arg via `compose_seq` (see its
/// own doc comment above `ends_with_terminator`) instead of blindly
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
        List.empty => { ctx := c, instrs := acc_instrs, blocks := acc_blocks, funcs := acc_funcs, globals := acc_globals, vals := (rev_vals acc_vals empty_vals), last_val := acc_val },
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
                                    let instrs1m := append_instrs instrs1 (append_instrs void_instrs bool_instrs) in
                                    match compose_seq ({ instrs := acc_instrs, blocks := acc_blocks, val := acc_val }) ({ instrs := instrs1m, blocks := blocks1, val := val1 }) {
                                        { instrs := new_instrs, blocks := new_blocks, val := new_val } =>
                                            compile_spine_args_go ctx1b rest
                                                new_instrs new_blocks
                                                (append_funcs acc_funcs funcs1)
                                                (append_globals acc_globals globals1)
                                                (cons_val val1 acc_vals)
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
                            let name := show_identifier id in
                            let llvm_name := replace_dots_with_underscores name in
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
                                CompileResult.ok c empty_instrs (LLVMValue.fn_ref llvm_name) empty_blocks empty_funcs empty_globals_list,
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
                            match compose_seq ({ instrs := instrs_h, blocks := blocks_h, val := val_h }) ({ instrs := instrs_a, blocks := blocks_a, val := last_val_a }) {
                                { instrs := combined, blocks := all_blocks, val := combined_val } =>
                                    let all_funcs := append_funcs funcs_h funcs_a in
                                    let all_globals := append_globals globals_h globals_a in
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
            match compose_seq ({ instrs := combined, blocks := blocks, val := last_val }) ({ instrs := (cons_instr call_instr empty_instrs), blocks := empty_blocks, val := (LLVMValue.var_ temp) }) {
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
            if I64.gt (List.length arg_vals) real_arity then
                let direct_args := take_vals real_arity arg_vals in
                let extra_args := drop_vals real_arity arg_vals in
                match combine_direct_call ctx_a name direct_args combined blocks funcs globals last_val {
                    CompileResult.ok ctx_d instrs_d val_d blocks_d funcs_d globals_d =>
                        apply_extra_args_one_by_one ctx_d val_d extra_args instrs_d blocks_d funcs_d globals_d,
                }
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
                (LLVMValue.call trampoline_name LLVMType.i64_ (cons_val callee_val arg_vals) false) in
            match compose_seq ({ instrs := combined, blocks := blocks, val := last_val }) ({ instrs := (cons_instr call_instr empty_instrs), blocks := empty_blocks, val := (LLVMValue.var_ temp) }) {
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
            match compose_seq ({ instrs := instrs, blocks := blocks, val := last_val }) ({ instrs := (cons_instr arith_instr empty_instrs), blocks := empty_blocks, val := (LLVMValue.var_ temp) }) {
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
                    let len_call := LLVMValue.call "monad_string_length" LLVMType.i64_ (cons_val arg2_val empty_vals) false in
                    let len_instr := LLVMInstruction.assign temp_len len_call in
                    match fresh_temp ctx_len {
                        CtxStrPair.mk new_ctx temp =>
                            let write_call := LLVMValue.call "monad_write_file" LLVMType.i64_ (cons_val arg1_val (cons_val arg2_val (cons_val (LLVMValue.var_ temp_len) empty_vals))) false in
                            let write_instr := LLVMInstruction.assign temp write_call in
                            match compose_seq ({ instrs := instrs, blocks := blocks, val := last_val }) ({ instrs := (cons_instr len_instr (cons_instr write_instr empty_instrs)), blocks := empty_blocks, val := (LLVMValue.var_ temp) }) {
                                { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                                    wrap_void_native_result new_ctx (LLVMValue.var_ temp) new_instrs new_blocks funcs globals,
                            },
                    },
            },
        _ =>
            match fresh_temp c {
                CtxStrPair.mk new_ctx temp =>
                    let fn_name := native_op_to_fn_name op in
                    let call_val := LLVMValue.call fn_name LLVMType.i64_ (cons_val arg1_val (cons_val arg2_val empty_vals)) false in
                    let call_instr := LLVMInstruction.assign temp call_val in
                    match compose_seq ({ instrs := instrs, blocks := blocks, val := last_val }) ({ instrs := (cons_instr call_instr empty_instrs), blocks := empty_blocks, val := (LLVMValue.var_ temp) }) {
                        { instrs := new_instrs, blocks := new_blocks, val := _ } =>
                            if is_void_native op then
                                wrap_void_native_result new_ctx (LLVMValue.var_ temp) new_instrs new_blocks funcs globals
                            else if needs_io_wrap op then
                                wrap_io_value_native_result new_ctx (LLVMValue.var_ temp) empty_instrs new_instrs new_blocks funcs globals (LLVMValue.var_ temp)
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
    LLVMValue.icmp_eq lhs rhs => Option.none,
    LLVMValue.icmp_ne lhs rhs => Option.none,
    LLVMValue.icmp_slt lhs rhs => Option.none,
    LLVMValue.icmp_sgt lhs rhs => Option.none,
    LLVMValue.zext val from_ty to_ty => Option.none,
    LLVMValue.trunc val from_ty to_ty => Option.none,
    LLVMValue.ptrtoint val from_ty to_ty => Option.none,
    LLVMValue.phi pairs => Option.none,
    LLVMValue.gep base indices => Option.none,
    LLVMValue.load ptr => Option.none,
    LLVMValue.bitcast val ty => Option.none,
    LLVMValue.alloc_closure entry arity env_size => Option.none,
    LLVMValue.alloc_constructor tag field_count => Option.none,
    LLVMValue.native_op op args => Option.none,
}

#[partial]
def append_instrs (a : List LLVMInstruction) (b : List LLVMInstruction) : List LLVMInstruction := match a {
    List.empty => b,
    List.cons hd tl => cons_instr hd (append_instrs tl b),
}

#[partial]
def append_blocks (a : List LLVMBasicBlock) (b : List LLVMBasicBlock) : List LLVMBasicBlock := match a {
    List.empty => b,
    List.cons hd tl => cons_block hd (append_blocks tl b),
}

#[partial]
def append_funcs (a : List LLVMFunction) (b : List LLVMFunction) : List LLVMFunction := match a {
    List.empty => b,
    List.cons hd tl => cons_func hd (append_funcs tl b),
}

def append_globals (a : List LLVMGlobal) (b : List LLVMGlobal) : List LLVMGlobal := match a {
    List.empty => b,
    List.cons hd tl => cons_global hd (append_globals tl b),
}

def cons_global (g : LLVMGlobal) (gs : List LLVMGlobal) : List LLVMGlobal :=
    List.cons g gs

#[partial]
def param_name_db (p : Param) : Identifier := match p {
    Param.mk name typ_ mult default _attrs => name,
}

#[partial]
def empty_blocks : List LLVMBasicBlock := List.empty

#[partial]
def cons_block (b : LLVMBasicBlock) (bs : List LLVMBasicBlock) : List LLVMBasicBlock :=
    List.cons b bs

#[partial]
def module_path_to_str (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => join_identifiers ids,
}

#[partial]
def join_identifiers (ids : List Identifier) : String := match ids {
    List.empty => "",
    List.cons hd rest => join_ids_rest hd rest,
}

#[partial]
def join_ids_rest (hd : Identifier) (rest : List Identifier) : String :=
    match rest {
        List.empty => show_identifier hd,
        List.cons x y => String.concat (show_identifier hd) (String.concat "__" (join_identifiers rest)),
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
        DebugName.named id_ => String.beq (show_identifier id_) "IO",
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

/// Which shape a native runtime function's raw `i64` result needs
/// wrapped into before it's a legitimate Monad-level value.
/// `passthrough` covers a native whose result IS ALREADY this
/// backend's uniform value representation for its type (a `String` is
/// always a bare `char*`/i64, per `monad_i64_to_string`'s own doc
/// comment -- `monad_string_concat` needs nothing further).
/// `bool_result` covers a native that's semantically `Bool`-returning
/// but implemented as a plain C `int64_t` 0/1 (`monad_string_eq`,
/// matching `NativeOp.op_eq`'s own raw-i1 comparison convention) -- a
/// raw 0/1 is NOT a valid `Bool` value on its own here: this backend's
/// `Bool` is always a tagged `Constructor` (`monad_ctor_Bool_true`/
/// `_false`, tags 1/2 -- see `constructor_tag`), and anything that
/// receives this result as an ordinary `Bool` VALUE rather than an
/// immediate `if`-condition (`ensure_i1_cond`'s own special-cased
/// native-comparison recognition only applies to a `Term` it can see
/// is a direct native-op call, not a value already reduced to a bare
/// local/parameter) will call `monad_get_tag` on it, segfaulting on a
/// small integer address -- confirmed as a real gap via direct repro
/// (`String.beq` passed into an ordinary `Bool`-parameter function).
type NativeWrapKind {
    passthrough (rt_fn_name : String),
    bool_result (rt_fn_name : String),
    // `IO String`-returning natives (`monad_read_file`): call, then wrap
    // the raw result directly as `IO.io raw` -- mirrors
    // `wrap_io_value_native_result_go`'s own treatment of read_file at
    // its (other, term-level fast-path) call site: this backend already
    // treats a native-sourced C string as a valid `String` value with no
    // extra boxing.
    io_passthrough (rt_fn_name : String),
    // `IO Bool`-returning natives using the "truthy pointer" C
    // convention (`monad_file_exists`/`monad_is_dir` -- non-null
    // pointer for true, `NULL` for false, NOT already 0/1 like
    // `bool_result`'s `monad_string_eq` assumes): `icmp_ne` against 0
    // first (`materialize_truthy_ptr_as_bool`), then IO-wrap the result.
    io_truthy_ptr_bool_result (rt_fn_name : String),
    // `IO Unit`-returning `monad_write_file`: needs a 3rd `len` arg
    // (`monad_string_length` on the content param) the mo-level call
    // site never supplies -- mirrors `emit_native_call2_instr`'s own
    // `op_write_file` special case.
    io_write_file (rt_fn_name : String),
}

/// A `#[native <name>]`-attributed def has no real body (`Term.hole`,
/// per `is_term_hole`) -- absent a special case, `compile_db_def_ir`
/// falls all the way through to its own `LLVMValue.void_val` arm below,
/// silently compiling EVERY native def to the exact same "return Unit"
/// stub regardless of what it's actually supposed to do (confirmed as a
/// real gap: `String.concat`'s own compiled body was this stub,
/// producing a do-block that printed nothing meaningful). Whitelisted
/// to the natives this backend actually has a real C implementation
/// for (`lang/codegen/runtime.c`) -- anything else still falls through
/// to the unchanged stub behavior below, so this can never newly break
/// a native this backend doesn't implement yet.
#[partial]
def native_runtime_fn_name (attrs : List Attribute) : Option NativeWrapKind :=
    match native_attr_target_name attrs {
        Option.none => Option.none,
        Option.some target =>
            if String.beq target "string_concat" then Option.some (NativeWrapKind.passthrough "monad_string_concat")
            else if String.beq target "string_eq" then Option.some (NativeWrapKind.bool_result "monad_string_eq")
            // `String.length` (std/string.mo) had no entry here either --
            // same "confirmed as a real gap" shape as `string_concat`'s
            // own doc comment above: a `#[native string_length]` def with
            // no real body silently compiled to the generic "return Unit"
            // stub, discarding its argument entirely. Found via a direct
            // repro (`println (I64.to_string (String.length "abc"))`
            // printed a garbage heap address instead of `3`).
            else if String.beq target "string_length" then Option.some (NativeWrapKind.passthrough "monad_string_length")
            // `String.hash`'s `#[native string_hash]` -- pure `U64`
            // result, same shape as `string_length`. `IO.write_file`/
            // `read_file`/`file_exists`/`is_dir` (`std/io.mo`, `#[native
            // "X_native"]` on the WRAPPED, `_native`-suffixed defs) were
            // the same "confirmed as a real gap" stub for any reference
            // to them that doesn't go through the term-level fast path
            // (`try_compile_inline_native_db`/`lookup_native_any`) --
            // which is every reference now that each has a real-bodied
            // `IO.X` wrapper calling `IO.X_native` as an ORDINARY call
            // (`Term.app (Term.var ...)` referencing the global by name,
            // never inlined). Confirmed live: `IO.is_dir (Path.path
            // "/tmp")`, compiled and run, always "false" -- its own
            // compiled `IO_is_dir_native` global was the bogus Unit
            // stub, called for real from `IO_is_dir`'s own compiled body.
            else if String.beq target "string_hash" then Option.some (NativeWrapKind.passthrough "monad_string_hash")
            else if String.beq target "read_file" then Option.some (NativeWrapKind.io_passthrough "monad_read_file")
            else if String.beq target "file_exists" then Option.some (NativeWrapKind.io_truthy_ptr_bool_result "monad_file_exists")
            else if String.beq target "is_dir" then Option.some (NativeWrapKind.io_truthy_ptr_bool_result "monad_is_dir")
            else if String.beq target "write_file" then Option.some (NativeWrapKind.io_write_file "monad_write_file")
            else Option.none,
    }

#[partial]
def native_attr_target_name (attrs : List Attribute) : Option String :=
    match attrs {
        List.empty => Option.none,
        List.cons a rest =>
            match a {
                Attribute.mk aname args =>
                    if id_eq aname (Identifier.id "native")
                    then attr_arg_as_string_first args
                    else native_attr_target_name rest,
            },
    }

#[partial]
def attr_arg_as_string_first (args : List AttrArg) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a _ =>
            match a {
                AttrArg.ident aid => Option.some (show_identifier aid),
                AttrArg.str s => Option.some s,
                _ => Option.none,
            },
    }

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
                    let entry_instrs := cons_instr assign_instr (cons_instr (LLVMInstruction.ret (LLVMValue.var_ temp)) empty_instrs) in
                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                    let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (cons_block entry_block empty_blocks) true in
                    { ctx := ctx_t, funcs := (cons_func native_func empty_funcs), globals := empty_globals_list }
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
                                    let con_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (cons_val (LLVMValue.var_ tag_temp) (cons_val (LLVMValue.int_ 0) empty_vals)) false in
                                    let con_instr := LLVMInstruction.assign con_temp con_val in
                                    let entry_instrs := cons_instr raw_instr (cons_instr tag_instr (cons_instr con_instr (cons_instr (LLVMInstruction.ret (LLVMValue.var_ con_temp)) empty_instrs))) in
                                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                    let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (cons_block entry_block empty_blocks) true in
                                    { ctx := ctx3, funcs := (cons_func native_func empty_funcs), globals := empty_globals_list }
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
                                    let entry_instrs := cons_instr raw_instr (cons_instr alloc_instr (append_instrs set_instrs (cons_instr (LLVMInstruction.ret (LLVMValue.var_ io_temp)) empty_instrs))) in
                                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                    let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (cons_block entry_block empty_blocks) true in
                                    { ctx := ctx_set, funcs := (cons_func native_func empty_funcs), globals := empty_globals_list }
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
                                            let entry_instrs := cons_instr raw_instr (append_instrs bool_instrs (cons_instr alloc_instr (append_instrs set_instrs (cons_instr (LLVMInstruction.ret (LLVMValue.var_ io_temp)) empty_instrs)))) in
                                            let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                            let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (cons_block entry_block empty_blocks) true in
                                            { ctx := ctx_set, funcs := (cons_func native_func empty_funcs), globals := empty_globals_list }
                                    },
                            },
                    },
            },
        NativeWrapKind.io_write_file rt_fn_name =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 len_temp =>
                    let len_call := LLVMValue.call "monad_string_length" LLVMType.i64_ (cons_val (LLVMValue.parm_ 1) empty_vals) false in
                    let len_instr := LLVMInstruction.assign len_temp len_call in
                    match fresh_temp ctx1 {
                        CtxStrPair.mk ctx2 write_temp =>
                            let write_call := LLVMValue.call rt_fn_name LLVMType.i64_ (cons_val (LLVMValue.parm_ 0) (cons_val (LLVMValue.parm_ 1) (cons_val (LLVMValue.var_ len_temp) empty_vals))) false in
                            let write_instr := LLVMInstruction.assign write_temp write_call in
                            match fresh_temp ctx2 {
                                CtxStrPair.mk ctx3 unit_temp =>
                                    let unit_call := LLVMValue.call "monad_ctor_Unit_unit" LLVMType.i64_ empty_vals false in
                                    let unit_instr := LLVMInstruction.assign unit_temp unit_call in
                                    match fresh_temp ctx3 {
                                        CtxStrPair.mk ctx4 io_temp =>
                                            let alloc_val := LLVMValue.alloc_constructor (constructor_tag c "IO.io") (List.cons (LLVMValue.var_ unit_temp) List.empty) in
                                            let alloc_instr := LLVMInstruction.assign io_temp alloc_val in
                                            match build_set_field_instrs (LLVMValue.var_ io_temp) (List.cons (LLVMValue.var_ unit_temp) List.empty) 0 ctx4 {
                                                { ctx := ctx_set, instrs := set_instrs } =>
                                                    let entry_instrs := cons_instr len_instr (cons_instr write_instr (cons_instr unit_instr (cons_instr alloc_instr (append_instrs set_instrs (cons_instr (LLVMInstruction.ret (LLVMValue.var_ io_temp)) empty_instrs))))) in
                                                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                                    let native_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (cons_block entry_block empty_blocks) true in
                                                    { ctx := ctx_set, funcs := (cons_func native_func empty_funcs), globals := empty_globals_list }
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

/// Compile a canonical Def (de Bruijn Term) to LLVM IR.
#[partial]
def compile_db_def_ir (c : CodegenCtx) (def_ : Def) : DefResult := match def_ {
    Def.mk name typ term_ constraints attrs _vis =>
        // Must match Term.var's call-site naming exactly (its "not a
        // local, not a constructor" fallback also runs the referenced
        // name through replace_dots_with_underscores before emitting a
        // call) -- a dotted top-level name like "Option.get_or_default"
        // previously defined itself as literal LLVM function
        // "Option.get_or_default" while every CALL to it emitted
        // "Option_get_or_default", an "undefined value" link error the
        // first time any real program actually called a dotted def name.
        let fn_name := replace_dots_with_underscores (module_path_to_str name) in
        let params := collect_db_params term_ in
        let llvm_params := build_llvm_params_db params in
        match native_runtime_fn_name attrs {
            Option.some wrap_kind => compile_native_def_wrapper_ir c fn_name llvm_params wrap_kind params,
            Option.none => compile_db_def_ir_body c fn_name typ term_ params llvm_params,
        },
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
                                let unit_val := LLVMValue.alloc_constructor 0 empty_vals in
                                let assign := LLVMInstruction.assign temp unit_val in
                                let new_instrs := append_instrs instrs_r (cons_instr assign empty_instrs) in
                                let entry_instrs := append_instrs new_instrs (cons_instr (LLVMInstruction.ret (LLVMValue.var_ temp)) empty_instrs) in
                                let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                                let all_blocks_raw := append_blocks (cons_block entry_block empty_blocks) blocks_r in
                                let all_blocks := if needs_io_unwrap then unwrap_io_return_blocks all_blocks_raw 0 else all_blocks_raw in
                                let main_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ all_blocks true in
                                { ctx := ctx_t, funcs := (cons_func main_func funcs_r), globals := globals_r }
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
                        let entry_instrs :=
                            if already_terminated
                            then instrs_r
                            else append_instrs bmr.instrs (cons_instr (LLVMInstruction.ret bmr.val) empty_instrs) in
                        let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                        let all_blocks_raw := append_blocks (cons_block entry_block empty_blocks) blocks_r in
                        let all_blocks := if needs_io_unwrap then unwrap_io_return_blocks all_blocks_raw 0 else all_blocks_raw in
                        let main_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ all_blocks true in
                        { ctx := bmr.ctx, funcs := (cons_func main_func funcs_r), globals := globals_r }
                },
        }

/// Compile a list of canonical Defs to LLVM functions.
#[partial]
def compile_db_def_list (c : CodegenCtx) (defs : List Def) : DefResult := match defs {
    // Trailing comma load-bearing -- see `build_get_env_instrs`'s doc
    // comment above for why.
    List.empty => { ctx := c, funcs := empty_funcs, globals := empty_globals_list },
    List.cons d rest =>
        match compile_db_def_ir c d {
            { ctx := ctx_d, funcs := funcs_d, globals := globals_d } =>
                match compile_db_def_list ctx_d rest {
                    { ctx := ctx_rest, funcs := funcs_rest, globals := globals_rest } =>
                        { ctx := ctx_rest, funcs := (append_funcs funcs_d funcs_rest), globals := (append_globals globals_d globals_rest) }
                },
        },
}

/// Compile a list of canonical Defs to a complete LLVM module.
#[partial]
def compile_db_decls_ir (defs : List Def) : LLVMModule :=
    let arities := build_arity_table defs in
    match compile_db_def_list (empty_ctx arities str_map_empty) defs {
        { ctx := _, funcs := compiled_funcs, globals := compiled_globals } =>
            let funcs := ren_main_and_wrap compiled_funcs in
            LLVMModule.mk "x86_64-unknown-linux-gnu" compiled_globals funcs runtime_declarations,
    }

/// Compile a list of Decl to a complete LLVM module.
/// Extracts def_d and inductive_d entries, compiles constructors and defs.
#[partial]
def compile_db_module (decl_list : List Decl) : LLVMModule :=
    let defs := extract_defs decl_list in
    let inds := extract_inductives decl_list in
    let ctor_tags := build_constructor_tag_map inds in
    let ctor_funcs := compile_db_inductive_decls inds ctor_tags in
    let arities := build_arity_table defs in
    match compile_db_def_list (empty_ctx arities ctor_tags) defs {
        { ctx := _, funcs := compiled_funcs, globals := compiled_globals } =>
            let all_funcs := append_funcs ctor_funcs compiled_funcs in
            let funcs := ren_main_and_wrap all_funcs in
            LLVMModule.mk "x86_64-unknown-linux-gnu" compiled_globals funcs runtime_declarations,
    }

/// Extract def_d entries from a list of Decl. A def wrapped in
/// Decl.scoped_open_d is intentionally invisible to codegen for now
/// (deliberate gap — see Decl.scoped_open_d's doc comment).
#[partial]
def extract_defs (decl_list : List Decl) : List Def := match decl_list {
    List.empty => List.empty,
    List.cons d rest =>
        let rest_defs := extract_defs rest in
        match d {
            Decl.def_d def_ => List.cons def_ rest_defs,
            _ => rest_defs,
        }
}

/// Extract inductive_d entries from a list of Decl.
#[partial]
def extract_inductives (decl_list : List Decl) : List Inductive := match decl_list {
    List.empty => List.empty,
    List.cons d rest =>
        let rest_inds := extract_inductives rest in
        match d {
            Decl.inductive_d ind => List.cons ind rest_inds,
            _ => rest_inds,
        }
}

/// Compile a list of canonical InductConstructors to LLVM constructor wrapper functions.
/// `ctor_tags` -- see `build_constructor_tag_map`'s own doc comment;
/// looked up by the constructor's full DOTTED name ("TypeName.ctorName")
/// -- falls back to tag 0 for anything not found (shouldn't happen for a
/// real reachable inductive, since `ctor_tags` is built from this exact
/// same `List Inductive`; matches this file's other "absent from the
/// table" fallbacks, e.g. `ctx_lookup_arity`'s own doc comment).
#[partial]
def compile_db_inductive_constructors (type_name : String) (constructors : List InductConstructor) (ctor_tags : HashMap String I64) : List LLVMFunction := match constructors {
    List.empty => empty_funcs,
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
                // Keyed by BARE name -- see `assign_constructor_tags`'s
                // own doc comment for why (match dispatch can only ever
                // supply the bare name, so the map is keyed that way
                // uniformly).
                let tag := match str_map_lookup name_str ctor_tags {
                    Option.some t => t,
                    Option.none => 0,
                } in
                let func := compile_constructor_decl qualified_name field_count tag in
                cons_func func (compile_db_inductive_constructors type_name rest ctor_tags)
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
    List.empty => empty_funcs,
    List.cons ind rest =>
        let funcs := compile_db_inductive ind ctor_tags in
        append_funcs funcs (compile_db_inductive_decls rest ctor_tags)
}

/// Builds a `HashMap` from a constructor's full DOTTED name
/// ("TypeName.ctorName") to a fresh, globally-unique tag, for every
/// constructor of every declared `Inductive` in the whole program.
/// Starts at 16 -- past `constructor_tag`'s existing hardcoded 0-15
/// builtin range (`unit, true, false, none, some, empty, cons, io,
/// trivial, refl, ok, err, zero, succ, nil, pair`), which is left
/// completely untouched (zero risk to already-working code) --
/// `constructor_tag`/`is_constructor_var` only ever consult this map as
/// a FALLBACK for a name the hardcoded list doesn't recognize.
/// See `implementations/2026-08-29-user-defined-constructor-codegen-gap.md`.
#[partial]
def build_constructor_tag_map (inds : List Inductive) : HashMap String I64 :=
    build_constructor_tag_map_go inds 16 str_map_empty

#[partial]
def build_constructor_tag_map_go (inds : List Inductive) (next_tag : I64) (acc : HashMap String I64) : HashMap String I64 := match inds {
    List.empty => acc,
    List.cons ind rest =>
        match ind {
            Inductive.mk _name _params _typ constructors _attrs _vis =>
                match assign_constructor_tags constructors next_tag acc {
                    TagAssignResult.mk next_tag2 acc2 => build_constructor_tag_map_go rest next_tag2 acc2,
                },
        },
}

struct TagAssignResult {
    next_tag : I64,
    acc : HashMap String I64,
}

/// Keyed by the constructor's own BARE name only (e.g. "present"), NOT
/// qualified by its enclosing type -- match dispatch (`build_match_
/// chain`'s own `MatchCase.mc` field, which never carries the type it
/// belongs to) can only ever supply the bare name, so a qualified key
/// would silently miss there and fall back to tag 0 (confirmed as a real
/// bug via a direct repro: a match on a custom 2-constructor type always
/// took the first arm, since BOTH arms' tag comparisons resolved to 0).
/// This mirrors the EXISTING hardcoded builtin table's own "check base
/// names" tier exactly (`unit`/`true`/`false`/... are already assumed
/// globally unique by bare name) -- extends the SAME assumption to
/// user-defined types rather than fixing it, which would need threading
/// the scrutinee's own static type down into match compilation (a much
/// bigger, separate change). Two different reachable user-defined types
/// sharing a bare constructor name would collide here, same as they
/// always could against the hardcoded 16 -- a known, accepted limitation,
/// not a regression.
#[partial]
def assign_constructor_tags (constructors : List InductConstructor) (next_tag : I64) (acc : HashMap String I64) : TagAssignResult := match constructors {
    List.empty => { next_tag := next_tag, acc := acc },
    List.cons c rest =>
        match c {
            InductConstructor.mk name _params _typ =>
                let acc2 := str_map_insert (module_path_to_str name) next_tag acc in
                assign_constructor_tags rest (next_tag + 1) acc2,
        },
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
    let entry_block := LLVMBasicBlock.mk "entry" (cons_instr assign_instr (cons_instr ret_instr empty_instrs)) in
    let func_name := String.concat "monad_ctor_" con_name in
    LLVMFunction.mk func_name params LLVMType.i64_ (cons_block entry_block empty_blocks) true

#[partial]
def build_constructor_params (count : I64) : List ParamPair :=
    build_params_from count 0

#[partial]
def build_params_from (count : I64) (idx : I64) : List ParamPair :=
    if idx == count then empty_pairs
    else
        let name := String.concat "p" (I64.to_string idx) in
        cons_pair (ParamPair.mk name LLVMType.i64_) (build_params_from count (idx + 1))

#[partial]
def build_param_fields (count : I64) : List LLVMValue :=
    build_fields_from count 0

#[partial]
def build_fields_from (count : I64) (idx : I64) : List LLVMValue :=
    if idx == count then empty_vals
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

#[partial]
def empty_vals : List LLVMValue := List.empty

#[partial]
def empty_phis : List PhiPair := List.empty

#[partial]
def cons_phi (p : PhiPair) (ps : List PhiPair) : List PhiPair := List.cons p ps

#[partial]
def append_phis (a : List PhiPair) (b : List PhiPair) : List PhiPair := match a {
    List.empty => b,
    List.cons x rest => List.cons x (append_phis rest b),
}

#[partial]
def cons_instr (i : LLVMInstruction) (is : List LLVMInstruction) : List LLVMInstruction :=
    List.cons i is

#[partial]
def empty_pairs : List ParamPair := List.empty

#[partial]
def cons_pair (p : ParamPair) (ps : List ParamPair) : List ParamPair :=
    List.cons p ps

#[partial]
def empty_strs : List String := List.empty

#[partial]
def cons_str (s : String) (ss : List String) : List String := List.cons s ss

#[partial]
def mk_decl (name : String) (params : List String) (ret_ty : String) : LLVMDeclaration :=
    LLVMDeclaration.mk name params ret_ty

#[partial]
def empty_decls : List LLVMDeclaration := List.empty

#[partial]
def runtime_declarations : List LLVMDeclaration :=
    let d1 := mk_decl "monad_alloc" (cons_str "i64" empty_strs) "i8*" in
    let d2 := mk_decl "monad_retain" (cons_str "i8*" empty_strs) "void" in
    let d3 := mk_decl "monad_release" (cons_str "i8*" empty_strs) "void" in
    let d4 := mk_decl "monad_print_str" (cons_str "i8*" empty_strs) "void" in
    let d5 := mk_decl "monad_read_file" (cons_str "i8*" empty_strs) "i8*" in
    let d6 := mk_decl "monad_write_file" (cons_str "i8*" (cons_str "i8*" (cons_str "i64" empty_strs))) "void" in
    let d7 := mk_decl "monad_file_exists" (cons_str "i8*" empty_strs) "i8*" in
    let d7b := mk_decl "monad_is_dir" (cons_str "i8*" empty_strs) "i8*" in
    let d7c := mk_decl "monad_string_hash" (cons_str "i8*" empty_strs) "i64" in
    let d8 := mk_decl "alloc_closure" (cons_str "i8*" (cons_str "i64" (cons_str "i64" empty_strs))) "i64" in
    let d9 := mk_decl "alloc_constructor" (cons_str "i64" (cons_str "i64" empty_strs)) "i64" in
    let d10 := mk_decl "alloc_string" (cons_str "i8*" (cons_str "i64" empty_strs)) "i64" in
    // Tag/field accessors for match dispatch (compile_match_ir) --
    // there's no other way to read back what an already-allocated value
    // was tagged/constructed with.
    let d11 := mk_decl "monad_get_tag" (cons_str "i64" empty_strs) "i64" in
    let d12 := mk_decl "monad_get_field" (cons_str "i64" (cons_str "i64" empty_strs)) "i64" in
    // Writes a constructor's field at allocation time (compile_con_ir) --
    // alloc_constructor only ever allocates space, it has no way to
    // accept field values itself.
    let d13 := mk_decl "monad_set_field" (cons_str "i64" (cons_str "i64" (cons_str "i64" empty_strs))) "void" in
    // Fixed-arity indirect-call trampolines for a boxed, zero-capture
    // closure value (runtime.c's apply_closureN family) -- see that
    // file's own doc comment on the family. Used by
    // compile_general_db_call's callee dispatch whenever the callee is a
    // computed value rather than a statically-known global name.
    let d14 := mk_decl "apply_closure1" (cons_str "i64" (cons_str "i64" empty_strs)) "i64" in
    let d15 := mk_decl "apply_closure2" (apply_closure_arg_types 2) "i64" in
    let d16 := mk_decl "apply_closure3" (apply_closure_arg_types 3) "i64" in
    let d17 := mk_decl "apply_closure4" (apply_closure_arg_types 4) "i64" in
    let d18 := mk_decl "apply_closure5" (apply_closure_arg_types 5) "i64" in
    let d19 := mk_decl "apply_closure6" (apply_closure_arg_types 6) "i64" in
    let d20 := mk_decl "apply_closure7" (apply_closure_arg_types 7) "i64" in
    let d21 := mk_decl "apply_closure8" (apply_closure_arg_types 8) "i64" in
    // `I64.to_string` (init/number.mo) is, like `I64.add`, a
    // native-signature-only def with no `:=` body at all -- unlike
    // `I64.add`, it had no runtime backing whatsoever (no C function,
    // no NativeOp variant), so every call to it -- reached only once
    // `lookup_native_any`'s I64_add-style fast path was fixed to
    // actually fire, see that fix's own doc comment -- fell through to
    // the same "Term.hole compiles as a bogus Unit stub" bug: `println
    // (I64.to_string n)` printed nothing at all (a real, hand-compiled
    // repro). `monad_i64_to_string` (runtime.c) is the actual
    // implementation; `test_compile_i64_to_string_native`
    // (lang/codegen/test/compile_tests.mo) is its regression test.
    let d22 := mk_decl "monad_i64_to_string" (cons_str "i64" empty_strs) "i8*" in
    // `Term.ntv`/`compile_ntv_ir`'s generic native-call mechanism (used
    // for every `#[native ...]`-attributed def, e.g. `String.length`)
    // emits a bare `call i64 @monad_<name>(...)` with no accompanying
    // `declare` of its own -- unlike a genuinely first-referenced-by-call
    // symbol in ordinary C, LLVM's textual IR does NOT implicitly
    // synthesize a declaration for it (confirmed via a direct repro: omitting
    // this line reproduced the exact same "use of undefined value
    // '@monad_string_length'" `llc` failure `monad_i64_to_string` (just
    // above) needed its own explicit declare entry to avoid) -- every
    // native this module ever calls needs its own entry here regardless
    // of which of the two parallel native-dispatch mechanisms
    // (`lookup_native_any` vs. `Term.ntv`) it goes through.
    let d23 := mk_decl "monad_string_length" (cons_str "i64" empty_strs) "i64" in
    // Same requirement as `monad_string_length` just above --
    // `compile_native_def_wrapper_ir`'s own `call` (the "native def
    // compiles to a real wrapper" fix) hits the identical "no implicit
    // declare" gap.
    let d24 := mk_decl "monad_string_concat" (cons_str "i64" (cons_str "i64" empty_strs)) "i64" in
    let d25 := mk_decl "monad_string_eq" (cons_str "i64" (cons_str "i64" empty_strs)) "i64" in
    // Closure free-variable capture (see `monad_closure_get_env`/
    // `monad_closure_set_env`, `runtime.c`, and `compile_db_lam_ir`'s
    // own doc comment above).
    let d26 := mk_decl "monad_closure_get_env" (cons_str "i64" (cons_str "i64" empty_strs)) "i64" in
    let d27 := mk_decl "monad_closure_set_env" (cons_str "i64" (cons_str "i64" (cons_str "i64" empty_strs))) "void" in
    [d1, d2, d3, d4, d5, d6, d7, d7b, d7c, d8, d9, d10, d11, d12, d13,
     d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27]

/// `apply_closureN`'s own declared param list: the closure value itself
/// plus `n` ordinary args, all i64 (matches every def's own uniform
/// boxed-i64 calling convention). `n` is the applied arity, so this
/// always produces `n + 1` total "i64" strings.
#[partial]
def apply_closure_arg_types (n : I64) : List String :=
    cons_str "i64" (repeat_str "i64" n)

#[partial]
def repeat_str (s : String) (n : I64) : List String :=
    if I64.beq n 0 then empty_strs else cons_str s (repeat_str s (n - 1))

#[partial]
def empty_funcs : List LLVMFunction := List.empty

#[partial]
def cons_func (f : LLVMFunction) (fs : List LLVMFunction) : List LLVMFunction :=
    List.cons f fs

#[partial]
def empty_globals_list : List LLVMGlobal := List.empty

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
            LLVMFunction.mk name params ret_ty blocks ghc_cc =>
                if list_contains_str seen name
                then dedup_funcs_by_name_go rest seen
                else List.cons f (dedup_funcs_by_name_go rest (List.cons name seen)),
        },
}

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
            LLVMFunction.mk name params ret_ty blocks ghc_cc =>
                if String.beq name "main" then true
                else has_main rest,
        },
}

/// When the user's main has no params, add an `args` param (List String from C runtime).
/// If main already has params (user wrote `def main (args : List String)`), keep them.
#[partial]
def rename_main (funcs : List LLVMFunction) : List LLVMFunction := match funcs {
    List.empty => empty_funcs,
    List.cons f rest =>
        match f {
            LLVMFunction.mk name params ret_ty blocks ghc_cc =>
                if String.beq name "main"
                then
                    let main_params := ensure_main_params params in
                    cons_func (LLVMFunction.mk "main_monad" main_params ret_ty blocks ghc_cc) (rename_main rest)
                else if ends_with_main name then
                    // For module-qualified main functions, always rename to just "main_monad"
                    // The runtime expects this exact name
                    let main_params := ensure_main_params params in
                    cons_func (LLVMFunction.mk "main_monad" main_params ret_ty blocks ghc_cc) (rename_main rest)
                else
                    cons_func f (rename_main rest),
        },
}

/// If main has no params, add a synthetic `args` param (List String from C runtime).
/// If main already has params (user wrote `def main (args : List String)`), keep them.
#[partial]
def ensure_main_params (params : List ParamPair) : List ParamPair := match params {
    List.empty => cons_pair (ParamPair.mk "args" LLVMType.i64_) empty_pairs,
    List.cons x y => params,
}

// === De Bruijn (canonical) def compilation ===

/// Collect lambda params from a de Bruijn Term body.
/// Strips `Term.lam` prefixes and returns Param for each.
#[partial]
def collect_db_params (term_ : Term) : List Param := match term_ {
    Term.lam dbg typ body =>
        let name : Identifier := match dbg {
            DebugName.named id => id,
            DebugName.unnamed => Identifier.id "x",
        } in
        let param_ := param_many name typ in
        List.cons param_ (collect_db_params body),
    Term.forall dbg kind body => collect_db_params body,
    _ => List.empty,
}

/// Strip lambda/forall prefixes from a de Bruijn Term body.
#[partial]
def strip_db_lams (term_ : Term) : Term := match term_ {
    Term.lam dbg typ body => strip_db_lams body,
    Term.forall dbg kind body => strip_db_lams body,
    _ => term_,
}

#[test]
def test_runtime_decls_not_empty : Bool :=
    match runtime_declarations {
        List.empty => false,
        List.cons x y => true,
    }

#[test]
def test_module_emit_has_header : Bool :=
    let text := emit_module (compile_db_decls_ir List.empty) in
    let prefix := String.slice text 0 12 in
    String.beq prefix "; ModuleID ="

#[test]
def test_empty_decls_module : Bool :=
    match (compile_db_decls_ir List.empty) {
        LLVMModule.mk triple globals funcs decl_list =>
            String.beq triple "x86_64-unknown-linux-gnu",
    }

#[test]
def test_compile_db_inductive_decls : Bool :=
    let some_name := ModulePath.mp (List.cons (Identifier.id "Some") List.empty) in
    let some_ctor := InductConstructor.mk some_name empty_params_list (Term.type_ 1) in
    let none_name := ModulePath.mp (List.cons (Identifier.id "None") List.empty) in
    let none_ctor := InductConstructor.mk none_name empty_params_list (Term.type_ 1) in
    let ctors := List.cons some_ctor (List.cons none_ctor List.empty) in
    let ind_name := ModulePath.mp (List.cons (Identifier.id "Option") List.empty) in
    let ind := Inductive.mk ind_name empty_params_list (Term.type_ 1) ctors empty_attrs Visibility.package_private in
    let funcs := compile_db_inductive_decls (List.cons ind List.empty) str_map_empty in
    let mod_ := LLVMModule.mk "x86_64-unknown-linux-gnu" empty_globals_list funcs empty_decls in
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
    let some_ctor := InductConstructor.mk some_name empty_params_list (Term.type_ 1) in
    let none_name := ModulePath.mp (List.cons (Identifier.id "None") List.empty) in
    let none_ctor := InductConstructor.mk none_name empty_params_list (Term.type_ 1) in
    let ctors := List.cons some_ctor (List.cons none_ctor List.empty) in
    let ind_name := ModulePath.mp (List.cons (Identifier.id "Option") List.empty) in
    let ind := Inductive.mk ind_name empty_params_list (Term.type_ 1) ctors empty_attrs Visibility.package_private in
    let tag_map := build_constructor_tag_map (List.cons ind List.empty) in
    let c := empty_ctx empty_arities tag_map in
    is_constructor_var c "Option.Some" && is_constructor_var c "Option.None"

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
    match compile_db_def_ir (empty_ctx empty_arities str_map_empty) (native_def_fixture name target) {
        { ctx := _, funcs := funcs, globals := _ } =>
            emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" empty_globals_list funcs empty_decls),
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
    // A native this backend doesn't implement yet (e.g. string_slice)
    // must be completely unaffected by the whitelist -- still the
    // pre-existing stub behavior, not a call to a nonexistent runtime
    // function.
    let text := compile_native_def_fixture_text "String.slice" "string_slice" in
    if check_contains text "call i64 @alloc_constructor(i64 0, i64 0)"
    then not (check_contains text "@monad_string_slice")
    else false

#[partial]
def empty_params_list : List Param := List.empty

#[partial]
def empty_attrs : List Attribute := List.empty

#[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

// === Multi-module compilation ===

/// Replace dots with underscores in a string for use as LLVM identifier
#[partial]
def replace_dots_with_underscores (s : String) : String := 
    replace_dots_loop s ""

#[partial]
def replace_dots_loop (s : String) (acc : String) : String := 
    if String.beq s "" then acc
    else
        let first_char : U8 := match String.get s 0 {
            Option.some b => b,
            Option.none => 0u8
        } in
        let rest := String.slice s 1 (String.length s) in
        let dot_byte : U8 := 46u8 in  // '.' character
        if U8.beq first_char dot_byte then
            replace_dots_loop rest (String.concat acc "_")
        else
            replace_dots_loop rest (String.concat acc (String.slice s 0 1))

/// Check if a function name is a main function (handles both "main" and module_main)
#[partial]
def ends_with_main (name : String) : Bool := 
    if String.beq name "main" then true
    else if String.length name > 3 then
        let suffix := String.slice name (String.length name - 3) (String.length name) in
        String.beq suffix "_main"
    else false

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
def compile_loaded_modules_to_ir (loaded : LoadedModules) (verbose : Bool) : IO (Result String LLVMModule) := do {
    let total_start := Bench.now;

    let all_mods := get_loaded_all loaded;

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
    let t_open_alias := Bench.now;
    let aliased_mods := resolve_open_aliases_in_modules all_mods;
    if verbose then do {
        let _ := Bench.report "open_alias_resolve" (I64.sub Bench.now t_open_alias);
        return unit
    } else return unit;

    // Stage 1: collect all declarations without module prefixes
    let t_collect := Bench.now;
    let all_decls := collect_all_decls_from_modules aliased_mods List.empty;
    if verbose then do {
        let def_count := List.length all_decls;
        let _ := Bench.report "collect_decls" (I64.sub Bench.now t_collect);
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
    let t_infix := Bench.now;
    let infixes := collect_infixes all_decls;
    let resolved_decls := resolve_infix_decls infixes all_decls;
    if verbose then do {
        let _ := Bench.report "infix_resolve" (I64.sub Bench.now t_infix);
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
    let t_dict := Bench.now;
    let promoted_decls := promote_instance_defs resolved_decls;
    let dict_param_decls := add_constraint_dict_params_decls promoted_decls;
    if verbose then do {
        let _ := Bench.report "dict_dispatch" (I64.sub Bench.now t_dict);
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
    let t_elab := Bench.now;
    let target_mp : ModulePath := match get_loaded_main loaded { ModuleInfo.mk mp_ _ _ => mp_ };
    let scope_data : ScopeData := build_scope_from_decls target_mp dict_param_decls;
    let scope : Scope := { module_id := target_mp, scope := scope_data, parent := Option.none };
    let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
    let elaborated := elaborate_module_decls_best_effort scope dict_param_decls empty_locs;
    let dispatched_decls := resolve_class_calls_decls elaborated;
    if verbose then do {
        let _ := Bench.report "elaborate_class" (I64.sub Bench.now t_elab);
        return unit
    } else return unit;

    // Stage 5: only compile Defs actually reachable (transitively) from `main` --
    // compiling the FULL 264-def loaded set unconditionally meant any
    // codegen bug anywhere in the whole standard library, reached or
    // not, blocked compiling any program at all. See
    // filter_reachable_decls's own doc comment.
    let t_reach := Bench.now;
    let reachable_decls := filter_reachable_decls dispatched_decls;
    if verbose then do {
        let reachable_count := List.length reachable_decls;
        let _ := Bench.report "filter_reachable" (I64.sub Bench.now t_reach);
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
        Result.ok _ => do {
            // Stage 6: compile the reachable, infix-resolved declarations to LLVM IR
            let t_llvm := Bench.now;
            let mod_ := compile_db_module reachable_decls;
            if verbose then do {
                let _ := Bench.report "compile_db_module" (I64.sub Bench.now t_llvm);
                let _ := Bench.report "compile_loaded_modules_to_ir total" (I64.sub Bench.now total_start);
                return unit
            } else return unit;

            return (Result.ok mod_)
        },
    }
}

/// Restricts `decl_list` to the transitive closure of Defs reachable from a
/// top-level `main`, plus every Inductive (kept unconditionally --
/// constructor-wrapper compilation is cheap, uniform, and, after the
/// qualified-naming fix in compile_db_inductive_constructors, collision
/// -free regardless of how many are compiled, so there's no correctness
/// reason to filter them and every reason to keep this simple).
/// `compile_loaded_modules_to_ir` previously fed `compile_db_module`
/// every loaded module's ENTIRE declaration set -- prelude, init,
/// string, number, io, id, ... -- regardless of whether the program
/// being compiled actually calls into any of it, so a codegen bug in
/// ANY of those 264 defs (even ones with zero callers from the actual
/// program) blocked compiling ANYTHING.
#[partial]
def filter_reachable_decls (decl_list : List Decl) : List Decl :=
    let all_defs := extract_defs decl_list in
    let all_inds := extract_inductives decl_list in
    // O(total) once, instead of `reachable_defs_from` re-scanning
    // `all_defs` per worklist item (O(reachable x total) -- confirmed the
    // dominant cost of a full self-compile via `--verbose` stage timing,
    // ~453s of ~944s). See `str_map_*`'s own doc comment for why this
    // bypasses `Map`'s typeclass dispatch (`BTreeMap.insert_loop`/
    // `lookup_loop` directly with `String.lt`/`String.gt`) instead of
    // calling `Map.insert`/`Map.lookup` -- same latent-bug workaround
    // `lang/scope.mo`'s `modpath_map_*` already uses.
    let defs_map := build_def_name_map all_defs str_map_empty in
    let reachable := reachable_defs_from defs_map (List.cons "main" List.empty) str_map_empty List.empty in
    List.append (map_inductive_decl all_inds) (map_def_decl reachable)

/// A `String`-keyed `HashMap` (preferred over `BTreeMap` here for
/// performance -- 16-bucket chaining beats an unbalanced-in-the-worst-
/// case tree walk at this N), bypassing `Map`'s abstract typeclass
/// dispatch (`Map.insert`/`Map.lookup`, the `[Hashable K, BOrd K] Map
/// HashMap` instance, `std/map.mo`) in favor of `HashMap.bucket_of`/
/// `get_bucket`/`set_bucket`/`bucket_insert`/`bucket_lookup` called
/// directly with plain `String.hash`/`String.lt`/`String.gt` (concrete
/// native functions, no class-method resolution at all). Mirrors
/// `lang/scope.mo`'s own `modpath_map_*` helpers exactly (just without
/// their `show_module_path` projection step -- `String` needs none),
/// which document why: calling through `Map`'s generic dispatch resolves
/// `Hashable.hash`/`BOrd.lt`/`BOrd.gt` as abstract class-method
/// references INSIDE `HashMap`'s own generic `[K, V]`-parameterized
/// body, and AGENTS.md's documented evaluator limitation
/// ("`resolve_class_method_instance` picks the FIRST REGISTERED
/// instance", not a type-directed lookup) means these can silently
/// resolve to the WRONG instance whenever invoked from deep within an
/// already-polymorphic call chain -- confirmed as a real, live bug for
/// `ScopeData.def_refs`/`inductives`, not just theoretical.
/// `String.hash`/`String.lt`/`String.gt` need no such dispatch at all
/// (native, already monomorphic), so this sidesteps the whole class of
/// risk rather than merely hoping it doesn't fire here too.
#[partial]
def str_map_empty {V : Type} : HashMap String V := HashMap.map HashMap.empty_buckets

#[partial]
def str_map_insert {V : Type} (key : String) (val : V) (m : HashMap String V) : HashMap String V :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            let bucket := HashMap.get_bucket buckets idx in
            let new_bucket := HashMap.bucket_insert String.lt String.gt key val bucket in
            HashMap.map (HashMap.set_bucket buckets idx new_bucket)
    }

#[partial]
def str_map_lookup {V : Type} (key : String) (m : HashMap String V) : Option V :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            let bucket := HashMap.get_bucket buckets idx in
            HashMap.bucket_lookup String.lt String.gt key bucket
    }

#[partial]
def build_def_name_map (defs : List Def) (acc : HashMap String Def) : HashMap String Def := match defs {
    List.empty => acc,
    List.cons d rest => build_def_name_map rest (str_map_insert (def_name_str d) d acc),
}

#[partial]
def map_def_decl (defs : List Def) : List Decl := match defs {
    List.empty => List.empty,
    List.cons d rest => List.cons (Decl.def_d d) (map_def_decl rest),
}

#[partial]
def map_inductive_decl (inds : List Inductive) : List Decl := match inds {
    List.empty => List.empty,
    List.cons i rest => List.cons (Decl.inductive_d i) (map_inductive_decl rest),
}

#[partial]
def def_name_str (d : Def) : String := match d {
    Def.mk name _typ _term _constraints _attrs _vis => module_path_to_str name,
}

#[partial]
def def_body_term (d : Def) : Term := match d {
    Def.mk _name _typ term_ _constraints _attrs _vis => term_,
}

#[partial]
def list_contains_str (xs : List String) (x : String) : Bool := match xs {
    List.empty => false,
    List.cons hd rest => if String.beq hd x then true else list_contains_str rest x,
}

/// Worklist-based reachability closure: BFS/DFS over Def names starting
/// from `worklist`, following every name `collect_referenced_names`
/// finds in each reached Def's body, until no new names are discovered.
/// A name that doesn't match any known Def (a native op, a constructor,
/// a bound-but-not-top-level local) is simply skipped, not an error --
/// this is a conservative over-approximation by design (collecting
/// every `Term.var`/`Con`/`MatchCase` name in a body, not just genuinely
/// free top-level references, so it may keep a few unreachable-in-
/// practice defs, but never drops one that's actually needed).
///
/// `defs_map`/`visited` are `str_map_*`-backed `HashMap String _`
/// lookups (O(log total) each) rather than the `List`-linear-scan this
/// used to do (`find_def_by_name` + `list_contains_str` over `visited`,
/// O(reachable x total) + O(reachable^2) respectively) -- confirmed via
/// `--verbose` stage timing as the single largest cost of a full
/// self-compile (~453s of ~944s, bigger than `elaborate_class`).
#[partial]
def reachable_defs_from (defs_map : HashMap String Def) (worklist : List String) (visited : HashMap String Bool) (acc : List Def) : List Def :=
    match worklist {
        List.empty => acc,
        List.cons name rest =>
            match str_map_lookup name visited {
                Option.some _ => reachable_defs_from defs_map rest visited acc,
                Option.none =>
                    match str_map_lookup name defs_map {
                        Option.some d =>
                            let referenced := collect_referenced_names (def_body_term d) List.empty in
                            reachable_defs_from defs_map (List.append referenced rest) (str_map_insert name true visited) (List.cons d acc),
                        Option.none =>
                            reachable_defs_from defs_map rest (str_map_insert name true visited) acc,
                    },
            },
    }

/// Collects every name referenced anywhere inside a Term -- variable
/// references, constructor names, match-case pattern names -- into
/// `acc`. Over-approximates deliberately (see reachable_defs_from's doc
/// comment): also picks up local/bound names that happen to shadow a
/// top-level Def name, but that's harmless here (worst case, an
/// unrelated same-named top-level def gets kept too).
#[partial]
def collect_referenced_names (t : Term) (acc : List String) : List String := match t {
    Term.var _idx dbg =>
        match dbg {
            DebugName.named id => List.cons (show_identifier id) acc,
            DebugName.unnamed => acc,
        },
    Term.lam _dbg typ body => collect_referenced_names body (collect_referenced_names typ acc),
    Term.forall _dbg kind body => collect_referenced_names body (collect_referenced_names kind acc),
    Term.pi arg ret => collect_referenced_names ret (collect_referenced_names arg acc),
    Term.app fun_ arg_ => collect_referenced_names arg_ (collect_referenced_names fun_ acc),
    Term.ntv native => collect_referenced_names_native native acc,
    Term.con con_ => collect_referenced_names_con con_ acc,
    Term.lit lit_ => collect_referenced_names_lit lit_ acc,
    Term.type_ _universe => acc,
    Term.hole => acc,
}

/// Now total (no `#[partial]`) — `struct_lit`/`struct_update` are
/// unreachable in practice (see `compile_lit_ir`'s matching doc
/// comment), but reachability analysis should still be correct for
/// them independent of that: a name referenced only from inside a
/// struct-literal field value (or a struct-update override/base) must
/// not be stripped as dead code.
def collect_referenced_names_lit (l : Literal) (acc : List String) : List String := match l {
    Literal.num _n _suffix => acc,
    Literal.flt _text _suffix => acc,
    Literal.str _s => acc,
    Literal.if_ cond then_ else_ => collect_referenced_names else_ (collect_referenced_names then_ (collect_referenced_names cond acc)),
    Literal.match_ scrutinee cases => collect_referenced_names_cases cases (collect_referenced_names scrutinee acc),
    Literal.struct_lit fields _type_name => collect_referenced_names_struct_fields fields acc,
    Literal.struct_update base fields => collect_referenced_names_struct_fields fields (collect_referenced_names base acc),
}

#[partial]
def collect_referenced_names_struct_fields (fields : List StructLitField) (acc : List String) : List String :=
    match fields {
        List.empty => acc,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value => collect_referenced_names_struct_fields rest (collect_referenced_names value acc),
            }
    }

#[partial]
def collect_referenced_names_cases (cases : List MatchCase) (acc : List String) : List String := match cases {
    List.empty => acc,
    List.cons c rest =>
        match c {
            MatchCase.mc name _args body _fp =>
                collect_referenced_names_cases rest (List.cons (show_identifier name) (collect_referenced_names body acc)),
        },
}

#[partial]
def collect_referenced_names_native (n : Native) (acc : List String) : List String := match n {
    Native.mk _name _num_args args => collect_referenced_names_opt_list args acc,
}

#[partial]
def collect_referenced_names_con (c : Con) (acc : List String) : List String := match c {
    Con.mk name _typ_name _num_args args => List.cons (show_identifier name) (collect_referenced_names_opt_list args acc),
}

#[partial]
def collect_referenced_names_opt_list (args : List (Option Term)) (acc : List String) : List String := match args {
    List.empty => acc,
    List.cons opt_ rest =>
        match opt_ {
            Option.some t => collect_referenced_names_opt_list rest (collect_referenced_names t acc),
            Option.none => collect_referenced_names_opt_list rest acc,
        },
}

#[partial]
def collect_all_decls_from_modules (modules : List ModuleInfo) (acc : List Decl) : List Decl := match modules {
    List.empty => acc,
    List.cons mod_ rest => 
        let mod_decls := get_module_info_decls mod_ in
        collect_all_decls_from_modules rest (append_decls_list mod_decls acc),
}

#[partial]
def append_decls_list (a : List Decl) (b : List Decl) : List Decl := match a {
    List.empty => b,
    List.cons hd tl => List.cons hd (append_decls_list tl b),
}
