use std.list {intercalate}

type LLVMType {
    void,
    i1_,
    i8_,
    i32_,
    i64_,
    ptr (inner : LLVMType),
    fn_ (params : List LLVMType) (ret : LLVMType),
    struct_ (name : String),
}

type ParamPair {
    mk (param_name : String) (param_ty : LLVMType),
}

type PhiPair {
    mk (val : LLVMValue) (label : String),
}

type NativeOp {
    op_add, op_sub, op_mul, op_sdiv, op_eq, op_lt, op_gt, op_ne,
    op_print_str, op_read_file, op_write_file, op_file_exists,
    op_is_dir, op_string_hash,
    op_i64_to_string,
}

type LLVMValue {
    int_ (n : I64),
    int32_ (n : I32),
    bool_ (b : Bool),
    void_val,
    var_ (name : String),
    parm_ (idx : I64),
    global_ (name : String),
    /// A direct reference to a top-level def's own compiled LLVM
    /// function, by its literal `@name` -- distinct from `var_` (an SSA
    /// local register, e.g. a `fresh_temp` result or a match-bound
    /// local, which may happen to hold a RUNTIME closure VALUE but is
    /// never itself a callable symbol) and from `global_` (a compiled
    /// string-literal constant, an unrelated concept that happens to
    /// also render as `@name`). Produced only by `compile_call_head`'s
    /// bare-global-name-in-callee-position bypass -- the ONLY place
    /// this backend knows for certain, from the term shape alone (not a
    /// runtime value), that a call's callee is a specific named global
    /// function, so `compile_general_db_call`'s dispatch can pick a
    /// real direct call over `apply_closureN`'s indirect-call fallback.
    /// See Phase 0 of plans/bootstrapping/self-hosted-compiler.md's
    /// dictionary-passing plan.
    fn_ref (name : String),
    call (fn_name : String) (ret_ty : LLVMType) (args : List LLVMValue) (tail : Bool),
    add (lhs : LLVMValue) (rhs : LLVMValue),
    sub (lhs : LLVMValue) (rhs : LLVMValue),
    mul (lhs : LLVMValue) (rhs : LLVMValue),
    sdiv (lhs : LLVMValue) (rhs : LLVMValue),
    udiv (lhs : LLVMValue) (rhs : LLVMValue),
    urem (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_eq (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_ne (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_slt (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_sgt (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_ult (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_ugt (lhs : LLVMValue) (rhs : LLVMValue),
    zext (val : LLVMValue) (from_ty : LLVMType) (to_ty : LLVMType),
    trunc (val : LLVMValue) (from_ty : LLVMType) (to_ty : LLVMType),
    /// Pointer-to-integer cast -- LLVM's ONLY legal conversion from a
    /// pointer value to an integer (`bitcast` explicitly disallows
    /// ptr<->int; confirmed via LLVM's own LangRef). Used to normalize a
    /// string LITERAL's `global_` (`ptr i8_`) reference to `i64` at its
    /// own construction site (`compile_lit_ir`'s `Literal.str` arm) --
    /// every COMPUTED String (`String.concat`, a boxed field, ...) is
    /// already `i64`-typed, so a bare literal used as a `phi`/match-merge
    /// branch's own value (the only place this backend needs every
    /// contributor to share ONE declared type -- ordinary calls tolerate
    /// per-argument type mismatches via `llc`'s own lenient callee-
    /// pointer-bitcast handling) previously produced a `phi i64 [ ...,
    /// @str_N, ... ]` that `llc` rejected outright ("global variable
    /// reference must have pointer type"). See plans/implementations/
    /// 2026-08-28-string-value-representation-unification.md.
    ptrtoint (val : LLVMValue) (from_ty : LLVMType) (to_ty : LLVMType),
    /// Integer-to-pointer cast -- the inverse of `ptrtoint`, and the
    /// companion a raw-`char*` byte access needs (see `load`'s own doc
    /// comment): this backend holds every pointer in an `i64` (Strings
    /// are raw `char*`, runtime.c:539-543), so reaching a loadable
    /// `i8*` first takes `inttoptr`. Used by the `lang/runtime.mo`
    /// generated-IR natives (plans/bootstrapping/self-hosted-runtime.md).
    inttoptr (val : LLVMValue) (from_ty : LLVMType) (to_ty : LLVMType),
    phi (pairs : List PhiPair),
    gep (base : LLVMValue) (indices : List I64),
    /// Typed load -- `load <ty>, <ptr_ty> <ptr>`. Previously a dead,
    /// never-constructed `load (ptr)` variant that rendered the invalid
    /// `load %p0` (no result type, untyped pointer); reborn with both
    /// missing pieces for the `lang/runtime.mo` generated-IR byte
    /// loop (`load i8, i8* %q` on an `inttoptr`'d address). `ptr_ty` is
    /// EXPLICIT (not derived via `llvm_value_type`) because the operand
    /// is in practice an SSA `var_` holding an `inttoptr`/`gep` result,
    /// and this backend's vars are `i64`-typed BY CONVENTION
    /// (`llvm_value_type`'s own `var_` arm) -- a var's real pointer
    /// type is unknowable from the value alone, and inttoptr on an SSA
    /// operand can't be inlined into the load (non-constant inttoptr is
    /// an instruction, not a constant expression).
    load (ty : LLVMType) (ptr_ty : LLVMType) (ptr : LLVMValue),
    bitcast (val : LLVMValue) (to_ty : LLVMType),
    alloc_closure (entry : String) (arity : I64) (env : List LLVMValue),
    alloc_constructor (tag : I64) (fields : List LLVMValue),
    native_op (op : NativeOp) (args : List LLVMValue),
}

type LLVMInstruction {
    assign (target : String) (value : LLVMValue),
    branch (cond : LLVMValue) (then_label : String) (else_label : String),
    jump (label : String),
    ret (val : LLVMValue),
    /// `store <pointee-typed val>, <ptr_ty> <ptr>` -- the write side
    /// `load`'s new typed form pairs with; no target SSA name (a store
    /// produces no value). `ptr_ty` is explicit for the same reason as
    /// `load`'s own (SSA vars are i64-typed by convention; the value's
    /// real pointer type is not derivable), and the renderer types the
    /// VALUE at `ptr_ty`'s pointee (`llvm_pointee`), not the value's own
    /// convention type -- LLVM requires the stored value's type to equal
    /// the pointee type, so the construction site must supply a value
    /// already at that width (e.g. `trunc` for an `i8*` store).
    store (val : LLVMValue) (ptr_ty : LLVMType) (ptr : LLVMValue),
    comment (text : String),
}

type LLVMBasicBlock {
    mk (label : String) (instructions : List LLVMInstruction),
}

/// A single point-in-source location for DWARF debug info -- v1 scope
/// is "one location per top-level def" (see plans/bootstrapping/
/// debug-info.md), not per-instruction, so this deliberately carries
/// just line/column, not a full `lang.types.SourceRange`/`Location`
/// (this file has no dependency on `lang.types` today; keeping it that
/// way avoids introducing one just for two integers).
struct DbgLoc {
    line : I64,
    column : I64,
}

/// `ghc_cc` selects LLVM's `cc 9` (GHC calling convention) -- true for
/// every compiled Monad def, false for the `lang/codegen/runtime.mo`
/// generated natives, which are ordinary ccc functions called from
/// cc-9 wrapper bodies.
struct LLVMFunction {
    name : String,
    params : List ParamPair,
    ret_ty : LLVMType,
    blocks : List LLVMBasicBlock,
    ghc_cc : Bool,
    dbg_loc : Option DbgLoc,
}

type LLVMGlobal {
    mk (name : String) (value : String) (byte_len : I64) (constant : Bool),
}

type LLVMDeclaration {
    mk (name : String) (params : List String) (ret_ty : String),
}

type LLVMModule {
    mk (target_triple : String)
       (globals : List LLVMGlobal)
       (functions : List LLVMFunction)
       (declarations : List LLVMDeclaration)
       /// The `.mo` source path debug info was requested for -- `none`
       /// means debug info is off (the default), in which case
       /// `emit_module` emits exactly the same text it always has.
       (debug_source : Option String),
}

open LLVMType {fn_, i1_, i32_, i64_, i8_, ptr, struct_, void}
open LLVMValue {
  add, alloc_closure, alloc_constructor, bitcast, bool_, call, fn_ref, gep, global_,
  icmp_eq, icmp_ne, icmp_sgt, icmp_slt, icmp_ult, icmp_ugt, int32_, int_, inttoptr,
  load, mul, native_op, parm_, phi, ptrtoint, sdiv, sub, trunc, udiv, urem, var_,
  void_val, zext,
}
open LLVMInstruction {assign, branch, comment, jump, ret, store}
open ParamPair {mk}
open PhiPair {mk}

#[partial]
def show_bool (b : Bool) : String := match b {
    true => "true",
    false => "false",
}

#[partial]
def show_llvm_type (ty : LLVMType) : String := match ty {
    void => "void",
    i1_ => "i1",
    i8_ => "i8",
    i32_ => "i32",
    i64_ => "i64",
    ptr inner => String.concat (show_llvm_type inner) "*",
    fn_ params ret => show_llvm_type_fn params ret,
    struct_ name => String.concat "%" name,
}

/// The element type a pointer type points at -- what a `store` through
/// it must render its value at (LLVM requires the stored value's type
/// to equal the pointee type, NOT the value's own convention type:
/// SSA vars are i64 by convention, so `store`'s renderer can't use
/// `llvm_value_type` on the value or every byte-pointer store would
/// come out as the ill-typed `store i64 %b, i8* %q`). A non-pointer
/// `ty` degenerates to `i64_` (never happens for a well-formed store;
/// keeps the function total).
def llvm_pointee (ty : LLVMType) : LLVMType := match ty {
    ptr inner => inner,
    _ => i64_,
}

#[partial]
def show_llvm_type_fn (params : List LLVMType) (ret : LLVMType) : String :=
    let params_str := join_types params in
    String.concat (show_llvm_type ret) (String.concat " (" (String.concat params_str ")"))

#[partial]
def join_types (types : List LLVMType) : String :=
    List.intercalate ", " (List.map show_llvm_type types)

#[partial]
def show_args_typed (args : List LLVMValue) : String :=
    List.intercalate ", " (List.map show_llvm_value_typed args)

#[partial]
def show_llvm_value (val : LLVMValue) : String := match val {
    int_ n => I64.to_string n,
    int32_ n => I32.to_string n,
    bool_ b => show_bool b,
    void_val => "void",
    var_ name => String.concat "%" name,
    parm_ idx => String.concat "%p" (I64.to_string idx),
    global_ name => String.concat "@" name,
    fn_ref name => String.concat "@" name,
    call fn_name ret_ty args tail => show_call fn_name ret_ty args tail,
    add lhs rhs => show_arith "add" lhs rhs,
    sub lhs rhs => show_arith "sub" lhs rhs,
    mul lhs rhs => show_arith "mul" lhs rhs,
    sdiv lhs rhs => show_arith "sdiv" lhs rhs,
    udiv lhs rhs => show_arith "udiv" lhs rhs,
    urem lhs rhs => show_arith "urem" lhs rhs,
    icmp_eq lhs rhs => show_arith "icmp eq" lhs rhs,
    icmp_ne lhs rhs => show_arith "icmp ne" lhs rhs,
    icmp_slt lhs rhs => show_arith "icmp slt" lhs rhs,
    icmp_sgt lhs rhs => show_arith "icmp sgt" lhs rhs,
    icmp_ult lhs rhs => show_arith "icmp ult" lhs rhs,
    icmp_ugt lhs rhs => show_arith "icmp ugt" lhs rhs,
    zext v from_ty to_ty => show_ext "zext" v from_ty to_ty,
    trunc v from_ty to_ty => show_ext "trunc" v from_ty to_ty,
    ptrtoint v from_ty to_ty => show_ext "ptrtoint" v from_ty to_ty,
    inttoptr v from_ty to_ty => show_ext "inttoptr" v from_ty to_ty,
    phi pairs => show_phi pairs,
    gep base indices => show_gep base indices,
    load ty ptr_ty ptr_ =>
        String.concat "load " (String.concat (show_llvm_type ty)
            (String.concat ", " (String.concat (show_llvm_type ptr_ty)
            (String.concat " " (show_llvm_value ptr_))))),
    bitcast v to_ty =>
        String.concat "bitcast " (String.concat (show_llvm_value v)
            (String.concat " to " (show_llvm_type to_ty))),
    alloc_closure entry arity env =>
        String.concat "call i64 @alloc_closure(i8* " (String.concat entry
            (String.concat ", i64 " (String.concat (I64.to_string arity)
            (String.concat ", i64 " (String.concat (I64.to_string (list_valu_len env)) ")"))))),
    alloc_constructor tag fields =>
        String.concat "call i64 @alloc_constructor(i64 " (String.concat (I64.to_string tag)
            (String.concat ", i64 " (String.concat (I64.to_string (list_valu_len fields)) ")"))),
    native_op op args =>
        let inner := String.concat "args=" (I64.to_string (list_valu_len args)) in
        String.concat "native_op(" (String.concat inner ")"),
}

#[partial]
def list_valu_len (xs : List LLVMValue) : I64 := match xs {
    List.empty => 0,
    List.cons x rest => 1 + list_valu_len rest,
}

#[partial]
def list_i64_len (xs : List I64) : I64 := match xs {
    List.empty => 0,
    List.cons x rest => 1 + list_i64_len rest,
}

#[partial]
def llvm_value_type (val : LLVMValue) : LLVMType := match val {
    int_ x => i64_,
    int32_ x => i32_,
    bool_ x => i1_,
    void_val => void,
    var_ x => i64_,
    parm_ x => i64_,
    global_ x => ptr i8_,
    fn_ref x => ptr i8_,
    call x ret_ty y z => ret_ty,
    add x y => i64_,
    sub x y => i64_,
    mul x y => i64_,
    sdiv x y => i64_,
    udiv x y => i64_,
    urem x y => i64_,
    icmp_eq x y => i1_,
    icmp_ne x y => i1_,
    icmp_slt x y => i1_,
    icmp_sgt x y => i1_,
    icmp_ult x y => i1_,
    icmp_ugt x y => i1_,
    zext x y to_ty => to_ty,
    trunc x y to_ty => to_ty,
    ptrtoint x y to_ty => to_ty,
    inttoptr x y to_ty => to_ty,
    // Previously hardcoded `i64_` regardless of what's actually merged
    // -- correct for an int-typed if/match merge, wrong for anything
    // pointer-typed (e.g. two different `String` literals: `if b then
    // "a" else "b"`). LLVM's verifier rejects a `phi i64 [ @str_0, ...
    // ]` outright ("global variable reference must have pointer type"),
    // since `@str_0` is `ptr`-typed, not `i64`. A well-formed phi's
    // incoming values always share one type, so the first pair's own
    // type (via the same `llvm_value_type` this arm belongs to) is
    // authoritative for all of them.
    phi pairs => phi_pairs_type pairs,
    gep x y => ptr i8_,
    load ty x y => ty,
    bitcast x to_ty => to_ty,
    alloc_closure x y z => ptr i8_,
    alloc_constructor x y => ptr i8_,
    native_op x y => i64_,
}

/// The real merge type of a phi node -- the first incoming pair's own
/// type (well-formed phis have all pairs agree; an empty pair list
/// can't arise from real codegen -- `compose_seq`/`splice_into_terminal_
/// block` only ever build a phi from at least two branches -- `i64_` is
/// just a harmless total-function fallback, never actually reached).
#[partial]
def phi_pairs_type (pairs : List PhiPair) : LLVMType := match pairs {
    List.empty => i64_,
    List.cons p _ => match p { PhiPair.mk val _ => llvm_value_type val },
}

#[partial]
def show_llvm_value_typed (val : LLVMValue) : String :=
    String.concat (show_llvm_type (llvm_value_type val))
        (String.concat " " (show_llvm_value val))

#[partial]
def show_call (fn_name : String) (ret_ty : LLVMType) (args : List LLVMValue) (tail : Bool) : String :=
    let prefix := if tail then "tail call " else "call " in
    let sig := String.concat prefix
        (String.concat (show_llvm_type ret_ty) (String.concat " @" fn_name)) in
    let args_str := show_args_typed args in
    String.concat sig (String.concat "(" (String.concat args_str ")"))

#[partial]
def show_arith (op : String) (lhs : LLVMValue) (rhs : LLVMValue) : String :=
    String.concat (String.concat op " i64 ") (String.concat (show_llvm_value lhs)
        (String.concat ", " (show_llvm_value rhs)))

#[partial]
def show_ext (op : String) (v : LLVMValue) (from_ty : LLVMType) (to_ty : LLVMType) : String :=
    String.concat (String.concat op " ") (String.concat (show_llvm_type from_ty)
        (String.concat " " (String.concat (show_llvm_value v)
        (String.concat " to " (show_llvm_type to_ty)))))

// Real merge type (`phi_pairs_type`), not hardcoded `i64` -- see
// `llvm_value_type`'s own `phi` arm doc comment for why (pointer-typed
// merges, e.g. `if b then "a" else "b"`, need `phi ptr` not `phi i64`).
#[partial]
def show_phi (pairs : List PhiPair) : String :=
    let inner := join_phi_pairs pairs in
    String.concat "phi " (String.concat (show_llvm_type (phi_pairs_type pairs)) (String.concat " " inner))

#[partial]
def join_phi_pairs (pairs : List PhiPair) : String :=
    List.intercalate ", " (List.map show_one_phi pairs)

#[partial]
def show_one_phi (p : PhiPair) : String := match p {
    PhiPair.mk val label =>
        String.concat "[" (String.concat (show_llvm_value val)
            (String.concat ", %" (String.concat label "]"))),
}

#[partial]
def show_gep (base : LLVMValue) (indices : List I64) : String :=
    let pre := String.concat "getelementptr " (String.concat (show_llvm_value_typed base)
        (String.concat ", " (I64.to_string (list_i64_len indices)))) in
    join_gep_indices pre indices

#[partial]
def join_gep_indices (pre : String) (indices : List I64) : String := match indices {
    List.empty => pre,
    List.cons i rest =>
        join_gep_indices
            (String.concat pre (String.concat ", i64 " (I64.to_string i)))
            rest,
}

/// `dbg_suffix` is a whole function's single `!dbg` annotation (e.g.
/// `", !dbg !7"`, or `""` when debug info is off or this function has
/// no known source location) -- v1 attaches the SAME suffix to every
/// instruction in a function rather than a distinct one per
/// instruction (see `DbgLoc`'s own doc comment). `comment` is a
/// source-text-only `;` line, not a real instruction, so it never
/// takes a `!dbg` suffix.
#[partial]
def show_instruction (instr : LLVMInstruction) (dbg_suffix : String) : String := match instr {
    assign target value =>
        String.concat "  %" (String.concat target (String.concat " = "
            (String.concat (show_llvm_value value) dbg_suffix))),
    branch cond then_label else_label =>
        String.concat "  br i1 " (String.concat (show_llvm_value cond)
            (String.concat ", label %" (String.concat then_label
            (String.concat ", label %" (String.concat else_label dbg_suffix))))),
    jump label =>
        String.concat "  br label %" (String.concat label dbg_suffix),
    store val ptr_ty ptr_ =>
        String.concat "  store " (String.concat (show_llvm_type (llvm_pointee ptr_ty))
            (String.concat " " (String.concat (show_llvm_value val)
            (String.concat ", " (String.concat (show_llvm_type ptr_ty)
            (String.concat " " (String.concat (show_llvm_value ptr_) dbg_suffix))))))),
    ret val => String.concat (show_ret_instr val) dbg_suffix,
    comment text =>
        String.concat "  ; " text,
}

// Every non-`void_val` `LLVMValue` renders the same way here (`"  ret "
// ++ show_llvm_value_typed val`) -- previously spelled out as 23
// identical match arms (one per variant), which made adding a new
// `LLVMValue` variant a maintenance trap (silently missing this list
// would be a non-exhaustive-match crash risk, per the real `fn_ref`
// repro noted below). Collapsed to the 2 cases that actually differ.
//
// A curried multi-param escaping lambda's OWN body (compile_db_lam_ir,
// lang/codegen/emit.mo) can itself be another Term.lam -- compiling
// THAT nested lambda returns a `fn_ref` (a direct reference to ITS
// own freshly-lifted function), which then becomes the OUTER
// lambda's own `ret` value: `(\x y z => x+y+z) 5 3 2`-shaped code
// hits this. A missing arm here once crashed the self-hosted
// interpreter itself ("non-exhaustive match: LLVMValue.fn_ref was
// constructed but not covered by this match") the moment `fn_ref`
// started being constructed by compile_db_lam_ir (see that def's own
// doc comment) -- confirmed via a real repro
// (test_compile_lambda_multi_arg, lang/codegen/test/e2e_typecheck_tests.mo).
// The wildcard fallback below covers every current and future variant
// the same way, so this can't recur.
#[partial]
def show_ret_instr (val : LLVMValue) : String := match val {
    void_val => "  ret void",
    _ => "  ret " ++ show_llvm_value_typed val,
}

#[partial]
def emit_block (block : LLVMBasicBlock) (dbg_suffix : String) : String := match block {
    LLVMBasicBlock.mk label instructions =>
        String.concat "\n" (String.concat label (String.concat ":" (emit_instrs instructions dbg_suffix))),
}

#[partial]
def emit_instrs (instructions : List LLVMInstruction) (dbg_suffix : String) : String := match instructions {
    List.empty => "",
    List.cons i rest =>
        String.concat "\n" (String.concat (show_instruction i dbg_suffix) (emit_instrs rest dbg_suffix)),
}

/// A function's own two `!dbg` attachment forms -- LLVM needs BOTH, not
/// just one, for `llc` to actually emit a real `.debug_line`/
/// `.debug_info`: `define_suffix` (` !dbg !N`, referencing the
/// `!DISubprogram` directly, spliced into the `define` line itself --
/// with NO attachment there, LLVM has no way to associate the
/// subprogram with this function's machine code at all, and silently
/// emits no debug sections whatsoever) and `instr_suffix` (`, !dbg !N`,
/// referencing the `!DILocation`, appended to every instruction --
/// see `DbgLoc`'s own doc comment for why every instruction in a
/// function shares the same one). Confirmed the hard way: an earlier
/// version attached only `instr_suffix` and produced a `.o` with zero
/// `.debug_line` entries despite `llc` exiting 0.
struct DbgFuncRefs {
    define_suffix : String,
    instr_suffix : String,
}

#[partial]
def empty_dbg_func_refs : DbgFuncRefs := { define_suffix := "", instr_suffix := "" }

/// `dbg_refs` is the module-wide `(function name -> DbgFuncRefs)` table
/// built once by `emit_debug_metadata` -- `List.empty` when debug info
/// is off, in which case `find_dbg_refs` always misses and every
/// function renders exactly as it did before this field existed.
#[partial]
def emit_function (func : LLVMFunction) (dbg_refs : List (Pair String DbgFuncRefs)) : String := match func {
    LLVMFunction.mk name params ret_ty blocks ghc_cc dbg_loc =>
        let cc := if ghc_cc then " cc 9" else "" in
        let prefix := String.concat "\n; Function: " (String.concat name "\n") in
        let sig := String.concat "define" (String.concat cc
            (String.concat " " (String.concat (show_llvm_type ret_ty)
            (String.concat " @" (String.concat name "("))))) in
        let refs := find_dbg_refs name dbg_refs in
        let sig2 := String.concat sig (String.concat (join_params params) (String.concat ")" (String.concat refs.define_suffix " {"))) in
        let body := emit_blocks blocks refs.instr_suffix in
        String.concat prefix (String.concat sig2 (String.concat body "\n}")),
}

/// Look up a function's `DbgFuncRefs` by name in the assoc list built
/// by `emit_debug_metadata` -- both fields `""` (no attachment at all)
/// on a miss, which covers both "debug info is off" (`dbg_refs` is
/// always `List.empty`) and "this function has no known source
/// location" uniformly.
#[partial]
def find_dbg_refs (name : String) (refs : List (Pair String DbgFuncRefs)) : DbgFuncRefs := match refs {
    List.empty => empty_dbg_func_refs,
    List.cons r rest =>
        match r {
            Pair.pair fname found => if String.beq fname name then found else find_dbg_refs name rest,
        },
}

#[partial]
def join_params (params : List ParamPair) : String :=
    List.intercalate ", " (List.map show_one_param params)

#[partial]
def show_one_param (p : ParamPair) : String := match p {
    ParamPair.mk param_name param_ty =>
        String.concat (show_llvm_type param_ty) (String.concat " %" param_name),
}

#[partial]
def emit_blocks (blocks : List LLVMBasicBlock) (dbg_suffix : String) : String := match blocks {
    List.empty => "",
    List.cons b rest => String.concat (emit_block b dbg_suffix) (emit_blocks rest dbg_suffix),
}

#[partial]
def emit_globals (gs : List LLVMGlobal) : String := match gs {
    List.empty => "",
    List.cons g rest => String.concat (show_llvm_global g) (String.concat "\n" (emit_globals rest)),
}

/// One hex digit (uppercase, matching LLVM's own convention) for a
/// nibble value 0-15. A plain if/else chain rather than a lookup-table
/// index, since there's no `U8`->`I64` cast native to index a String
/// with (the codebase's own established "if/else beats a fresh-list-
/// plus-closure scan" convention, `char_preds.mo`'s `is_digit`).
#[partial]
def llvm_hex_digit (n : U8) : String :=
    if U8.beq n 0u8 then "0"
    else if U8.beq n 1u8 then "1"
    else if U8.beq n 2u8 then "2"
    else if U8.beq n 3u8 then "3"
    else if U8.beq n 4u8 then "4"
    else if U8.beq n 5u8 then "5"
    else if U8.beq n 6u8 then "6"
    else if U8.beq n 7u8 then "7"
    else if U8.beq n 8u8 then "8"
    else if U8.beq n 9u8 then "9"
    else if U8.beq n 10u8 then "A"
    else if U8.beq n 11u8 then "B"
    else if U8.beq n 12u8 then "C"
    else if U8.beq n 13u8 then "D"
    else if U8.beq n 14u8 then "E"
    else "F"

/// LLVM's `\XX` constant-string escape needs `"`/`\` (the delimiter and
/// escape-introducer themselves) plus anything outside printable ASCII
/// escaped -- non-ASCII/control bytes pass through raw-but-unescaped
/// today, which is always syntactically valid LLVM IR (if less
/// readable) regardless of what UTF-8 text a String literal holds.
#[partial]
def llvm_byte_needs_escape (b : U8) : Bool :=
    U8.beq b 34u8 || U8.beq b 92u8 || U8.lt b 32u8 || U8.gt b 126u8

#[partial]
def llvm_escape_byte (b : U8) : String :=
    let hi := U8.div b 16u8 in
    let lo := U8.sub b (U8.mul hi 16u8) in
    String.concat "\\" (String.concat (llvm_hex_digit hi) (llvm_hex_digit lo))

/// Escape `s`'s raw bytes for embedding in an LLVM `c"..."` constant --
/// previously spliced in unescaped (`show_llvm_global` below), so any
/// string literal containing an embedded `"` or `\` produced
/// textually-invalid IR: LLVM's parser treats the first unescaped `"`
/// as the string's end, so the declared `[N x i8]` length (correctly
/// computed elsewhere as byte-count + 1) mismatched what actually got
/// parsed and `llc` rejected it outright. Confirmed via a live repro:
/// `lang/json.mo`'s own `{"name":"Alice"}` string literal produced
/// `@str_14 = constant [17 x i8] c"{"name":"Alice"}\00"`, which LLVM
/// parses as a 1-byte string, not 17.
///
/// Runs of bytes that don't need escaping are copied via a single
/// `String.slice` per run (mirroring the run-accumulation idiom used
/// elsewhere in this codebase for O(1)-amortized string building,
/// `AGENTS.md` item 12 Track 4) rather than paying for one
/// `String.concat` per byte -- only bytes that actually need escaping
/// cost an extra concat.
#[partial]
def llvm_escape_string_go (s : String) (idx : I64) (run_start : I64) (len : I64) (acc : String) : String :=
    if I64.beq idx len then
        String.concat acc (String.slice s run_start (len - run_start))
    else
        match (String.get s idx : Option U8) {
            Option.some b =>
                if llvm_byte_needs_escape b
                then
                    let with_run := String.concat acc (String.slice s run_start (idx - run_start)) in
                    let with_escape := String.concat with_run (llvm_escape_byte b) in
                    llvm_escape_string_go s (idx + 1) (idx + 1) len with_escape
                else llvm_escape_string_go s (idx + 1) run_start len acc,
            Option.none => acc,
        }

#[partial]
def llvm_escape_string (s : String) : String :=
    llvm_escape_string_go s 0 0 (String.length s) ""

#[partial]
def show_llvm_global (g : LLVMGlobal) : String := match g {
    LLVMGlobal.mk name value byte_len constant =>
        if constant
        then String.concat "@" (String.concat name
            (String.concat " = constant [" (String.concat (I64.to_string byte_len)
            (String.concat " x i8] c\"" (String.concat (llvm_escape_string value) "\\00\"")))))
        else String.concat "@" (String.concat name (String.concat " = global " value)),
}

#[partial]
def emit_decls (ds : List LLVMDeclaration) : String := match ds {
    List.empty => "",
    List.cons d rest => String.concat (show_llvm_decl d) (String.concat "\n" (emit_decls rest)),
}

#[partial]
def show_llvm_decl (d : LLVMDeclaration) : String := match d {
    LLVMDeclaration.mk name params ret_ty =>
        String.concat "declare " (String.concat ret_ty (String.concat " @"
            (String.concat name (String.concat "(" (String.concat (join_strs params) ")"))))),
}

#[partial]
def join_strs (xs : List String) : String :=
    List.intercalate ", " xs

#[partial]
def emit_functions (fs : List LLVMFunction) (dbg_refs : List (Pair String DbgFuncRefs)) : String := match fs {
    List.empty => "",
    List.cons f rest => String.concat (emit_function f dbg_refs) (String.concat "\n" (emit_functions rest dbg_refs)),
}

// --- DWARF debug info (v1: one location per top-level def) ---
// See plans/bootstrapping/debug-info.md. Every module that opts in gets
// exactly one `!DICompileUnit` + one `!DIFile` (one `.mo` file per
// compile) and every def with a known `dbg_loc` gets one
// `!DISubprogram` + one `!DILocation`, all sharing one empty
// `!DISubroutineType` (`!4`) and one empty retained-nodes list (`!5`) --
// a fixed, small shape that doesn't need a general metadata ADT the way
// a future per-instruction phase might.

/// '/' as U8 -- mirrors `lang/module.mo`'s own `slash_byte`/
/// `string_find_last_slash`. This file has no dependency on that
/// module, so a small local copy avoids introducing one just for this.
#[partial]
def ir_slash_byte : U8 := 47u8

#[partial]
def ir_find_last_slash (s : String) (idx : I64) : I64 :=
    if I64.lt 0 idx then
        match (String.get s (idx - 1) : Option U8) {
            Option.some b => if U8.beq b ir_slash_byte then idx - 1 else ir_find_last_slash s (idx - 1),
            Option.none => -1,
        }
    else -1

/// Split a file path into `Pair.pair directory filename` for
/// `!DIFile`. No slash in the path -- directory is `"."`.
#[partial]
def llvm_split_path (path : String) : Pair String String :=
    let last_slash := ir_find_last_slash path (String.length path) in
    if I64.lt last_slash 0 then
        Pair.pair "." path
    else
        Pair.pair (String.slice path 0 last_slash) (String.slice path (last_slash + 1) (String.length path - last_slash - 1))

/// The fixed module-level preamble: module flags (`!0`/`!1`), the
/// compile unit (`!2`), the file (`!3`), and the two nodes every
/// `!DISubprogram` shares in v1 -- an empty subroutine type (`!4`,
/// v1 doesn't describe parameter types) and an empty retained-nodes
/// list (`!5`).
#[partial]
def show_debug_preamble (filename : String) (directory : String) : String :=
    let flags := "!llvm.module.flags = !{!0, !1}\n!llvm.dbg.cu = !{!2}\n\n" in
    let f0 := "!0 = !{i32 2, !\"Dwarf Version\", i32 5}\n" in
    let f1 := "!1 = !{i32 2, !\"Debug Info Version\", i32 3}\n" in
    // `!DICompileUnit` has no `name:` field -- that's `!DIFile`'s own
    // field (below). Confirmed the hard way: `llc` rejected an earlier
    // version of this with "invalid field 'name'" pointed straight at
    // this node.
    let cu := "!2 = distinct !DICompileUnit(language: DW_LANG_C, file: !3, producer: \"monad 0.1.0\", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, debugInfoForProfiling: true)\n" in
    let file_head := String.concat "!3 = !DIFile(filename: \"" filename in
    let file_mid := String.concat file_head "\", directory: \"" in
    let file_ := String.concat (String.concat file_mid directory) "\")\n" in
    let sub_ty := "!4 = !DISubroutineType(types: !{})\n" in
    let retained := "!5 = !{}\n" in
    String.concat flags (String.concat f0 (String.concat f1 (String.concat cu (String.concat file_ (String.concat sub_ty retained)))))

#[partial]
def show_disubprogram (id : I64) (name : String) (line : I64) : String :=
    let line_s := I64.to_string line in
    let head := String.concat "!" (String.concat (I64.to_string id) " = distinct !DISubprogram(name: \"") in
    let with_name := String.concat head (String.concat name "\", linkageName: \"") in
    let with_name2 := String.concat with_name (String.concat name "\", scope: !3, file: !3, line: ") in
    let with_line := String.concat with_name2 (String.concat line_s ", type: !4, scopeLine: ") in
    String.concat with_line (String.concat line_s ", unit: !2, retainedNodes: !5)")

#[partial]
def show_dilocation (id : I64) (line : I64) (column : I64) (scope_ref : I64) : String :=
    let head := String.concat "!" (String.concat (I64.to_string id) " = !DILocation(line: ") in
    let with_line := String.concat head (String.concat (I64.to_string line) ", column: ") in
    let with_col := String.concat with_line (String.concat (I64.to_string column) ", scope: !") in
    String.concat with_col (String.concat (I64.to_string scope_ref) ")")

/// Walk `functions` once, in module order, assigning each function
/// with a known `dbg_loc` the next pair of free metadata IDs (`!N` =
/// its `!DISubprogram`, `!N+1` = its `!DILocation`) -- `next_id` starts
/// at 6 (0-5 are the fixed preamble from `show_debug_preamble`).
/// Returns BOTH the `(function name -> DbgFuncRefs)` assoc list AND the
/// rendered `!N = ...` text for every node just assigned, built
/// together in one pass so the two can never drift apart.
#[partial]
def build_dbg_refs (functions : List LLVMFunction) (next_id : I64) : Pair (List (Pair String DbgFuncRefs)) String := match functions {
    List.empty => Pair.pair List.empty "",
    List.cons f rest =>
        match f {
            LLVMFunction.mk name _ _ _ _ dbg_loc =>
                match dbg_loc {
                    Option.none => build_dbg_refs rest next_id,
                    Option.some loc =>
                        match loc {
                            DbgLoc.mk line column =>
                                let sp_ref := next_id in
                                let loc_ref := next_id + 1 in
                                let sp_text := show_disubprogram sp_ref name line in
                                let loc_text := show_dilocation loc_ref line column sp_ref in
                                match build_dbg_refs rest (next_id + 2) {
                                    Pair.pair rest_refs rest_text =>
                                        let define_suffix := String.concat " !dbg !" (I64.to_string sp_ref) in
                                        let instr_suffix := String.concat ", !dbg !" (I64.to_string loc_ref) in
                                        let refs : DbgFuncRefs := { define_suffix := define_suffix, instr_suffix := instr_suffix } in
                                        let this_text := String.concat sp_text (String.concat "\n" (String.concat loc_text "\n")) in
                                        Pair.pair
                                            (List.cons (Pair.pair name refs) rest_refs)
                                            (String.concat this_text rest_text),
                                },
                        },
                },
        },
}

/// Build both the per-function `DbgFuncRefs` table and the trailing
/// debug-metadata block for a module, together (see `build_dbg_refs`).
#[partial]
def emit_debug_metadata (source_path : String) (functions : List LLVMFunction) : Pair (List (Pair String DbgFuncRefs)) String :=
    match llvm_split_path source_path {
        Pair.pair directory filename =>
            let preamble := show_debug_preamble filename directory in
            match build_dbg_refs functions 6 {
                Pair.pair refs body => Pair.pair refs (String.concat preamble body),
            },
    }

#[partial]
def emit_module (module_ : LLVMModule) : String := match module_ {
    LLVMModule.mk target_triple globals functions declarations debug_source =>
        let h1 := String.concat "; ModuleID = 'monad'\ntarget triple = \"" (String.concat target_triple "\"\n\n") in
        let h2 := String.concat h1 "; === Type Definitions ===\n%Header = type { i64, i16, i16 }\n%Closure = type { %Header, i8*, i64, i64, [0 x i8*] }\n%Constructor = type { %Header, i64, i64, [0 x i8*] }\n%StringObj = type { %Header, i64, [0 x i8] }\n\n" in
        let h3 := match declarations {
            List.empty => h2,
            List.cons x y => String.concat h2 (String.concat "; === External Declarations ===\n"
                (String.concat (emit_decls declarations) "\n")),
        } in
        let h4 := match globals {
            List.empty => h3,
            List.cons x y => String.concat h3 (String.concat "; === Globals ===\n"
                (String.concat (emit_globals globals) "\n")),
        } in
        match debug_source {
            Option.none =>
                match functions {
                    List.empty => h4,
                    List.cons x y => String.concat h4 (String.concat "; === Functions ===\n"
                        (emit_functions functions List.empty)),
                },
            Option.some path =>
                match emit_debug_metadata path functions {
                    Pair.pair dbg_refs metadata_text =>
                        let h5 := match functions {
                            List.empty => h4,
                            List.cons x y => String.concat h4 (String.concat "; === Functions ===\n"
                                (emit_functions functions dbg_refs)),
                        } in
                        String.concat h5 (String.concat "\n; === Debug Info ===\n" metadata_text),
                },
        },
}

#[test]
def test_type_i64_display : Bool :=
    String.beq (show_llvm_type i64_) "i64"

#[test]
def test_type_void_display : Bool :=
    String.beq (show_llvm_type void) "void"

#[test]
def test_type_ptr_display : Bool :=
    String.beq (show_llvm_type (ptr i64_)) "i64*"

#[test]
def test_type_fn_display : Bool :=
    let fn_type := fn_ (List.cons i64_ (List.cons i64_ List.empty)) i64_ in
    String.beq (show_llvm_type fn_type) "i64 (i64, i64)"

#[test]
def test_type_struct_display : Bool :=
    String.beq (show_llvm_type (struct_ "Closure")) "%Closure"

#[test]
def test_value_int : Bool :=
    String.beq (show_llvm_value (int_ 42)) "42"

#[test]
def test_value_int_typed : Bool :=
    String.beq (show_llvm_value_typed (int_ 42)) "i64 42"

#[test]
def test_value_bool_true : Bool :=
    String.beq (show_llvm_value (bool_ true)) "true"

#[test]
def test_value_bool_false : Bool :=
    String.beq (show_llvm_value (bool_ false)) "false"

#[test]
def test_value_var : Bool :=
    String.beq (show_llvm_value (var_ "t0")) "%t0"

#[test]
def test_value_parm : Bool :=
    String.beq (show_llvm_value (parm_ 0)) "%p0"

#[test]
def test_value_global : Bool :=
    String.beq (show_llvm_value (global_ "str_0")) "@str_0"

#[test]
def test_value_add : Bool :=
    let val := add (parm_ 0) (parm_ 1) in
    String.beq (show_llvm_value val) "add i64 %p0, %p1"

#[test]
def test_value_call : Bool :=
    let val := call "add" i64_ (List.cons (parm_ 0) (List.cons (parm_ 1) List.empty)) false in
    String.beq (show_llvm_value val) "call i64 @add(i64 %p0, i64 %p1)"

#[test]
def test_value_icmp_eq : Bool :=
    let val := icmp_eq (parm_ 0) (parm_ 1) in
    String.beq (show_llvm_value val) "icmp eq i64 %p0, %p1"

#[test]
def test_instruction_assign : Bool :=
    let instr := assign "t0" (add (parm_ 0) (parm_ 1)) in
    String.beq (show_instruction instr "") "  %t0 = add i64 %p0, %p1"

#[test]
def test_instruction_ret_void : Bool :=
    String.beq (show_instruction (ret void_val) "") "  ret void"

#[test]
def test_instruction_ret_int : Bool :=
    String.beq (show_instruction (ret (int_ 42)) "") "  ret i64 42"

#[test]
def test_instruction_assign_with_dbg_suffix : Bool :=
    let instr := assign "t0" (add (parm_ 0) (parm_ 1)) in
    String.beq (show_instruction instr ", !dbg !7") "  %t0 = add i64 %p0, %p1, !dbg !7"

/// The `lang/runtime.mo` generated-IR natives' byte-access shape: an
/// i64-held address becomes a loadable pointer via `inttoptr`, then a
/// typed `load` reads through it (see both variants' own doc comments
/// above -- Strings are raw `char*`, so there is no header to offset).
#[test]
def test_value_inttoptr_load : Bool :=
    let cast := inttoptr (parm_ 0) i64_ (ptr i8_) in
    let ld := load i8_ (ptr i8_) cast in
    (String.beq (show_llvm_value cast) "inttoptr i64 %p0 to i8*"
        && String.beq (show_llvm_value ld) "load i8, i8* inttoptr i64 %p0 to i8*"
        && String.beq (show_llvm_value_typed ld) "i8 load i8, i8* inttoptr i64 %p0 to i8*")

/// The byte loop's actual shape: the inttoptr lands in an SSA temp
/// first, so the load's pointer operand is a plain i64-typed `var_` --
/// exactly why `load` carries an explicit `ptr_ty` (see the variant's
/// own doc comment).
#[test]
def test_value_load_typed_var : Bool :=
    let ld := load i8_ (ptr i8_) (var_ "q0") in
    String.beq (show_llvm_value ld) "load i8, i8* %q0"
        && String.beq (show_llvm_value_typed ld) "i8 load i8, i8* %q0"

/// A store's value renders at the POINTER's pointee type, not the
/// value's own convention type (an SSA var would otherwise render
/// `i64`, making every byte-pointer store ill-typed IR: `store i64 %b,
/// i8* %q`). The construction site's job is supplying a width-correct
/// value (a `trunc` temp for `i8*`); the renderer just keeps the
/// instruction internally consistent.
#[test]
def test_value_store : Bool :=
    let instr := store (var_ "b0") (ptr i8_) (var_ "q0") in
    let instr64 := store (var_ "b0") (ptr i64_) (var_ "q1") in
    String.beq (show_instruction instr "") "  store i8 %b0, i8* %q0"
        && String.beq (show_instruction instr64 "") "  store i64 %b0, i64* %q1"

#[test]
def test_value_urem_ult : Bool :=
    String.beq (show_llvm_value (urem (parm_ 0) (parm_ 1))) "urem i64 %p0, %p1"
        && String.beq (show_llvm_value (icmp_ult (parm_ 0) (parm_ 1))) "icmp ult i64 %p0, %p1"
        && String.beq (show_llvm_value (icmp_ugt (parm_ 0) (parm_ 1))) "icmp ugt i64 %p0, %p1"
        && String.beq (show_llvm_value (udiv (parm_ 0) (parm_ 1))) "udiv i64 %p0, %p1"
