use std.list {intercalate}
// The leaf string-map module, NOT `lang.codegen.util` -- that file imports
// this one, so the dependency cannot run both ways. See `strmap.mo`'s head.
use lang.codegen.strmap {str_map_empty, str_map_insert, str_map_lookup}
// For the `HashMap` type itself, which the `loc_suffixes` field names.
use std.map {}

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
    /// Zero-width marker: "every instruction from here on belongs to this
    /// source position, until the next marker." Renders to nothing.
    ///
    /// A marker rather than a `dbg` FIELD on each variant, because a field
    /// changes six constructor arities and every positional match on them
    /// breaks at RUNTIME with `expected N constructor fields, got N+1`, no
    /// location. And a marker rather than a parallel `List (Option DbgLoc)`
    /// alongside `LLVMBasicBlock`'s instructions, because instruction lists
    /// are spliced, truncated and rewritten all over -- `compose_seq`,
    /// `drop_last_instr` (`lang/codegen/util.mo`), `unwrap_io_return_blocks`,
    /// and `apply_self_tco`, which rewrites whole blocks
    /// (`rewrite_parm_in_instrs`, `remove_assign_of`, `prune_phi_in_instrs`).
    /// A parallel list desynchronizes at every one of those, and the symptom
    /// is line numbers silently drifting by k with nothing to catch it. A
    /// marker travels WITH the stream, so it cannot desync.
    ///
    /// Two hazards, both `--debug`-only since nothing else constructs one:
    /// `ends_with_terminator` (`lang/codegen/emit.mo`) inspects the LAST
    /// element of a list and `drop_last_instr` drops it blindly, so a marker
    /// must never be emitted at the end of an instruction list. Held by
    /// construction -- markers are only ever prepended to a compiled
    /// sub-term's own instructions.
    loc_marker (loc : DbgLoc),
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
       (debug_source : Option String)
       /// One `(module path string, file path)` pair per loaded module,
       /// attributing each function's `!DISubprogram` to the `!DIFile` of
       /// the file it was actually written in. Keyed by the same
       /// `show_module_path` string a function name's `<module>::<def>`
       /// prefix uses, so a function's file is recoverable from its name
       /// alone. Empty means every function is attributed to the target
       /// file (`!3`) -- v1's behavior, and still the fallback for any
       /// name the table has no entry for.
       (debug_files : List (Pair String String)),
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

/// Every `@`-prefixed LLVM global/function reference this module emits,
/// in one place -- quoted only when the name actually needs it.
///
/// A symbol here is now the def's fully qualified source name
/// (`lang.typecheck.infer.foo`, `init.string.String.beq`), emitted
/// VERBATIM rather than mangled -- see `def_symbol_name`
/// (`lang.codegen.emit`) for why flattening `.` to `_` was itself a bug
/// (it made `String.a` and `String_a` the same symbol). LLVM's unquoted
/// identifier grammar already admits `.`, so those names need no
/// quoting at all and the emitted IR stays readable; quoting is the
/// fallback for anything outside that grammar (a primed `foo'`, say),
/// which would otherwise render as silently invalid IR.
#[partial]
def llvm_symbol_ref (name : String) : String :=
    if llvm_name_is_bare_safe name
    then String.concat "@" name
    else String.concat "@\"" (String.concat name "\"")

/// LLVM's unquoted identifier grammar, verbatim from the LangRef:
/// `[-a-zA-Z$._][-a-zA-Z$._0-9]*` -- note a digit is legal after the
/// first position but not in it, and the empty string is never safe.
#[partial]
def llvm_name_is_bare_safe (s : String) : Bool :=
    let n := String.length s in
    if I64.beq n 0 then false else llvm_name_is_bare_safe_go s 0 n

#[partial]
def llvm_name_is_bare_safe_go (s : String) (i : I64) (n : I64) : Bool :=
    if I64.beq i n then true
    else match String.get s i {
        Option.some b =>
            if llvm_name_byte_ok b (I64.beq i 0)
            then llvm_name_is_bare_safe_go s (I64.add i 1) n
            else false,
        Option.none => false,
    }

#[partial]
def llvm_name_byte_ok (b : U8) (first : Bool) : Bool :=
    if llvm_name_alpha_or_punct b then true
    else if first then false
    else llvm_name_digit b

/// `A`-`Z` (65-90), `a`-`z` (97-122), and the four punctuation bytes
/// LLVM allows anywhere in a bare identifier: `-` (45), `$` (36),
/// `.` (46), `_` (95).
#[partial]
def llvm_name_alpha_or_punct (b : U8) : Bool :=
    if U8.beq b 45u8 then true
    else if U8.beq b 36u8 then true
    else if U8.beq b 46u8 then true
    else if U8.beq b 95u8 then true
    else if U8.lt b 65u8 then false
    else if Bool.not (U8.gt b 90u8) then true
    else if U8.lt b 97u8 then false
    else Bool.not (U8.gt b 122u8)

/// `0`-`9` (48-57).
#[partial]
def llvm_name_digit (b : U8) : Bool :=
    if U8.lt b 48u8 then false
    else Bool.not (U8.gt b 57u8)

#[partial]
def show_llvm_value (val : LLVMValue) : String := match val {
    int_ n => I64.to_string n,
    int32_ n => I32.to_string n,
    bool_ b => show_bool b,
    void_val => "void",
    var_ name => String.concat "%" name,
    parm_ idx => String.concat "%p" (I64.to_string idx),
    global_ name => llvm_symbol_ref name,
    fn_ref name => llvm_symbol_ref name,
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
        (String.concat (show_llvm_type ret_ty) (String.concat " " (llvm_symbol_ref fn_name))) in
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
    // Unreachable: `emit_instrs` consumes a marker to update the current
    // suffix and never renders it. The arm exists because this match is
    // exhaustive, and a marker that DID reach here must produce no line
    // rather than a stray one.
    loc_marker _loc => "",
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

/// Each block starts back at the function's own location rather than
/// inheriting whatever the previous block ended on. Blocks are control-flow
/// joins -- an instruction's position should not depend on which predecessor
/// happened to be emitted before it in the text. Every construct that
/// creates blocks (`if`, `match`) marks its own position on entry anyway.
#[partial]
def emit_block (block : LLVMBasicBlock) (refs : DbgFuncRefs) : String := match block {
    LLVMBasicBlock.mk label instructions =>
        String.concat "\n" (String.concat label (String.concat ":" (emit_instrs instructions refs refs.instr_suffix))),
}

/// `current` is the suffix in force, updated by each `loc_marker` and
/// applied to every instruction after it -- the same "position holds until
/// changed" model an assembler's `.loc` directive uses.
#[partial]
def emit_instrs (instructions : List LLVMInstruction) (refs : DbgFuncRefs) (current : String) : String := match instructions {
    List.empty => "",
    List.cons i rest => emit_instrs_step i rest refs current,
}

/// Split out because a marker CONSUMES itself: it renders no line and
/// changes the suffix for everything after it, so it cannot be handled
/// inside the `String.concat` the other instructions take.
#[partial]
def emit_instrs_step (i : LLVMInstruction) (rest : List LLVMInstruction) (refs : DbgFuncRefs) (current : String) : String :=
    match i {
        LLVMInstruction.loc_marker loc => emit_instrs rest refs (dbg_suffix_for refs loc),
        _ => String.concat "\n" (String.concat (show_instruction i current) (emit_instrs rest refs current)),
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
    /// The function's own location -- what an instruction gets when no
    /// `loc_marker` has been seen yet, and the whole of v1's behaviour.
    instr_suffix : String,
    /// `"line:col"` -> `", !dbg !M"`, one entry per DISTINCT location
    /// marked inside this function. Interned per function, never shared
    /// across functions: a `!DILocation` carries `scope: !N` pointing at
    /// its own `!DISubprogram`, so the same line in two functions is two
    /// nodes. Deduping WITHIN a function is where the win is -- many
    /// instructions share one line.
    loc_suffixes : HashMap String String,
}

/// A location's key in `loc_suffixes`. Line and column together, because
/// two constructs on one line are two positions.
#[partial]
def dbg_loc_key (loc : DbgLoc) : String :=
    String.concat (I64.to_string loc.line) (String.concat ":" (I64.to_string loc.column))

/// The `!dbg` suffix for a marked location, falling back to the
/// function's own. A miss is not an error: a function may carry markers
/// for positions that were interned under a different function, and
/// attributing such an instruction to the enclosing function is better
/// than emitting no location at all.
#[partial]
def dbg_suffix_for (refs : DbgFuncRefs) (loc : DbgLoc) : String :=
    match str_map_lookup (dbg_loc_key loc) refs.loc_suffixes {
        Option.some suffix => suffix,
        Option.none => refs.instr_suffix,
    }

#[partial]
def empty_dbg_func_refs : DbgFuncRefs :=
    { define_suffix := "", instr_suffix := "", loc_suffixes := str_map_empty }

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
            (String.concat " " (String.concat (llvm_symbol_ref name) "("))))) in
        let refs := find_dbg_refs name dbg_refs in
        let sig2 := String.concat sig (String.concat (join_params params) (String.concat ")" (String.concat refs.define_suffix " {"))) in
        let body := emit_blocks blocks refs in
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

/// Collect the pieces, then join once.
///
/// `String.concat a (recurse rest)` recopies the whole accumulated tail
/// at every step, so rendering a module this way costs time quadratic in
/// its output -- 3.8 MB of it for the compiler itself.
/// `String.concat_list` measures and copies in one pass. The same rewrite applies to
/// `emit_globals`/`emit_decls`/`emit_functions` below.
#[partial]
def emit_blocks (blocks : List LLVMBasicBlock) (refs : DbgFuncRefs) : String :=
    String.concat_list (List.reverse (emit_blocks_go blocks refs List.empty))

#[partial]
def emit_blocks_go (blocks : List LLVMBasicBlock) (refs : DbgFuncRefs) (acc : List String) : List String := match blocks {
    List.empty => acc,
    List.cons b rest => emit_blocks_go rest refs (List.cons (emit_block b refs) acc),
}

#[partial]
def emit_globals (gs : List LLVMGlobal) : String :=
    String.concat_list (List.reverse (emit_globals_go gs List.empty))

#[partial]
def emit_globals_go (gs : List LLVMGlobal) (acc : List String) : List String := match gs {
    List.empty => acc,
    List.cons g rest => emit_globals_go rest (List.cons (String.concat (show_llvm_global g) "\n") acc),
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
        then String.concat (llvm_symbol_ref name)
            (String.concat " = constant [" (String.concat (I64.to_string byte_len)
            (String.concat " x i8] c\"" (String.concat (llvm_escape_string value) "\\00\""))))
        else String.concat (llvm_symbol_ref name) (String.concat " = global " value),
}

#[partial]
def emit_decls (ds : List LLVMDeclaration) : String :=
    String.concat_list (List.reverse (emit_decls_go ds List.empty))

#[partial]
def emit_decls_go (ds : List LLVMDeclaration) (acc : List String) : List String := match ds {
    List.empty => acc,
    List.cons d rest => emit_decls_go rest (List.cons (String.concat (show_llvm_decl d) "\n") acc),
}

#[partial]
def show_llvm_decl (d : LLVMDeclaration) : String := match d {
    LLVMDeclaration.mk name params ret_ty =>
        String.concat "declare " (String.concat ret_ty (String.concat " "
            (String.concat (llvm_symbol_ref name) (String.concat "(" (String.concat (join_strs params) ")"))))),
}

#[partial]
def join_strs (xs : List String) : String :=
    List.intercalate ", " xs

#[partial]
def emit_functions (fs : List LLVMFunction) (dbg_refs : List (Pair String DbgFuncRefs)) : String :=
    String.concat_list (List.reverse (emit_functions_go fs dbg_refs List.empty))

#[partial]
def emit_functions_go (fs : List LLVMFunction) (dbg_refs : List (Pair String DbgFuncRefs)) (acc : List String) : List String := match fs {
    List.empty => acc,
    List.cons f rest => emit_functions_go rest dbg_refs (List.cons (String.concat (emit_function f dbg_refs) "\n") acc),
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
def show_disubprogram (id : I64) (name : String) (line : I64) (file_ref : I64) : String :=
    let line_s := I64.to_string line in
    let head := String.concat "!" (String.concat (I64.to_string id) " = distinct !DISubprogram(name: \"") in
    let with_name := String.concat head (String.concat name "\", linkageName: \"") in
    let with_scope := String.concat with_name (String.concat name "\", scope: !3, file: !") in
    let with_file := String.concat with_scope (String.concat (I64.to_string file_ref) ", line: ") in
    let with_line := String.concat with_file (String.concat line_s ", type: !4, scopeLine: ") in
    String.concat with_line (String.concat line_s ", unit: !2, retainedNodes: !5)")

#[partial]
def show_dilocation (id : I64) (line : I64) (column : I64) (scope_ref : I64) : String :=
    let head := String.concat "!" (String.concat (I64.to_string id) " = !DILocation(line: ") in
    let with_line := String.concat head (String.concat (I64.to_string line) ", column: ") in
    let with_col := String.concat with_line (String.concat (I64.to_string column) ", scope: !") in
    String.concat with_col (String.concat (I64.to_string scope_ref) ")")

// --- Per-module !DIFile interning ------------------------------------
//
// One `!DIFile` per module, so a function's `!DISubprogram` names the
// file it was actually written in instead of the target's. A function
// name is `<module path>::<def name>` (module-qualified symbols,
// `lang/codegen/symbols.mo`), so the module a function came from is
// recoverable from its name alone: everything before the first `::`.

/// Find the first `::` -- mirrors `lang.codegen.symbols`'s own
/// `string_find_qualifier_sep`. This file deliberately imports nothing
/// from that module (see the strmap import note at the top), so a small
/// local copy avoids introducing one just for this, same as
/// `ir_slash_byte`/`ir_find_last_slash` above.
#[partial]
def ir_find_qualifier_sep (s : String) (i : I64) (n : I64) : I64 :=
    if I64.gt (i + 2) n then (0 - 1)
    else if String.beq (String.slice s i 2) "::" then i
    else ir_find_qualifier_sep s (i + 1) n

/// The module path prefix of a `<module>::<def>` symbol -- `none` when
/// the name was never qualified (a synthesized or already-flat one).
#[partial]
def module_prefix_of (fn_name : String) : Option String :=
    let idx := ir_find_qualifier_sep fn_name 0 (String.length fn_name) in
    if I64.beq idx (0 - 1) then Option.none else Option.some (String.slice fn_name 0 idx)

/// The `!DIFile` id for the module a function name came from. A miss --
/// a synthesized name, or a module the table has no pair for -- falls
/// back to the target file (`!3`), which is what v1 attributed every
/// function to.
#[partial]
def module_file_ref (file_refs : HashMap String I64) (fn_name : String) : I64 :=
    match module_prefix_of fn_name {
        Option.some prefix =>
            match str_map_lookup prefix file_refs {
                Option.some id => id,
                Option.none => 3,
            },
        Option.none => 3,
    }

/// The interned per-module file table: the lookup map, the rendered
/// `!N = !DIFile(...)` lines, and one past the last id assigned -- built
/// in one pass so the three cannot drift apart, same property as
/// `build_dbg_refs` below.
struct ModuleFileTable {
    refs : HashMap String I64,
    text : String,
    next_id : I64,
}

/// Intern one `!DIFile` per module: the target's own module maps to the
/// preamble's `!3` (its file path is `source_path`); every other module
/// takes the next free id, `6, 7, ...` in list order -- order is what
/// makes id assignment reproducible run to run.
#[partial]
def intern_module_files (files : List (Pair String String)) (source_path : String) : ModuleFileTable :=
    intern_module_files_go files source_path 6 str_map_empty ""

#[partial]
def intern_module_files_go (files : List (Pair String String)) (source_path : String) (next_id : I64) (refs : HashMap String I64) (text : String) : ModuleFileTable := match files {
    List.empty => { refs := refs, text := text, next_id := next_id },
    List.cons pair rest =>
        match pair {
            Pair.pair mod file_path =>
                if String.beq file_path source_path
                then intern_module_files_go rest source_path next_id (str_map_insert mod 3 refs) text
                else
                    match llvm_split_path file_path {
                        Pair.pair directory filename =>
                            let head := String.concat "!" (String.concat (I64.to_string next_id) " = !DIFile(filename: \"") in
                            let mid := String.concat head (String.concat filename "\", directory: \"") in
                            let line := String.concat (String.concat mid (String.concat directory "\")")) "\n" in
                            intern_module_files_go rest source_path (next_id + 1)
                                (str_map_insert mod next_id refs) (String.concat text line),
                    },
        },
}

// --- Per-function location interning ---------------------------------
//
// A `!DILocation` names its enclosing `!DISubprogram` in `scope:`, so a
// location CANNOT be shared between two functions -- the same source line
// reached from two functions is two metadata nodes. Interning is therefore
// per function, and the dedup that matters is within one: a function body
// typically marks a handful of distinct positions and then emits many
// instructions against each.

/// Distinct `loc_marker` locations in one function's blocks, in encounter
/// order. Order is what makes ID assignment reproducible run to run.
#[partial]
def collect_marker_locs (blocks : List LLVMBasicBlock) (acc : List DbgLoc) : List DbgLoc := match blocks {
    List.empty => acc,
    List.cons b rest => collect_marker_locs rest (collect_marker_locs_block b acc),
}

#[partial]
def collect_marker_locs_block (b : LLVMBasicBlock) (acc : List DbgLoc) : List DbgLoc := match b {
    LLVMBasicBlock.mk _label instrs => collect_marker_locs_instrs instrs acc,
}

#[partial]
def collect_marker_locs_instrs (instrs : List LLVMInstruction) (acc : List DbgLoc) : List DbgLoc := match instrs {
    List.empty => acc,
    List.cons i rest => collect_marker_locs_instrs rest (collect_marker_loc i acc),
}

#[partial]
def collect_marker_loc (i : LLVMInstruction) (acc : List DbgLoc) : List DbgLoc := match i {
    LLVMInstruction.loc_marker loc =>
        if dbg_loc_list_has acc loc then acc else List.append acc (List.cons loc List.empty),
    _ => acc,
}

#[partial]
def dbg_loc_list_has (locs : List DbgLoc) (loc : DbgLoc) : Bool := match locs {
    List.empty => false,
    List.cons l rest =>
        if String.beq (dbg_loc_key l) (dbg_loc_key loc) then true else dbg_loc_list_has rest loc,
}

/// Assign one `!DILocation` ID per distinct location, all scoped to this
/// function's own `!DISubprogram`, returning the suffix table and the
/// rendered nodes together -- same "built in one pass so they cannot
/// drift" property `build_dbg_refs` has.
#[partial]
def build_loc_nodes (locs : List DbgLoc) (next_id : I64) (scope_ref : I64) (acc : HashMap String String) : Pair (HashMap String String) String :=
    match locs {
        List.empty => Pair.pair acc "",
        List.cons loc rest =>
            let suffix := String.concat ", !dbg !" (I64.to_string next_id) in
            let text := String.concat (show_dilocation next_id loc.line loc.column scope_ref) "\n" in
            match build_loc_nodes rest (next_id + 1) scope_ref (str_map_insert (dbg_loc_key loc) suffix acc) {
                Pair.pair final_map rest_text => Pair.pair final_map (String.concat text rest_text),
            }
    }

/// Walk `functions` once, in module order, assigning each function
/// with a known `dbg_loc` the next free metadata IDs -- `!N` = its
/// `!DISubprogram`, `!N+1` = its own `!DILocation`, then one more per
/// distinct location marked inside it. `next_id` starts where
/// `intern_module_files` left off (6 when there are no dep-file pairs:
/// 0-5 are the fixed preamble from `show_debug_preamble`).
/// Returns BOTH the `(function name -> DbgFuncRefs)` assoc list AND the
/// rendered `!N = ...` text for every node just assigned, built
/// together in one pass so the two can never drift apart.
#[partial]
def build_dbg_refs (functions : List LLVMFunction) (next_id : I64) (file_refs : HashMap String I64) : Pair (List (Pair String DbgFuncRefs)) String := match functions {
    List.empty => Pair.pair List.empty "",
    List.cons f rest =>
        match f.dbg_loc {
            Option.none => build_dbg_refs rest next_id file_refs,
            Option.some loc => build_dbg_refs_one f loc rest next_id file_refs,
        },
}

#[partial]
def build_dbg_refs_one (f : LLVMFunction) (loc : DbgLoc) (rest : List LLVMFunction) (next_id : I64) (file_refs : HashMap String I64) : Pair (List (Pair String DbgFuncRefs)) String :=
    let sp_ref := next_id in
    let loc_ref := next_id + 1 in
    let marks := collect_marker_locs f.blocks List.empty in
    let sp_text := show_disubprogram sp_ref f.name loc.line (module_file_ref file_refs f.name) in
    let loc_text := show_dilocation loc_ref loc.line loc.column sp_ref in
    match build_loc_nodes marks (next_id + 2) sp_ref str_map_empty {
        Pair.pair loc_map marks_text =>
            match build_dbg_refs rest (next_id + 2 + List.length marks) file_refs {
                Pair.pair rest_refs rest_text =>
                    let refs : DbgFuncRefs := {
                        define_suffix := String.concat " !dbg !" (I64.to_string sp_ref),
                        instr_suffix := String.concat ", !dbg !" (I64.to_string loc_ref),
                        loc_suffixes := loc_map,
                    } in
                    let this_text := String.concat sp_text (String.concat "\n" (String.concat loc_text (String.concat "\n" marks_text))) in
                    Pair.pair
                        (List.cons (Pair.pair f.name refs) rest_refs)
                        (String.concat this_text rest_text),
            },
    }

/// Build both the per-function `DbgFuncRefs` table and the trailing
/// debug-metadata block for a module, together (see `build_dbg_refs`).
#[partial]
def emit_debug_metadata (source_path : String) (files : List (Pair String String)) (functions : List LLVMFunction) : Pair (List (Pair String DbgFuncRefs)) String :=
    match llvm_split_path source_path {
        Pair.pair directory filename =>
            let preamble := show_debug_preamble filename directory in
            match intern_module_files files source_path {
                { refs := file_refs, text := file_text, next_id := files_next } =>
                    match build_dbg_refs functions files_next file_refs {
                        Pair.pair refs body => Pair.pair refs (String.concat (String.concat preamble file_text) body),
                    },
            },
    }

#[partial]
def emit_module (module_ : LLVMModule) : String := match module_ {
    LLVMModule.mk target_triple globals functions declarations debug_source debug_files =>
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
                match emit_debug_metadata path debug_files functions {
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

// --- loc_marker: distinct locations within one function ---------------

/// A `loc_marker` renders to NOTHING and changes the suffix for everything
/// after it. This is the whole mechanism that lets one function's
/// instructions carry different lines, so it is asserted directly on the
/// emitted text rather than only through a full compile.
#[test]
def test_loc_marker_switches_suffix_mid_block : Bool :=
    let refs : DbgFuncRefs := {
        define_suffix := " !dbg !6",
        instr_suffix := ", !dbg !7",
        loc_suffixes := str_map_insert "9:5" ", !dbg !8" str_map_empty,
    } in
    let instrs : List LLVMInstruction :=
        [LLVMInstruction.assign "t0" (add (parm_ 0) (parm_ 1)),
         LLVMInstruction.loc_marker (DbgLoc.mk 9 5),
         LLVMInstruction.assign "t1" (add (parm_ 0) (parm_ 1))] in
    // `t0` before the marker takes the function's own location; `t1` after
    // it takes the marked one; the marker itself occupies no line.
    String.beq (emit_instrs instrs refs refs.instr_suffix)
        "\n  %t0 = add i64 %p0, %p1, !dbg !7\n  %t1 = add i64 %p0, %p1, !dbg !8"

/// An unknown marker falls back to the function's own location rather than
/// emitting none -- a wrong-but-enclosing line beats no line at all.
#[test]
def test_loc_marker_unknown_falls_back : Bool :=
    let refs : DbgFuncRefs := {
        define_suffix := " !dbg !6",
        instr_suffix := ", !dbg !7",
        loc_suffixes := str_map_empty,
    } in
    let instrs : List LLVMInstruction :=
        [LLVMInstruction.loc_marker (DbgLoc.mk 42 1),
         LLVMInstruction.assign "t0" (add (parm_ 0) (parm_ 1))] in
    String.beq (emit_instrs instrs refs refs.instr_suffix)
        "\n  %t0 = add i64 %p0, %p1, !dbg !7"

/// Distinct locations are interned once each, deduped by line:column, and
/// numbered after the function's own two nodes (subprogram, own location).
#[test]
def test_build_loc_nodes_dedups_and_numbers : Bool :=
    let marks : List DbgLoc := [DbgLoc.mk 5 9, DbgLoc.mk 6 5] in
    match build_loc_nodes marks 8 6 str_map_empty {
        Pair.pair m text =>
            match str_map_lookup "5:9" m {
                Option.some s1 =>
                    match str_map_lookup "6:5" m {
                        Option.some s2 =>
                            // Exact text, not a substring check: `check_contains`
                            // lives in `emit.mo`, which imports this file, and
                            // the full rendering is knowable anyway.
                            String.beq s1 ", !dbg !8" && String.beq s2 ", !dbg !9"
                                && String.beq text
                                     "!8 = !DILocation(line: 5, column: 9, scope: !6)\n!9 = !DILocation(line: 6, column: 5, scope: !6)\n",
                        Option.none => false,
                    },
                Option.none => false,
            },
    }

/// The same position marked twice is one metadata node, not two. Without
/// this, a loop body would mint a node per instruction.
#[test]
def test_collect_marker_locs_dedups : Bool :=
    let b : LLVMBasicBlock := LLVMBasicBlock.mk "entry"
        [LLVMInstruction.loc_marker (DbgLoc.mk 5 9),
         LLVMInstruction.assign "t0" (parm_ 0),
         LLVMInstruction.loc_marker (DbgLoc.mk 5 9),
         LLVMInstruction.loc_marker (DbgLoc.mk 6 5)] in
    I64.beq (List.length (collect_marker_locs [b] List.empty)) 2

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
