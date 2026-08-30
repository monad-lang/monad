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
    icmp_eq (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_ne (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_slt (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_sgt (lhs : LLVMValue) (rhs : LLVMValue),
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
    phi (pairs : List PhiPair),
    gep (base : LLVMValue) (indices : List I64),
    load (ptr : LLVMValue),
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
    comment (text : String),
}

type LLVMBasicBlock {
    mk (label : String) (instructions : List LLVMInstruction),
}

type LLVMFunction {
    mk (name : String)
       (params : List ParamPair)
       (ret_ty : LLVMType)
       (blocks : List LLVMBasicBlock)
       (ghc_cc : Bool),
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
       (declarations : List LLVMDeclaration),
}

open LLVMType {fn_, i1_, i32_, i64_, i8_, ptr, struct_, void}
open LLVMValue {
  add, alloc_closure, alloc_constructor, bitcast, bool_, call, fn_ref, gep, global_,
  icmp_eq, icmp_ne, icmp_sgt, icmp_slt, int32_, int_, load, mul, native_op, parm_,
  phi, ptrtoint, sdiv, sub, trunc, var_, void_val, zext,
}
open LLVMInstruction {assign, branch, comment, jump, ret}
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

#[partial]
def show_llvm_type_fn (params : List LLVMType) (ret : LLVMType) : String :=
    let params_str := join_types params in
    String.concat (show_llvm_type ret) (String.concat " (" (String.concat params_str ")"))

#[partial]
def join_types (types : List LLVMType) : String := match types {
    List.empty => "",
    List.cons t rest => join_types_rest t rest,
}

#[partial]
def join_types_rest (t : LLVMType) (rest : List LLVMType) : String :=
    let shown := show_llvm_type t in
    match rest {
        List.empty => shown,
        List.cons x y => String.concat shown (String.concat ", " (join_types rest)),
    }

#[partial]
def show_args_typed (args : List LLVMValue) : String := match args {
    List.empty => "",
    List.cons a rest => show_args_typed_rest a rest,
}

#[partial]
def show_args_typed_rest (a : LLVMValue) (rest : List LLVMValue) : String :=
    let shown := show_llvm_value_typed a in
    match rest {
        List.empty => shown,
        List.cons x y => String.concat shown (String.concat ", " (show_args_typed rest)),
    }

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
    icmp_eq lhs rhs => show_arith "icmp eq" lhs rhs,
    icmp_ne lhs rhs => show_arith "icmp ne" lhs rhs,
    icmp_slt lhs rhs => show_arith "icmp slt" lhs rhs,
    icmp_sgt lhs rhs => show_arith "icmp sgt" lhs rhs,
    zext v from_ty to_ty => show_ext "zext" v from_ty to_ty,
    trunc v from_ty to_ty => show_ext "trunc" v from_ty to_ty,
    ptrtoint v from_ty to_ty => show_ext "ptrtoint" v from_ty to_ty,
    phi pairs => show_phi pairs,
    gep base indices => show_gep base indices,
    load ptr_ => String.concat "load " (show_llvm_value ptr_),
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
    icmp_eq x y => i1_,
    icmp_ne x y => i1_,
    icmp_slt x y => i1_,
    icmp_sgt x y => i1_,
    zext x y to_ty => to_ty,
    trunc x y to_ty => to_ty,
    ptrtoint x y to_ty => to_ty,
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
    load x => i64_,
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
def join_phi_pairs (pairs : List PhiPair) : String := match pairs {
    List.empty => "",
    List.cons p rest => join_phi_rest p rest,
}

#[partial]
def join_phi_rest (p : PhiPair) (rest : List PhiPair) : String :=
    let shown := show_one_phi p in
    match rest {
        List.empty => shown,
        List.cons x y => String.concat shown (String.concat ", " (join_phi_pairs rest)),
    }

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

#[partial]
def show_instruction (instr : LLVMInstruction) : String := match instr {
    assign target value =>
        String.concat "  %" (String.concat target (String.concat " = "
            (show_llvm_value value))),
    branch cond then_label else_label =>
        String.concat "  br i1 " (String.concat (show_llvm_value cond)
            (String.concat ", label %" (String.concat then_label
            (String.concat ", label %" else_label)))),
    jump label =>
        String.concat "  br label %" label,
    ret val => show_ret_instr val,
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
def emit_block (block : LLVMBasicBlock) : String := match block {
    LLVMBasicBlock.mk label instructions =>
        String.concat "\n" (String.concat label (String.concat ":" (emit_instrs instructions))),
}

#[partial]
def emit_instrs (instructions : List LLVMInstruction) : String := match instructions {
    List.empty => "",
    List.cons i rest =>
        String.concat "\n" (String.concat (show_instruction i) (emit_instrs rest)),
}

#[partial]
def emit_function (func : LLVMFunction) : String := match func {
    LLVMFunction.mk name params ret_ty blocks ghc_cc =>
        let cc := if ghc_cc then " cc 9" else "" in
        let prefix := String.concat "\n; Function: " (String.concat name "\n") in
        let sig := String.concat "define" (String.concat cc
            (String.concat " " (String.concat (show_llvm_type ret_ty)
            (String.concat " @" (String.concat name "("))))) in
        let sig2 := String.concat sig (String.concat (join_params params) ") {") in
        let body := emit_blocks blocks in
        String.concat prefix (String.concat sig2 (String.concat body "\n}")),
}

#[partial]
def join_params (params : List ParamPair) : String := match params {
    List.empty => "",
    List.cons p rest => join_params_rest p rest,
}

#[partial]
def join_params_rest (p : ParamPair) (rest : List ParamPair) : String :=
    let shown := show_one_param p in
    match rest {
        List.empty => shown,
        List.cons x y => String.concat shown (String.concat ", " (join_params rest)),
    }

#[partial]
def show_one_param (p : ParamPair) : String := match p {
    ParamPair.mk param_name param_ty =>
        String.concat (show_llvm_type param_ty) (String.concat " %" param_name),
}

#[partial]
def emit_blocks (blocks : List LLVMBasicBlock) : String := match blocks {
    List.empty => "",
    List.cons b rest => String.concat (emit_block b) (emit_blocks rest),
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
def join_strs (xs : List String) : String := match xs {
    List.empty => "",
    List.cons x rest => join_strs_rest x rest,
}

#[partial]
def join_strs_rest (x : String) (rest : List String) : String :=
    match rest {
        List.empty => x,
        List.cons y z => String.concat x (String.concat ", " (join_strs rest)),
    }

#[partial]
def emit_functions (fs : List LLVMFunction) : String := match fs {
    List.empty => "",
    List.cons f rest => String.concat (emit_function f) (String.concat "\n" (emit_functions rest)),
}

#[partial]
def emit_module (module_ : LLVMModule) : String := match module_ {
    LLVMModule.mk target_triple globals functions declarations =>
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
        let h5 := match functions {
            List.empty => h4,
            List.cons x y => String.concat h4 (String.concat "; === Functions ===\n"
                (emit_functions functions)),
        } in
        h5
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
    String.beq (show_instruction instr) "  %t0 = add i64 %p0, %p1"

#[test]
def test_instruction_ret_void : Bool :=
    String.beq (show_instruction (ret void_val)) "  ret void"

#[test]
def test_instruction_ret_int : Bool :=
    String.beq (show_instruction (ret (int_ 42))) "  ret i64 42"
