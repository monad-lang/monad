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

type LLVMValue {
    int_ (n : I64),
    int32_ (n : I32),
    bool_ (b : Bool),
    void_val,
    var_ (name : String),
    param_ (idx : I64),
    global_ (name : String),
    call (fn_name : String) (ret_ty : LLVMType) (args : List LLVMValue) (tail : Bool),
    add (lhs : LLVMValue) (rhs : LLVMValue),
    sub (lhs : LLVMValue) (rhs : LLVMValue),
    mul (lhs : LLVMValue) (rhs : LLVMValue),
    sdiv (lhs : LLVMValue) (rhs : LLVMValue),
    icmp_eq (lhs : LLVMValue) (rhs : LLVMValue),
    zext (val : LLVMValue) (from_ty : LLVMType) (to_ty : LLVMType),
    trunc (val : LLVMValue) (from_ty : LLVMType) (to_ty : LLVMType),
    phi (pairs : List PhiPair),
    gep (base : LLVMValue) (indices : List I64),
    load (ptr : LLVMValue),
    bitcast (val : LLVMValue) (to_ty : LLVMType),
    alloc_closure (entry : String) (arity : I64) (env : List LLVMValue),
    alloc_constructor (tag : I64) (fields : List LLVMValue),
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

open LLVMType
open LLVMValue
open LLVMInstruction
open ParamPair
open PhiPair

def show_bool (b : Bool) : String := match b {
    true => "true",
    false => "false",
}

def list_len (xs : List A) : I64 := match xs {
    List.empty => 0,
    List.cons _ rest => 1 + list_len rest,
}

def is_empty_list (xs : List A) : Bool := match xs {
    List.empty => true,
    List.cons _ _ => false,
}

def show_str_list (xs : List String) : String := match xs {
    List.empty => "",
    List.cons x List.empty => x,
    List.cons x rest => String.concat x (String.concat ", " (show_str_list rest)),
}

def show_llvm_global (g : LLVMGlobal) : String := match g {
    mk name value byte_len constant =>
        if constant
        then String.concat "@" (String.concat name
            (String.concat " = constant [" (String.concat (I64.to_string byte_len)
            (String.concat " x i8] c\"" (String.concat value "\\00\"")))))
        else String.concat "@" (String.concat name (String.concat " = global " value)),
}

def show_llvm_decl (d : LLVMDeclaration) : String := match d {
    mk name params ret_ty =>
        String.concat "declare " (String.concat ret_ty (String.concat " @"
            (String.concat name (String.concat "(" (String.concat (show_str_list params) ")"))))),
}

def show_llvm_type (ty : LLVMType) : String :=
    if is_void ty then "void"
    else if is_i1 ty then "i1"
    else if is_i8 ty then "i8"
    else if is_i32 ty then "i32"
    else if is_i64 ty then "i64"
    else if is_ptr ty then show_llvm_type_ptr ty
    else if is_fn ty then show_llvm_type_fn ty
    else if is_struct ty then show_llvm_type_struct ty
    else "unknown"

def is_void (ty : LLVMType) : Bool := match ty { void => true, _ => false }
def is_i1 (ty : LLVMType) : Bool := match ty { i1_ => true, _ => false }
def is_i8 (ty : LLVMType) : Bool := match ty { i8_ => true, _ => false }
def is_i32 (ty : LLVMType) : Bool := match ty { i32_ => true, _ => false }
def is_i64 (ty : LLVMType) : Bool := match ty { i64_ => true, _ => false }

def is_ptr (ty : LLVMType) : Bool := match ty {
    ptr _ => true,
    _ => false,
}

def is_fn (ty : LLVMType) : Bool := match ty {
    fn_ _ _ => true,
    _ => false,
}

def is_struct (ty : LLVMType) : Bool := match ty {
    struct_ _ => true,
    _ => false,
}

def show_llvm_type_ptr (ty : LLVMType) : String := match ty {
    ptr inner => String.concat (show_llvm_type inner) "*",
    _ => "",
}

def show_llvm_type_fn (ty : LLVMType) : String := match ty {
    fn_ params ret =>
        let params_str := show_type_list params in
        let inner := String.concat (show_llvm_type ret) (String.concat " (" params_str) in
        String.concat inner ")",
    _ => "",
}

def show_llvm_type_struct (ty : LLVMType) : String := match ty {
    struct_ name => String.concat "%" name,
    _ => "",
}

def show_type_list (types : List LLVMType) : String :=
    show_type_list_loop "" types

def show_type_list_loop (acc : String) (types : List LLVMType) : String := match types {
    List.empty => acc,
    List.cons t rest =>
        let shown := show_llvm_type t in
        show_type_list_loop (show_type_list_add acc shown rest) rest,
}

def show_type_list_add (acc : String) (shown : String) (rest : List LLVMType) : String :=
    if is_empty_list rest
    then shown
    else if String.beq acc ""
    then shown
    else String.concat acc (String.concat ", " shown)

def llvm_value_type (val : LLVMValue) : LLVMType :=
    if is_int_ val then i64_
    else if is_int32_ val then i32_
    else if is_bool_ val then i1_
    else if is_void_val val then void
    else if is_call val then llvm_value_type_call val
    else if is_zext val then llvm_value_type_zext val
    else if is_trunc val then llvm_value_type_trunc val
    else if is_bitcast val then llvm_value_type_bitcast val
    else i64_

def is_int_ (val : LLVMValue) : Bool := match val { int_ _ => true, _ => false }
def is_int32_ (val : LLVMValue) : Bool := match val { int32_ _ => true, _ => false }
def is_bool_ (val : LLVMValue) : Bool := match val { bool_ _ => true, _ => false }
def is_void_val (val : LLVMValue) : Bool := match val { void_val => true, _ => false }
def is_call (val : LLVMValue) : Bool := match val { call _ _ _ _ => true, _ => false }
def is_zext (val : LLVMValue) : Bool := match val { zext _ _ _ => true, _ => false }
def is_trunc (val : LLVMValue) : Bool := match val { trunc _ _ _ => true, _ => false }
def is_bitcast (val : LLVMValue) : Bool := match val { bitcast _ _ => true, _ => false }

def llvm_value_type_call (val : LLVMValue) : LLVMType := match val {
    call _ ret_ty _ _ => ret_ty,
    _ => i64_,
}

def llvm_value_type_zext (val : LLVMValue) : LLVMType := match val {
    zext _ _ to_ty => to_ty,
    _ => i64_,
}

def llvm_value_type_trunc (val : LLVMValue) : LLVMType := match val {
    trunc _ _ to_ty => to_ty,
    _ => i64_,
}

def llvm_value_type_bitcast (val : LLVMValue) : LLVMType := match val {
    bitcast _ to_ty => to_ty,
    _ => i64_,
}

def show_llvm_value (val : LLVMValue) : String :=
    if is_int_ val then show_llvm_value_int val
    else if is_int32_ val then show_llvm_value_int32 val
    else if is_bool_ val then show_llvm_value_bool val
    else if is_void_val val then "void"
    else if is_call val then show_llvm_value_call val
    else show_llvm_value_default val

def is_var_ (val : LLVMValue) : Bool := match val { var_ _ => true, _ => false }
def is_param_ (val : LLVMValue) : Bool := match val { param_ _ => true, _ => false }
def is_global_ (val : LLVMValue) : Bool := match val { global_ _ => true, _ => false }
def is_add (val : LLVMValue) : Bool := match val { add _ _ => true, _ => false }
def is_sub (val : LLVMValue) : Bool := match val { sub _ _ => true, _ => false }
def is_mul (val : LLVMValue) : Bool := match val { mul _ _ => true, _ => false }
def is_sdiv_ (val : LLVMValue) : Bool := match val { sdiv _ _ => true, _ => false }
def is_icmp_eq_ (val : LLVMValue) : Bool := match val { icmp_eq _ _ => true, _ => false }
def is_phi (val : LLVMValue) : Bool := match val { phi _ => true, _ => false }
def is_gep (val : LLVMValue) : Bool := match val { gep _ _ => true, _ => false }
def is_load_ (val : LLVMValue) : Bool := match val { load _ => true, _ => false }
def is_alloc_closure_ (val : LLVMValue) : Bool := match val { alloc_closure _ _ _ => true, _ => false }
def is_alloc_constructor_ (val : LLVMValue) : Bool := match val { alloc_constructor _ _ => true, _ => false }

def show_llvm_value_int (val : LLVMValue) : String := match val {
    int_ n => I64.to_string n,
    _ => "",
}

def show_llvm_value_int32 (val : LLVMValue) : String := match val {
    int32_ n => I32.to_string n,
    _ => "",
}

def show_llvm_value_bool (val : LLVMValue) : String := match val {
    bool_ b => show_bool b,
    _ => "",
}

def show_llvm_value_var (val : LLVMValue) : String := match val {
    var_ name => String.concat "%" name,
    _ => "",
}

def show_llvm_value_param (val : LLVMValue) : String := match val {
    param_ idx => String.concat "%p" (I64.to_string idx),
    _ => "",
}

def show_llvm_value_global (val : LLVMValue) : String := match val {
    global_ name => String.concat "@" name,
    _ => "",
}

def show_llvm_value_call (val : LLVMValue) : String := match val {
    call fn_name ret_ty args tail =>
        let prefix := if tail then "tail call " else "call " in
        let sig := String.concat prefix
            (String.concat (show_llvm_type ret_ty) (String.concat " @" fn_name)) in
        let args_str := show_args_typed args in
        String.concat sig (String.concat "(" (String.concat args_str ")")),
    _ => "",
}

def show_llvm_value_default (val : LLVMValue) : String :=
    if is_var_ val then show_llvm_value_var val
    else if is_param_ val then show_llvm_value_param val
    else if is_global_ val then show_llvm_value_global val
    else if is_add val then show_arith val "add"
    else if is_sub val then show_arith val "sub"
    else if is_mul val then show_arith val "mul"
    else if is_sdiv_ val then show_arith val "sdiv"
    else if is_icmp_eq_ val then show_arith val "icmp eq"
    else if is_zext val then show_ext_call val "zext"
    else if is_trunc val then show_ext_call val "trunc"
    else if is_phi val then show_phi_call val
    else if is_gep val then show_gep_call val
    else if is_load_ val then show_load_call val
    else if is_bitcast val then show_bitcast_call val
    else if is_alloc_closure_ val then show_alloc_closure_call val
    else if is_alloc_constructor_ val then show_alloc_constructor_call val
    else "unknown"

def show_arith (val : LLVMValue) (op : String) : String := match val {
    add lhs rhs => show_arith_parts op lhs rhs,
    sub lhs rhs => show_arith_parts op lhs rhs,
    mul lhs rhs => show_arith_parts op lhs rhs,
    sdiv lhs rhs => show_arith_parts op lhs rhs,
    icmp_eq lhs rhs => show_arith_parts op lhs rhs,
    _ => "",
}

def show_arith_parts (op : String) (lhs : LLVMValue) (rhs : LLVMValue) : String :=
    String.concat (String.concat op " i64 ") (String.concat (show_llvm_value lhs)
        (String.concat ", " (show_llvm_value rhs)))

def show_ext_call (val : LLVMValue) (op : String) : String := match val {
    zext v from_ty to_ty => show_ext_parts op v from_ty to_ty,
    trunc v from_ty to_ty => show_ext_parts op v from_ty to_ty,
    _ => "",
}

def show_ext_parts (op : String) (v : LLVMValue) (from_ty : LLVMType) (to_ty : LLVMType) : String :=
    String.concat (String.concat op " ") (String.concat (show_llvm_type from_ty)
        (String.concat " " (String.concat (show_llvm_value v)
        (String.concat " to " (show_llvm_type to_ty)))))

def show_phi_call (val : LLVMValue) : String := match val {
    phi pairs =>
        let inner := show_phi_pairs pairs in
        String.concat "phi i64 [" (String.concat inner "]"),
    _ => "",
}

def show_phi_pairs (pairs : List PhiPair) : String :=
    show_phi_pairs_loop "" pairs

def show_phi_pairs_loop (acc : String) (pairs : List PhiPair) : String := match pairs {
    List.empty => acc,
    List.cons p rest =>
        let shown := show_one_phi_pair p in
        let next := if is_empty_list rest then shown
            else String.concat shown ", " in
        show_phi_pairs_loop (String.concat acc next) rest,
}

def show_one_phi_pair (p : PhiPair) : String := match p {
    mk val label =>
        String.concat "[" (String.concat (show_llvm_value val)
            (String.concat ", %" (String.concat label "]"))),
}

def show_gep_call (val : LLVMValue) : String := match val {
    gep base indices =>
        let pre := String.concat "getelementptr " (String.concat (show_llvm_value_typed base)
            (String.concat ", " (I64.to_string (list_len indices)))) in
        show_gep_indices pre indices,
    _ => "",
}

def show_gep_indices (pre : String) (indices : List I64) : String := match indices {
    List.empty => pre,
    List.cons i rest =>
        show_gep_indices
            (String.concat pre (String.concat ", i64 " (I64.to_string i)))
            rest,
}

def show_load_call (val : LLVMValue) : String := match val {
    load ptr_ => String.concat "load " (show_llvm_value ptr_),
    _ => "",
}

def show_bitcast_call (val : LLVMValue) : String := match val {
    bitcast v to_ty =>
        String.concat "bitcast " (String.concat (show_llvm_value v)
            (String.concat " to " (show_llvm_type to_ty))),
    _ => "",
}

def show_alloc_closure_call (val : LLVMValue) : String := match val {
    alloc_closure entry arity env =>
        String.concat "alloc_closure(" (String.concat entry
            (String.concat ", " (String.concat (I64.to_string arity)
            (String.concat ", " (String.concat (I64.to_string (list_len env)) ")"))))),
    _ => "",
}

def show_alloc_constructor_call (val : LLVMValue) : String := match val {
    alloc_constructor tag fields =>
        String.concat "alloc_constructor("
            (String.concat (I64.to_string tag)
            (String.concat ", " (String.concat (I64.to_string (list_len fields)) ")"))),
    _ => "",
}

def show_llvm_value_typed (val : LLVMValue) : String :=
    String.concat (show_llvm_type (llvm_value_type val))
        (String.concat " " (show_llvm_value val))

def show_args_typed (args : List LLVMValue) : String :=
    show_args_typed_loop "" args

def show_args_typed_loop (acc : String) (args : List LLVMValue) : String := match args {
    List.empty => acc,
    List.cons a rest =>
        let shown := show_llvm_value_typed a in
        let next := if is_empty_list rest then shown
            else String.concat shown ", " in
        show_args_typed_loop (String.concat acc next) rest,
}

def show_instruction (instr : LLVMInstruction) : String := match instr {
    assign target value =>
        String.concat "  %" (String.concat target (String.concat " = "
            (show_llvm_value value))),
    branch cond then_label else_label =>
        String.concat "  br " (String.concat (show_llvm_value_typed cond)
            (String.concat " %" (String.concat then_label
            (String.concat ", %" else_label)))),
    jump label =>
        String.concat "  br label %" label,
    ret val => show_ret_instr val,
    comment text =>
        String.concat "  ; " text,
}

def show_ret_instr (val : LLVMValue) : String :=
    if is_void_val val then "  ret void"
    else String.concat "  ret " (show_llvm_value_typed val)

def emit_block (block : LLVMBasicBlock) : String := match block {
    mk label instructions =>
        let header := String.concat "\n" (String.concat label ":") in
        emit_instrs header instructions,
}

def emit_instrs (acc : String) (instructions : List LLVMInstruction) : String := match instructions {
    List.empty => acc,
    List.cons i rest =>
        emit_instrs (String.concat acc (String.concat "\n" (show_instruction i))) rest,
}

def show_one_param (p : ParamPair) : String := match p {
    mk param_name param_ty =>
        String.concat (show_llvm_type param_ty) (String.concat " %" param_name),
}

def show_fn_params_loop (acc : String) (params : List ParamPair) : String := match params {
    List.empty => acc,
    List.cons p rest =>
        let shown := show_one_param p in
        let next := if is_empty_list rest then shown
            else String.concat shown ", " in
        show_fn_params_loop (String.concat acc next) rest,
}

def show_fn_params (params : List ParamPair) : String :=
    show_fn_params_loop "" params

def emit_function (func : LLVMFunction) : String := match func {
    mk name params ret_ty blocks ghc_cc =>
        let cc := if ghc_cc then " cc 9" else "" in
        let header := String.concat "\n; Function: " (String.concat name "\n") in
        let sig := String.concat header (String.concat "define" (String.concat cc
            (String.concat " " (String.concat (show_llvm_type ret_ty)
            (String.concat " @" (String.concat name "(")))))) in
        let sig2 := String.concat sig (String.concat (show_fn_params params) ") {") in
        let body := emit_blocks_loop "" blocks in
        String.concat sig2 (String.concat body "\n}"),
}

def emit_blocks_loop (acc : String) (blocks : List LLVMBasicBlock) : String := match blocks {
    List.empty => acc,
    List.cons b rest =>
        emit_blocks_loop (String.concat acc (emit_block b)) rest,
}

def emit_decls_loop (acc : String) (ds : List LLVMDeclaration) : String := match ds {
    List.empty => acc,
    List.cons d rest =>
        emit_decls_loop (String.concat acc (String.concat (show_llvm_decl d) "\n")) rest,
}

def emit_globals_loop (acc : String) (gs : List LLVMGlobal) : String := match gs {
    List.empty => acc,
    List.cons g rest =>
        emit_globals_loop (String.concat acc (String.concat (show_llvm_global g) "\n")) rest,
}

def emit_functions_loop (acc : String) (fs : List LLVMFunction) : String := match fs {
    List.empty => acc,
    List.cons f rest =>
        emit_functions_loop (String.concat acc (String.concat (emit_function f) "\n")) rest,
}

def emit_module_parts (triple : String) (gs : List LLVMGlobal) (fs : List LLVMFunction) (ds : List LLVMDeclaration) : String :=
    let h1 := String.concat "; ModuleID = 'monad'\ntarget triple = \"" (String.concat triple "\"\n\n") in
    let h2 := String.concat h1 "; === Type Definitions ===\n%Header = type { i64, i16, i16 }\n%Closure = type { %Header, i8*, i64, i64, [0 x i8*] }\n%Constructor = type { %Header, i64, i64, [0 x i8*] }\n%StringObj = type { %Header, i64, [0 x i8] }\n\n" in
    let h3 := if is_empty_list ds then h2
        else String.concat h2 (String.concat "; === External Declarations ===\n"
            (String.concat (emit_decls_loop "" ds) "\n")) in
    let h4 := if is_empty_list gs then h3
        else String.concat h3 (String.concat "; === Globals ===\n"
            (String.concat (emit_globals_loop "" gs) "\n")) in
    let h5 := if is_empty_list fs then h4
        else String.concat h4 (String.concat "; === Functions ===\n"
            (emit_functions_loop "" fs)) in
    h5

def emit_module (module_ : LLVMModule) : String := match module_ {
    mk target_triple globals functions declarations =>
        emit_module_parts target_triple globals functions declarations,
}

def empty_module : LLVMModule := LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty List.empty List.empty

@[test]
def test_type_i64_display : Bool :=
    String.beq (show_llvm_type i64_) "i64"

@[test]
def test_type_void_display : Bool :=
    String.beq (show_llvm_type void) "void"

@[test]
def test_type_ptr_display : Bool :=
    String.beq (show_llvm_type (ptr i64_)) "i64*"

@[test]
def test_type_fn_display : Bool :=
    let fn_type := fn_ (List.cons i64_ (List.cons i64_ List.empty)) i64_ in
    String.beq (show_llvm_type fn_type) "i64 (i64, i64)"

@[test]
def test_type_struct_display : Bool :=
    String.beq (show_llvm_type (struct_ "Closure")) "%Closure"

@[test]
def test_value_int : Bool :=
    String.beq (show_llvm_value (int_ 42)) "42"

@[test]
def test_value_int_typed : Bool :=
    String.beq (show_llvm_value_typed (int_ 42)) "i64 42"

@[test]
def test_value_bool_true : Bool :=
    String.beq (show_llvm_value (bool_ true)) "true"

@[test]
def test_value_bool_false : Bool :=
    String.beq (show_llvm_value (bool_ false)) "false"

@[test]
def test_value_var : Bool :=
    String.beq (show_llvm_value (var_ "t0")) "%t0"

@[test]
def test_value_param : Bool :=
    String.beq (show_llvm_value (param_ 0)) "%p0"

@[test]
def test_value_global : Bool :=
    String.beq (show_llvm_value (global_ "str_0")) "@str_0"

@[test]
def test_value_add : Bool :=
    let val := add (param_ 0) (param_ 1) in
    String.beq (show_llvm_value val) "add i64 %p0, %p1"

@[test]
def test_value_call : Bool :=
    let val := call "add" i64_ (List.cons (param_ 0) (List.cons (param_ 1) List.empty)) false in
    String.beq (show_llvm_value val) "call i64 @add(i64 %p0, i64 %p1)"

@[test]
def test_value_icmp_eq : Bool :=
    let val := icmp_eq (param_ 0) (param_ 1) in
    String.beq (show_llvm_value val) "icmp eq i64 %p0, %p1"

@[test]
def test_instruction_assign : Bool :=
    let instr := assign "t0" (add (param_ 0) (param_ 1)) in
    String.beq (show_instruction instr) "  %t0 = add i64 %p0, %p1"

@[test]
def test_instruction_ret_void : Bool :=
    String.beq (show_instruction (ret void_val)) "  ret void"

@[test]
def test_instruction_ret_int : Bool :=
    String.beq (show_instruction (ret (int_ 42))) "  ret i64 42"

@[test]
def test_module_empty : Bool :=
    let output := emit_module empty_module in
    String.beq output "; ModuleID = 'monad'\ntarget triple = \"x86_64-unknown-linux-gnu\"\n\n; === Type Definitions ===\n%Header = type { i64, i16, i16 }\n%Closure = type { %Header, i8*, i64, i64, [0 x i8*] }\n%Constructor = type { %Header, i64, i64, [0 x i8*] }\n%StringObj = type { %Header, i64, [0 x i8] }\n\n"

def main : I64 := 42
