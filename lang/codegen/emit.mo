use lang.types
use lang.codegen.ir

type LocalBinding {
    mk (lname : Identifier) (lval : LLVMValue),
}

type CodegenCtx {
    ctx (locals : List LocalBinding) (next_temp : I64) (next_label : I64),
}

type CompileResult {
    ok (cr_ctx : CodegenCtx) (cr_val : LLVMValue),
}

type CtxStrPair {
    mk (cs_ctx : CodegenCtx) (cs_str : String),
}

def empty_bindings : List LocalBinding := List.empty

def empty_ctx : CodegenCtx := CodegenCtx.ctx empty_bindings 0 0

def fresh_temp (c : CodegenCtx) : CtxStrPair := match c {
    CodegenCtx.ctx locals nt nl =>
        let name := String.concat "t" (I64.to_string nt) in
        CtxStrPair.mk (CodegenCtx.ctx locals (nt + 1) nl) name,
}

def fresh_label (c : CodegenCtx) (prefix : String) : CtxStrPair := match c {
    CodegenCtx.ctx locals nt nl =>
        let name := String.concat prefix (String.concat "_" (I64.to_string nl)) in
        CtxStrPair.mk (CodegenCtx.ctx locals nt (nl + 1)) name,
}

def ctx_bind_local (c : CodegenCtx) (name : Identifier) (val : LLVMValue) : CodegenCtx := match c {
    CodegenCtx.ctx locals nt nl => CodegenCtx.ctx (List.cons (LocalBinding.mk name val) locals) nt nl,
}

def ctx_lookup_local (c : CodegenCtx) (name : Identifier) : Option LLVMValue := match c {
    CodegenCtx.ctx locals nt nl => lookup_binding locals name,
}

def lookup_binding (bindings : List LocalBinding) (name : Identifier) : Option LLVMValue := match bindings {
    List.empty => Option.none,
    List.cons b rest =>
        match b {
            LocalBinding.mk lname lval =>
                if identifier_eq lname name
                then Option.some lval
                else lookup_binding rest name,
        },
}

def identifier_eq (a : Identifier) (b : Identifier) : Bool := match a {
    Identifier.id as => match b {
        Identifier.id bs => String.beq as bs,
    },
}

def show_identifier (id : Identifier) : String := match id {
    Identifier.id s => s,
}

def compile_lit_ir (c : CodegenCtx) (lit_ : Literal) : CompileResult := match lit_ {
    Literal.num n suffix => CompileResult.ok c (LLVMValue.int_ n),
    Literal.str s => CompileResult.ok c (LLVMValue.global_ "str"),
    Literal.if_ cond then_ else_ => CompileResult.ok c LLVMValue.void_val,
    Literal.match_ scrutinee cases => CompileResult.ok c LLVMValue.void_val,
}

def compile_term_ir (c : CodegenCtx) (term_ : Term) : CompileResult := match term_ {
    Term.lit val => compile_lit_ir c val,
    Term.var name =>
        match name {
            NameRef.nid id =>
                match ctx_lookup_local c id {
                    Option.some val => CompileResult.ok c val,
                    Option.none => CompileResult.ok c (LLVMValue.var_ (show_identifier id)),
                },
            NameRef.nmp mp => CompileResult.ok c (LLVMValue.var_ "modpath"),
            NameRef.nop op => CompileResult.ok c (LLVMValue.var_ "operator"),
        },
    Term.lam param_ body =>
        let bname := param_name param_ in
        CompileResult.ok c (LLVMValue.parm_ 0),
    Term.app fun arg =>
        CompileResult.ok c (LLVMValue.var_ "app"),
    Term.ntv native => CompileResult.ok c LLVMValue.void_val,
    Term.con constr => CompileResult.ok c LLVMValue.void_val,
    Term.forall name typ body => CompileResult.ok c LLVMValue.void_val,
    Term.pi arg ret => CompileResult.ok c LLVMValue.void_val,
    Term.type_ universe => CompileResult.ok c LLVMValue.void_val,
    Term.hole => CompileResult.ok c LLVMValue.void_val,
}

def param_name (p : Param) : Identifier := match p {
    Param.mk name typ_ => name,
}

def empty_blocks : List LLVMBasicBlock := List.empty

def cons_block (b : LLVMBasicBlock) (bs : List LLVMBasicBlock) : List LLVMBasicBlock :=
    List.cons b bs

def collect_def_params (term_ : Term) : List Param := match term_ {
    Term.lam param body => List.cons param (collect_def_params body),
    Term.forall name typ body => collect_def_params body,
    Term.var name => List.empty,
    Term.app fun arg => List.empty,
    Term.lit val => List.empty,
    Term.ntv native => List.empty,
    Term.con constr => List.empty,
    Term.pi arg ret => List.empty,
    Term.type_ universe => List.empty,
    Term.hole => List.empty,
}

def strip_lams (term_ : Term) : Term := match term_ {
    Term.lam param body => strip_lams body,
    Term.forall name typ body => strip_lams body,
    Term.var name => term_,
    Term.app fun arg => term_,
    Term.lit val => term_,
    Term.ntv native => term_,
    Term.con constr => term_,
    Term.pi arg ret => term_,
    Term.type_ universe => term_,
    Term.hole => term_,
}

def module_path_to_str (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => join_identifiers ids,
}

def join_identifiers (ids : List Identifier) : String := match ids {
    List.empty => "",
    List.cons hd rest => join_ids_rest hd rest,
}

def join_ids_rest (hd : Identifier) (rest : List Identifier) : String :=
    match rest {
        List.empty => show_identifier hd,
        List.cons x y => String.concat (show_identifier hd) (String.concat "_" (join_identifiers rest)),
    }

def build_llvm_params (params : List Param) : List ParamPair := match params {
    List.empty => List.empty,
    List.cons p rest =>
        let pp := ParamPair.mk (param_name p) LLVMType.i64_ in
        List.cons pp (build_llvm_params rest),
}

def compile_def_ir (def_ : Def) : LLVMFunction := match def_ {
    Def.mk name typ term_ constraints attrs =>
        let fn_name := module_path_to_str name in
        let params := collect_def_params term_ in
        let llvm_params := build_llvm_params params in
        let entry_block := LLVMBasicBlock.mk "entry" List.empty in
        LLVMFunction.mk fn_name llvm_params LLVMType.i64_ (cons_block entry_block empty_blocks) true,
}

def empty_vals : List LLVMValue := List.empty

def cons_instr (i : LLVMInstruction) (is : List LLVMInstruction) : List LLVMInstruction :=
    List.cons i is

def compile_main_wrapper_ir : LLVMFunction :=
    let argc_pair := ParamPair.mk (Identifier.id "argc") LLVMType.i32_ in
    let argv_pair := ParamPair.mk (Identifier.id "argv") LLVMType.i64_ in
    let wrapper_params := cons_pair argc_pair (cons_pair argv_pair (empty_pairs)) in
    let call_instr := LLVMInstruction.assign "t0"
        (LLVMValue.call "main_monad" LLVMType.i64_ empty_vals false) in
    let trunc_instr := LLVMInstruction.assign "t1"
        (LLVMValue.trunc (LLVMValue.var_ "t0") LLVMType.i64_ LLVMType.i32_) in
    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ "t1") in
    let entry_instrs := cons_instr call_instr (cons_instr trunc_instr (cons_instr ret_instr List.empty)) in
    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
    LLVMFunction.mk "main" wrapper_params LLVMType.i32_ (cons_block entry_block empty_blocks) false

def empty_pairs : List ParamPair := List.empty

def cons_pair (p : ParamPair) (ps : List ParamPair) : List ParamPair :=
    List.cons p ps



@[test]
def test_collect_def_params_empty : Bool :=
    match (collect_def_params (Term.lit (Literal.num 42 NumSuffix.i64))) {
        List.empty => true,
        List.cons x y => false,
    }

@[test]
def test_collect_def_params_lam : Bool :=
    let id := Identifier.id "x" in
    let param := Param.mk id (Term.type_ 1) in
    match (collect_def_params (Term.lam param (Term.var (NameRef.nid id)))) {
        List.empty => false,
        List.cons p rest =>
            match rest {
                List.empty => true,
                List.cons x y => false,
            },
    }

@[test]
def test_compile_main_wrapper_has_name : Bool :=
    match (compile_main_wrapper_ir) {
        LLVMFunction.mk name params ret_ty blocks ghc_cc =>
            String.beq name "main",
    }

@[test]
def test_compile_main_wrapper_returns_i32 : Bool :=
    match (compile_main_wrapper_ir) {
        LLVMFunction.mk name params ret_ty blocks ghc_cc =>
            match ret_ty {
                LLVMType.i32_ => true,
                LLVMType.void => false,
                LLVMType.i1_ => false,
                LLVMType.i8_ => false,
                LLVMType.i64_ => false,
                LLVMType.ptr x => false,
                LLVMType.fn_ x y => false,
                LLVMType.struct_ x => false,
            },
    }

@[test]
def test_compile_def_ir_strips_lams : Bool :=
    let id := Identifier.id "x" in
    let param := Param.mk id (Term.type_ 1) in
    let def_ := Def.mk (ModulePath.mp (List.cons (Identifier.id "f") List.empty)) (Term.type_ 1) (Term.lam param (Term.var (NameRef.nid id))) List.empty List.empty in
    match (compile_def_ir def_) {
        LLVMFunction.mk name params ret_ty blocks ghc_cc =>
            String.beq name "f",
    }

def main : I64 := 42
