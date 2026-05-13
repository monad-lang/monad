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


@[test]
def test_compile_lit_num : Bool :=
    match (compile_term_ir empty_ctx (Term.lit (Literal.num 42 NumSuffix.i64))) {
        CompileResult.ok c val =>
            String.beq (lang.codegen.ir.show_llvm_value val) "42",
    }

@[test]
def test_compile_var_unbound : Bool :=
    let id := Identifier.id "x" in
    match (compile_term_ir empty_ctx (Term.var (NameRef.nid id))) {
        CompileResult.ok c val =>
            String.beq (lang.codegen.ir.show_llvm_value val) "%x",
    }

@[test]
def test_compile_var_bound : Bool :=
    let id := Identifier.id "x" in
    let ctx := ctx_bind_local empty_ctx id (LLVMValue.int_ 10) in
    match (compile_term_ir ctx (Term.var (NameRef.nid id))) {
        CompileResult.ok c val =>
            String.beq (lang.codegen.ir.show_llvm_value val) "10",
    }

@[test]
def test_compile_lam : Bool :=
    let id := Identifier.id "x" in
    let param := Param.mk id (Term.type_ 1) in
    match (compile_term_ir empty_ctx (Term.lam param (Term.var (NameRef.nid id)))) {
        CompileResult.ok c val =>
            String.beq (lang.codegen.ir.show_llvm_value val) "%p0",
    }

@[test]
def test_compile_app : Bool :=
    let id := Identifier.id "f" in
    let arg := Term.lit (Literal.num 1 NumSuffix.i64) in
    match (compile_term_ir empty_ctx (Term.app (Term.var (NameRef.nid id)) arg)) {
        CompileResult.ok c val =>
            let s := lang.codegen.ir.show_llvm_value val in
            String.beq (String.slice s 0 1) "%",
    }

def main : I64 := 42
