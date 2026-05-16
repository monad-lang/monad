use lang.types
use lang.codegen.ir

open LLVMType
open LLVMValue

type LocalBinding {
    mk (lname : Identifier) (lval : LLVMValue),
}

type CodegenCtx {
    ctx (locals : List LocalBinding) (next_temp : I64) (next_label : I64),
}

type CompileResult {
    ok (cr_ctx : CodegenCtx) (cr_instrs : List LLVMInstruction) (cr_val : LLVMValue) (cr_blocks : List LLVMBasicBlock),
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

def show_name_ref (name : NameRef) : String := match name {
    NameRef.nid id => show_identifier id,
    NameRef.nmp mp => module_path_to_str mp,
    NameRef.nop op => show_operator op,
}

def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

def cons_val (v : LLVMValue) (vs : List LLVMValue) : List LLVMValue := List.cons v vs

def lookup_native (name : String) : Option NativeOp :=
    if String.beq name "I64_add" then Option.some NativeOp.op_add
    else if String.beq name "I64_sub" then Option.some NativeOp.op_sub
    else if String.beq name "I64_mul" then Option.some NativeOp.op_mul
    else if String.beq name "I64_div" then Option.some NativeOp.op_sdiv
    else if String.beq name "I64_eq" then Option.some NativeOp.op_eq
    else Option.none

def compile_native_val (op : NativeOp) (lhs : LLVMValue) (rhs : LLVMValue) : LLVMValue :=
    match op {
        NativeOp.op_add => LLVMValue.add lhs rhs,
        NativeOp.op_sub => LLVMValue.sub lhs rhs,
        NativeOp.op_mul => LLVMValue.mul lhs rhs,
        NativeOp.op_sdiv => LLVMValue.sdiv lhs rhs,
        NativeOp.op_eq => LLVMValue.icmp_eq lhs rhs,
    }

def extract_lit_val (term_ : Term) : Option I64 := match term_ {
    Term.lit val => extract_lit_val_inner val,
    Term.forall a b c => Option.none,
    Term.pi a b => Option.none,
    Term.var a => Option.none,
    Term.lam a b => Option.none,
    Term.app a b => Option.none,
    Term.ntv a => Option.none,
    Term.con a => Option.none,
    Term.type_ a => Option.none,
    Term.hole => Option.none,
}

def extract_lit_val_inner (lit_ : Literal) : Option I64 := match lit_ {
    Literal.num n suffix => Option.some n,
    Literal.str s => Option.none,
    Literal.if_ a b c => Option.none,
    Literal.match_ a b => Option.none,
}

def try_compile_native (op : NativeOp) (arg2 : Term) (arg : Term) : Option LLVMValue :=
    match extract_lit_val arg2 {
        Option.some n1 =>
            match extract_lit_val arg {
                Option.some n2 =>
                    Option.some (compile_native_val op (LLVMValue.int_ n1) (LLVMValue.int_ n2)),
                Option.none => Option.none,
            },
        Option.none => Option.none,
    }

def try_compile_body (term_ : Term) : Option LLVMValue := match term_ {
    Term.app fun arg =>
        match fun {
            Term.app fun2 arg2 =>
                match fun2 {
                    Term.var name_ref =>
                        let var_name := show_name_ref name_ref in
                        match lookup_native var_name {
                            Option.some op => try_compile_native op arg2 arg,
                            Option.none => Option.none,
                        },
                    Term.lit val => Option.none,
                    Term.app fun3 arg3 => Option.none,
                    Term.forall a b c => Option.none,
                    Term.pi a b => Option.none,
                    Term.lam a b => Option.none,
                    Term.ntv a => Option.none,
                    Term.con a => Option.none,
                    Term.type_ a => Option.none,
                    Term.hole => Option.none,
                },
            Term.lit val => Option.none,
            Term.forall a b c => Option.none,
            Term.pi a b => Option.none,
            Term.var a => Option.none,
            Term.lam a b => Option.none,
            Term.ntv a => Option.none,
            Term.con a => Option.none,
            Term.type_ a => Option.none,
            Term.hole => Option.none,
        },
    Term.lit val =>
        match val {
            Literal.num n suffix => Option.some (LLVMValue.int_ n),
            Literal.str s => Option.none,
            Literal.if_ a b c => Option.none,
            Literal.match_ a b => Option.none,
        },
    Term.forall a b c => Option.none,
    Term.pi a b => Option.none,
    Term.var a => Option.none,
    Term.lam a b => Option.none,
    Term.ntv a => Option.none,
    Term.con a => Option.none,
    Term.type_ a => Option.none,
    Term.hole => Option.none,
}

def empty_instrs : List LLVMInstruction := List.empty

def compile_body_instrs (body : Term) : List LLVMInstruction :=
    match try_compile_body body {
        Option.some val =>
            if is_llvm_constant val
            then cons_instr (LLVMInstruction.ret val) empty_instrs
            else cons_instr (LLVMInstruction.assign "t0" val) (cons_instr (LLVMInstruction.ret (LLVMValue.var_ "t0")) empty_instrs),
        Option.none => empty_instrs,
    }

/// Check if an LLVMValue is a constant that can be used directly
/// in an instruction (no need for assignment).
def is_llvm_constant (val : LLVMValue) : Bool := match val {
    LLVMValue.int_ n => true,
    LLVMValue.int32_ n => true,
    LLVMValue.bool_ b => true,
    LLVMValue.void_val => true,
    LLVMValue.global_ name => true,
    LLVMValue.var_ name => true,
    LLVMValue.parm_ idx => true,
    LLVMValue.call fn_name ret_ty args tail => false,
    LLVMValue.add lhs rhs => false,
    LLVMValue.sub lhs rhs => false,
    LLVMValue.mul lhs rhs => false,
    LLVMValue.sdiv lhs rhs => false,
    LLVMValue.icmp_eq lhs rhs => false,
    LLVMValue.zext val from_ty to_ty => false,
    LLVMValue.trunc val from_ty to_ty => false,
    LLVMValue.phi pairs => false,
    LLVMValue.gep base indices => false,
    LLVMValue.load ptr => false,
    LLVMValue.bitcast val ty => false,
    LLVMValue.alloc_closure entry arity env_size => false,
    LLVMValue.alloc_constructor tag field_count => false,
}

def compile_lit_ir (c : CodegenCtx) (lit_ : Literal) : CompileResult := match lit_ {
    Literal.num n suffix => CompileResult.ok c empty_instrs (LLVMValue.int_ n) empty_blocks,
    Literal.str s => CompileResult.ok c empty_instrs (LLVMValue.global_ "str") empty_blocks,
    Literal.if_ cond then_ else_ => compile_if_ir c cond then_ else_,
    Literal.match_ scrutinee cases => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks,
}

type IfLabels {
    mk (ctx_after : CodegenCtx) (then_label : String) (else_label : String) (merge_label : String),
}

def compile_if_ir (c : CodegenCtx) (cond : Term) (then_ : Term) (else_ : Term) : CompileResult :=
    match compile_term_ir c cond {
        CompileResult.ok ctx_cond cond_instrs cond_val blocks_cond =>
            match build_if_labels ctx_cond {
                IfLabels.mk ctx_branches then_label else_label merge_label =>
                    let branch_instr := LLVMInstruction.branch cond_val then_label else_label in
                    let entry_instrs := cons_instr branch_instr cond_instrs in
                    build_if_blocks ctx_branches then_label else_label merge_label then_ else_ entry_instrs blocks_cond,
            },
    }

def build_if_labels (c : CodegenCtx) : IfLabels :=
    match fresh_label c "then" {
        CtxStrPair.mk ctx1 tl =>
            match fresh_label ctx1 "else" {
                CtxStrPair.mk ctx2 el =>
                    match fresh_label ctx2 "merge" {
                        CtxStrPair.mk ctx3 ml =>
                            IfLabels.mk ctx3 tl el ml,
                    },
            },
    }

def build_branch_block (label : String) (merge_label : String) (instrs : List LLVMInstruction) : LLVMBasicBlock :=
    LLVMBasicBlock.mk label (cons_instr (LLVMInstruction.jump merge_label) instrs)

def build_if_blocks (ctx : CodegenCtx) (then_label : String) (else_label : String) (merge_label : String) (then_ : Term) (else_ : Term) (entry_instrs : List LLVMInstruction) (entry_blocks : List LLVMBasicBlock) : CompileResult :=
    match compile_term_ir ctx then_ {
        CompileResult.ok ctx_then then_instrs then_val blocks_then =>
            let then_block := build_branch_block then_label merge_label then_instrs in
            match compile_term_ir ctx_then else_ {
                CompileResult.ok ctx_else else_instrs else_val blocks_else =>
                    let else_block := build_branch_block else_label merge_label else_instrs in
                    build_merge_result ctx_else merge_label then_val then_label else_val else_label entry_instrs entry_blocks blocks_then blocks_else then_block else_block,
            },
    }

def build_merge_result (ctx_else : CodegenCtx) (merge_label : String) (then_val : LLVMValue) (then_label : String) (else_val : LLVMValue) (else_label : String) (entry_instrs : List LLVMInstruction) (entry_blocks : List LLVMBasicBlock) (blocks_then : List LLVMBasicBlock) (blocks_else : List LLVMBasicBlock) (then_block : LLVMBasicBlock) (else_block : LLVMBasicBlock) : CompileResult :=
    match fresh_temp ctx_else {
        CtxStrPair.mk ctx_phi phi_temp =>
            let phi_val := LLVMValue.phi (cons_phi (PhiPair.mk then_val then_label) (cons_phi (PhiPair.mk else_val else_label) empty_phis)) in
            let phi_instr := LLVMInstruction.assign phi_temp phi_val in
            let ret_instr := LLVMInstruction.ret (LLVMValue.var_ phi_temp) in
            let merge_instrs := cons_instr phi_instr (cons_instr ret_instr empty_instrs) in
            let merge_block := LLVMBasicBlock.mk merge_label merge_instrs in
            let all_blocks := cons_block then_block (cons_block else_block (cons_block merge_block (append_blocks (append_blocks entry_blocks blocks_then) blocks_else))) in
            CompileResult.ok ctx_phi entry_instrs (LLVMValue.var_ phi_temp) all_blocks,
    }

def compile_term_ir (c : CodegenCtx) (term_ : Term) : CompileResult := match term_ {
    Term.lit val => compile_lit_ir c val,
    Term.var name =>
        match name {
            NameRef.nid id =>
                match ctx_lookup_local c id {
                    Option.some val => CompileResult.ok c empty_instrs val empty_blocks,
                    Option.none => CompileResult.ok c empty_instrs (LLVMValue.var_ (show_identifier id)) empty_blocks,
                },
            NameRef.nmp mp => CompileResult.ok c empty_instrs (LLVMValue.var_ (module_path_to_str mp)) empty_blocks,
            NameRef.nop op => CompileResult.ok c empty_instrs (LLVMValue.var_ (show_operator op)) empty_blocks,
        },
    Term.lam param_ body => CompileResult.ok c empty_instrs (LLVMValue.parm_ 0) empty_blocks,
    Term.app fun arg => compile_app_ir c fun arg,
    Term.ntv native => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks,
    Term.con constr => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks,
    Term.forall name typ body => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks,
    Term.pi arg ret => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks,
    Term.type_ universe => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks,
    Term.hole => CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks,
}

def compile_app_ir (c : CodegenCtx) (fun : Term) (arg : Term) : CompileResult :=
    match try_compile_inline_native c fun arg {
        Option.some result => result,
        Option.none => compile_general_call c fun arg,
    }

def try_compile_inline_native (c : CodegenCtx) (fun : Term) (arg : Term) : Option CompileResult :=
    match fun {
        Term.app fun2 arg2 =>
            match fun2 {
                Term.var name_ref =>
                    let var_name := show_name_ref name_ref in
                    match lookup_native var_name {
                        Option.some op =>
                            Option.some (compile_native_app c op arg2 arg),
                        Option.none => Option.none,
                    },
                Term.lit val => Option.none,
                Term.app fun3 arg3 => Option.none,
                Term.forall a b c => Option.none,
                Term.pi a b => Option.none,
                Term.lam a b => Option.none,
                Term.ntv a => Option.none,
                Term.con a => Option.none,
                Term.type_ a => Option.none,
                Term.hole => Option.none,
            },
        Term.lit val => Option.none,
        Term.var a => Option.none,
        Term.lam a b => Option.none,
        Term.ntv a => Option.none,
        Term.con a => Option.none,
        Term.forall a b c => Option.none,
        Term.pi a b => Option.none,
        Term.type_ a => Option.none,
        Term.hole => Option.none,
    }

def compile_native_app (c : CodegenCtx) (op : NativeOp) (arg2 : Term) (arg : Term) : CompileResult :=
    match compile_term_ir c arg2 {
        CompileResult.ok ctx2 instrs2 val2 _ =>
            match compile_term_ir ctx2 arg {
                CompileResult.ok ctx1 instrs1 val1 _ =>
                    let combined := append_instrs instrs2 instrs1 in
                    match extract_lit_from_val val2 {
                        Option.some n1 =>
                            match extract_lit_from_val val1 {
                                Option.some n2 =>
                                    CompileResult.ok ctx1 combined (compile_native_val op (LLVMValue.int_ n1) (LLVMValue.int_ n2)) empty_blocks,
                                Option.none =>
                                    emit_arith_instr ctx1 op val2 val1 combined,
                            },
                        Option.none =>
                            emit_arith_instr ctx1 op val2 val1 combined,
                    },
            },
    }

def emit_arith_instr (c : CodegenCtx) (op : NativeOp) (lhs : LLVMValue) (rhs : LLVMValue) (instrs : List LLVMInstruction) : CompileResult :=
    match fresh_temp c {
        CtxStrPair.mk new_ctx temp =>
            let arith_val := compile_native_val op lhs rhs in
            let arith_instr := LLVMInstruction.assign temp arith_val in
            CompileResult.ok new_ctx (cons_instr arith_instr instrs) (LLVMValue.var_ temp) empty_blocks,
    }

def extract_lit_from_val (val : LLVMValue) : Option I64 := match val {
    LLVMValue.int_ n => Option.some n,
    LLVMValue.int32_ n => Option.none,
    LLVMValue.bool_ b => Option.none,
    LLVMValue.void_val => Option.none,
    LLVMValue.var_ name => Option.none,
    LLVMValue.parm_ idx => Option.none,
    LLVMValue.global_ name => Option.none,
    LLVMValue.call fn_name ret_ty args tail => Option.none,
    LLVMValue.add lhs rhs => Option.none,
    LLVMValue.sub lhs rhs => Option.none,
    LLVMValue.mul lhs rhs => Option.none,
    LLVMValue.sdiv lhs rhs => Option.none,
    LLVMValue.icmp_eq lhs rhs => Option.none,
    LLVMValue.zext val from_ty to_ty => Option.none,
    LLVMValue.trunc val from_ty to_ty => Option.none,
    LLVMValue.phi pairs => Option.none,
    LLVMValue.gep base indices => Option.none,
    LLVMValue.load ptr => Option.none,
    LLVMValue.bitcast val ty => Option.none,
    LLVMValue.alloc_closure entry arity env_size => Option.none,
    LLVMValue.alloc_constructor tag field_count => Option.none,
    LLVMValue.native_op op args => Option.none,
}

def compile_general_call (c : CodegenCtx) (fun : Term) (arg : Term) : CompileResult :=
    match compile_term_ir c fun {
        CompileResult.ok ctx_f instrs_f val_f _ =>
            match compile_term_ir ctx_f arg {
                CompileResult.ok ctx_a instrs_a val_a _ =>
                    let combined := append_instrs instrs_f instrs_a in
                    match val_f {
                        LLVMValue.var_ name =>
                            compile_direct_call ctx_a name val_a combined,
                        LLVMValue.parm_ idx =>
                            compile_indirect_call ctx_a val_a combined,
                        LLVMValue.int_ n => compile_call_stub ctx_a combined,
                        LLVMValue.int32_ n => compile_call_stub ctx_a combined,
                        LLVMValue.bool_ b => compile_call_stub ctx_a combined,
                        LLVMValue.void_val => compile_call_stub ctx_a combined,
                        LLVMValue.global_ name => compile_call_stub ctx_a combined,
                        LLVMValue.call fn_name ret_ty args tail => compile_call_stub ctx_a combined,
                        LLVMValue.add lhs rhs => compile_call_stub ctx_a combined,
                        LLVMValue.sub lhs rhs => compile_call_stub ctx_a combined,
                        LLVMValue.mul lhs rhs => compile_call_stub ctx_a combined,
                        LLVMValue.sdiv lhs rhs => compile_call_stub ctx_a combined,
                        LLVMValue.icmp_eq lhs rhs => compile_call_stub ctx_a combined,
                        LLVMValue.zext val from_ty to_ty => compile_call_stub ctx_a combined,
                        LLVMValue.trunc val from_ty to_ty => compile_call_stub ctx_a combined,
                        LLVMValue.phi pairs => compile_call_stub ctx_a combined,
                        LLVMValue.gep base indices => compile_call_stub ctx_a combined,
                        LLVMValue.load ptr => compile_call_stub ctx_a combined,
                        LLVMValue.bitcast val ty => compile_call_stub ctx_a combined,
                        LLVMValue.alloc_closure entry arity env_size => compile_call_stub ctx_a combined,
                        LLVMValue.alloc_constructor tag field_count => compile_call_stub ctx_a combined,
                        LLVMValue.native_op op args => compile_call_stub ctx_a combined,
                    },
            },
    }

def compile_direct_call (ctx_a : CodegenCtx) (name : String) (val_a : LLVMValue) (combined : List LLVMInstruction) : CompileResult :=
    match fresh_temp ctx_a {
        CtxStrPair.mk ctx_t temp =>
            let call_instr := LLVMInstruction.assign temp
                (LLVMValue.call name LLVMType.i64_ (cons_val val_a empty_vals) false) in
            CompileResult.ok ctx_t (cons_instr call_instr combined) (LLVMValue.var_ temp) empty_blocks,
    }

def compile_indirect_call (ctx_a : CodegenCtx) (val_a : LLVMValue) (combined : List LLVMInstruction) : CompileResult :=
    match fresh_temp ctx_a {
        CtxStrPair.mk ctx_t temp =>
            let call_instr := LLVMInstruction.assign temp
                (LLVMValue.call "apply_fun" LLVMType.i64_ (cons_val val_a empty_vals) false) in
            CompileResult.ok ctx_t (cons_instr call_instr combined) (LLVMValue.var_ temp) empty_blocks,
    }

def compile_call_stub (ctx_a : CodegenCtx) (combined : List LLVMInstruction) : CompileResult :=
    match fresh_temp ctx_a {
        CtxStrPair.mk ctx_t temp =>
            CompileResult.ok ctx_t combined (LLVMValue.var_ temp) empty_blocks,
    }

def append_instrs (a : List LLVMInstruction) (b : List LLVMInstruction) : List LLVMInstruction := match a {
    List.empty => b,
    List.cons hd tl => cons_instr hd (append_instrs tl b),
}

def append_blocks (a : List LLVMBasicBlock) (b : List LLVMBasicBlock) : List LLVMBasicBlock := match a {
    List.empty => b,
    List.cons hd tl => cons_block hd (append_blocks tl b),
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
        let pp := ParamPair.mk (show_identifier (param_name p)) LLVMType.i64_ in
        List.cons pp (build_llvm_params rest),
}

def compile_def_ir (def_ : Def) : LLVMFunction := match def_ {
    Def.mk name typ term_ constraints attrs =>
        let fn_name := module_path_to_str name in
        let params := collect_def_params term_ in
        let llvm_params := build_llvm_params params in
        let body := strip_lams term_ in
        let c0 := bind_params_in_ctx empty_ctx params in
        match compile_term_ir c0 body {
            CompileResult.ok ctx_r instrs_r val_r blocks_r =>
                let entry_instrs := append_instrs instrs_r (cons_instr (LLVMInstruction.ret val_r) empty_instrs) in
                let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                let all_blocks := append_blocks (cons_block entry_block empty_blocks) blocks_r in
                LLVMFunction.mk fn_name llvm_params LLVMType.i64_ all_blocks true,
        },
}

def bind_params_in_ctx (c : CodegenCtx) (params : List Param) : CodegenCtx :=
    bind_params_with_idx c params 0

def bind_params_with_idx (c : CodegenCtx) (params : List Param) (idx : I64) : CodegenCtx := match params {
    List.empty => c,
    List.cons p rest =>
        let c1 := ctx_bind_local c (param_name p) (LLVMValue.parm_ idx) in
        bind_params_with_idx c1 rest (idx + 1),
}

def empty_vals : List LLVMValue := List.empty

def empty_phis : List PhiPair := List.empty

def cons_phi (p : PhiPair) (ps : List PhiPair) : List PhiPair := List.cons p ps

def cons_instr (i : LLVMInstruction) (is : List LLVMInstruction) : List LLVMInstruction :=
    List.cons i is

def compile_main_wrapper_ir : LLVMFunction :=
    let argc_pair := ParamPair.mk "argc" LLVMType.i32_ in
    let argv_pair := ParamPair.mk "argv" LLVMType.i64_ in
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

def empty_strs : List String := List.empty

def cons_str (s : String) (ss : List String) : List String := List.cons s ss

def mk_decl (name : String) (params : List String) (ret_ty : String) : LLVMDeclaration :=
    LLVMDeclaration.mk name params ret_ty

def empty_decls : List LLVMDeclaration := List.empty

def cons_decl (d : LLVMDeclaration) (ds : List LLVMDeclaration) : List LLVMDeclaration :=
    List.cons d ds

def runtime_declarations : List LLVMDeclaration :=
    let d1 := mk_decl "monad_alloc" (cons_str "i64" empty_strs) "i8*" in
    let d2 := mk_decl "monad_retain" (cons_str "i8*" empty_strs) "void" in
    let d3 := mk_decl "monad_release" (cons_str "i8*" empty_strs) "void" in
    let d4 := mk_decl "monad_print_str" (cons_str "i8*" empty_strs) "void" in
    let d5 := mk_decl "alloc_closure" (cons_str "i8*" (cons_str "i64" (cons_str "i64" empty_strs))) "%Closure*" in
    let d6 := mk_decl "alloc_constructor" (cons_str "i64" (cons_str "i64" empty_strs)) "%Constructor*" in
    let d7 := mk_decl "alloc_string" (cons_str "i8*" (cons_str "i64" empty_strs)) "%StringObj*" in
    cons_decl d1 (cons_decl d2 (cons_decl d3 (cons_decl d4 (cons_decl d5 (cons_decl d6 (cons_decl d7 empty_decls))))))

def empty_funcs : List LLVMFunction := List.empty

def cons_func (f : LLVMFunction) (fs : List LLVMFunction) : List LLVMFunction :=
    List.cons f fs

def empty_globals_list : List LLVMGlobal := List.empty

def compile_decls_ir (defs : List Def) : LLVMModule :=
    let compiled := compile_def_list defs in
    let funcs := ren_main_and_wrap compiled in
    LLVMModule.mk "x86_64-unknown-linux-gnu" empty_globals_list funcs runtime_declarations

def compile_def_list (defs : List Def) : List LLVMFunction := match defs {
    List.empty => empty_funcs,
    List.cons d rest =>
        cons_func (compile_def_ir d) (compile_def_list rest),
}

def ren_main_and_wrap (funcs : List LLVMFunction) : List LLVMFunction :=
    rename_main funcs

def has_main (funcs : List LLVMFunction) : Bool := match funcs {
    List.empty => false,
    List.cons f rest =>
        match f {
            LLVMFunction.mk name params ret_ty blocks ghc_cc =>
                if String.beq name "main" then true
                else has_main rest,
        },
}

def rename_main (funcs : List LLVMFunction) : List LLVMFunction := match funcs {
    List.empty => empty_funcs,
    List.cons f rest =>
        match f {
            LLVMFunction.mk name params ret_ty blocks ghc_cc =>
                let renamed := if String.beq name "main"
                    then LLVMFunction.mk "main_monad" params ret_ty blocks ghc_cc
                    else f in
                cons_func renamed (rename_main rest),
        },
}


@[test]
def test_runtime_decls_not_empty : Bool :=
    match runtime_declarations {
        List.empty => false,
        List.cons x y => true,
    }

def empty_defs : List Def := List.empty

@[test]
def test_compile_decls_ir_runtime : Bool :=
    match (compile_decls_ir empty_defs) {
        LLVMModule.mk triple globals funcs decls =>
            match decls {
                List.empty => false,
                List.cons x y => true,
            },
    }

@[test]
def test_compile_decls_ir_has_def : Bool :=
    let id := Identifier.id "x" in
    let param := Param.mk id (Term.type_ 1) in
    let def_ := Def.mk (ModulePath.mp (List.cons (Identifier.id "test") List.empty)) (Term.type_ 1) (Term.lam param (Term.var (NameRef.nid id))) List.empty List.empty in
    match (compile_decls_ir (List.cons def_ empty_defs)) {
        LLVMModule.mk triple globals funcs decls =>
            match funcs {
                List.empty => false,
                List.cons x y => true,
            },
    }

@[test]
def test_module_emit_has_header : Bool :=
    let text := lang.codegen.ir.emit_module (compile_decls_ir empty_defs) in
    let prefix := String.slice text 0 12 in
    String.beq prefix "; ModuleID ="

@[test]
def test_empty_decls_module : Bool :=
    match (compile_decls_ir empty_defs) {
        LLVMModule.mk triple globals funcs decls =>
            String.beq triple "x86_64-unknown-linux-gnu",
    }

@[test]
def test_native_add_inlined : Bool :=
    match try_compile_body (Term.app (Term.app (Term.var (NameRef.nid (Identifier.id "I64_add"))) (Term.lit (Literal.num 1 NumSuffix.i64))) (Term.lit (Literal.num 2 NumSuffix.i64))) {
        Option.some val => true,
        Option.none => false,
    }

@[test]
def test_literal_body_compiles : Bool :=
    match try_compile_body (Term.lit (Literal.num 42 NumSuffix.i64)) {
        Option.some val => true,
        Option.none => false,
    }

@[test]
def test_arithmetic_full_chain : Bool :=
    let id := Identifier.id "test" in
    let nid := NameRef.nid (Identifier.id "I64_add") in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let var_ := Term.var nid in
    let app1 := Term.app var_ one in
    let body := Term.app app1 two in
    let def_ := Def.mk (ModulePath.mp (List.cons id List.empty)) (Term.type_ 1) body List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "add i64"

@[test]
def test_sub_inlined : Bool :=
    match try_compile_body (Term.app (Term.app (Term.var (NameRef.nid (Identifier.id "I64_sub"))) (Term.lit (Literal.num 5 NumSuffix.i64))) (Term.lit (Literal.num 3 NumSuffix.i64))) {
        Option.some val => true,
        Option.none => false,
    }

@[test]
def test_mul_inlined : Bool :=
    match try_compile_body (Term.app (Term.app (Term.var (NameRef.nid (Identifier.id "I64_mul"))) (Term.lit (Literal.num 3 NumSuffix.i64))) (Term.lit (Literal.num 4 NumSuffix.i64))) {
        Option.some val => true,
        Option.none => false,
    }

@[test]
def test_div_inlined : Bool :=
    match try_compile_body (Term.app (Term.app (Term.var (NameRef.nid (Identifier.id "I64_div"))) (Term.lit (Literal.num 8 NumSuffix.i64))) (Term.lit (Literal.num 2 NumSuffix.i64))) {
        Option.some val => true,
        Option.none => false,
    }

@[test]
def test_eq_inlined : Bool :=
    match try_compile_body (Term.app (Term.app (Term.var (NameRef.nid (Identifier.id "I64_eq"))) (Term.lit (Literal.num 1 NumSuffix.i64))) (Term.lit (Literal.num 1 NumSuffix.i64))) {
        Option.some val => true,
        Option.none => false,
    }

@[test]
def test_sub_full_chain : Bool :=
    let id := Identifier.id "test" in
    let nid := NameRef.nid (Identifier.id "I64_sub") in
    let one := Term.lit (Literal.num 5 NumSuffix.i64) in
    let two := Term.lit (Literal.num 3 NumSuffix.i64) in
    let var_ := Term.var nid in
    let app1 := Term.app var_ one in
    let body := Term.app app1 two in
    let def_ := Def.mk (ModulePath.mp (List.cons id List.empty)) (Term.type_ 1) body List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "sub i64"

@[test]
def test_mul_full_chain : Bool :=
    let id := Identifier.id "test" in
    let nid := NameRef.nid (Identifier.id "I64_mul") in
    let one := Term.lit (Literal.num 3 NumSuffix.i64) in
    let two := Term.lit (Literal.num 4 NumSuffix.i64) in
    let var_ := Term.var nid in
    let app1 := Term.app var_ one in
    let body := Term.app app1 two in
    let def_ := Def.mk (ModulePath.mp (List.cons id List.empty)) (Term.type_ 1) body List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "mul i64"

@[test]
def test_div_full_chain : Bool :=
    let id := Identifier.id "test" in
    let nid := NameRef.nid (Identifier.id "I64_div") in
    let one := Term.lit (Literal.num 8 NumSuffix.i64) in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let var_ := Term.var nid in
    let app1 := Term.app var_ one in
    let body := Term.app app1 two in
    let def_ := Def.mk (ModulePath.mp (List.cons id List.empty)) (Term.type_ 1) body List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "sdiv i64"

@[test]
def test_eq_full_chain : Bool :=
    let id := Identifier.id "test" in
    let nid := NameRef.nid (Identifier.id "I64_eq") in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let two := Term.lit (Literal.num 1 NumSuffix.i64) in
    let var_ := Term.var nid in
    let app1 := Term.app var_ one in
    let body := Term.app app1 two in
    let def_ := Def.mk (ModulePath.mp (List.cons id List.empty)) (Term.type_ 1) body List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "icmp eq"

def empty_ids : List Identifier := List.empty

def empty_cons : List TypeConstraint := List.empty

def empty_attrs : List String := List.empty

def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

@[test]
def test_param_binding : Bool :=
    let x_id := Identifier.id "x" in
    let nid := NameRef.nid (Identifier.id "I64_add") in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let x_var := Term.var (NameRef.nid x_id) in
    let var_ := Term.var nid in
    let app1 := Term.app var_ x_var in
    let body := Term.app app1 one in
    let param := Param.mk x_id (Term.type_ 1) in
    let term_ := Term.lam param body in
    let def_ := Def.mk (ModulePath.mp (List.cons (Identifier.id "add1") List.empty)) (Term.type_ 1) term_ List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "add i64"

@[test]
def test_multi_param : Bool :=
    let a_id := Identifier.id "a" in
    let b_id := Identifier.id "b" in
    let nid := NameRef.nid (Identifier.id "I64_mul") in
    let a_var := Term.var (NameRef.nid a_id) in
    let b_var := Term.var (NameRef.nid b_id) in
    let var_ := Term.var nid in
    let app1 := Term.app var_ a_var in
    let body := Term.app app1 b_var in
    let param_a := Param.mk a_id (Term.type_ 1) in
    let param_b := Param.mk b_id (Term.type_ 1) in
    let term_ := Term.lam param_a (Term.lam param_b body) in
    let def_ := Def.mk (ModulePath.mp (List.cons (Identifier.id "mul2") List.empty)) (Term.type_ 1) term_ List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    String.beq (String.slice text 0 5) "; Mod"

@[test]
def test_nested_native : Bool :=
    let x_id := Identifier.id "x" in
    let add_nid := NameRef.nid (Identifier.id "I64_add") in
    let mul_nid := NameRef.nid (Identifier.id "I64_mul") in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let x_var := Term.var (NameRef.nid x_id) in
    let mul_var := Term.var mul_nid in
    let mul_app1 := Term.app mul_var x_var in
    let mul_body := Term.app mul_app1 two in
    let add_var := Term.var add_nid in
    let add_app1 := Term.app add_var mul_body in
    let body := Term.app add_app1 one in
    let param := Param.mk x_id (Term.type_ 1) in
    let term_ := Term.lam param body in
    let def_ := Def.mk (ModulePath.mp (List.cons (Identifier.id "nested") List.empty)) (Term.type_ 1) term_ List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "mul i64"

@[test]
def test_general_call_emitted : Bool :=
    let x_id := Identifier.id "x" in
    let f_nid := NameRef.nid (Identifier.id "some_fun") in
    let x_var := Term.var (NameRef.nid x_id) in
    let f_var := Term.var f_nid in
    let body := Term.app f_var x_var in
    let param := Param.mk x_id (Term.type_ 1) in
    let term_ := Term.lam param body in
    let def_ := Def.mk (ModulePath.mp (List.cons (Identifier.id "caller") List.empty)) (Term.type_ 1) term_ List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "call i64"

@[test]
def test_if_then_else_compiled : Bool :=
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let eq_var := Term.var (NameRef.nid (Identifier.id "I64_eq")) in
    let eq_one := Term.app eq_var one in
    let cond := Term.app eq_one two in
    let if_term := Term.lit (Literal.if_ cond one two) in
    let def_ := Def.mk (ModulePath.mp (List.cons (Identifier.id "iftest") List.empty)) (Term.type_ 1) if_term List.empty List.empty in
    let mod_ := compile_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    if check_contains text "br i1"
    then check_contains text "phi i64"
    else false

def main : I64 := 42
