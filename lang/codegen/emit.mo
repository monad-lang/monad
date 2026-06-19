use lang.types
use lang.codegen.ir
use lang.module

open LLVMType
open LLVMValue

type LocalBinding {
    mk (lname : Identifier) (lval : LLVMValue),
}

type CodegenCtx {
    ctx (locals : List LocalBinding) (next_temp : I64) (next_label : I64),
}

type CompileResult {
    ok (cr_ctx : CodegenCtx) (cr_instrs : List LLVMInstruction) (cr_val : LLVMValue) (cr_blocks : List LLVMBasicBlock) (cr_funcs : List LLVMFunction) (cr_globals : List LLVMGlobal),
}

type CtxStrPair {
    mk (cs_ctx : CodegenCtx) (cs_str : String),
}

@[partial]
def empty_bindings : List LocalBinding := List.empty

@[partial]
def empty_ctx : CodegenCtx := CodegenCtx.ctx empty_bindings 0 0

@[partial]
def fresh_temp (c : CodegenCtx) : CtxStrPair := match c {
    CodegenCtx.ctx locals nt nl =>
        let name := String.concat "t" (I64.to_string nt) in
        CtxStrPair.mk (CodegenCtx.ctx locals (nt + 1) nl) name,
}

@[partial]
def fresh_label (c : CodegenCtx) (prefix : String) : CtxStrPair := match c {
    CodegenCtx.ctx locals nt nl =>
        let name := String.concat prefix (String.concat "_" (I64.to_string nl)) in
        CtxStrPair.mk (CodegenCtx.ctx locals nt (nl + 1)) name,
}

@[partial]
def ctx_bind_local (c : CodegenCtx) (name : Identifier) (val : LLVMValue) : CodegenCtx := match c {
    CodegenCtx.ctx locals nt nl => CodegenCtx.ctx (List.cons (LocalBinding.mk name val) locals) nt nl,
}

@[partial]
def ctx_lookup_local (c : CodegenCtx) (name : Identifier) : Option LLVMValue := match c {
    CodegenCtx.ctx locals nt nl => lookup_binding locals name,
}

@[partial]
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

@[partial]
def identifier_eq (a : Identifier) (b : Identifier) : Bool := match a {
    Identifier.id as => match b {
        Identifier.id bs => String.beq as bs,
    },
}

/// List of known constructor names that should be compiled as alloc_constructor
/// instead of variable references. These are constructors with 0 or more arguments.
@[partial]
def constructor_names : List String :=
    ["unit", "true", "false", "none", "some", "empty", "cons", "io", "IO.io",
     "trivial", "refl", "ok", "err", "zero", "succ", "nil", "pair"]

@[partial]
def extract_base_name (name : String) : String :=
    let last_dot := string_find_last name "." in
    if I64.gt last_dot (-1)
    then String.slice name (last_dot + 1) (String.length name)
    else name

@[partial]
def constructor_tag (name : String) : I64 :=
    // Extract base name for qualified constructors like IO.io
    let base_name := extract_base_name name in
    // Simple mapping of constructor names to tags
    // This should match the tag assignment in the runtime
    // Check qualified names first
    if String.beq name "IO.io" then 7
    else if String.beq name "Unit.unit" then 0
    else if String.beq name "Bool.true" then 1
    else if String.beq name "Bool.false" then 2
    else if String.beq name "Option.none" then 3
    else if String.beq name "Option.some" then 4
    else if String.beq name "List.empty" then 5
    else if String.beq name "List.cons" then 6
    // Check base names
    else if String.beq base_name "unit" then 0
    else if String.beq base_name "true" then 1
    else if String.beq base_name "false" then 2
    else if String.beq base_name "none" then 3
    else if String.beq base_name "some" then 4
    else if String.beq base_name "empty" then 5
    else if String.beq base_name "cons" then 6
    else if String.beq base_name "io" then 7
    else if String.beq base_name "trivial" then 8
    else if String.beq base_name "refl" then 9
    else if String.beq base_name "ok" then 10
    else if String.beq base_name "err" then 11
    else if String.beq base_name "zero" then 12
    else if String.beq base_name "succ" then 13
    else if String.beq base_name "nil" then 14
    else if String.beq base_name "pair" then 15
    else 0

/// Check if a variable name is a known constructor
/// Handles both simple names ("unit", "true") and qualified names ("Unit.unit", "IO.io")
@[partial]
def is_constructor_var (name : String) : Bool :=
    // Extract the last component after the final dot (for qualified names like "Unit.unit")
    let base_name := extract_base_name name in
    check_constructor base_name constructor_names

@[partial]
def check_constructor (name : String) (names : List String) : Bool := match names {
    List.empty => false,
    List.cons hd rest =>
        if String.beq name hd then true
        else check_constructor name rest,
}

@[partial]
def show_identifier (id : Identifier) : String := match id {
    Identifier.id s => remove_quotes_from_identifier s,
}

@[partial]
def remove_quotes_from_identifier (s : String) : String := 
    remove_quotes_loop s ""

@[partial]
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
@[partial]
def string_find_last (haystack : String) (needle : String) : I64 :=
    if String.beq needle "" then -1
    else if I64.gt (String.length needle) (String.length haystack) then -1
    else string_find_last_loop haystack needle (String.length haystack - String.length needle)

@[partial]
def string_find_last_loop (haystack : String) (needle : String) (start_idx : I64) : I64 :=
    if I64.lt start_idx 0 then -1
    else if String.beq (String.slice haystack start_idx (start_idx + String.length needle)) needle then start_idx
    else string_find_last_loop haystack needle (start_idx - 1)

@[partial]
def show_name_ref (name : NameRef) : String := match name {
    NameRef.nid id => show_identifier id,
    NameRef.nmp mp => module_path_to_str mp,
    NameRef.nop op => show_operator op,
}

@[partial]
def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

@[partial]
def cons_val (v : LLVMValue) (vs : List LLVMValue) : List LLVMValue := List.cons v vs

@[partial]
def lookup_native (name : String) : Option NativeOp :=
    if String.beq name "I64_add" then Option.some NativeOp.op_add
    else if String.beq name "I64_sub" then Option.some NativeOp.op_sub
    else if String.beq name "I64_mul" then Option.some NativeOp.op_mul
    else if String.beq name "I64_div" then Option.some NativeOp.op_sdiv
    else if String.beq name "I64_eq" then Option.some NativeOp.op_eq
    else if String.beq name "I64_lt" then Option.some NativeOp.op_lt
    else if String.beq name "I64_gt" then Option.some NativeOp.op_gt
    else if String.beq name "I64_ne" then Option.some NativeOp.op_ne
    else if String.beq name "monad_print_str" then Option.some NativeOp.op_print_str
    else if String.beq name "println" then Option.some NativeOp.op_print_str
    else if String.beq name "monad_read_file" then Option.some NativeOp.op_read_file
    else if String.beq name "read_file" then Option.some NativeOp.op_read_file
    else if String.beq name "monad_write_file" then Option.some NativeOp.op_write_file
    else if String.beq name "write_file" then Option.some NativeOp.op_write_file
    else if String.beq name "monad_file_exists" then Option.some NativeOp.op_file_exists
    else if String.beq name "file_exists" then Option.some NativeOp.op_file_exists
    else Option.none

@[partial]
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

@[partial]
def i64_ne (a : I64) (b : I64) : Bool := not (a == b)

@[partial]
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

@[partial]
def empty_instrs : List LLVMInstruction := List.empty

/// Check if an LLVMValue is a constant that can be used directly
/// in an instruction (no need for assignment).
@[partial]
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
    LLVMValue.icmp_ne lhs rhs => false,
    LLVMValue.icmp_slt lhs rhs => false,
    LLVMValue.icmp_sgt lhs rhs => false,
    LLVMValue.zext val from_ty to_ty => false,
    LLVMValue.trunc val from_ty to_ty => false,
    LLVMValue.phi pairs => false,
    LLVMValue.gep base indices => false,
    LLVMValue.load ptr => false,
    LLVMValue.bitcast val ty => false,
    LLVMValue.alloc_closure entry arity env_size => false,
    LLVMValue.alloc_constructor tag field_count => false,
}

@[partial]
def compile_lit_ir (c : CodegenCtx) (lit_ : Literal) : CompileResult := match lit_ {
    Literal.num n suffix => CompileResult.ok c empty_instrs (LLVMValue.int_ n) empty_blocks empty_funcs empty_globals_list,
    Literal.str s =>
        match fresh_label c "str" {
            CtxStrPair.mk ctx1 name =>
                // Add 1 to byte length for the null terminator \00 appended in the LLVM IR
                let byte_len := String.length s + 1 in
                let global := LLVMGlobal.mk name s byte_len true in
                CompileResult.ok ctx1 empty_instrs (LLVMValue.global_ name) empty_blocks empty_funcs (cons_global global empty_globals_list),
        },
    Literal.if_ cond then_ else_ => compile_db_if_ir c cond then_ else_,
    Literal.match_ scrutinee cases => compile_match_ir c scrutinee cases,
}

/// Compile a match expression to LLVM IR.
/// For now, this is a simplified implementation that just compiles the first case body.
/// A full implementation would check constructor tags and branch accordingly.
@[partial]
def compile_match_ir (c : CodegenCtx) (scrutinee : Term) (cases : List MatchCase) : CompileResult :=
    match cases {
        List.empty =>
            // No cases - return void
            CompileResult.ok c empty_instrs LLVMValue.void_val empty_blocks empty_funcs empty_globals_list,
        List.cons first_case rest_cases =>
            // For now, just compile and return the first case body
            match first_case {
                MatchCase.mc name args body =>
                    compile_db_term_ir c body,
            },
    }

type NtvArgs {
    mk (ctx : CodegenCtx) (instrs : List LLVMInstruction) (vals : List LLVMValue),
}

@[partial]
def compile_ntv_args (c : CodegenCtx) (args : List (Option Term)) (acc_instrs : List LLVMInstruction) (acc_vals : List LLVMValue) : NtvArgs :=
    match args {
        List.cons opt_ rest =>
            match opt_ {
                Option.some term_ =>
                    match compile_db_term_ir c term_ {
                        CompileResult.ok ctx_t instrs val _ _ _ =>
                            compile_ntv_args ctx_t rest
                                (append_instrs acc_instrs instrs)
                                (cons_val val acc_vals),
                    },
                Option.none =>
                    compile_ntv_args c rest acc_instrs acc_vals,
            },
        List.empty =>
            NtvArgs.mk c acc_instrs (rev_vals acc_vals empty_vals),
    }

@[partial]
def rev_vals (xs : List LLVMValue) (acc : List LLVMValue) : List LLVMValue := match xs {
    List.cons x rest => rev_vals rest (cons_val x acc),
    List.empty => acc,
}

@[partial]
def compile_ntv_ir (c : CodegenCtx) (native : Native) : CompileResult :=
    match native {
        Native.mk name num_args args =>
            let name_str := show_identifier name in
            let llvm_name := extract_base_name name_str in
            let fn_name := String.concat "monad_" llvm_name in
            match compile_ntv_args c args empty_instrs empty_vals {
                NtvArgs.mk ctx_args all_instrs all_vals =>
                    match fresh_temp ctx_args {
                        CtxStrPair.mk ctx_t temp =>
                            let call_val := LLVMValue.call fn_name LLVMType.i64_ all_vals false in
                            let assign_instr := LLVMInstruction.assign temp call_val in
                            CompileResult.ok ctx_t (cons_instr assign_instr all_instrs) (LLVMValue.var_ temp) empty_blocks empty_funcs empty_globals_list,
                    },
            },
    }

@[partial]
def compile_con_ir (c : CodegenCtx) (con : Con) : CompileResult :=
    match con {
        Con.mk name typ_name num_args args =>
            match compile_ntv_args c args empty_instrs empty_vals {
                NtvArgs.mk ctx_args all_instrs all_vals =>
                    match fresh_temp ctx_args {
                        CtxStrPair.mk ctx_t temp =>
                            // Call the @alloc_constructor runtime function
                            // alloc_constructor takes (tag, field_count) and allocates space for fields
                            // The tag is determined by the constructor name
                            let tag_val := constructor_tag (show_identifier name) in
                            let alloc_val := LLVMValue.alloc_constructor tag_val all_vals in
                            let assign_instr := LLVMInstruction.assign temp alloc_val in
                            CompileResult.ok ctx_t (append_instrs all_instrs (cons_instr assign_instr empty_instrs)) (LLVMValue.var_ temp) empty_blocks empty_funcs empty_globals_list,
                    },
            },
    }

type IfLabels {
    mk (ctx_after : CodegenCtx) (then_label : String) (else_label : String) (merge_label : String),
}

@[partial]
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

@[partial]
def build_branch_block (label : String) (merge_label : String) (instrs : List LLVMInstruction) : LLVMBasicBlock :=
    if ends_with_terminator instrs
    then LLVMBasicBlock.mk label instrs
    else LLVMBasicBlock.mk label (append_instrs instrs (cons_instr (LLVMInstruction.jump merge_label) empty_instrs))

@[partial]
def ends_with_terminator (instrs : List LLVMInstruction) : Bool := match instrs {
    List.empty => false,
    List.cons hd tl => match tl {
        List.empty => is_terminator_instr hd,
        List.cons x y => ends_with_terminator tl,
    },
}

@[partial]
def is_terminator_instr (instr : LLVMInstruction) : Bool := match instr {
    LLVMInstruction.branch a b c => true,
    LLVMInstruction.jump a => true,
    LLVMInstruction.ret a => true,
    LLVMInstruction.assign a b => false,
    LLVMInstruction.comment a => false,
}

@[partial]
def compile_db_lam_ir (c : CodegenCtx) (dbg : DebugName) (typ : Term) (body : Term) : CompileResult :=
    match fresh_label c "lambda" {
        CtxStrPair.mk ctx1 lam_name =>
            let name : Identifier := match dbg {
                named id => id,
                unnamed => Identifier.id "x",
            } in
            let c1 := ctx_bind_local ctx1 name (LLVMValue.parm_ 0) in
            match compile_db_term_ir c1 body {
                CompileResult.ok ctx2 instrs_r val_r blocks_r funcs_r globals_r =>
                    let entry_instrs := append_instrs instrs_r (cons_instr (LLVMInstruction.ret val_r) empty_instrs) in
                    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                    let lam_pair := ParamPair.mk "p0" LLVMType.i64_ in
                    let lam_params := cons_pair lam_pair empty_pairs in
                    let lam_func := LLVMFunction.mk lam_name lam_params LLVMType.i64_ (cons_block entry_block blocks_r) false in
                    CompileResult.ok ctx2 empty_instrs (LLVMValue.var_ lam_name) empty_blocks (cons_func lam_func funcs_r) globals_r,
            },
    }

@[partial]
def compile_db_if_ir (c : CodegenCtx) (cond : Term) (then_ : Term) (else_ : Term) : CompileResult :=
    match compile_db_term_ir c cond {
        CompileResult.ok ctx_cond cond_instrs cond_val blocks_cond funcs_cond globals_cond =>
            match build_if_labels ctx_cond {
                IfLabels.mk ctx_branches then_label else_label merge_label =>
                    let branch_instr := LLVMInstruction.branch cond_val then_label else_label in
                    let entry_instrs := append_instrs cond_instrs (cons_instr branch_instr empty_instrs) in
                    build_db_if_blocks ctx_branches then_label else_label merge_label then_ else_ entry_instrs blocks_cond funcs_cond globals_cond,
            },
    }

@[partial]
def build_db_if_blocks (ctx : CodegenCtx) (then_label : String) (else_label : String) (merge_label : String) (then_ : Term) (else_ : Term) (entry_instrs : List LLVMInstruction) (entry_blocks : List LLVMBasicBlock) (entry_funcs : List LLVMFunction) (entry_globals : List LLVMGlobal) : CompileResult :=
    match compile_db_term_ir ctx then_ {
        CompileResult.ok ctx_then then_instrs then_val blocks_then funcs_then globals_then =>
            let then_block := build_branch_block then_label merge_label then_instrs in
            match compile_db_term_ir ctx_then else_ {
                CompileResult.ok ctx_else else_instrs else_val blocks_else funcs_else globals_else =>
                    let else_block := build_branch_block else_label merge_label else_instrs in
                    build_merge_result ctx_else merge_label then_val then_label else_val else_label entry_instrs entry_blocks entry_funcs entry_globals blocks_then blocks_else funcs_then funcs_else globals_then globals_else then_block else_block,
            },
    }

@[partial]
def build_merge_result (ctx_else : CodegenCtx) (merge_label : String) (then_val : LLVMValue) (then_label : String) (else_val : LLVMValue) (else_label : String) (entry_instrs : List LLVMInstruction) (entry_blocks : List LLVMBasicBlock) (entry_funcs : List LLVMFunction) (entry_globals : List LLVMGlobal) (blocks_then : List LLVMBasicBlock) (blocks_else : List LLVMBasicBlock) (funcs_then : List LLVMFunction) (funcs_else : List LLVMFunction) (globals_then : List LLVMGlobal) (globals_else : List LLVMGlobal) (then_block : LLVMBasicBlock) (else_block : LLVMBasicBlock) : CompileResult :=
    match fresh_temp ctx_else {
        CtxStrPair.mk ctx_phi phi_temp =>
            let phi_val := LLVMValue.phi (cons_phi (PhiPair.mk then_val then_label) (cons_phi (PhiPair.mk else_val else_label) empty_phis)) in
            let phi_instr := LLVMInstruction.assign phi_temp phi_val in
            let ret_instr := LLVMInstruction.ret (LLVMValue.var_ phi_temp) in
            let merge_instrs := cons_instr phi_instr (cons_instr ret_instr empty_instrs) in
            let merge_block := LLVMBasicBlock.mk merge_label merge_instrs in
            let all_blocks := cons_block then_block (cons_block else_block (cons_block merge_block (append_blocks (append_blocks entry_blocks blocks_then) blocks_else))) in
            let all_funcs := append_funcs (append_funcs entry_funcs funcs_then) funcs_else in
            let all_globals := append_globals (append_globals entry_globals globals_then) globals_else in
            CompileResult.ok ctx_phi entry_instrs (LLVMValue.var_ phi_temp) all_blocks all_funcs all_globals,
    }

@[partial]
def compile_db_term_ir (c : CodegenCtx) (term_ : Term) : CompileResult := match term_ {
    Term.lit val => compile_lit_ir c val,
    Term.var idx dbg =>
        match dbg {
            DebugName.named id =>
                match ctx_lookup_local c id {
                    Option.some val => CompileResult.ok c empty_instrs val empty_blocks empty_funcs empty_globals_list,
                    Option.none =>
                        // Check if this is a constructor reference
                        let name := show_identifier id in
                        let llvm_name := replace_dots_with_underscores name in
                        if is_constructor_var name then
                            // Compile as alloc_constructor with 0 fields
                            match fresh_temp c {
                                CtxStrPair.mk ctx_t temp =>
                                    let alloc_val := LLVMValue.call "alloc_constructor" LLVMType.i64_ (List.cons (LLVMValue.int_ 0) (List.cons (LLVMValue.int_ 0) List.empty)) false in
                                    let assign_instr := LLVMInstruction.assign temp alloc_val in
                                    CompileResult.ok ctx_t (cons_instr assign_instr empty_instrs) (LLVMValue.var_ temp) empty_blocks empty_funcs empty_globals_list,
                            }
                        else
                            CompileResult.ok c empty_instrs (LLVMValue.var_ llvm_name) empty_blocks empty_funcs empty_globals_list,
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

@[partial]
def compile_db_app_ir (c : CodegenCtx) (fun : Term) (arg : Term) : CompileResult :=
    // Check if this is a constructor application
    match try_compile_constructor_app_db c fun arg {
        Option.some result => result,
        Option.none =>
            match try_compile_inline_native_db c fun arg {
                Option.some result => result,
                Option.none => compile_general_db_call c fun arg,
            },
    }

@[partial]
def try_compile_constructor_app_db (c : CodegenCtx) (fun : Term) (arg : Term) : Option CompileResult :=
    match fun {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id =>
                    let name := show_identifier id in
                    if is_constructor_var name then
                        // This is a constructor application like IO.io unit or io unit
                        // Compile it as a constructor with the argument
                        let base_name := extract_base_name name in
                        let tag := constructor_tag base_name in
                        let con := Con.mk (Identifier.id base_name) (ModulePath.mp List.empty) 1 (List.cons (Option.some arg) List.empty) in
                        Option.some (compile_con_ir c con)
                    else Option.none,
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

@[partial]
def try_compile_inline_native_db (c : CodegenCtx) (fun : Term) (arg : Term) : Option CompileResult :=
    match fun {
        Term.app fun2 arg2 =>
            match fun2 {
                Term.var idx dbg =>
                    match dbg {
                        DebugName.named id =>
                            let name := show_identifier id in
                            let base_name := extract_base_name name in
                            match lookup_native base_name {
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
                    let base_name := extract_base_name name in
                    match lookup_native base_name {
                        Option.some op =>
                            Option.some (compile_native_app_unary_db c op arg),
                        Option.none => Option.none,
                    },
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

@[partial]
def compile_native_app_unary_db (c : CodegenCtx) (op : NativeOp) (arg : Term) : CompileResult :=
    match compile_db_term_ir c arg {
        CompileResult.ok ctx1 instrs1 val1 blocks1 funcs1 globals1 =>
            // For unary native operations like print_str, call the runtime function
            match fresh_temp ctx1 {
                CtxStrPair.mk ctx_t temp =>
                    let fn_name := native_op_to_fn_name op in
                    let call_val := LLVMValue.call fn_name LLVMType.i64_ (cons_val val1 empty_vals) false in
                    let assign_instr := LLVMInstruction.assign temp call_val in
                    CompileResult.ok ctx_t (append_instrs instrs1 (cons_instr assign_instr empty_instrs)) (LLVMValue.var_ temp) blocks1 funcs1 globals1,
            },
    }

@[partial]
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
}

@[partial]
def compile_native_app_db (c : CodegenCtx) (op : NativeOp) (arg2 : Term) (arg : Term) : CompileResult :=
    match compile_db_term_ir c arg2 {
        CompileResult.ok ctx2 instrs2 val2 _ _ _ =>
            match compile_db_term_ir ctx2 arg {
                CompileResult.ok ctx1 instrs1 val1 _ _ _ =>
                    let combined := append_instrs instrs2 instrs1 in
                    match extract_lit_from_val val2 {
                        Option.some n1 =>
                            match extract_lit_from_val val1 {
                                Option.some n2 =>
                                    CompileResult.ok ctx1 combined (fold_native_const op n1 n2) empty_blocks empty_funcs empty_globals_list,
                                Option.none =>
                                    emit_arith_instr ctx1 op val2 val1 combined,
                            },
                        Option.none =>
                            emit_arith_instr ctx1 op val2 val1 combined,
                    },
            },
    }

@[partial]
def compile_general_db_call (c : CodegenCtx) (fun : Term) (arg : Term) : CompileResult :=
    match compile_db_term_ir c fun {
        CompileResult.ok ctx_f instrs_f val_f blocks_f funcs_f globals_f =>
            match compile_db_term_ir ctx_f arg {
                CompileResult.ok ctx_a instrs_a val_a blocks_a funcs_a globals_a =>
                    let combined := append_instrs instrs_f instrs_a in
                    let all_blocks := append_blocks blocks_f blocks_a in
                    let all_funcs := append_funcs funcs_f funcs_a in
                    let all_globals := append_globals globals_f globals_a in
                    match val_f {
                        LLVMValue.var_ name =>
                            combine_direct_call ctx_a name val_a combined all_blocks all_funcs all_globals,
                        LLVMValue.parm_ idx =>
                            combine_indirect_call ctx_a val_a combined all_blocks all_funcs all_globals,
                        _ =>
                            CompileResult.ok ctx_a combined LLVMValue.void_val all_blocks all_funcs all_globals,
                    },
            },
    }

@[partial]
def combine_direct_call (ctx_a : CodegenCtx) (name : String) (val_a : LLVMValue) (combined : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) : CompileResult :=
    match fresh_temp ctx_a {
        CtxStrPair.mk ctx_t temp =>
            let call_instr := LLVMInstruction.assign temp
                (LLVMValue.call name LLVMType.i64_ (cons_val val_a empty_vals) false) in
            CompileResult.ok ctx_t (append_instrs combined (cons_instr call_instr empty_instrs)) (LLVMValue.var_ temp) blocks funcs globals,
    }

@[partial]
def combine_indirect_call (ctx_a : CodegenCtx) (val_a : LLVMValue) (combined : List LLVMInstruction) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal) : CompileResult :=
    match fresh_temp ctx_a {
        CtxStrPair.mk ctx_t temp =>
            let call_instr := LLVMInstruction.assign temp
                (LLVMValue.call "apply_fun" LLVMType.i64_ (cons_val val_a empty_vals) false) in
            CompileResult.ok ctx_t (append_instrs combined (cons_instr call_instr empty_instrs)) (LLVMValue.var_ temp) blocks funcs globals,
    }

@[partial]
def emit_arith_instr (c : CodegenCtx) (op : NativeOp) (lhs : LLVMValue) (rhs : LLVMValue) (instrs : List LLVMInstruction) : CompileResult :=
    match fresh_temp c {
        CtxStrPair.mk new_ctx temp =>
            let arith_val := compile_native_val op lhs rhs in
            let arith_instr := LLVMInstruction.assign temp arith_val in
            CompileResult.ok new_ctx (append_instrs instrs (cons_instr arith_instr empty_instrs)) (LLVMValue.var_ temp) empty_blocks empty_funcs empty_globals_list,
    }

@[partial]
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
    LLVMValue.icmp_ne lhs rhs => Option.none,
    LLVMValue.icmp_slt lhs rhs => Option.none,
    LLVMValue.icmp_sgt lhs rhs => Option.none,
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

@[partial]
def append_instrs (a : List LLVMInstruction) (b : List LLVMInstruction) : List LLVMInstruction := match a {
    List.empty => b,
    List.cons hd tl => cons_instr hd (append_instrs tl b),
}

@[partial]
def append_blocks (a : List LLVMBasicBlock) (b : List LLVMBasicBlock) : List LLVMBasicBlock := match a {
    List.empty => b,
    List.cons hd tl => cons_block hd (append_blocks tl b),
}

@[partial]
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

@[partial]
def param_name_db (p : Param) : Identifier := match p {
    Param.mk name typ_ mult default => name,
}

@[partial]
def empty_blocks : List LLVMBasicBlock := List.empty

@[partial]
def cons_block (b : LLVMBasicBlock) (bs : List LLVMBasicBlock) : List LLVMBasicBlock :=
    List.cons b bs

@[partial]
def module_path_to_str (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => join_identifiers ids,
}

@[partial]
def join_identifiers (ids : List Identifier) : String := match ids {
    List.empty => "",
    List.cons hd rest => join_ids_rest hd rest,
}

@[partial]
def join_ids_rest (hd : Identifier) (rest : List Identifier) : String :=
    match rest {
        List.empty => show_identifier hd,
        List.cons x y => String.concat (show_identifier hd) (String.concat "__" (join_identifiers rest)),
    }

type DefResult {
    dr (ctx : CodegenCtx) (funcs : List LLVMFunction) (globals : List LLVMGlobal),
}

@[partial]
def build_llvm_params_db (params : List Param) : List ParamPair :=
    build_llvm_params_from_db params 0

@[partial]
def build_llvm_params_from_db (params : List Param) (idx : I64) : List ParamPair := match params {
    List.empty => List.empty,
    List.cons p rest =>
        let pp := ParamPair.mk (String.concat "p" (I64.to_string idx)) LLVMType.i64_ in
        List.cons pp (build_llvm_params_from_db rest (idx + 1)),
}

/// Compile a canonical Def (de Bruijn Term) to LLVM IR.
@[partial]
def compile_db_def_ir (c : CodegenCtx) (def_ : Def) : DefResult := match def_ {
    Def.mk name typ term_ constraints attrs =>
        let fn_name := module_path_to_str name in
        let params := collect_db_params term_ in
        let llvm_params := build_llvm_params_db params in
        let body := strip_db_lams term_ in
        let c0 := bind_params_in_ctx_db c params in
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
                                let all_blocks := append_blocks (cons_block entry_block empty_blocks) blocks_r in
                                let main_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ all_blocks true in
                                DefResult.dr ctx_t (cons_func main_func funcs_r) globals_r,
                        },
                    _ =>
                        let entry_instrs := append_instrs instrs_r (cons_instr (LLVMInstruction.ret val_r) empty_instrs) in
                        let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                        let all_blocks := append_blocks (cons_block entry_block empty_blocks) blocks_r in
                        let main_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ all_blocks true in
                        DefResult.dr ctx_r (cons_func main_func funcs_r) globals_r,
                },
        },
}

/// Compile a list of canonical Defs to LLVM functions.
@[partial]
def compile_db_def_list (c : CodegenCtx) (defs : List Def) : DefResult := match defs {
    List.empty => DefResult.dr c empty_funcs empty_globals_list,
    List.cons d rest =>
        match compile_db_def_ir c d {
            DefResult.dr ctx_d funcs_d globals_d =>
                match compile_db_def_list ctx_d rest {
                    DefResult.dr ctx_rest funcs_rest globals_rest =>
                        DefResult.dr ctx_rest (append_funcs funcs_d funcs_rest) (append_globals globals_d globals_rest),
                },
        },
}

/// Compile a list of canonical Defs to a complete LLVM module.
@[partial]
def compile_db_decls_ir (defs : List Def) : LLVMModule :=
    match compile_db_def_list empty_ctx defs {
        DefResult.dr _ compiled_funcs compiled_globals =>
            let funcs := ren_main_and_wrap compiled_funcs in
            LLVMModule.mk "x86_64-unknown-linux-gnu" compiled_globals funcs runtime_declarations,
    }

/// Compile a list of Decl to a complete LLVM module.
/// Extracts def_d and inductive_d entries, compiles constructors and defs.
@[partial]
def compile_db_module (decls : List Decl) : LLVMModule :=
    let defs := extract_defs decls in
    let inds := extract_inductives decls in
    let ctor_funcs := compile_db_inductive_decls inds in
    match compile_db_def_list empty_ctx defs {
        DefResult.dr _ compiled_funcs compiled_globals =>
            let all_funcs := append_funcs ctor_funcs compiled_funcs in
            let funcs := ren_main_and_wrap all_funcs in
            LLVMModule.mk "x86_64-unknown-linux-gnu" compiled_globals funcs runtime_declarations,
    }

/// Extract def_d entries from a list of Decl.
@[partial]
def extract_defs (decls : List Decl) : List Def := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        let rest_defs := extract_defs rest in
        match d {
            Decl.def_d def_ => List.cons def_ rest_defs,
            _ => rest_defs,
        }
}

/// Extract inductive_d entries from a list of Decl.
@[partial]
def extract_inductives (decls : List Decl) : List Inductive := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        let rest_inds := extract_inductives rest in
        match d {
            Decl.inductive_d ind => List.cons ind rest_inds,
            _ => rest_inds,
        }
}

/// Compile a list of canonical InductConstructors to LLVM constructor wrapper functions.
@[partial]
def compile_db_inductive_constructors (constructors : List InductConstructor) : List LLVMFunction := match constructors {
    List.empty => empty_funcs,
    List.cons c rest =>
        match c {
            InductConstructor.mk name params typ =>
                let name_str := module_path_to_str name in
                let field_count := count_db_params params 0 in
                let func := compile_constructor_decl name_str field_count in
                cons_func func (compile_db_inductive_constructors rest)
        }
}

/// Compile a single canonical Inductive to LLVM constructor wrapper functions.
@[partial]
def compile_db_inductive (ind : Inductive) : List LLVMFunction := match ind {
    Inductive.mk name params typ constructors attrs =>
        compile_db_inductive_constructors constructors
}

/// Compile a list of canonical Inductives to LLVM constructor wrapper functions.
@[partial]
def compile_db_inductive_decls (ind_decls : List Inductive) : List LLVMFunction := match ind_decls {
    List.empty => empty_funcs,
    List.cons ind rest =>
        let funcs := compile_db_inductive ind in
        append_funcs funcs (compile_db_inductive_decls rest)
}

/// Compile an inductive type constructor to an LLVM wrapper function.
/// Generates: define cc 9 i64 @monad_ctor_<name>(i64 %p0, i64 %p1, ...) {
///   entry:
///     %ctemp = alloc_constructor(%p0, %p1, ...)
///     ret i64 %ctemp
/// }
/// Matches Rust reference: llvm-codegen/src/codegen/constructors.rs:38-82
@[partial]
def compile_constructor_decl (con_name : String) (field_count : I64) : LLVMFunction :=
    let params := build_constructor_params field_count in
    let fields := build_param_fields field_count in
    let alloc_val := LLVMValue.alloc_constructor 0 fields in
    let assign_instr := LLVMInstruction.assign "ctemp" alloc_val in
    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ "ctemp") in
    let entry_block := LLVMBasicBlock.mk "entry" (cons_instr assign_instr (cons_instr ret_instr empty_instrs)) in
    let func_name := String.concat "monad_ctor_" con_name in
    LLVMFunction.mk func_name params LLVMType.i64_ (cons_block entry_block empty_blocks) true

@[partial]
def build_constructor_params (count : I64) : List ParamPair :=
    build_params_from count 0

@[partial]
def build_params_from (count : I64) (idx : I64) : List ParamPair :=
    if idx == count then empty_pairs
    else
        let name := String.concat "p" (I64.to_string idx) in
        cons_pair (ParamPair.mk name LLVMType.i64_) (build_params_from count (idx + 1))

@[partial]
def build_param_fields (count : I64) : List LLVMValue :=
    build_fields_from count 0

@[partial]
def build_fields_from (count : I64) (idx : I64) : List LLVMValue :=
    if idx == count then empty_vals
    else List.cons (LLVMValue.parm_ idx) (build_fields_from count (idx + 1))

@[partial]
def bind_params_in_ctx_db (c : CodegenCtx) (params : List Param) : CodegenCtx :=
    bind_params_with_idx_db c params 0

@[partial]
def bind_params_with_idx_db (c : CodegenCtx) (params : List Param) (idx : I64) : CodegenCtx := match params {
    List.empty => c,
    List.cons p rest =>
        let c1 := ctx_bind_local c (param_name_db p) (LLVMValue.parm_ idx) in
        bind_params_with_idx_db c1 rest (idx + 1),
}

@[partial]
def empty_vals : List LLVMValue := List.empty

@[partial]
def empty_phis : List PhiPair := List.empty

@[partial]
def cons_phi (p : PhiPair) (ps : List PhiPair) : List PhiPair := List.cons p ps

@[partial]
def cons_instr (i : LLVMInstruction) (is : List LLVMInstruction) : List LLVMInstruction :=
    List.cons i is

/// LLVM wrapper from C main->main_monad. Unused in the current pipeline
/// (the C runtime's main() calls main_monad directly). Kept as reference
/// for future pipeline integration.
@[partial]
def compile_main_wrapper_ir : LLVMFunction :=
    let argc_pair := ParamPair.mk "argc" LLVMType.i32_ in
    let argv_pair := ParamPair.mk "argv" LLVMType.i64_ in
    let wrapper_params := cons_pair argc_pair (cons_pair argv_pair (empty_pairs)) in
    let argv_val := LLVMValue.parm_ 1 in
    let args_singleton := List.cons argv_val List.empty in
    let call_instr := LLVMInstruction.assign "t0"
        (LLVMValue.call "main_monad" LLVMType.i64_ args_singleton false) in
    let trunc_instr := LLVMInstruction.assign "t1"
        (LLVMValue.trunc (LLVMValue.var_ "t0") LLVMType.i64_ LLVMType.i32_) in
    let ret_instr := LLVMInstruction.ret (LLVMValue.var_ "t1") in
    let entry_instrs := cons_instr call_instr (cons_instr trunc_instr (cons_instr ret_instr List.empty)) in
    let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
    LLVMFunction.mk "main" wrapper_params LLVMType.i32_ (cons_block entry_block empty_blocks) false

@[partial]
def empty_pairs : List ParamPair := List.empty

@[partial]
def cons_pair (p : ParamPair) (ps : List ParamPair) : List ParamPair :=
    List.cons p ps

@[partial]
def empty_strs : List String := List.empty

@[partial]
def cons_str (s : String) (ss : List String) : List String := List.cons s ss

@[partial]
def mk_decl (name : String) (params : List String) (ret_ty : String) : LLVMDeclaration :=
    LLVMDeclaration.mk name params ret_ty

@[partial]
def empty_decls : List LLVMDeclaration := List.empty

@[partial]
def cons_decl (d : LLVMDeclaration) (ds : List LLVMDeclaration) : List LLVMDeclaration :=
    List.cons d ds

@[partial]
def runtime_declarations : List LLVMDeclaration :=
    let d1 := mk_decl "monad_alloc" (cons_str "i64" empty_strs) "i8*" in
    let d2 := mk_decl "monad_retain" (cons_str "i8*" empty_strs) "void" in
    let d3 := mk_decl "monad_release" (cons_str "i8*" empty_strs) "void" in
    let d4 := mk_decl "monad_print_str" (cons_str "i8*" empty_strs) "void" in
    let d5 := mk_decl "monad_read_file" (cons_str "i8*" empty_strs) "i8*" in
    let d6 := mk_decl "monad_write_file" (cons_str "i8*" (cons_str "i8*" (cons_str "i64" empty_strs))) "void" in
    let d7 := mk_decl "monad_file_exists" (cons_str "i8*" empty_strs) "i8*" in
    let d8 := mk_decl "alloc_closure" (cons_str "i8*" (cons_str "i64" (cons_str "i64" empty_strs))) "i64" in
    let d9 := mk_decl "alloc_constructor" (cons_str "i64" (cons_str "i64" empty_strs)) "i64" in
    let d10 := mk_decl "alloc_string" (cons_str "i8*" (cons_str "i64" empty_strs)) "i64" in
    cons_decl d1 (cons_decl d2 (cons_decl d3 (cons_decl d4 (cons_decl d5 (cons_decl d6 (cons_decl d7 (cons_decl d8 (cons_decl d9 (cons_decl d10 empty_decls)))))))))

@[partial]
def empty_funcs : List LLVMFunction := List.empty

@[partial]
def cons_func (f : LLVMFunction) (fs : List LLVMFunction) : List LLVMFunction :=
    List.cons f fs

@[partial]
def empty_globals_list : List LLVMGlobal := List.empty

/// Count the number of fields in a Param list.
@[partial]
def count_db_params (params : List Param) (n : I64) : I64 := match params {
    List.empty => n,
    List.cons p rest => count_db_params rest (n + 1),
}

/// When the user's main has no params, add an `args` param so the C runtime
/// can pass the command-line argument list. If main already has params (e.g.,
/// `def main (args : List String) : I64`), keep them as-is.
@[partial]
def ren_main_and_wrap (funcs : List LLVMFunction) : List LLVMFunction :=
    rename_main funcs

@[partial]
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
@[partial]
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
@[partial]
def ensure_main_params (params : List ParamPair) : List ParamPair := match params {
    List.empty => cons_pair (ParamPair.mk "args" LLVMType.i64_) empty_pairs,
    List.cons x y => params,
}

// === De Bruijn (canonical) def compilation ===

/// Collect lambda params from a de Bruijn Term body.
/// Strips `Term.lam` prefixes and returns Param for each.
@[partial]
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
@[partial]
def strip_db_lams (term_ : Term) : Term := match term_ {
    Term.lam dbg typ body => strip_db_lams body,
    Term.forall dbg kind body => strip_db_lams body,
    _ => term_,
}

@[test]
def test_runtime_decls_not_empty : Bool :=
    match runtime_declarations {
        List.empty => false,
        List.cons x y => true,
    }

@[test]
def test_module_emit_has_header : Bool :=
    let text := lang.codegen.ir.emit_module (compile_db_decls_ir List.empty) in
    let prefix := String.slice text 0 12 in
    String.beq prefix "; ModuleID ="

@[test]
def test_empty_decls_module : Bool :=
    match (compile_db_decls_ir List.empty) {
        LLVMModule.mk triple globals funcs decls =>
            String.beq triple "x86_64-unknown-linux-gnu",
    }

@[test]
def test_compile_db_inductive_decls : Bool :=
    let some_name := ModulePath.mp (List.cons (Identifier.id "Some") List.empty) in
    let some_ctor := InductConstructor.mk some_name empty_params_list (Term.type_ 1) in
    let none_name := ModulePath.mp (List.cons (Identifier.id "None") List.empty) in
    let none_ctor := InductConstructor.mk none_name empty_params_list (Term.type_ 1) in
    let ctors := List.cons some_ctor (List.cons none_ctor List.empty) in
    let ind_name := ModulePath.mp (List.cons (Identifier.id "Option") List.empty) in
    let ind := Inductive.mk ind_name empty_params_list (Term.type_ 1) ctors empty_attrs in
    let funcs := compile_db_inductive_decls (List.cons ind List.empty) in
    let mod_ := LLVMModule.mk "x86_64-unknown-linux-gnu" empty_globals_list funcs empty_decls in
    let text := lang.codegen.ir.emit_module mod_ in
    if check_contains text "monad_ctor_Some"
    then check_contains text "monad_ctor_None"
    else false

@[partial]
def empty_params_list : List Param := List.empty

@[partial]
def empty_attrs : List String := List.empty

@[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

// === Multi-module compilation ===

/// Compile a single module's declarations to LLVM IR
/// This takes a ModuleInfo (which preserves module boundaries) and compiles
/// only the declarations from that specific module.
@[partial]
def compile_module_to_ir (module_info : ModuleInfo) : LLVMModule :=
    match module_info {
        ModuleInfo.mk path file_path decls =>
            let defs := extract_defs decls in
            compile_db_decls_ir defs
    }

// === Multi-module compilation ===

/// Replace dots with underscores in a string for use as LLVM identifier
@[partial]
def replace_dots_with_underscores (s : String) : String := 
    replace_dots_loop s ""

@[partial]
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

/// Check if a function name is a main function (handles both "main" and module__main)
@[partial]
def ends_with_main (name : String) : Bool := 
    if String.beq name "main" then true
    else if String.length name > 3 then
        let suffix := String.slice name (String.length name - 3) (String.length name) in
        String.beq suffix "__main"
    else false

/// Compile all loaded modules to a single LLVM module.
/// All declarations from all modules are compiled together with fully qualified names.
@[partial]
def compile_loaded_modules_to_ir (loaded : LoadedModules) : LLVMModule := 
    let main_mod := get_loaded_main loaded in
    let all_mods := get_loaded_all loaded in
    // Collect all declarations without module prefixes (to avoid name resolution issues)
    let all_decls := collect_all_decls_from_modules all_mods List.empty in
    // Compile all declarations together
    compile_db_module all_decls

@[partial]
def collect_all_decls_from_modules_with_prefix (modules : List ModuleInfo) (acc : List Decl) : List Decl := match modules {
    List.empty => acc,
    List.cons mod_ rest => 
        let mod_decls := get_module_info_decls mod_ in
        let mod_path := get_module_info_path mod_ in
        let prefixed_decls := prefix_decl_names mod_decls mod_path in
        collect_all_decls_from_modules_with_prefix rest (append_decls_list prefixed_decls acc),
}

@[partial]
def prefix_decl_names (decls : List Decl) (module_path : ModulePath) : List Decl := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        let prefixed_d := prefix_decl_name d module_path in
        List.cons prefixed_d (prefix_decl_names rest module_path),
}

@[partial]
def prefix_decl_name (d : Decl) (module_path : ModulePath) : Decl := match d {
    Decl.def_d def_ => Decl.def_d (prefix_def_name def_ module_path),
    Decl.inductive_d ind => Decl.inductive_d (prefix_inductive_name ind module_path),
    _ => d,
}

@[partial]
def prefix_def_name (def_ : Def) (module_path : ModulePath) : Def := match def_ {
    Def.mk name typ term constraints attrs =>
        let prefixed_name := prefix_module_path module_path name in
        Def.mk prefixed_name typ term constraints attrs,
}

@[partial]
def prefix_inductive_name (ind : Inductive) (module_path : ModulePath) : Inductive := match ind {
    Inductive.mk name params typ constructors attrs =>
        let prefixed_name := prefix_module_path module_path name in
        Inductive.mk prefixed_name params typ (prefix_constructor_names constructors module_path) attrs,
}

@[partial]
def prefix_constructor_names (cons : List InductConstructor) (module_path : ModulePath) : List InductConstructor := match cons {
    List.empty => List.empty,
    List.cons c rest =>
        let prefixed_c := prefix_constructor_name c module_path in
        List.cons prefixed_c (prefix_constructor_names rest module_path),
}

@[partial]
def prefix_constructor_name (c : InductConstructor) (module_path : ModulePath) : InductConstructor := match c {
    InductConstructor.mk name params typ =>
        let prefixed_name := prefix_module_path module_path name in
        InductConstructor.mk prefixed_name params typ,
}

@[partial]
def prefix_module_path (module_path : ModulePath) (name : ModulePath) : ModulePath := 
    // Concatenate module_path and name to create a fully qualified path
    match module_path {
        ModulePath.mp mp_ids =>
            match name {
                ModulePath.mp name_ids =>
                    ModulePath.mp (append_identifiers mp_ids name_ids),
            },
    }

@[partial]
def append_identifiers (a : List Identifier) (b : List Identifier) : List Identifier := match a {
    List.empty => b,
    List.cons hd tl => List.cons hd (append_identifiers tl b),
}

@[partial]
def collect_all_decls_from_modules (modules : List ModuleInfo) (acc : List Decl) : List Decl := match modules {
    List.empty => acc,
    List.cons mod_ rest => 
        let mod_decls := get_module_info_decls mod_ in
        collect_all_decls_from_modules rest (append_decls_list mod_decls acc),
}

@[partial]
def append_decls_list (a : List Decl) (b : List Decl) : List Decl := match a {
    List.empty => b,
    List.cons hd tl => List.cons hd (append_decls_list tl b),
}
