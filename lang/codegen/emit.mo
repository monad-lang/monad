use io {IO, println}
use lang.types {
  Con, DebugName, Decl, Def, Identifier, InductConstructor, Inductive, Literal,
  LoadedModules, LocalScope, MatchCase, ModulePath, NameRef, Native, Operator,
  Param, Scope, ScopeData, StructLitField, Term,
  app, con, ctx, def_d, forall, hole, id, if_, inductive_d, join_identifiers, lam,
  lit, match_, mc, mk, mp, name, named, nid, nmp, nop, ntv, num, operator,
  param_many, pi, show_identifier, show_operator, str, type_, unnamed, var,
}
use lang.codegen.ir {
  LLVMBasicBlock, LLVMDeclaration, LLVMFunction, LLVMGlobal, LLVMInstruction,
  LLVMModule, LLVMType, LLVMValue, NativeOp, ParamPair, PhiPair, add, alloc_closure,
  alloc_constructor, assign, bitcast, bool_, branch, call, comment, emit_module,
  fn_, gep, global_, i32_, i64_, icmp_eq, icmp_ne, icmp_sgt, icmp_slt, int32_, int_,
  jump, load, mk, mul, native_op, op_add, op_eq, op_file_exists, op_gt, op_lt,
  op_mul, op_ne, op_print_str, op_read_file, op_sdiv, op_sub, op_write_file,
  parm_, phi, ret, sdiv, show_llvm_type, sub, trunc, var_, void_val, zext,
}
use lang.module {
  LoadedModules, ModuleInfo, elaborate_module_decls_best_effort, get_loaded_all,
  get_loaded_main, get_module_info_decls, mk,
}
use lang.scope {
  add_constraint_dict_params_decls, build_scope_from_decls, collect_infixes,
  promote_instance_defs, resolve_class_calls_decls, resolve_infix_decls,
}

open IO {println}
open LLVMType {i32_, i64_}
open LLVMValue {
  add, alloc_closure, alloc_constructor, bitcast, bool_, call, gep, global_,
  icmp_eq, icmp_ne, icmp_sgt, icmp_slt, int32_, int_, load, mul, native_op, parm_,
  phi, sdiv, sub, trunc, var_, void_val, zext,
}

type LocalBinding {
    mk (lname : Identifier) (lval : LLVMValue),
}

/// One top-level def's own known arity (its param count, i.e. the number
/// of leading `Term.lam`s in its body) keyed by the SAME `llvm_name` a
/// bare `Term.var` reference to it would compute (`replace_dots_with_
/// underscores` of its module path) -- built once per module compile
/// (`build_arity_table`) and threaded through `CodegenCtx` so `Term.var`'s
/// value-position case (Phase 0 of the dictionary-passing plan, see
/// plans/bootstrapping/self-hosted-compiler.md) can tell an arity-0 def
/// (still an eager 0-arg call, unchanged) from an arity>0 def (now boxed
/// via `alloc_closure` instead of miscompiling as a 0-arg call to a
/// function that isn't one).
type ArityEntry {
    mk (aname : String) (aarity : I64),
}

type CodegenCtx {
    ctx (locals : List LocalBinding) (next_temp : I64) (next_label : I64) (arities : List ArityEntry),
}

type CompileResult {
    ok (cr_ctx : CodegenCtx) (cr_instrs : List LLVMInstruction) (cr_val : LLVMValue) (cr_blocks : List LLVMBasicBlock) (cr_funcs : List LLVMFunction) (cr_globals : List LLVMGlobal),
}

type CtxStrPair {
    mk (cs_ctx : CodegenCtx) (cs_str : String),
}

#[partial]
def empty_bindings : List LocalBinding := List.empty

#[partial]
def empty_arities : List ArityEntry := List.empty

/// `arities` -- see `ArityEntry`'s own doc comment. Callers with a real
/// `List Def` in scope should build one via `build_arity_table` instead
/// of passing `empty_arities` (an empty table just means every bare
/// global reference falls back to today's eager-0-arg-call behavior --
/// correct only for genuinely 0-arity defs).
#[partial]
def empty_ctx (arities : List ArityEntry) : CodegenCtx := CodegenCtx.ctx empty_bindings 0 0 arities

#[partial]
def fresh_temp (c : CodegenCtx) : CtxStrPair := match c {
    CodegenCtx.ctx locals nt nl arities =>
        let name := String.concat "t" (I64.to_string nt) in
        CtxStrPair.mk (CodegenCtx.ctx locals (nt + 1) nl arities) name,
}

#[partial]
def fresh_label (c : CodegenCtx) (prefix : String) : CtxStrPair := match c {
    CodegenCtx.ctx locals nt nl arities =>
        let name := String.concat prefix (String.concat "_" (I64.to_string nl)) in
        CtxStrPair.mk (CodegenCtx.ctx locals nt (nl + 1) arities) name,
}

#[partial]
def ctx_bind_local (c : CodegenCtx) (name : Identifier) (val : LLVMValue) : CodegenCtx := match c {
    CodegenCtx.ctx locals nt nl arities => CodegenCtx.ctx (List.cons (LocalBinding.mk name val) locals) nt nl arities,
}

#[partial]
def ctx_lookup_local (c : CodegenCtx) (name : Identifier) : Option LLVMValue := match c {
    CodegenCtx.ctx locals nt nl arities => lookup_binding locals name,
}

/// Looks up a global's own known arity by its already-mangled
/// `llvm_name` (see `ArityEntry`'s doc comment). `Option.none` for any
/// name not in the table -- a name genuinely absent from the compiled
/// module's own def list (shouldn't happen for a real reachable
/// reference) as well as for a module compiled via `empty_ctx
/// empty_arities` (no table built) both fall back safely to the
/// pre-Phase-0 eager-0-arg-call behavior at the one call site that reads
/// this (`compile_db_term_ir`'s `Term.var` value-position case) --
/// correct for 0-arity defs, and no worse than before Phase 0 for
/// anything else.
#[partial]
def ctx_lookup_arity (c : CodegenCtx) (llvm_name : String) : Option I64 := match c {
    CodegenCtx.ctx locals nt nl arities => lookup_arity arities llvm_name,
}

#[partial]
def lookup_arity (arities : List ArityEntry) (llvm_name : String) : Option I64 := match arities {
    List.empty => Option.none,
    List.cons a rest =>
        match a {
            ArityEntry.mk aname aarity =>
                if String.beq aname llvm_name
                then Option.some aarity
                else lookup_arity rest llvm_name,
        },
}

/// Builds the arity table `empty_ctx` needs from a module's own `List
/// Def`, keyed by the exact same `llvm_name` `compile_db_def_ir` gives
/// each def's own compiled LLVM function (`replace_dots_with_underscores`
/// of its module path) -- callers (`compile_db_decls_ir`/
/// `compile_db_module`) always have the full `List Def` in scope before
/// compiling any of them, so this runs once per module compile, not per
/// reference.
#[partial]
def build_arity_table (defs : List Def) : List ArityEntry := match defs {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Def.mk name typ term_ constraints attrs _vis =>
                let llvm_name := replace_dots_with_underscores (module_path_to_str name) in
                let arity := List.length (collect_db_params term_) in
                List.cons (ArityEntry.mk llvm_name arity) (build_arity_table rest),
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

#[partial]
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

#[partial]
def identifier_eq (a : Identifier) (b : Identifier) : Bool := match a {
    Identifier.id as => match b {
        Identifier.id bs => String.beq as bs,
    },
}

/// List of known constructor names that should be compiled as alloc_constructor
/// instead of variable references. These are constructors with 0 or more arguments.
#[partial]
def constructor_names : List String :=
    ["unit", "true", "false", "none", "some", "empty", "cons", "io", "IO.io",
     "trivial", "refl", "ok", "err", "zero", "succ", "nil", "pair"]

#[partial]
def extract_base_name (name : String) : String :=
    let last_dot := string_find_last name "." in
    if I64.gt last_dot (-1)
    then String.slice name (last_dot + 1) (String.length name)
    else name

#[partial]
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
#[partial]
def is_constructor_var (name : String) : Bool :=
    // Extract the last component after the final dot (for qualified names like "Unit.unit")
    let base_name := extract_base_name name in
    check_constructor base_name constructor_names

#[partial]
def check_constructor (name : String) (names : List String) : Bool := match names {
    List.empty => false,
    List.cons hd rest =>
        if String.beq name hd then true
        else check_constructor name rest,
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

#[partial]
def string_find_last_loop (haystack : String) (needle : String) (start_idx : I64) : I64 :=
    if I64.lt start_idx 0 then -1
    else if String.beq (String.slice haystack start_idx (start_idx + String.length needle)) needle then start_idx
    else string_find_last_loop haystack needle (start_idx - 1)

#[partial]
def show_name_ref (name : NameRef) : String := match name {
    NameRef.nid id => show_identifier id,
    NameRef.nmp mp => module_path_to_str mp,
    NameRef.nop op => show_operator op,
}

#[partial]
def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

#[partial]
def cons_val (v : LLVMValue) (vs : List LLVMValue) : List LLVMValue := List.cons v vs

#[partial]
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
    else if String.beq name "I64_to_string" then Option.some NativeOp.op_i64_to_string
    else Option.none

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

/// Check if an LLVMValue is a constant that can be used directly
/// in an instruction (no need for assignment).
#[partial]
def is_llvm_constant (val : LLVMValue) : Bool := match val {
    LLVMValue.int_ n => true,
    LLVMValue.int32_ n => true,
    LLVMValue.bool_ b => true,
    LLVMValue.void_val => true,
    LLVMValue.global_ name => true,
    LLVMValue.fn_ref name => true,
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
                CompileResult.ok ctx1 empty_instrs (LLVMValue.global_ name) empty_blocks empty_funcs (cons_global global empty_globals_list),
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
                                            match compose_seq (Triple.tr instrs_s blocks_s val_s) (Triple.tr tag_and_jump empty_blocks tag_val) {
                                                Triple.tr entry_instrs blocks_s_spliced _ =>
                                                    match build_match_chain ctx_merge tag_val val_s cases merge_label first_check_label {
                                                        MatchChainResult.mk ctx_chain chain_blocks chain_funcs chain_globals phi_pairs =>
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

type MatchChainResult {
    mk (mcr_ctx : CodegenCtx) (mcr_blocks : List LLVMBasicBlock) (mcr_funcs : List LLVMFunction) (mcr_globals : List LLVMGlobal) (mcr_phis : List PhiPair),
}

/// Recursively builds the check/case block chain for every case in
/// order. `check_label` is the label already allocated for THIS case's
/// tag comparison (or, for the last case, its own block directly -- no
/// comparison needed there).
#[partial]
def build_match_chain (c : CodegenCtx) (tag_val : LLVMValue) (scrutinee_val : LLVMValue) (cases : List MatchCase) (merge_label : String) (check_label : String) : MatchChainResult :=
    match cases {
        List.empty =>
            MatchChainResult.mk c empty_blocks empty_funcs empty_globals_list empty_phis,
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
                                                    let tag_of_case := constructor_tag (show_identifier name) in
                                                    let cmp_instr := LLVMInstruction.assign cmp_temp (LLVMValue.icmp_eq tag_val (LLVMValue.int_ tag_of_case)) in
                                                    let branch_instr := LLVMInstruction.branch (LLVMValue.var_ cmp_temp) case_label next_check_label in
                                                    let check_block := LLVMBasicBlock.mk check_label (cons_instr cmp_instr (cons_instr branch_instr empty_instrs)) in
                                                    match build_match_case_block ctx3 scrutinee_val this_case case_label merge_label {
                                                        MatchChainResult.mk ctx4 case_blocks case_funcs case_globals case_phis =>
                                                            match build_match_chain ctx4 tag_val scrutinee_val rest merge_label next_check_label {
                                                                MatchChainResult.mk ctx5 rest_blocks rest_funcs rest_globals rest_phis =>
                                                                    MatchChainResult.mk ctx5
                                                                        (cons_block check_block (append_blocks case_blocks rest_blocks))
                                                                        (append_funcs case_funcs rest_funcs)
                                                                        (append_globals case_globals rest_globals)
                                                                        (append_phis case_phis rest_phis),
                                                            },
                                                    },
                                            },
                                    },
                            },
                    },
            },
    }

type FieldBindResult {
    mk (fbr_ctx : CodegenCtx) (fbr_instrs : List LLVMInstruction),
}

/// Binds every name in a case's pattern args, in order, to a
/// @monad_get_field call on the scrutinee -- e.g. `cons a tail` binds
/// `a` to field 0, `tail` to field 1, matching the order fields were
/// passed to the constructor at allocation time (compile_con_ir's
/// compile_ntv_args processes constructor args in the same order).
#[partial]
def bind_match_fields (c : CodegenCtx) (scrutinee_val : LLVMValue) (args : List Identifier) (idx : I64) : FieldBindResult :=
    match args {
        List.empty => FieldBindResult.mk c empty_instrs,
        List.cons name rest =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 temp =>
                    let field_call := LLVMValue.call "monad_get_field" LLVMType.i64_ (cons_val scrutinee_val (cons_val (LLVMValue.int_ idx) empty_vals)) false in
                    let field_instr := LLVMInstruction.assign temp field_call in
                    let ctx2 := ctx_bind_local ctx1 name (LLVMValue.var_ temp) in
                    match bind_match_fields ctx2 scrutinee_val rest (idx + 1) {
                        FieldBindResult.mk ctx3 rest_instrs =>
                            FieldBindResult.mk ctx3 (cons_instr field_instr rest_instrs),
                    },
            },
    }

/// Compiles a single case's body (after binding its fields) into its own
/// block. If the body's own instructions already end in a terminator
/// (e.g. the body is itself a nested if/match that returns directly, as
/// `List.last`'s `cons a tail => if ... then some a else List.last tail`
/// does), this case never actually reaches the match's merge block --
/// contributing a phi entry for it anyway would reference a
/// non-predecessor block, invalid LLVM IR -- so no phi entry is produced
/// for that case at all.
#[partial]
def build_match_case_block (c : CodegenCtx) (scrutinee_val : LLVMValue) (case_ : MatchCase) (case_label : String) (merge_label : String) : MatchChainResult :=
    match case_ {
        MatchCase.mc _name args body _fp =>
            match bind_match_fields c scrutinee_val args 0 {
                FieldBindResult.mk c1 field_instrs =>
                    match compile_db_term_ir c1 body {
                        CompileResult.ok ctx_r instrs_r val_r blocks_r funcs_r globals_r =>
                            let full_instrs := append_instrs field_instrs instrs_r in
                            let already_terminated := ends_with_terminator full_instrs in
                            let case_block := build_branch_block case_label merge_label full_instrs in
                            let phis :=
                                if already_terminated
                                then empty_phis
                                else cons_phi (PhiPair.mk val_r case_label) empty_phis in
                            MatchChainResult.mk ctx_r (cons_block case_block blocks_r) funcs_r globals_r phis,
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
type NtvArgs {
    mk (ctx : CodegenCtx) (instrs : List LLVMInstruction) (vals : List LLVMValue) (blocks : List LLVMBasicBlock) (funcs : List LLVMFunction) (globals : List LLVMGlobal),
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
                        CompileResult.ok ctx_t instrs val blocks_t funcs_t globals_t =>
                            match compose_seq (Triple.tr acc_instrs acc_blocks acc_val) (Triple.tr instrs blocks_t val) {
                                Triple.tr new_instrs new_blocks new_val =>
                                    compile_ntv_args_go ctx_t rest
                                        new_instrs new_blocks
                                        (append_funcs acc_funcs funcs_t)
                                        (append_globals acc_globals globals_t)
                                        (cons_val val acc_vals)
                                        new_val,
                            },
                    },
                Option.none =>
                    compile_ntv_args_go c rest acc_instrs acc_blocks acc_funcs acc_globals acc_vals acc_val,
            },
        List.empty =>
            NtvArgs.mk c acc_instrs (rev_vals acc_vals empty_vals) acc_blocks acc_funcs acc_globals,
    }

#[partial]
def compile_ntv_args (c : CodegenCtx) (args : List (Option Term)) (acc_instrs : List LLVMInstruction) (acc_vals : List LLVMValue) : NtvArgs :=
    compile_ntv_args_go c args acc_instrs empty_blocks empty_funcs empty_globals_list acc_vals LLVMValue.void_val

#[partial]
def rev_vals (xs : List LLVMValue) (acc : List LLVMValue) : List LLVMValue := match xs {
    List.cons x rest => rev_vals rest (cons_val x acc),
    List.empty => acc,
}

#[partial]
def compile_ntv_ir (c : CodegenCtx) (native : Native) : CompileResult :=
    match native {
        Native.mk name num_args args =>
            let name_str := show_identifier name in
            let llvm_name := extract_base_name name_str in
            let fn_name := String.concat "monad_" llvm_name in
            match compile_ntv_args c args empty_instrs empty_vals {
                NtvArgs.mk ctx_args all_instrs all_vals all_blocks all_funcs all_globals =>
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
                            CompileResult.ok ctx_t (append_instrs all_instrs (cons_instr assign_instr empty_instrs)) (LLVMValue.var_ temp) all_blocks all_funcs all_globals,
                    },
            },
    }

#[partial]
def compile_con_ir (c : CodegenCtx) (con : Con) : CompileResult :=
    match con {
        Con.mk name typ_name num_args args =>
            match compile_ntv_args c args empty_instrs empty_vals {
                NtvArgs.mk ctx_args all_instrs all_vals all_blocks all_funcs all_globals =>
                    match fresh_temp ctx_args {
                        CtxStrPair.mk ctx_t temp =>
                            // Call the @alloc_constructor runtime function
                            // alloc_constructor takes (tag, field_count) and allocates space for fields
                            // The tag is determined by the constructor name
                            let tag_val := constructor_tag (show_identifier name) in
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
                                SetFieldResult.mk ctx_set set_instrs =>
                                    let all_con_instrs := append_instrs all_instrs (cons_instr assign_instr set_instrs) in
                                    CompileResult.ok ctx_set all_con_instrs (LLVMValue.var_ temp) all_blocks all_funcs all_globals,
                            },
                    },
            },
    }

type SetFieldResult {
    mk (sfr_ctx : CodegenCtx) (sfr_instrs : List LLVMInstruction),
}

/// One @monad_set_field call per already-compiled argument value, in
/// order -- the write half of constructor field storage (monad_get_field
/// is the read half, used by match dispatch).
#[partial]
def build_set_field_instrs (obj_val : LLVMValue) (vals : List LLVMValue) (idx : I64) (c : CodegenCtx) : SetFieldResult :=
    match vals {
        List.empty => SetFieldResult.mk c empty_instrs,
        List.cons v rest =>
            match fresh_temp c {
                CtxStrPair.mk ctx1 temp =>
                    let set_call := LLVMValue.call "monad_set_field" LLVMType.i64_ (cons_val obj_val (cons_val (LLVMValue.int_ idx) (cons_val v empty_vals))) false in
                    let set_instr := LLVMInstruction.assign temp set_call in
                    match build_set_field_instrs obj_val rest (idx + 1) ctx1 {
                        SetFieldResult.mk ctx2 rest_instrs =>
                            SetFieldResult.mk ctx2 (cons_instr set_instr rest_instrs),
                    },
            },
    }

type IfLabels {
    mk (ctx_after : CodegenCtx) (then_label : String) (else_label : String) (merge_label : String),
}

#[partial]
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
type Triple {
    tr (t_instrs : List LLVMInstruction) (t_blocks : List LLVMBasicBlock) (t_val : LLVMValue),
}

#[partial]
def compose_seq (a : Triple) (b : Triple) : Triple := match a {
    Triple.tr a_instrs a_blocks a_val => match b {
        Triple.tr b_instrs b_blocks b_val =>
            if ends_with_terminator a_instrs then
                match splice_into_terminal_block a_blocks a_val b_instrs b_val {
                    Option.some rewritten =>
                        Triple.tr a_instrs (append_blocks rewritten b_blocks) b_val,
                    // Couldn't find a's own terminal block (shouldn't
                    // happen given compile_db_if_ir/compile_match_ir's
                    // own invariant that a branching term's LAST
                    // appended block is always closed with `ret <its
                    // own reported val>` — but stay total/safe rather
                    // than crash if that invariant is ever violated by
                    // something not yet accounted for here).
                    Option.none =>
                        Triple.tr (append_instrs a_instrs b_instrs) (append_blocks a_blocks b_blocks) b_val,
                }
            else
                Triple.tr (append_instrs a_instrs b_instrs) (append_blocks a_blocks b_blocks) b_val,
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

/// Structural equality on the one shape that actually arises here: a
/// branching sub-expression's own reported value is always a fresh SSA
/// temp (`LLVMValue.var_`, `compile_db_if_ir`/`build_merge_result`'s own
/// `fresh_temp`-allocated phi result) — every other `LLVMValue` variant
/// falls through to `false`, since none of them are ever what a merge
/// block's own `ret` returns.
#[partial]
def llvm_value_eq (a : LLVMValue) (b : LLVMValue) : Bool := match a {
    LLVMValue.var_ na => match b {
        LLVMValue.var_ nb => String.beq na nb,
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

#[partial]
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
                    CompileResult.ok ctx2 empty_instrs (LLVMValue.fn_ref lam_name) empty_blocks (cons_func lam_func funcs_r) globals_r,
            },
    }

#[partial]
def compile_db_if_ir (c : CodegenCtx) (cond : Term) (then_ : Term) (else_ : Term) : CompileResult :=
    match compile_db_term_ir c cond {
        CompileResult.ok ctx_cond cond_instrs cond_val blocks_cond funcs_cond globals_cond =>
            match ensure_i1_cond ctx_cond cond_instrs blocks_cond cond_val cond {
                BoolCondResult.mk ctx_bool instrs_bool blocks_bool bool_val =>
                    match build_if_labels ctx_bool {
                        IfLabels.mk ctx_branches then_label else_label merge_label =>
                            let branch_instr := LLVMInstruction.branch bool_val then_label else_label in
                            // `if (if p then true else false) then ...`
                            // -- a branching COND itself -- means
                            // `instrs_bool` might already end in a
                            // terminator; splice via `compose_seq`
                            // instead of blindly appending (see its own
                            // doc comment above `ends_with_terminator`).
                            match compose_seq (Triple.tr instrs_bool blocks_bool bool_val) (Triple.tr (cons_instr branch_instr empty_instrs) empty_blocks bool_val) {
                                Triple.tr entry_instrs blocks_bool_spliced _ =>
                                    build_db_if_blocks ctx_branches then_label else_label merge_label then_ else_ entry_instrs blocks_bool_spliced funcs_cond globals_cond,
                            },
                    },
            },
    }

type BoolCondResult {
    mk (bcr_ctx : CodegenCtx) (bcr_instrs : List LLVMInstruction) (bcr_blocks : List LLVMBasicBlock) (bcr_val : LLVMValue),
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
    then BoolCondResult.mk c instrs blocks cond_val
    else
        match fresh_temp c {
            CtxStrPair.mk ctx1 tag_temp =>
                let tag_call := LLVMValue.call "monad_get_tag" LLVMType.i64_ (cons_val cond_val empty_vals) false in
                let tag_instr := LLVMInstruction.assign tag_temp tag_call in
                match fresh_temp ctx1 {
                    CtxStrPair.mk ctx2 bool_temp =>
                        let bool_true_tag := constructor_tag "true" in
                        let cmp_instr := LLVMInstruction.assign bool_temp (LLVMValue.icmp_eq (LLVMValue.var_ tag_temp) (LLVMValue.int_ bool_true_tag)) in
                        let extra := cons_instr tag_instr (cons_instr cmp_instr empty_instrs) in
                        match compose_seq (Triple.tr instrs blocks cond_val) (Triple.tr extra empty_blocks (LLVMValue.var_ bool_temp)) {
                            Triple.tr new_instrs new_blocks new_val =>
                                BoolCondResult.mk ctx2 new_instrs new_blocks new_val,
                        },
                },
        }

#[partial]
def term_is_native_bool_op (t : Term) : Bool := match t {
    Term.app fun_ _arg =>
        match fun_ {
            Term.app fun2 _arg2 =>
                match fun2 {
                    Term.var _idx dbg =>
                        match dbg {
                            DebugName.named id => is_native_bool_op_name (extract_base_name (show_identifier id)),
                            DebugName.unnamed => false,
                        },
                    _ => false,
                },
            _ => false,
        },
    _ => false,
}

#[partial]
def is_native_bool_op_name (name : String) : Bool :=
    String.beq name "I64_eq" || String.beq name "I64_lt" || String.beq name "I64_gt" || String.beq name "I64_ne"

#[partial]
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

#[partial]
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

#[partial]
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
                            // Compile as alloc_constructor with 0 fields.
                            // Must use THIS constructor's own tag (e.g.
                            // `none` = 3), not a hardcoded 0 (`Unit.unit`'s
                            // tag) -- a hardcoded tag made every bare
                            // 0-arg constructor reference indistinguishable
                            // from Unit.unit during match dispatch.
                            match fresh_temp c {
                                CtxStrPair.mk ctx_t temp =>
                                    let tag_val := constructor_tag name in
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
                                        match fresh_temp c {
                                            CtxStrPair.mk ctx_t temp =>
                                                let entry_text := global_fn_ptr_text llvm_name arity in
                                                let box_val := LLVMValue.alloc_closure entry_text arity List.empty in
                                                let assign_instr := LLVMInstruction.assign temp box_val in
                                                CompileResult.ok ctx_t (cons_instr assign_instr empty_instrs) (LLVMValue.var_ temp) empty_blocks empty_funcs empty_globals_list,
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
                CompileResult.ok ctx1 instrs1 val1 blocks1 funcs1 globals1 =>
                    let ctx_bound := ctx_bind_local ctx1 name val1 in
                    match compile_db_term_ir ctx_bound body {
                        CompileResult.ok ctx2 instrs2 val2 blocks2 funcs2 globals2 =>
                            match compose_seq (Triple.tr instrs1 blocks1 val1) (Triple.tr instrs2 blocks2 val2) {
                                Triple.tr combined all_blocks last_val =>
                                    Option.some (CompileResult.ok ctx2 combined last_val all_blocks (append_funcs funcs1 funcs2) (append_globals globals1 globals2)),
                            },
                    },
            },
        _ => Option.none,
    }

#[partial]
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
                    match compose_seq (Triple.tr instrs1 blocks1 val1) (Triple.tr (cons_instr assign_instr empty_instrs) empty_blocks (LLVMValue.var_ temp)) {
                        Triple.tr new_instrs new_blocks _ =>
                            CompileResult.ok ctx_t new_instrs (LLVMValue.var_ temp) new_blocks funcs1 globals1,
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
    NativeOp.op_i64_to_string => "monad_i64_to_string",
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
                    match compose_seq (Triple.tr instrs2 blocks2 val2) (Triple.tr instrs1 blocks1 val1) {
                        Triple.tr combined all_blocks last_val =>
                            let all_funcs := append_funcs funcs2 funcs1 in
                            let all_globals := append_globals globals2 globals1 in
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

type AppSpine {
    mk (as_head : Term) (as_args : List Term),
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
        _ => AppSpine.mk t acc,
    }

/// `sa_last_val` is the running "last-known value" from `compose_seq`'s
/// own accumulation (see `compile_spine_args_go`) -- exposed so THIS
/// spine's own caller (`compile_general_db_call`) can keep correctly
/// splicing after it too, instead of losing track once the args are
/// fully combined.
type SpineArgs {
    mk (sa_ctx : CodegenCtx) (sa_instrs : List LLVMInstruction) (sa_blocks : List LLVMBasicBlock) (sa_funcs : List LLVMFunction) (sa_globals : List LLVMGlobal) (sa_vals : List LLVMValue) (sa_last_val : LLVMValue),
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
        List.empty => SpineArgs.mk c acc_instrs acc_blocks acc_funcs acc_globals (rev_vals acc_vals empty_vals) acc_val,
        List.cons t rest =>
            match compile_db_term_ir c t {
                CompileResult.ok ctx1 instrs1 val1 blocks1 funcs1 globals1 =>
                    match compose_seq (Triple.tr acc_instrs acc_blocks acc_val) (Triple.tr instrs1 blocks1 val1) {
                        Triple.tr new_instrs new_blocks new_val =>
                            compile_spine_args_go ctx1 rest
                                new_instrs new_blocks
                                (append_funcs acc_funcs funcs1)
                                (append_globals acc_globals globals1)
                                (cons_val val1 acc_vals)
                                new_val,
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
                            if is_constructor_var name
                            then compile_db_term_ir c head
                            else
                                // `fn_ref`, not `var_` -- this IS a
                                // statically-known callable global
                                // function name (not a local SSA
                                // register that merely happens to hold
                                // a runtime value) -- see `fn_ref`'s own
                                // doc comment, `lang/codegen/ir.mo`.
                                let llvm_name := replace_dots_with_underscores name in
                                CompileResult.ok c empty_instrs (LLVMValue.fn_ref llvm_name) empty_blocks empty_funcs empty_globals_list,
                    },
                DebugName.unnamed => compile_db_term_ir c head,
            },
        _ => compile_db_term_ir c head,
    }

#[partial]
def compile_general_db_call (c : CodegenCtx) (fun : Term) (arg : Term) : CompileResult :=
    match flatten_app_spine (Term.app fun arg) {
        AppSpine.mk head args =>
            match compile_call_head c head {
                CompileResult.ok ctx_h instrs_h val_h blocks_h funcs_h globals_h =>
                    match compile_spine_args ctx_h args {
                        SpineArgs.mk ctx_a instrs_a blocks_a funcs_a globals_a vals_a last_val_a =>
                            match compose_seq (Triple.tr instrs_h blocks_h val_h) (Triple.tr instrs_a blocks_a last_val_a) {
                                Triple.tr combined all_blocks combined_val =>
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
                                            combine_direct_call ctx_a name vals_a combined all_blocks all_funcs all_globals combined_val,
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
            match compose_seq (Triple.tr combined blocks last_val) (Triple.tr (cons_instr call_instr empty_instrs) empty_blocks (LLVMValue.var_ temp)) {
                Triple.tr new_instrs new_blocks _ =>
                    CompileResult.ok ctx_t new_instrs (LLVMValue.var_ temp) new_blocks funcs globals,
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
            match compose_seq (Triple.tr combined blocks last_val) (Triple.tr (cons_instr call_instr empty_instrs) empty_blocks (LLVMValue.var_ temp)) {
                Triple.tr new_instrs new_blocks _ =>
                    CompileResult.ok ctx_t new_instrs (LLVMValue.var_ temp) new_blocks funcs globals,
            },
    }

#[partial]
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
            match compose_seq (Triple.tr instrs blocks last_val) (Triple.tr (cons_instr arith_instr empty_instrs) empty_blocks (LLVMValue.var_ temp)) {
                Triple.tr new_instrs new_blocks _ =>
                    CompileResult.ok new_ctx new_instrs (LLVMValue.var_ temp) new_blocks funcs globals,
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

type DefResult {
    dr (ctx : CodegenCtx) (funcs : List LLVMFunction) (globals : List LLVMGlobal),
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
#[partial]
def emit_type_head_is_io (t : Term) : Bool := match t {
    Term.var _idx dbg => match dbg {
        DebugName.named id_ => String.beq (show_identifier id_) "IO",
        DebugName.unnamed => false,
    },
    Term.app f _arg => emit_type_head_is_io f,
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
                                DefResult.dr ctx_t (cons_func main_func funcs_r) globals_r,
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
                        let already_terminated := ends_with_terminator instrs_r in
                        let entry_instrs :=
                            if already_terminated
                            then instrs_r
                            else append_instrs instrs_r (cons_instr (LLVMInstruction.ret val_r) empty_instrs) in
                        let entry_block := LLVMBasicBlock.mk "entry" entry_instrs in
                        let all_blocks_raw := append_blocks (cons_block entry_block empty_blocks) blocks_r in
                        let all_blocks := if needs_io_unwrap then unwrap_io_return_blocks all_blocks_raw 0 else all_blocks_raw in
                        let main_func := LLVMFunction.mk fn_name llvm_params LLVMType.i64_ all_blocks true in
                        DefResult.dr ctx_r (cons_func main_func funcs_r) globals_r,
                },
        },
}

/// Compile a list of canonical Defs to LLVM functions.
#[partial]
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
#[partial]
def compile_db_decls_ir (defs : List Def) : LLVMModule :=
    let arities := build_arity_table defs in
    match compile_db_def_list (empty_ctx arities) defs {
        DefResult.dr _ compiled_funcs compiled_globals =>
            let funcs := ren_main_and_wrap compiled_funcs in
            LLVMModule.mk "x86_64-unknown-linux-gnu" compiled_globals funcs runtime_declarations,
    }

/// Compile a list of Decl to a complete LLVM module.
/// Extracts def_d and inductive_d entries, compiles constructors and defs.
#[partial]
def compile_db_module (decl_list : List Decl) : LLVMModule :=
    let defs := extract_defs decl_list in
    let inds := extract_inductives decl_list in
    let ctor_funcs := compile_db_inductive_decls inds in
    let arities := build_arity_table defs in
    match compile_db_def_list (empty_ctx arities) defs {
        DefResult.dr _ compiled_funcs compiled_globals =>
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
#[partial]
def compile_db_inductive_constructors (type_name : String) (constructors : List InductConstructor) : List LLVMFunction := match constructors {
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
                let func := compile_constructor_decl qualified_name field_count in
                cons_func func (compile_db_inductive_constructors type_name rest)
        }
}

/// Compile a single canonical Inductive to LLVM constructor wrapper functions.
#[partial]
def compile_db_inductive (ind : Inductive) : List LLVMFunction := match ind {
    Inductive.mk name params typ constructors attrs _vis =>
        compile_db_inductive_constructors (module_path_to_str name) constructors
}

/// Compile a list of canonical Inductives to LLVM constructor wrapper functions.
#[partial]
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
#[partial]
def compile_constructor_decl (con_name : String) (field_count : I64) : LLVMFunction :=
    let params := build_constructor_params field_count in
    let fields := build_param_fields field_count in
    let alloc_val := LLVMValue.alloc_constructor 0 fields in
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

#[partial]
def bind_params_in_ctx_db (c : CodegenCtx) (params : List Param) : CodegenCtx :=
    bind_params_with_idx_db c params 0

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

/// LLVM wrapper from C main->main_monad. Unused in the current pipeline
/// (the C runtime's main() calls main_monad directly). Kept as reference
/// for future pipeline integration.
#[partial]
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
def cons_decl (d : LLVMDeclaration) (ds : List LLVMDeclaration) : List LLVMDeclaration :=
    List.cons d ds

#[partial]
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
    [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
     d14, d15, d16, d17, d18, d19, d20, d21, d22, d23]

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

/// When the user's main has no params, add an `args` param so the C runtime
/// can pass the command-line argument list. If main already has params (e.g.,
/// `def main (args : List String) : I64`), keep them as-is.
#[partial]
def ren_main_and_wrap (funcs : List LLVMFunction) : List LLVMFunction :=
    rename_main funcs

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
    let funcs := compile_db_inductive_decls (List.cons ind List.empty) in
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
#[partial]
def compile_loaded_modules_to_ir (loaded : LoadedModules) : IO LLVMModule := do {
    let all_mods := get_loaded_all loaded;
    
    // Debug: log loaded modules count
    let module_count := List.length all_mods;
    println ("Loaded " ++ I64.to_string module_count ++ " modules");
    
    // Collect all declarations without module prefixes
    let all_decls := collect_all_decls_from_modules all_mods List.empty;

    // Debug: log def count
    let def_count := List.length all_decls;
    println ("Total defs collected: " ++ I64.to_string def_count);

    // Resolve every infix-operator reference (`+`, `==`, ...) to its
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
    let infixes := collect_infixes all_decls;
    let resolved_decls := resolve_infix_decls infixes all_decls;

    // Dictionary-passing typeclass dispatch (see
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
    let promoted_decls := promote_instance_defs resolved_decls;
    let dict_param_decls := add_constraint_dict_params_decls promoted_decls;

    // Stage 3 of `bootstrapping/unify-check-compile-test-elaboration.md`:
    // try real dictionary-dispatch resolution via the type checker first
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
    let target_mp : ModulePath := match get_loaded_main loaded { ModuleInfo.mk mp_ _ _ => mp_ };
    let scope_data : ScopeData := build_scope_from_decls target_mp dict_param_decls;
    let scope : Scope := { module_id := target_mp, scope := scope_data, parent := Option.none };
    let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
    let elaborated := elaborate_module_decls_best_effort scope dict_param_decls empty_locs;
    let dispatched_decls := resolve_class_calls_decls elaborated;

    // Only compile Defs actually reachable (transitively) from `main` --
    // compiling the FULL 264-def loaded set unconditionally meant any
    // codegen bug anywhere in the whole standard library, reached or
    // not, blocked compiling any program at all. See
    // filter_reachable_decls's own doc comment.
    let reachable_decls := filter_reachable_decls dispatched_decls;
    let reachable_count := List.length reachable_decls;
    println ("Reachable decl_list: " ++ I64.to_string reachable_count);

    // Compile the reachable, infix-resolved declarations
    let mod_ := compile_db_module reachable_decls;
    return mod_
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
    let reachable := reachable_defs_from all_defs (List.cons "main" List.empty) List.empty List.empty in
    List.append (map_inductive_decl all_inds) (map_def_decl reachable)

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
def find_def_by_name (defs : List Def) (name : String) : Option Def := match defs {
    List.empty => Option.none,
    List.cons d rest =>
        if String.beq (def_name_str d) name
        then Option.some d
        else find_def_by_name rest name,
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
#[partial]
def reachable_defs_from (all_defs : List Def) (worklist : List String) (visited : List String) (acc : List Def) : List Def :=
    match worklist {
        List.empty => acc,
        List.cons name rest =>
            if list_contains_str visited name
            then reachable_defs_from all_defs rest visited acc
            else
                match find_def_by_name all_defs name {
                    Option.some d =>
                        let referenced := collect_referenced_names (def_body_term d) List.empty in
                        reachable_defs_from all_defs (List.append referenced rest) (List.cons name visited) (List.cons d acc),
                    Option.none =>
                        reachable_defs_from all_defs rest (List.cons name visited) acc,
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
