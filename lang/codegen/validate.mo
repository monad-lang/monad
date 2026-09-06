/// The fail-fast gates.
///
/// Codegen has several ways to produce a silently WRONG program rather
/// than an error, and each of these exists because one of them actually
/// shipped:
///
/// * an unwired `#[native]` compiles to a "return Unit" stub -- a
///   runtime SIGSEGV, discovered only in the built binary;
/// * a struct literal that best-effort elaboration never desugared
///   compiles to a void placeholder;
/// * two defs sharing an LLVM symbol means one is silently dropped and
///   its callers re-pointed at the other -- the collision that crashed
///   the self-compiled compiler inside `strcmp`;
/// * a call to a symbol nothing defines surfaces only as `llc:
///   undefined value` at the END of a 15-25 minute self-compile, naming
///   one symbol and no call site.
///
/// All four run on the REACHABLE decls, so a bug in dead code cannot
/// block a build that never touches it.
use lang.types {Con, Decl, Def, Literal, MatchCase, Native, Term}
use lang.codegen.ir {
  LLVMBasicBlock, LLVMDeclaration, LLVMFunction, LLVMInstruction, LLVMModule,
  LLVMValue, PhiPair,
}
use lang.codegen.decls {def_name_str, extract_defs}
use lang.codegen.runtime {runtime_native_functions}
use lang.codegen.natives {
  lookup_native_any, native_attr_target_name, native_runtime_fn_name,
  runtime_declarations,
}
use lang.codegen.symbols {module_path_to_str}
use lang.codegen.util {
  dedup_strs, join_semicolon_msgs, str_map_empty, str_map_insert, str_map_lookup,
}
use std.map {}

/// A bodyless `#[native X]` def compiles to a "return Unit" stub unless
/// X is wired into the native backend somewhere -- a
/// `native_runtime_fn_name` entry (the def compiles to a real wrapper
/// calling a runtime `monad_*` function) or an inline `native_op_table`
/// key (`lookup_native_any` on the def's own name, the same lookup every
/// direct call site's own fast path uses). This exact gap has now cost
/// two multi-hour runtime-debugging sessions: `String.length`'s "printed
/// a garbage heap address instead of `3`" repro (see its own doc comment
/// above) and the self-compiled v25 binary's SIGSEGV deep inside
/// `List_reverse_append` -- `String_to_list` stubbed to Unit,
/// `String.ends_with`/`String.reverse` then pattern-matching that Unit
/// object and walking a wild pointer out of `monad_get_field`. In both
/// cases the miscompile was silent and structural: `llc`'s IR verifier
/// passes it, only running the binary finds it. Fail fast instead, over
/// the REACHABLE decls (same reasoning as
/// `validate_no_unresolved_class_calls`'s own doc comment: a bug in dead
/// code the program never uses must not block a compile that works),
/// with the native target and enclosing def named directly.
///
/// Deliberately NOT covered: a native that IS in `native_op_table` still
/// has its stub def emitted (direct calls inline, but a VALUE-position
/// reference -- `List.map I64.to_string ids`, a class-instance method
/// binding -- calls the stub global). That narrower gap needs the def
/// itself to compile a wrapper, not a validator; left alone here rather
/// than false-positive-ing every program that only ever calls it directly.
#[partial]
def validate_no_unwired_natives (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := find_unwired_native_defs (extract_defs decl_list) in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
    }

/// One error message per reachable bodyless `#[native X]` def whose X is
/// wired nowhere -- see `validate_no_unwired_natives`'s own doc comment
/// for the fail-fast contract. Only BODYLESS natives are checked: a
/// real-bodied def compiles a real function whatever its attributes.
#[partial]
def find_unwired_native_defs (defs : List Def) : List String :=
    List.reverse (find_unwired_native_defs_go defs List.empty)

#[partial]
def find_unwired_native_defs_go (defs : List Def) (acc : List String) : List String :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Def.mk name _typ term_ _constraints attrs _vis =>
                    match strip_db_lams term_ {
                        Term.hole =>
                            match native_attr_target_name attrs {
                                Option.some target =>
                                    match native_runtime_fn_name attrs {
                                        Option.some _ => find_unwired_native_defs_go rest acc,
                                        Option.none =>
                                            match lookup_native_any (def_symbol_name name) {
                                                Option.some _ => find_unwired_native_defs_go rest acc,
                                                Option.none =>
                                                    let def_name := module_path_to_str name in
                                                    let head := String.concat "native `" (String.concat target "`") in
                                                    let mid := String.concat " (needed by def `" (String.concat def_name "`)") in
                                                    let msg := String.concat head (String.concat mid " is not wired into the native backend -- it would silently compile to a 'return Unit' stub; add a monad_* runtime function + native_runtime_fn_name entry, or an inline native_op_table key") in
                                                    find_unwired_native_defs_go rest (List.cons msg acc),
                                            },
                                    },
                                Option.none => find_unwired_native_defs_go rest acc,
                            },
                        _ => find_unwired_native_defs_go rest acc,
                    },
            },
    }

/// Fail fast on a struct literal that reached codegen still spelled as
/// `Literal.struct_lit`/`Literal.struct_update` instead of a real
/// `Term.con`.
///
/// `compile_lit_ir` compiles both of those to `void_val` -- a silent
/// placeholder written on the assumption that
/// `lang/typecheck/infer.mo`'s `type_check_struct_lit` ALWAYS desugars
/// them first (see its own doc comment there). That assumption holds
/// only for a def that elaboration actually SUCCEEDED on:
/// `elaborate_module_decls_best_effort` is best-effort by design, and
/// when `type_check` fails for a def it keeps the ORIGINAL, un-desugared
/// decl and codegen proceeds anyway. A bare struct literal with no
/// `: StructName` annotation and no expected type from context (the
/// literal `type_check_struct_lit` rejects with "cannot infer struct
/// type for struct literal") is exactly such a def, and `compile`/
/// `check` typecheck only the TARGET file -- so one written in a
/// DEPENDENCY module is never diagnosed anywhere and goes straight to
/// `void_val`.
///
/// That cost a full ladder rung. `check_file_cached` (lang/module.mo)
/// returned `{ result := { path := ..., diagnostics := ... }, cache :=
/// ... }` under a `return`; the self-compiled binary printed
/// `FAIL   (0 error(s))` -- empty path, and a `diagnostics` value that
/// answered "cons" to `run_check_loop`'s match while `List.length` read
/// it as empty -- then `print_diagnostics` recursed on its garbage tail
/// until the 16MB stack was gone (SIGSEGV, no output, frame-pointer
/// chain destroyed). Same silent-structural-miscompile shape as the
/// unwired-native stubs above: `llc` verifies it, only running the
/// binary finds it.
///
/// Reachable decls only, same reasoning as
/// `validate_no_unwired_natives`. The fix at any reported site is to
/// bind the literal to a local with an explicit type annotation first
/// (AGENTS.md's rule-1 pitfall).
#[partial]
def validate_no_undesugared_struct_lits (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := find_undesugared_struct_lit_defs (extract_defs decl_list) in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
    }

/// One message per reachable def whose body still contains an
/// un-desugared struct literal -- see
/// `validate_no_undesugared_struct_lits`'s own doc comment.
#[partial]
def find_undesugared_struct_lit_defs (defs : List Def) : List String :=
    List.reverse (find_undesugared_struct_lit_defs_go defs List.empty)

#[partial]
def find_undesugared_struct_lit_defs_go (defs : List Def) (acc : List String) : List String :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Def.mk name _typ term_ _constraints _attrs _vis =>
                    if term_has_struct_lit term_
                    then
                        let def_name := module_path_to_str name in
                        let head := String.concat "def `" (String.concat def_name "`") in
                        let msg := String.concat head " contains a struct literal that never desugared to a constructor -- it would silently compile to a void placeholder; give the literal an explicit `: StructName` annotation, or bind it to an annotated local before passing it" in
                        find_undesugared_struct_lit_defs_go rest (List.cons msg acc)
                    else find_undesugared_struct_lit_defs_go rest acc,
            },
    }

/// Total structural walk for a surviving `Literal.struct_lit`/
/// `Literal.struct_update` anywhere inside `t`.
def term_has_struct_lit (t : Term) : Bool := match t {
    Term.var _idx _dbg => false,
    Term.lam _dbg typ body => term_has_struct_lit typ || term_has_struct_lit body,
    Term.forall _dbg kind body => term_has_struct_lit kind || term_has_struct_lit body,
    Term.pi arg ret => term_has_struct_lit arg || term_has_struct_lit ret,
    Term.app fun_ arg_ => term_has_struct_lit fun_ || term_has_struct_lit arg_,
    Term.ntv native => native_has_struct_lit native,
    Term.con con_ => con_has_struct_lit con_,
    Term.lit lit_ => lit_has_struct_lit lit_,
    Term.type_ _universe => false,
    Term.hole => false,
}

def lit_has_struct_lit (l : Literal) : Bool := match l {
    Literal.num _n _suffix => false,
    Literal.flt _text _suffix => false,
    Literal.str _s => false,
    Literal.if_ cond then_ else_ =>
        term_has_struct_lit cond || term_has_struct_lit then_ || term_has_struct_lit else_,
    Literal.match_ scrutinee cases =>
        term_has_struct_lit scrutinee || cases_have_struct_lit cases,
    Literal.struct_lit _fields _type_name => true,
    Literal.struct_update _base _fields => true,
}

#[partial]
def native_has_struct_lit (n : Native) : Bool := match n {
    Native.mk _name _num_args args => opt_terms_have_struct_lit args,
}

#[partial]
def con_has_struct_lit (c : Con) : Bool := match c {
    Con.mk _name _typ_name _num_args args => opt_terms_have_struct_lit args,
}

#[partial]
def opt_terms_have_struct_lit (args : List (Option Term)) : Bool := match args {
    List.empty => false,
    List.cons opt_ rest =>
        match opt_ {
            Option.some t => term_has_struct_lit t || opt_terms_have_struct_lit rest,
            Option.none => opt_terms_have_struct_lit rest,
        },
}

#[partial]
def cases_have_struct_lit (cases : List MatchCase) : Bool := match cases {
    List.empty => false,
    List.cons c rest =>
        match c {
            MatchCase.mc _name _args body _fp =>
                term_has_struct_lit body || cases_have_struct_lit rest,
        },
}

/// One message per LLVM symbol claimed by two or more reachable defs.
#[partial]
def validate_no_colliding_def_symbols (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := colliding_def_symbol_msgs (extract_defs decl_list) str_map_empty in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
    }

#[partial]
def colliding_def_symbol_msgs (defs : List Def) (seen : HashMap String Bool) : List String :=
    match defs {
        List.empty => List.empty,
        List.cons d rest =>
            let sym := def_name_str d in
            match str_map_lookup sym seen {
                Option.some _ =>
                    List.cons (String.concat "two definitions share the LLVM symbol `" (String.concat sym
                        "` -- one of them would be silently dropped; give them distinct names or distinct modules"))
                        (colliding_def_symbol_msgs rest seen),
                Option.none =>
                    if reserved_runtime_symbol sym
                    then List.cons (String.concat "def `" (String.concat sym
                            "` collides with a runtime symbol of the same name -- rename the def"))
                            (colliding_def_symbol_msgs rest (str_map_insert sym true seen))
                    else colliding_def_symbol_msgs rest (str_map_insert sym true seen),
            },
    }

/// The symbols the C runtime and the generated runtime natives already
/// own. A def landing on one of these is dropped by `dedup_funcs_by_name`
/// exactly like a def-vs-def collision -- `compile_db_module_with_debug`
/// concatenates `runtime_native_functions` ahead of the compiled defs,
/// so the runtime one wins and the real def vanishes.
#[partial]
def reserved_runtime_symbol (sym : String) : Bool :=
    if runtime_func_name_matches runtime_native_functions sym then true
    else runtime_decl_name_matches runtime_declarations sym

#[partial]
def runtime_func_name_matches (funcs : List LLVMFunction) (sym : String) : Bool := match funcs {
    List.empty => false,
    List.cons f rest => if String.beq (f.name) sym then true else runtime_func_name_matches rest sym,
}

#[partial]
def runtime_decl_name_matches (decls : List LLVMDeclaration) (sym : String) : Bool := match decls {
    List.empty => false,
    List.cons d rest =>
        match d {
            LLVMDeclaration.mk name _params _ret =>
                if String.beq name sym then true else runtime_decl_name_matches rest sym,
        },
}

/// Every function symbol reachable from `funcs` as a CALL TARGET -- the
/// `fn_name` of every `call`, plus every `fn_ref` (a callee named
/// directly by symbol rather than through a register).
#[partial]
def collect_call_targets (funcs : List LLVMFunction) : List String := match funcs {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            LLVMFunction.mk _name _params _ret _blocks _cc _dbg =>
                List.append (call_targets_in_blocks (f.blocks)) (collect_call_targets rest),
        },
}

#[partial]
def call_targets_in_blocks (bs : List LLVMBasicBlock) : List String := match bs {
    List.empty => List.empty,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk _label instrs =>
                List.append (call_targets_in_instrs instrs) (call_targets_in_blocks rest),
        },
}

#[partial]
def call_targets_in_instrs (is_ : List LLVMInstruction) : List String := match is_ {
    List.empty => List.empty,
    List.cons i rest => List.append (call_targets_in_instr i) (call_targets_in_instrs rest),
}

#[partial]
def call_targets_in_instr (i : LLVMInstruction) : List String := match i {
    LLVMInstruction.assign _t v => call_targets_in_value v,
    LLVMInstruction.ret v => call_targets_in_value v,
    LLVMInstruction.branch c _t _e => call_targets_in_value c,
    LLVMInstruction.store v _pty p => List.append (call_targets_in_value v) (call_targets_in_value p),
    LLVMInstruction.jump _l => List.empty,
    LLVMInstruction.comment _t => List.empty,
}

/// Total walk over `LLVMValue`. Every arm is spelled out rather than
/// falling through a wildcard: a new value constructor that can carry a
/// callee must fail to compile here rather than silently escape the
/// gate.
#[partial]
def call_targets_in_value (v : LLVMValue) : List String := match v {
    LLVMValue.call fn_name _rt args _tail => List.cons fn_name (call_targets_in_values args),
    LLVMValue.fn_ref name => List.cons name List.empty,
    LLVMValue.add a b => call_targets_in_pair a b,
    LLVMValue.sub a b => call_targets_in_pair a b,
    LLVMValue.mul a b => call_targets_in_pair a b,
    LLVMValue.sdiv a b => call_targets_in_pair a b,
    LLVMValue.udiv a b => call_targets_in_pair a b,
    LLVMValue.urem a b => call_targets_in_pair a b,
    LLVMValue.icmp_eq a b => call_targets_in_pair a b,
    LLVMValue.icmp_ne a b => call_targets_in_pair a b,
    LLVMValue.icmp_slt a b => call_targets_in_pair a b,
    LLVMValue.icmp_sgt a b => call_targets_in_pair a b,
    LLVMValue.icmp_ult a b => call_targets_in_pair a b,
    LLVMValue.icmp_ugt a b => call_targets_in_pair a b,
    LLVMValue.zext v2 _f _t => call_targets_in_value v2,
    LLVMValue.trunc v2 _f _t => call_targets_in_value v2,
    LLVMValue.ptrtoint v2 _f _t => call_targets_in_value v2,
    LLVMValue.inttoptr v2 _f _t => call_targets_in_value v2,
    LLVMValue.bitcast v2 _t => call_targets_in_value v2,
    LLVMValue.gep base _idxs => call_targets_in_value base,
    LLVMValue.load _ty _pty p => call_targets_in_value p,
    // `entry` is an already-rendered text fragment (`global_fn_ptr_text`'s
    // `bitcast (... @"name" to i8*)`), not a bare symbol, so the callee
    // it names is not extractable here without re-parsing it. It is
    // always a shim emitted into this same function list by the site
    // that built it, so it cannot dangle -- the env values still get
    // walked.
    LLVMValue.alloc_closure _entry _arity env => call_targets_in_values env,
    LLVMValue.alloc_constructor _tag fields => call_targets_in_values fields,
    LLVMValue.native_op _op args => call_targets_in_values args,
    LLVMValue.phi pairs => call_targets_in_phis pairs,
    LLVMValue.int_ _n => List.empty,
    LLVMValue.int32_ _n => List.empty,
    LLVMValue.bool_ _b => List.empty,
    LLVMValue.void_val => List.empty,
    LLVMValue.var_ _n => List.empty,
    LLVMValue.parm_ _i => List.empty,
    LLVMValue.global_ _n => List.empty,
}

#[partial]
def call_targets_in_pair (a : LLVMValue) (b : LLVMValue) : List String :=
    List.append (call_targets_in_value a) (call_targets_in_value b)

#[partial]
def call_targets_in_values (vs : List LLVMValue) : List String := match vs {
    List.empty => List.empty,
    List.cons v rest => List.append (call_targets_in_value v) (call_targets_in_values rest),
}

#[partial]
def call_targets_in_phis (ps : List PhiPair) : List String := match ps {
    List.empty => List.empty,
    List.cons p rest =>
        match p {
            PhiPair.mk v _label => List.append (call_targets_in_value v) (call_targets_in_phis rest),
        },
}

/// Fail with every call target that has no matching `define` or
/// `declare`, deduplicated (one missing symbol called fifty times is
/// one message, not fifty).
#[partial]
def validate_all_call_targets_defined (m : LLVMModule) : Result String LLVMModule :=
    match m {
        LLVMModule.mk _triple _globals funcs decls _src =>
            let defined := build_defined_symbol_set funcs decls in
            let missing := dedup_strs (missing_call_targets (collect_call_targets funcs) defined) in
            match missing {
                List.empty => Result.ok m,
                List.cons _ _ =>
                    Result.err (String.concat "call to undefined symbol(s): "
                        (String.concat (join_semicolon_msgs missing "")
                            " -- a reference resolved to a name nothing defines; def_symbol_name and ref_symbol_name must agree")),
            },
    }

#[partial]
def build_defined_symbol_set (funcs : List LLVMFunction) (decls : List LLVMDeclaration) : HashMap String Bool :=
    add_decl_symbols decls (add_func_symbols funcs str_map_empty)

#[partial]
def add_func_symbols (funcs : List LLVMFunction) (acc : HashMap String Bool) : HashMap String Bool := match funcs {
    List.empty => acc,
    List.cons f rest => add_func_symbols rest (str_map_insert (f.name) true acc),
}

#[partial]
def add_decl_symbols (decls : List LLVMDeclaration) (acc : HashMap String Bool) : HashMap String Bool := match decls {
    List.empty => acc,
    List.cons d rest =>
        match d {
            LLVMDeclaration.mk name _params _ret => add_decl_symbols rest (str_map_insert name true acc),
        },
}

#[partial]
def missing_call_targets (targets : List String) (defined : HashMap String Bool) : List String := match targets {
    List.empty => List.empty,
    List.cons t rest =>
        match str_map_lookup t defined {
            Option.some _ => missing_call_targets rest defined,
            Option.none => List.cons t (missing_call_targets rest defined),
        },
}

/// Strip lambda/forall prefixes from a de Bruijn Term body.
#[partial]
def strip_db_lams (term_ : Term) : Term := match term_ {
    Term.lam dbg typ body => strip_db_lams body,
    Term.forall dbg kind body => strip_db_lams body,
    _ => term_,
}
