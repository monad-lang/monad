/// Tests moved out of `codegen::emit` so the production module stays readable.

use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use std::bench {Bench.now, Bench.report_since}
use std::map {HashMap}
use std::list {List.any, List.intercalate}
use lang::mote {Mote.toolchain_root}
use lang::types {
    AttrArg, Attribute, Binder, Con, DebugName, Decl, Def, Identifier, InductConstructor,
    Inductive, Literal, LocalScope, Location, MatchCase, ModulePath, Multiplicity,
    NamePath, Native, Operator, Param, Scope, ScopeData, Struct, StructField,
    StructLitField, Term, TypeConstraint, UseFilter, UseItem, Visibility,
    binder_is_explicit, binder_name, binder_named, char_to_string, concrete, empty_attrs,
    group, i64, id_eq,
    ident, param_many, sentinel, show_identifier, show_module_path, term_peel,
    Cubical, face_eq0, face_eq1, hcomp, i0, i1, ijoin, imeet, ineg, interval,
    is_one, it_is_one, pathp, transp, glue, glue_elim, glue_intro,
}
use llvm::ir {
    DbgLoc, LLVMBasicBlock, LLVMDeclaration, LLVMFunction, LLVMGlobal,
    LLVMInstruction, LLVMModule, LLVMType, LLVMValue, NativeOp, ParamPair,
    PhiPair, emit_module, llvm_symbol_ref, llvm_value_type, show_llvm_type
}
use runtime::natives {runtime_native_functions}
use lib::validate {
    build_defined_symbol_set, collect_call_targets, missing_call_targets,
    strip_db_lams, validate_export_defs, validate_no_colliding_def_symbols,
    report_elab_stats, validate_no_undesugared_struct_lits,
    validate_no_undesugared_elims,
    validate_no_monad_externs, validate_no_unwired_natives,
    validate_native_target_availability,
}
use lib::ctors {
    bare_ctor_tag, build_constructor_arity_map,
    build_constructor_arity_map_with_structs, build_constructor_tag_map,
    builtin_ctor_arities, builtin_ctor_tags, constructor_arity, constructor_tag,
    ctor_composite_key, is_constructor_var,
}
use lib::natives {
    NativeWrapKind, lookup_native, lookup_native_any,
    native_op_table, native_runtime_fn_name, runtime_declarations,
    runtime_declarations_for,
}
use llvm::target {TargetKind}
use lib::decls {
    build_def_name_map, collect_all_decls_from_modules, def_name_str, export_names,
    export_pairs, export_roots, extract_defs, extract_inductives, extract_structs,
    filter_reachable_decls, reachable_defs_from,
}
use lib::tco {apply_self_tco}
use lib::qualify {qualified_def_name_str, qualify_modules}
use lib::free_names {collect_referenced_names, free_names_of_term}
use lang::typecheck::traverse {term_map_children}
use lang::elim_lower {elim_to_literal}
use lib::ctx {
    CodegenCtx, CtxInstrsVal, CtxInstrsVals, CtxStrPair, LocalBinding,
    build_arity_table, build_type_level_table, collect_db_params, ctx_bind_local,
    ctx_lookup_arity, ctx_lookup_ctor_arity, ctx_lookup_ctor_tag, ctx_lookup_local,
    ctx_lookup_type_level, ctx_reset_locals, ctx_restore_locals, dbg_loc_of_location,
    empty_ctx, fresh_label, fresh_temp, lookup_binding, resolve_call_name
}
use lib::symbols {
    bare_modpath, def_symbol_name, ends_with_main, extract_base_name,
    bare_npath, mangle_identifiers, name_path_to_str, module_path_to_str,
    ref_symbol_name,
    replace_dots_with_underscores, symbol_identifier,
}
use lang::name_text {unqualify_def_name}
use lang::elaborate {names_of_decls}
use lib::util {
    dedup_idents, dedup_idents_go, drop_last_instr,
    ident_in_list, join_semicolon_msgs
}
use lang::module {
    BestEffortElab, LoadedModules, ModuleInfo, bench_step, best_effort_decls,
    best_effort_errors, best_effort_failed, decl_display_name, elaborate_def_typs, elaborate_module_decls_best_effort,
    elaborate_module_decls_reporting, get_loaded_all, get_loaded_main,
    resolve_open_aliases_in_modules
}
use lang::scope {
    add_constraint_dict_params_decls, alias_map_empty, alias_map_insert,
    alias_map_lookup, build_scope_from_decls, collect_classes, collect_open_aliases,
    modpath_eq, refine_scope_instances, scope_find_inductive,
    resolve_open_alias_decls,
    collect_infixes, promote_instance_defs,
    resolve_infix_decls, strip_all_leading_binders,
    validate_no_unresolved_class_calls,
}
use lang::typecheck::infer {type_head_name, struct_lit_build_args, struct_lit_con_name}
use lang::typecheck::usage {spine_head_name}
use std::log {fail_line, stage}
open IO {println}
open LLVMType {i1_, i8_, i32_, i64_, f32_, f64_, ptr, void}
open LLVMValue {
    add, alloc_closure, alloc_constructor, bitcast, bool_, call, gep, global_,
    icmp_eq, icmp_ne, icmp_sgt, icmp_slt, int32_, int_, inttoptr, load, mul, native_op,
    parm_, phi, ptrtoint, sdiv, sext, sub, trunc, typed, var_, void_val, zext,
}
use lib::emit {
    CompileResult, compile_db_decls_ir, compile_db_decls_ir_with_debug, compile_db_def_ir,
    compile_db_inductive_constructors, compile_db_inductive_decls,
    compile_db_module_with_debug, compile_db_term_ir, constructor_tag_at,
    dbg_loc_of_body, decls_have_no_i8_star, empty_arities,
    ends_with_terminator, i64_ne, prepend_loc_marker,
    validate_reachable_elaborated,
}
use lib::test::support {check_contains, check_count, qtest_def}

#[partial]
def unit_test_param (nm : String) : Param :=
    Param.mk (Identifier.id nm) (Term.sort (SortLevel.concrete 1)) Multiplicity.many Option.none List.empty

/// A `Struct` with one field per name given, as a decl-list-free value
/// (`extract_structs` is what turns real decls into these).
#[partial]
def unit_test_struct (type_name : String) (field_names : List String) : Struct :=
    Struct.mk (Identifier.id type_name)
        (List.map (fn n => StructField.mk (Identifier.id n) (Term.sort (SortLevel.concrete 1)) Option.none Multiplicity.many) field_names)
        List.empty Visibility.package_private

/// Regression tests for `native_runtime_fn_name`/`compile_native_def_wrapper_ir`:
/// a `#[native string_concat]`/`#[native string_eq]`-attributed def
/// (`String.concat`/`String.beq`'s own shape, init/string.mo) must
/// compile to a real call into its whitelisted runtime function, not
/// the generic hole-bodied-native fallback's `alloc_constructor(0, 0)`
/// "return Unit" stub (confirmed as a real gap: that stub was
/// `String.concat`'s own actual compiled body, silently discarding both
/// arguments and producing an empty/meaningless result at runtime).
#[partial]
def native_attr (target : String) : List Attribute :=
    List.cons (Attribute.mk (Identifier.id "native") (List.cons (AttrArg.ident (Identifier.id target)) List.empty)) List.empty

/// A 2-param, hole-bodied `#[native <target>]` def -- `lam_params`
/// (lang/parser.mo) always wraps even a hole body in one lambda per
/// param, so a REAL parsed native def's own body looks exactly like
/// this, not a bare `Term.hole`.
#[partial]
def native_def_fixture (name : String) (target : String) : Def :=
    let body := Term.lam (binder_named (Identifier.id "a")) Term.hole
        (Term.lam (binder_named (Identifier.id "b")) Term.hole Term.hole) in
    Def.mk (NamePath.mk (List.cons (Identifier.id name) List.empty)) Term.hole body
        List.empty (native_attr target) Visibility.package_private List.empty

#[partial]
def compile_native_def_fixture_text (name : String) (target : String) : String :=
    match compile_db_def_ir (empty_ctx empty_arities str_map_empty str_map_empty str_map_empty str_map_empty) (native_def_fixture name target) {
        { ctx := _, funcs := funcs, globals := _, .. } =>
            emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty funcs List.empty Option.none List.empty),
    }

/// `Option.some _ => true` -- a presence test without needing a `BEq`
/// instance for `NativeWrapKind` (there is none, and deriving one just to
/// compare against `Option.none` would be the tail wagging the dog).
#[partial]
def native_wrap_is_some (attrs : List Attribute) : Bool :=
    match native_runtime_fn_name attrs {
        Option.some _ => true,
        Option.none => false,
    }

/// A single, unlocated `myfunc` fixture def -- used by the
/// `compile_db_decls_ir_with_debug` tests below.
#[partial]
def debug_fixture_def : Def :=
    Def.mk (NamePath.mk [Identifier.id "myfunc"]) (Term.sort (SortLevel.concrete 1))
        (Term.lit (Literal.num 42 NumSuffix.i64)) List.empty empty_attrs Visibility.package_private List.empty

/// A def with a source position on an INNER term, as
/// `decls_parser_located` produces.
///
/// Two things this fixture's shape is deliberate about, both learned by
/// getting them wrong first:
///
///   - **The wrapper is on the body, and `strip_db_lams` must keep it.**
///     That helper peels wrappers to see THROUGH them to a binder, but
///     returns the final term wrapped -- `compile_db_def_ir_body` compiles
///     exactly that term, so peeling it there would silently discard the
///     body's own position. Getting this wrong is invisible: the def still
///     compiles and still carries the function-level location.
///   - **The located term is an `if`, not a literal.** A literal compiles to
///     a VALUE and emits no instructions, so there is nothing to attach a
///     position to and `prepend_loc_marker` correctly emits no marker. That
///     is exactly why `factorial`'s `then 1` produces no line-6 entry: the
///     constant is folded into a phi operand.
#[partial]
def located_fixture_def : Def :=
    Def.mk (NamePath.mk [Identifier.id "myfunc"]) (Term.sort (SortLevel.concrete 1))
        (Term.ctx (Location.mk 40 9 7)
            (Term.lit (Literal.if_ (Term.lit (Literal.num 1 NumSuffix.i64))
                (Term.lit (Literal.num 2 NumSuffix.i64))
                (Term.lit (Literal.num 3 NumSuffix.i64)))))
        List.empty empty_attrs Visibility.package_private List.empty

/// `debug_fixture_def` with the position a located parse puts on the
/// body -- line 2, column 3, at offset 5.
#[partial]
def located_num_fixture_def : Def :=
    Def.mk (NamePath.mk [Identifier.id "myfunc"]) (Term.sort (SortLevel.concrete 1))
        (Term.ctx (Location.mk 5 2 3) (Term.lit (Literal.num 42 NumSuffix.i64)))
        List.empty empty_attrs Visibility.package_private List.empty

/// A def whose body is a native Bool comparison over a BRANCHING
/// operand -- `I64.beq (if b then x else y) (-1)` -- the exact shape
/// that ended the bootstrap at `llc` (`lang.types::parse_span_is_unknown`,
/// whose real operand is a struct field access: that compiles as a
/// single-case match with the same entry/check/merge block chain this
/// `if` produces). The comparison's `icmp` gets spliced into the
/// operand's merge block, which `compose_seq` re-closes with
/// `ret <raw i1>`; the def's own entry list ends in the operand's
/// branch, so `already_terminated` is true and the plain-ret boxing
/// (`materialize_branch_val`) never runs.
#[partial]
def native_bool_over_branching_fixture_def : Def :=
    Def.mk (NamePath.mk [Identifier.id "spbeq"]) (Term.sort (SortLevel.concrete 1))
        (Term.lam (binder_named (Identifier.id "b")) (Term.sort (SortLevel.concrete 1))
            (Term.lam (binder_named (Identifier.id "x")) (Term.sort (SortLevel.concrete 1))
                (Term.lam (binder_named (Identifier.id "y")) (Term.sort (SortLevel.concrete 1))
                    (Term.app
                        (Term.app (Term.var 3 (DebugName.named (Identifier.id "I64.beq")))
                            (Term.lit (Literal.if_
                                (Term.var 2 (DebugName.named (Identifier.id "b")))
                                (Term.var 1 (DebugName.named (Identifier.id "x")))
                                (Term.var 0 (DebugName.named (Identifier.id "y"))))))
                        (Term.lit (Literal.num (-1) NumSuffix.i64))))))
        List.empty empty_attrs Visibility.package_private List.empty

#[test]
def test_runtime_decls_not_empty : Bool :=
    match runtime_declarations {
        List.empty => false,
        List.cons x y => true,
    }

/// Every runtime declaration uses the i64 calling convention (see
/// `runtime_declarations`' own CONVENTION comment): the backend holds
/// Strings and pointers as raw i64 values, every emitter types its
/// calls `LLVMType.i64_`, and a declare typed any other way mismatches
/// every call site of that native in the emitted module. This used to
/// be live: 15 declares carried the C header's `i8*` shapes while the
/// module called them all as i64 (malformed IR that the current llc
/// 21.1.8 happens to silently accept; a stricter parser would reject
/// the whole module).
#[test]
def test_runtime_decls_i64_convention : Bool :=
    decls_have_no_i8_star runtime_declarations
        && check_contains (emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty List.empty runtime_declarations Option.none List.empty)) "declare void @monad_set_field(i64, i64, i64)"
        && check_contains (emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty List.empty runtime_declarations Option.none List.empty)) "declare i64 @monad_file_exists(i64)"
        && check_contains (emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty List.empty runtime_declarations Option.none List.empty)) "declare i64 @monad_i64_to_string(i64)"

#[test]
def test_module_emit_has_header : Bool :=
    let text := emit_module (compile_db_decls_ir List.empty) in
    let prefix := String.slice text 0 12 in
    String.beq prefix "; ModuleID ="

#[test]
def test_empty_decls_module : Bool :=
    match (compile_db_decls_ir List.empty) {
        LLVMModule.mk triple globals funcs decl_list debug_source _files =>
            String.beq triple "x86_64-unknown-linux-gnu",
    }

/// The threading itself: the triple the caller passes is the one the header
/// records. Compared against a value the module cannot have got anywhere
/// else, so this fails if `triple` is dropped between here and `LLVMModule.mk`
/// rather than passing on two copies of the same constant.
#[test]
def test_compile_db_module_records_the_passed_triple : Bool :=
    match (compile_db_module_with_debug List.empty Option.none List.empty "aarch64-unknown-linux-gnu") {
        LLVMModule.mk triple _globals _funcs _decls _debug_source _files =>
            String.beq triple "aarch64-unknown-linux-gnu",
    }

#[test]
def test_compile_db_inductive_decls : Bool :=
    let some_name := NamePath.mk (List.cons (Identifier.id "Some") List.empty) in
    let some_ctor := InductConstructor.mk some_name List.empty (Term.sort (SortLevel.concrete 1)) in
    let none_name := NamePath.mk (List.cons (Identifier.id "None") List.empty) in
    let none_ctor := InductConstructor.mk none_name List.empty (Term.sort (SortLevel.concrete 1)) in
    let ctors := List.cons some_ctor (List.cons none_ctor List.empty) in
    let ind_name := NamePath.mk (List.cons (Identifier.id "Option") List.empty) in
    let ind := Inductive.mk ind_name List.empty (Term.sort (SortLevel.concrete 1)) ctors empty_attrs Visibility.package_private in
    let funcs := compile_db_inductive_decls (List.cons ind List.empty) str_map_empty in
    let mod_ := LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty funcs List.empty Option.none List.empty in
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

/// Regression test for the `string_find_last`/`extract_base_name`
/// off-by-length bug (see `extract_base_name`'s own doc comment):
/// `String.slice`'s third argument is a LENGTH, not an end index, so
/// `is_constructor_var`/`constructor_tag`'s dynamic-fallback tier
/// (`build_constructor_tag_map`) silently failed to strip a qualified
/// name's own type prefix, looking up "Option.Some" in a map keyed by
/// the bare "Some" and never finding it. Isolated from the whole self-
/// hosted parse/typecheck/elaborate pipeline (a hand-built `Inductive`,
/// like `test_compile_db_inductive_decls` above) so this test exercises
/// exactly the map-building + lookup mechanism, not elaboration.
#[test]
def test_ctor_tag_map_qualified_name_lookup : Bool :=
    let some_name := NamePath.mk (List.cons (Identifier.id "Some") List.empty) in
    let some_ctor := InductConstructor.mk some_name List.empty (Term.sort (SortLevel.concrete 1)) in
    let none_name := NamePath.mk (List.cons (Identifier.id "None") List.empty) in
    let none_ctor := InductConstructor.mk none_name List.empty (Term.sort (SortLevel.concrete 1)) in
    let ctors := List.cons some_ctor (List.cons none_ctor List.empty) in
    let ind_name := NamePath.mk (List.cons (Identifier.id "Option") List.empty) in
    let ind := Inductive.mk ind_name List.empty (Term.sort (SortLevel.concrete 1)) ctors empty_attrs Visibility.package_private in
    let tag_map := build_constructor_tag_map (List.cons ind List.empty) in
    let c := empty_ctx empty_arities tag_map str_map_empty str_map_empty str_map_empty in
    is_constructor_var c "Option.Some" && is_constructor_var c "Option.None"

/// A struct's implicit `mk` is ARITY-known to codegen even though it
/// stays out of the tag map: `is_constructor_var` answers true for the
/// owner-qualified `Point.mk` a decl-gen macro emits (`std/derive.mo`'s
/// `lens_setter`, via `e_ctor`), and the arity is the struct's field
/// count. Before this tier existed the name was not a constructor at
/// all, so the reference compiled as a call to a function that does not
/// exist -- `examples/derive.mo`'s `llc: use of undefined value
/// '@Point.mk'`. The tag map here is deliberately EMPTY: with no
/// inductive claiming bare `mk` either, the struct tier is the only
/// thing that can answer true.
#[test]
def test_struct_ctor_reference_is_arity_known : Bool :=
    let structs : List Struct := List.cons (unit_test_struct "Point" ["x", "y"]) List.empty in
    let arity_map := build_constructor_arity_map_with_structs List.empty structs in
    let c := empty_ctx empty_arities str_map_empty arity_map str_map_empty str_map_empty in
    is_constructor_var c "Point.mk"
        && I64.beq (constructor_arity c "Point.mk") 2

/// ...and it must ALLOCATE under the tag a struct literal does. A struct
/// literal's tag comes from the bare-name tier (`constructor_tag_at c
/// "mk" arity` -- a struct has no composite key), so a reference that
/// took any other tag would allocate the same shape under a different
/// tag than every `match` on a literal compares against. Checked with
/// another type claiming bare `mk` at a DIFFERENT arity, which is where
/// the two paths could plausibly disagree, and which also pins that the
/// tag is a real table entry rather than the 0 fallback.
#[test]
def test_struct_ctor_reference_shares_the_literals_tag : Bool :=
    let slim_mk := InductConstructor.mk (NamePath.mk (List.cons (Identifier.id "mk") List.empty))
        [unit_test_param "only"] (Term.sort (SortLevel.concrete 1)) in
    let slim := Inductive.mk (NamePath.mk (List.cons (Identifier.id "Slim") List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) [slim_mk] empty_attrs Visibility.package_private in
    let tag_map := build_constructor_tag_map (List.cons slim List.empty) in
    let arity_map := build_constructor_arity_map_with_structs (List.cons slim List.empty) (List.cons (unit_test_struct "Point" ["x", "y"]) List.empty) in
    let c := empty_ctx empty_arities tag_map arity_map str_map_empty str_map_empty in
    let by_reference : I64 := constructor_tag_at c "Point.mk" 2 in
    let by_literal : I64 := constructor_tag_at c "mk" 2 in
    I64.gt by_reference 15
        && I64.beq by_reference by_literal

/// A declared TYPE's NAME in value position (`idT I64 5`). With no local,
/// def or constructor entry it used to reach the 0-arg-call fallback and
/// emit `call i64 @"I64"` for a symbol nothing defines. The type-level
/// table now answers with the inert level immediate.
#[test]
def test_type_name_in_value_position_is_an_inert_level : Bool :=
    let ind := Inductive.mk (NamePath.mk (List.cons (Identifier.id "I64") List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) List.empty empty_attrs Visibility.package_private in
    let levels := build_type_level_table (List.cons ind List.empty) List.empty in
    let c := empty_ctx empty_arities str_map_empty str_map_empty str_map_empty levels in
    let t := Term.var sentinel (DebugName.named (Identifier.id "I64")) in
    match compile_db_term_ir c t {
        CompileResult.ok _ctx _instrs val _blocks _funcs _globals =>
            match val {
                LLVMValue.int_ level => I64.beq level 0,
                _ => false,
            },
    }

/// Composite tag keying (`build_constructor_tag_map` +
/// `constructor_tag_at`): two different types both declaring a `mk`
/// constructor at DIFFERING arities -- the v29 self-compiled binary's
/// 283-way `mk` collision scaled to a hand-built minimum -- must get
/// DISTINCT tags, both past the builtin range; the arity-unknown
/// qualified lookups ("Slim.mk"/"Wide.mk", how a value-position
/// reference is written) must agree with the arity-carrying composite
/// lookups; and the bare name, now claimed at two arities, must still
/// answer `is_constructor_var` (its bare entry is the -1 sentinel).
/// Isolated from the whole self-hosted pipeline like
/// `test_ctor_tag_map_qualified_name_lookup` above so this exercises
/// exactly the map-building + lookup mechanism.
#[test]
def test_ctor_tags_distinguish_same_name_differing_arity : Bool :=
    let slim_mk := InductConstructor.mk (NamePath.mk (List.cons (Identifier.id "mk") List.empty))
        [unit_test_param "only"] (Term.sort (SortLevel.concrete 1)) in
    let slim := Inductive.mk (NamePath.mk (List.cons (Identifier.id "Slim") List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) [slim_mk] empty_attrs Visibility.package_private in
    let wide_mk := InductConstructor.mk (NamePath.mk (List.cons (Identifier.id "mk") List.empty))
        [unit_test_param "a", unit_test_param "b", unit_test_param "c"] (Term.sort (SortLevel.concrete 1)) in
    let wide := Inductive.mk (NamePath.mk (List.cons (Identifier.id "Wide") List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) [wide_mk] empty_attrs Visibility.package_private in
    let tag_map := build_constructor_tag_map (List.cons slim (List.cons wide List.empty)) in
    let arity_map := build_constructor_arity_map (List.cons slim (List.cons wide List.empty)) in
    let c := empty_ctx empty_arities tag_map arity_map str_map_empty str_map_empty in
    let slim_at := constructor_tag_at c "mk" 1 in
    let wide_at := constructor_tag_at c "mk" 3 in
    Bool.not (I64.beq slim_at wide_at)
        && I64.gt slim_at 15
        && I64.gt wide_at 15
        && I64.beq (constructor_tag c "Slim.mk") slim_at
        && I64.beq (constructor_tag c "Wide.mk") wide_at
        && I64.beq (constructor_arity c "Slim.mk") 1
        && I64.beq (constructor_arity c "Wide.mk") 3
        && is_constructor_var c "mk"

/// The whole-program pass names a type with its module (`repro::Tick`),
/// but a value-position reference is written `Tick.exited`. A nullary
/// `Tick.exited` beside `Status.exited (code)` must answer its OWN arity
/// (0, not `Status`'s 1) and tag through the module-less alias; it used
/// to fall to the bare name and compile as a one-field closure, so every
/// `match` on it took `_`.
#[test]
def test_ctor_reference_resolves_through_the_module_less_owner : Bool :=
    let st_exited := InductConstructor.mk (NamePath.mk (List.cons (Identifier.id "exited") List.empty))
        [unit_test_param "code"] (Term.sort (SortLevel.concrete 1)) in
    let status := Inductive.mk (NamePath.mk (List.cons (Identifier.id "repro::Status") List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) [st_exited] empty_attrs Visibility.package_private in
    let tk_waiting := InductConstructor.mk (NamePath.mk (List.cons (Identifier.id "waiting") List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) in
    let tk_exited := InductConstructor.mk (NamePath.mk (List.cons (Identifier.id "exited") List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) in
    let tick := Inductive.mk (NamePath.mk (List.cons (Identifier.id "repro::Tick") List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) [tk_waiting, tk_exited] empty_attrs Visibility.package_private in
    let inds := List.cons status (List.cons tick List.empty) in
    let c := empty_ctx empty_arities (build_constructor_tag_map inds) (build_constructor_arity_map inds) str_map_empty str_map_empty in
    I64.beq (constructor_arity c "Tick.exited") 0
        && I64.beq (constructor_arity c "Status.exited") 1
        && I64.beq (constructor_tag c "Tick.exited") (constructor_tag_at c "exited" 0)
        && I64.beq (constructor_tag c "Status.exited") (constructor_tag_at c "exited" 1)
        && Bool.not (I64.beq (constructor_tag c "Tick.exited") (constructor_tag c "Status.exited"))

#[test]
def test_native_string_concat_calls_runtime_fn_not_unit_stub : Bool :=
    let text := compile_native_def_fixture_text "String.concat" "string_concat" in
    if check_contains text "call i64 @monad_string_concat"
    then not (check_contains text "call i64 @alloc_constructor(i64 0, i64 0)")
    else false

/// `I64.to_string`'s own value-position half: the def IS reachable as an
/// ordinary function value (`list_show I64.to_string xs`, `List.map
/// I64.to_string ids`), and every one of those references reads the
/// def's own compiled body -- which used to be the Unit stub, so the
/// element rendered as the empty string. Its siblings (i32/u8/u64) were
/// already wired here; only i64 was missed, masked by the direct-call
/// inlining that makes the common case work.
#[test]
def test_native_i64_to_string_wraps_value_position_reference : Bool :=
    let text := compile_native_def_fixture_text "I64.to_string" "i64_to_string" in
    if check_contains text "call i64 @monad_i64_to_string"
    then not (check_contains text "call i64 @alloc_constructor(i64 0, i64 0)")
    else false

/// The `I64` arithmetic/comparison family's value-position half -- the
/// same gap as `I64.to_string` above, but a live miscompile rather than a
/// blank string, because its results are consumed as `Bool`/`I64`
/// values. Direct calls inline through `native_op_table`, which is
/// exactly why every earlier wiring pass missed this group; only a
/// value-position reference (`native_i64_bool_binop I64.beq args` in
/// `lang/src/core_eval.mo`) reads the def's own body. See
/// `native_runtime_fn_name`'s `i64_*` group for the full account.
///
/// `i64_eq` is the one that broke the meta-evaluator (`0 == 0` answered
/// false, so every `#[derive]`d `BEq` body took its "different
/// constructor" arm), so it is the one pinned here; the other six are
/// pinned by the same table entry and by
/// `test_native_i64_family_entries_are_wired` below.
#[test]
def test_native_i64_beq_wraps_value_position_reference : Bool :=
    let text := compile_native_def_fixture_text "I64.beq" "i64_eq" in
    if check_contains text "call i64 @monad_i64_eq"
    then not (check_contains text "call i64 @alloc_constructor(i64 0, i64 0)")
    else false

/// `bool_result`, not `passthrough`: a raw 0/1 is not a `Bool` value in
/// this backend (its `Bool` is a tagged Constructor), so the wrapper must
/// allocate one from the comparison's result. Same rule
/// `test_native_string_eq_wraps_raw_result_as_tagged_bool` pins for
/// `String.beq`.
#[test]
def test_native_i64_lt_boxed_as_tagged_bool : Bool :=
    let text := compile_native_def_fixture_text "I64.lt" "i64_lt" in
    if check_contains text "call i64 @monad_i64_lt"
    then check_contains text "call i64 @alloc_constructor"
    else false

/// `I64.add`'s value-position reference is `passthrough` -- one runtime
/// call, no boxing.
#[test]
def test_native_i64_add_wraps_value_position_reference : Bool :=
    let text := compile_native_def_fixture_text "I64.add" "i64_add" in
    if check_contains text "call i64 @monad_i64_add"
    then not (check_contains text "call i64 @alloc_constructor(i64 0, i64 0)")
    else false

/// Every `I64` native `native_op_table` registers must ALSO have a
/// `native_runtime_fn_name` entry -- otherwise it is the value-position
/// stub again, silently. Pins the whole group at once, so a future
/// `I64` op added to one table and forgotten in the other fails here
/// rather than at runtime. `i64_ne` is excluded deliberately: it is dead
/// code with no runtime backing (see `native_op_table`'s own comment).
#[test]
def test_native_i64_family_entries_are_wired : Bool :=
    native_wrap_is_some (native_attr "i64_add")
        && native_wrap_is_some (native_attr "i64_sub")
        && native_wrap_is_some (native_attr "i64_mul")
        && native_wrap_is_some (native_attr "i64_div")
        && native_wrap_is_some (native_attr "i64_eq")
        && native_wrap_is_some (native_attr "i64_lt")
        && native_wrap_is_some (native_attr "i64_gt")

/// `raw_io_passthrough`: the proc natives return the `RawIO` payload
/// ALONE -- exactly ONE `alloc_constructor` (the inner `RawIO.io`). The
/// outer `IO.mk` layer is the `.mo` wrappers' job (`std/src/process.mo`),
/// the same split `IO.pure`/`RawIO.pure` use. An exact count is the only
/// way to tell a raw IO wrap from a doubly-wrapped one in the emitted IR:
/// both call the same runtime fn and both allocate. `proc_stream_fd` is
/// pinned (it kept the pin the removed `proc_read` carried); the other two
/// share its wrap kind and are pinned, as a group, by
/// `test_native_proc_family_entries_are_wired` below.
#[test]
def test_native_proc_stream_fd_wraps_raw_io_not_io : Bool :=
    let text := compile_native_def_fixture_text "Proc.stream_fd" "proc_stream_fd" in
    if check_contains text "call i64 @monad_proc_stream_fd"
    then if I64.beq (check_count text "@alloc_constructor") 1
        then not (check_contains text "@alloc_constructor(i64 0, i64 0)")
        else false
    else false

/// The proc natives (and `file_size`) must have a `native_runtime_fn_name` entry --
/// without one, a value-position reference compiles to the Unit stub,
/// silently (the same gap `test_native_i64_family_entries_are_wired`
/// pins for the `I64` family).
#[test]
def test_native_proc_family_entries_are_wired : Bool :=
    native_wrap_is_some (native_attr "proc_spawn")
        && native_wrap_is_some (native_attr "proc_stream_fd")
        && native_wrap_is_some (native_attr "proc_wait")
        && native_wrap_is_some (native_attr "proc_kill_group")
        && native_wrap_is_some (native_attr "file_size")

#[test]
def test_native_string_eq_wraps_raw_result_as_tagged_bool : Bool :=
    let text := compile_native_def_fixture_text "String.beq" "string_eq" in
    // Must call the real comparison AND allocate a genuine tagged
    // Constructor from its (dynamically computed) result -- NOT return
    // the raw 0/1 i64 directly, which crashes (monad_get_tag on a small
    // integer) the moment it's used as an ordinary Bool value rather
    // than an immediate if-condition.
    if check_contains text "call i64 @monad_string_eq"
    then check_contains text "call i64 @alloc_constructor"
    else false

#[test]
def test_native_unwhitelisted_native_still_gets_unit_stub : Bool :=
    // A native this backend doesn't implement must be completely
    // unaffected by the whitelist -- still the pre-existing stub
    // behavior at THIS level, not a call to a nonexistent runtime
    // function that would fail at link time.
    //
    // The example is a deliberately fictional native rather than a real
    // unimplemented one: every previous choice here
    // (string_slice/string_drop, then string_to_lowercase) eventually
    // got a real implementation and silently flipped this test to
    // failing for the wrong reason. A name no runtime will ever define
    // cannot rot that way.
    //
    // Reaching this stub is now a COMPILE ERROR one level up:
    // `validate_no_unwired_natives` rejects any such def that is
    // actually reachable, precisely because the stub miscompiles
    // silently (see that def's own doc comment). This test pins the
    // fallback the validator guards, which still has to behave sanely
    // for an UNREACHABLE native -- dead code the validator deliberately
    // does not block a compile over.
    let text := compile_native_def_fixture_text "String.no_such_op" "definitely_not_a_real_native" in
    if check_contains text "call i64 @alloc_constructor(i64 0, i64 0)"
    then not (check_contains text "@monad_definitely_not_a_real_native")
    else false

#[test]
def test_compile_db_decls_ir_with_debug_emits_dbg : Bool :=
    let mod_ := compile_db_decls_ir_with_debug (List.cons located_fixture_def List.empty) (Option.some "hello.mo") List.empty in
    let text := emit_module mod_ in
    if check_contains text "!DICompileUnit"
    then (if check_contains text "!DISubprogram" then check_contains text "!dbg !" else false)
    else false

/// Exact-content regression: the body wrapper's captured `Location.mk
/// 5 2 3` (line 2, column 3) must land verbatim in the emitted
/// `!DILocation`, the function name in `!DISubprogram`, and the source
/// path (split into filename/directory by `llvm_split_path`) in `!DIFile`.
#[test]
def test_compile_db_decls_ir_with_debug_exact_content : Bool :=
    let mod_ := compile_db_decls_ir_with_debug (List.cons located_num_fixture_def List.empty) (Option.some "hello.mo") List.empty in
    let text := emit_module mod_ in
    if check_contains text "!DIFile(filename: \"hello.mo\", directory: \".\")"
    then (if check_contains text "name: \"myfunc\""
        then (if check_contains text "line: 2"
            then check_contains text "!DILocation(line: 2, column: 3, scope: !6)"
            else false)
        else false)
    else false

/// A located term emits a DISTINCT `!DILocation` and attaches it to the
/// instructions it produced, instead of everything sharing the function's
/// one location.
///
/// This is the assertion that separates "locations work" from "locations
/// are transparently doing nothing" -- the transparency oracle passes
/// either way, so it cannot be the only check.
///
/// The function's OWN location is the body wrapper's (line 9, column 7)
/// -- a decl-span entry would start at the attributes, while the wrapper
/// starts at the body -- and `dbg_loc_of_body` reads it directly. The
/// wrapper on the body's INNER `if` additionally produces per-instruction
/// markers, which is the distinct-location part this test asserts.
#[test]
def test_located_term_emits_its_own_dilocation : Bool :=
    let located : Def := located_fixture_def in
    let mod_ := compile_db_decls_ir_with_debug (List.cons located List.empty) (Option.some "hello.mo") List.empty in
    let text := emit_module mod_ in
    // The subprogram and its own location node both carry the BODY's
    // position.
    if check_contains text "line: 9, type: !4"
    then check_contains text "!DILocation(line: 9, column: 7, scope: !6)"
    else false

/// A location wrapped around a term that emits NO instructions must emit
/// no marker: one prepended to an empty list ends up at the END of
/// whatever list it is spliced into, where `ends_with_terminator` would
/// read it as a terminator and `drop_last_instr` would silently drop it.
#[test]
def test_located_empty_term_emits_no_marker : Bool :=
    let d : DbgLoc := DbgLoc.mk 9 7 in
    // `Term.hole` compiles to no instructions at all.
    match prepend_loc_marker (Location.mk 40 9 7) List.empty {
        List.empty => true,
        List.cons _ _ => false,
    }

/// The plain (non-`_with_debug`) entry point must emit BYTE-IDENTICAL
/// text (no debug metadata at all) whether or not this feature exists --
/// it always passes `Option.none`/`str_map_empty` through, so this is a
/// straightforward regression guard for that default.
#[test]
def test_compile_db_decls_ir_default_has_no_debug_info : Bool :=
    let mod_ := compile_db_decls_ir (List.cons debug_fixture_def List.empty) in
    let text := emit_module mod_ in
    not (check_contains text "!DICompileUnit")

/// Regression: a Bool-returning def whose body is a native comparison
/// over a BRANCHING operand must box its tail value inside the terminal
/// block before that block's own `ret` -- otherwise the raw `i1` becomes
/// the function's real return and `llc` rejects the module
/// (`'%tN' defined with type 'i1' but expected 'i64'`, the live
/// self-compile failure). The `zext i1 ... to i64` is the boxing's first
/// instruction; without the fix the emitted module contains none at all.
#[test]
def test_native_bool_branching_tail_boxes_ret : Bool :=
    let mod_ := compile_db_decls_ir (List.cons native_bool_over_branching_fixture_def List.empty) in
    let text := emit_module mod_ in
    check_contains text "zext i1"

/// The gate behind the qualification: two defs on one symbol must fail
/// the build, not silently lose one.
#[test]
def test_collision_gate_rejects_two_defs_on_one_symbol : Bool :=
    let d1 := qtest_def "dup" "x" in
    let d2 := qtest_def "dup" "y" in
    match validate_no_colliding_def_symbols (List.cons d1 (List.cons d2 List.empty)) {
        Result.err _ => true,
        Result.ok _ => false,
    }

/// ...and it must not fire on a program that is actually fine.
#[test]
def test_collision_gate_accepts_distinct_symbols : Bool :=
    let d1 := qtest_def "a::dup" "x" in
    let d2 := qtest_def "b::dup" "y" in
    match validate_no_colliding_def_symbols (List.cons d1 (List.cons d2 List.empty)) {
        Result.err _ => false,
        Result.ok _ => true,
    }

/// A def landing on a runtime symbol is the same silent drop --
/// `compile_db_module_with_debug` puts the runtime natives FIRST, so the
/// runtime one wins and the real def disappears.
#[test]
def test_collision_gate_rejects_runtime_symbol_clash : Bool :=
    match validate_no_colliding_def_symbols (List.cons (qtest_def "monad_string_to_list" "x") List.empty) {
        Result.err _ => true,
        Result.ok _ => false,
    }

/// The reachable-elaboration gate is UNCONDITIONAL (standing Item 11): the
/// retried `MONAD_STRICT_ELAB` switch is gone, so no environment can turn it
/// off. A failed decl the reachable closure CONTAINS is an error; the same
/// failure on an unreachable decl is not (a bug in dead code must not block a
/// compile that otherwise works).
#[test]
def test_reachable_elaboration_gate_is_unconditional : Bool :=
    let f_def : Def := Def.mk (NamePath.mk [Identifier.id "f"]) Term.hole Term.hole List.empty List.empty Visibility.package_private List.empty in
    let g_def : Def := Def.mk (NamePath.mk [Identifier.id "g"]) Term.hole Term.hole List.empty List.empty Visibility.package_private List.empty in
    let report : BestEffortElab := { decls := List.empty, failed := ["f"], errors := ["f: boom"] } in
    let hit : Bool := match validate_reachable_elaborated report [Decl.def_d f_def] {
        Result.ok _ => false,
        Result.err _ => true,
    } in
    let miss : Bool := match validate_reachable_elaborated report [Decl.def_d g_def] {
        Result.ok _ => true,
        Result.err _ => false,
    } in
    hit && miss
