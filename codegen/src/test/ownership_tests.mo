/// Unit tests for `codegen::ownership`: the ownership verdict, the I10
/// containment fixed point, the drop predicate and the exit-drop insertion.
///
/// These build `Term`/`Inductive`/`Scope` values by hand, so they pin the
/// analysis without a full front end. The end-to-end fixture lives in
/// `init/src/ownership_tests.mo`.
use llvm::ir {LLVMBasicBlock, LLVMInstruction, LLVMValue}
use llvm::strmap {str_map_empty, str_map_insert}
use std::list {List.length}
use lang::types {
    Attribute, DebugName, Decl, Def, Identifier, InductConstructor, Inductive,
    Instance, Literal, ModulePath, Multiplicity, NamePath, Param, Scope, Term,
    TypeConstraint, Visibility, binder_named, sentinel,
}
use lang::scope {build_scope_from_decls}
use lib::ownership {
    DropBinding, OwnershipMode, OwnershipTables, alloc_fn_for_ctor, classify_program,
    drop_fn_for_type, drop_plan_for, insert_drops_before_rets, ownership_mode_of_env,
    ownership_tables_empty, plan_def,
}

def oid (s : String) : Identifier := Identifier.id s

def onp (s : String) : NamePath := NamePath.mk [oid s]

/// A type reference term, the shape `head_name` resolves.
def oty (s : String) : Term := Term.var sentinel (DebugName.named (oid s))

def oparam (n : String) (t : Term) : Param :=
    Param.mk (oid n) t Multiplicity.many Option.none ([] : List Attribute)

#[partial]
def ofields (fs : List (Pair String Term)) (acc : List Param) : List Param :=
    match fs {
        List.empty => List.reverse acc,
        List.cons f rest =>
            match f {
                Pair.pair n t => ofields rest (List.cons (oparam n t) acc),
            },
    }

def octorr (n : String) (fs : List (Pair String Term)) : InductConstructor :=
    InductConstructor.mk (onp n) (ofields fs List.empty) Term.hole

def oinductive (n : String) (params : List Param) (ctors : List InductConstructor) (attrs : List Attribute) : Inductive :=
    Inductive.mk (onp n) params Term.hole ctors attrs Visibility.pub_

def odecl (n : String) (fields : List (Pair String Term)) : Decl :=
    Decl.inductive_d (oinductive n List.empty [octorr (String.concat n "_mk") fields] List.empty)

def oscope : Scope :=
    let mp := ModulePath.mk [oid "ownership_test"] in
    Scope.mk mp (build_scope_from_decls mp List.empty) Option.none false

def tables_owning (name : String) (fn_ : String) : OwnershipTables :=
    { ownership_tables_empty with owned := str_map_insert name fn_ str_map_empty }

// ─── Mode parsing ──────────────────────────────────────────────────────

#[test]
def test_ownership_mode_off_when_unset_or_zero : Bool :=
    match ownership_mode_of_env Option.none {
        OwnershipMode.ownership_off =>
            match ownership_mode_of_env (Option.some "") {
                OwnershipMode.ownership_off =>
                    match ownership_mode_of_env (Option.some "0") {
                        OwnershipMode.ownership_off => true,
                        _ => false,
                    },
                _ => false,
            },
        _ => false,
    }

#[test]
def test_ownership_mode_poison_and_on : Bool :=
    match ownership_mode_of_env (Option.some "poison") {
        OwnershipMode.ownership_poison =>
            match ownership_mode_of_env (Option.some "1") {
                OwnershipMode.ownership_on => true,
                _ => false,
            },
        _ => false,
    }

// ─── Verdict ───────────────────────────────────────────────────────────

#[test]
def test_monomorphic_non_copy_inductive_is_owned : Bool :=
    let tables : OwnershipTables := classify_program oscope [odecl "Box" [Pair.pair "x" (oty "I64")]] in
    match drop_fn_for_type tables (oty "Box") {
        Option.some fn_ => String.beq fn_ "monad_owned_drop_Box",
        Option.none => false,
    }

#[test]
def test_generic_inductive_is_region : Bool :=
    let ind := oinductive "BoxG" [oparam "A" Term.hole] [octorr "boxg" [Pair.pair "x" (oty "A")]] List.empty in
    let tables : OwnershipTables := classify_program oscope [Decl.inductive_d ind] in
    match drop_fn_for_type tables (oty "BoxG") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_nullary_constructor_makes_the_type_region : Bool :=
    let ind := oinductive "MaybeBox" List.empty
        [InductConstructor.mk (onp "mb_none") List.empty Term.hole,
            InductConstructor.mk (onp "mb_some") [oparam "x" (oty "Box")] Term.hole]
        List.empty in
    let box := odecl "Box" [Pair.pair "x" (oty "I64")] in
    let tables : OwnershipTables := classify_program oscope [box, Decl.inductive_d ind] in
    match drop_fn_for_type tables (oty "MaybeBox") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_containment_demotes_a_field_of_a_region_type : Bool :=
    // `MaybeBox` has a nullary constructor, so it is Region; it holds a
    // `Box`, and I10 must demote `Box` with it.
    let ind := oinductive "MaybeBox" List.empty
        [InductConstructor.mk (onp "mb_none") List.empty Term.hole,
            InductConstructor.mk (onp "mb_some") [oparam "x" (oty "Box")] Term.hole]
        List.empty in
    let box := odecl "Box" [Pair.pair "x" (oty "I64")] in
    let tables : OwnershipTables := classify_program oscope [box, Decl.inductive_d ind] in
    match drop_fn_for_type tables (oty "Box") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_containment_demotes_a_type_argument_of_a_region_generic : Bool :=
    let container := oinductive "Container" [oparam "A" Term.hole]
        [octorr "cont" [Pair.pair "v" (oty "A")]] List.empty in
    let box := odecl "Box" [Pair.pair "x" (oty "I64")] in
    // A def whose signature mentions `Container Box`.
    let d := Def.mk (onp "holds") (Term.app (oty "Container") (oty "Box")) Term.hole
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private List.empty in
    let tables : OwnershipTables := classify_program oscope [box, Decl.inductive_d container, Decl.def_d d] in
    match drop_fn_for_type tables (oty "Box") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_a_copy_instance_makes_the_type_region : Bool :=
    let box := odecl "Box" [Pair.pair "x" (oty "I64")] in
    let ins := Instance.mk (oid "copyBox") (onp "Copy") ([] : List TypeConstraint)
        [oty "Box"] Visibility.pub_ ([] : List Param) ([] : List Def) in
    let decls : List Decl := [box, Decl.instance_d ins] in
    let mp := ModulePath.mk [oid "ownership_test"] in
    let sc := Scope.mk mp (build_scope_from_decls mp decls) Option.none false in
    let tables : OwnershipTables := classify_program sc decls in
    match drop_fn_for_type tables (oty "Box") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_region_field_demotes_its_owner : Bool :=
    // `Heap` has a heap constructor (`h_cons`), so it is Region; an Owned
    // cell holding one would hide that pointer from the collector, which
    // does not scan `malloc` blocks. `Holder` must therefore be Region too.
    let heap := oinductive "Heap" List.empty
        [InductConstructor.mk (onp "h_nil") List.empty Term.hole,
            InductConstructor.mk (onp "h_cons") [oparam "x" (oty "I64")] Term.hole]
        List.empty in
    let holder := oinductive "Holder" List.empty [octorr "holder" [Pair.pair "r" (oty "Heap")]] List.empty in
    let tables : OwnershipTables := classify_program oscope [Decl.inductive_d heap, Decl.inductive_d holder] in
    match drop_fn_for_type tables (oty "Holder") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_all_nullary_field_is_exempt : Bool :=
    // `Flag`'s values are static `g_nullary` singletons, which the collector
    // roots; an Owned cell may hold one without demoting itself.
    let flag := oinductive "Flag" List.empty
        [InductConstructor.mk (onp "flag_a") List.empty Term.hole,
            InductConstructor.mk (onp "flag_b") List.empty Term.hole]
        List.empty in
    let holder := oinductive "Holder2" List.empty [octorr "holder2" [Pair.pair "f" (oty "Flag")]] List.empty in
    let tables : OwnershipTables := classify_program oscope [Decl.inductive_d flag, Decl.inductive_d holder] in
    match drop_fn_for_type tables (oty "Holder2") {
        Option.some _ => true,
        Option.none => false,
    }

#[test]
def test_hole_field_fails_closed : Bool :=
    let holder := oinductive "Holder3" List.empty [octorr "holder3" [Pair.pair "h" Term.hole]] List.empty in
    let tables : OwnershipTables := classify_program oscope [Decl.inductive_d holder] in
    match drop_fn_for_type tables (oty "Holder3") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_alloc_site_follows_the_verdict : Bool :=
    let base : OwnershipTables := tables_owning "Box" "monad_owned_drop_Box" in
    let tables : OwnershipTables := { base with ctor_owner := str_map_insert "Box_mk#1" "Box" str_map_empty } in
    let owned : String := alloc_fn_for_ctor tables (oid "Box_mk") (Option.some (onp "Box")) 1 in
    let plain : String := alloc_fn_for_ctor tables (oid "Other_mk") (Option.some (onp "Other")) 1 in
    let by_key : String := alloc_fn_for_ctor tables (oid "Box_mk") Option.none 1 in
    String.beq owned "alloc_constructor_owned"
        && String.beq plain "alloc_constructor"
        && String.beq by_key "alloc_constructor_owned"

// ─── Drop predicate ────────────────────────────────────────────────────

def lam_box_unused : Term :=
    Term.lam (binder_named (oid "x")) (oty "Box") (Term.lit (Literal.str "k"))

def lam_box_used : Term :=
    Term.lam (binder_named (oid "x")) (oty "Box") (Term.var 0 (DebugName.named (oid "x")))

#[test]
def test_unused_owned_param_is_dropped : Bool :=
    let tables : OwnershipTables := tables_owning "Box" "monad_owned_drop_Box" in
    let plan := plan_def tables [oparam "x" (oty "Box")] lam_box_unused in
    match drop_plan_for plan (oid "x") {
        Option.some fn_ => String.beq fn_ "monad_owned_drop_Box",
        Option.none => false,
    }

#[test]
def test_used_owned_param_is_not_dropped : Bool :=
    let tables : OwnershipTables := tables_owning "Box" "monad_owned_drop_Box" in
    let plan := plan_def tables [oparam "x" (oty "Box")] lam_box_used in
    match drop_plan_for plan (oid "x") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_region_param_is_not_dropped : Bool :=
    let tables : OwnershipTables := ownership_tables_empty in
    let plan := plan_def tables [oparam "x" (oty "Box")] lam_box_unused in
    match drop_plan_for plan (oid "x") {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_zero_multiplicity_param_is_not_dropped : Bool :=
    let tables : OwnershipTables := tables_owning "Box" "monad_owned_drop_Box" in
    let p := Param.mk (oid "x") (oty "Box") Multiplicity.zero Option.none ([] : List Attribute) in
    let lam := Term.lam (binder_named (oid "x")) (oty "Box") (Term.lit (Literal.str "k")) in
    let plan := plan_def tables [p] lam in
    match drop_plan_for plan (oid "x") {
        Option.none => true,
        Option.some _ => false,
    }

// ─── Exit-drop insertion ───────────────────────────────────────────────

def odrop_one : DropBinding := DropBinding.mk (oid "x") (LLVMValue.int_ 7) "monad_owned_drop_Box"

#[test]
def test_drop_inserted_before_a_reachable_ret : Bool :=
    let b := LLVMBasicBlock.mk "entry" [LLVMInstruction.ret (LLVMValue.int_ 0)] in
    let out := insert_drops_before_rets [odrop_one] [b] in
    match first_block_instrs out {
        Option.some instrs => ends_with_drop_then_ret instrs,
        Option.none => false,
    }

#[test]
def test_no_drops_leaves_the_block_list_unchanged : Bool :=
    let b := LLVMBasicBlock.mk "entry" [LLVMInstruction.ret (LLVMValue.int_ 0)] in
    let out := insert_drops_before_rets List.empty [b] in
    match first_block_instrs out {
        Option.some instrs => is_bare_ret instrs && I64.beq (List.length out) 1,
        Option.none => false,
    }

#[test]
def test_unreachable_ret_is_not_rewritten : Bool :=
    let entry := LLVMBasicBlock.mk "entry" [LLVMInstruction.ret (LLVMValue.int_ 0)] in
    let dead := LLVMBasicBlock.mk "dead" [LLVMInstruction.ret (LLVMValue.int_ 1)] in
    let out := insert_drops_before_rets [odrop_one] [entry, dead] in
    match second_block_instrs out {
        Option.some dinstrs => is_bare_ret dinstrs,
        Option.none => false,
    }

#[partial]
def first_block_instrs (blocks : List LLVMBasicBlock) : Option (List LLVMInstruction) :=
    match blocks {
        List.empty => Option.none,
        List.cons b _ =>
            match b {
                LLVMBasicBlock.mk _ instrs => Option.some instrs,
            },
    }

#[partial]
def second_block_instrs (blocks : List LLVMBasicBlock) : Option (List LLVMInstruction) :=
    match blocks {
        List.empty => Option.none,
        List.cons _ rest =>
            match rest {
                List.empty => Option.none,
                List.cons b _ =>
                    match b {
                        LLVMBasicBlock.mk _ instrs => Option.some instrs,
                    },
            },
    }

#[partial]
def is_bare_ret (instrs : List LLVMInstruction) : Bool :=
    match instrs {
        List.cons i rest =>
            match i {
                LLVMInstruction.ret _ => List.is_empty rest,
                _ => false,
            },
        List.empty => false,
    }

#[partial]
def ends_with_drop_then_ret (instrs : List LLVMInstruction) : Bool :=
    match List.reverse instrs {
        List.cons first rest =>
            match first {
                LLVMInstruction.ret _ =>
                    match rest {
                        List.cons second _ =>
                            match second {
                                LLVMInstruction.call_void _ => true,
                                _ => false,
                            },
                        _ => false,
                    },
                _ => false,
            },
        List.empty => false,
    }
