/// Small, shared building blocks for the LLVM backend.
///
/// These are the defs the rest of `lang/codegen/` reaches for constantly
/// -- `empty_instrs`/`cons_instr` alone have 39 callers each, and
/// `str_map_lookup` 28. They lived in `lang/codegen/emit.mo` until that
/// file reached 8,204 lines, and they are extracted FIRST because every
/// other candidate extraction pulls them in: nothing else could be split
/// out cleanly while they had no home of their own.
///
/// Deliberately dependency-light -- `lang.types` and `lang.codegen.ir`
/// only -- so that every other backend module can import this one
/// without creating a cycle.
use lang.types {Decl, Identifier}
use lang.codegen.ir {
  LLVMBasicBlock, LLVMFunction, LLVMGlobal, LLVMInstruction, LLVMValue, ParamPair,
}
use std.map {}

#[partial]
def append_vals (a : List LLVMValue) (b : List LLVMValue) : List LLVMValue := match a {
    List.empty => b,
    List.cons hd tl => cons_val hd (append_vals tl b),
}

#[partial]
def identifier_eq (a : Identifier) (b : Identifier) : Bool := match a {
    Identifier.id as => match b {
        Identifier.id bs => String.beq as bs,
    },
}

#[partial]
def cons_val (v : LLVMValue) (vs : List LLVMValue) : List LLVMValue := List.cons v vs

#[partial]
def empty_instrs : List LLVMInstruction := List.empty

#[partial]
def rev_vals (xs : List LLVMValue) (acc : List LLVMValue) : List LLVMValue := match xs {
    List.cons x rest => rev_vals rest (cons_val x acc),
    List.empty => acc,
}

#[partial]
def ident_in_list (xs : List Identifier) (x : Identifier) : Bool := match xs {
    List.empty => false,
    List.cons y rest => if identifier_eq y x then true else ident_in_list rest x,
}

#[partial]
def dedup_idents (names : List Identifier) : List Identifier := dedup_idents_go names List.empty

#[partial]
def dedup_idents_go (names : List Identifier) (seen : List Identifier) : List Identifier := match names {
    List.empty => List.empty,
    List.cons n rest =>
        if ident_in_list seen n
        then dedup_idents_go rest seen
        else List.cons n (dedup_idents_go rest (List.cons n seen)),
}

#[partial]
def append_instrs (a : List LLVMInstruction) (b : List LLVMInstruction) : List LLVMInstruction := match a {
    List.empty => b,
    List.cons hd tl => cons_instr hd (append_instrs tl b),
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
def empty_blocks : List LLVMBasicBlock := List.empty

#[partial]
def cons_block (b : LLVMBasicBlock) (bs : List LLVMBasicBlock) : List LLVMBasicBlock :=
    List.cons b bs

/// `"; "`-join a fail-fast validator's error messages. Unlike
/// `validate_no_unresolved_class_calls` (first message only), a broken
/// compile from the fail-fast validator family usually has a whole
/// FAMILY of defects at once (the self-hosted compiler's own closure
/// references ~20 unwired natives), and naming them one
/// per compile would cost one full ~8-minute self-compile run each.
/// The complete list is the point. Shared by both fail-fast
/// gates: `validate_no_unwired_natives` and
/// `validate_no_undesugared_struct_lits`.
#[partial]
def join_semicolon_msgs (msgs : List String) (acc : String) : String :=
    match msgs {
        List.empty => acc,
        List.cons m rest =>
            if String.beq acc ""
            then join_semicolon_msgs rest m
            else join_semicolon_msgs rest (String.concat acc (String.concat "; " m)),
    }

#[partial]
def empty_vals : List LLVMValue := List.empty

#[partial]
def cons_instr (i : LLVMInstruction) (is : List LLVMInstruction) : List LLVMInstruction :=
    List.cons i is

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
def empty_funcs : List LLVMFunction := List.empty

#[partial]
def cons_func (f : LLVMFunction) (fs : List LLVMFunction) : List LLVMFunction :=
    List.cons f fs

#[partial]
def empty_globals_list : List LLVMGlobal := List.empty

#[partial]
def dedup_strs (xs : List String) : List String := dedup_strs_go xs List.empty

#[partial]
def dedup_strs_go (xs : List String) (seen : List String) : List String := match xs {
    List.empty => List.empty,
    List.cons x rest =>
        if list_contains_str seen x
        then dedup_strs_go rest seen
        else List.cons x (dedup_strs_go rest (List.cons x seen)),
}

/// A `String`-keyed `HashMap` (preferred over `BTreeMap` here for
/// performance -- 16-bucket chaining beats an unbalanced-in-the-worst-
/// case tree walk at this N), bypassing `Map`'s abstract typeclass
/// dispatch (`Map.insert`/`Map.lookup`, the `[Hashable K, BOrd K] Map
/// HashMap` instance, `std/map.mo`) in favor of `HashMap.bucket_of`/
/// `get_bucket`/`set_bucket`/`bucket_insert`/`bucket_lookup` called
/// directly with plain `String.hash`/`String.lt`/`String.gt` (concrete
/// native functions, no class-method resolution at all). Mirrors
/// `lang/scope.mo`'s own `modpath_map_*` helpers exactly (just without
/// their `show_module_path` projection step -- `String` needs none),
/// which document why: calling through `Map`'s generic dispatch resolves
/// `Hashable.hash`/`BOrd.lt`/`BOrd.gt` as abstract class-method
/// references INSIDE `HashMap`'s own generic `[K, V]`-parameterized
/// body, and AGENTS.md's documented evaluator limitation
/// ("`resolve_class_method_instance` picks the FIRST REGISTERED
/// instance", not a type-directed lookup) means these can silently
/// resolve to the WRONG instance whenever invoked from deep within an
/// already-polymorphic call chain -- confirmed as a real, live bug for
/// `ScopeData.def_refs`/`inductives`, not just theoretical.
/// `String.hash`/`String.lt`/`String.gt` need no such dispatch at all
/// (native, already monomorphic), so this sidesteps the whole class of
/// risk rather than merely hoping it doesn't fire here too.
#[partial]
def str_map_empty {V : Type} : HashMap String V := HashMap.map HashMap.empty_buckets

#[partial]
def str_map_insert {V : Type} (key : String) (val : V) (m : HashMap String V) : HashMap String V :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            let bucket := HashMap.get_bucket buckets idx in
            let new_bucket := HashMap.bucket_insert_eq String.beq key val bucket in
            HashMap.map (HashMap.set_bucket buckets idx new_bucket)
    }

#[partial]
def str_map_lookup {V : Type} (key : String) (m : HashMap String V) : Option V :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            let bucket := HashMap.get_bucket buckets idx in
            HashMap.bucket_lookup_eq String.beq key bucket
    }

#[partial]
def list_contains_str (xs : List String) (x : String) : Bool := match xs {
    List.empty => false,
    List.cons hd rest => if String.beq hd x then true else list_contains_str rest x,
}

#[partial]
def append_decls_list (a : List Decl) (b : List Decl) : List Decl := match a {
    List.empty => b,
    List.cons hd tl => List.cons hd (append_decls_list tl b),
}

#[partial]
def drop_last_instr (instrs : List LLVMInstruction) : List LLVMInstruction := match instrs {
    List.empty => List.empty,
    List.cons i rest => match rest {
        List.empty => List.empty,
        List.cons _ _ => List.cons i (drop_last_instr rest),
    },
}
