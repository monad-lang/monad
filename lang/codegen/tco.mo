/// Self-recursive tail call -> loop rewrite.
///
/// A self-recursive Monad function compiles to a real machine call per
/// iteration, so a scan over a large input exhausts the native stack --
/// the crash class `String_beq` hit on a whole-file `take_while`. This
/// pass finds calls in tail position to the function being compiled and
/// rewrites them into a jump back to a loop header with the arguments
/// re-bound through phis.
///
/// Extracted from `lang/codegen/emit.mo` as the cleanest seam in that
/// file: 40 of its 41 defs are private to the rewrite, and the whole
/// pass has exactly ONE entry point, `apply_self_tco`.
use lang.types {Identifier}
use lang.codegen.ir {
  LLVMBasicBlock, LLVMInstruction, LLVMType, LLVMValue, PhiPair,
}
use lang.codegen.ctx {CodegenCtx, CtxStrPair, fresh_label, fresh_temp}
use lang.codegen.util {
  drop_last_instr,
  str_map_empty, str_map_insert, str_map_lookup,
}
use std.map {}

/// One detected self-recursive tail-call site: `site_block` is the label
/// of the block containing the `assign ret_temp (call <this Def's own
/// name> args false)` instruction that needs rewriting into a loop
/// back-edge instead. `merge_label` is `Option.some <phi-owning block's
/// label>` when this site was found by tracing back through a match/if's
/// own merge `phi` (the overwhelming common case -- every confirmed real
/// repro is match-shaped) -- that block's phi needs `site_block`'s own
/// incoming pair pruned once `site_block`'s terminator is retargeted away
/// from it. `Option.none` when the site was found directly (the Def's
/// WHOLE body is nothing but its own tail call, no branching at all) --
/// there, `site_block` IS the block whose own `ret` is being eliminated,
/// so there's no separate phi to prune. `args` are this call's own
/// argument values (always atomic -- `var_`/`parm_`/a literal/`global_` --
/// per how every call-argument list in this backend is built), captured
/// BEFORE the parameter-substitution rewrite below, later rewritten the
/// same way.
struct SelfTailCallSite {
    site_block : String,
    ret_temp : String,
    merge_label : Option String,
    args : List LLVMValue,
}

struct SelfTcoResult {
    ctx : CodegenCtx,
    blocks : List LLVMBasicBlock,
}

/// Entry point -- called from `compile_db_def_ir_body` on a Def's own
/// fully-composed block list, before `unwrap_io_return_blocks` (so IO-
/// unwrap only ever sees genuine exit-point `ret`s, never an eliminated
/// recursive-call one). A strict no-op (returns `blocks` byte-for-byte
/// unchanged) for the overwhelming majority of Defs, which have no self-
/// recursive tail-call site at all.
#[partial]
def apply_self_tco (ctx : CodegenCtx) (fn_name : String) (arity : I64) (blocks : List LLVMBasicBlock) : SelfTcoResult :=
    let sites := find_self_tail_call_sites fn_name arity blocks in
    match sites {
        List.empty => { ctx := ctx, blocks := blocks },
        List.cons _ _ =>
            match try_apply_self_tco ctx fn_name arity blocks sites {
                Option.some result => result,
                Option.none => { ctx := ctx, blocks := blocks },
            },
    }

/// The real transform, once at least one site is known -- see the 4
/// numbered steps in this section's own top doc comment. Returns
/// `Option.none` (leave `blocks` entirely unchanged, the safe fallback)
/// if pruning a stale phi predecessor would ever leave that phi with ZERO
/// incoming pairs -- i.e. every arm feeding some merge was itself self-
/// recursive, meaning the Def has no reachable base case at all. Such a
/// Def could never have produced a useful answer before this pass either
/// (it's a genuine non-terminating-by-construction bug in the source),
/// so emitting it unchanged (an ordinary, if pointless, infinite-via-
/// stack-growth recursive call) is strictly no worse than before, and
/// never risks emitting invalid IR.
#[partial]
def try_apply_self_tco (ctx : CodegenCtx) (fn_name : String) (arity : I64) (blocks : List LLVMBasicBlock) (sites : List SelfTailCallSite) : Option SelfTcoResult :=
    match mint_loop_names ctx arity {
        { ctx := ctx1, names := loop_names } =>
            let blocks1 := rewrite_parm_in_blocks blocks loop_names in
            let sites1 := rewrite_sites_args sites loop_names in
            match fresh_label ctx1 "tco_loop" {
                CtxStrPair.mk ctx2 header_label =>
                    let stripped_blocks := strip_all_tailcall_sites blocks1 sites1 header_label in
                    match prune_all_phi_predecessors stripped_blocks sites1 {
                        Option.some pruned_blocks =>
                            match split_entry_for_tco pruned_blocks header_label arity loop_names sites1 {
                                Option.some final_blocks =>
                                    let tco : SelfTcoResult := { ctx := ctx2, blocks := final_blocks } in
                                    Option.some tco,
                                Option.none => Option.none,
                            },
                        Option.none => Option.none,
                    },
            },
    }

/// Finds every self-recursive tail-call site in `blocks` (the Def named
/// `fn_name`, of arity `arity`) by building an SSA-temp provenance map
/// once, then tracing every block's own terminal `ret` back through it.
#[partial]
def find_self_tail_call_sites (fn_name : String) (arity : I64) (blocks : List LLVMBasicBlock) : List SelfTailCallSite :=
    let defs := build_ssa_def_map blocks in
    find_sites_in_blocks fn_name arity defs blocks

/// Maps every SSA temp name to the `LLVMValue` it was `assign`ed from --
/// every OTHER instruction shape (`branch`/`jump`/`ret`/`comment`)
/// contributes nothing, since only `assign` ever introduces a new SSA
/// name.
#[partial]
def build_ssa_def_map (blocks : List LLVMBasicBlock) : HashMap String LLVMValue :=
    build_ssa_def_map_blocks blocks str_map_empty

#[partial]
def build_ssa_def_map_blocks (blocks : List LLVMBasicBlock) (acc : HashMap String LLVMValue) : HashMap String LLVMValue := match blocks {
    List.empty => acc,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk _label instrs =>
                build_ssa_def_map_blocks rest (build_ssa_def_map_instrs instrs acc),
        },
}

#[partial]
def build_ssa_def_map_instrs (instrs : List LLVMInstruction) (acc : HashMap String LLVMValue) : HashMap String LLVMValue := match instrs {
    List.empty => acc,
    List.cons i rest =>
        match i {
            LLVMInstruction.assign target value =>
                build_ssa_def_map_instrs rest (str_map_insert target value acc),
            LLVMInstruction.branch _cond _t _e => build_ssa_def_map_instrs rest acc,
            LLVMInstruction.jump _label => build_ssa_def_map_instrs rest acc,
            LLVMInstruction.ret _val => build_ssa_def_map_instrs rest acc,
            LLVMInstruction.store _val _pty _ptr => build_ssa_def_map_instrs rest acc,
            LLVMInstruction.comment _text => build_ssa_def_map_instrs rest acc,
        },
}

#[partial]
def find_sites_in_blocks (fn_name : String) (arity : I64) (defs : HashMap String LLVMValue) (blocks : List LLVMBasicBlock) : List SelfTailCallSite := match blocks {
    List.empty => List.empty,
    List.cons b rest =>
        List.append (find_sites_in_block fn_name arity defs b) (find_sites_in_blocks fn_name arity defs rest),
}

/// Only a block whose own LAST instruction is a bare `ret v` can possibly
/// hold (directly, or via a phi chain) the Def's own final answer -- every
/// other block ends in `jump`/`branch` by this compiler's own established
/// construction (`build_branch_block`/`retarget_terminal_ret` always
/// retarget a would-be-`ret` into a `jump` the moment it's not the Def's
/// OWN outermost answer). A `ret` of a non-`var_` value (a literal, e.g.
/// `build_merge_result`'s own "neither branch reaches merge" dead-code
/// fallback `ret (int_ 0)`) is safely skipped by `trace_tail_value` below,
/// not specially handled here.
#[partial]
def find_sites_in_block (fn_name : String) (arity : I64) (defs : HashMap String LLVMValue) (b : LLVMBasicBlock) : List SelfTailCallSite := match b {
    LLVMBasicBlock.mk label instrs =>
        match List.last instrs {
            Option.some last_instr =>
                match last_instr {
                    LLVMInstruction.ret v => trace_tail_value fn_name arity defs v label,
                    LLVMInstruction.assign _t _v => List.empty,
                    LLVMInstruction.branch _c _t _e => List.empty,
                    LLVMInstruction.jump _l => List.empty,
                    LLVMInstruction.store _v _pty _p => List.empty,
                    LLVMInstruction.comment _t => List.empty,
                },
            Option.none => List.empty,
        },
}

/// Traces `v` (a block's own terminal `ret` value, or -- one recursion
/// level down -- a phi pair's own value) back through `defs`. Only ever
/// matches a `var_` (every call result and every phi result is always
/// assigned to a fresh `var_` temp first in this backend, never left as a
/// bare unassigned expression) -- any other shape (a bare `parm_`/
/// literal/`global_`, or an arithmetic/comparison/cast expression) can't
/// be a self-tail-call and stops the trace on that branch, correctly
/// leaving it untouched.
#[partial]
def trace_tail_value (fn_name : String) (arity : I64) (defs : HashMap String LLVMValue) (v : LLVMValue) (owning_label : String) : List SelfTailCallSite :=
    match v {
        LLVMValue.var_ name =>
            match str_map_lookup name defs {
                Option.some def_val => trace_tail_def fn_name arity defs name def_val owning_label,
                Option.none => List.empty,
            },
        LLVMValue.int_ _n => List.empty,
        LLVMValue.int32_ _n => List.empty,
        LLVMValue.bool_ _b => List.empty,
        LLVMValue.void_val => List.empty,
        LLVMValue.parm_ _idx => List.empty,
        LLVMValue.global_ _n => List.empty,
        LLVMValue.fn_ref _n => List.empty,
        LLVMValue.call _fn _rt _args _tail => List.empty,
        LLVMValue.add _a _b => List.empty,
        LLVMValue.sub _a _b => List.empty,
        LLVMValue.mul _a _b => List.empty,
        LLVMValue.sdiv _a _b => List.empty,
        LLVMValue.udiv _a _b => List.empty,
        LLVMValue.urem _a _b => List.empty,
        LLVMValue.icmp_eq _a _b => List.empty,
        LLVMValue.icmp_ne _a _b => List.empty,
        LLVMValue.icmp_slt _a _b => List.empty,
        LLVMValue.icmp_sgt _a _b => List.empty,
        LLVMValue.icmp_ult _a _b => List.empty,
        LLVMValue.icmp_ugt _a _b => List.empty,
        LLVMValue.zext _v2 _f _t => List.empty,
        LLVMValue.trunc _v2 _f _t => List.empty,
        LLVMValue.ptrtoint _v2 _f _t => List.empty,
        LLVMValue.inttoptr _v2 _f _t => List.empty,
        LLVMValue.phi _pairs => List.empty,
        LLVMValue.gep _base _idxs => List.empty,
        LLVMValue.load _ty _pty _p => List.empty,
        LLVMValue.bitcast _v2 _t => List.empty,
        LLVMValue.alloc_closure _e _a2 _env => List.empty,
        LLVMValue.alloc_constructor _tag _f => List.empty,
        LLVMValue.native_op _op _args => List.empty,
    }

/// What `name`'s own definition (`def_val`) is: either a genuine
/// self-recursive call (site found), a `phi` (recurse one level into its
/// own pairs, still owned by `owning_label` -- see this section's own
/// "Critical wrinkle" doc comment: the phi's `assign` and the `ret` that
/// consumes it always live in the SAME block), or anything else (stop).
#[partial]
def trace_tail_def (fn_name : String) (arity : I64) (defs : HashMap String LLVMValue) (name : String) (def_val : LLVMValue) (owning_label : String) : List SelfTailCallSite :=
    match def_val {
        LLVMValue.call callee _ret_ty args _tail =>
            if String.beq callee fn_name && I64.beq (List.length args) arity
            then List.cons (SelfTailCallSite.mk owning_label name Option.none args) List.empty
            else List.empty,
        LLVMValue.phi pairs => trace_phi_pairs fn_name arity defs pairs owning_label,
        LLVMValue.int_ _n => List.empty,
        LLVMValue.int32_ _n => List.empty,
        LLVMValue.bool_ _b => List.empty,
        LLVMValue.void_val => List.empty,
        LLVMValue.var_ _n => List.empty,
        LLVMValue.parm_ _idx => List.empty,
        LLVMValue.global_ _n => List.empty,
        LLVMValue.fn_ref _n => List.empty,
        LLVMValue.add _a _b => List.empty,
        LLVMValue.sub _a _b => List.empty,
        LLVMValue.mul _a _b => List.empty,
        LLVMValue.sdiv _a _b => List.empty,
        LLVMValue.udiv _a _b => List.empty,
        LLVMValue.urem _a _b => List.empty,
        LLVMValue.icmp_eq _a _b => List.empty,
        LLVMValue.icmp_ne _a _b => List.empty,
        LLVMValue.icmp_slt _a _b => List.empty,
        LLVMValue.icmp_sgt _a _b => List.empty,
        LLVMValue.icmp_ult _a _b => List.empty,
        LLVMValue.icmp_ugt _a _b => List.empty,
        LLVMValue.zext _v2 _f _t => List.empty,
        LLVMValue.trunc _v2 _f _t => List.empty,
        LLVMValue.ptrtoint _v2 _f _t => List.empty,
        LLVMValue.inttoptr _v2 _f _t => List.empty,
        LLVMValue.gep _base _idxs => List.empty,
        LLVMValue.load _ty _pty _p => List.empty,
        LLVMValue.bitcast _v2 _t => List.empty,
        LLVMValue.alloc_closure _e _a2 _env => List.empty,
        LLVMValue.alloc_constructor _tag _f => List.empty,
        LLVMValue.native_op _op _args => List.empty,
    }

#[partial]
def trace_phi_pairs (fn_name : String) (arity : I64) (defs : HashMap String LLVMValue) (pairs : List PhiPair) (merge_label : String) : List SelfTailCallSite := match pairs {
    List.empty => List.empty,
    List.cons p rest =>
        List.append (trace_phi_pair fn_name arity defs p merge_label) (trace_phi_pairs fn_name arity defs rest merge_label),
}

/// `p`'s own `label` is the PREDECESSOR block contributing this pair's
/// value -- the candidate `site_block` if it turns out to be a
/// self-recursive call. `merge_label` (threaded down from the caller) is
/// the block that OWNS this phi -- what needs pruning if so.
#[partial]
def trace_phi_pair (fn_name : String) (arity : I64) (defs : HashMap String LLVMValue) (p : PhiPair) (merge_label : String) : List SelfTailCallSite :=
    match p {
        PhiPair.mk val pred_label =>
            match val {
                LLVMValue.var_ name =>
                    match str_map_lookup name defs {
                        Option.some def_val => trace_phi_pair_def fn_name arity defs name def_val pred_label merge_label,
                        Option.none => List.empty,
                    },
                LLVMValue.int_ _n => List.empty,
                LLVMValue.int32_ _n => List.empty,
                LLVMValue.bool_ _b => List.empty,
                LLVMValue.void_val => List.empty,
                LLVMValue.parm_ _idx => List.empty,
                LLVMValue.global_ _n => List.empty,
                LLVMValue.fn_ref _n => List.empty,
                LLVMValue.call _fn _rt _args _tail => List.empty,
                LLVMValue.add _a _b => List.empty,
                LLVMValue.sub _a _b => List.empty,
                LLVMValue.mul _a _b => List.empty,
                LLVMValue.sdiv _a _b => List.empty,
                LLVMValue.icmp_eq _a _b => List.empty,
                LLVMValue.icmp_ne _a _b => List.empty,
                LLVMValue.icmp_slt _a _b => List.empty,
                LLVMValue.icmp_sgt _a _b => List.empty,
                LLVMValue.zext _v2 _f _t => List.empty,
                LLVMValue.trunc _v2 _f _t => List.empty,
                LLVMValue.ptrtoint _v2 _f _t => List.empty,
        LLVMValue.inttoptr _v2 _f _t => List.empty,
                LLVMValue.phi _pairs => List.empty,
                LLVMValue.gep _base _idxs => List.empty,
                LLVMValue.load _ty _pty _p2 => List.empty,
                LLVMValue.bitcast _v2 _t => List.empty,
                LLVMValue.alloc_closure _e _a2 _env => List.empty,
                LLVMValue.alloc_constructor _tag _f => List.empty,
                LLVMValue.native_op _op _args => List.empty,
            },
    }

/// A nested match-in-match: `def_val` resolving to ANOTHER `phi` means
/// `pred_label`'s own block is itself a nested if/match's merge block
/// (`retarget_terminal_ret` bubbles a nested merge's own `ret` up to the
/// OUTER merge one hop at a time, per this file's own established
/// invariant -- never skips a level), so recurse into ITS pairs, now
/// owned by `pred_label`.
#[partial]
def trace_phi_pair_def (fn_name : String) (arity : I64) (defs : HashMap String LLVMValue) (name : String) (def_val : LLVMValue) (pred_label : String) (merge_label : String) : List SelfTailCallSite :=
    match def_val {
        LLVMValue.call callee _ret_ty args _tail =>
            if String.beq callee fn_name && I64.beq (List.length args) arity
            then List.cons (SelfTailCallSite.mk pred_label name (Option.some merge_label) args) List.empty
            else List.empty,
        LLVMValue.phi pairs2 => trace_phi_pairs fn_name arity defs pairs2 pred_label,
        LLVMValue.int_ _n => List.empty,
        LLVMValue.int32_ _n => List.empty,
        LLVMValue.bool_ _b => List.empty,
        LLVMValue.void_val => List.empty,
        LLVMValue.var_ _n => List.empty,
        LLVMValue.parm_ _idx => List.empty,
        LLVMValue.global_ _n => List.empty,
        LLVMValue.fn_ref _n => List.empty,
        LLVMValue.add _a _b => List.empty,
        LLVMValue.sub _a _b => List.empty,
        LLVMValue.mul _a _b => List.empty,
        LLVMValue.sdiv _a _b => List.empty,
        LLVMValue.udiv _a _b => List.empty,
        LLVMValue.urem _a _b => List.empty,
        LLVMValue.icmp_eq _a _b => List.empty,
        LLVMValue.icmp_ne _a _b => List.empty,
        LLVMValue.icmp_slt _a _b => List.empty,
        LLVMValue.icmp_sgt _a _b => List.empty,
        LLVMValue.icmp_ult _a _b => List.empty,
        LLVMValue.icmp_ugt _a _b => List.empty,
        LLVMValue.zext _v2 _f _t => List.empty,
        LLVMValue.trunc _v2 _f _t => List.empty,
        LLVMValue.ptrtoint _v2 _f _t => List.empty,
        LLVMValue.inttoptr _v2 _f _t => List.empty,
        LLVMValue.gep _base _idxs => List.empty,
        LLVMValue.load _ty _pty _p => List.empty,
        LLVMValue.bitcast _v2 _t => List.empty,
        LLVMValue.alloc_closure _e _a2 _env => List.empty,
        LLVMValue.alloc_constructor _tag _f => List.empty,
        LLVMValue.native_op _op _args => List.empty,
    }

struct LoopNamesResult {
    ctx : CodegenCtx,
    names : List String,
}

/// Mints `arity` fresh SSA names, one per loop-carried parameter --
/// `fresh_temp`'s own counter is module-global (never reset per-Def, see
/// its own doc comment), so these are guaranteed collision-free against
/// every other name in the whole module compile.
#[partial]
def mint_loop_names (ctx : CodegenCtx) (arity : I64) : LoopNamesResult :=
    if I64.lt arity 1
    then { ctx := ctx, names := List.empty }
    else
        match fresh_temp ctx {
            CtxStrPair.mk ctx1 nm =>
                match mint_loop_names ctx1 (arity - 1) {
                    { ctx := ctx2, names := rest } => { ctx := ctx2, names := List.cons nm rest },
                },
        }

/// Substitutes every `parm_ idx` with `var_ loop_names[idx]`, EXHAUSTIVE
/// over every `LLVMValue` variant (unlike `llvm_value_eq`'s deliberately
/// NARROW match a few hundred lines up -- that function only needs to
/// recognize a handful of ATOMIC "running composed value" shapes; this
/// one must rewrite `parm_` wherever it occurs, however deeply nested
/// inside an arbitrary expression). A missed variant here would be a
/// SILENT correctness bug (a stale, iteration-0 parameter value read on
/// every later loop iteration), not a compile error -- every arm is
/// listed explicitly, no wildcard, on purpose.
#[partial]
def rewrite_parm_to_loopvar (v : LLVMValue) (loop_names : List String) : LLVMValue :=
    match v {
        LLVMValue.parm_ idx =>
            match List.get idx loop_names {
                Option.some nm => LLVMValue.var_ nm,
                Option.none => v,
            },
        LLVMValue.int_ _n => v,
        LLVMValue.int32_ _n => v,
        LLVMValue.bool_ _b => v,
        LLVMValue.void_val => v,
        LLVMValue.var_ _n => v,
        LLVMValue.global_ _n => v,
        LLVMValue.fn_ref _n => v,
        LLVMValue.call fn_name ret_ty args tail =>
            LLVMValue.call fn_name ret_ty (rewrite_parm_list args loop_names) tail,
        LLVMValue.add a b => LLVMValue.add (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.sub a b => LLVMValue.sub (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.mul a b => LLVMValue.mul (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.sdiv a b => LLVMValue.sdiv (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.udiv a b => LLVMValue.udiv (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.urem a b => LLVMValue.urem (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.icmp_eq a b => LLVMValue.icmp_eq (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.icmp_ne a b => LLVMValue.icmp_ne (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.icmp_slt a b => LLVMValue.icmp_slt (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.icmp_sgt a b => LLVMValue.icmp_sgt (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.icmp_ult a b => LLVMValue.icmp_ult (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.icmp_ugt a b => LLVMValue.icmp_ugt (rewrite_parm_to_loopvar a loop_names) (rewrite_parm_to_loopvar b loop_names),
        LLVMValue.zext val from_ty to_ty => LLVMValue.zext (rewrite_parm_to_loopvar val loop_names) from_ty to_ty,
        LLVMValue.trunc val from_ty to_ty => LLVMValue.trunc (rewrite_parm_to_loopvar val loop_names) from_ty to_ty,
        LLVMValue.ptrtoint val from_ty to_ty => LLVMValue.ptrtoint (rewrite_parm_to_loopvar val loop_names) from_ty to_ty,
        LLVMValue.inttoptr val from_ty to_ty => LLVMValue.inttoptr (rewrite_parm_to_loopvar val loop_names) from_ty to_ty,
        LLVMValue.phi pairs => LLVMValue.phi (rewrite_parm_in_phi_pairs pairs loop_names),
        LLVMValue.gep base indices => LLVMValue.gep (rewrite_parm_to_loopvar base loop_names) indices,
        LLVMValue.load ty pty ptr_ => LLVMValue.load ty pty (rewrite_parm_to_loopvar ptr_ loop_names),
        LLVMValue.bitcast val to_ty => LLVMValue.bitcast (rewrite_parm_to_loopvar val loop_names) to_ty,
        LLVMValue.alloc_closure entry ar env => LLVMValue.alloc_closure entry ar (rewrite_parm_list env loop_names),
        LLVMValue.alloc_constructor tag fields => LLVMValue.alloc_constructor tag (rewrite_parm_list fields loop_names),
        LLVMValue.native_op op args => LLVMValue.native_op op (rewrite_parm_list args loop_names),
    }

#[partial]
def rewrite_parm_list (vs : List LLVMValue) (loop_names : List String) : List LLVMValue := match vs {
    List.empty => List.empty,
    List.cons v rest => List.cons (rewrite_parm_to_loopvar v loop_names) (rewrite_parm_list rest loop_names),
}

#[partial]
def rewrite_parm_in_phi_pairs (pairs : List PhiPair) (loop_names : List String) : List PhiPair := match pairs {
    List.empty => List.empty,
    List.cons p rest => List.cons (rewrite_parm_in_phi_pair p loop_names) (rewrite_parm_in_phi_pairs rest loop_names),
}

#[partial]
def rewrite_parm_in_phi_pair (p : PhiPair) (loop_names : List String) : PhiPair := match p {
    PhiPair.mk val label => PhiPair.mk (rewrite_parm_to_loopvar val loop_names) label,
}

#[partial]
def rewrite_parm_in_instr (i : LLVMInstruction) (loop_names : List String) : LLVMInstruction := match i {
    LLVMInstruction.assign target value => LLVMInstruction.assign target (rewrite_parm_to_loopvar value loop_names),
    LLVMInstruction.branch cond then_label else_label => LLVMInstruction.branch (rewrite_parm_to_loopvar cond loop_names) then_label else_label,
    LLVMInstruction.jump label => LLVMInstruction.jump label,
    LLVMInstruction.ret val => LLVMInstruction.ret (rewrite_parm_to_loopvar val loop_names),
    LLVMInstruction.store val pty ptr_ => LLVMInstruction.store (rewrite_parm_to_loopvar val loop_names) pty (rewrite_parm_to_loopvar ptr_ loop_names),
    LLVMInstruction.comment text => LLVMInstruction.comment text,
}

#[partial]
def rewrite_parm_in_instrs (instrs : List LLVMInstruction) (loop_names : List String) : List LLVMInstruction := match instrs {
    List.empty => List.empty,
    List.cons i rest => List.cons (rewrite_parm_in_instr i loop_names) (rewrite_parm_in_instrs rest loop_names),
}

#[partial]
def rewrite_parm_in_block (b : LLVMBasicBlock) (loop_names : List String) : LLVMBasicBlock := match b {
    LLVMBasicBlock.mk label instrs => LLVMBasicBlock.mk label (rewrite_parm_in_instrs instrs loop_names),
}

#[partial]
def rewrite_parm_in_blocks (blocks : List LLVMBasicBlock) (loop_names : List String) : List LLVMBasicBlock := match blocks {
    List.empty => List.empty,
    List.cons b rest => List.cons (rewrite_parm_in_block b loop_names) (rewrite_parm_in_blocks rest loop_names),
}

/// `sites` were captured (`find_self_tail_call_sites`) from the ORIGINAL,
/// pre-rewrite blocks -- their own `args` need the identical `parm_` ->
/// `var_ loop_names[idx]` substitution applied directly (not re-derived
/// by re-scanning), so a recursive call that passes a parameter STRAIGHT
/// THROUGH unchanged (e.g. `remove_quotes_loop s new_acc`, param 1 of 2)
/// correctly feeds the header phi the CURRENT loop iteration's value
/// (`var_ loop_names[idx]`) rather than the stale original argument
/// register (`parm_ idx`).
#[partial]
def rewrite_sites_args (sites : List SelfTailCallSite) (loop_names : List String) : List SelfTailCallSite := match sites {
    List.empty => List.empty,
    List.cons s rest =>
        let s2 := { s with args := rewrite_parm_list s.args loop_names } in
        List.cons s2 (rewrite_sites_args rest loop_names),
}

#[partial]
def strip_all_tailcall_sites (blocks : List LLVMBasicBlock) (sites : List SelfTailCallSite) (header_label : String) : List LLVMBasicBlock := match sites {
    List.empty => blocks,
    List.cons s rest => strip_all_tailcall_sites (strip_one_tailcall_site blocks s header_label) rest header_label,
}

#[partial]
def strip_one_tailcall_site (blocks : List LLVMBasicBlock) (site : SelfTailCallSite) (header_label : String) : List LLVMBasicBlock := match blocks {
    List.empty => List.empty,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk label instrs =>
                if String.beq label site.site_block
                then List.cons (LLVMBasicBlock.mk label (strip_tailcall_site instrs site.ret_temp header_label)) rest
                else List.cons b (strip_one_tailcall_site rest site header_label),
        },
}

/// Removes the `assign ret_temp (call ...)` instruction (wherever it
/// falls in the block -- not assumed adjacent to the terminator) and
/// replaces whatever the block's own CURRENT last instruction is (a
/// `ret`, for a Def whose whole body is its own tail call with no
/// branching; a `jump merge_label`, for the common match/if-arm case)
/// with `jump header_label`.
#[partial]
def strip_tailcall_site (instrs : List LLVMInstruction) (ret_temp : String) (header_label : String) : List LLVMInstruction :=
    let without_call := remove_assign_of instrs ret_temp in
    let without_term := drop_last_instr without_call in
    List.append without_term (List.cons (LLVMInstruction.jump header_label) List.empty)

#[partial]
def remove_assign_of (instrs : List LLVMInstruction) (target : String) : List LLVMInstruction := match instrs {
    List.empty => List.empty,
    List.cons i rest =>
        match i {
            LLVMInstruction.assign t _v =>
                if String.beq t target
                then rest
                else List.cons i (remove_assign_of rest target),
            LLVMInstruction.branch _c _tl _el => List.cons i (remove_assign_of rest target),
            LLVMInstruction.jump _l => List.cons i (remove_assign_of rest target),
            LLVMInstruction.ret _v => List.cons i (remove_assign_of rest target),
            LLVMInstruction.store _val _pty _ptr => List.cons i (remove_assign_of rest target),
            LLVMInstruction.comment _t => List.cons i (remove_assign_of rest target),
        },
}

/// Prunes each site's stale incoming phi pair (only for sites found via a
/// phi, `merge_label := Option.some m`) -- `Option.none` bubbles up
/// (abort the whole transform) the instant any single pruning would empty
/// a phi. See `try_apply_self_tco`'s own doc comment for why that's safe.
#[partial]
def prune_all_phi_predecessors (blocks : List LLVMBasicBlock) (sites : List SelfTailCallSite) : Option (List LLVMBasicBlock) := match sites {
    List.empty => Option.some blocks,
    List.cons s rest =>
        match s.merge_label {
            Option.some m =>
                match prune_phi_predecessor blocks m s.site_block {
                    Option.some pruned => prune_all_phi_predecessors pruned rest,
                    Option.none => Option.none,
                },
            Option.none => prune_all_phi_predecessors blocks rest,
        },
}

#[partial]
def prune_phi_predecessor (blocks : List LLVMBasicBlock) (merge_label : String) (stale_label : String) : Option (List LLVMBasicBlock) := match blocks {
    List.empty => Option.some List.empty,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk label instrs =>
                if String.beq label merge_label
                then
                    match prune_phi_in_instrs instrs stale_label {
                        Option.some new_instrs => Option.some (List.cons (LLVMBasicBlock.mk label new_instrs) rest),
                        Option.none => Option.none,
                    }
                else
                    match prune_phi_predecessor rest merge_label stale_label {
                        Option.some pruned => Option.some (List.cons b pruned),
                        Option.none => Option.none,
                    },
        },
}

#[partial]
def prune_phi_in_instrs (instrs : List LLVMInstruction) (stale_label : String) : Option (List LLVMInstruction) := match instrs {
    List.empty => Option.some List.empty,
    List.cons i rest =>
        match i {
            LLVMInstruction.assign target value =>
                match value {
                    LLVMValue.phi pairs =>
                        let pairs2 := remove_phi_pair_with_label pairs stale_label in
                        if List.is_empty pairs2
                        then Option.none
                        else Option.some (List.cons (LLVMInstruction.assign target (LLVMValue.phi pairs2)) rest),
                    LLVMValue.int_ _n => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.int32_ _n => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.bool_ _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.void_val => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.var_ _n => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.parm_ _idx => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.global_ _n => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.fn_ref _n => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.call _fn _rt _args _tail => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.add _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.sub _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.mul _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.sdiv _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.udiv _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.urem _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.icmp_eq _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.icmp_ne _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.icmp_slt _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.icmp_sgt _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.icmp_ult _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.icmp_ugt _a _b => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.zext _v2 _f _t => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.trunc _v2 _f _t => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.ptrtoint _v2 _f _t => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.inttoptr _v2 _f _t => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.gep _base _idxs => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.load _ty _pty _p => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.bitcast _v2 _t => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.alloc_closure _e _a2 _env => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.alloc_constructor _tag _f => prune_phi_in_instrs_rest i rest stale_label,
                    LLVMValue.native_op _op _args => prune_phi_in_instrs_rest i rest stale_label,
                },
            LLVMInstruction.branch _c _tl _el => prune_phi_in_instrs_rest i rest stale_label,
            LLVMInstruction.jump _l => prune_phi_in_instrs_rest i rest stale_label,
            LLVMInstruction.ret _v => prune_phi_in_instrs_rest i rest stale_label,
            LLVMInstruction.store _val _pty _ptr => prune_phi_in_instrs_rest i rest stale_label,
            LLVMInstruction.comment _t => prune_phi_in_instrs_rest i rest stale_label,
        },
}

#[partial]
def prune_phi_in_instrs_rest (i : LLVMInstruction) (rest : List LLVMInstruction) (stale_label : String) : Option (List LLVMInstruction) :=
    match prune_phi_in_instrs rest stale_label {
        Option.some r => Option.some (List.cons i r),
        Option.none => Option.none,
    }

#[partial]
def remove_phi_pair_with_label (pairs : List PhiPair) (stale_label : String) : List PhiPair := match pairs {
    List.empty => List.empty,
    List.cons p rest =>
        match p {
            PhiPair.mk val label =>
                if String.beq label stale_label
                then rest
                else List.cons p (remove_phi_pair_with_label rest stale_label),
        },
}

/// Splits the function's own `"entry"` block (guaranteed to exist exactly
/// once, by `compile_db_def_ir_body`'s own hardcoded construction) into a
/// new, genuinely predecessor-free trivial `"entry"` (LLVM requires a
/// function's entry block to have NO predecessors, so it can't itself
/// carry a `phi`) that just jumps to `header_label`, and a new
/// `header_label` block holding the loop-carried `phi`s followed by the
/// original entry's own (already parm-rewritten) instructions.
/// `Option.none` only if `"entry"` is somehow missing (shouldn't happen,
/// total-safe fallback -- `apply_self_tco`'s own caller then discards
/// this whole transform and emits the Def unchanged).
#[partial]
def split_entry_for_tco (blocks : List LLVMBasicBlock) (header_label : String) (arity : I64) (loop_names : List String) (sites : List SelfTailCallSite) : Option (List LLVMBasicBlock) :=
    match find_block "entry" blocks {
        Option.some entry_block =>
            match entry_block {
                LLVMBasicBlock.mk _label entry_instrs =>
                    let header_phis := build_tco_header_phis arity "entry" loop_names sites in
                    let header_instrs := List.append header_phis entry_instrs in
                    let header_block := LLVMBasicBlock.mk header_label header_instrs in
                    let new_entry := LLVMBasicBlock.mk "entry" (List.cons (LLVMInstruction.jump header_label) List.empty) in
                    Option.some (List.cons new_entry (List.cons header_block (remove_block "entry" blocks))),
            },
        Option.none => Option.none,
    }

#[partial]
def find_block (label : String) (blocks : List LLVMBasicBlock) : Option LLVMBasicBlock := match blocks {
    List.empty => Option.none,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk l _instrs =>
                if String.beq l label then Option.some b else find_block label rest,
        },
}

#[partial]
def remove_block (label : String) (blocks : List LLVMBasicBlock) : List LLVMBasicBlock := match blocks {
    List.empty => List.empty,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk l _instrs =>
                if String.beq l label then rest else List.cons b (remove_block label rest),
        },
}

/// One `phi` instruction per loop-carried parameter: `[ %pIDX, "entry" ]`
/// for the initial-entry edge (the RAW, un-rewritten `parm_ idx` -- this
/// is a fresh literal built here, never itself passed through `rewrite_
/// parm_to_loopvar`, so it correctly still refers to the true incoming
/// argument register), plus one `[ <rewritten arg>, site_block ]` pair
/// per detected site that supplies this parameter index.
#[partial]
def build_tco_header_phis (arity : I64) (entry_label : String) (loop_names : List String) (sites : List SelfTailCallSite) : List LLVMInstruction :=
    build_tco_header_phis_go 0 arity entry_label loop_names sites

#[partial]
def build_tco_header_phis_go (idx : I64) (arity : I64) (entry_label : String) (loop_names : List String) (sites : List SelfTailCallSite) : List LLVMInstruction :=
    if I64.beq idx arity
    then List.empty
    else
        match List.get idx loop_names {
            Option.some name =>
                let init_pair := PhiPair.mk (LLVMValue.parm_ idx) entry_label in
                let site_pairs := build_site_pairs_for_idx idx sites in
                let all_pairs := List.cons init_pair site_pairs in
                let instr := LLVMInstruction.assign name (LLVMValue.phi all_pairs) in
                List.cons instr (build_tco_header_phis_go (idx + 1) arity entry_label loop_names sites),
            Option.none => build_tco_header_phis_go (idx + 1) arity entry_label loop_names sites,
        }

#[partial]
def build_site_pairs_for_idx (idx : I64) (sites : List SelfTailCallSite) : List PhiPair := match sites {
    List.empty => List.empty,
    List.cons s rest =>
        match List.get idx s.args {
            Option.some v => List.cons (PhiPair.mk v s.site_block) (build_site_pairs_for_idx idx rest),
            Option.none => build_site_pairs_for_idx idx rest,
        },
}