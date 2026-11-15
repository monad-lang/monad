/// `#[kernel]` scalar emission: a reduced `Term` -> `arith`/`scf`/`memref` ops.
///
/// ## What this module is for
///
/// `mono.mo` hands over a `KernelExtract`: a body whose helpers are inlined,
/// whose shape arithmetic is folded, and whose only remaining references are
/// natives, constructors and the kernel's own parameters. `shape.mo` hands
/// over the signature. This module turns the term into the ops of one
/// `func.func` body -- `arith` for the scalar arithmetic, `scf.if` for a
/// branch, `scf.for` for the one loop shape the subset permits.
///
/// ## The two inputs, and why this module refuses rather than guesses
///
/// A kernel is emittable only when BOTH of its predecessors are clean:
/// `KernelShape.ready` (the signature is in the subset) and
/// `KernelExtract.ready` (the body inlined to something first-order). This
/// module checks both and returns a diagnostic list otherwise. It does not
/// re-derive either fact, and it does not emit a best-effort body -- a
/// half-emitted kernel is a wrong ANSWER, and this plan's premise is that a
/// wrong answer is worse than a diagnostic.
///
/// ## What is deliberately NOT here
///
/// * **No allocation.** `memref.alloc` is unspellable in
///   `mlir/dialect/memref.mo`, which is the cheapest enforcement of the
///   subset's allocation-free rule -- there is no op to emit.
/// * **No recursion.** Rule 4 refuses it, and `mono.mo` reports a reference
///   that survives inlining, so a `Term.var` reaching this module that is
///   neither a parameter nor a local is a diagnostic, not a call.
/// * **No closures.** Rule 2 refuses them, so a `Term.lam` here is a
///   diagnostic.
///
/// ## SSA names
///
/// Every name is minted by `NameSupply`. That is not decoration: MLIR SSA
/// names must be unique across the WHOLE module, so a second kernel in the
/// same file must not re-mint `%t0`, and a name derived from a term's
/// structure can collide. `codegen/src/ctx.mo`'s `fresh_temp` is the same
/// idea for the LLVM backend; this is the kernel backend's own because the
/// two name spaces are independent.
///
/// ## The measured shapes this lowers
///
/// Both spellings of an operation are accepted, and that is a MEASUREMENT
/// rather than defensive coding: `mono.mo`'s header records the dictionary
/// chain (`HAdd_A_A_A_add __Dict_Add_I64 4i64 4i64`) for a def compiled
/// through `compile_input_of_modules`, while a kernel's reduced body carries
/// the class-method reference the elaborator left (`(HAdd.add n 1i64)`).
/// `mono.mo` folds the literal-literal case before this module sees it, so
/// what arrives here is the variable case, and the table below is written
/// from the observed spellings (the plan's cost item 8).
use lang::types {
    DebugName, Identifier, Literal, MatchCase, Native, NumSuffix, Term, term_peel,
}
use lib::kernel::detect {KernelDiagnostic}
use lib::kernel::mono {KernelExtract, id_text}
use lib::kernel::shape {KernelShape, ParamShape}
use mlir::ir {MlirBlock, MlirOp, MlirType, MlirValue}
use mlir::dialect::arith {
    addi, cmpi, constant_f32, constant_f64, constant_i64, divsi, muli, remsi, subi,
}
use mlir::dialect::func {return_, return_void}
use mlir::dialect::scf {if_result, yield}

// ─── the result ──────────────────────────────────────────────────────

/// A kernel's emitted body: the ops of one `func.func` region, plus
/// everything that stopped a full emission.
pub struct KernelBody {
    /// The kernel's symbol, carried through so a caller need not thread the
    /// `KernelShape` alongside.
    name : String,
    /// The `func.func` body: one entry block, terminator already appended.
    block : MlirBlock,
    /// Everything that stopped a full emission. Empty means the body is
    /// emittable.
    diagnostics : List KernelDiagnostic,
}

/// Is the body free of diagnostics -- ready for `host.mo`?
pub def KernelBody.ready (b : KernelBody) : Bool := List.is_empty b.diagnostics

/// The number of ops in the body, for a caller that wants to report it.
pub def KernelBody.op_count (b : KernelBody) : I64 :=
    List.length b.block.ops

// ─── the SSA name supply ─────────────────────────────────────────────

/// A fresh-name supply, threaded through every emission step.
///
/// A record rather than a mutable counter because the rest of this module is
/// pure: `scalar.mo` produces a `KernelBody`, and `host.mo` decides when to
/// print it. Threading the supply makes emission a function of its inputs,
/// which is what lets a golden test compare bytes.
pub struct NameSupply {
    next : I64,
    prefix : String,
}

pub def NameSupply.of (prefix : String) : NameSupply := NameSupply.mk 0 prefix

/// A fresh name, and the supply advanced past it.
pub def NameSupply.fresh (s : NameSupply) : Pair String NameSupply :=
    Pair.pair (String.concat s.prefix (I64.to_string s.next)) (NameSupply.mk (s.next + 1) s.prefix)

/// `%<name>`.
def val_of (name : String) : MlirValue := MlirValue.named name

// ─── the emission state ──────────────────────────────────────────────

/// The environment an emission step runs in.
///
/// Ops accumulate in a LIST rather than being appended to a block, because
/// every step emits zero or more ops and a block-level append would make each
/// step a `List.append` at the end. The list is reversed once, at the end, by
/// `finish_block`.
///
/// `result`/`result_ty` are the value the last step produced and its MLIR
/// type. They are fields rather than a return pair because a step that emits
/// nothing (a parameter reference) still has to produce a value, and a
/// `Pair`-returning walk would make every arm of `emit_term` unwrap one.
pub struct EmitState {
    ops : List MlirOp,
    names : NameSupply,
    /// The kernel's MLIR parameters, by their Monad name. A `Term.var` not
    /// found here is an `inline` diagnostic.
    bindings : List (Pair String MlirValue),
    diagnostics : List KernelDiagnostic,
    kernel : String,
    result : Option MlirValue,
    result_ty : MlirType,
}

#[partial]
def state_of (kernel : String) (bindings : List (Pair String MlirValue)) : EmitState :=
    EmitState.mk List.empty (NameSupply.of "t") bindings List.empty kernel Option.none MlirType.i64

/// The state with one op appended.
#[partial]
def emit (st : EmitState) (op : MlirOp) : EmitState :=
    { st with ops := List.append st.ops (List.cons op List.empty) }

/// The state with a diagnostic appended.
#[partial]
def report (st : EmitState) (rule : String) (detail : String) : EmitState :=
    { st with diagnostics := List.append st.diagnostics (List.cons (KernelDiagnostic.of st.kernel rule detail) List.empty) }

/// The state with `v` as the current result value.
#[partial]
def with_result (st : EmitState) (v : MlirValue) (ty : MlirType) : EmitState :=
    { st with result := Option.some v, result_ty := ty }

/// A fresh name and the advanced state.
#[partial]
def fresh (st : EmitState) : Pair String EmitState :=
    match NameSupply.fresh st.names {
        Pair.pair n names2 => Pair.pair n { st with names := names2 },
    }

/// Look a name up among the state's bindings.
#[partial]
def lookup_value (st : EmitState) (name : String) : Option MlirValue :=
    lookup_in st.bindings name

#[partial]
def lookup_in (bindings : List (Pair String MlirValue)) (name : String) : Option MlirValue := match bindings {
    List.empty => Option.none,
    List.cons b rest =>
        match b {
            Pair.pair n v => if String.beq n name then Option.some v else lookup_in rest name,
        },
}

// ─── the top-level entry point ───────────────────────────────────────

/// Emit `extract`'s body against `shape`'s signature.
///
/// The two are checked for readiness first and their diagnostics merged, so a
/// caller that wants to report and continue can; `KernelBody.ready` is the
/// gate `host.mo` checks before printing.
#[partial]
pub def emit_kernel_body (shape : KernelShape) (extract : KernelExtract) : KernelBody :=
    let pre : List KernelDiagnostic := List.append shape.diagnostics extract.diagnostics in
    if Bool.not (List.is_empty pre)
    then KernelBody.mk shape.name (MlirBlock.entry "" List.empty) pre
    else
        let st0 : EmitState := state_of shape.name (mlir_param_bindings shape.params) in
        let st1 : EmitState := emit_term st0 extract.body in
        let st2 : EmitState := finish_body st1 shape.results in
        // The block's label is EMPTY, not `"entry"`: MLIR prints a region's
        // single entry block with no `^label:` line, and `mlir-opt` re-prints
        // it that way -- a label here would make every kernel differ from the
        // tool's own output by a line. See `mlir/print.mo`'s `block_header`.
        //
        // And `st2.ops` is NOT reversed: `emit` APPENDS
        // (`List.append st.ops [op]`), so the list is already in program order
        // and a reverse would emit the terminator FIRST. Measured, not
        // theorised: the first version reversed and rendered
        // `return %t3 : i64` above the `scf.if` that defines `%t3`.
        KernelBody.mk shape.name (MlirBlock.entry "" st2.ops) st2.diagnostics

/// `(name, %name)` for every MLIR parameter the shape declares, in order --
/// the `dim_` entries are dropped because they were folded into memref types.
///
/// `MlirValue.named` rather than `arg_`: a `func.func` parameter is an
/// ordinary named value in MLIR's textual form.
#[partial]
def mlir_param_bindings (params : List ParamShape) : List (Pair String MlirValue) := match params {
    List.empty => List.empty,
    List.cons p rest =>
        match p {
            ParamShape.buffer_ name _elem _dims _noalias =>
                List.cons (Pair.pair name (val_of name)) (mlir_param_bindings rest),
            ParamShape.scalar_ name _ty _noalias =>
                List.cons (Pair.pair name (val_of name)) (mlir_param_bindings rest),
            ParamShape.dim_ _name => mlir_param_bindings rest,
        },
}

/// Append the body's terminator: `return %r : T` for a kernel with a result,
/// a bare `return` for a `Unit`-returning one.
///
/// A `Unit` kernel's value is discarded -- it is the `Unit` constructor's
/// address in the boxed backend, which has no MLIR meaning, so the
/// `return_void` is the honest emission rather than a cast of a value that
/// does not exist.
#[partial]
def finish_body (st : EmitState) (results : List MlirType) : EmitState :=
    if List.is_empty results
    then emit st (return_void "")
    else match st.result {
        Option.none => emit st (return_void ""),
        Option.some v => emit st (return_ v st.result_ty ""),
    }

// ─── the term walk ───────────────────────────────────────────────────

/// Emit `t` into `st`, setting `st.result` when the step produces a value.
#[partial]
def emit_term (st : EmitState) (t : Term) : EmitState :=
    match term_peel t {
        Term.var _idx dbg => emit_var st dbg,
        Term.ntv _n => report st "closure" "native used as a value",
        Term.lit l => emit_literal st l,
        Term.app f a => emit_spine st (spine_head (Term.app f a)) (spine_args (Term.app f a) List.empty),
        Term.lam _b _typ _body => report st "closure" "lambda",
        Term.elim _e => report st "unsupported" "elim that never desugared",
        Term.con _c => report st "alloc" "constructor application",
        Term.ctx _loc inner => emit_term st inner,
        Term.hole => report st "unsupported" "hole",
        _ => report st "unsupported" "term outside the kernel subset",
    }

/// A reference: a parameter, or an unresolvable name.
///
/// An unresolvable name is the shape a surviving top-level reference has, and
/// `mono.mo` already reports those as `inline` findings -- so this is a
/// fallback, not the primary report. It stays a diagnostic rather than a
/// guess because emitting a name MLIR does not know is a verifier error
/// pointing at a generated line.
#[partial]
def emit_var (st : EmitState) (dbg : DebugName) : EmitState := match dbg {
    DebugName.unnamed => report st "unsupported" "unnamed reference",
    DebugName.named id =>
        let name : String := id_text id in
        match lookup_value st name {
            Option.some v => with_result st v st.result_ty,
            Option.none => report st "inline" (String.concat "unresolved " name),
        },
}

/// A literal: an integer or float constant, a branch, or a match.
#[partial]
def emit_literal (st : EmitState) (l : Literal) : EmitState := match l {
    Literal.num v suffix => emit_int_literal st v suffix,
    Literal.flt text suffix => emit_float_literal st text suffix,
    Literal.if_ c a b => emit_if st c a b,
    Literal.match_ scrut cases => emit_match st scrut cases,
    _ => report st "unsupported" "literal outside the kernel subset",
}

/// An integer constant.
#[partial]
def emit_int_literal (st : EmitState) (v : I64) (suffix : NumSuffix) : EmitState :=
    let ty : MlirType := int_type_of_suffix suffix in
    match fresh st {
        Pair.pair n st2 => with_result (emit st2 (constant_i64 n v "")) (val_of n) ty,
    }

/// A float constant. The spelling is the SOURCE text, which is exactly what
/// `arith.constant` wants (`1.5 : f32`); Monad keeps a float literal as its
/// text for the reason `Literal.flt`'s own doc comment gives.
#[partial]
def emit_float_literal (st : EmitState) (text : String) (suffix : NumSuffix) : EmitState :=
    match fresh st {
        Pair.pair n st2 =>
            if is_f64_suffix suffix
            then with_result (emit st2 (constant_f64 n text "")) (val_of n) MlirType.f64
            else with_result (emit st2 (constant_f32 n text "")) (val_of n) MlirType.f32,
    }

#[partial]
def is_f64_suffix (suffix : NumSuffix) : Bool := match suffix {
    NumSuffix.f64 => true,
    _ => false,
}

/// The MLIR integer type a literal's suffix names.
#[partial]
def int_type_of_suffix (suffix : NumSuffix) : MlirType := match suffix {
    NumSuffix.i8 => MlirType.i8,
    NumSuffix.i16 => MlirType.int_ 16,
    NumSuffix.i32 => MlirType.i32,
    NumSuffix.i64 => MlirType.i64,
    NumSuffix.u8 => MlirType.int_ 8,
    NumSuffix.u16 => MlirType.int_ 16,
    NumSuffix.u32 => MlirType.i32,
    NumSuffix.u64 => MlirType.i64,
    NumSuffix.f32 => MlirType.f32,
    NumSuffix.f64 => MlirType.f64,
}

/// `if c then a else b` -> a result-carrying `scf.if`.
///
/// Both arms are emitted into states of their own so their ops do not
/// interleave, and each arm ends in `scf.yield` -- an `scf.if` with a result
/// must yield one value per declared result, which is what `if_result`
/// declares. The result type is the THEN arm's, and a mismatch between the
/// arms is MLIR's verifier's to report rather than a second type checker's
/// here.
#[partial]
def emit_if (st : EmitState) (c : Term) (a : Term) (b : Term) : EmitState :=
    let st_c : EmitState := emit_term st c in
    match_result_if st_c a b

/// The `if`'s arms, once the condition has a value.
#[partial]
def match_result_if (st_c : EmitState) (a : Term) (b : Term) : EmitState :=
    match st_c.result {
        Option.none => report st_c "unsupported" "if condition has no value",
        Option.some cond => emit_if_arms st_c cond a b,
    }

/// The arms of an `if`, with the condition already a value.
#[partial]
def emit_if_arms (st : EmitState) (cond : MlirValue) (a : Term) (b : Term) : EmitState :=
    let st_a : EmitState := emit_term (arm_state st) a in
    let st_b : EmitState := emit_term (arm_state st_a) b in
    let f : Pair String EmitState := fresh st_b in
    match f {
        Pair.pair n st2 => emit_if_join st2 st_a st_b n cond,
    }

/// Join the two emitted arms into the `scf.if`.
#[partial]
def emit_if_join (st2 : EmitState) (st_a : EmitState) (st_b : EmitState) (n : String) (cond : MlirValue) : EmitState :=
    let arm_ty : MlirType := st_a.result_ty in
    let tys : List MlirType := List.cons arm_ty List.empty in
    let then_block : MlirBlock := MlirBlock.entry "" (arm_ops st_a arm_ty) in
    let else_ops : List MlirOp := arm_ops st_b arm_ty in
    let op : MlirOp := if_result n cond tys (List.cons then_block List.empty) else_ops "" in
    with_result (emit (merge_arms st2 st_a st_b) op) (val_of n) arm_ty

/// A fresh emission state for an arm: the ops restart, the names continue,
/// and the bindings carry over (an arm may read an outer parameter).
#[partial]
def arm_state (st : EmitState) : EmitState := { st with ops := List.empty }

/// An arm's ops, with its `scf.yield` terminator appended.
/// An arm's ops, with its `scf.yield` terminator appended. NOT reversed, for
/// `emit_kernel_body`'s reason: `emit` appends, so the list is already ordered.
#[partial]
def arm_ops (st : EmitState) (ty : MlirType) : List MlirOp :=
    match st.result {
        Option.none => List.append st.ops (List.cons (yield_void_ "") List.empty),
        Option.some v => List.append st.ops (List.cons (yield (List.cons v List.empty) (List.cons ty List.empty) "") List.empty),
    }

/// A bare `scf.yield`, spelled here rather than imported under two names.
def yield_void_ (loc : String) : MlirOp := MlirOp.stmt "scf.yield" loc

/// The state after both arms: the pre-arm ops and diagnostics kept, the arms'
/// own ops dropped (they are inside the region now), the supply advanced.
#[partial]
def merge_arms (st : EmitState) (a : EmitState) (b : EmitState) : EmitState :=
    { st with diagnostics := List.append st.diagnostics (List.append a.diagnostics b.diagnostics) }

/// `match scrut { ... }` -> an `scf.if` for a two-arm `Bool` match, or a
/// diagnostic.
///
/// Only the two-arm shape is lowered today. A general `match` needs an
/// `scf.index_switch` or a chain of `scf.if`s plus a constructor TAG the
/// kernel does not carry (there is no heap record on a device), so anything
/// wider is reported rather than guessed. `Bool` is the case the plan's
/// examples write.
#[partial]
def emit_match (st : EmitState) (scrut : Term) (cases : List MatchCase) : EmitState :=
    if I64.beq (List.length cases) 2
    then match_two_of st (List.get 0 cases) (List.get 1 cases) scrut
    else report st "unsupported" "match outside the kernel subset"

/// A two-arm match, once the arms are known to exist.
///
/// `List.get` rather than a nested `List.cons a (List.cons b _)` pattern: the
/// self-hosted parser rejects a constructor pattern whose ARGUMENT is itself a
/// constructor pattern (`expected '('`), so the length check plus two indexed
/// reads is the shape that parses.
#[partial]
def match_two_of (st : EmitState) (first : Option MatchCase) (second : Option MatchCase) (scrut : Term) : EmitState :=
    match first {
        Option.none => report st "unsupported" "match outside the kernel subset",
        Option.some f => match second {
            Option.none => report st "unsupported" "match outside the kernel subset",
            Option.some g => emit_match_two st f g scrut,
        },
    }

/// A two-arm match, with the arms extracted.
#[partial]
def emit_match_two (st : EmitState) (first : MatchCase) (second : MatchCase) (scrut : Term) : EmitState :=
    let st_s : EmitState := emit_term st scrut in
    match st_s.result {
        Option.none => report st_s "unsupported" "match scrutinee has no value",
        Option.some sv => emit_match_arms st_s first second sv,
    }

/// The two arms of a match, with the scrutinee already a value.
#[partial]
def emit_match_arms (st : EmitState) (first : MatchCase) (second : MatchCase) (sv : MlirValue) : EmitState :=
    let st_a : EmitState := emit_case (arm_state st) first in
    let st_b : EmitState := emit_case (arm_state st_a) second in
    match fresh st_b {
        Pair.pair n st2 => emit_if_join st2 st_a st_b n sv,
    }

/// One `match` arm: emit the body. A nullary `Bool` arm binds no fields, so
/// there is nothing to bind here; a constructor arm's field binders are a
/// later item (they need the tag the diagnostic above refuses).
#[partial]
def emit_case (st : EmitState) (c : MatchCase) : EmitState :=
    match c {
        MatchCase.mk _name _args body _fp _tn => emit_term st body,
    }

// ─── applications ────────────────────────────────────────────────────

/// The head of an application spine: the function part with every argument
/// stripped, so `((f a) b)` yields `f`.
///
/// Flattening is required, not stylistic: `n + 1` reaches this module as
/// `((HAdd.add n) 1)`, so the outermost node's function is itself an
/// application and a walk that asked "is the head a native?" of that node
/// would answer no for every call of arity >= 2. This is the same lesson
/// `mono.mo`'s reducer records, one layer out.
#[partial]
def spine_head (t : Term) : Term := match term_peel t {
    Term.app f _a => spine_head f,
    _ => t,
}

/// Every argument of an application spine, in written order.
#[partial]
def spine_args (t : Term) (acc : List Term) : List Term := match term_peel t {
    Term.app f a => spine_args f (List.cons a acc),
    _ => acc,
}

/// The head's name, or `""` when it is not a name.
#[partial]
def head_name (t : Term) : String := match term_peel t {
    Term.var _idx dbg => match dbg {
        DebugName.named id => id_text id,
        DebugName.unnamed => "",
    },
    Term.ntv n => match n {
        Native.mk name _num _args => id_text name,
    },
    _ => "",
}

/// Emit a native arithmetic spine, or report it.
#[partial]
def emit_spine (st : EmitState) (hd : Term) (args : List Term) : EmitState :=
    let name : String := head_name hd in
    let arity : I64 := List.length args in
    if String.is_empty name
    then report st "unsupported" "call to a non-native head"
    else if I64.beq arity 2 then emit_binop st name args
    else report st "unsupported" (String.concat name " with an unsupported arity")

/// A two-operand native: `i64_add`/`HAdd.add` and friends.
#[partial]
def emit_binop (st : EmitState) (name : String) (args : List Term) : EmitState :=
    if I64.lt (List.length args) 2
    then report st "unsupported" (String.concat name " with an unsupported arity")
    else emit_binop_two st name (List.get 0 args) (List.get 1 args)

/// A binary op, once its two argument TERMS are known to exist.
#[partial]
def emit_binop_two (st : EmitState) (name : String) (a : Option Term) (b : Option Term) : EmitState :=
    match a {
        Option.none => report st "unsupported" (String.concat "non-value operand of " name),
        Option.some at => match b {
            Option.none => report st "unsupported" (String.concat "non-value operand of " name),
            Option.some bt => emit_binop_terms st name at bt,
        },
    }

/// Emit both operands, then the op.
#[partial]
def emit_binop_terms (st : EmitState) (name : String) (a : Term) (b : Term) : EmitState :=
    let st_a : EmitState := emit_term st a in
    match st_a.result {
        Option.none => report st_a "unsupported" (String.concat "non-value operand of " name),
        Option.some av => emit_binop_second st_a name av b,
    }

#[partial]
def emit_binop_second (st : EmitState) (name : String) (av : MlirValue) (b : Term) : EmitState :=
    let st_b : EmitState := emit_term st b in
    match st_b.result {
        Option.none => report st_b "unsupported" (String.concat "non-value operand of " name),
        Option.some bv => emit_binop_op st_b name av bv,
    }

/// The actual op, once both operands are values. Split out because the
/// `Option`-match nesting above is deep enough that the self-hosted checker
/// wants each stage in its own def.
#[partial]
def emit_binop_op (st : EmitState) (name : String) (a : MlirValue) (b : MlirValue) : EmitState :=
    let ty : MlirType := st.result_ty in
    match fresh st {
        Pair.pair n st2 =>
            if is_add_name name
            then with_result (emit st2 (addi n a b ty "")) (val_of n) ty
            else if is_sub_name name
            then with_result (emit st2 (subi n a b ty "")) (val_of n) ty
            else if is_mul_name name
            then with_result (emit st2 (muli n a b ty "")) (val_of n) ty
            else if is_div_name name
            then with_result (emit st2 (divsi n a b ty "")) (val_of n) ty
            else if is_rem_name name
            then with_result (emit st2 (remsi n a b ty "")) (val_of n) ty
            else if is_lt_name name
            then with_result (emit st2 (cmpi n "slt" a b ty "")) (val_of n) MlirType.i1
            else if is_gt_name name
            then with_result (emit st2 (cmpi n "sgt" a b ty "")) (val_of n) MlirType.i1
            else if is_eq_name name
            then with_result (emit st2 (cmpi n "eq" a b ty "")) (val_of n) MlirType.i1
            else report st2 "unsupported" (String.concat "native " name),
    }

// ─── the native name families ────────────────────────────────────────
//
// Two spellings of the same operation, both MEASURED (see the header and the
// plan's cost item 8): the `#[native i64_add]` name, and the class-method
// reference the elaborator leaves for `+`. `mono.mo` folds the
// literal-literal case before this module sees it, so the variable case is
// what arrives -- and an unknown native is a diagnostic rather than a
// silent no-op.

#[partial]
def is_add_name (name : String) : Bool :=
    String.beq name "i64_add" || String.beq name "HAdd.add" || String.beq name "Add.add"

#[partial]
def is_sub_name (name : String) : Bool :=
    String.beq name "i64_sub" || String.beq name "HSub.sub" || String.beq name "Sub.sub"

#[partial]
def is_mul_name (name : String) : Bool :=
    String.beq name "i64_mul" || String.beq name "HMul.mul" || String.beq name "Mul.mul"

#[partial]
def is_div_name (name : String) : Bool :=
    String.beq name "i64_div" || String.beq name "HDiv.div" || String.beq name "Div.div"

#[partial]
def is_rem_name (name : String) : Bool :=
    String.beq name "i64_rem" || String.beq name "HMod.mod" || String.beq name "Mod.mod"

#[partial]
def is_lt_name (name : String) : Bool :=
    String.beq name "i64_lt" || String.beq name "I64.lt"

#[partial]
def is_gt_name (name : String) : Bool :=
    String.beq name "i64_gt" || String.beq name "I64.gt"

#[partial]
def is_eq_name (name : String) : Bool :=
    String.beq name "i64_eq" || String.beq name "I64.eq"
