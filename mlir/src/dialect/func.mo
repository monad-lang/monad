/// The `func` dialect: calls, returns, and the `func.func`-adjacent ops.
///
/// `func.func` ITSELF is not here: it is the module's top-level structure,
/// and `print.mo` owns its header (`MlirFunction` in `ir.mo` is a record,
/// not an `MlirOp`). What this module owns is what appears INSIDE a body --
/// `func.call` and `func.return` -- plus the argument-attribute vocabulary
/// Decision 5 needs.
///
/// ## `func.call` spells a signature, not a type
///
/// `func.call @f(%a, %b) : (memref<16xf32>, f32) -> f64` -- both the
/// argument types and the result type are on the op, which is why
/// `common.call_signature` exists rather than the usual `type_suffix`.
/// Getting this wrong is a `mlir-opt` verifier error naming the callee, so
/// the constructor takes both so a caller cannot spell half of it.

use lib::ir {MlirOp, MlirAttr, MlirType, MlirValue, show_mlir_value}
use lib::dialect::common {call_signature, operands, type_suffix}

/// `func.call @name(%a, %b) : (t0, t1) -> ret` -- binds the result.
///
/// `tail` is MLIR's own `tail` keyword. Kernel bodies do not use it today
/// (a kernel has no call to make in tail position that matters), but the
/// field is here rather than added later because it is a single word in a
/// printer that already has three other optional pieces.
pub def call (result : String) (callee : String) (args : List MlirValue)
    (param_tys : List MlirType) (ret_ty : MlirType) (tail : Bool) (loc : String) : MlirOp :=
    MlirOp.assign result (call_text callee args param_tys ret_ty tail) loc

/// `func.call @name(%a) : (...) -> ret` as a statement -- a call whose
/// result is discarded. `%_ = func.call ...` is legal MLIR but reads as a
/// binding nobody uses, so the statement shape is used instead.
pub def call_void (callee : String) (args : List MlirValue)
    (param_tys : List MlirType) (ret_ty : MlirType) (tail : Bool) (loc : String) : MlirOp :=
    MlirOp.stmt (call_text callee args param_tys ret_ty tail) loc

/// `return %x : <ty>` -- MLIR prints `func.return` in its SHORT form.
///
/// Measured against `mlir-opt` 21.1.8: `func.return %x : f64` parses and is
/// re-printed as `return %x : f64`. Both are the same op, and this backend
/// emits the short one because a golden compares BYTES against `mlir-opt`'s
/// own output -- the long form would make every function differ from the
/// tool by a prefix for a reason no reviewer wants to re-derive.
pub def return_ (val : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    MlirOp.stmt ("return " ++ show_mlir_value val ++ type_suffix ty) loc

/// A bare `return`: the shape `void @kernel(...)` ends with. Its own
/// constructor because `return %x : <ty>` and `return` are different lines
/// and a caller that has nothing to return should not have to spell a dummy
/// type to say so.
pub def return_void (loc : String) : MlirOp :=
    MlirOp.stmt "return" loc

/// `func.constant @fref : <fn ty>` -- a function reference as a value.
/// Present for Phase 9's PJRT work (a struct of function pointers needs a
/// value that names a function), and deliberately unused until then.
pub def constant_fn (name : String) (fn_name : String) (fn_ty : MlirType) (loc : String) : MlirOp :=
    MlirOp.assign name ("func.constant @" ++ fn_name ++ type_suffix fn_ty) loc

/// The `{llvm.noalias}` argument attribute, spelled as a list so it can
/// join with others through `MlirOp`'s own attribute block.
pub def noalias_attr : MlirAttr := MlirAttr.unit "llvm.noalias"

/// The shared `[@callee](args) : (...) -> ret` text.
def call_text (callee : String) (args : List MlirValue)
    (param_tys : List MlirType) (ret_ty : MlirType) (tail : Bool) : String :=
    let kw := if tail then "tail call " else "call " in
    "func." ++ kw ++ "@" ++ callee ++ "(" ++ operands args ++ ")"
        ++ call_signature param_tys ret_ty

/// A `func.call`'s argument list is positional and its length must match
/// the signature's. Nothing in the types enforces that (both are lists,
/// and Monad has no length-indexed list in this position), so the check
/// that CAN be made cheaply is asserted here: the two lists render in the
/// same order, which is what a transposition bug would break.
#[test]
def test_call_renders_args_before_signature : Bool :=
    let op := call "r" "saxpy" [MlirValue.named "a", MlirValue.named "b"]
        [MlirType.memref_1d 16 MlirType.f32, MlirType.i32] MlirType.f64 false "" in
    String.beq op.text "func.call @saxpy(%a, %b) : (memref<16xf32>, i32) -> f64"

/// A bare `return` has no operand and no type suffix -- the whole reason
/// it is not `return_` with a dummy.
///
/// The op is bound to a local before `.text` is read: a field access on an
/// APPLICATION result does not resolve self-hosted (the receiver's type is
/// not known at the projection), which is why the sibling test above
/// spells it the same way.
#[test]
def test_return_void_is_bare : Bool :=
    let op := return_void "" in
    String.beq op.text "return"
