/// The `memref` dialect: the buffer load/store pair and buffer views.
///
/// Small, and that is the design rather than an unfinished state: the
/// backend enters at `memref`, never at `tensor` (the plan's "Why `memref`,
/// not `tensor`"), so `memref.alloc`/`memref.dealloc` are deliberately
/// ABSENT. A kernel is allocation-free by construction, and an allocator
/// this module cannot spell is the cheapest possible enforcement of that --
/// stronger than a subset rule, because there is no op to emit.
///
/// ## The subscript is what makes this dialect's syntax special
///
/// `memref.store %v, %b[%i] : memref<16xf32>` puts one operand BEFORE the
/// comma and the indices INSIDE brackets after it. That is the reason the
/// model carries per-op text (`ir.mo`'s header explains at length): no
/// flat operand list produces this line, so the knowledge belongs in the
/// dialect that owns it, which is here.

use lib::ir {MlirOp, MlirType, MlirValue, show_mlir_value}
use lib::dialect::common {type_suffix}

/// `memref.load %b[%i] : <memref ty>` -- binds the loaded element.
pub def load (name : String) (buf : MlirValue) (buf_ty : MlirType) (indices : List MlirValue) (loc : String) : MlirOp :=
    MlirOp.assign name ("memref.load " ++ show_mlir_value buf ++ subscript indices
        ++ type_suffix buf_ty) loc

/// `memref.store %v, %b[%i] : <memref ty>` -- a statement, no result.
pub def store (val : MlirValue) (buf : MlirValue) (buf_ty : MlirType) (indices : List MlirValue) (loc : String) : MlirOp :=
    MlirOp.stmt ("memref.store " ++ show_mlir_value val ++ ", " ++ show_mlir_value buf
        ++ subscript indices ++ type_suffix buf_ty) loc

/// `[%i, %j]` -- the subscript form, `[]` for a rank-0 access (which does
/// not occur but must not render as a bare `%b`).
#[partial]
def subscript (indices : List MlirValue) : String :=
    "[" ++ String.concat_list (List.reverse (subscript_go indices List.empty)) ++ "]"

#[partial]
def subscript_go (indices : List MlirValue) (acc : List String) : List String := match indices {
    List.empty => acc,
    List.cons i rest => subscript_go rest (List.cons (show_mlir_value i) acc),
}

/// The memref type a rank-1 kernel buffer has, for the tests and for the
/// callers that have only a length and an element type.
pub def buf_type (n : I64) (elem : MlirType) : MlirType := MlirType.memref_1d n elem
