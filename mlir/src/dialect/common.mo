/// Shared operand-rendering helpers for the dialect modules.
///
/// Small on purpose. Every dialect composes its own op syntax (see
/// `ir.mo`'s file header for why the model carries text), and what they
/// genuinely share is only this: how a comma-separated operand list is
/// spelled, and how a `-> (a, b)` result list is. Putting those here keeps
/// ~20 construction sites from each carrying their own copy of a join,
/// which is the shape that drifts.
///
/// No dialect-to-dialect edge: every `dialect/*.mo` imports `ir.mo` and
/// this file, and nothing else. That is what keeps the diamond acyclic --
/// `lib.mo` re-exports, it does not re-order.

use std::list {List.intercalate}
use lib::ir {MlirAttr, MlirType, MlirValue, show_mlir_attr, show_mlir_type, show_mlir_value}

/// `%a, %b, %c` -- the comma-separated operand list every op spells.
#[partial]
pub def operands (vs : List MlirValue) : String :=
    List.intercalate ", " (List.map show_op_value vs)

/// `show_mlir_value`, eta-expanded because `List.map` wants a
/// one-argument function and a sibling `pub def` is not one.
#[partial]
def show_op_value (v : MlirValue) : String := show_mlir_value v

/// Types, comma-separated: what a `func.call`'s `: (memref<16xf32>, f32)
/// -> f64` operand list spells.
#[partial]
pub def type_list (tys : List MlirType) : String :=
    List.intercalate ", " (List.map show_op_type tys)

#[partial]
def show_op_type (t : MlirType) : String := show_mlir_type t

/// Attributes, comma-separated, with no braces.
#[partial]
pub def attr_list (attrs : List MlirAttr) : String :=
    List.intercalate ", " (List.map show_op_attr attrs)

#[partial]
def show_op_attr (a : MlirAttr) : String := show_mlir_attr a

/// `" {a, b}"` for a non-empty body, `""` for an empty one. The
/// emptiness test runs on the joined string (which is `Copy`) rather than
/// on the list, so an attribute list is mentioned exactly once either way.
pub def attr_block (body : String) : String :=
    if String.is_empty body then "" else " {" ++ body ++ "}"

/// `: (t0, t1) -> ret` -- an op's type suffix in the `func.call` shape,
/// which spells its whole SIGNATURE rather than one type.
pub def call_signature (params : List MlirType) (ret : MlirType) : String :=
    " : (" ++ type_list params ++ ") -> " ++ show_mlir_type ret

/// `: <type>` -- the common suffix, one type at a use site.
pub def type_suffix (ty : MlirType) : String :=
    " : " ++ show_mlir_type ty
