/// The `arith` dialect: scalar arithmetic, constants and casts.
///
/// Every op here is a pure scalar. They are what a kernel's loop body is
/// made of, so the set is small and deliberately closed: an op this module
/// does not have is one the emitter cannot produce, which is the property
/// that keeps Phase 2's `scalar.mo` from growing a syntax of its own.
///
/// ## The type suffix is per-op, not per-value
///
/// `arith.addi %a, %b : i32` spells its operand width on the op, where
/// `memref.store` spells it on the destination. That is MLIR's own
/// convention and the reason these constructors take an `MlirType` rather
/// than reading one off a value: `MlirValue` deliberately carries no type
/// (`ir.mo`), and inventing one here to be inferred would be the wrong
/// half of the model to make clever.
///
/// ## Float constants are spellings
///
/// `arith.constant 1.000000e+00 : f32` -- the text `mlir-opt` itself
/// re-prints. `float_const` takes the spelling rather than a bit pattern,
/// for the reason `ir.mo`'s header gives at length (Monad has no
/// `to_bits`; `implementations/float-bit-conversions.md` is unimplemented).

use lib::ir {MlirOp, MlirType, MlirValue, show_mlir_type, show_mlir_value}
use lib::dialect::common {type_suffix}

/// `%x = arith.constant <value> : <ty>`.
///
/// One constructor for every literal kind, because MLIR's own syntax
/// differs only in the value's spelling: `0 : index`, `42 : i32`,
/// `1.000000e+00 : f32`. The caller supplies the spelling, which is what
/// lets an integer literal and a float spelling share one path.
pub def constant (name : String) (value : String) (ty : MlirType) (loc : String) : MlirOp :=
    MlirOp.assign name ("arith.constant " ++ value ++ type_suffix ty) loc

/// `%x = arith.constant <n> : index` -- the loop bound form, which is the
/// most common constant in a kernel.
pub def constant_index (name : String) (n : I64) (loc : String) : MlirOp :=
    constant name (I64.to_string n) MlirType.index loc

/// `%x = arith.constant <n> : i64`.
pub def constant_i64 (name : String) (n : I64) (loc : String) : MlirOp :=
    constant name (I64.to_string n) MlirType.i64 loc

/// `%x = arith.constant <spelling> : f32` -- the spelling is the VALUE
/// (`"1.0"`, `"3.000000e+00"`), not a bit pattern. See the header.
pub def constant_f32 (name : String) (spelling : String) (loc : String) : MlirOp :=
    constant name spelling MlirType.f32 loc

/// `%x = arith.constant <spelling> : f64`.
pub def constant_f64 (name : String) (spelling : String) (loc : String) : MlirOp :=
    constant name spelling MlirType.f64 loc

/// `%r = arith.addi %a, %b : <ty>`.
pub def addi (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.addi" a b ty loc

/// `%r = arith.subi %a, %b : <ty>`.
pub def subi (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.subi" a b ty loc

/// `%r = arith.muli %a, %b : <ty>`.
pub def muli (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.muli" a b ty loc

/// `%r = arith.divsi %a, %b : <ty>` -- SIGNED division, which is what
/// Monad's `I64.div` means.
pub def divsi (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.divsi" a b ty loc

/// `%r = arith.remsi %a, %b : <ty>`.
pub def remsi (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.remsi" a b ty loc

/// `%r = arith.addf %a, %b : <ty>`.
pub def addf (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.addf" a b ty loc

/// `%r = arith.subf %a, %b : <ty>`.
pub def subf (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.subf" a b ty loc

/// `%r = arith.mulf %a, %b : <ty>`.
pub def mulf (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.mulf" a b ty loc

/// `%r = arith.divf %a, %b : <ty>`.
pub def divf (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.divf" a b ty loc

/// `%r = arith.cmpi slt, %a, %b : <ty>` -- an `i1`.
///
/// `pred` is the predicate word MLIR uses (`slt`, `sgt`, `eq`, `ne`,
/// `ult`, ...) rather than an enum, because the predicate set changes with
/// the language's signedness vocabulary and a misspelled one is a
/// `mlir-opt` error naming it exactly.
pub def cmpi (name : String) (pred : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    MlirOp.assign name ("arith.cmpi " ++ pred ++ ", " ++ show_mlir_value a ++ ", "
        ++ show_mlir_value b ++ type_suffix ty) loc

/// `%r = arith.cmpf olt, %a, %b : <ty>`.
pub def cmpf (name : String) (pred : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    MlirOp.assign name ("arith.cmpf " ++ pred ++ ", " ++ show_mlir_value a ++ ", "
        ++ show_mlir_value b ++ type_suffix ty) loc

/// `%r = arith.andi %a, %b : <ty>`.
pub def andi (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.andi" a b ty loc

/// `%r = arith.ori %a, %b : <ty>`.
pub def ori (name : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    binary name "arith.ori" a b ty loc

/// `%r = arith.select %c, %t, %f : <ty>` -- the branchless if, which is
/// what an `if` inside a kernel body lowers to when both arms are scalars.
pub def select (name : String) (cond : MlirValue) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    MlirOp.assign name ("arith.select " ++ show_mlir_value cond ++ ", "
        ++ show_mlir_value a ++ ", " ++ show_mlir_value b ++ type_suffix ty) loc

/// `%r = arith.index_cast %x : index to <to>`.
pub def index_cast (name : String) (x : MlirValue) (to : MlirType) (loc : String) : MlirOp :=
    cast name "arith.index_cast" x MlirType.index to loc

/// `%r = arith.sitofp %x : <from> to <to>` -- signed int to float.
pub def sitofp (name : String) (x : MlirValue) (from : MlirType) (to : MlirType) (loc : String) : MlirOp :=
    cast name "arith.sitofp" x from to loc

/// `%r = arith.extf %x : <from> to <to>` -- float widening (`f32` ->
/// `f64`), the shape a kernel's `F32` read becomes before it accumulates.
pub def extf (name : String) (x : MlirValue) (from : MlirType) (to : MlirType) (loc : String) : MlirOp :=
    cast name "arith.extf" x from to loc

/// `%r = arith.truncf %x : <from> to <to>` -- float narrowing.
pub def truncf (name : String) (x : MlirValue) (from : MlirType) (to : MlirType) (loc : String) : MlirOp :=
    cast name "arith.truncf" x from to loc

/// `%r = arith.extsi %x : <from> to <to>`.
pub def extsi (name : String) (x : MlirValue) (from : MlirType) (to : MlirType) (loc : String) : MlirOp :=
    cast name "arith.extsi" x from to loc

/// `%r = arith.trunci %x : <from> to <to>`.
pub def trunci (name : String) (x : MlirValue) (from : MlirType) (to : MlirType) (loc : String) : MlirOp :=
    cast name "arith.trunci" x from to loc

/// `%r = arith.bitcast %x : <from> to <to>`.
///
/// The shape Phase 0's fixture needed: an `F32` argument crosses the C ABI
/// as an `i32` bit pattern (`emit_extern_param_cast`), so the kernel
/// bitcasts it back rather than taking a float.
pub def bitcast (name : String) (x : MlirValue) (from : MlirType) (to : MlirType) (loc : String) : MlirOp :=
    cast name "arith.bitcast" x from to loc

/// `<op> %a, %b : <ty>` -- the shared shape of every two-operand op.
def binary (name : String) (op : String) (a : MlirValue) (b : MlirValue) (ty : MlirType) (loc : String) : MlirOp :=
    MlirOp.assign name (op ++ " " ++ show_mlir_value a ++ ", " ++ show_mlir_value b
        ++ type_suffix ty) loc

/// `<op> %x : <from> to <to>` -- the shared shape of every cast.
def cast (name : String) (op : String) (x : MlirValue) (from : MlirType) (to : MlirType) (loc : String) : MlirOp :=
    MlirOp.assign name (op ++ " " ++ show_mlir_value x ++ " : "
        ++ show_mlir_type from ++ " to " ++ show_mlir_type to) loc
