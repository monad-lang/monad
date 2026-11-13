/// The `cf` dialect: the branch vocabulary `convert-scf-to-cf` lands in.
///
/// This dialect is the one this backend never AUTHORS in a normal build,
/// and the module exists anyway, for a reason the plan makes explicit: the
/// CPU pipeline's `convert-scf-to-cf` lowers `scf.for`/`scf.if` into
/// `cf.br`/`cf.cond_br`, and that pass has to have somewhere to land. The
/// blocks it produces are MLIR's, not ours.
///
/// So what is here is exactly what a test needs to say "the shape
/// `convert-scf-to-cf` produces is a `cf.cond_br`" -- the branch
/// constructors, with their block-argument forwarding spelled out -- and
/// nothing else. An emitter that reached for these would be one that had
/// given up on `scf`, which the plan's ordering deliberately avoids.
///
/// ## Why `cf.br` carries operands and `cf.cond_br` carries two lists
///
/// A branch to a block with arguments must pass one value per argument, and
/// `cf.cond_br` passes a different list down each edge. That asymmetry is
/// MLIR's, and it is the reason the two are separate constructors rather
/// than one with a flag.

use std::list {List.intercalate}
use lib::ir {MlirOp, MlirType, MlirValue, show_mlir_type, show_mlir_value}

/// `cf.br ^dest(%args : types)` -- an unconditional branch.
///
/// `args` and `arg_tys` are parallel; MLIR requires the pass-through types
/// to be spelled when there are any, and omitting them is accepted only
/// for a branch to a block with no arguments. Rendering them via one
/// helper keeps the two lists in step.
pub def br (dest : String) (args : List MlirValue) (arg_tys : List MlirType) (loc : String) : MlirOp :=
    MlirOp.stmt ("cf.br ^" ++ dest ++ pass_args args arg_tys) loc

/// `cf.cond_br %c, ^then(%a : T), ^else(%b : U)`.
pub def cond_br (cond : MlirValue) (then_dest : String) (then_args : List MlirValue)
    (then_tys : List MlirType) (else_dest : String) (else_args : List MlirValue)
    (else_tys : List MlirType) (loc : String) : MlirOp :=
    MlirOp.stmt ("cf.cond_br " ++ show_mlir_value cond
        ++ ", ^" ++ then_dest ++ pass_args then_args then_tys
        ++ ", ^" ++ else_dest ++ pass_args else_args else_tys) loc

/// `switch` is absent: no kernel this backend emits has a multi-way branch,
/// and `cf.switch`'s syntax (a `[`-list of case/default pairs) is a
/// surface with no caller.

/// `(%a : f64, %b : f32)`, empty when there are no arguments.
///
/// The emptiness test runs on the JOINED string, so the two lists are each
/// mentioned exactly once whatever the case -- the affine rule's shape,
/// the same one `common.attr_block` uses.
#[partial]
def pass_args (args : List MlirValue) (arg_tys : List MlirType) : String :=
    pass_args_text (List.intercalate ", " (List.map show_passed_arg args)) arg_tys

/// `"(%a : f64)"` for a non-empty body, `""` otherwise.
#[partial]
def pass_args_text (body : String) (arg_tys : List MlirType) : String :=
    if String.is_empty body then "" else "(" ++ body ++ " : " ++ type_list arg_tys ++ ")"

#[partial]
def show_passed_arg (v : MlirValue) : String := show_mlir_value v

#[partial]
def type_list (tys : List MlirType) : String :=
    List.intercalate ", " (List.map show_one_type tys)

#[partial]
def show_one_type (t : MlirType) : String := show_mlir_type t

/// A branch to a block with arguments spells them; one to a block without
/// spells nothing at all.
#[test]
def test_pass_args_is_empty_for_no_arguments : Bool :=
    String.beq (pass_args List.empty List.empty) ""

#[test]
def test_pass_args_spells_values_and_types : Bool :=
    String.beq (pass_args [MlirValue.named "acc"] [MlirType.f64]) "(%acc : f64)"

/// A branch is a statement: no `%x = ` prefix, which is what `MlirOp.stmt`
/// is for.
#[test]
def test_br_is_a_statement : Bool :=
    let op := br "loop" [MlirValue.named "acc"] [MlirType.f64] "" in
    String.beq op.lhs "" && String.beq op.text "cf.br ^loop(%acc : f64)"
