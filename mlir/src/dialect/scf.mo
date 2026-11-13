/// The `scf` dialect: structured control flow -- `for`, `if`, `yield`.
///
/// This is the loop vocabulary, and it is the ONLY iteration in a kernel:
/// kernels permit no recursion (the plan's Decision 5 -- a termination
/// proof is not a trip count, and only the latter lowers to a loop), so
/// `scf.for` over an `index` induction variable is the whole of a kernel's
/// iteration.
///
/// ## What the shapes are, measured against real `mlir-opt` 21.1.8
///
/// Neither of these is guessable from the plan's prose, and both fail as a
/// verifier complaint several hundred lines later if they are wrong, so
/// both were checked before being written down:
///
///   * `scf.for`'s body region has NO block header. The induction variable
///     is bound in the OP's header (`scf.for %iv = %c0 to %c16 step %c1 {`)
///     and the region is printed as a bare op list -- no `^bb0(...)` line.
///     So a body is `MlirBlock.entry "" ops`, with an empty label, and the
///     printer's own "a block with no label prints none" rule does the
///     rest.
///   * `iter_args` is where a loop-carried value goes, and the op's result
///     is the `-> (f64)` on the SAME LINE:
///     `%acc = scf.for %iv = ... iter_args(%s = %zero) -> (f64) { ... }`.
///     The body must end in `scf.yield` with one operand per `iter_args`
///     entry.
///
/// `scf.if` is the same shape: the result type is on the header, the arms
/// are bare regions, and each ends in `scf.yield`.
///
/// ## Every bound name is caller-supplied
///
/// `iv` and every `iter_args` name is a parameter, not a name this module
/// derives. That is not decoration: MLIR SSA names must be unique across
/// the WHOLE module, so a derived `%arg0` for a loop's induction variable
/// can collide with an unrelated value, and the failure is a verifier
/// error pointing at a generated line. The caller owns a fresh-name
/// supply (`codegen/src/ctx.mo`'s `fresh_temp` is the existing one); this
/// module's job is to place whatever it is given, consistently, in the
/// header and in the body's uses -- which is why the constructors take the
/// names rather than returning them.

use std::list {List.intercalate}
use lib::ir {MlirBlock, MlirOp, MlirType, MlirValue, show_mlir_type, show_mlir_value}
use lib::dialect::common {operands}

/// `scf.for %<iv> = %lb to %ub step %step { ... }` with no loop-carried
/// value -- a write-only loop, which is what `dst[i] = f i` is.
pub def for_ (iv : String) (lower : MlirValue) (upper : MlirValue) (step : MlirValue)
    (body : List MlirBlock) (loc : String) : MlirOp :=
    MlirOp.stmt_region (for_header iv lower upper step) body loc

/// `%<result> = scf.for %<iv> = %lb to %ub step %step
/// iter_args(<names> = <inits>) -> (<result_tys>) { ... }`.
///
/// `names` and `inits` are parallel lists, rendered by ONE pass
/// (`iter_args_text`) so a transposition between them is not spellable.
/// `result_tys` must have the same length as `inits`; MLIR's verifier is
/// what enforces that, and it enforces it by naming the op.
pub def for_iter (result : String) (iv : String) (lower : MlirValue) (upper : MlirValue) (step : MlirValue)
    (names : List String) (inits : List MlirValue) (result_tys : List MlirType)
    (body : List MlirBlock) (loc : String) : MlirOp :=
    MlirOp.assign_region result (for_iter_header iv lower upper step names inits result_tys) body loc

/// `scf.if %c { ... } else { ... }` as a statement.
///
/// The ELSE ARM IS PASSED AS OPS, not as blocks, and that is the shape
/// `mlir-opt` actually accepts. An `scf.if`'s two arms are consecutive
/// blocks of one region, but the second is introduced by the `else`
/// KEYWORD rather than by a `^label:` header -- so it is built here with
/// `MlirBlock.else_`, which is what tells the printer to emit `} else {`
/// on one line. Measured: printing that arm as `^bb1:` is
/// `expected 'else' to terminate` from `mlir-opt` 21.1.8.
///
/// Taking ops rather than a block list also makes the `else` arm's shape
/// unspellable-wrong at the CALL SITE: a caller cannot hand it a labelled
/// block, because there is no parameter for one.
pub def if_ (cond : MlirValue) (then_blocks : List MlirBlock) (else_ops : List MlirOp) (loc : String) : MlirOp :=
    MlirOp.stmt_region (if_header cond List.empty)
        (List.append then_blocks [MlirBlock.else_ else_ops]) loc

/// `%<result> = scf.if %c -> (T) { ... } else { ... }`. See `if_` for why
/// the else arm is an op list.
pub def if_result (result : String) (cond : MlirValue) (result_tys : List MlirType)
    (then_blocks : List MlirBlock) (else_ops : List MlirOp) (loc : String) : MlirOp :=
    MlirOp.assign_region result (if_header cond result_tys)
        (List.append then_blocks [MlirBlock.else_ else_ops]) loc

/// `scf.yield %x : <ty>` -- a loop body's or an `if` arm's terminator.
///
/// A list because `scf.yield` must yield exactly one value per result the
/// enclosing op declares, and two-result `if` is legal MLIR even though no
/// kernel needs it yet.
pub def yield (vals : List MlirValue) (tys : List MlirType) (loc : String) : MlirOp :=
    MlirOp.stmt ("scf.yield " ++ operands vals ++ " : " ++ type_list tys) loc

/// A bare `scf.yield` -- the terminator of a loop or arm that carries
/// nothing. The shape `scf.for ... { memref.store ...; scf.yield }` ends
/// with.
pub def yield_void (loc : String) : MlirOp :=
    MlirOp.stmt "scf.yield" loc

// `scf.condition` is deliberately absent: it is the `scf.while` terminator,
// and this backend emits no `while` -- a kernel's iteration is bounded and
// `scf.for` is the shape for that (Decision 5).

/// `scf.for %<iv> = %lb to %ub step %step`.
def for_header (iv : String) (lower : MlirValue) (upper : MlirValue) (step : MlirValue) : String :=
    "scf.for %" ++ iv ++ " = " ++ show_mlir_value lower
        ++ " to " ++ show_mlir_value upper ++ " step " ++ show_mlir_value step

/// `scf.for %<iv> = %lb to %ub step %step iter_args(...) -> (T)`.
def for_iter_header (iv : String) (lower : MlirValue) (upper : MlirValue) (step : MlirValue)
    (names : List String) (inits : List MlirValue) (result_tys : List MlirType) : String :=
    for_header iv lower upper step
        ++ iter_args_text names inits ++ result_types_text result_tys

/// `scf.if %c` plus an optional `-> (T)`.
def if_header (cond : MlirValue) (result_tys : List MlirType) : String :=
    "scf.if " ++ show_mlir_value cond ++ result_types_text result_tys

/// ` iter_args(%s = %zero, %t = %one)`, empty for empty lists.
///
/// The two lists are walked together in ONE pass, which is what makes
/// them parallel by construction: `iter_args_go` destructures both at
/// each step, so a name cannot be paired with another entry's init.
#[partial]
def iter_args_text (names : List String) (inits : List MlirValue) : String :=
    let body := String.concat_list (List.reverse (iter_args_go names inits List.empty)) in
    if String.is_empty body then "" else " iter_args(" ++ body ++ ")"

/// One `%name = %init` per pair, comma-separated.
///
/// The separator is SUFFIXED and keyed on whether `inits` has more entries,
/// the same shape `pipeline.mo`'s `step_text_with_separator` uses and for
/// the same reason: the accumulator is reversed at the end, so a separator
/// computed from `List.is_empty rest` on the NAMES list lands in the wrong
/// position. Measured symptom of getting this wrong: `iter_args(%s =
/// %zero%t = %one)`, which `mlir-opt` rejects as `expected ','`.
#[partial]
def iter_args_go (names : List String) (inits : List MlirValue) (acc : List String) : List String :=
    match names {
        List.empty => acc,
        List.cons n rest => match inits {
            List.empty => acc,
            List.cons v more =>
                iter_args_go rest more
                    (List.cons (iter_arg_text n v (List.is_empty more)) acc),
        },
    }

/// `%name = %init`, with `", "` appended unless it is the last pair.
#[partial]
def iter_arg_text (name : String) (init : MlirValue) (last : Bool) : String :=
    let body := "%" ++ name ++ " = " ++ show_mlir_value init in
    if last then body else body ++ ", "

/// ` -> (f64, f32)`, empty for an empty list.
#[partial]
def result_types_text (tys : List MlirType) : String :=
    let body := type_list tys in
    if String.is_empty body then "" else " -> (" ++ body ++ ")"

/// Types, comma-separated.
#[partial]
def type_list (tys : List MlirType) : String :=
    List.intercalate ", " (List.map show_one_type tys)

#[partial]
def show_one_type (t : MlirType) : String := show_mlir_type t

/// The induction variable is bound once, in the header, and the body
/// region carries no block header at all -- the measured shape. Asserted
/// because a `^bb0(%arg0: index):` line here is accepted by some MLIR
/// forms and rejected by `scf.for`'s, so the error would arrive as a
/// verifier message rather than as a compile error.
#[test]
def test_for_header_binds_the_induction_variable : Bool :=
    String.beq (for_header "iv" (MlirValue.named "c0") (MlirValue.named "c16")
        (MlirValue.named "c1")) "scf.for %iv = %c0 to %c16 step %c1"

/// `iter_args` names come from the caller, one per init, and the result
/// list is a separate `-> (...)`.
#[test]
def test_iter_args_pair_names_with_inits : Bool :=
    String.beq (for_iter_header "iv" (MlirValue.named "c0") (MlirValue.named "c16")
        (MlirValue.named "c1") ["s", "t"] [MlirValue.named "zero", MlirValue.named "one"]
        [MlirType.f64, MlirType.f32])
        "scf.for %iv = %c0 to %c16 step %c1 iter_args(%s = %zero, %t = %one) -> (f64, f32)"

/// A name list longer than the init list stops rather than reading past
/// it -- an arity mismatch is MLIR's verifier's to report, and this must
/// not be the thing that crashes first.
#[test]
def test_iter_args_stops_at_the_shorter_list : Bool :=
    String.beq (iter_args_text ["s"] List.empty) ""

/// No `iter_args` at all renders nothing -- not an empty pair of parens.
#[test]
def test_no_iter_args_is_empty : Bool :=
    String.beq (iter_args_text List.empty List.empty) ""
