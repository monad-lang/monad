/// The `builtin` dialect: the module op, and the type vocabulary shared by
/// every other dialect.
///
/// Almost always EMPTY, and that is the design. The `builtin` dialect's
/// job in an MLIR file is the module wrapper, and this backend does not
/// author one: a bare top-level `func.func` IS module level, and
/// `mlir-opt` supplies the `module { ... }` wrapper when it re-prints.
/// Phase 1's golden comparison asserts exactly that (see
/// `scripts/check-mlir-goldens.sh`), which is why the omission is
/// deliberate rather than pending.
///
/// What IS here is the two things a caller genuinely needs spelled:
/// `module_` for a caller that wants the wrapper explicitly, and the
/// `MlirType` vocabulary the dialect modules render (`index`, `iN`, `fN`).
/// The types live in `ir.mo` -- they are the model, not a dialect -- so
/// this module only re-exports the constructors a reader would look for
/// here.
///
/// Nothing in this file emits an op: an empty op list is what a `builtin`
/// module usually is, and a constructor with no callers is a guess.

use lib::ir {MlirType}

/// `index` -- the induction-variable type `scf.for` uses, re-exported so
/// a dialect module can name it without importing `ir` for one constant.
pub def index_type : MlirType := MlirType.index

/// `memref<d0xd1x...xT>`, re-exported for the same reason.
pub def memref_type (dims : List I64) (elem : MlirType) : MlirType :=
    MlirType.memref_of dims elem

/// The `module {` line `mlir-opt` re-prints around every top-level op.
///
/// Exposed as a STRING rather than as a region, because the wrapper is not
/// part of this backend's model: `MlirModule` is a function list
/// (`ir.mo`), and this exists so the round-trip test can name what it
/// expects to see on the other side without hard-coding the text twice.
pub def module_open : String := "module {"

/// The matching close.
pub def module_close : String := "}"
