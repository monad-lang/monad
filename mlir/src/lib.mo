/// The mlir mote's library root -- bare `use mlir` resolves here.
///
/// Everything here is compiler-agnostic: the MLIR data model and its text
/// rendering (`mlir.ir`, `mlir.print`), the pass pipelines as data
/// (`mlir.pipeline`), the target vocabulary (`mlir.target`), the
/// external-tool glue (`mlir.tool`), and one module per dialect this
/// backend emits (`mlir.dialect.*`).
///
/// Nothing in this mote knows what a Monad term is. That is the seam the
/// kernel emitter (`codegen/src/kernel/`, Phase 2) sits on, and it is what
/// lets this phase's goldens run with no front end at all.
///
/// The re-export list is deliberately short, for the reason
/// `codegen/src/lib.mo` gives: a hub mirroring the whole mote would be a
/// second, always-stale index of it. Consumers name the module they want
/// (`mlir::print`, `mlir::tool`, `mlir::dialect::arith`).
///
/// The one thing re-exported from every module is the TYPE (or the single
/// pipeline string) a caller cannot work without: a Phase 2 emitter builds
/// an `MlirModule`, hands it to `print_module`, and passes a
/// `cpu_pipeline_string` to the tool glue, so those three names carry the
/// whole seam. Everything else -- every op constructor, every pass step --
/// is reached by naming its dialect module, which is what keeps this file
/// from needing an edit every time a dialect grows an op.

pub use lib::ir {
    MlirAttr, MlirBlock, MlirFunction, MlirModule, MlirOp, MlirParam,
    MlirType, MlirValue, mlir_loc, show_mlir_attr,
    show_mlir_type, show_mlir_value,
}
pub use lib::print {print_module}
pub use lib::target {MlirTarget}
pub use lib::pipeline {
    MlirPipeline, cpu_pipeline_string, gpu_pipeline_string,
}
pub use lib::tool {
    MlirToolRun, mlir_opt_available, mlir_opt_version, run_mlir_opt,
    run_mlir_opt_reprint, run_mlir_opt_verified, run_mlir_runner,
    run_mlir_translate,
}
