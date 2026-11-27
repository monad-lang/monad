/// The `IO` half of a kernel build: each ready `KernelPlan`'s `.mlir` text
/// through `mlir-opt` (the CPU pipeline), `mlir-translate` and `llc`, to an
/// object the final link takes beside the program's own.
///
/// Split from the pure `compile_db_def_ir` the way `link_ir` is split from
/// `compile_db_module_with_debug`: codegen only needs each compiled kernel's
/// ABI, and this step is what decides which kernels have an object at all.
/// A kernel whose tools fail is reported and compiles as its ordinary body,
/// so a missing `mlir-opt` slows a program down rather than breaking it.
use lib::kernel::detect {KernelDiagnostic}
use lib::kernel::host {KernelAbi}
use lib::kernel::plan {KernelPlan}
use llvm::link {compile_ir_to_obj, mkdir_parent}
use mlir::pipeline {cpu_pipeline}
use mlir::tool {MlirToolRun, run_mlir_opt, run_mlir_translate}
use std::log {fail_line}

/// A kernel with an object: its symbol, its C ABI, and the `.o` to link.
pub struct CompiledKernel {
    name : String,
    abi : KernelAbi,
    object : Path,
}

/// What `compile_db_module_with_kernels` takes.
pub def CompiledKernel.entry (k : CompiledKernel) : Pair String KernelAbi := Pair.pair k.name k.abi

/// Compile every ready plan into `dir`; report every other plan's
/// diagnostics and every tool failure on stderr. Plans that are not ready
/// are not errors: their defs compile as ordinary functions.
#[partial]
pub def compile_kernels (plans : List KernelPlan) (dir : Path) : IO (List CompiledKernel) := match plans {
    List.empty => IO.pure List.empty,
    List.cons p rest => do {
        let here <- compile_kernel p dir;
        let later <- compile_kernels rest dir;
        return (List.append here later)
    },
}

#[partial]
def compile_kernel (p : KernelPlan) (dir : Path) : IO (List CompiledKernel) :=
    if KernelPlan.ready p then compile_ready_kernel p dir
    else do {
        report_not_a_kernel p.name p.diagnostics;
        return List.empty
    }

#[partial]
def compile_ready_kernel (p : KernelPlan) (dir : Path) : IO (List CompiledKernel) := do {
    let stem : String := file_stem p.name;
    let mlir : Path := Path.join dir (Path.path (String.concat stem ".mlir"));
    let lowered : Path := Path.join dir (Path.path (String.concat stem ".llvm.mlir"));
    let ll : Path := Path.join dir (Path.path (String.concat stem ".ll"));
    let obj : Path := Path.join dir (Path.path (String.concat stem ".o"));
    let _mk <- mkdir_parent mlir;
    let _w <- IO.write_file mlir p.text;
    let opt <- run_mlir_opt cpu_pipeline (Path.to_string mlir) (Path.to_string lowered);
    if Bool.not (MlirToolRun.is_ok opt) then tool_failed p.name (MlirToolRun.message opt)
    else do {
        let tr <- run_mlir_translate (Path.to_string lowered) (Path.to_string ll);
        if Bool.not (MlirToolRun.is_ok tr) then tool_failed p.name (MlirToolRun.message tr)
        else do {
            let rc <- compile_ir_to_obj ll obj;
            if Bool.not (I64.beq rc 0) then tool_failed p.name "llc failed on the translated kernel"
            else do {
                let k : CompiledKernel := { name := p.name, abi := p.abi, object := obj };
                return [k]
            }
        }
    }
}

/// The kernel's symbol as a file name: `main::k` -> `main__k`, since `:` is
/// not a portable file-name byte. The symbol itself keeps its `::`.
#[partial]
pub def file_stem (name : String) : String := match String.index_of name "::" {
    Option.none => name,
    Option.some i =>
        String.concat_all [String.slice name 0 i, "__",
            file_stem (String.slice name (i + 2) (String.length name - i - 2))],
}

#[partial]
def tool_failed (name : String) (message : String) : IO (List CompiledKernel) := do {
    fail_line (String.concat_all ["kernel '", name, "' compiles as its ordinary body: ", message]);
    return List.empty
}

#[partial]
def report_not_a_kernel (name : String) (diags : List KernelDiagnostic) : IO Unit := match diags {
    List.empty => IO.pure Unit.unit,
    List.cons d rest => do {
        fail_line (String.concat_all ["kernel '", name, "' compiles as its ordinary body: ", KernelDiagnostic.render d]);
        report_not_a_kernel name rest
    },
}
