/// `#[kernel]` host integration: the `MlirModule` a kernel compiles from, and
/// the two names the host links against.
///
/// ## What this module is for, and what it deliberately is NOT
///
/// The plan's Decision 3 is the reason this module is small: with
/// `convert-func-to-llvm{use-bare-ptr-memref-call-conv=1}`, a kernel lowers to
/// a PLAIN C FUNCTION -- `void @monad_kernel_saxpy(float*, i64)` -- whose
/// preconditions the kernel subset already enforces (identity layout, static
/// dimensions, `allocated == aligned`, no allocation). So the host side of a
/// kernel is an ordinary `#[extern "c"]` call, and the whole boxed-`i64` -> C
/// marshalling already exists in `emit.mo`'s
/// `compile_extern_def_wrapper_ir`.
///
/// That is why this module does **not** emit any LLVM IR. Its job is the two
/// things that are genuinely new:
///
/// 1. **Assemble the `MlirModule`** the kernel compiles from -- the
///    `func.func` whose signature is `shape.mo`'s and whose body is
///    `scalar.mo`'s. One function per kernel, at module level.
/// 2. **Name the two artifacts** the host needs: the kernel's own symbol
///    (`<def>`, what the compiled `.o` defines and the host calls) and the
///    REFERENCE body's symbol (`<def>__ref`, the Monad implementation the
///    interpreter runs). The pair is the plan's differential oracle: a kernel
///    has a Monad body, so `monad run` executes it and the two can be compared
///    number for number.
///
/// ## Why the reference body is a NAME and not emitted here
///
/// The reference body is the kernel's ORDINARY Monad def. The LLVM backend
/// already compiles it (`compile_db_def_ir` has no kernel special case), so
/// emitting a second copy under a `__ref` name would be a second
/// implementation of the same function -- exactly the differential check's
/// failure mode, where a bug the two share is invisible. `reference_symbol`
/// therefore names what the ordinary backend emits, and `host.mo`'s caller
/// decides whether to alias it.
///
/// ## Where the `ExternInfo` comes from, and why it is not built here
///
/// The plan's Decision 3 says the host side "reduces to synthesising an
/// `ExternInfo`". It does not, however, reduce to doing it *in this module*:
/// `ExternInfo` is private to `emit.mo` (`:4350`), and `emit.mo` is the file
/// that will import this one for the third arm of `compile_db_def_ir`. An
/// import back the other way would be a module cycle, and making `ExternInfo`
/// `pub` would leak the LLVM model into a module whose whole point is to stay
/// free of it.
///
/// So the split is: **this module carries the ABI as data** (`KernelAbi`, a
/// list of C spellings plus a return), and **`emit.mo`'s third arm turns that
/// into an `ExternInfo`** and hands it to the existing
/// `compile_extern_def_wrapper_ir`. That keeps the dependency edge one-way
/// (`emit` -> `host`), keeps the LLVM model out of this file, and leaves the
/// synthesis where the type it produces is already in scope. The same third
/// arm emits the `<def>__ref` alias for the reference body, because that is
/// LLVM IR and this module emits none.
use lang::types {Def, Term}
use lib::decls {def_name_str}
use lib::kernel::detect {KernelDiagnostic}
use lib::kernel::mono {KernelExtract}
use lib::kernel::scalar {KernelBody, emit_kernel_body}
use lib::kernel::shape {KernelShape, ParamShape, result_types_of, show_signature}
use mlir::ir {MlirBlock, MlirFunction, MlirModule, MlirParam, MlirType}
use mlir::print {print_module}

// ─── the two names ───────────────────────────────────────────────────

/// The symbol the COMPILED kernel defines, and the one the host calls.
///
/// `def_name_str` is codegen's own spelling (`def_symbol_name`), so the name
/// here and the name `compile_db_def_ir` emits for the same def agree by
/// construction -- the plan records a real link error from the last time the
/// define side and the call side disagreed about a dotted name.
pub def kernel_symbol (shape : KernelShape) : String := shape.name

/// The symbol the REFERENCE body is known by: the same name with `__ref`
/// appended.
///
/// A distinct name rather than the def's own, because the two live in one
/// binary: the MLIR-compiled kernel and the ordinary LLVM-compiled body are
/// different functions with the same source-level def, and linking them under
/// one symbol is a duplicate-definition error.
pub def reference_symbol (shape : KernelShape) : String :=
    String.concat shape.name "__ref"

// ─── the module ──────────────────────────────────────────────────────

/// A kernel's whole `.mlir` file: one `func.func`, at module level.
///
/// One function because a kernel IS one function -- helpers are inlined by
/// `mono.mo`, so nothing else is reachable. `MlirModule` is a flat function
/// list rather than an explicit `builtin.module` region, which is what
/// `mlir-opt` re-prints for a bare top-level `func.func`.
#[partial]
pub def kernel_module (shape : KernelShape) (body : KernelBody) : MlirModule :=
    MlirModule.of_functions (List.cons (kernel_function shape body) List.empty)

/// The `func.func`: `shape.mo`'s signature, `scalar.mo`'s body.
///
/// `KernelShape.mlir_params` drops the `dim_` entries -- they were folded into
/// the memref types -- so the emitted arity is the C arity, which is what
/// Decision 3's bare-pointer convention needs.
pub def kernel_function (shape : KernelShape) (body : KernelBody) : MlirFunction :=
    MlirFunction.function shape.name (KernelShape.mlir_params shape) shape.results body.block

/// The rendered `.mlir` text -- what `mlir-opt` is handed.
pub def render_module (module_ : MlirModule) : String := print_module module_

/// A kernel's `.mlir` in one step: assemble, then render.
///
/// The order is deliberate: `emit_kernel_body` can report a diagnostic, and a
/// caller that renders first would have to re-check readiness anyway. This
/// function returns BOTH, so a caller never has a rendered module it should not
/// compile.
#[partial]
pub def render_kernel (shape : KernelShape) (extract : KernelExtract) : KernelModule :=
    let body : KernelBody := emit_kernel_body shape extract in
    let module_ : MlirModule := kernel_module shape body in
    // The text is emitted ONLY when the body is ready. A dirty kernel's
    // `emit_kernel_body` returns an EMPTY block, so rendering it would hand
    // `mlir-opt` a bodyless `func.func` -- a verifier complaint that buries the
    // real diagnostic. The readiness gate is `KernelModule.ready`'s contract,
    // and this is where it is kept.
    let text : String := if List.is_empty body.diagnostics then render_module module_ else "" in
    KernelModule.mk shape.name (reference_symbol shape) text body.diagnostics

/// A kernel's two names and its rendered module, with everything that stopped
/// a full emission.
pub struct KernelModule {
    /// The compiled kernel's symbol.
    kernel : String,
    /// The reference body's symbol.
    reference : String,
    /// The `.mlir` text. `""` when `diagnostics` is non-empty -- there is
    /// nothing to compile, and handing `mlir-opt` an empty module would be a
    /// second, worse diagnostic.
    text : String,
    /// Everything that stopped a full emission.
    diagnostics : List KernelDiagnostic,
}

/// Is the module free of diagnostics -- ready for `mlir-opt`?
pub def KernelModule.ready (m : KernelModule) : Bool := List.is_empty m.diagnostics

// ─── the host ABI ────────────────────────────────────────────────────

/// The C ABI of a kernel: what `#[extern "c"]` declares, and what
/// `convert-func-to-llvm{use-bare-ptr-memref-call-conv=1}` produces.
///
/// Every `Buf` becomes a bare `i8*` (the plan's Decision 3: one pointer to the
/// aligned data, not MLIR's five-word memref descriptor) and every scalar keeps
/// its width. The struct exists so the ABI is a VALUE a caller can assert on,
/// rather than a fact spread across a declaration string -- and so the third
/// arm of `compile_db_def_ir` has one thing to synthesise an `ExternInfo` from.
pub struct KernelAbi {
    /// One entry per C parameter, in declaration order. `dim_` parameters are
    /// absent: they were folded into the memref's static shape.
    params : List KernelAbiParam,
    /// The C return type, or `Option.none` for a `Unit`-returning kernel.
    ret : Option KernelAbiParam,
}

/// One C parameter: a name and its C spelling.
pub struct KernelAbiParam {
    name : String,
    /// `"ptr"` for a `Buf`, or the scalar's C spelling (`"i64"`, `"f32"`).
    /// A STRING rather than an `LLVMType` so this module stays free of the
    /// LLVM model -- `emit.mo` is what turns a spelling into a type, and it
    /// already has the table.
    c_type : String,
}

/// The kernel's C ABI, from its shape.
#[partial]
pub def kernel_abi (shape : KernelShape) : KernelAbi :=
    KernelAbi.mk (abi_params shape.params) (abi_result shape.results)

#[partial]
def abi_params (params : List ParamShape) : List KernelAbiParam := match params {
    List.empty => List.empty,
    List.cons p rest =>
        match p {
            ParamShape.buffer_ name _elem _dims _noalias =>
                List.cons (KernelAbiParam.mk name "ptr") (abi_params rest),
            ParamShape.scalar_ name ty _noalias =>
                List.cons (KernelAbiParam.mk name (c_scalar_name ty)) (abi_params rest),
            ParamShape.dim_ _name => abi_params rest,
        },
}

/// The C return type, or `none` for `Unit` (whose MLIR result list is empty).
#[partial]
def abi_result (results : List MlirType) : Option KernelAbiParam := match results {
    List.empty => Option.none,
    List.cons ty _ => Option.some (KernelAbiParam.mk "_ret" (c_scalar_name ty)),
}

/// The C spelling of an MLIR scalar type.
///
/// The widths are the ABI's, not a widening: an `f32` argument crosses the C
/// boundary as a `float` and an `i32` as an `int32_t`, because the kernel was
/// compiled against those exact widths.
#[partial]
def c_scalar_name (ty : MlirType) : String := match ty {
    MlirType.int_ width => String.concat "i" (I64.to_string width),
    MlirType.float_ spelling => spelling,
    MlirType.index_ => "index",
    MlirType.memref_ _dims _elem => "ptr",
    MlirType.llvm_ptr => "ptr",
    MlirType.opaque_ spelling => spelling,
}

/// The kernel's C signature as text -- what an `#[extern "c"]` declaration
/// would spell, and what a diagnostic or a `monad kernels` line prints.
///
/// Rendered from the ABI rather than from the MLIR types so a reader sees the
/// HOST's view of the kernel: `void monad_kernel_saxpy(ptr, i64)` is the
/// declaration the linker needs, while `saxpy(memref<16xf32>, index)` is the
/// compiler's view of the same function.
pub def show_abi (abi : KernelAbi) : String :=
    String.concat (abi_ret_text abi.ret)
        (String.concat "(" (String.concat (show_abi_params abi.params) ")"))

#[partial]
def abi_ret_text (ret : Option KernelAbiParam) : String := match ret {
    Option.none => "void",
    Option.some p => p.c_type,
}

/// `i64, f32` -- comma-separated, no trailing separator.
///
/// The separator is built into the recursion rather than appended afterwards,
/// because a first version appended a space to EVERY entry and produced
/// `i64(i64 )` for a one-parameter kernel -- a stray space a golden comparison
/// would have to encode. `mlir/print.mo`'s `print_param_with_separator` is the
/// same shape for the same reason.
#[partial]
def show_abi_params (params : List KernelAbiParam) : String :=
    String.concat_list (List.reverse (show_abi_params_go params List.empty))

#[partial]
def show_abi_params_go (params : List KernelAbiParam) (acc : List String) : List String := match params {
    List.empty => acc,
    List.cons p rest =>
        show_abi_params_go rest
            (List.cons (if List.is_empty rest then p.c_type else String.concat p.c_type ", ") acc),
}

// ─── the summary a `monad kernels` line prints ───────────────────────

/// One line per kernel: its MLIR signature and its C ABI.
///
/// Both, because they answer different questions and a reader debugging a
/// kernel needs both: the MLIR signature is what `mlir-opt` sees, the C ABI is
/// what the linker sees, and a mismatch between them is exactly the class of
/// bug Decision 3's bare-pointer convention exists to prevent.
pub def describe (shape : KernelShape) : String :=
    String.concat (show_signature shape)
        (String.concat "  [c: " (String.concat (show_abi (kernel_abi shape)) "]"))
