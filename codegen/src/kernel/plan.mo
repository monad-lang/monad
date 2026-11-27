/// Every `#[kernel]` in a program, carried from its def to the `.mlir` text
/// and C ABI the build needs: the one composition of `detect.mo`, `mono.mo`,
/// `shape.mo`, `scalar.mo` and `host.mo`.
///
/// Pure. `monad kernels` prints a plan; the build compiles each ready plan's
/// `text` through MLIR and hands the ABI to `compile_db_module_with_kernels`.
/// A plan that is not ready is not an error: its def compiles as an ordinary
/// function, and its diagnostics say why it did not become a kernel.
use lang::types {Decl, Def, Term}
use lib::decls {def_name_str}
use lib::kernel::detect {KernelDiagnostic, check_kernel, extract_kernels}
use lib::kernel::host {KernelAbi, KernelModule, describe, kernel_abi, render_kernel}
use lib::kernel::mono {
    KernelCallSite, KernelExtract, call_sites_of, extract_kernel, int_literal_of, kernel_params,
}
use lib::kernel::shape {
    KernelShape, ParamShape, dim_positions_from_shapes, noalias_flags_of, param_shapes_of,
    shape_diagnostic, shape_of_kernel,
}
use std::list {List.any}

/// One kernel, planned.
pub struct KernelPlan {
    /// The kernel's symbol (`def_symbol_name`).
    name : String,
    shape : KernelShape,
    abi : KernelAbi,
    /// The extracted body (inlined and reduced) `scalar.mo` lowered.
    body : Term,
    /// The `.mlir` text; `""` unless `diagnostics` is empty.
    text : String,
    /// Everything that keeps this def from compiling as a kernel, from every
    /// stage, in stage order.
    diagnostics : List KernelDiagnostic,
}

/// Can the build compile this plan through MLIR?
pub def KernelPlan.ready (p : KernelPlan) : Bool := List.is_empty p.diagnostics

/// The `monad kernels` line: the MLIR signature and C ABI, then the verdict.
#[partial]
pub def KernelPlan.describe (p : KernelPlan) : String :=
    if KernelPlan.ready p then String.concat (describe p.shape) "  ok"
    else String.concat (describe p.shape) "  not a kernel:"

/// A plan per `#[kernel]` def in `decl_list`, in declaration order.
#[partial]
pub def plan_kernels (decl_list : List Decl) : List KernelPlan :=
    List.map (fn (k : Def) => plan_kernel decl_list k) (extract_kernels decl_list)

/// One kernel's plan. Dims come from its call sites: every site must pass
/// the same literal at each dim position, which is what makes the memref
/// shape static.
#[partial]
pub def plan_kernel (decl_list : List Decl) (k : Def) : KernelPlan :=
    let name : String := def_name_str k in
    let sites : List KernelCallSite := call_sites_of decl_list [name] in
    let unfilled : List ParamShape := param_shapes_of (kernel_params k) (noalias_flags_of k) in
    let positions : List I64 := dim_positions_from_shapes unfilled in
    let dims : List I64 := first_site_dims sites positions in
    let extract : KernelExtract := extract_kernel k decl_list sites positions in
    let shape : KernelShape := shape_of_kernel k dims in
    let module_ : KernelModule := render_kernel shape extract in
    let diags : List KernelDiagnostic :=
        List.append (check_kernel k)
            (List.append (dim_agreement_diags name sites positions dims) module_.diagnostics) in
    { name := name, shape := shape, abi := kernel_abi shape, body := extract.body,
        text := if List.is_empty diags then module_.text else "",
        diagnostics := diags }

/// The literal dims of the first call site, one per dim position. A site
/// with a non-literal dim yields nothing for it; `mono.mo` already reports
/// that as a `dim` diagnostic.
#[partial]
def first_site_dims (sites : List KernelCallSite) (positions : List I64) : List I64 := match sites {
    List.empty => List.empty,
    List.cons s _ => literal_args_at s.args positions,
}

#[partial]
def literal_args_at (args : List Term) (positions : List I64) : List I64 := match positions {
    List.empty => List.empty,
    List.cons i rest => match List.get i args {
        Option.some a => match int_literal_of a {
            Option.some v => List.cons v (literal_args_at args rest),
            Option.none => literal_args_at args rest,
        },
        Option.none => literal_args_at args rest,
    },
}

/// One kernel compiles to one function, so every call site must agree on
/// its dims; a site that disagrees with the first needs its own kernel.
#[partial]
def dim_agreement_diags (name : String) (sites : List KernelCallSite) (positions : List I64) (dims : List I64) : List KernelDiagnostic :=
    if List.any (fn (s : KernelCallSite) => Bool.not (same_dims (literal_args_at s.args positions) dims)) sites
    then [shape_diagnostic name "call sites pass different dimensions; one kernel has one static shape"]
    else List.empty

#[partial]
def same_dims (a : List I64) (b : List I64) : Bool := match a {
    List.empty => List.is_empty b,
    List.cons x xs => match b {
        List.empty => false,
        List.cons y ys => I64.beq x y && same_dims xs ys,
    },
}
