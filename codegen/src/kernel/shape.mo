/// `#[kernel]` shapes: an extracted kernel's elaborated signature -> the
/// MLIR types `scalar.mo` emits.
///
/// ## What this module is for
///
/// `mono.mo` produces a `KernelExtract`: a name, the kernel's explicit
/// parameters, and an inlined-and-reduced body. This module turns the
/// PARAMETERS into MLIR types -- `Buf F32` -> `memref<nxf32>`, `I64` -> `i64`
/// -- and reports the ways a signature can be outside the subset.
///
/// It is the plan's `shape.mo` item ("folded dims -> `MlirType`; `Buf E` ->
/// `memref<nx...>`"), and it is also where the SIXTH subset rule gets its
/// real answer: `mono.mo` ships `dim_positions_of`, which calls every explicit
/// `I64` parameter a dimension. That is an honest over-approximation, and
/// `dim_positions_from_shapes` here replaces it with the structural answer --
/// the `I64` parameters that FOLLOW a `Buf` parameter, which is the ABI
/// convention `saxpy (dst : Buf F32) (n : I64)` spells.
///
/// ## The measurement that shaped the interface
///
/// The plan left one question open: whether an elaborated kernel that takes a
/// `Buf F32` carries an implicit `{Buf : Type}` binder, which `detect.mo`'s
/// polymorphism rule would then reject -- i.e. whether a `Buf`-taking kernel
/// is *unwritable*. **Measured 2026-11-15 through `elaborate_loaded_modules`
/// (the real front end), and the answer is no:**
///
/// ```monad,ignore
/// #[kernel] def saxpy (dst : Buf F32) (n : I64) : Unit := unit
/// // elaborated type := ((Buf F32) -> (I64 -> Unit))
/// //   binder explicit=true name=dst dom=(Buf F32)
/// //   binder explicit=true name=n   dom=I64
/// // polymorphic? false
/// ```
///
/// The elaborator does NOT introduce a binder for `Buf`'s own type parameter:
/// it stays an unresolved name inside the domain, exactly as `I64` does. So
/// the pi spine IS the source signature, `detect.mo`'s rule 3 accepts it, and
/// this module reads the domains off it directly.
///
/// ## The dimension value is NOT in the def, and that is the whole point
///
/// A kernel's `n` parameter is an `I64` whose VALUE is a call-site literal
/// (the plan's sixth rule, `mono.mo`'s `dim` tag). So this module derives the
/// signature's SHAPE from the def alone -- which positions are buffers, which
/// are their dimensions, what the element types are -- and takes the folded
/// dimension VALUES as an argument. `shape_of_kernel` is that composition;
/// `param_shapes_of` alone is enough for the `monad kernels` subcommand, which
/// reports the shape with the dimensions symbolic rather than inventing a
/// number no call site supplied.
///
/// ## Why the result list is small
///
/// `Unit` -> no results, an `I64`/`I32`/`F32`/`F64` -> one result, anything
/// else -> a `shape` diagnostic. A kernel returning a `Buf` or a boxed ADT is
/// outside the subset for the same reason one *taking* it is: the host owns
/// the buffer, and there is no allocator on the device (the plan's "no GC
/// allocation" rule).
///
/// ## A `Buf` with no dimension is a diagnostic, not a rank-0 memref
///
/// `MlirType.memref_of` cannot spell a dynamic `?` dimension (that is
/// deliberate: Decision 5 folds every dimension). So a kernel whose `Buf`
/// parameter is not followed by an `I64` bound has no static shape at all, and
/// this module reports a `shape` finding rather than emitting a rank-0
/// `memref<f32>` -- which would be a *different type*, not a smaller one.
/// Such a buffer carries a `[1]` placeholder that is never emitted, because
/// `KernelShape.ready` is false.
///
/// ## No `mlir` dependency beyond the data model
///
/// This module imports `mlir::ir` (`MlirType`, `MlirParam`) and nothing else
/// from that mote: no dialects, no printer, no tool glue. It does NOT import
/// `scalar.mo`'s `arith`/`scf`/`memref` ops, so the shape half is testable
/// with no emitter at all -- the same split Phase 1's goldens rest on.
///
/// **This is the first `codegen -> mlir` import in the tree.** The same
/// commit therefore adds `"mlir"` to `scripts/build-self-hosted.sh`'s
/// staleness scan and to `nix/monad.nix`'s `compilerSrc` fileset, and
/// `[dependencies.mlir]` to `codegen/mote.toml`: from here on `mlir/` is
/// compiled INTO the compiler and is part of the compiler-source surface
/// (the plan's "Phase 2's costs the item list does not name", item 1).
use lang::types {
    Binder, Con, DebugName, Def, Identifier, Multiplicity, Term, binder_is_explicit,
    term_peel,
}
use lib::decls {def_name_str}
use lib::kernel::detect {KernelDiagnostic}
use lib::kernel::mono {KernelExtract, KernelParam, id_text, kernel_params}
use mlir::ir {MlirParam, MlirType, show_mlir_type}
use std::list {List.intercalate}

// ─── the derived signature ───────────────────────────────────────────

/// One kernel parameter, in the subset's terms.
///
/// A dimension parameter is its own constructor rather than a `scalar_` with
/// a flag, because the two are treated differently in every consumer: a `dim_`
/// never becomes an MLIR parameter (it is consumed as a `memref` bound), and
/// it is the thing the sixth rule judges at the call site.
pub type ParamShape {
    /// A `Buf E` argument. `dims` are the folded dimension values, in the
    /// order the kernel's dimension parameters were declared.
    buffer_ (name : String) (elem : MlirType) (dims : List I64) (noalias : Bool),
    /// A scalar argument: `I64`, `I32`, `U8`, `F32`, `F64`, `Bool`.
    scalar_ (name : String) (ty : MlirType) (noalias : Bool),
    /// An `I64` parameter that bounds a preceding `Buf`. Consumed as a
    /// `memref` dimension, so it is not an MLIR parameter of its own.
    dim_ (name : String),
}

/// A kernel's derived MLIR signature.
pub struct KernelShape {
    /// The kernel's symbol, spelled the way codegen spells it -- what
    /// `host.mo` needs to name the emitted function.
    name : String,
    params : List ParamShape,
    /// The result types. Empty for a `Unit`-returning kernel, which is every
    /// kernel the plan's examples write.
    results : List MlirType,
    /// Everything that stops this signature being emittable: a `shape` finding
    /// for a parameter or result type outside the subset, and a `dim` finding
    /// for a dimension the call site did not supply as a literal.
    diagnostics : List KernelDiagnostic,
}

/// Is the signature free of diagnostics -- ready for `scalar.mo`?
pub def KernelShape.ready (s : KernelShape) : Bool := List.is_empty s.diagnostics

/// The signature's MLIR parameters, in declaration order: one per `buffer_`
/// and `scalar_`, with the `dim_` entries dropped because they were folded
/// into the memref types.
///
/// `noalias` comes from the parameter's binder multiplicity (see
/// `noalias_flags_of`), which is Decision 3's carrier for the aliasing facts
/// quantitative types would eventually supply.
pub def KernelShape.mlir_params (s : KernelShape) : List MlirParam :=
    mlir_params_of s.params

#[partial]
def mlir_params_of (params : List ParamShape) : List MlirParam := match params {
    List.empty => List.empty,
    List.cons p rest =>
        match p {
            ParamShape.buffer_ name elem dims noalias =>
                List.cons (mlir_param name (MlirType.memref_of dims elem) noalias)
                    (mlir_params_of rest),
            ParamShape.scalar_ name ty noalias =>
                List.cons (mlir_param name ty noalias) (mlir_params_of rest),
            ParamShape.dim_ _name => mlir_params_of rest,
        },
}

/// `MlirParam.restrict` or `MlirParam.plain`, picked by the flag. A helper
/// rather than a conditional at each call site because a bare struct literal
/// in argument position is the miscompile trap `MlirParam.plain`'s own doc
/// comment records.
def mlir_param (name : String) (ty : MlirType) (noalias : Bool) : MlirParam :=
    if noalias then MlirParam.restrict name ty else MlirParam.plain name ty

/// The signature's result list. Empty when the kernel returns `Unit`, which is
/// the shape every Phase 2 kernel has.
pub def KernelShape.mlir_results (s : KernelShape) : List MlirType := s.results

/// `saxpy(dst: memref<16xf32>, n: index) -> ()` -- the one-line signature the
/// `monad kernels` subcommand prints, and the string a diagnostic quotes.
///
/// A `dim_` parameter IS shown, as `n: index`: it is not an MLIR parameter (it
/// was folded into the memref), but the plan's own rejection message names
/// `n`, and dropping it silently would make the printed signature
/// unrecognisable to the author who wrote it.
pub def show_signature (s : KernelShape) : String := match s {
    { name, params, results, .. } =>
        String.concat name
            (String.concat "("
                (String.concat (show_shape_params params)
                    (String.concat ")" (show_shape_results results)))),
}

#[partial]
def show_shape_params (params : List ParamShape) : String :=
    List.intercalate ", " (List.map show_shape_param params)

def show_shape_param (p : ParamShape) : String := match p {
    ParamShape.buffer_ name elem dims _noalias =>
        String.concat name (String.concat ": " (show_mlir_type (MlirType.memref_of dims elem))),
    ParamShape.scalar_ name ty _noalias =>
        String.concat name (String.concat ": " (show_mlir_type ty)),
    ParamShape.dim_ name => String.concat name ": index",
}

def show_shape_results (results : List MlirType) : String :=
    let body : String := show_result_list results in
    if String.is_empty body then " -> ()" else " -> (" ++ body ++ ")"

#[partial]
def show_result_list (results : List MlirType) : String :=
    List.intercalate ", " (List.map show_mlir_type results)

// ─── classifying one parameter ───────────────────────────────────────

/// Is `t` a `Buf E` -- `Buf` applied to one argument, by bare name?
///
/// A NAME test rather than a type comparison, for the same reason `detect.mo`'s
/// rules are name tests: this module has no `Scope`, and a kernel's elaborated
/// domain is a small first-order term where a name is precise enough to be
/// actionable. Deliberately NOT a test for `ByteBuf`: `Buf E` is the
/// polymorphic surface the kernel ABI is defined over (`std/src/buf.mo`), and
/// `ByteBuf` is its `u8` case, reached as `Buf U8`.
#[partial]
pub def is_buffer_type (t : Term) : Bool := match term_peel t {
    Term.app f _arg => name_is f "Buf",
    _ => false,
}

/// The element type of a `Buf E`, or `Option.none` when `t` is not one (or its
/// element type is not a scalar this backend knows).
#[partial]
pub def buffer_elem_type_of (t : Term) : Option MlirType := match term_peel t {
    Term.app f arg => if name_is f "Buf" then scalar_mlir_type_of arg else Option.none,
    _ => Option.none,
}

/// The MLIR scalar type for a Monad scalar type name, or `Option.none`.
///
/// The widths are the ABI's, not a widening: `I32` -> `i32` (four bytes, what
/// `Buf I32`'s element stride already is), `U8` -> `i8`, `Bool` -> `i1`. An
/// unknown name answers `none` so the caller reports a `shape` diagnostic
/// naming it, rather than silently emitting `i64` over a payload that is not
/// eight bytes.
#[partial]
pub def scalar_mlir_type_of (t : Term) : Option MlirType :=
    match bare_name_of t {
        Option.none => Option.none,
        Option.some n => scalar_mlir_type_named n,
    }

#[partial]
def scalar_mlir_type_named (n : String) : Option MlirType :=
    if String.beq n "I64" then Option.some MlirType.i64
    else if String.beq n "I32" then Option.some MlirType.i32
    else if String.beq n "I16" then Option.some (MlirType.int_ 16)
    else if String.beq n "I8" then Option.some MlirType.i8
    else if String.beq n "U64" then Option.some MlirType.i64
    else if String.beq n "U32" then Option.some MlirType.i32
    else if String.beq n "U16" then Option.some (MlirType.int_ 16)
    else if String.beq n "U8" then Option.some MlirType.i8
    else if String.beq n "F64" then Option.some MlirType.f64
    else if String.beq n "F32" then Option.some MlirType.f32
    else if String.beq n "Bool" then Option.some MlirType.i1
    else Option.none

/// The bare (last dotted segment) name of a type-shaped term, or `Option.none`
/// when it is not a name at all.
///
/// Both spellings are handled, exactly as `mono.mo`'s `constructor_head_of`
/// documents: a `Term.var` head (what the parser and the elaborator build for
/// a type reference) and a `Term.con` (what a hand-built fixture uses, and what
/// a zero-argument type is in an elaborated term).
#[partial]
pub def bare_name_of (t : Term) : Option String := match term_peel t {
    Term.var _idx dbg => match dbg {
        DebugName.named id => Option.some (last_segment (id_text id)),
        DebugName.unnamed => Option.none,
    },
    Term.con c => match c {
        Con.mk name _typ _n _args => Option.some (last_segment (id_text name)),
    },
    _ => Option.none,
}

/// Is `t` a name whose last dotted segment is `want`?
#[partial]
def name_is (t : Term) (want : String) : Bool := match bare_name_of t {
    Option.some n => String.beq n want,
    Option.none => false,
}

/// The segment after the LAST `.` -- `Foo.I64` -> `I64`. A name with no dot is
/// returned unchanged, so a bare `I64` works too.
///
/// `mono.mo` has its own `ctor_last_segment` for the same purpose. This is a
/// deliberate second copy rather than a shared helper, because the two serve
/// different namespaces: that one reduces a CONSTRUCTOR's dotted name for a
/// `match`-arm comparison, this one a TYPE's. Sharing would put a function
/// named for constructors in the type half's import list.
#[partial]
def last_segment (s : String) : String :=
    let i : I64 := last_dot_at s 0 (0 - 1) in
    if I64.lt i 0 then s else String.slice s (i + 1) (String.length s - i - 1)

#[partial]
def last_dot_at (s : String) (i : I64) (last : I64) : I64 :=
    if I64.gt (i + 1) (String.length s) then last
    else match String.get s i {
        Option.some b =>
            if U8.beq b 46u8 then last_dot_at s (i + 1) i else last_dot_at s (i + 1) last,
        Option.none => last,
    }

/// Is `t` the bare type name `I64`? A name test, like `is_buffer_type`, and
/// deliberately loose: a parameter whose type is an alias for `I64` is a
/// dimension too, and the cost of a false positive is one diagnostic on a
/// kernel whose dimension is genuinely non-literal.
#[partial]
pub def is_i64_type (t : Term) : Bool := name_is t "I64"

// ─── the parameter walk ──────────────────────────────────────────────

/// The parameter shapes for a kernel's `params`, with `noalias` read off
/// `flags` (one per parameter, in order).
///
/// The walk is stateful in exactly one way: an `I64` parameter is a `dim_` only
/// when a `buffer_` has already been seen and the most recent non-dimension
/// parameter was a buffer. That is the `saxpy (dst) (n)` / `scale (a) (n) (out)`
/// convention from the plan's own examples, and it is the structural answer
/// `mono.mo`'s over-approximation was waiting for.
///
/// Every OTHER `I64` is a `scalar_`: a kernel may take a plain integer that is
/// not a shape (a stride, a flag), and calling it a dimension would make the
/// sixth rule fire on a call site that is perfectly static.
#[partial]
pub def param_shapes_of (params : List KernelParam) (flags : List Bool) : List ParamShape :=
    param_shapes_go params flags false

#[partial]
def param_shapes_go (params : List KernelParam) (flags : List Bool) (after_buffer : Bool) : List ParamShape :=
    match params {
        List.empty => List.empty,
        List.cons p rest => match p {
            { typ, .. } =>
                let next_run : Bool := opens_a_dimension_run typ after_buffer in
                match flags {
                    // More parameters than flags: only reachable from a
                    // hand-built fixture, and `false` is the honest default (no
                    // multiplicity annotation means affine, not linear).
                    List.empty =>
                        List.cons (param_shape p false after_buffer)
                            (param_shapes_go rest List.empty next_run),
                    List.cons f more =>
                        List.cons (param_shape p f after_buffer)
                            (param_shapes_go rest more next_run),
                },
        },
    }

/// Whether the parameter whose type is `typ` makes the NEXT one a dimension:
/// a buffer does; another `I64` continues the run it is already in; anything
/// else ends it.
///
/// Takes the TYPE rather than the `KernelParam`, so the caller reads the
/// parameter record once (`param_shape` does the same) -- the affine checker
/// counts a field access as a use, and a `KernelParam` is not `Copy`.
#[partial]
def opens_a_dimension_run (typ : Term) (after_buffer : Bool) : Bool :=
    if is_buffer_type typ then true
    else if is_i64_type typ then after_buffer
    else false

/// One parameter's shape. `after_buffer` says whether an `I64` here is a
/// dimension rather than an ordinary scalar.
#[partial]
def param_shape (p : KernelParam) (noalias : Bool) (after_buffer : Bool) : ParamShape := match p {
    { name, typ } => match buffer_elem_type_of typ {
        Option.some elem => ParamShape.buffer_ name elem List.empty noalias,
        Option.none =>
            if is_buffer_type typ
            then ParamShape.buffer_ name MlirType.i64 List.empty noalias
            else if is_i64_type typ then
                if after_buffer
                then ParamShape.dim_ name
                else ParamShape.scalar_ name MlirType.i64 noalias
            else match scalar_mlir_type_of typ {
                Option.some ty => ParamShape.scalar_ name ty noalias,
                // An unknown type keeps an `i64` placeholder and is reported by
                // `param_type_diagnostics`; the placeholder is never emitted
                // because `KernelShape.ready` is false.
                Option.none => ParamShape.scalar_ name MlirType.i64 noalias,
            },
    },
}

/// One `noalias` flag per EXPLICIT binder of the kernel's declared type, in
/// declaration order -- read off the binder's multiplicity.
///
/// Decision 3: `memref` has no restrict/no-alias attribute of its own, so the
/// carrier for linearity-derived aliasing facts is `llvm.noalias` on the
/// `func.func` argument. A `linear` binder is the source of that fact
/// (`plans/type-system/quantitative-types.md`); an `affine` or `many` one is
/// not, because a second reference to the buffer may exist.
///
/// There is no multiplicity ANNOTATION syntax today
/// (`docs/src/linear-types.md`: the `!`, `?` and `%` prefixes were removed), so
/// every source-level kernel answers `false` -- but the flag is threaded rather
/// than hardcoded, so the emitted IR gains the attribute the moment the
/// multiplicity becomes reachable, with no change here.
#[partial]
pub def noalias_flags_of (kernel : Def) : List Bool := match kernel {
    Def.mk { typ, .. } => noalias_flags_in typ,
}

/// `noalias_flags_in`'s name for the `Def`-shaped caller, so a caller holding a
/// `Term` (a `KernelExtract` does not carry one, but a test may) does not have
/// to build a `Def` to ask.
#[partial]
pub def noalias_flags_for_type (typ : Term) : List Bool := noalias_flags_in typ

#[partial]
def noalias_flags_in (typ : Term) : List Bool := match term_peel typ {
    Term.pi b _dom ret =>
        if binder_is_explicit b
        then List.cons (binder_is_linear b) (noalias_flags_in ret)
        else noalias_flags_in ret,
    _ => List.empty,
}

def binder_is_linear (b : Binder) : Bool := match b {
    { mult := m, .. } => match m {
        Multiplicity.linear => true,
        _ => false,
    },
}

// ─── the result ──────────────────────────────────────────────────────

/// The kernel's declared result type: the pi spine's final codomain.
#[partial]
pub def result_type_of_kernel (kernel : Def) : Term := match kernel {
    Def.mk { typ, .. } => pi_codomain typ,
}

/// The final codomain of a pi chain.
///
/// The catch-all must be `_`, and that is a checker fact rather than taste: a
/// NAMED catch-all after a `Term.pi` arm is `constructor not found in
/// inductive` from the self-hosted checker (measured 2026-11-15 -- every name
/// tried is rejected, including `_`-prefixed ones). `_` parses and checks.
///
/// The `_` arm therefore has to re-read the parameter, which the affine
/// checker counts as a second use of a non-`Copy` `Term`. Splitting the walk
/// into a helper that takes the peeled term AND the original does not help --
/// the call site still reads `typ` twice -- so this def carries the warning
/// deliberately rather than being restructured around it.
#[partial]
pub def pi_codomain (typ : Term) : Term := match term_peel typ {
    Term.pi _b _dom ret => pi_codomain ret,
    _ => typ,
}

/// The result types for a kernel's declared return type: empty for `Unit`, one
/// entry for a scalar, empty (plus a diagnostic) for anything else.
///
/// `Unit` -> no results rather than a `()`, because MLIR spells "no results"
/// by omitting the `-> (...)` entirely, which is what `MlirFunction`'s empty
/// `results` list renders as.
#[partial]
pub def result_types_of (ret : Term) : List MlirType :=
    if name_is ret "Unit"
    then List.empty
    else match scalar_mlir_type_of ret {
        Option.some ty => List.cons ty List.empty,
        Option.none => List.empty,
    }

// ─── diagnostics ─────────────────────────────────────────────────────

/// One `shape` finding: a parameter or result type this backend cannot lower.
pub def shape_diagnostic (kernel : String) (detail : String) : KernelDiagnostic :=
    KernelDiagnostic.of kernel "shape" detail

/// The `shape` findings for a kernel's parameters and result: a `Buf` with no
/// dimension, a `Buf` whose element type is not a scalar, and a parameter or
/// result type that is not a scalar, buffer or `Unit`.
///
/// One rule per finding, each with its own message, because the remedy differs:
/// "give the buffer a dimension" is not "use a scalar".
#[partial]
pub def shape_diagnostics (name : String) (params : List KernelParam) (shapes : List ParamShape) (ret : Term) : List KernelDiagnostic :=
    List.append (param_type_diagnostics name params)
        (List.append (param_dim_diagnostics name shapes) (result_type_diagnostics name ret))

/// The diagnostics for a signature whose dimensions have ALREADY been folded.
///
/// `shape_of_kernel` calls this rather than `shape_diagnostics` directly, and
/// the distinction is load-bearing: the dimension rule must run over the
/// FILLED shapes, or every buffer reports "no dimension" even when the call
/// site supplied one. That was a real bug, caught by
/// `test_ready_when_every_dimension_is_supplied` -- every positive test that
/// only inspected the rendered signature passed while the kernel was
/// unemittable.
#[partial]
pub def filled_shape_diagnostics (name : String) (params : List KernelParam) (filled : List ParamShape) (ret : Term) : List KernelDiagnostic :=
    shape_diagnostics name params filled ret

/// A parameter whose type this backend cannot lower at all.
#[partial]
def param_type_diagnostics (name : String) (params : List KernelParam) : List KernelDiagnostic := match params {
    List.empty => List.empty,
    List.cons p rest =>
        List.append (one_param_type_diagnostic name p) (param_type_diagnostics name rest),
}

#[partial]
def one_param_type_diagnostic (name : String) (p : KernelParam) : List KernelDiagnostic := match p {
    { name := pname, typ } =>
        if is_buffer_type typ then
            match buffer_elem_type_of typ {
                Option.some _elem => List.empty,
                Option.none =>
                    List.cons (shape_diagnostic name
                        (String.concat pname "'s element type is not a scalar; kernels need i64/f64/f32/i32/u8 elements")) List.empty,
            }
        else if is_i64_type typ then List.empty
        else match scalar_mlir_type_of typ {
            Option.some _ty => List.empty,
            Option.none =>
                List.cons (shape_diagnostic name
                    (String.concat pname " has a type a kernel cannot take; use a scalar or a Buf")) List.empty,
        },
}

/// A `Buf` parameter with no dimension: the shape is dynamic, which the subset
/// forbids (Decision 5).
#[partial]
def param_dim_diagnostics (name : String) (shapes : List ParamShape) : List KernelDiagnostic := match shapes {
    List.empty => List.empty,
    List.cons s rest =>
        List.append (one_param_dim_diagnostic name s) (param_dim_diagnostics name rest),
}

#[partial]
def one_param_dim_diagnostic (name : String) (s : ParamShape) : List KernelDiagnostic := match s {
    ParamShape.buffer_ pname _elem dims _noalias =>
        if List.is_empty dims
        then List.cons (shape_diagnostic name
            (String.concat pname " has no dimension; give the kernel an I64 bound after it")) List.empty
        else List.empty,
    _ => List.empty,
}

/// A result type this backend cannot lower.
#[partial]
def result_type_diagnostics (name : String) (ret : Term) : List KernelDiagnostic :=
    if name_is ret "Unit" then List.empty
    else match scalar_mlir_type_of ret {
        Option.some _ty => List.empty,
        Option.none =>
            List.cons (shape_diagnostic name
                "returns a type a kernel cannot return; kernels return Unit or a scalar") List.empty,
    }

// ─── folding the call site's dimensions in ───────────────────────────

/// `shapes` with the buffer placeholders replaced by `values`, in order: the
/// first buffer gets the first value, the second the second, and so on.
///
/// A buffer with no value left keeps its empty `dims`, which is what
/// `one_param_dim_diagnostic` reports. Extra values are ignored rather than an
/// error: `mono.mo`'s sixth rule already refuses a non-literal call-site
/// argument, so a surplus here means the caller passed values for a kernel it
/// also reported on, and reporting it twice would be noise.
#[partial]
pub def fill_dims (shapes : List ParamShape) (values : List I64) : List ParamShape :=
    fill_dims_go shapes values

#[partial]
def fill_dims_go (shapes : List ParamShape) (values : List I64) : List ParamShape := match shapes {
    List.empty => List.empty,
    List.cons s rest =>
        match s {
            ParamShape.buffer_ name elem _dims noalias =>
                match values {
                    List.empty => List.cons s (fill_dims_go rest List.empty),
                    List.cons v more =>
                        List.cons (ParamShape.buffer_ name elem (List.cons v List.empty) noalias)
                            (fill_dims_go rest more),
                },
            _ => List.cons s (fill_dims_go rest values),
        },
}

/// The argument positions of `shapes` that are dimensions -- the real answer to
/// `mono.mo`'s `dim_positions_of`, which calls every explicit `I64` parameter a
/// dimension.
///
/// A `dim_` sits immediately after the `buffer_` it bounds, so the position
/// counted here is the SOURCE argument index (buffers and scalars alike are
/// counted), which is what `mono.mo`'s `dim_diagnostics` compares against.
#[partial]
pub def dim_positions_from_shapes (shapes : List ParamShape) : List I64 :=
    dim_positions_go shapes 0

#[partial]
def dim_positions_go (shapes : List ParamShape) (i : I64) : List I64 := match shapes {
    List.empty => List.empty,
    List.cons s rest =>
        match s {
            ParamShape.dim_ _name => List.cons i (dim_positions_go rest (i + 1)),
            _ => dim_positions_go rest (i + 1),
        },
}

/// The positions of the BUFFER parameters, in source argument order -- what
/// `shape_of_kernel`'s `dim_values` list corresponds to, one value per buffer.
#[partial]
pub def buffer_positions_from_shapes (shapes : List ParamShape) : List I64 :=
    buffer_positions_go shapes 0

#[partial]
def buffer_positions_go (shapes : List ParamShape) (i : I64) : List I64 := match shapes {
    List.empty => List.empty,
    List.cons s rest =>
        match s {
            ParamShape.buffer_ _name _elem _dims _noalias =>
                List.cons i (buffer_positions_go rest (i + 1)),
            _ => buffer_positions_go rest (i + 1),
        },
}

// ─── composition ─────────────────────────────────────────────────────

/// The full shape of one kernel: parameters classified, dimensions folded from
/// `dim_values`, results derived, diagnostics collected.
///
/// `dim_values` are the call site's literal dimensions, one per buffer in
/// declaration order -- so a kernel called as `saxpy dst 16` with
/// `dim_positions = [1]` folds `[16]` into `dst`'s memref. A caller that has no
/// call site (the `monad kernels` subcommand, or a test) passes `List.empty`,
/// which yields a `dim` diagnostic per buffer -- honest, because a shape with no
/// bound is not a static shape.
#[partial]
pub def shape_of_kernel (kernel : Def) (dim_values : List I64) : KernelShape := match kernel {
    Def.mk { typ, .. } =>
        let name : String := def_name_str kernel in
        let params : List KernelParam := kernel_params kernel in
        let flags : List Bool := noalias_flags_in typ in
        let shapes : List ParamShape := param_shapes_of params flags in
        let filled : List ParamShape := fill_dims shapes dim_values in
        let ret : Term := pi_codomain typ in
        KernelShape.mk name filled (result_types_of ret)
            (filled_shape_diagnostics name params filled ret),
}

/// A `KernelExtract`'s shape: the extractor already holds the parameters, so
/// this avoids re-deriving them from the def.
///
/// The extractor's own diagnostics are carried through, so a caller that has
/// already run the subset checker does not have to merge two lists.
#[partial]
pub def shape_of_extract (extract : KernelExtract) (dim_values : List I64) : KernelShape := match extract {
    { name, params, diagnostics, .. } =>
        let shapes : List ParamShape := param_shapes_of params List.empty in
        let filled : List ParamShape := fill_dims shapes dim_values in
        KernelShape.mk name filled List.empty
            (List.append (param_dim_diagnostics name filled) diagnostics),
}
