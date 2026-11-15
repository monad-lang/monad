/// `codegen::kernel::shape` -- the signature half of the kernel emitter.
///
/// ## What this file has to prove
///
/// `shape.mo` turns a kernel's elaborated signature into MLIR types. Two
/// things can go wrong silently, and each has its own section below:
///
/// 1. **A wrong MLIR type.** `Buf F32` becoming `memref<nxf64>` still
///    compiles and still runs; it just reads every second element. So the
///    positive tests pin the rendered type TEXT rather than the constructor,
///    because the text is what reaches `mlir-opt`.
/// 2. **A missing diagnostic.** A `Buf` with no dimension, a `Buf` of a
///    non-scalar, a parameter of an unlowerable type and a non-scalar result
///    are four distinct ways to be outside the subset, and a rule that
///    silently stopped firing would show up as an emitted `memref<f32>` --
///    a rank-0 memref, which is a *different type*, not a smaller one. Each
///    rule therefore gets a negative test AND a control that must stay
///    silent, the same discipline `kernel_detect_tests.mo` uses.
///
/// ## The measurement this file transcribes
///
/// The elaborated signature is not guessed. `saxpy (dst : Buf F32) (n : I64)
/// : Unit` was measured 2026-11-15 through `elaborate_loaded_modules` -- the
/// real front end -- and its type is `((Buf F32) -> (I64 -> Unit))` with
/// **no** implicit `{Buf : Type}` binder, which is the question the plan left
/// open. `measured_saxpy_type` below is that shape transcribed, so the
/// fixtures here are the real thing and the suite stays a unit test rather
/// than paying a module load per run.
///
/// ## Two parse facts this file's fixtures cost time on
///
/// * **A numeric-literal match pattern does not parse** (`match n { 0 => ... }`
///   is `expected '('`). Every count assertion here is an `if`.
/// * **`head` is a reserved keyword** and cannot be a parameter name; the
///   helpers below use `xs`/`first`.
use lang::types {
    Attribute, Binder, Con, DebugName, Def, Identifier, NamePath, Term,
    TypeConstraint, Visibility, binder_named, sentinel, term_peel,
}
use lib::kernel::detect {KernelDiagnostic}
use lib::kernel::mono {KernelExtract, KernelParam}
use lib::kernel::shape {
    KernelShape, ParamShape, bare_name_of, buffer_elem_type_of, buffer_positions_from_shapes,
    dim_positions_from_shapes, fill_dims, is_buffer_type, is_i64_type, noalias_flags_of,
    param_shapes_of, result_type_of_kernel, result_types_of, scalar_mlir_type_of,
    shape_diagnostic, shape_diagnostics, shape_of_kernel, show_signature,
}
use mlir::ir {MlirParam, MlirType, show_mlir_type}
use std::list {List.any}

// ─── fixtures ────────────────────────────────────────────────────────

def kernel_attr : List Attribute :=
    List.cons (Attribute.mk (Identifier.id "kernel") List.empty) List.empty

def bare_npath (s : String) : NamePath :=
    NamePath.mk (List.cons (Identifier.id s) List.empty)

/// A free global reference: the shape `mono.mo`'s delta step unfolds, and the
/// shape the elaborator builds for a type name.
def ref (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

/// A type as a `Term.con` -- the other spelling `shape.mo` accepts, and the
/// one a hand-built fixture naturally reaches for.
def con_ty (name : String) : Term :=
    Term.con (Con.mk (Identifier.id name) (bare_npath name) 0 List.empty)

/// `Buf E` as an application: `Term.app (ref "Buf") (ref "F32")`.
def buf_of (elem : Term) : Term := Term.app (ref "Buf") elem

/// `I64`.
def i64_ty : Term := con_ty "I64"

/// `fn (a : T) => ... ` -- one explicit pi binder per parameter, which is the
/// shape the measured signature has.
def pi_chain (names : List String) (doms : List Term) (ret : Term) : Term :=
    pi_chain_go names doms ret

#[partial]
def pi_chain_go (names : List String) (doms : List Term) (ret : Term) : Term :=
    match names {
        List.empty => ret,
        List.cons n rest =>
            match doms {
                List.empty => ret,
                List.cons d drest =>
                    Term.pi (binder_named (Identifier.id n)) d (pi_chain_go rest drest ret),
            },
    }

def mk_kernel (name : String) (typ : Term) : Def :=
    Def.mk (bare_npath name) typ Term.hole ([] : List TypeConstraint) kernel_attr
        Visibility.package_private List.empty

/// The MEASURED elaborated type of `#[kernel] def saxpy (dst : Buf F32)
/// (n : I64) : Unit`, transcribed (see the file header).
def measured_saxpy_type : Term :=
    pi_chain ["dst", "n"] [buf_of (ref "F32"), ref "I64"] (ref "Unit")

/// The same shape with a scalar first, from the plan's second example
/// (`scale (a : F32) (n : I64) (out : Buf F32)`), so the dimension pairing is
/// exercised where the buffer is NOT first.
def measured_scale_type : Term :=
    pi_chain ["a", "n", "out"] [ref "F32", ref "I64", buf_of (ref "F32")] (ref "Unit")

def kernel_param (name : String) (typ : Term) : KernelParam := KernelParam.mk name typ

// ─── 1. the type vocabulary ──────────────────────────────────────────

#[test]
def test_scalar_types_map_to_their_widths : Bool :=
    match scalar_mlir_type_of (ref "F32") {
        Option.some ty => String.beq (show_mlir_type ty) "f32",
        Option.none => false,
    }

/// The width is the ABI's, not a widening: an `I32` buffer's element stride is
/// four bytes, so emitting `i64` over it would read the wrong elements.
#[test]
def test_i32_is_i32_not_i64 : Bool :=
    match scalar_mlir_type_of (ref "I32") {
        Option.some ty => String.beq (show_mlir_type ty) "i32",
        Option.none => false,
    }

/// `U8` -> `i8`: a byte is a byte. `U64` -> `i64` for the same reason in the
/// other direction.
#[test]
def test_unsigned_widths_follow_the_storage : Bool :=
    match scalar_mlir_type_of (ref "U8") {
        Option.some ty8 => match scalar_mlir_type_of (ref "U64") {
            Option.some ty64 =>
                String.beq (show_mlir_type ty8) "i8" && String.beq (show_mlir_type ty64) "i64",
            Option.none => false,
        },
        Option.none => false,
    }

/// `Bool` -> `i1`, MLIR's boolean width.
#[test]
def test_bool_is_i1 : Bool :=
    match scalar_mlir_type_of (ref "Bool") {
        Option.some ty => String.beq (show_mlir_type ty) "i1",
        Option.none => false,
    }

/// A type this backend does not know is reported, not silently widened. This
/// is the control for the diagnostic section below: `String` must answer
/// `none` here, or the `shape` rule can never fire.
#[test]
def test_unknown_scalar_type_is_none : Bool :=
    match scalar_mlir_type_of (ref "String") {
        Option.some _ => false,
        Option.none => true,
    }

/// Both term spellings of a type name are accepted -- a `Term.var` and a
/// `Term.con` -- because an elaborated domain uses the first and a hand-built
/// fixture the second, and a version that handled only one would report a
/// `shape` finding on every real kernel (or on every test).
#[test]
def test_both_type_spellings_resolve : Bool :=
    match bare_name_of (ref "I64") {
        Option.some a => match bare_name_of (i64_ty) {
            Option.some b => String.beq a "I64" && String.beq b "I64",
            Option.none => false,
        },
        Option.none => false,
    }

/// A dotted name is reduced to its last segment, so a module-qualified type
/// reference matches.
#[test]
def test_dotted_type_name_is_reduced : Bool :=
    match bare_name_of (ref "std.F32") {
        Option.some n => String.beq n "F32",
        Option.none => false,
    }

// ─── 2. Buf E -> memref ──────────────────────────────────────────────

#[test]
def test_buf_is_recognised : Bool :=
    is_buffer_type (buf_of (ref "F32"))

/// The control: a bare `F32` is not a buffer, and neither is an `I64`. Without
/// this, a `Buf` test that answered `true` for everything would pass.
#[test]
def test_scalars_are_not_buffers : Bool :=
    Bool.not (is_buffer_type (ref "F32")) && Bool.not (is_buffer_type (ref "I64"))

#[test]
def test_buf_element_type_is_f32 : Bool :=
    match buffer_elem_type_of (buf_of (ref "F32")) {
        Option.some ty => String.beq (show_mlir_type ty) "f32",
        Option.none => false,
    }

/// A `Buf` whose element is not a scalar this backend knows answers `none`, so
/// the caller reports a `shape` finding rather than emitting an `i64` memref
/// over a payload that is not eight bytes.
#[test]
def test_buf_of_unknown_element_is_none : Bool :=
    match buffer_elem_type_of (buf_of (ref "String")) {
        Option.some _ => false,
        Option.none => true,
    }

// ─── 3. the parameter walk: which I64 is a dimension ─────────────────

/// `saxpy (dst : Buf F32) (n : I64)`: the `I64` after the buffer is a
/// DIMENSION, not a scalar parameter. This is the whole structural answer
/// `mono.mo`'s over-approximation was waiting for.
#[test]
def test_i64_after_a_buffer_is_a_dimension : Bool :=
    let params : List KernelParam := [
        kernel_param "dst" (buf_of (ref "F32")),
        kernel_param "n" (ref "I64"),
    ] in
    match param_shapes_of params List.empty {
        List.cons first rest => match rest {
            List.cons second _ =>
                is_buffer_shape first && is_dim_shape second,
            _ => false,
        },
        _ => false,
    }

/// `scale (a : F32) (n : I64) (out : Buf F32)`: the `n` follows a SCALAR, so
/// it is an ordinary scalar parameter, not a dimension. A version that called
/// every `I64` a dimension would pass the test above and fail this one.
#[test]
def test_i64_after_a_scalar_is_not_a_dimension : Bool :=
    let params : List KernelParam := [
        kernel_param "a" (ref "F32"),
        kernel_param "n" (ref "I64"),
    ] in
    match param_shapes_of params List.empty {
        List.cons _first rest => match rest {
            List.cons second _ => is_scalar_shape second,
            _ => false,
        },
        _ => false,
    }

/// The plan's second example: `scale (a : F32) (n : I64) (out : Buf F32)`.
///
/// `n` follows a SCALAR, so it is a scalar parameter -- and `out` after it is a
/// buffer whose own dimension is a FOURTH parameter, which this three-parameter
/// spelling does not have. So the walk is `S S B`, and `out` is reported as a
/// buffer with no dimension (the negative test for that rule lives below).
#[test]
def test_scale_parameters_are_scalar_scalar_buffer : Bool :=
    let shapes : List ParamShape :=
        param_shapes_of
            [kernel_param "a" (ref "F32"), kernel_param "n" (ref "I64"),
                kernel_param "out" (buf_of (ref "F32"))]
            List.empty in
    shape_kinds shapes "SSB"

/// `matmul (a : Buf F32) (b : Buf F32) (c : Buf F32) (m : I64) (n : I64)
/// (k : I64)` -- the shape the plan's `motes/kernel_example/` wants. Every
/// `I64` follows a buffer, so all three are dimensions and the signature is
/// three memrefs.
#[test]
def test_three_dimensions_after_three_buffers : Bool :=
    let shapes : List ParamShape :=
        param_shapes_of
            [kernel_param "a" (buf_of (ref "F32")), kernel_param "b" (buf_of (ref "F32")),
                kernel_param "c" (buf_of (ref "F32")), kernel_param "m" (ref "I64"),
                kernel_param "n" (ref "I64"), kernel_param "k" (ref "I64")]
            List.empty in
    shape_kinds shapes "BBBIII"

/// The dimension POSITIONS are the source argument indices, which is what
/// `mono.mo`'s `dim_diagnostics` compares a call site's arguments against.
/// For `saxpy` that is `[1]`; for `matmul` `[3, 4, 5]`.
#[test]
def test_dim_positions_are_source_indices : Bool :=
    let saxpy : List ParamShape :=
        param_shapes_of
            [kernel_param "dst" (buf_of (ref "F32")), kernel_param "n" (ref "I64")]
            List.empty in
    let matmul : List ParamShape :=
        param_shapes_of
            [kernel_param "a" (buf_of (ref "F32")), kernel_param "b" (buf_of (ref "F32")),
                kernel_param "c" (buf_of (ref "F32")), kernel_param "m" (ref "I64"),
                kernel_param "n" (ref "I64"), kernel_param "k" (ref "I64")]
            List.empty in
    i64_list_eq (dim_positions_from_shapes saxpy) [1]
        && i64_list_eq (dim_positions_from_shapes matmul) [3, 4, 5]

/// And the BUFFER positions, which is what `shape_of_kernel`'s `dim_values`
/// list is ordered by: `saxpy` -> `[0]`, `matmul` -> `[0, 1, 2]`.
#[test]
def test_buffer_positions_are_source_indices : Bool :=
    let matmul : List ParamShape :=
        param_shapes_of
            [kernel_param "a" (buf_of (ref "F32")), kernel_param "m" (ref "I64"),
                kernel_param "b" (buf_of (ref "F32"))]
            List.empty in
    i64_list_eq (buffer_positions_from_shapes matmul) [0, 2]

/// A buffer NOT followed by an `I64` yields a buffer shape with no dimension,
/// which the diagnostics section reports. This is the control that makes the
/// `no dimension` rule fireable at all.
#[test]
def test_buffer_without_a_dimension_has_none : Bool :=
    let shapes : List ParamShape :=
        param_shapes_of [kernel_param "dst" (buf_of (ref "F32"))] List.empty in
    match shapes {
        List.cons first _ => buffer_has_no_dim first,
        _ => false,
    }

/// `is_i64_type` is a name test and is deliberately loose, so a dotted
/// reference works -- the same behaviour `mono.mo`'s `is_i64_type` documents.
#[test]
def test_i64_type_test_accepts_a_dotted_name : Bool :=
    is_i64_type (ref "prelude.I64") && Bool.not (is_i64_type (ref "I32"))

// ─── 4. noalias from the binder multiplicity ─────────────────────────

/// The measured signature's binders are all `many`, so no argument carries
/// `llvm.noalias` today. Pinned so a change to the multiplicity default shows
/// up here rather than in emitted IR.
#[test]
def test_default_multiplicity_is_not_noalias : Bool :=
    let k : Def := mk_kernel "saxpy" measured_saxpy_type in
    match noalias_flags_of k {
        List.cons first rest => match rest {
            List.cons second _ =>
                Bool.not first && Bool.not second,
            _ => false,
        },
        _ => false,
    }

// ─── 5. results ──────────────────────────────────────────────────────

#[test]
def test_unit_result_is_empty : Bool :=
    List.is_empty (result_types_of (ref "Unit"))

#[test]
def test_scalar_result_is_one_type : Bool :=
    match result_types_of (ref "F64") {
        List.cons ty rest =>
            String.beq (show_mlir_type ty) "f64" && List.is_empty rest,
        _ => false,
    }

/// The codomain is read through the whole pi spine, so a three-parameter
/// kernel's result is still its final type.
#[test]
def test_result_type_skips_the_whole_spine : Bool :=
    let k : Def := mk_kernel "scale" measured_scale_type in
    match bare_name_of (result_type_of_kernel k) {
        Option.some n => String.beq n "Unit",
        Option.none => false,
    }

// ─── 6. folding the call site's dimension values in ──────────────────

/// `saxpy dst 16` folds `16` into the buffer's memref: `memref<16xf32>`. This
/// is the plan's Decision 5 made concrete -- the dimension is a CALL-SITE
/// literal, and `shape.mo` is where it becomes a static bound.
#[test]
def test_fill_dims_makes_a_static_memref : Bool :=
    let shapes : List ParamShape :=
        param_shapes_of
            [kernel_param "dst" (buf_of (ref "F32")), kernel_param "n" (ref "I64")]
            List.empty in
    let filled : List ParamShape := fill_dims shapes [16] in
    match filled {
        List.cons first _ => buffer_memref_text first "memref<16xf32>",
        _ => false,
    }

/// The value binds to the buffer it follows, not to the position: with
/// `[0, 2]` for the two buffers of `matmul`, the SECOND buffer's value is the
/// one that lands on it. A version that matched by argument index would pass
/// the single-buffer test and get this wrong.
#[test]
def test_fill_dims_pairs_with_buffers_not_positions : Bool :=
    let shapes : List ParamShape :=
        param_shapes_of
            [kernel_param "a" (buf_of (ref "F32")), kernel_param "m" (ref "I64"),
                kernel_param "b" (buf_of (ref "F32")), kernel_param "n" (ref "I64")]
            List.empty in
    let filled : List ParamShape := fill_dims shapes [4, 8] in
    match filled {
        List.cons first rest => match rest {
            List.cons _dim rest2 => match rest2 {
                List.cons third _ =>
                    buffer_memref_text first "memref<4xf32>"
                        && buffer_memref_text third "memref<8xf32>",
                _ => false,
            },
            _ => false,
        },
        _ => false,
    }

/// Fewer values than buffers leaves the remainder unfilled rather than
/// guessing, which is what makes the `no dimension` diagnostic fire.
#[test]
def test_fill_dims_leaves_extra_buffers_unfilled : Bool :=
    let shapes : List ParamShape :=
        param_shapes_of
            [kernel_param "a" (buf_of (ref "F32")), kernel_param "b" (buf_of (ref "F32"))]
            List.empty in
    match fill_dims shapes [4] {
        List.cons _first rest => match rest {
            List.cons second _ => buffer_has_no_dim second,
            _ => false,
        },
        _ => false,
    }

// ─── 7. the whole signature ──────────────────────────────────────────

/// The rendered signature, which is what `monad kernels` prints and what a
/// diagnostic quotes. `n` stays visible as `index`: it is not an MLIR
/// parameter (it was folded into the memref), but the author wrote it and the
/// plan's rejection message names it.
#[test]
def test_show_signature_renders_the_measured_kernel : Bool :=
    let k : Def := mk_kernel "saxpy" measured_saxpy_type in
    let s : KernelShape := shape_of_kernel k [16] in
    String.beq (show_signature s) "saxpy(dst: memref<16xf32>, n: index) -> ()"

/// The MLIR parameter list drops the dimension: two source parameters, ONE
/// MLIR parameter, because the bound is in the memref type. A version that
/// emitted the dimension as an `i64` argument would produce a kernel with the
/// wrong ABI -- and `fixtures/mlir/saxpy.mlir`'s exact-two-parameter
/// assertion is the Phase 0 proof that this is the right count.
#[test]
def test_mlir_params_drop_the_dimension : Bool :=
    let k : Def := mk_kernel "saxpy" measured_saxpy_type in
    let s : KernelShape := shape_of_kernel k [16] in
    match KernelShape.mlir_params s {
        List.cons p rest =>
            param_is_buffer p "dst" "memref<16xf32>" && List.is_empty rest,
        _ => false,
    }

/// A scalar parameter IS an MLIR parameter, with its own width. The control
/// for the test above: if `mlir_params` dropped everything, that test would
/// pass and this one fail.
///
/// `scale (a : F32) (n : I64) (out : Buf F32) (len : I64)` -- the four-parameter
/// spelling, so `out` has a dimension and the list is exactly `f32`, `i64`,
/// `memref<8xf32>`.
#[test]
def test_mlir_params_keep_scalars : Bool :=
    let k : Def := mk_kernel "scale"
        (pi_chain ["a", "n", "out", "len"]
            [ref "F32", ref "I64", buf_of (ref "F32"), ref "I64"] (ref "Unit")) in
    let s : KernelShape := shape_of_kernel k [8] in
    match KernelShape.mlir_params s {
        List.cons a rest => match rest {
            List.cons n rest2 => match rest2 {
                List.cons out rest3 =>
                    param_is_scalar a "a" "f32"
                        && param_is_scalar n "n" "i64"
                        && param_is_buffer out "out" "memref<8xf32>"
                        && List.is_empty rest3,
                _ => false,
            },
            _ => false,
        },
        _ => false,
    }

/// A kernel with a scalar result reports it, so `scalar.mo` knows to emit
/// `func.return %v : f64`.
#[test]
def test_scalar_result_reaches_the_shape : Bool :=
    let k : Def := mk_kernel "sum"
        (pi_chain ["v", "n"] [buf_of (ref "F32"), ref "I64"] (ref "F64")) in
    let s : KernelShape := shape_of_kernel k [16] in
    match KernelShape.mlir_results s {
        List.cons ty rest =>
            String.beq (show_mlir_type ty) "f64" && List.is_empty rest,
        _ => false,
    }

/// A fully-specified kernel is READY -- no diagnostics -- which is the gate
/// `scalar.mo` will check before emitting.
#[test]
def test_ready_when_every_dimension_is_supplied : Bool :=
    let k : Def := mk_kernel "saxpy" measured_saxpy_type in
    KernelShape.ready (shape_of_kernel k [16])

/// And NOT ready when a buffer has no bound: a shape with a dynamic dimension
/// is exactly what Decision 5 forbids.
#[test]
def test_not_ready_without_a_dimension : Bool :=
    let k : Def := mk_kernel "saxpy" measured_saxpy_type in
    Bool.not (KernelShape.ready (shape_of_kernel k List.empty))

// ─── 8. the shape diagnostics, one rule each ─────────────────────────

/// Rule A: a `Buf` with no dimension.
#[test]
def test_reports_a_buffer_without_a_dimension : Bool :=
    let k : Def := mk_kernel "k"
        (pi_chain ["dst"] [buf_of (ref "F32")] (ref "Unit")) in
    let s : KernelShape := shape_of_kernel k List.empty in
    has_rule s.diagnostics "shape"

/// The control: the SAME kernel with the bound supplied is silent.
#[test]
def test_silent_when_the_bound_is_supplied : Bool :=
    let k : Def := mk_kernel "k"
        (pi_chain ["dst", "n"] [buf_of (ref "F32"), ref "I64"] (ref "Unit")) in
    KernelShape.ready (shape_of_kernel k [16])

/// Rule B: a `Buf` whose element type is not a scalar.
#[test]
def test_reports_a_buf_of_a_non_scalar : Bool :=
    let k : Def := mk_kernel "k"
        (pi_chain ["dst", "n"] [buf_of (ref "String"), ref "I64"] (ref "Unit")) in
    let s : KernelShape := shape_of_kernel k [16] in
    has_rule s.diagnostics "shape"

/// Rule C: a parameter type a kernel cannot take at all -- here a `List`.
#[test]
def test_reports_an_unlowerable_parameter : Bool :=
    let k : Def := mk_kernel "k"
        (pi_chain ["xs", "n"] [Term.app (ref "List") (ref "I64"), ref "I64"] (ref "Unit")) in
    let s : KernelShape := shape_of_kernel k [16] in
    has_rule s.diagnostics "shape"

/// Rule D: a result type a kernel cannot return -- a `Buf`, which the host
/// owns and the device has no allocator for.
#[test]
def test_reports_an_unlowerable_result : Bool :=
    let k : Def := mk_kernel "k"
        (pi_chain ["n"] [ref "I64"] (buf_of (ref "F32"))) in
    let s : KernelShape := shape_of_kernel k [16] in
    has_rule s.diagnostics "shape"

/// The control for rule D: a scalar result is silent.
#[test]
def test_scalar_result_is_silent : Bool :=
    let k : Def := mk_kernel "k"
        (pi_chain ["n"] [ref "I64"] (ref "F64")) in
    KernelShape.ready (shape_of_kernel k List.empty)

/// A scalar-only kernel with no buffer is READY with no dimension values at
/// all -- the control that proves the `dim` finding is about buffers, not
/// about the absence of values.
#[test]
def test_scalar_only_kernel_needs_no_dimensions : Bool :=
    let k : Def := mk_kernel "k" (pi_chain ["n"] [ref "I64"] (ref "Unit")) in
    KernelShape.ready (shape_of_kernel k List.empty)

/// Every diagnostic carries the `shape` rule tag, so `monad kernels` can group
/// it and `detect.mo`'s `rule_message` can render it.
#[test]
def test_shape_diagnostics_carry_the_rule_tag : Bool :=
    let d : KernelDiagnostic := shape_diagnostic "k" "detail" in
    String.beq d.rule "shape" && String.beq d.kernel "k"

// ─── helpers ─────────────────────────────────────────────────────────

/// `is_buffer_type` on a `ParamShape`.
def is_buffer_shape (s : ParamShape) : Bool := match s {
    ParamShape.buffer_ _name _elem _dims _noalias => true,
    _ => false,
}

def is_scalar_shape (s : ParamShape) : Bool := match s {
    ParamShape.scalar_ _name _ty _noalias => true,
    _ => false,
}

def is_dim_shape (s : ParamShape) : Bool := match s {
    ParamShape.dim_ _name => true,
    _ => false,
}

def buffer_has_no_dim (s : ParamShape) : Bool := match s {
    ParamShape.buffer_ _name _elem dims _noalias => List.is_empty dims,
    _ => false,
}

/// A buffer shape's rendered memref text -- the assertion that catches a wrong
/// element type or a wrong bound, which a constructor comparison would miss
/// (two `MlirType.memref_` values with different dims are both "a memref").
def buffer_memref_text (s : ParamShape) (want : String) : Bool := match s {
    ParamShape.buffer_ _name elem dims _noalias =>
        String.beq (show_mlir_type (MlirType.memref_of dims elem)) want,
    _ => false,
}

def param_is_buffer (p : MlirParam) (name : String) (ty : String) : Bool := match p {
    { name := n, ty := t, .. } => String.beq n name && String.beq (show_mlir_type t) ty,
}

def param_is_scalar (p : MlirParam) (name : String) (ty : String) : Bool :=
    param_is_buffer p name ty

/// A compact assertion over a shape list: one letter per parameter, `B` for a
/// buffer, `S` for a scalar, `I` for a dimension. Keeps the multi-parameter
/// tests readable instead of six nested matches each.
#[partial]
def shape_kinds (shapes : List ParamShape) (want : String) : Bool :=
    String.beq (shape_kinds_text shapes) want

#[partial]
def shape_kinds_text (shapes : List ParamShape) : String :=
    String.concat_list (List.reverse (shape_kinds_go shapes List.empty))

#[partial]
def shape_kinds_go (shapes : List ParamShape) (acc : List String) : List String := match shapes {
    List.empty => acc,
    List.cons s rest =>
        shape_kinds_go rest (List.cons (kind_letter s) acc),
}

def kind_letter (s : ParamShape) : String := match s {
    ParamShape.buffer_ _name _elem _dims _noalias => "B",
    ParamShape.scalar_ _name _ty _noalias => "S",
    ParamShape.dim_ _name => "I",
}

/// Is `rule` among the diagnostics? The assertion every negative test makes,
/// and deliberately a tag test rather than a message test: the message's prose
/// is `detect.mo`'s, and pinning it twice would make one edit break two files.
#[partial]
def has_rule (ds : List KernelDiagnostic) (rule : String) : Bool :=
    List.any (fn d => String.beq d.rule rule) ds

#[partial]
def i64_list_eq (a : List I64) (b : List I64) : Bool := match a {
    List.empty => List.is_empty b,
    List.cons x arest => match b {
        List.empty => false,
        List.cons y brest => I64.beq x y && i64_list_eq arest brest,
    },
}
