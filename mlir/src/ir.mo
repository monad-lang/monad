/// The MLIR data model and the scalar renderers over it: types, values,
/// attributes, operations, blocks, regions and modules.
///
/// Compiler-agnostic. Nothing in this file -- or in this mote -- knows what
/// a Monad term is: the kernel emitter lives in `codegen/src/kernel/`, and
/// it is what lowers a `Term` into these shapes. Keeping the seam exactly
/// here is what lets this phase's golden tests run with no front-end
/// involvement at all, which is Phase 1's acceptance condition.
///
/// The split with `print.mo` mirrors `llvm/`: this file holds the model and
/// the SCALAR renderers (`show_mlir_type`, `show_mlir_value`,
/// `show_mlir_attr`), and `print.mo` holds the module-level printer
/// (`print_module`) that the `llvm` mote spells `emit_module`. Same file
/// shape, same reason: the scalar renderers are what the dialect modules
/// need, and they must not import the printer to get them.
///
/// ## Why a hand-written model rather than generic op form
///
/// `plans/bootstrapping/mlir-codegen.md` Decision 2 settles this: this
/// backend emits PRETTY form (`memref.store %v, %b[%i] : memref<16xf32>`)
/// rather than generic form (`"memref.store"(%v, %b, %i) : ...`). Generic
/// form round-trips only within one MLIR version, so it guards against
/// pretty-printer churn and not against release-to-release change -- it
/// buys nothing the golden round-trip tests do not buy more cheaply and
/// more legibly. The op set is ~20 ops and a text file is the only
/// debugging channel available (Decision 2: subprocesses, no libMLIR).
///
/// ## Why an operation carries TEXT
///
/// `MlirOp.text` is the op's own syntax, already composed by the dialect
/// module that owns it. That is deliberate, and it is the shape the plan
/// asks for rather than a shortcut around it: MLIR's op syntax is
/// POSITION-typed and op-specific -- `memref.store %v, %b[%i]` puts one
/// operand in a subscript, `scf.for %i = %c0 to %c16 step %c1` is not a
/// comma-separated operand list at all, and `arith.constant 0 : index`
/// carries an attribute where the others carry values. A single general
/// operand list would need a per-op printer to put them back in the right
/// places anyway, so the per-op knowledge lives where the plan puts it:
/// `mlir/src/dialect/*.mo`.
///
/// What stays STRUCTURED is what several dialects share and what the
/// printer has to place rather than just concatenate: `MlirType`,
/// `MlirValue`, `MlirAttr`, an op's `lhs`/`body`/`loc`, and a
/// `MlirFunction`'s parameter list. So the division is
/// "dialects spell op syntax, `print.mo` owns indentation, region nesting,
/// `loc(...)` placement and the `func.func` header" -- which is also how
/// the `llvm` mote divides `ir.mo` from its callers.
///
/// ## Why float constants carry TEXT
///
/// An `f32`/`f64` constant is a source spelling (`"1.0"`,
/// `"3.000000e+00"`), never a bit pattern. Monad cannot read a float's
/// bits yet (`implementations/float-bit-conversions.md`, 0%), so a model
/// carrying an `I64` would force every construction site to pass a magic
/// decimal -- which is exactly what Phase 0's fixture had to do
/// (`1077936128` for `3.0f32`), and what the plan records as a real gap.
/// Carrying the spelling lets an integral literal and a kernel-derived one
/// use one field, and `mlir-opt`'s parser is the arbiter of the text
/// either way.
///
/// ## Deliberate omissions
///
/// * No `affine` dialect (the plan cuts it: `--lower-affine` stays in the
///   pipeline only because `convert-linalg-to-loops` can emit it).
/// * No `vector` dialect (Phase 8, and only if measurement asks).
/// * No `gpu` dialect (Phase 4; `dialect/gpu.mo` does not exist yet).

/// An MLIR type.
///
/// The `iN` family is ONE constructor with a width payload rather than one
/// per width, because every use site spells the width anyway
/// (`arith.addi %a, %b : i32`) and a per-width constructor would make
/// `show_mlir_type` a twelve-arm match for no benefit. `f32`/`f64` are
/// likewise one constructor with a spelling, for the same reason
/// `LLVMType` keeps `f32_`/`f64_` apart: the ABI distinguishes them, and a
/// mistyped memref element type is a silent miscompile rather than an
/// error.
pub type MlirType {
    /// `i1`, `i8`, `i32`, `i64`, ... -- the width is the payload.
    int_ (width : I64),
    /// `f16`/`f32`/`f64`/`bf16` -- the spelling is the payload, so a
    /// future half type needs no new constructor.
    float_ (spelling : String),
    /// `index` -- MLIR's loop induction variable type. Deliberately not an
    /// integer width: `index` tracks the target's pointer width and the
    /// conversions to and from it are explicit (`arith.index_cast`).
    index_,
    /// `memref<NxMxT>` with a STATIC shape. Kernels never take a dynamic
    /// `?` dimension: Decision 3's bare-pointer convention needs
    /// `allocated == aligned`, which a dynamic stride does not guarantee,
    /// and Decision 5 folds every dimension at extraction. A static-only
    /// memref is therefore the type, not a limitation of the model --
    /// `MlirType.memref_of` is the only constructor, so a dynamic shape is
    /// unspellable.
    memref_ (dims : List I64) (elem : MlirType),
    /// `!llvm.ptr` -- produced by `mlir-opt`, never authored here. Present
    /// so a test can assert a LOWERED signature; no emitter path in this
    /// backend builds one (the `llvm` dialect is never authored: Decision
    /// 3, `mlir-opt` produces it and `mlir-translate` consumes it).
    llvm_ptr,
    /// Any type this model does not name, verbatim -- the escape hatch
    /// that lets a golden test spell something exotic without widening the
    /// ADT for every future dialect.
    opaque_ (spelling : String),
}

/// An MLIR value: an SSA name, or a block argument.
///
/// Much smaller than `LLVMValue` on purpose. MLIR's textual form is typed
/// at every use site (`arith.addi %a, %b : i32`), so a value does not have
/// to carry its own type the way an `LLVMValue` must.
pub type MlirValue {
    /// `%name` -- an SSA result or a `func.func` parameter. Stored WITHOUT
    /// the `%`, and the renderer adds it, so a construction site cannot
    /// produce a doubled sigil.
    var_ (name : String),
    /// The bare `%argN` form a region's block arguments take. Its own
    /// constructor only so an `scf` body cannot accidentally read like an
    /// ordinary named SSA value.
    arg_ (index : I64),
}

/// An MLIR attribute, in the two shapes that actually occur.
///
/// Text-first, for the same reason float constants are: the attribute
/// language is the part of MLIR most likely to move between releases, and
/// the golden round-trip is the defence (Decision 2). `valued_`'s payload
/// is already in MLIR's attribute syntax (`1 : i64`, `"sm_80"`), so adding
/// an attribute never widens this type.
pub type MlirAttr {
    /// A unit attribute -- `llvm.noalias` with no value.
    unit_ (name : String),
    /// `name = value`, `value` already spelled in MLIR's attribute syntax.
    valued_ (name : String) (value : String),
    /// A nameless attribute.
    bare_ (spelling : String),
}

/// An operation.
///
/// `lhs` is the whole left-hand side, `"%acc = "` or `""` -- spelled
/// rather than derived, because `scf.for`'s result is declared on the same
/// line as its header (`%acc = scf.for ... -> (f64)`) and the difference
/// between that and a statement is not recoverable from the op name alone.
///
/// `body` is the op's nested region, as a block list, empty for every op
/// that does not nest. A region IS its block list at this size -- MLIR
/// prints the braces and the printer indents, so a wrapping `MlirRegion`
/// record would add a match arm and no information. Recorded here rather
/// than left implicit because the plan's model list names `MlirRegion`.
pub struct MlirOp {
    lhs : String,
    /// The op's own syntax, after `lhs`: `arith.addf %a, %b : f32`.
    text : String,
    /// The op's region, if any, as a block list. EMPTY MEANS NO REGION --
    /// which is why the region-ness question is asked of `body` alone and
    /// not of a separate flag: an op with an empty region body is not a
    /// shape this backend emits.
    body : List MlirBlock,
    /// The op's `loc(...)`, or `""` for none. See "Diagnostics: the
    /// pipeline's only feedback channel" -- a `loc(...)` suffix is how an
    /// `mlir-opt` diagnostic points back at Monad source, and it is the
    /// cheapest quality win in the plan.
    ///
    /// WHERE it is printed depends on whether the op carries a region, and
    /// that is not a detail: measured against `mlir-opt` 21.1.8, an
    /// op-level `loc(...)` goes BEFORE the opening brace and is a parse
    /// error after it (`expected '{' to begin a region`). So the printer
    /// emits `scf.for ... step %c1 loc(...) {` -- see `print.mo`'s
    /// `print_op`.
    loc : String,
}

/// A basic block: a label, its block-argument TYPES (their names are
/// positional, `%arg0`...), its operations, and the keyword that introduces
/// it.
///
/// Blocks after the first need an explicit terminator in MLIR. The
/// construction sites in `dialect/scf.mo` supply it; nothing here enforces
/// it, because a single-block region's terminator is `func.return` or
/// `scf.yield` and both are ordinary ops.
pub struct MlirBlock {
    label : String,
    args : List MlirType,
    ops : List MlirOp,
    /// How this block is INTRODUCED inside its region. `scf.if`'s second
    /// arm is introduced by the `else` keyword and not by a `^label:`, and
    /// that is not a cosmetic difference -- measured against `mlir-opt`
    /// 21.1.8, printing a second `scf.if` arm as `^bb1:` is
    /// `expected 'else' to terminate with `scf.yield``. Every other block
    /// in this backend is `plain`.
    separator : MlirBlockSeparator,
}

/// What introduces a block.
pub type MlirBlockSeparator {
    /// A region's first block (no line), or a later one introduced by its
    /// `^label(args):` header.
    plain,
    /// An `scf.if`'s second arm: the `else` keyword.
    else_arm,
}

/// A `func.func` parameter.
pub struct MlirParam {
    name : String,
    ty : MlirType,
    /// `{llvm.noalias}` on this argument. A field rather than an
    /// `MlirAttr` because it is the one attribute with an ABI consequence
    /// and the printer has to place it on the ARGUMENT
    /// (`%a: memref<16xf32> {llvm.noalias}`), not in an op's own `{...}`
    /// block. It is Decision 5's carrier for the aliasing facts
    /// quantitative types would eventually supply, which is why Phase 0's
    /// fixture pins that it survives `convert-func-to-llvm`.
    noalias : Bool,
}

/// A `func.func`: the only top-level op this backend emits.
pub struct MlirFunction {
    name : String,
    params : List MlirParam,
    results : List MlirType,
    body : MlirBlock,
    loc : String,
    /// `private`, `public`, or `""` for no visibility keyword.
    visibility : String,
}

/// A whole `.mlir` file: the functions, in order.
///
/// A flat function list rather than a `builtin.module` op with a region.
/// Module level IS the file's top level in MLIR -- a bare top-level
/// `func.func` is module-level, and `mlir-opt` re-prints it exactly that
/// way -- so modelling the implicit module as an explicit region would add
/// a nesting level that the tools then disagree with.
pub struct MlirModule {
    functions : List MlirFunction,
}

// ─── type constructors ───────────────────────────────────────────────

/// `iN`.
pub def MlirType.i_n (width : I64) : MlirType := MlirType.int_ width

/// `i1`.
pub def MlirType.i1 : MlirType := MlirType.int_ 1

/// `i8`.
pub def MlirType.i8 : MlirType := MlirType.int_ 8

/// `i32`.
pub def MlirType.i32 : MlirType := MlirType.int_ 32

/// `i64`.
pub def MlirType.i64 : MlirType := MlirType.int_ 64

/// `f32`.
pub def MlirType.f32 : MlirType := MlirType.float_ "f32"

/// `f64`.
pub def MlirType.f64 : MlirType := MlirType.float_ "f64"

/// `index`.
pub def MlirType.index : MlirType := MlirType.index_

/// `memref<d0xd1x...xT>`. The ONLY memref constructor, so a dynamic `?`
/// dimension is unspellable (see `memref_`'s own doc comment).
pub def MlirType.memref_of (dims : List I64) (elem : MlirType) : MlirType :=
    MlirType.memref_ dims elem

/// A one-dimensional `memref` of `n` elements -- the shape every kernel
/// argument has (`Buf F32` of length `n` -> `memref<nxf32>`).
pub def MlirType.memref_1d (n : I64) (elem : MlirType) : MlirType :=
    MlirType.memref_ [n] elem

/// The element type a `Buf E` of kind `elem_kind` lowers to, using the
/// runtime's `MONAD_ELEM_*` codes (`std/src/buf.mo`: 0=i64 1=f64 2=f32
/// 3=i32 4=u8).
///
/// `U8` maps to `i8`, not to `i32`: a byte buffer is a byte buffer, and
/// the memref stride follows from the element type. A kind this function
/// does not know answers `i64` rather than failing, because its caller has
/// already read the kind out of a real `BufObj`: the runtime's `-1` means
/// "not a Buf at all", which is a bug upstream, and an `i64` memref over a
/// bogus payload is at least a *typed* mistake rather than an unspellable
/// type.
pub def MlirType.of_elem_kind (kind : I64) : MlirType :=
    if I64.beq kind 0 then MlirType.i64
    else if I64.beq kind 1 then MlirType.f64
    else if I64.beq kind 2 then MlirType.f32
    else if I64.beq kind 3 then MlirType.i32
    else if I64.beq kind 4 then MlirType.i8
    else MlirType.i64

// ─── value and attribute constructors ────────────────────────────────

/// An SSA name reference.
pub def MlirValue.named (name : String) : MlirValue := MlirValue.var_ name

/// The `%argN` form a block's arguments take.
pub def MlirValue.arg (index : I64) : MlirValue := MlirValue.arg_ index

/// A unit attribute.
pub def MlirAttr.unit (name : String) : MlirAttr := MlirAttr.unit_ name

/// `name = value`.
pub def MlirAttr.valued (name : String) (value : String) : MlirAttr :=
    MlirAttr.valued_ name value

// ─── op constructors ─────────────────────────────────────────────────
//
// Three arities, and they are the three that occur: a statement, a
// statement with a nested region, and a value-binding op. All three take
// the op's text already composed by its dialect module (see the file
// header for why), and all three take the `loc(...)` suffix.

/// A statement-shaped op: no results, no region. `memref.store`,
/// `func.return`, `scf.yield`.
pub def MlirOp.stmt (text : String) (loc : String) : MlirOp :=
    { lhs := "", text := text, body := List.empty, loc := loc }

/// A statement-shaped op with a nested region -- `scf.if`, and `scf.for`
/// when its result is unused.
pub def MlirOp.stmt_region (text : String) (body : List MlirBlock) (loc : String) : MlirOp :=
    { lhs := "", text := text, body := body, loc := loc }

/// A value-binding op: `%name = <text>`. `text` carries any `-> (ty)`
/// header the op needs (`scf.for`'s own).
pub def MlirOp.assign (name : String) (text : String) (loc : String) : MlirOp :=
    { lhs := "%" ++ name ++ " = ", text := text, body := List.empty, loc := loc }

/// A value-binding op with a nested region: `%acc = scf.for ... -> (f64) {`.
pub def MlirOp.assign_region (name : String) (text : String) (body : List MlirBlock) (loc : String) : MlirOp :=
    { lhs := "%" ++ name ++ " = ", text := text, body := body, loc := loc }

// ─── block, function and module constructors ─────────────────────────

/// A block with no arguments -- the common case, so an arity the caller
/// does not care about is not a parameter it has to spell.
pub def MlirBlock.entry (label : String) (ops : List MlirOp) : MlirBlock :=
    { label := label, args := List.empty, ops := ops, separator := MlirBlockSeparator.plain }

/// A block with block-argument types. An `scf.for` body's induction
/// variable and `iter_args` are block arguments, not parameters, which is
/// why this exists.
pub def MlirBlock.with_args (label : String) (args : List MlirType) (ops : List MlirOp) : MlirBlock :=
    { label := label, args := args, ops := ops, separator := MlirBlockSeparator.plain }

/// An `scf.if`'s `else` arm: a `plain` block introduced by the `else`
/// keyword. Its label is ignored -- MLIR prints the keyword, not a label --
/// so the caller passes `""`.
pub def MlirBlock.else_ (ops : List MlirOp) : MlirBlock :=
    { label := "", args := List.empty, ops := ops, separator := MlirBlockSeparator.else_arm }

/// A parameter with no `llvm.noalias`. Named `plain` rather than `mk`
/// because a struct already has an implicit `MlirParam.mk`, and two
/// definitions of one name collide at load.
pub def MlirParam.plain (name : String) (ty : MlirType) : MlirParam :=
    { name := name, ty := ty, noalias := false }

/// A parameter carrying `{llvm.noalias}` -- Decision 5's aliasing carrier.
pub def MlirParam.restrict (name : String) (ty : MlirType) : MlirParam :=
    { name := name, ty := ty, noalias := true }

/// A `func.func` with no visibility keyword and no `loc`. Named `function`
/// rather than `def` because `def` is a reserved keyword and cannot be a
/// name segment.
pub def MlirFunction.function (name : String) (params : List MlirParam)
    (results : List MlirType) (body : MlirBlock) : MlirFunction :=
    { name := name, params := params, results := results, body := body,
        loc := "", visibility := "" }

/// A module of `functions`, in order.
pub def MlirModule.of_functions (functions : List MlirFunction) : MlirModule :=
    { functions := functions }

// ─── scalar renderers ────────────────────────────────────────────────
//
// These are what the dialect modules compose their op text from, which is
// why they live here and not in `print.mo` -- exactly the split
// `llvm/src/ir.mo` makes with `show_llvm_type`/`show_llvm_value`.

/// `i64`, `f32`, `index`, `memref<16xf32>`, ...
///
/// `#[partial]` rather than plain: the `memref_` arm recurses into the
/// ELEMENT type, which is not a structural subterm of `MlirType` as the
/// termination checker sees it.
#[partial]
pub def show_mlir_type (ty : MlirType) : String := match ty {
    MlirType.int_ width => String.concat "i" (I64.to_string width),
    MlirType.float_ spelling => spelling,
    MlirType.index_ => "index",
    MlirType.memref_ dims elem =>
        String.concat "memref<" (String.concat (show_dims dims) (String.concat (show_mlir_type elem) ">")),
    MlirType.llvm_ptr => "!llvm.ptr",
    MlirType.opaque_ spelling => spelling,
}

/// `16x32x` -- each dimension followed by its `x`, so the element type
/// concatenates straight on with no separator logic.
#[partial]
def show_dims (dims : List I64) : String := match dims {
    List.empty => "",
    List.cons d rest =>
        String.concat (I64.to_string d) (String.concat "x" (show_dims rest)),
}

/// `%name` or `%argN`.
pub def show_mlir_value (val : MlirValue) : String := match val {
    MlirValue.var_ name => String.concat "%" name,
    MlirValue.arg_ index => String.concat "%arg" (I64.to_string index),
}

/// One attribute, as it appears in an op's `{...}` block.
pub def show_mlir_attr (attr : MlirAttr) : String := match attr {
    MlirAttr.unit_ name => name,
    MlirAttr.valued_ name value => name ++ " = " ++ value,
    MlirAttr.bare_ spelling => spelling,
}

/// `loc("file.mo":12:5)`.
///
/// One place owns the format, so a diagnostic's location cannot come out
/// with a different spelling from a different call site -- and the format
/// is exactly what `mlir-opt` echoes back, which Phase 0's malformed-module
/// step asserts reaches the caller (`broken.mlir:2:12: error:`).
pub def mlir_loc (file : String) (line : I64) (column : I64) : String :=
    String.concat "loc(\"" (String.concat file
        (String.concat "\":" (String.concat (I64.to_string line)
            (String.concat ":" (String.concat (I64.to_string column) ")")))))

/// The `{...}` block for `attrs`, or `""` for none.
///
/// `attrs` is mentioned exactly ONCE -- by `collect_attr_text` -- and the
/// emptiness test then runs on the joined STRING, which is `Copy`. The
/// obvious shape (`match attrs { List.empty => "", List.cons _ _ => ... use
/// attrs ... }`) mentions it in the scrutinee and again in an arm, which the
/// affine rule reads as a double use; going through a string satisfies it
/// and is no less clear.
#[partial]
pub def show_mlir_attrs (attrs : List MlirAttr) : String :=
    show_attr_block (String.concat_list (List.reverse (collect_attr_text attrs List.empty)))

/// The rendered attributes, reversed (the accumulator convention every list
/// renderer in this mote uses).
#[partial]
def collect_attr_text (attrs : List MlirAttr) (acc : List String) : List String := match attrs {
    List.empty => acc,
    List.cons a rest => collect_attr_text rest (List.cons (show_mlir_attr a) acc),
}

/// `" {a, b}"` for a non-empty body, `""` for an empty one.
def show_attr_block (body : String) : String :=
    if String.is_empty body then "" else " {" ++ body ++ "}"
