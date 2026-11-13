/// `MlirModule` -> `.mlir` text. The `llvm/src/ir.mo`'s `emit_module`
/// analogue, and the ONLY module that produces a whole file.
///
/// The division with `ir.mo`: the dialect modules compose an op's own
/// syntax (`arith.addf %a, %b : f32`) and this file owns everything
/// AROUND it -- indentation, region nesting, `loc(...)` placement, and
/// the `func.func` header. That is the same split `llvm/` uses, and it is
/// what keeps a per-op printer from having to know about block structure.
///
/// ## `loc(...)` is placed here, not by the dialects
///
/// An op's `loc` field is a string and this printer appends it as MLIR's
/// own trailing attribute (`... : f32 loc("k.mo":12:5)`). Placing it in
/// one loop rather than at ~20 construction sites is what makes
/// "every op carries a location" a property of the printer instead of a
/// convention the emitter has to remember -- which matters because
/// `plans/bootstrapping/mlir-codegen.md` records `loc(...)` as the
/// cheapest quality win in the plan and the only channel a `mlir-opt`
/// diagnostic has back to Monad source.
///
/// ## `#[partial]` throughout, and why
///
/// The whole printer family is one recursive cycle over REGION NESTING:
/// `print_function` -> `print_block` -> `print_ops` -> `print_op` ->
/// `print_region_body` -> `print_block`. A nested region arrives through an
/// op's `body` field, so the descent is not a structural subterm of any
/// parameter the checker can see, and it rejects the family without the
/// annotation. `llvm/src/ir.mo`'s `emit_block`/`emit_instrs` pair is marked
/// for exactly the same reason. The list-walking helpers are marked too so
/// that the cycle has no unannotated edge anywhere in it.
///
/// ## Chunk-then-join, like `llvm/src/ir.mo`
///
/// Every list renderer collects chunks and joins ONCE. The
/// `String.concat a (recurse rest)` shape recopies the whole accumulated
/// tail per element, which `llvm/src/ir.mo` measured as ~1.7 GB of copying
/// for the compiler's own module and fixed there; a kernel module is small,
/// but the same shape costs the same asymptotically and this file is the
/// template a large module would follow.

// The two `MlirBlockSeparator` CONSTRUCTORS are imported by name, not just
// the type: the self-hosted compiler requires a constructor to be named in a
// `use ... {...}` line before a pattern can match on it, and it is the
// authority here. The Rust host reports them as "unused" because it resolves
// a constructor through the matched value's type instead -- a cosmetic
// divergence on the bootstrap side, and the self-hosted answer wins
// (AGENTS.md). Removing them to silence that note breaks the real compiler.
use lib::ir {
    MlirBlock, MlirBlockSeparator, MlirBlockSeparator.else_arm,
    MlirBlockSeparator.plain, MlirFunction, MlirModule, MlirOp, MlirParam,
    MlirType, show_mlir_type,
}

/// Two spaces per nesting level, which is MLIR's own pretty-printer
/// convention and therefore what the re-parse comparison in
/// `scripts/check-mlir-goldens.sh` will see.
def indent (depth : I64) : String := String.repeat "  " depth

/// A whole module: each function at top level, one blank line between.
#[partial]
pub def print_module (module_ : MlirModule) : String := match module_ {
    { functions := functions } => print_functions functions,
}

#[partial]
def print_functions (functions : List MlirFunction) : String :=
    String.concat_list (List.reverse (print_functions_go functions List.empty))

#[partial]
def print_functions_go (functions : List MlirFunction) (acc : List String) : List String :=
    match functions {
        List.empty => acc,
        List.cons f rest =>
            print_functions_go rest (List.cons (print_function f) acc),
    }

/// One `func.func`, header and body.
///
/// The blank line between functions is MLIR's own output shape: `mlir-opt`
/// separates top-level ops by one empty line, and a golden compared against
/// its output would otherwise differ by whitespace alone -- which is a
/// diff nobody reads and every reviewer has to re-derive.
#[partial]
def print_function (f : MlirFunction) : String := match f {
    { name, params, results, body, loc, visibility } =>
        let head := function_header name params results visibility loc in
        String.concat head (String.concat (print_block body 1) "\n}") ++ "\n",
}

/// `func.func private @name(%a: memref<16xf32> {llvm.noalias}, %b: i32) -> f64 {`
///
/// `visibility` and the result list are both optional and both appear in a
/// fixed order, so they are spliced. The opening brace is unconditional:
/// MLIR prints the `{` for a body-less function too (`func.func @f() {`),
/// so there is nothing for the result list to decide here.
/// The header from its parts, so the two callers above destructure a
/// function exactly once each. Splitting it this way is what keeps the
/// printer affine-clean: `print_function` needs the BODY as well as the
/// header, so it cannot simply hand the whole record on.
#[partial]
def function_header (name : String) (params : List MlirParam) (results : List MlirType)
    (visibility : String) (loc : String) : String :=
    let vis := if String.is_empty visibility then "" else visibility ++ " " in
    "func.func " ++ vis ++ "@" ++ name ++ "(" ++ print_params params ++ ")"
        ++ print_result_list results ++ print_func_loc_suffix loc ++ " {"

/// ` -> (f64)`, or `""` for a function returning nothing.
#[partial]
def print_result_list (results : List MlirType) : String :=
    let body := String.concat_list (List.reverse (print_types_go results List.empty)) in
    if String.is_empty body then "" else " -> (" ++ body ++ ")"

#[partial]
def print_types_go (tys : List MlirType) (acc : List String) : List String := match tys {
    List.empty => acc,
    List.cons t rest => print_types_go rest (List.cons (show_mlir_type t) acc),
}

/// `%a: memref<16xf32> {llvm.noalias}, %n: i32`.
///
/// `{llvm.noalias}` is placed on the ARGUMENT, which is where MLIR's
/// parser requires it -- an op-level `{...}` block would land on the
/// `func.func` itself and be a different (and rejected) attribute.
/// `%a: T, %b: U` -- COMMA-separated, and the separator is appended to
/// everything but the last entry.
///
/// A missing comma here is not a cosmetic bug: `%dst: memref<16xf32>%a_bits:
/// i32` is `expected ','` from `mlir-opt`, which is what the first version
/// of this file produced and what the golden harness caught.
#[partial]
def print_params (params : List MlirParam) : String :=
    String.concat_list (List.reverse (print_params_go params List.empty))

#[partial]
def print_params_go (params : List MlirParam) (acc : List String) : List String :=
    match params {
        List.empty => acc,
        List.cons p rest =>
            print_params_go rest
                (List.cons (print_param_with_separator p (List.is_empty rest)) acc),
    }

/// `p`'s text, with `, ` appended unless it is the last parameter.
#[partial]
def print_param_with_separator (p : MlirParam) (last : Bool) : String :=
    let body := print_param p in
    if last then body else body ++ ", "

#[partial]
def print_param (p : MlirParam) : String := match p {
    { name, ty, noalias } =>
        let base := "%" ++ name ++ ": " ++ show_mlir_type ty in
        if noalias then base ++ " {llvm.noalias}" else base,
}

/// A block at `depth`: its label (when it has one), its block arguments,
/// and its ops.
///
/// A FUNCTION's entry block is printed without a `^label:` line: MLIR
/// allows a region's single entry block to be implicit, and `mlir-opt`
/// prints it that way -- printing the label would make every golden differ
/// from the tool's own output. Which blocks get a line is decided by the
/// label being EMPTY (`print_block_header`), not by a caller-passed flag:
/// `MlirBlock.entry` builds a function body's entry block with `""` and
/// every nested block names itself, so the shape follows from the model.
#[partial]
def print_block (block : MlirBlock) (depth : I64) : String := match block {
    { label, args, ops, .. } =>
        String.concat (block_header label args depth) (print_ops ops depth),
}

/// The `^label(...args):` line, or `""` for a function body's entry block.
/// The `^label(...args):` line from its parts, `""` for an entry block --
/// split out of `print_block_header` for the same reason
/// `function_header` is split out of `print_function_header`: the caller
/// that needs the ops as well destructures the block once and passes the
/// two fields down.
#[partial]
def block_header (label : String) (args : List MlirType) (depth : I64) : String :=
    if String.is_empty label then ""
    else String.concat "\n" (String.concat (indent depth) (block_label label args))

#[partial]
def block_label (label : String) (args : List MlirType) : String :=
    "^" ++ label ++ print_block_args args ++ ":"

/// `(%i: index, %acc: f64)` for a block's arguments, `""` for none.
///
/// The names are positional (`%arg0`, `%arg1`, ...) because a block
/// argument has no name of its own in this model: an `scf.for` body binds
/// them by POSITION, and the ops inside refer to them by the same
/// `MlirValue.arg_` index, so generating the name here is the only place
/// the two could disagree -- and generating it in one place is what stops
/// them.
#[partial]
def print_block_args (args : List MlirType) : String :=
    let body := String.concat_list (List.reverse (print_block_args_go args 0 List.empty)) in
    if String.is_empty body then "" else "(" ++ body ++ ")"

#[partial]
def print_block_args_go (args : List MlirType) (i : I64) (acc : List String) : List String :=
    match args {
        List.empty => acc,
        List.cons t rest =>
            print_block_args_go rest (i + 1)
                (List.cons ("%arg" ++ I64.to_string i ++ ": " ++ show_mlir_type t) acc),
    }

/// An op list at `depth`. A nested region's blocks are printed one level
/// deeper, and the closing `}` of the region at `depth`.
#[partial]
def print_ops (ops : List MlirOp) (depth : I64) : String :=
    String.concat_list (List.reverse (print_ops_go ops depth List.empty))

#[partial]
def print_ops_go (ops : List MlirOp) (depth : I64) (acc : List String) : List String := match ops {
    List.empty => acc,
    List.cons op rest => print_ops_go rest depth (List.cons (print_op op depth) acc),
}

/// One op: its own line, then (for a region-carrying op) its nested blocks
/// and a closing brace.
///
/// ## `loc(...)` goes BEFORE the brace, and that was measured
///
/// MLIR's pretty form puts an op's `loc(...)` between the header and the
/// region, not after it: `scf.for %i = %c0 to %c16 step %c1 loc(...) {`.
/// Printed after the closing brace it is `expected '{' to begin a region`
/// from `mlir-opt` 21.1.8 -- a parse error, not a warning. So the suffix is
/// spliced in before the `{` and nowhere else, which is why it lives in
/// `print_op` rather than in each dialect.
#[partial]
def print_op (op : MlirOp) (depth : I64) : String := match op {
    { lhs, text, body, loc } =>
        let line := "\n" ++ indent depth ++ lhs ++ text in
        let inner := print_region_body body (depth + 1) in
        // The emptiness test runs on the RENDERED region rather than on the
        // list, so `body` is mentioned exactly once: an empty region renders
        // nothing, which is what makes this a statement instead of a block.
        //
        // `loc(...)` goes at the very END of the op: after the type suffix
        // for an op with no region, and after the closing brace for one with
        // a region. Both were measured against `mlir-opt` 21.1.8, and the
        // region case is the surprising one -- `scf.for ... loc(...) {` is
        // `expected '{' to begin a region`, so the suffix cannot be spliced
        // before the brace.
        if String.is_empty inner then line ++ print_loc_suffix loc
        else line ++ " {" ++ inner ++ "\n" ++ indent depth ++ "}" ++ print_loc_suffix loc,
}

/// A region's blocks: the first at `depth` (which the caller has already
/// opened a brace for), every later one after a blank line -- MLIR
/// separates blocks with an empty line, and the round-trip comparison
/// sees it.
#[partial]
def print_region_body (blocks : List MlirBlock) (depth : I64) : String :=
    String.concat_list (List.reverse (print_region_body_go blocks depth true List.empty))

#[partial]
def print_region_body_go (blocks : List MlirBlock) (depth : I64) (first : Bool) (acc : List String) : List String :=
    match blocks {
        List.empty => acc,
        List.cons b rest =>
            print_region_body_go rest depth false (List.cons (print_region_block b depth first) acc),
    }

/// One block of a region, introduced by its separator.
///
/// `scf.if`'s second arm is introduced by the `else` keyword, on the SAME
/// line as the first arm's closing brace: `} else {`. So `else_arm` gets no
/// leading newline and emits its own `else {`, and the caller's closing
/// brace for the first arm is what precedes it. Measured against
/// `mlir-opt` 21.1.8: printing that arm as a `^bb1:` header is
/// `expected 'else' to terminate`.
#[partial]
def print_region_block (b : MlirBlock) (depth : I64) (first : Bool) : String := match b {
    { label, args, ops, separator } => match separator {
        // `} else {` -- the FIRST arm's closing brace, then the keyword,
        // then the second arm's opening brace, all on one line. The arm's
        // OWN closing brace is `print_op`'s trailing `}`, which is emitted
        // once for the whole region -- so this string deliberately does not
        // emit one, or the op would end with `}}`.
        // `depth` here is ALREADY the op's own indent -- the caller
        // (`print_region_body`) passes `depth + 1`, so the arm's body sits
        // one level in. The joining `}` therefore belongs at `depth - 1`,
        // which is `indent (depth - 1)`: the level the op itself is at.
        MlirBlockSeparator.else_arm =>
            "\n" ++ indent (depth - 1) ++ "} else {" ++ print_ops ops depth,
        MlirBlockSeparator.plain =>
            // A nested block always carries its label; only a func body's
            // entry block may omit one, and that path goes through
            // `print_function`.
            (if first then "" else "\n")
                ++ String.concat (block_header label args depth) (print_ops ops depth),
    },
}

/// ` loc("file.mo":12:5)`, or `""` -- an OP's location.
///
/// One place owns this, so an op cannot lose its location by being
/// constructed through a path that forgot -- and the dialects never see the
/// syntax at all (`ir.mo`'s `MlirOp.stmt` takes the suffix as a plain
/// string).
#[partial]
def print_loc_suffix (loc : String) : String :=
    if String.is_empty loc then "" else " " ++ loc

/// ` attributes {loc = loc("file.mo":12:5)}`, or `""` -- a `func.func`'s
/// location, which is a DIFFERENT SHAPE from an op's.
///
/// Measured against `mlir-opt` 21.1.8: `func.func @f() loc(...) {` is
/// `expected operation name in quotes`, because a function's location is
/// carried in its attribute dictionary, not as the trailing `loc` an
/// operation gets. Printed the op way, every function header would fail to
/// parse -- which is exactly what the first version of this printer did,
/// and why the goldens are run through real `mlir-opt` rather than only
/// byte-compared to a file this printer also wrote.
#[partial]
def print_func_loc_suffix (loc : String) : String :=
    if String.is_empty loc then "" else " attributes {loc = " ++ loc ++ "}"
