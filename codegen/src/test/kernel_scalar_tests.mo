/// `codegen::kernel::scalar` -- the scalar emitter.
///
/// ## What this file has to prove
///
/// `scalar.mo` turns a reduced `Term` into `arith`/`scf`/`memref` ops. Two
/// things can go wrong silently, and each has its own section below:
///
/// 1. **A wrong OP.** An `i64_add` that emitted `arith.subi` still compiles and
///    still runs; it computes the wrong number. So the positive tests pin the
///    rendered op TEXT rather than the constructor, because the text is what
///    reaches `mlir-opt` -- the same discipline `kernel_shape_tests.mo` uses
///    for types.
/// 2. **A missing diagnostic.** A closure, an unresolved reference, a
///    constructor and an unlowerable literal are four distinct ways to be
///    outside the subset, and a rule that stopped firing would show up as
///    emitted IR that `mlir-opt` rejects several hundred lines later. Each
///    therefore gets a negative test AND a control that stays silent.
///
/// ## The readiness gate, tested first
///
/// `emit_kernel_body` refuses when EITHER predecessor reported a finding
/// (`KernelShape.ready` / `KernelExtract.ready`). That is a deliberate
/// difference from a best-effort emitter, and it is the first thing this file
/// pins: a shape with a diagnostic emits NOTHING, even for a body it could
/// have lowered.
///
/// ## Two measured facts the fixtures transcribe
///
/// * **`n + 1` reaches the emitter as `((HAdd.add n) 1)`**, not as
///   `i64_add n 1` -- measured through the real front end (the plan's cost item
///   8). Both spellings are accepted, so both are tested, and the spine
///   flattening that makes the arity-2 case work is what the second test pins.
/// * **A `Term.var` at the sentinel index is a global reference**, which is
///   what an unresolved name looks like; a param is a bound de Bruijn variable
///   whose NAME is what the emitter looks up.
use lang::types {
    Con, DebugName, Elim, Identifier, Literal, MatchCase, NamePath, NumSuffix, Term,
    binder_named, sentinel,
}
use lib::kernel::detect {KernelDiagnostic}
use lib::kernel::mono {KernelExtract}
use lib::kernel::shape {KernelShape, ParamShape}
use lib::kernel::scalar {KernelBody, NameSupply, emit_kernel_body}
use mlir::ir {MlirType}
use mlir::print {print_block_at}
use std::list {List.any}

// ─── fixtures ────────────────────────────────────────────────────────

def bare_npath (s : String) : NamePath := NamePath.mk (List.cons (Identifier.id s) List.empty)

/// A free global reference -- the shape an UNRESOLVED name has, and the shape
/// `mono.mo`'s delta step unfolds.
def ref (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

/// `f a`.
def app (f : Term) (a : Term) : Term := Term.app f a

/// `f a b`.
def app2 (f : Term) (a : Term) (b : Term) : Term := Term.app (Term.app f a) b

/// An `I64` literal.
def int_lit (v : I64) : Term := Term.lit (Literal.num v NumSuffix.i64)

/// A one-argument lambda -- a closure, which rule 2 refuses.
def lam (arg : String) (body : Term) : Term :=
    Term.lam (binder_named (Identifier.id arg)) Term.hole body

/// A signature with `params` and no diagnostics -- the READY shape.
def ready_shape (params : List ParamShape) (results : List MlirType) : KernelShape :=
    KernelShape.mk "k" params results List.empty

/// An extract with `body` and no diagnostics -- the READY body.
def ready_extract (body : Term) : KernelExtract :=
    KernelExtract.mk "k" List.empty body List.empty

/// One `(n : I64)` scalar parameter, not noalias.
def scalar_n : List ParamShape :=
    List.cons (ParamShape.scalar_ "n" MlirType.i64 false) List.empty

/// The rendered body text, at the depth a `func.func` body sits at.
def body_text (b : KernelBody) : String := print_block_at b.block 1

/// Does the rendered body contain `needle`?
def has_text (b : KernelBody) (needle : String) : Bool :=
    String.contains (body_text b) needle

/// Emit `body` against the ready `(n : I64) -> I64` signature.
def emit_body (body : Term) : KernelBody :=
    emit_kernel_body (ready_shape scalar_n (List.cons MlirType.i64 List.empty)) (ready_extract body)

/// The rule tags a diagnostic list reports, in order.
def rules_of (ds : List KernelDiagnostic) : List String := List.map (fn (d : KernelDiagnostic) => d.rule) ds

def has_rule (rule : String) (ds : List KernelDiagnostic) : Bool :=
    List.any (fn (d : KernelDiagnostic) => String.beq d.rule rule) ds

/// Emit and report whether the ONLY thing that happened is a finding tagged
/// `rule` -- the same shape `kernel_detect_tests.mo`'s `reports_exactly` uses.
def reports_exactly (rule : String) (b : KernelBody) : Bool :=
    has_rule rule b.diagnostics && List.length b.diagnostics == 1

// ─── 1. the readiness gate ───────────────────────────────────────────

/// A SHAPE with a diagnostic emits nothing, even though the body is one this
/// emitter could lower. The emitter is not best-effort: a half-emitted kernel
/// is a wrong answer, and this is the test that makes that a rule.
#[test]
def test_a_dirty_shape_emits_nothing : Bool :=
    let shape : KernelShape :=
        KernelShape.mk "k" scalar_n (List.cons MlirType.i64 List.empty)
            (List.cons (KernelDiagnostic.of "k" "shape" "no dimension") List.empty)
    in
    let b : KernelBody := emit_kernel_body shape (ready_extract (int_lit 5)) in
    Bool.not (KernelBody.ready b) && I64.beq (KernelBody.op_count b) 0

/// And the same for an EXTRACT with a diagnostic -- the other half of the gate,
/// which a test of only the shape half would leave open.
#[test]
def test_a_dirty_extract_emits_nothing : Bool :=
    let extract : KernelExtract :=
        KernelExtract.mk "k" List.empty (int_lit 5)
            (List.cons (KernelDiagnostic.of "k" "inline" "unresolved helper") List.empty)
    in
    let b : KernelBody := emit_kernel_body (ready_shape scalar_n (List.cons MlirType.i64 List.empty)) extract in
    Bool.not (KernelBody.ready b) && I64.beq (KernelBody.op_count b) 0

/// The control: with both predecessors clean, the body IS emitted and the
/// function ends in a `return`. Without this, the two tests above would pass
/// for an emitter that never emitted anything.
#[test]
def test_a_ready_kernel_emits_a_body : Bool :=
    let b : KernelBody := emit_body (int_lit 5) in
    KernelBody.ready b && has_text b "return"

// ─── 2. constants ────────────────────────────────────────────────────

/// An `I64` literal becomes an `arith.constant ... : i64`, and the body returns
/// it. The TYPE is what the text pins: an `i32` here would be a different
/// number at the ABI.
#[test]
def test_an_i64_literal_is_an_i64_constant : Bool :=
    let b : KernelBody := emit_body (int_lit 5) in
    has_text b "arith.constant 5 : i64" && has_text b "return %t0 : i64"

/// An `f32` literal keeps its SOURCE spelling, which is exactly what
/// `arith.constant` wants (`1.5 : f32`) -- Monad keeps a float literal as its
/// text for the reason `Literal.flt`'s own doc comment gives.
#[test]
def test_an_f32_literal_keeps_its_spelling : Bool :=
    let b : KernelBody :=
        emit_kernel_body
            (ready_shape List.empty (List.cons MlirType.f32 List.empty))
            (ready_extract (Term.lit (Literal.flt "1.5" NumSuffix.f32)))
    in
    has_text b "arith.constant 1.5 : f32"

// ─── 3. arithmetic: both measured spellings ──────────────────────────

/// The `#[native i64_add]` spelling.
#[test]
def test_i64_add_is_arith_addi : Bool :=
    let b : KernelBody := emit_body (app2 (ref "i64_add") (ref "n") (int_lit 1)) in
    has_text b "arith.addi %n, %t0 : i64"

/// The MEASURED spelling: `n + 1` arrives as `((HAdd.add n) 1)`, so the head is
/// a class-method reference and the spine has arity 2. This is the test that
/// pins the spine FLATTENING -- a walk that only looked at the outermost node
/// would see a non-native head and report `unsupported`.
#[test]
def test_the_measured_class_method_spelling_is_also_addi : Bool :=
    let b : KernelBody := emit_body (app2 (ref "HAdd.add") (ref "n") (int_lit 1)) in
    has_text b "arith.addi %n, %t0 : i64"

/// A multiplication, so the table is not accidentally one entry wide.
#[test]
def test_i64_mul_is_arith_muli : Bool :=
    let b : KernelBody := emit_body (app2 (ref "i64_mul") (ref "n") (int_lit 2)) in
    has_text b "arith.muli"

/// A comparison yields an `i1`, NOT an `i64`: `arith.cmpi`'s result is the
/// predicate's type, and emitting `i64` there would make the `scf.if` below
/// fail to verify.
#[test]
def test_a_comparison_is_an_i1 : Bool :=
    let b : KernelBody := emit_body (app2 (ref "i64_lt") (ref "n") (int_lit 1)) in
    has_text b "arith.cmpi slt, %n, %t0 : i64"

/// An unknown native is a DIAGNOSTIC rather than a silent no-op -- the control
/// for the table above, and the reason an unsupported op cannot slip through as
/// emitted IR that `mlir-opt` rejects later.
#[test]
def test_an_unknown_native_is_reported : Bool :=
    let b : KernelBody := emit_body (app2 (ref "i64_frobnicate") (ref "n") (int_lit 1)) in
    reports_exactly "unsupported" b

// ─── 4. references ───────────────────────────────────────────────────

/// A parameter reference resolves to its MLIR argument -- no op, just a value.
#[test]
def test_a_parameter_reference_resolves : Bool :=
    let b : KernelBody := emit_body (ref "n") in
    KernelBody.ready b && has_text b "return %n : i64"

/// An UNRESOLVED reference is an `inline` finding, which is the same rule
/// `mono.mo` reports: a reference that survived inlining is a call
/// `scalar.mo` cannot lower. It stays a diagnostic rather than a guess because
/// emitting a name MLIR does not know is a verifier error.
#[test]
def test_an_unresolved_reference_is_reported : Bool :=
    let b : KernelBody := emit_body (ref "helper") in
    reports_exactly "inline" b

/// The control for the two above: a name that IS a parameter is silent, and a
/// name that is not is not -- the difference the rule turns on.
#[test]
def test_only_unknown_names_are_reported : Bool :=
    KernelBody.ready (emit_body (ref "n")) && Bool.not (KernelBody.ready (emit_body (ref "helper")))

// ─── 5. the constructs the subset refuses ────────────────────────────

/// A lambda is a `closure` finding. Rule 2 already refuses it one layer up, so
/// this is the emitter's own backstop -- and it matters because a body reaching
/// here with a lambda would otherwise emit nothing for it and return a value
/// that does not exist.
#[test]
def test_a_lambda_is_reported : Bool :=
    reports_exactly "closure" (emit_body (lam "y" (ref "y")))

/// A constructor application is an `alloc` finding: there is no heap on a
/// device, and `memref.alloc` is deliberately unspellable in the dialect module.
#[test]
def test_a_constructor_is_reported : Bool :=
    let some : Term := Term.con (Con.mk (Identifier.id "some") (bare_npath "Option") 1 List.empty) in
    reports_exactly "alloc" (emit_body some)

/// A `Term.elim` that never desugared is reported rather than emitted. This is
/// the shape a kernel read through `elaborate_loaded_modules` (rather than
/// `compile_input_of_modules`) carries for an `if` -- the plan's cost item 8 --
/// so the diagnostic is the honest answer for a term the desugarer never
/// reached.
#[test]
def test_an_undesugared_elim_is_reported : Bool :=
    let e : Elim :=
        Elim.mk (bare_npath "Bool") List.empty List.empty List.empty Term.hole
            (List.cons (ref "n") List.empty) (ref "n")
    in
    reports_exactly "unsupported" (emit_body (Term.elim e))

/// A hole is reported. A body-less native reaches the emitter as `Term.hole`,
/// and emitting nothing for it would silently produce a function returning an
/// uninitialised value.
#[test]
def test_a_hole_is_reported : Bool :=
    reports_exactly "unsupported" (emit_body Term.hole)

// ─── 6. branches ─────────────────────────────────────────────────────

/// An `if` becomes a result-carrying `scf.if`, with `scf.yield` in each arm.
///
/// Both halves are asserted: the op's header (so the result type is declared)
/// and the arm terminator (so `mlir-opt`'s verifier accepts the region). The
/// second is the one a hand-written emitter forgets, and it fails as a
/// verifier complaint rather than as a wrong number.
#[test]
def test_an_if_becomes_an_scf_if : Bool :=
    let b : KernelBody :=
        emit_body (Term.lit (Literal.if_ (app2 (ref "i64_lt") (ref "n") (int_lit 1)) (int_lit 0) (ref "n")))
    in
    KernelBody.ready b && has_text b "scf.if" && has_text b "scf.yield"

/// The arms' ops go INSIDE the region, not before it: the then arm's constant
/// must not be emitted at the function's top level, where it would be computed
/// unconditionally. A version that appended arm ops to the outer list would
/// still render a plausible-looking body, so this is pinned by counting the
/// `arith.constant` lines.
#[test]
def test_the_arm_ops_are_inside_the_region : Bool :=
    let b : KernelBody :=
        emit_body (Term.lit (Literal.if_ (app2 (ref "i64_lt") (ref "n") (int_lit 1)) (int_lit 0) (ref "n")))
    in
    I64.beq (count_occurrences (body_text b) "arith.constant 0 : i64") 1

/// A three-arm `match` is reported rather than lowered. Only the two-arm `Bool`
/// shape is emittable today -- a wider one needs a constructor tag the kernel
/// does not carry -- so this is the control that keeps the two-arm case from
/// being "any match at all".
#[test]
def test_a_three_arm_match_is_reported : Bool :=
    let cases : List MatchCase := [
        MatchCase.mk (Identifier.id "a") List.empty (int_lit 0) Option.none Option.none,
        MatchCase.mk (Identifier.id "b") List.empty (int_lit 1) Option.none Option.none,
        MatchCase.mk (Identifier.id "c") List.empty (int_lit 2) Option.none Option.none,
    ] in
    reports_exactly "unsupported" (emit_body (Term.lit (Literal.match_ (ref "n") cases)))

/// A two-arm match lowers, with the scrutinee as the condition -- the positive
/// control for the test above.
#[test]
def test_a_two_arm_match_lowers : Bool :=
    let cases : List MatchCase := [
        MatchCase.mk (Identifier.id "a") List.empty (int_lit 0) Option.none Option.none,
        MatchCase.mk (Identifier.id "b") List.empty (int_lit 1) Option.none Option.none,
    ] in
    let b : KernelBody := emit_body (Term.lit (Literal.match_ (ref "n") cases)) in
    KernelBody.ready b && has_text b "scf.if"

// ─── 7. the name supply ──────────────────────────────────────────────

/// Fresh names are distinct and monotone, which is what MLIR's whole-module SSA
/// uniqueness requires. A supply that returned the same name twice would emit a
/// body `mlir-opt` rejects, and the failure would point at a generated line.
#[test]
def test_fresh_names_are_distinct : Bool :=
    let s0 : NameSupply := NameSupply.of "t" in
    match NameSupply.fresh s0 {
        Pair.pair n1 s1 => match NameSupply.fresh s1 {
            Pair.pair n2 _ => String.beq n1 "t0" && String.beq n2 "t1",
        },
    }

/// Two ops in one body get different names, which is the property the supply
/// exists for -- pinned through the emitter rather than on the supply alone.
#[test]
def test_two_ops_get_distinct_names : Bool :=
    let b : KernelBody := emit_body (app2 (ref "i64_add") (int_lit 1) (int_lit 2)) in
    has_text b "%t0" && has_text b "%t1"

// ─── small helpers ───────────────────────────────────────────────────

/// How many times `needle` occurs in `haystack`. `String.contains` is a Bool,
/// so a count needs the split -- and `String.split` takes `(s, sep)` in that
/// order, which a first version had reversed (and which made the count read 0
/// for a body that plainly contained the needle).
def count_occurrences (haystack : String) (needle : String) : I64 :=
    I64.sub (List.length (String.split haystack needle)) 1
