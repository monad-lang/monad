/// `codegen::kernel::mono` -- the reducer, the inliner, and the SIXTH rule.
///
/// ## What this file has to prove, and why each half is separate
///
/// The plan's sixth subset rule ("dimensions literal at the call site") is the
/// one rule `detect.mo` cannot own, because it is a property of a CALL. Its
/// tests therefore live here, and the first section below is one NEGATIVE test
/// per direction of that rule, each with a control that must stay silent.
///
/// The rest of the file is the REDUCER, and the reason it is tested at all is
/// that the whole extraction premise rests on it: an elaborated kernel body
/// spells `4 + 4` as `HAdd_A_A_A_add __Dict_Add_I64 4i64 4i64`, so if the four
/// reduction steps (delta, iota, beta, native fold) do not compose, no
/// dimension ever becomes a literal and `shape.mo` has nothing to read. Each
/// step gets its own test -- a step that stopped firing would be invisible in
/// the end-to-end test if another step happened to cover for it -- and the
/// end-to-end test then pins the COMPOSITION against the exact measured shape.
///
/// ## Two facts about the fixtures, both measured rather than assumed
///
/// * **A `Literal.match_` pattern cannot be nested inside a `Term.lit`
///   pattern.** `match term_peel t { Term.lit (Literal.match_ s c) => ... }`
///   is `expected '('`; the two-step `Term.lit l => match l { ... }` is what
///   parses. `mono.mo`'s own `match_redex_literal` is split for that reason.
/// * **A numeric-literal match pattern does not parse** (`match n { 0 => ... }`
///   is `expected '('`). Every count assertion below is an `if`, not a match.
///
/// ## The dictionary fixtures are HAND-BUILT, and deliberately
///
/// `lang::module`'s `elaborate_synthetic_source` produces the real shapes --
/// and that is how they were measured -- but it needs a whole module load and
/// minutes of wall time per run. The fixtures below are the measured shapes
/// transcribed, so the suite stays a unit test. The end-to-end pin against the
/// real front end is `motes/kernel_example/`'s, in Phase 2's last item.
use lang::types {
    AttrArg, Attribute, Con, DebugName, Decl, Def, Identifier, Literal, MatchCase,
    NamePath, Native, NumSuffix, Term, TypeConstraint, Visibility, binder_named,
    sentinel, term_peel,
}
use lib::kernel::detect {KernelDiagnostic, extract_kernels}
use lib::kernel::mono {
    KernelCallSite, KernelExtract, build_def_table, call_sites_of, ctor_last_segment,
    dim_diagnostic, dim_diagnostics, dim_diagnostics_for_sites, dim_positions_of,
    extract_kernel, fold_native_binop, id_text, inline_term, int_lit,
    int_literal_of, iota_match, reduce_with, spine_args_of, unresolved_refs_of,
}
use llvm::strmap {str_map_empty}
use std::list {List.any}
use std::map {HashMap}

// ─── fixtures ────────────────────────────────────────────────────────

def kernel_attr : List Attribute :=
    List.cons (Attribute.mk (Identifier.id "kernel") List.empty) List.empty

def bare_npath (s : String) : NamePath := NamePath.mk (List.cons (Identifier.id s) List.empty)

/// A global reference: a `Term.var` at the free sentinel index, which is the
/// only shape `mono.mo`'s delta step unfolds.
def ref (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

/// A bound variable at index `i`.
def bound (i : I64) : Term := Term.var i DebugName.unnamed

def app (f : Term) (a : Term) : Term := Term.app f a

def app2 (f : Term) (a : Term) (b : Term) : Term := Term.app (Term.app f a) b

def app3 (f : Term) (a : Term) (b : Term) (c : Term) : Term :=
    Term.app (Term.app (Term.app f a) b) c

def lam (arg : String) (body : Term) : Term :=
    Term.lam (binder_named (Identifier.id arg)) Term.hole body

/// `I64` as a term, for signatures.
def i64_ty : Term := Term.con (Con.mk (Identifier.id "I64") (bare_npath "I64") 0 List.empty)

/// A `#[native name]`-attributed def with no body -- how `init/src/number.mo`
/// declares `I64.add`.
def native_def (name : String) (native_name : String) : Def :=
    Def.mk (bare_npath name) i64_ty Term.hole ([] : List TypeConstraint)
        [Attribute.mk (Identifier.id "native")
            (List.cons (AttrArg.ident (Identifier.id native_name)) List.empty)]
        Visibility.package_private List.empty

/// A plain def with a body.
def mk_def (name : String) (body : Term) : Def :=
    Def.mk (bare_npath name) i64_ty body ([] : List TypeConstraint)
        ([] : List Attribute) Visibility.package_private List.empty

def mk_kernel (name : String) (typ : Term) (body : Term) : Def :=
    Def.mk (bare_npath name) typ body ([] : List TypeConstraint) kernel_attr
        Visibility.package_private List.empty

/// `fn (a : I64) => fn (b : I64) => body` -- the arity every native binary op
/// reaches the reducer with.
def binop_body (body : Term) : Term := lam "a" (lam "b" body)

/// `Term.ntv (Native.mk name 2 [first])` -- a native reference carrying its
/// FIRST argument, which is the shape `I64.add x y` reaches the reducer in
/// (`fold_native_two` reads the first operand out of the native's own `args`).
def ntv1 (name : String) (first : Term) : Term :=
    Term.ntv (Native.mk (Identifier.id name) 2 (List.cons (Option.some first) List.empty))

/// `fn a => fn b => i64_add a b` -- the elaborated `Add_I64_add` body.
def add_body : Term := binop_body (app (ntv1 "i64_add" (bound 1)) (bound 0))

/// The dictionary bridge's body: `fn __dict => fn a => fn b =>
/// (match __dict { mk add => add }) a b`.
def bridge_body (arm_name : String) : Term :=
    lam "__dict"
        (lam "a" (lam "b"
            (app2 (Term.lit (Literal.match_ (bound 2)
                [MatchCase.mk (Identifier.id arm_name) [Identifier.id "add"] (bound 0)
                    Option.none Option.none]))
                (bound 1) (bound 0))))

def table_of (defs : List Def) : HashMap String Term :=
    build_def_table (List.map (fn d => Decl.def_d d) defs)

/// The whole measured dictionary chain: `HAdd_A_A_A_add`, its dictionary and
/// `Add_I64_add`. Shared by the two composition tests because it IS the claim
/// they make; a per-test copy would let one drift from the other.
def add_chain : HashMap String Term := table_of [
    mk_def "HAdd_A_A_A_add" (bridge_body "mk"),
    mk_def "__Dict_Add_I64" (app (ref "__Dict_Add_I64.mk") (ref "Add_I64_add")),
    mk_def "Add_I64_add" add_body,
]

// ─── the SIXTH rule: literal dimensions at the call site ─────────────

/// The rule fires on a variable at a dimension position.
#[test]
def test_dim_fires_on_a_variable_dimension : Bool :=
    let ds : List KernelDiagnostic := dim_diagnostics "saxpy" [ref "n"] [0]
    in
    List.length ds == 1 && String.beq (hd_rule ds) "dim"

/// The control: a LITERAL argument at the same position is silent. This is the
/// difference the whole rule is.
#[test]
def test_dim_is_silent_for_a_literal_dimension : Bool :=
    List.is_empty (dim_diagnostics "saxpy" [int_lit 16] [0])

/// A computed argument is not a literal either -- a dimension has to be a
/// CONSTANT, and a computation is exactly what `mono.mo` exists to fold away.
#[test]
def test_dim_fires_on_a_computed_dimension : Bool :=
    let ds : List KernelDiagnostic :=
        dim_diagnostics "saxpy" [app2 (ref "f") (ref "x") (ref "y")] [0]
    in
    List.length ds == 1 && String.beq (hd_rule ds) "dim"

/// A position that is NOT a dimension is not checked: a non-literal argument
/// at position 1, with only position 0 declared a dimension, is silent.
/// Without this the rule would reject every kernel taking a pointer.
#[test]
def test_dim_ignores_a_non_dimension_position : Bool :=
    List.is_empty (dim_diagnostics "saxpy" [int_lit 16, ref "buf"] [0])

/// One finding PER offending position.
#[test]
def test_dim_reports_every_offending_position : Bool :=
    List.length (dim_diagnostics "saxpy" [ref "n", ref "m"] [0, 1]) == 2

/// The diagnostic names the callee, the position and what was written -- the
/// plan's message shape, and the only thing a user sees.
#[test]
def test_dim_diagnostic_names_the_call : Bool :=
    let rendered : String := KernelDiagnostic.render (dim_diagnostic "saxpy" 0 "n")
    in
    String.contains rendered "saxpy"
        && String.contains rendered "non-literal dimension"
        && String.contains rendered "argument 0"
        && String.contains rendered "n"

/// A float is NOT a dimension. `Literal.flt` is the one literal shape that must
/// not satisfy the rule, and `int_literal_of` is where that is decided.
#[test]
def test_a_float_literal_is_not_a_dimension : Bool :=
    List.length (dim_diagnostics "k" [Term.lit (Literal.flt "3.0" NumSuffix.f64)] [0]) == 1

/// A suffixed integer literal IS a dimension: `16u8` names a constant just as
/// `16` does, and refusing it would be a false positive.
#[test]
def test_a_suffixed_integer_literal_is_a_dimension : Bool :=
    match int_literal_of (Term.lit (Literal.num 16 NumSuffix.u8)) {
        Option.some v => I64.beq v 16,
        Option.none => false,
    }

/// A negative literal is a dimension too. `Literal.num` carries a signed
/// `I64`, so this is the sign's own control.
#[test]
def test_a_negative_integer_literal_is_a_dimension : Bool :=
    match int_literal_of (int_lit (0 - 3)) {
        Option.some v => I64.beq v (0 - 3),
        Option.none => false,
    }

// ─── dim_positions_of ────────────────────────────────────────────────

/// Every explicit `I64` parameter position, and only those. The fixture has
/// `(n : I64) (buf : Ptr) (m : I64)`, so positions 0 and 2 are dimensions and
/// position 1 is not -- the over-approximation is over I64-ness, not arity.
#[test]
def test_dim_positions_are_the_i64_parameters : Bool :=
    let positions : List I64 := dim_positions_of (mk_kernel "k" three_param_typ Term.hole)
    in
    List.length positions == 2
        && List.any (fn i => I64.beq i 0) positions
        && List.any (fn i => I64.beq i 2) positions
        && Bool.not (List.any (fn i => I64.beq i 1) positions)

def three_param_typ : Term :=
    Term.pi (binder_named (Identifier.id "n")) i64_ty
        (Term.pi (binder_named (Identifier.id "buf")) (ref "Ptr")
            (Term.pi (binder_named (Identifier.id "m")) i64_ty i64_ty))

/// A kernel with no `I64` parameter has no dimensions, so nothing is checked.
#[test]
def test_no_i64_parameters_means_no_dimensions : Bool :=
    let typ : Term := Term.pi (binder_named (Identifier.id "buf")) (ref "Ptr") Term.hole
    in
    List.is_empty (dim_positions_of (mk_kernel "k" typ Term.hole))

// ─── the reducer: each step on its own ───────────────────────────────

/// **Beta**: `(fn x => body) arg` substitutes. The fixture's body returns the
/// bound variable, so the answer is the argument itself.
#[test]
def test_reduce_beta_substitutes_the_argument : Bool :=
    match int_literal_of (reduce_with str_map_empty (app (lam "x" (bound 0)) (int_lit 7))) {
        Option.some v => I64.beq v 7,
        Option.none => false,
    }

/// **Delta**: a free reference to a known def becomes its body.
#[test]
def test_reduce_delta_unfolds_a_known_def : Bool :=
    let defs : HashMap String Term := table_of [mk_def "answer" (int_lit 42)]
    in
    match int_literal_of (reduce_with defs (ref "answer")) {
        Option.some v => I64.beq v 42,
        Option.none => false,
    }

/// The control for delta: an UNKNOWN reference stays put. Without this, delta
/// could be unfolding something it invented and the test above would still
/// pass.
#[test]
def test_reduce_leaves_an_unknown_reference_alone : Bool :=
    let defs : HashMap String Term := table_of [mk_def "answer" (int_lit 42)]
    in
    String.beq (var_text (reduce_with defs (ref "other"))) "other"

/// **Native fold**: `i64_add 4 4` -> `8`, reached through the application spine
/// rather than the native's own `args` (the second operand is the
/// application's argument, which is `fold_native_two`'s whole point).
#[test]
def test_reduce_folds_a_native_binop : Bool :=
    let t : Term := app (ntv1 "i64_add" (int_lit 4)) (int_lit 4)
    in
    match int_literal_of (reduce_with str_map_empty t) {
        Option.some v => I64.beq v 8,
        Option.none => false,
    }

/// The native fold's control: one operand non-literal means NO fold, and the
/// application survives.
#[test]
def test_reduce_does_not_fold_a_non_literal_operand : Bool :=
    match term_peel (reduce_with str_map_empty (app (ntv1 "i64_add" (ref "n")) (int_lit 4))) {
        Term.app _ _ => true,
        _ => false,
    }

/// The native fold is per-OPERATION, not a single `+`: `i64_mul` folds as
/// multiplication. This is the test that catches a table wired to the wrong
/// operation -- a `mul` entry mapping to `add` would pass every test above.
#[test]
def test_reduce_folds_multiplication_as_multiplication : Bool :=
    match int_literal_of (reduce_with str_map_empty (app (ntv1 "i64_mul" (int_lit 6)) (int_lit 7))) {
        Option.some v => I64.beq v 42,
        Option.none => false,
    }

/// **Iota**: a `match` on a constructor application fires the arm selected by
/// the constructor's NAME, and the arm's binder receives the constructor's
/// field.
#[test]
def test_iota_fires_the_arm_named_by_the_constructor : Bool :=
    match iota_match (app (ref "__Dict_Add_I64.mk") (int_lit 5)) one_mk_case {
        Option.some fired => match int_literal_of (reduce_with str_map_empty fired) {
            Option.some v => I64.beq v 5,
            Option.none => false,
        },
        Option.none => false,
    }

def one_mk_case : List MatchCase :=
    [MatchCase.mk (Identifier.id "mk") [Identifier.id "x"] (bound 0) Option.none Option.none]

/// The control: a scrutinee whose head is not a name is STUCK, not an error.
#[test]
def test_iota_is_stuck_on_a_non_constructor_scrutinee : Bool :=
    is_none_opt (iota_match (ref "n") one_mk_case)

/// The control's other half: an arm whose name does not match the constructor
/// does not fire, so a miss is distinguishable from a hit.
#[test]
def test_iota_does_not_fire_a_non_matching_arm : Bool :=
    is_none_opt (iota_match (app (ref "__Dict_Add_I64.mk") (int_lit 5))
        [MatchCase.mk (Identifier.id "other") [Identifier.id "x"] (bound 0) Option.none Option.none])

/// An arity mismatch does not fire either -- `whnf_fire_case`'s contract, and
/// the guard against a de-Bruijn-misaligned arm.
#[test]
def test_iota_does_not_fire_an_arity_mismatch : Bool :=
    is_none_opt (iota_match (ref "__Dict_Add_I64.mk") one_mk_case)

/// The constructor's own dotted name reduces to its LAST segment, which is what
/// makes the `MatchCase.name` comparison work at all.
#[test]
def test_ctor_last_segment_takes_the_last_segment : Bool :=
    String.beq (ctor_last_segment "__Dict_Add_I64.mk") "mk"
        && String.beq (ctor_last_segment "mk") "mk"
        && String.beq (ctor_last_segment "a.b.c") "c"

// ─── the composition: the measured dictionary chain ──────────────────

/// **THE test this module exists for.** The exact shape the front end produces
/// for `4 + 4` -- measured 2026-11-15 through `compile_input_of_modules` --
/// must reduce to `8`.
///
/// The fixture is the whole chain, because the chain is the claim:
/// `HAdd_A_A_A_add` (delta) -> its body's lambda chain (beta) -> the `match` on
/// the dictionary (iota) -> the dictionary's `mk` arm (beta) -> `Add_I64_add`
/// (delta) -> `i64_add` (fold). No single step's test covers this, and no step
/// can be removed without it failing.
#[test]
def test_reduce_folds_the_measured_dictionary_chain : Bool :=
    match int_literal_of (reduce_with add_chain
        (app3 (ref "HAdd_A_A_A_add") (ref "__Dict_Add_I64") (int_lit 4) (int_lit 4))) {
        Option.some v => I64.beq v 8,
        Option.none => false,
    }

/// The same chain with `*` and `+` nested -- the shape `n * 2 + 1` takes, and
/// the reason the reducer is operands-first rather than weak-head. A
/// weak-head-only reducer folds nothing here: the head is `+`, whose left
/// operand is still the `*` redex.
#[test]
def test_reduce_folds_a_nested_dictionary_chain : Bool :=
    match int_literal_of (reduce_with mul_add_chain (nested_sum_call)) {
        Option.some v => I64.beq v 9,
        Option.none => false,
    }

def mul_add_chain : HashMap String Term := table_of [
    mk_def "HAdd_A_A_A_add" (bridge_body "mk"),
    mk_def "HMul_A_A_A_mul" (bridge_body "mk"),
    mk_def "__Dict_Add_I64" (app (ref "__Dict_Add_I64.mk") (ref "Add_I64_add")),
    mk_def "__Dict_Mul_I64" (app (ref "__Dict_Mul_I64.mk") (ref "Mul_I64_mul")),
    mk_def "Add_I64_add" add_body,
    mk_def "Mul_I64_mul" (binop_body (app (ntv1 "i64_mul" (bound 1)) (bound 0))),
]

/// `4 * 2 + 1`, with `4 * 2` spelled as the dictionary chain so the left operand
/// is still a redex when the `+` head is first seen.
def nested_sum_call : Term :=
    app3 (ref "HAdd_A_A_A_add") (ref "__Dict_Add_I64")
        (app3 (ref "HMul_A_A_A_mul") (ref "__Dict_Mul_I64") (int_lit 4) (int_lit 2))
        (int_lit 1)

// ─── native fold semantics ───────────────────────────────────────────

/// A zero divisor yields 0, matching the interpreter and the runtime. This is a
/// real convention, not a defensive default: `int_div_width`
/// (`rust/core/src/core_native.rs`) returns 0 for every width.
#[test]
def test_native_fold_div_by_zero_is_zero : Bool :=
    match fold_native_binop "i64_div" 7 0 {
        Option.some v => I64.beq v 0,
        Option.none => false,
    }

#[test]
def test_native_fold_rem_by_zero_is_zero : Bool :=
    match fold_native_binop "i64_rem" 7 0 {
        Option.some v => I64.beq v 0,
        Option.none => false,
    }

/// Subtraction folds as subtraction. With the two tests above this pins that
/// the operation is selected by NAME, not positionally.
#[test]
def test_native_fold_subtracts : Bool :=
    match fold_native_binop "i64_sub" 10 3 {
        Option.some v => I64.beq v 7,
        Option.none => false,
    }

/// An unknown native is not folded -- the control for the whole table. A
/// catch-all `Option.some` would make every operation look foldable.
#[test]
def test_native_fold_refuses_an_unknown_op : Bool :=
    is_none_opt (fold_native_binop "f64_sqrt" 4 2)

// ─── inlining ────────────────────────────────────────────────────────

/// A helper call is unfolded: the reference is replaced by the helper's body.
#[test]
def test_inline_replaces_a_helper_reference : Bool :=
    let defs : HashMap String Term := table_of [mk_def "helper" (int_lit 3)]
    in
    match int_literal_of (inline_term defs 10 (ref "helper")) {
        Option.some v => I64.beq v 3,
        Option.none => false,
    }

/// A helper nested under an application is inlined too -- the walk is over the
/// whole term, not only its head. This is what a shallow inliner would miss.
#[test]
def test_inline_reaches_a_nested_helper : Bool :=
    let defs : HashMap String Term := table_of [mk_def "helper" (int_lit 3)]
    in
    match term_peel (inline_term defs 10 (app (ref "f") (ref "helper"))) {
        Term.app _f a => match int_literal_of a {
            Option.some v => I64.beq v 3,
            Option.none => false,
        },
        _ => false,
    }

/// The inliner's control: a reference that names no def is left alone, so a
/// native and a kernel's own parameter both survive.
#[test]
def test_inline_leaves_an_unknown_reference_alone : Bool :=
    let defs : HashMap String Term := table_of [mk_def "helper" (int_lit 3)]
    in
    String.beq (var_text (inline_term defs 10 (ref "n"))) "n"

/// The budget stops the inliner rather than letting it loop, and the leftover
/// is REPORTED -- this is what makes the bound honest instead of silent.
#[test]
def test_inline_budget_leaves_a_reference_and_reports_it : Bool :=
    let defs : HashMap String Term := table_of [mk_def "a" (ref "b"), mk_def "b" (ref "a")]
    in
    Bool.not (List.is_empty (unresolved_refs_of (inline_term defs 2 (ref "a")) defs))

/// A fully inlined body has nothing unresolved, which is the control for the
/// test above.
#[test]
def test_inline_complete_has_no_unresolved_refs : Bool :=
    let defs : HashMap String Term := table_of [mk_def "helper" (int_lit 3)]
    in
    List.is_empty (unresolved_refs_of (inline_term defs 10 (ref "helper")) defs)

// ─── call-site discovery ─────────────────────────────────────────────

/// A kernel called from ordinary host code is FOUND. This is the reason the
/// sixth rule's input is a decl list rather than a `Def` -- the call site is
/// not in the kernel.
#[test]
def test_call_sites_are_found_in_host_code : Bool :=
    let sites : List KernelCallSite :=
        call_sites_of [Decl.def_d (mk_def "main" (app (ref "saxpy") (ref "b")))] ["saxpy"]
    in
    List.length sites == 1 && String.beq (hd_callee sites) "saxpy"

/// The control: a call to something that is NOT a kernel is not a call site, so
/// the rule does not fire on ordinary code.
#[test]
def test_call_sites_ignore_non_kernels : Bool :=
    List.is_empty (call_sites_of [Decl.def_d (mk_def "main" (app (ref "println") (ref "s")))] ["saxpy"])

/// The arguments come out in WRITTEN order, which is what makes the position in
/// the `dim` message mean anything. `saxpy dst 16` must report `[dst, 16]`, not
/// the reverse -- the spine walk builds tail-first and reverses.
#[test]
def test_call_site_arguments_are_in_written_order : Bool :=
    let args : List Term := spine_args_of (app2 (ref "saxpy") (ref "dst") (int_lit 16))
    in
    List.length args == 2
        && String.beq (var_text (nth_or_hole args 0)) "dst"
        && match int_literal_of (nth_or_hole args 1) {
            Option.some v => I64.beq v 16,
            Option.none => false,
        }

/// End to end through the rule: the call site's SECOND argument is the
/// dimension and it is a literal, so a kernel called as `saxpy dst 16` is
/// silent -- and the same call with a variable dimension fires.
#[test]
def test_call_site_dimension_is_checked_at_the_call : Bool :=
    let variable : List KernelCallSite :=
        call_sites_of [Decl.def_d (mk_def "main" (app2 (ref "saxpy") (ref "dst") (ref "n")))] ["saxpy"]
    in
    let literal : List KernelCallSite :=
        call_sites_of [Decl.def_d (mk_def "main" (app2 (ref "saxpy") (ref "dst") (int_lit 16)))] ["saxpy"]
    in
    List.length (dim_diagnostics_for_sites variable [1]) == 1
        && List.is_empty (dim_diagnostics_for_sites literal [1])

// ─── extract_kernel ──────────────────────────────────────────────────

/// A clean kernel extracts with no diagnostics, its own parameters, and a body
/// that no longer references its helper.
#[test]
def test_extract_kernel_inlines_and_reports_nothing : Bool :=
    let helper : Decl := Decl.def_d (mk_def "helper" (int_lit 3))
    in
    let kernel : Decl := Decl.def_d (mk_kernel "k" (Term.pi (binder_named (Identifier.id "n")) i64_ty i64_ty) (ref "helper"))
    in
    let k : KernelExtract := extract_kernel (the_kernel [kernel]) [kernel, helper] List.empty []
    in
    KernelExtract.ready k
        && List.length k.params == 1
        && match int_literal_of k.body {
            Option.some v => I64.beq v 3,
            Option.none => false,
        }

/// A kernel whose helper cannot be fully unfolded reports an `inline` finding
/// rather than emitting a body with a live reference to a top-level def.
///
/// The fixture is a mutually recursive PAIR, which is the case that actually
/// reaches the budget: `a` unfolds to `b` unfolds to `a`, so no number of
/// unfoldings settles it and the inliner stops with a reference still in the
/// body. A single reference to an unknown name would NOT do -- an unknown name
/// is not a def, so it is legitimately left alone (see
/// `test_inline_leaves_an_unknown_reference_alone`) and reporting it would be a
/// false positive.
#[test]
def test_extract_kernel_reports_an_unresolved_reference : Bool :=
    let a : Decl := Decl.def_d (mk_def "a" (ref "b"))
    in
    let b : Decl := Decl.def_d (mk_def "b" (ref "a"))
    in
    let kernel : Decl := Decl.def_d (mk_kernel "k" i64_ty (ref "a"))
    in
    Bool.not (KernelExtract.ready (extract_kernel (the_kernel [kernel]) [kernel, a, b] List.empty []))

// ─── small helpers, kept last so the tests above read ────────────────

/// The name of a `Term.var`, `""` for anything else.
#[partial]
def var_text (t : Term) : String := match term_peel t {
    Term.var _idx dbg => debug_text dbg,
    _ => "",
}

#[partial]
def debug_text (dbg : DebugName) : String := match dbg {
    DebugName.named id => id_text id,
    DebugName.unnamed => "_",
}

#[partial]
def hd_rule (ds : List KernelDiagnostic) : String := match ds {
    List.empty => "",
    List.cons d _ => d.rule,
}

#[partial]
def hd_callee (sites : List KernelCallSite) : String := match sites {
    List.empty => "",
    List.cons s _ => s.callee,
}

#[partial]
def is_none_opt {A : Type} (o : Option A) : Bool := match o {
    Option.some _ => false,
    Option.none => true,
}

#[partial]
def nth_or_hole (xs : List Term) (i : I64) : Term := match xs {
    List.empty => Term.hole,
    List.cons x rest => if I64.beq i 0 then x else nth_or_hole rest (i - 1),
}

/// The first kernel in a decl list -- `extract_kernels`' own discovery, so the
/// fixture and the extractor agree on what a kernel is.
#[partial]
def the_kernel (decls : List Decl) : Def := match extract_kernels decls {
    List.empty => mk_def "" Term.hole,
    List.cons d _ => d,
}
