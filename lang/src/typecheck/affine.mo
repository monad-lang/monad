/// The affine-by-default usage rule — Milestone 2 of the
/// affine-by-default experiment (*Design B: Viability
/// Experiment*).
///
/// [[lang/typecheck/usage.mo]] counts uses; [[lang/typecheck/copy_class.mo]]
/// decides whether a type may be shared. This module is the judgement
/// that combines them, and it is the first thing in the experiment that
/// says a program is *wrong*.
///
/// ## The rule
///
/// Design B's effective multiplicity, verbatim:
///
/// ```text
/// 1   if annotated `!x`, or the type is #[linear]
/// 0   if annotated `%x`
/// ω   if `Copy A` resolves            // the only route to ω
/// ≤1  otherwise                        // the default
/// ```
///
/// **`Multiplicity.many` is the parser's default for an UNANNOTATED
/// binder, and under this rule that means affine, not ω.** Reading it
/// as ω would silently pass every program and disable the whole check
/// while still looking like it worked — the same shape of blind-
/// classifier bug that once made the borrow measurement report 99.9%
/// borrowable. `test_unannotated_is_affine_not_many` exists to keep it
/// from coming back.
///
/// ## Warnings, not errors — and why they are still `TypeError`
///
/// Nothing here rejects a program. The corpus has 2,394 binders this
/// would fire on, so enforcement has to arrive per-mote as each one
/// reaches zero, and until then these are advisory.
///
/// They are nonetheless `TypeError` values (`lang/types.mo`), not a
/// separate warning type. Warn-versus-error is properly the *driver's*
/// decision — whether a diagnostic fails the build — and keeping these
/// in the existing error type means promotion is a caller-side switch
/// rather than a second diagnostic pipeline to build and then retire.
/// The cost was checked before committing to it: exactly one site
/// (`lang/typecheck/diagnostic.mo`) matches `TypeError` exhaustively.
///
/// ## Which diagnostic, and why three
///
/// The three cases have genuinely different remedies, and the
/// measurement in `bench/src/affine_report.mo` already separates them,
/// so the diagnostic names the fix instead of just reporting a count:
///
/// - **`copy_required`** — used more than once, but at most one of
///   those uses takes ownership. A borrow serves it, or a `Copy`
///   instance does. This is the large, tractable bucket (2,447 in the
///   compiler's own closure).
/// - **`value_used_after_move`** — two or more OWNING uses: the value
///   really is moved twice. No borrow discipline rescues it; it needs
///   `Copy`, `Clone`, or a rewrite. The irreducible bucket (187).
/// - **`linear_unused`** — a `!x` never used. The one case affine's
///   weakening does not excuse, since linear means *exactly* once.
///
/// An erased `%x` used in runtime position reports through
/// `TypeError.custom`: it is real but has no corpus instances at all
/// (the whole corpus carries zero multiplicity annotations), so it does
/// not earn a fourth variant yet.
use lib::types {DebugName, Def, Identifier, ModulePath, Multiplicity, Scope, Term, TypeError, binder_named, show_identifier}
use lib::scope {scope_data_empty}
use lib::typecheck::usage {BinderKind, BinderUse, attribute_binder_types, collect_binder_uses}
use lib::typecheck::copy_class {is_copy}
use std::map {HashMap}
use llvm::strmap {str_map_empty, str_map_insert}

// ─── The rule ──────────────────────────────────────────────────────

/// Design B's effective multiplicity for one binder.
///
/// `declared` is what the source wrote. The corpus writes nothing
/// today — every binder arrives as `Multiplicity.many`, the parser's
/// default — so in practice this function's job is to turn "unannotated"
/// into "affine unless Copy". It takes `declared` anyway so the rule is
/// complete and testable now, ahead of the plumbing that will carry a
/// real `!`/`%` through lowering (which needs the `Def.attrs` carrier
/// described in the plan, since `Term.lam` has nowhere to put one).
pub def effective_mult (scope : Scope) (declared : Multiplicity) (typ : Term) : Multiplicity :=
    match declared {
        // Explicit annotations are strict: Design B says they are never
        // rescued by Copy. `!Qubit` stays linear even if someone writes
        // an instance for it.
        Multiplicity.linear => Multiplicity.linear,
        Multiplicity.zero => Multiplicity.zero,
        Multiplicity.affine => Multiplicity.affine,
        // The unannotated case. NOT ω -- see this file's header.
        Multiplicity.many =>
            if is_copy scope typ then Multiplicity.many else Multiplicity.affine,
    }

/// Does this effective multiplicity permit unrestricted use?
pub def permits_sharing (m : Multiplicity) : Bool :=
    match m {
        Multiplicity.many => true,
        Multiplicity.linear => false,
        Multiplicity.affine => false,
        Multiplicity.zero => false,
    }

// ─── Checking one binder ───────────────────────────────────────────

/// The diagnostic this binder earns, if any.
///
/// `declared` is threaded in rather than read off `BinderUse`, which
/// carries no multiplicity: annotations die at `pt_lam`
/// (`lang/src/parser.mo`) and the corpus writes none. Every caller
/// passes `Multiplicity.many` today.
///
/// The over-use gates compare the BORROW-AWARE budget `count -
/// borrowed`, not the raw count: `f (Borrow.of x); g (Borrow.of x)`
/// mentions `x` twice but consumes it zero times, and gating on the raw
/// count there was the false positive B1 existed to remove. `borrowed`
/// is computed per-branch consistently (`usage.mo`'s `BinderUse`
/// doc comment says why a separately-maxed count would under-count),
/// so the budget is exact across match arms too.
pub def check_binder (scope : Scope) (declared : Multiplicity) (u : BinderUse) : Option TypeError :=
    let typ : Term := BinderUse.typ u in
    let uses : I64 := BinderUse.count u in
    let borrowed : I64 := BinderUse.borrowed u in
    let budget : I64 := uses - borrowed in
    let owning : I64 := BinderUse.owning u in
    let name : Identifier := BinderUse.name u in
    match effective_mult scope declared typ {
        // Unrestricted: nothing to check.
        Multiplicity.many => Option.none,
        // Exactly once.
        Multiplicity.linear =>
            if I64.beq budget 0 then Option.some (TypeError.linear_unused name typ)
            else if I64.gt budget 1 then Option.some (over_use_error name typ budget owning)
            else Option.none,
        // At most once. Zero uses is fine -- weakening is admissible,
        // and that binder becomes a release at scope exit under M3.
        Multiplicity.affine =>
            if I64.gt budget 1 then Option.some (over_use_error name typ budget owning)
            else Option.none,
        // Erased: must not appear in runtime position at all. A borrow
        // still names the binder at run time, so this one counts RAW
        // uses -- there is no budget to spend.
        Multiplicity.zero =>
            if I64.gt uses 0 then
                Option.some (TypeError.custom
                    (String.concat "erased `" (String.concat (show_identifier name)
                        "` is used at run time")))
            else Option.none,
    }

/// Split an over-use by whether a borrow could fix it. This is the
/// distinction `usage.mo`'s `owning_uses` exists to draw: one owning
/// use plus any number of reads is borrow-shaped; two owning uses is
/// not. `budget` is the borrow-aware use count, so the diagnostic
/// reports what the fix has to cover, not how often the name happens
/// to appear.
def over_use_error (name : Identifier) (typ : Term) (budget : I64) (owning : I64) : TypeError :=
    if I64.gt owning 1 then TypeError.value_used_after_move name typ owning
    else TypeError.copy_required name typ budget

// ─── Checking a definition ─────────────────────────────────────────

/// Every affine diagnostic a def's body earns.
///
/// Takes the constructor-name set and the borrow-name set rather than
/// deriving them, because building either is a scan of every inductive
/// in scope and a caller checking many defs must build them once.
/// `ctor_name_set`/`borrow_of_name_set` (`lang/typecheck/usage.mo`) are
/// the builders.
#[partial]
pub def check_def (scope : Scope) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (d : Def) : List TypeError :=
    let raw : List BinderUse := collect_binder_uses ctors borrows (def_body d) in
    let attributed : List BinderUse := attribute_binder_types scope raw in
    List.reverse (check_binders_go scope attributed List.empty)

def def_body (d : Def) : Term := d.term

#[partial]
def check_binders_go (scope : Scope) (us : List BinderUse) (acc : List TypeError) : List TypeError :=
    match us {
        List.empty => acc,
        List.cons u rest =>
            // Every binder is unannotated in today's corpus; see
            // `check_binder`.
            match check_binder scope Multiplicity.many u {
                Option.some e => check_binders_go scope rest (List.cons e acc),
                Option.none => check_binders_go scope rest acc,
            },
    }

// ─── Tests ─────────────────────────────────────────────────────────
//
// An empty scope resolves no `Copy` instance, so every carrier is
// affine there. That is exactly the setting these need: the rule's
// behaviour is what is under test, not instance resolution, which
// `bench/src/affine_report.mo` exercises against the real corpus.

def probe_scope : Scope :=
    { module_id := ModulePath.mp (List.cons (Identifier.id "probe") List.empty),
      scope := scope_data_empty,
      parent := Option.none,
      incomplete_match_ok := false }

def a_type : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "Term"))

/// A binder with the given use and owning counts.
def binder (uses : I64) (owning : I64) : BinderUse :=
    { name := Identifier.id "x", kind := BinderKind.bk_lam, typ := a_type,
      count := uses, owning := owning, ctor := Identifier.id "", pos := 0 - 1 }

/// A binder whose uses split between real and borrowed.
def borrowable (uses : I64) (borrowed : I64) (owning : I64) : BinderUse :=
    { name := Identifier.id "x", kind := BinderKind.bk_lam, typ := a_type,
      count := uses, borrowed := borrowed, owning := owning,
      ctor := Identifier.id "", pos := 0 - 1 }

#[test]
def test_unannotated_is_affine_not_many : Bool :=
    // THE test for this module. `Multiplicity.many` is the parser's
    // "no annotation was written", and reading it as ω would pass
    // every program while looking like a working check.
    match effective_mult probe_scope Multiplicity.many a_type {
        Multiplicity.affine => true,
        _ => false,
    }

#[test]
def test_an_explicit_linear_is_never_rescued_by_copy : Bool :=
    // Design B: `!` and `%` are strict, never widened by a Copy
    // instance. Checked against a scope with none anyway, but the rule
    // must not even consult it.
    match effective_mult probe_scope Multiplicity.linear a_type {
        Multiplicity.linear => true,
        _ => false,
    }

#[test]
def test_affine_allows_zero_uses : Bool :=
    // Weakening is admissible: a dropped binder is legal, and becomes
    // a release at scope exit under Milestone 3.
    match check_binder probe_scope Multiplicity.many (binder 0 0) {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_affine_allows_one_use : Bool :=
    match check_binder probe_scope Multiplicity.many (binder 1 1) {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_two_uses_one_owning_asks_for_a_borrow_or_copy : Bool :=
    // Read plus move: borrow-shaped, so the remedy is Copy or a borrow.
    match check_binder probe_scope Multiplicity.many (binder 2 1) {
        Option.some e =>
            match e {
                TypeError.copy_required _n _t uses => I64.beq uses 2,
                _ => false,
            },
        Option.none => false,
    }

#[test]
def test_two_owning_uses_is_a_move_twice : Bool :=
    // Stored twice. No borrow fixes this one, and the diagnostic says
    // so rather than suggesting one.
    match check_binder probe_scope Multiplicity.many (binder 2 2) {
        Option.some e =>
            match e {
                TypeError.value_used_after_move _n _t owning => I64.beq owning 2,
                _ => false,
            },
        Option.none => false,
    }

#[test]
def test_linear_unused_is_an_error : Bool :=
    // The one case affine's weakening does not excuse.
    match check_binder probe_scope Multiplicity.linear (binder 0 0) {
        Option.some e =>
            match e {
                TypeError.linear_unused _n _t => true,
                _ => false,
            },
        Option.none => false,
    }

#[test]
def test_linear_used_once_is_fine : Bool :=
    match check_binder probe_scope Multiplicity.linear (binder 1 1) {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_erased_used_at_runtime_is_an_error : Bool :=
    match check_binder probe_scope Multiplicity.zero (binder 1 1) {
        Option.some e =>
            match e {
                TypeError.custom _msg => true,
                _ => false,
            },
        Option.none => false,
    }

#[test]
def test_erased_unused_is_fine : Bool :=
    match check_binder probe_scope Multiplicity.zero (binder 0 0) {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_sharing_is_permitted_only_by_many : Bool :=
    permits_sharing Multiplicity.many
        && not (permits_sharing Multiplicity.affine)
        && not (permits_sharing Multiplicity.linear)
        && not (permits_sharing Multiplicity.zero)

// ─── Tests: the borrow-aware budget ─────────────────────────────────

/// `Borrow.of <arg>` as an elaborated application: head var `of`, the
/// spelling `usage.mo`'s `head_is_borrow_of` checks first.
def borrow_of (arg : Term) : Term :=
    Term.app (Term.var (0 - 1) (DebugName.named (Identifier.id "of"))) arg

/// The borrow set a scope where `Borrow` really is the sole inductive
/// declaring `of` resolves to. Hand-built here; `borrow_of_name_set`
/// end-to-end is `usage.mo`'s own test territory.
def probe_borrows : HashMap String Bool :=
    str_map_insert "of" true (str_map_insert "Borrow.of" true str_map_empty)

#[test]
def test_a_borrowed_use_does_not_spend_the_budget : Bool :=
    // One real use, one borrow: `f (Borrow.of x); P x`. Budget 1, so
    // no diagnostic where the raw count of 2 used to fire one.
    match check_binder probe_scope Multiplicity.many (borrowable 2 1 0) {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_two_borrows_are_not_an_over_use : Bool :=
    // `f (Borrow.of x); g (Borrow.of x)` — the exact case from the plan
    // doc's B1 gap, exercised end-to-end through collection rather
    // than a hand-built `BinderUse`: two uses, both direct borrow
    // arguments, budget zero, clean pass.
    let f : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "f")) in
    let g : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "g")) in
    let x : Term := Term.var 0 (DebugName.named (Identifier.id "x")) in
    let body : Term := Term.app (Term.app f (borrow_of x)) (Term.app g (borrow_of x)) in
    let lam : Term := Term.lam (binder_named (Identifier.id "x")) Term.hole body in
    match collect_binder_uses str_map_empty probe_borrows lam {
        List.cons u _rest =>
            I64.beq (BinderUse.count u) 2
                && I64.beq (BinderUse.borrowed u) 2
                && (match check_binder probe_scope Multiplicity.many u {
                        Option.none => true,
                        Option.some _ => false,
                    }),
        List.empty => false,
    }

#[test]
def test_a_borrow_does_not_hide_a_real_over_use : Bool :=
    // `f (Borrow.of x); P x x` — one borrow, two real stores. The
    // borrow buys nothing here; budget 2 is still an over-use, and one
    // the diagnostic must not under-report.
    match check_binder probe_scope Multiplicity.many (borrowable 3 1 2) {
        Option.some e =>
            match e {
                TypeError.value_used_after_move _n _t owning => I64.beq owning 2,
                _ => false,
            },
        Option.none => false,
    }

#[test]
def test_a_linear_binder_only_ever_borrowed_is_unused : Bool :=
    // Linear means consumed EXACTLY once, and a borrow does not
    // consume. Only ever borrowed is never consumed — the weakening
    // affine allows is exactly what linear forbids.
    match check_binder probe_scope Multiplicity.linear (borrowable 2 2 0) {
        Option.some e =>
            match e {
                TypeError.linear_unused _n _t => true,
                _ => false,
            },
        Option.none => false,
    }

#[test]
def test_a_borrow_still_cannot_name_an_erased_binder : Bool :=
    // `Borrow.of x` still mentions `x` at run time, so the erased
    // multiplicity counts RAW uses. There is no budget to spend.
    match check_binder probe_scope Multiplicity.zero (borrowable 1 1 0) {
        Option.some e =>
            match e {
                TypeError.custom _msg => true,
                _ => false,
            },
        Option.none => false,
    }
