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
use lib::types {DebugName, Def, Identifier, ModulePath, Multiplicity, Scope, Term, TypeConstraint, TypeError, binder_named, id_member, show_identifier}
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
    effective_mult_with_vars scope List.empty declared typ

/// The rule with the enclosing def's `[Copy A]` constraints in hand.
///
/// `copy_vars` is the type-variable half of the Copy gate. `Copy`'s own
/// instance registry cannot answer for a bare variable -- the carrier is
/// not a type constructor, and `copy_class.mo` deliberately fails closed
/// there. Under Design B a generic def that shares a parameter must
/// therefore SAY it may (`[Copy A]`), and this list is where that
/// permission lands.
pub def effective_mult_with_vars (scope : Scope) (copy_vars : List Identifier) (declared : Multiplicity) (typ : Term) : Multiplicity :=
    match declared {
        // Explicit annotations are strict: Design B says they are never
        // rescued by Copy. `!Qubit` stays linear even if someone writes
        // an instance for it.
        Multiplicity.linear => Multiplicity.linear,
        Multiplicity.zero => Multiplicity.zero,
        Multiplicity.affine => Multiplicity.affine,
        // The unannotated case. NOT ω -- see this file's header.
        Multiplicity.many =>
            if is_copy scope typ then Multiplicity.many
            else if type_var_is_copy copy_vars typ then Multiplicity.many
            else Multiplicity.affine,
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
    check_binder_with scope List.empty false declared u

/// The checking variant used by the always-on rule: `copy_vars` is the
/// def's `[Copy A]` permission list, and `strict` selects fail-closed
/// (the report's measurement) over fail-open (enforcement).
///
/// **Fail-open, and why the direction flips here.** The report must never
/// flatter the design, so an unattributable binder counts as affine
/// there. Enforcement is the opposite question: rejecting a program the
/// analysis cannot type is a false positive, and a false positive is
/// worse than a missed one while nothing frees memory yet. So a binder
/// whose type is still `Term.hole` -- an unannotated lambda, or a match
/// binder whose constructor is corpus-ambiguous -- is left alone. The
/// report keeps calling `check_def_strict`, so its numbers stay an upper
/// bound.
pub def check_binder_with (scope : Scope) (copy_vars : List Identifier) (strict : Bool) (declared : Multiplicity) (u : BinderUse) : Option TypeError :=
    let typ : Term := BinderUse.typ u in
    let uses : I64 := BinderUse.count u in
    let borrowed : I64 := BinderUse.borrowed u in
    let budget : I64 := uses - borrowed in
    let owning : I64 := BinderUse.owning u in
    let name : Identifier := BinderUse.name u in
    if Bool.not strict
       && is_unannotated declared
       && Bool.not (typ_is_attributable typ)
    then Option.none
    else
    match effective_mult_with_vars scope copy_vars declared typ {
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

/// Did the source omit a multiplicity? `Multiplicity.many` is the
/// parser's spelling for "none written", not an explicit ω.
def is_unannotated (declared : Multiplicity) : Bool :=
    match declared {
        Multiplicity.many => true,
        _ => false,
    }

/// Can this binder's type be named at all? A hole (an unannotated
/// lambda, or an unresolved match field) or an unnamed de-Bruijn
/// variable carries no answer, and enforcement treats "no answer" as
/// "not our question" rather than as affine. A NAMED type variable is
/// attributable: affine is the correct answer for it unless the def
/// carries `[Copy A]`.
pub def typ_is_attributable (t : Term) : Bool :=
    match t {
        Term.hole => false,
        Term.var _ dbg =>
            match dbg {
                DebugName.named _id => true,
                DebugName.unnamed => false,
            },
        Term.ctx _loc inner => typ_is_attributable inner,
        _ => true,
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

/// Every affine diagnostic a def's body earns, as enforcement sees it:
/// binders the syntax-based attribution cannot type are left alone
/// (`check_binder_with`'s own doc says why the direction flips).
///
/// Takes the constructor-name set and the borrow-name set rather than
/// deriving them, because building either is a scan of every inductive
/// in scope and a caller checking many defs must build them once.
/// `ctor_name_set`/`borrow_of_name_set` (`lang/typecheck/usage.mo`) are
/// the builders.
#[partial]
pub def check_def (scope : Scope) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (d : Def) : List TypeError :=
    check_def_with scope ctors borrows false d

/// The report's variant: fail-closed on an unattributable binder, so the
/// migration cost stays an upper bound. Every number in
/// `bench/src/affine_report.mo` comes from this one.
#[partial]
pub def check_def_strict (scope : Scope) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (d : Def) : List TypeError :=
    check_def_with scope ctors borrows true d

#[partial]
def check_def_with (scope : Scope) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (strict : Bool) (d : Def) : List TypeError :=
    let raw : List BinderUse := collect_binder_uses ctors borrows (def_body d) in
    let attributed : List BinderUse := attribute_binder_types scope raw in
    let copy_vars : List Identifier := copy_vars_of_def d in
    List.reverse (check_binders_go scope copy_vars strict attributed List.empty)

/// The type variables the def's `[Copy A]` constraints license. This is
/// the polymorphic half of the Copy gate: `copy_class.mo` resolves type
/// CONSTRUCTORS through instances, and deliberately fails closed on a
/// bare variable, so a generic def must say which variables it may
/// share. `Def.constraints` has carried them since the class machinery
/// landed; nothing read them for this rule until now.
pub def copy_vars_of_def (d : Def) : List Identifier :=
    copy_vars_of_constraints d.constraints List.empty

#[partial]
def copy_vars_of_constraints (cs : List TypeConstraint) (acc : List Identifier) : List Identifier :=
    match cs {
        List.empty => acc,
        List.cons c rest =>
            if constraint_class_is_copy c then
                copy_vars_of_constraints rest (List.append c.vars acc)
            else copy_vars_of_constraints rest acc,
    }

def constraint_class_is_copy (c : TypeConstraint) : Bool :=
    match c.cls.segments {
        List.cons s rest =>
            String.beq (show_identifier s) "Copy" && List.is_empty rest,
        List.empty => false,
    }

/// Is `typ` a bare type variable named in `copy_vars`?
///
/// Only a BARE variable. `List A` is not Copy merely because `A` is:
/// the list is still a heap chain, and its own Copy instance would have
/// to deep-copy. Peeling stops at the first non-`ctx` constructor, so
/// the applied case correctly answers no.
def type_var_is_copy (copy_vars : List Identifier) (typ : Term) : Bool :=
    match type_var_name typ {
        Option.some id => id_member id copy_vars,
        Option.none => false,
    }

def type_var_name (t : Term) : Option Identifier :=
    match t {
        Term.ctx _loc inner => type_var_name inner,
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => Option.some id,
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

#[partial]
def def_body (d : Def) : Term := d.term

#[partial]
def check_binders_go (scope : Scope) (copy_vars : List Identifier) (strict : Bool) (us : List BinderUse) (acc : List TypeError) : List TypeError :=
    match us {
        List.empty => acc,
        List.cons u rest =>
            // Every binder is unannotated in today's corpus; see
            // `check_binder`.
            match check_binder_with scope copy_vars strict Multiplicity.many u {
                Option.some e => check_binders_go scope copy_vars strict rest (List.cons e acc),
                Option.none => check_binders_go scope copy_vars strict rest acc,
            },
    }

// ─── Tests ─────────────────────────────────────────────────────────
//
// An empty scope resolves no `Copy` instance, so every carrier is
// affine there. That is exactly the setting these need: the rule's
// behaviour is what is under test, not instance resolution, which
// `bench/src/affine_report.mo` exercises against the real corpus.

def probe_scope : Scope :=
    { module_id := ModulePath.mk (List.cons (Identifier.id "probe") List.empty),
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

// ─── `[Copy A]` and the fail-open gate ─────────────────────────────

/// A bare type variable, the shape a generic def's parameter has.
def a_type_var : Term := Term.var 0 (DebugName.named (Identifier.id "A"))

/// A `List A` application -- a heap chain whose head is a type
/// constructor, NOT a bare variable.
def list_of_a : Term :=
    Term.app (Term.var (0 - 1) (DebugName.named (Identifier.id "List"))) a_type_var

def hole_binder (uses : I64) (owning : I64) : BinderUse :=
    { name := Identifier.id "x", kind := BinderKind.bk_lam, typ := Term.hole,
      count := uses, owning := owning }

def var_binder (uses : I64) (owning : I64) : BinderUse :=
    { name := Identifier.id "x", kind := BinderKind.bk_lam, typ := a_type_var,
      count := uses, owning := owning }

#[test]
def test_copy_constrained_var_may_be_shared : Bool :=
    // `def f [Copy A] (x : A) := x + x` must be legal: the constraint
    // is the permission. Without it the same binder is affine.
    match effective_mult_with_vars probe_scope [Identifier.id "A"] Multiplicity.many a_type_var {
        Multiplicity.many => true,
        _ => false,
    }

#[test]
def test_a_copy_constraint_does_not_leak_into_an_applied_type : Bool :=
    // `[Copy A]` says nothing about `List A`: the list is still a heap
    // chain, and sharing it is a deep copy, not a pointer duplicate.
    match effective_mult_with_vars probe_scope [Identifier.id "A"] Multiplicity.many list_of_a {
        Multiplicity.affine => true,
        _ => false,
    }

#[test]
def test_copy_constrained_var_used_twice_passes_the_gate : Bool :=
    match check_binder_with probe_scope [Identifier.id "A"] false Multiplicity.many (var_binder 2 1) {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_unattributable_binder_is_exempt_under_enforcement : Bool :=
    // Enforcement fails OPEN: a binder the syntax-based attribution
    // cannot type is not rejected. See `check_binder_with`.
    match check_binder_with probe_scope List.empty false Multiplicity.many (hole_binder 2 1) {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_unattributable_binder_is_counted_by_the_report : Bool :=
    // The report fails CLOSED, so its migration cost stays an upper
    // bound. Same binder, same hole, opposite answer on purpose.
    match check_binder_with probe_scope List.empty true Multiplicity.many (hole_binder 2 1) {
        Option.some e =>
            match e {
                TypeError.copy_required _n _t _uses => true,
                _ => false,
            },
        Option.none => false,
    }
