/// `Borrow A` — a type-level marker that a value is being read, not
/// owned. B1 of the borrow design (*Design B: Viability Experiment* /
/// M2.5): B0 moved `Copy` here, B1 is this file, B2 the escape rule,
/// B3 gradual conversion.
///
/// ## What "Option 1" means here
///
/// Three readings of "a normal type constructor with a Copy instance"
/// were on the table; this file implements the smallest one,
/// deliberately, to isolate the measurement before committing to more:
/// **caller-side only.** `Borrow.of x` marks a value as read rather
/// than moved at the CALL site, so the same `x` can be handed to
/// several borrowing functions without tripping the affine rule
/// (`lang/typecheck/affine.mo`). What a borrowing function does with
/// the borrow once it has it — whether it may store the underlying
/// value, whether pattern matching should work through the wrapper
/// directly — is NOT addressed here. Two options were set aside:
///
/// - `Borrow.get` plus a zero-owning-use escape check on the unwrapped
///   binder (would need `lang/typecheck/affine.mo`'s `check_binder`
///   extended with a new binder provenance for "came from Borrow.get").
/// - `match` working through a `Borrow` directly, yielding borrowed
///   fields (match ergonomics) — a real type-system feature, not a
///   newtype.
///
/// Both stay open; this file's job is to prove the smallest version
/// moves the number before either is built.
///
/// ## Representation
///
/// Exactly one constructor, exactly one field — the shape a
/// `#[transparent]`-style erasure (M2.5's own risk-flagged step) would
/// target. Nothing in THIS file erases it, and this is MEASURED, not
/// predicted: a compiled probe's emitted IR shows `Borrow.of` lowering
/// to `monad_ctor_Borrow_of`, which calls `alloc_constructor(tag, 1)` —
/// a real boxed `Constructor` with a header, exactly as
/// `alloc_constructor` (`runtime/src/runtime.c`) caching only nullary
/// constructors predicted it would. `lang/src/scope.mo`'s
/// `last_colon_colon` is converted to take `Borrow String` despite
/// this — deliberately, per the decision recorded in the experiment log:
/// the counting win is
/// real and measured (`bench/src/affine_report.mo`), and the allocation
/// cost is provably ONE PER CALL, not one per character scanned —
/// `last_colon_colon` is self-recursive and threads the same `Borrow`
/// value through every recursive step unchanged, so only its single
/// external caller's one `Borrow.of` wrap ever allocates. (The first
/// candidate tried, `alias_map_insert`, was reverted: a corpus-wide grep
/// found two more callers in `lang/codegen/qualify.mo`'s hot
/// per-declared-name pass — ~3,172 names — which is exactly the danger
/// this file's own header warns an unerased `Borrow` risks, and
/// converting it there would have paid that cost for real, not just in
/// the static count.) Erasure is deliberately left as its own future
/// step rather than attempted under this one's time pressure — it means
/// teaching `lang/src/codegen/emit.mo`, the central codegen file with
/// real miscompile history from careless changes, to special-case this
/// constructor as the identity, which deserves its own verification
/// pass (an IR diff before/after), not a rushed addition here.
use init::copy {Copy}

type Borrow A {
    of (value : A)
}

/// Project the borrowed value back out. Deliberately UNRESTRICTED for
/// now — nothing stops the result from being stored, which is unsound
/// in general. That enforcement is exactly what was deferred above
/// (the second option's escape check); B1 is measurement, not
/// enforcement, and nothing in this experiment rejects a program yet.
pub def Borrow.get (b : Borrow A) : A :=
    match b { of v => v }

/// `Borrow A` is `Copy` REGARDLESS of `A` — duplicating a borrow copies
/// the marker, not the value underneath, which is why this instance
/// carries no `[Copy A]` constraint. An UNCONDITIONAL parametric
/// instance needed a real fix to `lang/typecheck/copy_class.mo`'s
/// instance-admission rule to resolve at all — see that file's
/// `instance_unconditionally_copy`, and `bench/src/affine_report.mo`
/// for the measurement this instance existing was meant to produce.
instance {A : Type} Copy (Borrow A) {
    def copy (b : Borrow A) : Pair (Borrow A) (Borrow A) := Pair.pair b b
}

#[test]
def test_borrow_get_roundtrips : Bool :=
    I64.beq (Borrow.get (Borrow.of 7)) 7

#[test]
def test_borrow_of_a_string_roundtrips : Bool :=
    String.beq (Borrow.get (Borrow.of "hi")) "hi"

#[test]
def test_copy_borrow_duplicates_the_marker : Bool :=
    let b : Borrow I64 := Borrow.of 9 in
    match Copy.copy b {
        Pair.pair b1 b2 => I64.beq (Borrow.get b1) 9 && I64.beq (Borrow.get b2) 9,
    }
