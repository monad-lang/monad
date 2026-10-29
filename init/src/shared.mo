/// `Shared A` — a shareable, read-only handle. It is a plain type
/// constructor, not reference syntax: **the type is the mode**
/// (*Design B*, `plans/type-system/quantitative-types.md`). There is no
/// `&` spelling and none is planned.
///
/// ## What it is
///
/// `Shared.of x` marks a value as *read*, not moved, at the call site: the
/// same `x` can be handed to several shared-taking functions without
/// tripping the affine rule (`lang/src/typecheck/affine.mo`). Inside the
/// callee, `Shared.get b` yields a **borrowed view** of the payload: it may
/// be read, matched, used as a callee or passed to another `Shared`
/// parameter, and it may be re-wrapped by `Shared.of`; it may not be stored
/// into a constructor, returned from its def, or passed to an owning
/// parameter (`borrowed_value_escapes`). A view never moves the payload out,
/// so a `Shared` handle carries no ownership.
///
/// ## Representation
///
/// Exactly one constructor, exactly one field — the shape a transparent
/// erasure would target (`plans/bootstrapping/ownership-regions-memory.md`
/// O2). Nothing erases it yet: a compiled probe's emitted IR shows
/// `Shared.of` lowering to `monad_ctor_Shared_of`, which calls
/// `alloc_constructor(tag, 1)` — a real boxed `Constructor`. Callers keep the
/// cost to one allocation per call (`lang/src/scope.mo`'s
/// `last_colon_colon` threads the same handle through its self-recursion),
/// and erasure is O2's work.
///
/// ## Lifetime
///
/// `Shared.of` does not move its argument, so a handle does not own the
/// payload and must not outlive it. The type system does not yet state that
/// (memory-safety hazard R1 of the current plan); until regions land (O5), a
/// handle must stay within the borrow's dynamic extent.
///
/// `Copy (Shared A)` is unconditional — the handle, not the payload, is what
/// may be duplicated.
///
/// `#[shared]` is the marker the affine checker keys on
/// (`lang/src/typecheck/usage.mo`'s `shared_name_set`). Renaming the type
/// cannot silently disable borrow-aware counting, because the marker travels
/// with the declaration rather than with any literal spelling.
use init::copy {Copy}

#[shared]
pub type Shared A {
    of (value : A)
}

/// Project the borrowed payload out as a **view**. See this file's header:
/// the result may be read or passed on as a view, never stored or returned.
pub def Shared.get (b : Shared A) : A :=
    match b { of v => v }

/// `Shared A` is `Copy` REGARDLESS of `A` — duplicating a handle copies the
/// marker, not the payload, which is why this instance carries no
/// `[Copy A]` constraint. An UNCONDITIONAL parametric instance needed a real
/// fix to `lang/typecheck/copy_class.mo`'s instance-admission rule to resolve
/// at all — see that file's `instance_unconditionally_copy`.
pub instance {A : Type} Copy (Shared A) {
    def copy (b : Shared A) : Pair (Shared A) (Shared A) := Pair.pair b b
}

#[test]
def test_shared_get_roundtrips : Bool :=
    I64.beq (Shared.get (Shared.of 7)) 7

#[test]
def test_shared_of_a_string_roundtrips : Bool :=
    String.beq (Shared.get (Shared.of "hi")) "hi"

#[test]
def test_copy_shared_duplicates_the_handle : Bool :=
    let b : Shared I64 := Shared.of 9 in
    match Copy.copy b {
        Pair.pair b1 b2 => I64.beq (Shared.get b1) 9 && I64.beq (Shared.get b2) 9,
    }
