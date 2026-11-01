/// Safe pointers on quantitative types: `Cell` and its erased `At` proof.
///
/// First milestone of `plans/type-system/view-types.md`. A `Cell A` is an
/// opaque, LINEAR handle that owns one `Copy` payload. It has no
/// constructors and no `Copy`/`Clone` instance, so:
///
/// - duplicating it is untypable (`Copy` has no instance for it);
/// - dropping it is `linear_unused` (`#[linear]` forces every binder of
///   this type to be used exactly once);
/// - its operations take `!c` and return the handle, so a use-after-free
///   or double-free requires two uses of one binder, which the affine
///   rule rejects.
///
/// ## Representation
///
/// One pointer-sized word: a GC-scanned block holding the payload word
/// (`runtime/src/runtime_core.c`'s `CellObj`). The block is scanned, not
/// atomic, because a `Copy` payload can still be a `String` pointer.
/// `Cell.free` POISONS the block (tag + payload cleared) rather than
/// freeing it: under Boehm the block is collector-owned, and a real free
/// arrives with `ownership-regions-memory` O3/O4. A use-after-free
/// therefore fails the handle's tag check instead of corrupting memory.
///
/// ## The proof component
///
/// `At A` is the view-types proof (an ATS `T @ L` without the address
/// index). In v1 it is a phantom: `Cell`'s typing pairs it with the
/// handle, but it is not a source-level field, and proofs have no
/// run-time representation. A proof type is `#[proof]`, so it is forced
/// linear, never `Copy`, and user defs may not bind or return one until
/// the erasure pass lands.
///
/// ## What is deliberately absent
///
/// `Cell.get` returns an ordinary boxed `Pair` in v1 (one allocation per
/// read). The zero-allocation unboxed return is a separate, IR-gated
/// milestone; a boxed v1 first keeps the safety rules and the runtime
/// correct.
use init::copy {Copy}

/// The proof that `A` is live at a location. Opaque and erased: it has no
/// constructors, so no user code can forge one. The only producer is a
/// primitive that allocates or splits a view.
///
/// A type with no constructors is the empty type (`False`); a native that
/// returned one would be asserting an inhabitant of `False`. So an opaque
/// native-backed type declares exactly one nullary WITNESS constructor.
/// `#[opaque]` makes that constructor unreferenceable: it can be neither
/// constructed nor matched, which is what keeps the type abstract. Values
/// come only from the natives.
#[proof]
#[opaque]
pub type At (A : Type) { at_witness }

/// An opaque linear handle owning one `Copy` payload. The nullary witness
/// is the inhabitation proof; `#[opaque]` forbids constructing or matching
/// it (see `At`'s own comment).
#[linear]
#[opaque]
pub type Cell (A : Type) { cell_witness }

// ── Natives ─────────────────────────────────────────────────────────
//
// All four are side-effecting and therefore `RawIO`; the public wrappers
// add `IO.mk`. `view_get` returns a `Pair` built in C with the builtin
// `pair` tag (15): a handle plus its payload must travel as one value, or
// the wrapper would have to use `c` twice.

#[native view_new]
priv def view_new_raw [Copy A] (a : A) : RawIO (Cell A)

#[native view_get]
priv def view_get_raw [Copy A] (!c : Cell A) : RawIO (Pair A (Cell A))

#[native view_set]
priv def view_set_raw [Copy A] (!c : Cell A) (a : A) : RawIO (Cell A)

#[native view_free]
priv def view_free_raw [Copy A] (!c : Cell A) : RawIO Unit

// ── The user-facing operations ──────────────────────────────────────

/// Allocate a cell holding `a`.
pub def Cell.new [Copy A] (a : A) : IO (Cell A) :=
    IO.mk (view_new_raw a)

/// Read the payload, returning it with the same handle. Consumes and
/// returns the handle (view-types P2): the old handle is unusable after
/// the call.
pub def Cell.get [Copy A] (!c : Cell A) : IO (Pair A (Cell A)) :=
    IO.mk (view_get_raw c)

/// Overwrite the payload, leaving the cell intact.
pub def Cell.set [Copy A] (!c : Cell A) (a : A) : IO (Cell A) :=
    IO.mk (view_set_raw c a)

/// Consume the cell and release its storage. In v1 this poisons the block
/// (the collector owns it; see this file's header).
pub def Cell.free [Copy A] (!c : Cell A) : IO Unit :=
    IO.mk (view_free_raw c)
