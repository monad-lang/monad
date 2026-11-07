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
/// ## The fused do-bind
///
/// The public types are unchanged, so an escaping `Pair` is still an
/// ordinary boxed value -- that path stays the reference semantics (the
/// Rust host interprets exactly it). But the common shape, a do-bind
/// whose initializer is one of these accessors and whose continuation
/// consumes the result immediately, is lowered WITHOUT the box:
/// `lang/src/codegen/emit.mo`'s `try_compile_view_bind_db` reads the
/// payload with `monad_view_payload` and passes the handle through
/// (below), and calls `monad_view_new`/`_set`/`_free` directly for the
/// other three. The fusion is shape-selected, never a semantic change: anything
/// that does not match keeps the boxed path, and the emitted shape is
/// pinned by `lang/src/codegen/test/view_ir_tests.mo`.
///
/// ## The handle invariant the fusion relies on
///
/// `view_get_impl` and `view_set_impl` return the SAME handle word they
/// were given, and `view_new_impl` returns a fresh one. A fused `get`
/// therefore needs no aggregate result: one i64 (the payload) plus the
/// unchanged input word is the whole pair.
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

// ── Slot: the empty/full view ───────────────────────────────────────
//
// The second view-types shape: a linear handle whose STATE is in the type,
// so a move is expressible without a `Copy` payload. `Slot Empty A` has no
// value; `Slot Full A` holds exactly one. `take` moves the value out and
// returns an empty slot; `fill` moves one in. A `Full` slot must be taken
// before it can be freed, so a linear payload is never silently dropped.
//
// `Empty`/`Full` are ordinary inhabited phantom tags (never constructed);
// they are deliberately not empty inductives — an inductive with no
// constructors is `False`, which AGENTS.md reserves for `Void`.

pub type Empty {
    empty_tag,
}

pub type Full {
    full_tag,
}

/// An opaque linear handle that is either empty or holds one value of any
/// type. The witness is the inhabitation proof and is unreferenceable
/// (`#[opaque]`); values come only from the natives below.
#[linear]
#[opaque]
pub type Slot (s : Type) (A : Type) { slot_witness }

#[native slot_new]
priv def slot_new_raw (a : A) : RawIO (Slot Full A)

#[native slot_empty]
priv def slot_empty_raw {A : Type} : RawIO (Slot Empty A)

#[native slot_take]
priv def slot_take_raw (!s : Slot Full A) : RawIO (Pair A (Slot Empty A))

#[native slot_fill]
priv def slot_fill_raw (!s : Slot Empty A) (a : A) : RawIO (Slot Full A)

#[native slot_peek]
priv def slot_peek_raw [Copy A] (!s : Slot Full A) : RawIO (Pair A (Slot Full A))

#[native slot_free]
priv def slot_free_raw (!s : Slot Empty A) : RawIO Unit

/// Allocate a full slot holding `a`. Any type moves in; no `Copy` needed.
pub def Slot.new (a : A) : IO (Slot Full A) :=
    IO.mk (slot_new_raw a)

/// Allocate an empty slot. `A` is usually pinned by the annotation
/// (`let s : Slot Empty I64 <- Slot.empty;`) because nothing else mentions it.
pub def Slot.empty {A : Type} : IO (Slot Empty A) :=
    IO.mk slot_empty_raw

/// Move the value out, leaving the slot empty. Consumes and returns the
/// handle (P2); the old `Slot Full A` is unusable after the call.
pub def Slot.take (!s : Slot Full A) : IO (Pair A (Slot Empty A)) :=
    IO.mk (slot_take_raw s)

/// Move a value in, leaving the slot full.
pub def Slot.fill (!s : Slot Empty A) (a : A) : IO (Slot Full A) :=
    IO.mk (slot_fill_raw s a)

/// Read a full slot of a `Copy` payload without emptying it. This is the
/// only operation that duplicates the payload, so only a `Copy` one is
/// allowed; use `take`/`fill` for a linear value.
pub def Slot.peek [Copy A] (!s : Slot Full A) : IO (Pair A (Slot Full A)) :=
    IO.mk (slot_peek_raw s)

/// Consume an EMPTY slot. A full slot must be `take`n first, so a linear
/// payload is never silently dropped.
pub def Slot.free (!s : Slot Empty A) : IO Unit :=
    IO.mk (slot_free_raw s)
