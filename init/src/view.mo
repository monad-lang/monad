/// Safe pointers on quantitative types: `Cell` and its erased `At` proof.
///
/// First milestone of `plans/type-system/view-types.md`. A `Cell A` is an
/// opaque, LINEAR handle that owns one `Copy` payload. It has no
/// constructors and no `Copy`/`Clone` instance, so:
///
/// - duplicating it is untypable (`Copy` has no instance for it);
/// - dropping it is `linear_unused` (`#[linear]` forces every binder of
///   this type to be used exactly once);
/// - its operations take the handle as an ordinary affine binder and
///   return it, so a use-after-free or double-free requires two uses of
///   one binder, which the affine rule rejects.
///
/// Every operation is a PURE linear mutation: the native writes only the
/// handle it consumes and returns, so no other reference can witness the
/// change and there is nothing for `IO` to track (AGENTS.md, "a mutation
/// through a linearly-owned value is not an effect"). No `IO.mk` wrapper.
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
/// ## The fused `let`
///
/// The common shape -- `let p := Cell.get c in match p { ... }`, with the
/// match consuming the pair immediately -- is lowered WITHOUT the box:
/// `codegen/src/emit.mo`'s `try_compile_view_bind_db` reads the payload with
/// `monad_view_payload` and passes the handle through (below), and calls
/// `monad_view_new`/`_set`/`_free` directly for the other three. The fusion
/// is shape-selected, never a semantic change: an escaping `Pair` (the
/// `finish_with_42` shape in `view_tests.mo`) keeps the boxed path, which is
/// the reference semantics (the Rust host interprets exactly it), and the
/// emitted shape is pinned by `codegen/src/test/view_ir_tests.mo`.
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
// These are PURE, not `RawIO`: the write is confined to the linearly-owned
// handle they consume and return, so no other reference can witness it.
// `view_get` returns a `Pair` built in C with the builtin `pair` tag (15):
// a handle plus its payload must travel as one value, or the wrapper would
// have to use `c` twice.

#[native view_new]
priv def view_new_raw [Copy A] (a : A) : Cell A

#[native view_get]
priv def view_get_raw [Copy A] (c : Cell A) : Pair A (Cell A)

#[native view_set]
priv def view_set_raw [Copy A] (c : Cell A) (a : A) : Cell A

#[native view_free]
priv def view_free_raw [Copy A] (c : Cell A) : Unit

// ── The user-facing operations ──────────────────────────────────────

/// Allocate a cell holding `a`. Allocation is pure: the fresh handle is the
/// only route to the new block.
pub def Cell.new [Copy A] (a : A) : Cell A :=
    view_new_raw a

/// Read the payload, returning it with the same handle. Consumes and
/// returns the handle (view-types P2): the old handle is unusable after
/// the call.
pub def Cell.get [Copy A] (c : Cell A) : Pair A (Cell A) :=
    view_get_raw c

/// Overwrite the payload, leaving the cell intact.
pub def Cell.set [Copy A] (c : Cell A) (a : A) : Cell A :=
    view_set_raw c a

/// Consume the cell and release its storage. In v1 this poisons the block
/// (the collector owns it; see this file's header).
pub def Cell.free [Copy A] (c : Cell A) : Unit :=
    view_free_raw c

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
priv def slot_new_raw (a : A) : Slot Full A

#[native slot_empty]
priv def slot_empty_raw {A : Type} : Slot Empty A

#[native slot_take]
priv def slot_take_raw (s : Slot Full A) : Pair A (Slot Empty A)

#[native slot_fill]
priv def slot_fill_raw (s : Slot Empty A) (a : A) : Slot Full A

#[native slot_peek]
priv def slot_peek_raw [Copy A] (s : Slot Full A) : Pair A (Slot Full A)

#[native slot_free]
priv def slot_free_raw (s : Slot Empty A) : Unit

/// Allocate a full slot holding `a`. Any type moves in; no `Copy` needed.
pub def Slot.new (a : A) : Slot Full A :=
    slot_new_raw a

/// Allocate an empty slot. `A` is usually pinned by the annotation
/// (`let s : Slot Empty I64 := Slot.empty in ...`) because nothing else
/// mentions it.
pub def Slot.empty {A : Type} : Slot Empty A :=
    slot_empty_raw

/// Move the value out, leaving the slot empty. Consumes and returns the
/// handle (P2); the old `Slot Full A` is unusable after the call.
pub def Slot.take (s : Slot Full A) : Pair A (Slot Empty A) :=
    slot_take_raw s

/// Move a value in, leaving the slot full.
pub def Slot.fill (s : Slot Empty A) (a : A) : Slot Full A :=
    slot_fill_raw s a

/// Read a full slot of a `Copy` payload without emptying it. This is the
/// only operation that duplicates the payload, so only a `Copy` one is
/// allowed; use `take`/`fill` for a linear value.
pub def Slot.peek [Copy A] (s : Slot Full A) : Pair A (Slot Full A) :=
    slot_peek_raw s

/// Consume an EMPTY slot. A full slot must be `take`n first, so a linear
/// payload is never silently dropped.
pub def Slot.free (s : Slot Empty A) : Unit :=
    slot_free_raw s

// ── Swap: two handles, one exchange ─────────────────────────────────
//
// A swap is the smallest operation that shows what the linear discipline
// buys: it needs BOTH handles at once, gives BOTH back, and neither payload
// is ever in two places. There is no way to write it with one handle
// duplicated (that is untypable), and no way to leave one behind (the
// emptied handle is refilled or freed on every path).
//
/// Exchange the payloads of two cells. Both handles are consumed and returned
/// (in the same order they were given), so `Cell.swap a b` leaves `a` holding
/// `b`'s old value and vice versa.
pub def Cell.swap [Copy A] (a : Cell A) (b : Cell A) : Pair (Cell A) (Cell A) :=
    let pa : Pair A (Cell A) := Cell.get a in
    match pa {
        Pair.pair va ra => cell_swap_second va ra b,
    }

def cell_swap_second [Copy A] (va : A) (ra : Cell A) (b : Cell A) : Pair (Cell A) (Cell A) :=
    let pb : Pair A (Cell A) := Cell.get b in
    match pb {
        Pair.pair vb rb => cell_swap_apply va ra vb rb,
    }

def cell_swap_apply [Copy A] (va : A) (ra : Cell A) (vb : A) (rb : Cell A) : Pair (Cell A) (Cell A) :=
    let rb2 := Cell.set rb va in
    let ra2 := Cell.set ra vb in
    Pair.pair ra2 rb2

/// Exchange the payloads of two full slots. No `Copy` is needed: the values
/// MOVE between the handles, and each handle is emptied and refilled exactly
/// once. This is the pointer swap — the cells stay where they are and only
/// what they point at changes.
pub def Slot.swap (a : Slot Full A) (b : Slot Full A) : Pair (Slot Full A) (Slot Full A) :=
    let pa : Pair A (Slot Empty A) := Slot.take a in
    match pa {
        Pair.pair va ea => slot_swap_second va ea b,
    }

def slot_swap_second (va : A) (ea : Slot Empty A) (b : Slot Full A) : Pair (Slot Full A) (Slot Full A) :=
    let pb : Pair A (Slot Empty A) := Slot.take b in
    match pb {
        Pair.pair vb eb => slot_swap_apply va ea vb eb,
    }

def slot_swap_apply (va : A) (ea : Slot Empty A) (vb : A) (eb : Slot Empty A) : Pair (Slot Full A) (Slot Full A) :=
    // `a`'s handle takes `b`'s value, `b`'s handle takes `a`'s.
    let fa := Slot.fill ea vb in
    let fb := Slot.fill eb va in
    Pair.pair fa fb

// ── Slice: the indexed contiguous view ──────────────────────────────
//
// The third view-types shape: a linear handle over `n` CONTIGUOUS
// elements, with the length in the TYPE (`Slice n A`). `n` is a
// `Nat`, so a computed length and a literal one are the same term
// (`Vec`'s discipline, and why `whnf` reduces literal indices).
//
// The index is a runtime-checked contract, not a proof:
// `Slice.of_list` compares the list's actual length with the `n` value
// argument it is given (the SAME binder that indexes the result), and
// `Slice.split_at` splits at its `Nat` argument and types the halves
// `Slice k A` / `Slice (Nat.sub n k) A`. So a `Slice n A` always really
// has `n` elements; an index that does not fit is an error, never a
// silent difference between the type and the data. A static `Fits i n`
// proof (discharged at the call from a literal index) is the planned
// follow-up; until then every access is bounds-checked at run time, and
// an out-of-range access returns the HANDLE in the error variant so a
// linear slice is never lost to a failed operation.
//
// A slice never owns its elements: `split_at` gives two handles over one
// backing array with disjoint ranges, and the array is released by the
// collector once every handle over it is gone. Element access needs
// `[Copy A]` for the same reason `Cell.get` does -- the element stays in
// the slice and a copy leaves -- and `set` requires it too, so a linear
// element is never silently overwritten.

/// Why `Slice.of_list` refused a list -- it is the only thing that can go
/// wrong at construction, and `actual` is what the list really held, so a
/// caller can report the disagreement, not just that one exists. (Every
/// other `Slice` failure is a bounds miss, which returns the handle
/// instead; there is nothing left to describe.)
pub struct SliceError {
    actual : I64,
}

/// An opaque LINEAR handle over `n` contiguous elements of `A`. The
/// witness is the inhabitation proof and is unreferenceable
/// (`#[opaque]`); values come only from `Slice.of_list` and
/// `Slice.split_at`.
#[linear]
#[opaque]
pub type Slice (n : Nat) (A : Type) { slice_witness }

// ── Natives ─────────────────────────────────────────────────────────
//
// Pure for the same reason `Cell`'s are: the write is confined to the
// handle the native consumes and returns. The `{n : Nat}` / `{i : Nat}`
// binders are TYPE-ONLY -- an implicit binder is never passed to a
// native -- so each signature also carries the I64 offset the runtime
// actually uses. `Result` (10/11) and `Pair` (15) are the fixed
// builtin tags, which is what lets the C side build them.

#[native slice_of_list]
priv def slice_of_list_raw {n : Nat} (xs : List A) (len : I64) : Result I64 (Slice n A)

#[native slice_length]
priv def slice_length_raw {n : Nat} (s : Slice n A) : Pair I64 (Slice n A)

#[native slice_get]
priv def slice_get_raw [Copy A] {n : Nat} (s : Slice n A) (i : I64) : Result (Slice n A) (Pair A (Slice n A))

#[native slice_set]
priv def slice_set_raw [Copy A] {n : Nat} (s : Slice n A) (i : I64) (a : A) : Result (Slice n A) (Slice n A)

#[native slice_split]
priv def slice_split_raw {n : Nat} {k : Nat} (s : Slice n A) (ix : I64)
    : Result (Slice n A) (Pair (Slice k A) (Slice (Nat.sub n k) A))

#[native slice_free]
priv def slice_free_raw {n : Nat} (s : Slice n A) : Unit

// ── The user-facing operations ──────────────────────────────────────

/// Allocate a slice of exactly `n` elements from `xs`. `n` indexes the
/// result AND is the length checked against the list, so the two cannot
/// disagree: a list of a different length comes back as `Result.err`
/// carrying its actual length. Construction is
/// pure -- the fresh handle is the only route to the new block.
pub def Slice.of_list (xs : List A) (n : Nat) : Result SliceError (Slice n A) :=
    match slice_of_list_raw xs (Nat.to_i64 n) {
        Result.ok s => Result.ok s,
        Result.err actual => Result.err (SliceError.mk actual),
    }

/// The runtime element count, with the handle returned. Equal to the
/// type index `n` by construction; the value is what a loop needs.
pub def Slice.length {n : Nat} (s : Slice n A) : Pair I64 (Slice n A) :=
    slice_length_raw s

/// Read element `i`, returning it with the same handle. Consumes and
/// returns the handle (view-types P2). An out-of-range `i` returns
/// `Result.err` carrying the handle -- reading never loses the slice.
pub def Slice.get [Copy A] {n : Nat} (s : Slice n A) (i : I64) : Result (Slice n A) (Pair A (Slice n A)) :=
    slice_get_raw s i

/// Overwrite element `i`, leaving the slice intact. `[Copy A]` because
/// the overwritten element is duplicated away (see this section's
/// header); an out-of-range `i` returns the handle unchanged.
pub def Slice.set [Copy A] {n : Nat} (s : Slice n A) (i : I64) (a : A) : Result (Slice n A) (Slice n A) :=
    slice_set_raw s i a

/// Split at `k`, giving two handles with the left one's length in ITS
/// type and the right one's `Nat.sub n k`. `k` must satisfy `k <= n`;
/// a larger `k` is an error carrying the unsplit handle. Both halves
/// share the backing array -- the ranges are disjoint, and the type
/// index of each half is the runtime length `split_at` enforces.
pub def Slice.split_at {n : Nat} (s : Slice n A) (k : Nat)
    : Result (Slice n A) (Pair (Slice k A) (Slice (Nat.sub n k) A)) :=
    slice_split_raw s (Nat.to_i64 k)

/// Consume the slice and release its storage (the backing array is
/// collector-owned; this POISONS the handle, see `Cell.free`).
pub def Slice.free {n : Nat} (s : Slice n A) : Unit :=
    slice_free_raw s
