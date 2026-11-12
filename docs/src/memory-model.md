# Memory Model

Monad aims for a memory-safe language with **no garbage collector and no
reference counting**: values that have a single owner are freed
deterministically, values that may be shared are reclaimed a region at a time,
and raw pointer access only happens through linear *view* handles.

That is the destination. This chapter describes the model as it is designed,
says plainly what is implemented today, and points at the limitations.

> [!IMPORTANT]
> **The default build still uses a garbage collector.** Native binaries link
> the Boehm conservative collector (the WASI and web profiles use allocators
> with no collector). A `MONAD_OWNERSHIP=1` build is the first
> real step away from it: it frees a narrow class of constructors with
> generated drop glue. The region allocator is designed but not yet
> implemented. See [Linear Types](./linear-types.md) and
> [Compiling and Running](./compiling.md#memory).

## The three allocation classes

Every run-time value belongs to one class.

| Class | What it is | Who frees it | Examples |
|---|---|---|---|
| **Owned** | An affine value with no aliases | Type-directed drop glue at the end of its definition (v1: unused binders only) | A monomorphic user inductive with no nullary constructor (e.g. the `OwnedBox` fixture type) |
| **Region** | A value that may be shared, copied, cyclic, or stored in a container | The region, all at once, at region exit | `String`, `ByteBuf`, `Ref`, `Array`, `Shared`, `List`, `Option`, `Result`, `IO`, and anything containing one |
| **Static** | A value that lives for the process | Never | String literals, nullary constructors, `argv` |

The class is decided from the **type**, not from an allocation site. It is a
whole-program property in both directions: a type that a Region value can
contain is Region, because the Region value is never freed individually and
must not point at something that was; and a type that can contain a Region
value is Region too, because an Owned cell is not scanned by the collector and
would hide the pointer.

## What a value looks like

At the backend boundary every Monad value is an `i64` word. A constructor is a
heap cell `{ header, tag, field_count, fields[] }`; a closure is
`{ header, entry, arity, env_size, env[] }`; a `String` is a bare
NUL-terminated `char*` (literals live in the compiled binary, computed strings
are heap buffers); a `ByteBuf` is a header plus a byte payload; `Ref`, `Cell`,
`Slot` and the other handles are raw structs with an allocation-kind tag.

Two consequences matter for safety:

- A constructor's fields mix scalars, string pointers, and heap objects, so
  **freeing is per-type**, never a generic recursion over raw words.
- Nullary constructors are shared singletons. Freeing one would corrupt every
  other user, so drop glue never frees them.

## Multiplicity and `Copy`

Binders are affine by default: an unannotated binder may be used **at most
once**, unless its type has a `Copy` instance. `Copy` is the only route to
unrestricted use. `Clone` is the explicit copy operation and is never inserted
by the compiler; each instance decides what a copy means (`Clone String`
shares its bytes).

```monad
def sum_twice (x : I64) : I64 := x + x      // ok: I64 is Copy

def first_char_twice (s : String) : String :=
    String.slice s 0 1 ++ String.slice s 0 1 // ok: String is Copy (a shared pointer)
```

`String` is `Copy` because it is an immutable shared pointer — copying it
duplicates the pointer, never the bytes. `ByteBuf` is deliberately **not**
`Copy`, because it is mutable: two owners could observe each other's writes.
Full rules, annotations and diagnostics are in [Linear Types](./linear-types.md).

## `Shared`: borrowing without ownership

`Shared A` is a `Copy` handle that names a value without owning it.
`Shared.get` yields a **view** of the payload. A view may be read, matched,
called, or passed to another `Shared` parameter; it may not be stored or
returned. Passing it where an owner is expected is not rejected yet (gap #12).

A `Shared` handle answers "how do many readers reach one value?" It does not
answer "how long does the value live?" Today the collector keeps the payload
alive; once the collector is gone, an escaping handle is the sharpest open
hazard in the model. The lifetime story is part of the planned region work.

## Views: safe pointers

A *view* pairs a pointer with a linear, compile-time proof that the pointer is
valid. The proof is erased, so a dereference is a plain load with no collector
or refcount traffic. The v1 handles are:

- `Cell A` — a linear handle that owns one `Copy` payload.
- `Slot Empty A` / `Slot Full A` — a linear handle whose *state is in the type*;
  `take` moves the value out and returns an empty slot, `fill` moves one in, and
  a full slot must be taken before it can be freed.

Neither handle has a `Copy` or `Clone` instance. Every mutating operation
consumes the handle, and `get`/`set`/`take`/`fill` return the new one, so a
use-after-free or double-free would require duplicating a handle — which the
affine rule rejects.

```monad
use init::view {Cell}

def main (_args : List String) : IO Unit := do {
    let c0 <- Cell.new 41;
    let p <- Cell.get c0;
    match p {
        Pair.pair x c1 => do {
            let c2 <- Cell.set c1 (I64.add x 1);
            let p2 <- Cell.get c2;
            match p2 {
                Pair.pair y c3 => do {
                    let _ <- Cell.free c3;
                    IO.println (I64.to_string y)
                },
            }
        },
    }
}
```

`Slice n A`, an indexed array view with an erased `Fits i n` bounds proof, is
designed but waits on value-dependent type constructors (`Vec n A`).

## Freeing today

A `MONAD_OWNERSHIP=1` build routes a narrow class of constructors through
`calloc`/`free` and emits a `drop_<T>` function for each Owned type: it
switches on the constructor tag, drops owned fields, skips `Copy` and region
values, and frees the cell. Drops are planned for unused binders only: a
parameter whose declared type resolves to an Owned type, or a `let` whose
initializer is a freshly allocated Owned constructor. A `let` bound to a call
or a variable is not dropped. This is deliberately fail-closed: an unprovable
definition emits no drop and leaks.

Everything else stays with the collector. A `MONAD_OWNERSHIP=poison` build
fills freed cells with `0xDE` instead of returning them, so a use-after-free
shows up deterministically during testing.

The mode refuses to build a mote that is still `[affine] mode = "warn"`,
because drop glue is only sound on code the checker accepts in error mode.

## The target: regions

The next step is a page arena. `monad_region_alloc` becomes a bump allocator
over pages, freed all at once when a region ends. Three regions are planned:

- one root region per thread, freed at thread exit;
- one region per fiber, adopted into the parent at join;
- explicit `Region.with`, which runs a computation in a child region and
  copies its result back out.

Copying out needs a compiler-generated `Transfer` dictionary, because the
runtime cannot deep-copy an untyped value. `Transfer String` copies the bytes
(unlike `Clone String`, which shares the pointer). A type with no `Transfer`
instance cannot be returned from `Region.with` — that compile-time rejection
is the escape gate. A write through a `Ref`, `Array` or `Channel` takes the
conservative route instead: the current region is adopted into its parent and
never freed, so the write cannot dangle.

```monad,ignore
// Planned surface (not implemented).
def render (model : Model) : IO String :=
    Region.with (fn _ => render_inner model)
```

## Known limitations

- The default build uses Boehm; `-lgc` is still linked.
- `MONAD_OWNERSHIP=1` frees only monomorphic, non-`Copy`, non-nullary
  constructors, and only for unused binders. Generic containers, closures and
  anything reachable from `Ref`/`Array`/`Shared` are region values and leak.
- Regions are designed, not implemented. `Cell.free` and `Slot.free` currently
  poison their block rather than freeing it.
- A `Shared` handle that escapes its referent is not rejected yet; lifetime
  typing is open.
- Closure captures are counted but a capturing closure is not made linear.
- WASI uses `malloc` with no free; the web build uses a bump allocator that
  never returns memory to the host.
- The Rust bootstrap host accepts this code but does not enforce the affine or
  view rules; `monad check` is the authority.

The design, the full hazard catalogue, and the verification obligations are
recorded in `plans/bootstrapping/memory-model-design.md`.
