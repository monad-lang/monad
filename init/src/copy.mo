/// `Copy` — the only route to unrestricted (ω) use under the
/// affine-by-default experiment.
///
/// Part of Milestone 2 of that experiment (*Design B: Viability
/// Experiment*). Nothing enforces
/// multiplicity yet; this file declares the gate that enforcement will
/// consult, and `lang/src/typecheck/copy_class.mo` is the side that
/// consults it.
///
/// ## Why this lives in `init`
///
/// `init` is the pure, portable core — it "depends on nothing: it must
/// work in any environment, wasm and embedded targets included"
/// (`init/mote.toml`). `Copy` is a type-system concept with no OS
/// surface, and `Pair`, which `copy` returns, is already here
/// (`init/src/prelude.mo`). It started out in `std` and had to move:
/// `Borrow A` belongs in `init` for the same reason, `std` depends on
/// `init` and never the reverse, so a `Copy` in `std` would strand
/// `instance Copy (Borrow A)` away from its own type and put it out of
/// reach of every `init`-only consumer.
///
/// ## Why a class and not a compiler table
///
/// Under Design B every binder is affine by default: usable at most
/// once, droppable. Sharing has to be *requested*, and the request is
/// checked by the same instance machinery that types the rest of the
/// program rather than by a list baked into the checker. That makes the
/// gate user-extensible — a plain-old-data type of your own can opt in —
/// where a hardcoded table would not.
///
/// ## Why `copy` returns a pair
///
/// Duplication is the thing being authorised, so the method's type says
/// exactly that: one value in, two out. Design B's rule R3 names this
/// primitive `dup`, and a use that needs ω elaborates to it — `x * x`
/// becoming `let (a, b) = copy x; a * b`, inserted by the compiler, not
/// written. **There is no copy call in the surface language**, and none
/// of the instances below is meant to be called by hand.
///
/// ## The instance bodies duplicate, and cannot not
///
/// `Pair.pair x x` uses `x` twice. Under the very rule this class
/// gates, that is a double use needing `Copy I64` — which is what is
/// being defined. The circularity is real and it is why Design B says
/// builtin instances lower to a core `dup` primitive rather than to a
/// checkable Monad body: bitwise duplication of a scalar is trusted, not
/// verified. Until erasure and `dup` exist these bodies are ordinary
/// code, and an affine checker run over this file would flag every one
/// of them. That is expected, and this comment is the reason not to
/// "fix" it.
///
/// ## What is deliberately absent
///
/// `List`, `Map` and every other heap-allocated inductive. Design B
/// shares those through a borrow, and deep-copies them through an
/// explicit `Clone` whose cost stays visible at the call site. M1
/// measured why this matters: `List` is the second largest source of
/// over-used binders in the compiler's own corpus, so a `Copy (List A)`
/// instance would quietly convert a borrow-shaped workload into silent
/// deep copies.
///
/// **`String` IS `Copy`, and that is not a contradiction.** A compiled
/// `String` is a bare `char*` (`runtime/src/runtime_core.c`) pointing at
/// immutable UTF-8 bytes; no operation mutates a string's bytes, so two
/// pointers to the same bytes are observationally indistinguishable and
/// aliasing cannot be observed. `copy` therefore duplicates the POINTER,
/// never the bytes -- this is the `&str` reading of a string, not a
/// `Vec<u8>` reading. It is the one heap type where a bitwise duplicate
/// is the correct duplicate. The bytes themselves are the collector's
/// (or, once the collector is retired, a refcounted `StringObj`'s) --
/// that is a separate question from whether the value may be shared.
/// See `plans/type-system/quantitative-types.md`'s *Strings* section.
///
/// **`ByteBuf` is not here, and must not be.** It is a MUTABLE buffer
/// (`std/src/bytebuf.mo`); aliasing it would let one owner observe
/// another's writes, so it stays affine despite being collector-managed.
///
/// **`Nat` is absent on purpose, and the design's own table disagrees.**
/// Design B's *Copy policy for core types* lists `Nat` alongside the
/// scalars as a builtin `Copy`. That is only defensible once `Nat` has
/// a machine-word representation (the efficient `Nat`/`String`/
/// `ByteArray` proposal). Today it is a unary inductive —
/// `type Nat { zero, succ (n : Nat) }` in `init/src/prelude.mo` — so a
/// value of it is a heap chain, and granting `Copy` would hand two
/// owners to the same allocation. That is precisely the double free the
/// gate exists to prevent, so the table is aspirational here and the
/// instance stays out until the representation changes. The affine
/// report surfaces the consequence honestly: `Nat` binders show up
/// under `value_used_after_move`, which is the correct answer for a
/// linked structure moved twice.
pub class Copy A {
    def copy : A -> Pair A A
}

// ---------- Builtin instances ----------
//
// Scalars, `Bool`, `Char`, `Unit` — Design B's *Copy policy for core
// types*. These are the types whose duplication is a register move.

pub instance Copy I64 {
    def copy (x : I64) : Pair I64 I64 := Pair.pair x x
}

pub instance Copy U64 {
    def copy (x : U64) : Pair U64 U64 := Pair.pair x x
}

pub instance Copy I32 {
    def copy (x : I32) : Pair I32 I32 := Pair.pair x x
}

pub instance Copy U32 {
    def copy (x : U32) : Pair U32 U32 := Pair.pair x x
}

pub instance Copy U8 {
    def copy (x : U8) : Pair U8 U8 := Pair.pair x x
}

pub instance Copy F64 {
    def copy (x : F64) : Pair F64 F64 := Pair.pair x x
}

pub instance Copy Bool {
    def copy (x : Bool) : Pair Bool Bool := Pair.pair x x
}

pub instance Copy Char {
    def copy (x : Char) : Pair Char Char := Pair.pair x x
}

pub instance Copy Unit {
    def copy (x : Unit) : Pair Unit Unit := Pair.pair x x
}

/// A `String` is an immutable shared pointer (see this file's header):
/// duplicating it copies the pointer, never the bytes. Every operation
/// on a `String` is read-only, so the alias is unobservable. The bytes
/// stay collector-owned; that is why this instance needs no free.
pub instance Copy String {
    def copy (x : String) : Pair String String := Pair.pair x x
}
