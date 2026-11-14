# Linear Types

Monad's design calls for **linear** and **affine** types for resource-safe
programming, inspired by Rust's ownership system and Idris's Quantitative Type
Theory (QTT).

> [!IMPORTANT]
> **Affine is the default and is enforced.** An unannotated binder may be
> used **at most once** unless its type has a `Copy` instance (or the
> enclosing def carries a `[Copy A]` constraint). A second use is a compile
> error: `copy_required` if at most one of the uses takes ownership (a
> borrow serves it), `value_used_after_move` if two do.
>
> The rule runs on **every** check and compile path — `monad check`,
> `build`, `run`, `test`, `eval` and the language server. There is no flag
> and no off switch. A mote that has not finished migrating can opt into
> warnings with `[affine] mode = "warn"` in its `mote.toml`; the default is
> `error`. `init`, `std`, `sys`, `runtime`, `proofs` and `web_event` are at
> zero and enforced; the rest of the compiler closure is still migrating
> (the exact set is `scripts/affine-closure-allowlist.txt`, and the gate is
> `scripts/check-affine-closure.sh`).
> A single def can opt out with `#[allow_non_affine "<reason>"]`, and a
> `#[proof]` def is exempt structurally.
>
> There is **no multiplicity annotation syntax**. The `!`, `?` and `%`
> prefixes an earlier design used on parameters and fields were parsed but
> never enforced, and they have been removed from both compilers. Linearity
> is expressed by the type, not by a binder prefix.
>
> Three gaps remain: a `Shared.get` view is rejected when it is stored or
> returned but not yet when it is passed to an *owning* call parameter
> (that needs the callee's signature); and memory reclamation is experimental
> — the default build still uses the collector, while `MONAD_OWNERSHIP=1`
> frees only a narrow class of constructors. See
> [Memory Model](./memory-model.md).

## The rule

Every binder carries an **effective multiplicity**, decided by its type and
the enclosing def's constraints — never by a source annotation:

| Multiplicity | When | Meaning |
|-------------|------|---------|
| `Many` (ω) | `Copy A` resolves, or `A` is named in the def's `[Copy A]` constraints | Shared: usable any number of times |
| `Linear` (1) | the type is `#[linear]` or `#[proof]` | Exactly once — cannot be copied or discarded |
| `Affine` (≤1) | everything else (the default) | At most once; dropping is allowed |

A `Copy` instance is the only route to unrestricted sharing. Resolution is
*fail-closed*: where it cannot tell, it denies sharing rather than granting
it, because the opposite default would quietly disable the whole check.

## Sharing: `Copy`, `Clone` and `Shared`

`Copy` (`lang/src/typecheck/copy_class.mo`, with the class itself in
`init/src/copy.mo`) decides which types may still be shared. Instances are
unconstrained — `Copy (Shared A)` and `Copy String` resolve, `Copy (Pair A B)`
does not.

`Shared` (`init/src/shared.mo`) is a plain type constructor, not reference
syntax: there is no `&T` spelling and none is planned. **The type is the
mode.** It is marked `#[shared]`, and that marker — not the type's name — is
what the checker keys on when it recognizes a `Shared.of` read, so renaming
the type cannot silently disable the check.

A **function-typed binder** is measured by *moves*, not raw mentions:
calling a closure (`f x`) reads it and may happen any number of times,
while passing it on, storing it or returning it transfers it — and exactly
one transfer is allowed. That is what lets `List.map f tail` type-check
without a `Copy (A -> B)` instance: the closure is never duplicated, so the
environment it captured is never double-owned.

`Copy` duplicates implicitly; **`Clone`** (`init/src/clone.mo`) copies
explicitly. `Clone.clone (Shared.of x)` takes the source as a shared read and
returns a fresh owned value, so it neither consumes `x` nor hands out an
alias, and the checker never inserts it. Instances exist for the scalars,
`String`, `Pair`, `Option`, `Result` and `List`; mutable state and handles
(`ByteBuf`, `Ref`, `Ptr`, streams) have none by design — a copy of those is a
new resource and must be written out.

**Usage counting** (`lang/src/typecheck/usage.mo`) counts each binder's uses,
distinguishing one that takes ownership from one that only reads, and combining
branches by max rather than sum (`if c then x else x` uses `x` once) — so both
arms of a match may use a value once without it counting as a double use.

**The rule** (`lang/src/typecheck/affine.mo`) combines the two into the
*effective multiplicity* of a binder. **An unannotated binder is affine, not
`Many`**, so a second use of an ordinary parameter is an error.

`String` is `Copy`: it is an immutable pointer to bytes, so duplication shares
the bytes rather than copying them. `ByteBuf` is not — it is mutable.

Three diagnostics come out of it, named for the fix rather than the count: a
binder used more than once but *owned* at most once wants a borrow or a `Copy`
instance; a binder owned twice really is moved twice and wants a rewrite; and
a linear binder never used is the one case affine's weakening does not excuse.

## Inherently linear types

Instead of annotating every binder with a prefix, a type *declaration* can
carry an attribute:

```monad,ignore
#[linear]
type Qubit {
    qubit_witness
}
```

A binder whose type resolves to a `#[linear]` inductive is treated as linear
— used exactly once — regardless of how it is bound. `#[proof]` is stronger:
every binder is linear, never `Copy`, and the type has no run-time
representation. Recognition is by attribute, not by name, so renaming a type
cannot silently disable its kind. A `Copy` or `Clone` instance for a
linear-or-proof type is rejected.

The prelude's view types use these attributes: `init/src/view.mo`'s `Cell`
and `Slot` are `#[linear]`, and the `At` proof is `#[proof]` — which is what
keeps a safe-pointer handle consumed exactly once without any annotation on
its operations' parameters.

## A def's constraints are enforced at the call site too

A def's declared constraints are enforced where the def is **called**: once a
call's types are solved, every `[C A]` it declares needs a matching instance,
or the call is a `no instance of …` error. That includes `[Copy A]`, so
`over [Copy S] (ln : Lens S A) …` rejects a structure with no `Copy` instance
instead of duplicating it anyway. A bare reference (`let f : S -> S := op`) is
the same obligation: it is a partial application. So is a class **method**
call — `Foo.foo x` with no `instance Foo I64` is a type error where the method
takes the carrier as its first argument (`Show.show`, `BEq.beq`); a
higher-kinded carrier (`Monad.pure`) or a multi-parameter class keeps the
abstract-signature fallback. A caller that is itself generic (`[Copy T]`
forwarding its own parameter) is not decidable and stays accepted.

## Where the rule stops

Two caveats matter. **Freeing is opt-in and narrow.** Codegen still emits no
`monad_release` for ordinary values and `Shared` is boxed rather than erased,
so the GC described in
[Compiling and Running](./compiling.md#memory) remains the default and is not
going anywhere yet. A build with `MONAD_OWNERSHIP=1` instead allocates
monomorphic, non-`Copy` constructors with `calloc` and frees them with
generated `drop_<T>` glue at a definition's exits — but only for binders that
are completely unused, which is what makes the drop sound before a full move
analysis exists. Closures, generic data (`List A`) and anything reachable from
a `Ref`, `Array` or `Shared` stay region-owned and leak, and the build refuses
any mote still in `[affine] mode = "warn"`. See
`plans/bootstrapping/ownership-regions-memory.md`.
Second, the rule only sees the binders it can *type*: a binder whose type is
still an unannotated hole, or a match field whose constructor is ambiguous
corpus-wide (`mk`, `cons`, `ok`), is exempt from enforcement rather than
guessed at. The measurement report stays fail-closed, so its numbers are an
upper bound.

## Why It Matters Beyond Correctness

Multiplicities are also the intended basis for **memory management**. Compiled
binaries currently reach for a conservative garbage collector because codegen
never emits a free — see
[Compiling and Running](./compiling.md#memory). The plan is for the affine
rule's ownership information to tell the backend exactly where a value's last
use is, so it can free deterministically and drop the GC.

That is the strongest argument for finishing this work, and it is why the GC is
described as a stopgap rather than a design choice.

## Comparison to Rust

| Concept | Monad | Rust |
|---------|-------|------|
| Unrestricted (ω) | only when `Copy A` resolves (builtin instance or `[Copy A]`) | `Copy` types |
| Affine (≤1, the default) | unannotated `x : A` | non-`Copy` values / `Drop` types |
| Linear (exactly once) | a `#[linear]` type's binders | move semantics |
| Explicit deep copy | `Clone` (never inserted) | `Clone` |
| Enforcement | the affine usage rule, always on | borrow checker |
| Run-time cost | none | none |

## Roadmap

Roughly in order:

- ~~Wire the usage rule into the self-hosted definition- and
  lambda-parameter parsers~~ — done, destructured parameters included
- ~~Reinstate usage checking in the current type checker~~ — done: the affine
  rule is always on (`lang/src/typecheck/affine.mo`)
- ~~Track let-bound variables, not just parameters~~ — a `let` elaborates to a
  lambda application, so its binder is counted like any other
- ~~`#[linear]` / `#[proof]` type attributes~~ — done
  (`lang/src/typecheck/type_kinds.mo`)
- ~~Closure-capture detection~~ — done (`usage.mo`'s `captured_uses_of*`);
  making a capturing closure itself linear (M4) is still pending
- Enforce the rule on constructor fields under pattern matching
- Drive codegen's memory reclamation from the rule, replacing the GC
  (type-directed drop glue; a `String` field is never released)
- `noalias` attributes on linear parameters in the emitted LLVM IR

Affine-by-default covers the counting and sharing halves of this list
(`Copy` plays the part of subsumption, from the other side: everything is
affine unless `Copy` says otherwise). It never touches lowering — it reads
the parse tree as it stands — and `dropck.mo` computes drop points without
emitting anything from them.

Next, we'll explore **concurrency**.
