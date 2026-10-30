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
> `error`. `init`, `runtime`, `proofs` and `web_event` are at zero and enforced.
>
> Three gaps remain: the explicit `!`/`?`/`%` annotations below parse but are
> dropped before checking in some positions, so only the affine row is
> enforced; a `Shared.get` view is rejected when it is stored or returned but
> not yet when it is passed to an *owning* call parameter (that needs the
> callee's signature); and memory reclamation is not implemented (codegen
> emits no `monad_release` yet, so the collector remains).

## Overview

Every variable in Monad is meant to carry a **multiplicity** controlling how many
times it may be used:

| Multiplicity | Syntax | Constraint | Meaning |
|-------------|--------|------------|---------|
| `Affine` (≤1) | `x : A` (no prefix), or `?x : A` | at most once | **The default.** Usable 0 or 1 times; dropping is allowed |
| `Many` (ω) | no prefix, when `Copy A` resolves | none | Shared: usable any number of times. A `Copy` instance (or `[Copy A]` on the def) is the only route here |
| `Linear` (1) | `!x : A` | exactly once | Cannot be copied or discarded (parsed; not yet carried into the checker in every position) |
| `Zero` (0) | `%x : A` | never at run time | Erased; type-level only (parsed; not yet carried everywhere) |

## What Parses Today

Struct fields accept all four, in both implementations:

```monad
struct Buffer {
    !data : String,
    ?label : String,
    size : I64
}
```

So do parameters, on definitions and on typed lambda parameters:

```monad
def f (!a : I64) (?b : I64) (%c : I64) (d : I64) : I64 := a + b + c + d
def h : I64 -> I64 := fn (!x : I64) => x
```

Two things about the parameter form are easy to get wrong:

- **The prefix applies to the whole group, not one name.** `(!x y : I64)` marks
  both `x` and `y` linear. Write separate groups if you meant otherwise.
- **A lambda parameter must be parenthesised and annotated.** Bare `\ !x => x`
  is a parse error in both implementations.

A destructured parameter takes a prefix too:

```monad,ignore
struct Coord { fst : I64, snd : I64 }

// Self-hosted only -- the bootstrap host rejects a prefix on this form.
def sum_coord (!{fst, snd} : Coord) : I64 := fst + snd
```

All of it is recorded on the parse tree and then discarded.

## Usage Rules

Enforced at compile time, with no run-time overhead:

1. **Unannotated / Affine** (`x` or `?x`): must appear **at most once**, unless
   `Copy A` resolves (then it is shared freely).
2. **Linear** (`!x`): must appear **exactly once**. Parsed, but the annotation
   is not carried into the checker in every position yet.
3. **Zero** (`%x`): must not appear in run-time position at all. Same caveat.
4. **Many** is not written: it is what an unannotated binder becomes when its
   type is `Copy`.

```monad
def ok (!x : I64) : I64 := x           // passes (once carried)
def unused (!x : I64) : I64 := 42      // intended: fails — never used
def overused (!x : I64) : I64 := x + x // intended: fails — used twice
def affine_ok (?x : I64) : I64 := 42   // passes
def many_ok (x : I64) : I64 := x + x   // passes: I64 is Copy
```

`many_ok` passes because `Copy I64` is a builtin instance. Replace `I64`
with a type that has no `Copy` instance — a `struct`, a `List`, a user
inductive — and the second use is a `copy_required` error. A `String` is
`Copy` (an immutable shared pointer), so strings may be shared freely; a
`List`, by contrast, is a heap chain and is not.

The affine rows are live on every path. The `!`/`%` rows are not: those
annotations are dropped at `pt_lam` before the rule sees them, so
`unused`/`overused` still compile.

## Where This Actually Stands

The affine rule is live; the annotations are not yet.

1. **The affine rule is wired into everything.** `lang/src/typecheck/usage.mo`
   counts runtime uses, `copy_class.mo` resolves `Copy`, and
   `affine.mo` decides. `lang/src/module.mo`'s
   `check_module_with_scope_classified` classifies the result by the mote's
   `[affine] mode`, and `check`/`compile`/`run`/`test`/`eval` all go through it.
2. **Explicit `!`/`?`/`%` are still dropped before lowering.** The parser
   records a multiplicity on each parameter, but the pass that builds the core
   `pi`/`lam` terms has nowhere to put it — those terms have no multiplicity
   field. So `linear_unused` and the erased-at-runtime check have no real-code
   coverage.
3. **Codegen emits no frees.** `dropck.mo` computes drop points but is pure and
   unwired, and `monad_release` is never called from generated code. The
   collector is still doing the work.

## Affine by default

`Copy` (`lang/src/typecheck/copy_class.mo`, with the class itself in
`init/src/copy.mo`) decides which types may still be shared. Resolution is
*fail-closed*: where it cannot tell, it denies sharing rather than granting it,
because the opposite default would quietly disable the whole check. Instances
are unconstrained — `Copy (Shared A)` and `Copy String` resolve, `Copy (Pair A B)`
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

**The affine rule** (`lang/src/typecheck/affine.mo`) combines the two into the
*effective multiplicity* of a binder: `1` if annotated `!x` (or the type is
`#[linear]`), `0` if annotated `%x`, `ω` if `Copy A` resolves or `A` is named in
the def's `[Copy A]` constraints, and `≤1` otherwise. **An unannotated binder is
affine, not `Many`**, so a second use of an ordinary parameter is an error. That
reading is guarded by a test, because reading the parser's `Many` default as ω
would pass every program while still looking like it worked.

`String` is `Copy`: it is an immutable pointer to bytes, so duplication shares
the bytes rather than copying them. `ByteBuf` is not — it is mutable.

Three diagnostics come out of it, named for the fix rather than the count: a
binder used more than once but *owned* at most once wants a borrow or a `Copy`
instance; a binder owned twice really is moved twice and wants a rewrite; a
`!x` never used is the one case affine's weakening does not excuse.

A def's declared constraints are also enforced where the def is **called**:
once a call's types are solved, every `[C A]` it declares needs a matching
instance, or the call is a `no instance of …` error. That includes `[Copy A]`,
which never becomes a dictionary parameter — so `over [Copy S] (ln : Lens S A)
…` rejects a structure with no `Copy` instance instead of duplicating it
anyway. A caller that is itself generic (`[Copy T]` forwarding its own
parameter) is not decidable and stays accepted.

Two caveats matter. **Nothing frees memory yet.** Codegen still emits no
`monad_release`, `Shared` is boxed rather than erased, and `String` is
collector-owned, so the GC described in
[Compiling and Running](./compiling.md#memory) is not going anywhere yet.
Second, the rule only sees the binders it can *type*: a binder whose type is
still an unannotated hole, or a match field whose constructor is ambiguous
corpus-wide (`mk`, `cons`, `ok`), is exempt from enforcement rather than
guessed at. The measurement report stays fail-closed, so its numbers are an
upper bound. `!` and `%` are dropped at `pt_lam` in some positions, so the
`Linear` and `Zero` rows of the table have no real-code coverage.

## Why It Matters Beyond Correctness

Multiplicities are also the intended basis for **memory management**. Compiled
binaries currently reach for a conservative garbage collector because codegen
never emits a free — see
[Compiling and Running](./compiling.md#memory). The plan is for linear and affine
information to tell the backend exactly where a value's last use is, so it can
free deterministically and drop the GC.

That is the strongest argument for finishing this work, and it is why the GC is
described as a stopgap rather than a design choice.

## Comparison to Rust

| Concept | Monad (intended) | Rust |
|---------|------------------|------|
| Unrestricted (ω) | only when `Copy A` resolves (builtin instance or `[Copy A]`) | `Copy` types |
| Affine (≤1, the default) | unannotated `x : A`, or `?x` | non-`Copy` values / `Drop` types |
| Linear (exactly once) | `!x` | move semantics |
| Erased | `%x` | (no equivalent) |
| Enforcement | type checker | borrow checker |
| Run-time cost | none | none |

## Roadmap

Roughly in order:

- ~~Wire `multiplicity_prefix` into the self-hosted definition- and
  lambda-parameter parsers~~ — done, destructured parameters included
- ~~Reinstate usage checking in the current type checker~~ — done: the affine
  rule is always on (`lang/src/typecheck/affine.mo`)
- ~~Track let-bound variables, not just parameters~~ — a `let` elaborates to a
  lambda application, so its binder is counted like any other
- Carry the `!`/`?`/`%` multiplicity through lowering, so `pi` and `lam` can
  hold one (today the annotations are dropped at `pt_lam`)
- Check arrow multiplicity at application sites
- Enforce multiplicities on constructor fields under pattern matching
- Subsumption: `Many` should subsume `Linear` and `Affine`
- Drive codegen's memory reclamation from multiplicities, replacing the GC
  (type-directed drop glue; a `String` field is never released)
- `noalias` attributes on linear parameters in the emitted LLVM IR

Affine-by-default covers the counting and sharing halves of this list
(`Copy` plays the part of subsumption, from the other side: everything is
affine unless `Copy` says otherwise). It never touches lowering — it reads
the multiplicity off the parse tree as it stands — and `dropck.mo` computes
drop points without emitting anything from them.

Next, we'll explore **concurrency**.
