# Linear Types

Monad's design calls for **linear** and **affine** types for resource-safe
programming, inspired by Rust's ownership system and Idris's Quantitative Type
Theory (QTT).

> [!WARNING]
> **The syntax parses; nothing is enforced.** Struct fields, `def` parameters,
> lambda parameters and destructured parameters all accept `!`, `?` and `%` in
> the self-hosted compiler. Every one of those annotations is then dropped
> before type checking — no use is counted, and every binder the checker builds
> is `Many`.
>
> So today a multiplicity is documentation that the compiler carries as far as
> its own AST and no further. This chapter documents the intended design; see
> [Where this actually stands](#where-this-actually-stands) for the state of the
> implementation.
>
> One opt-in exception exists and is **off by default**: `monad check --affine`
> runs an experimental *affine-by-default* rule alongside the ordinary
> diagnostics. It is not an enforcement of the table below — it reads an
> unannotated binder as `Affine`, not `Many` — so it lives on the experiment's
> own terms, described in [The affine experiment](#the-affine-experiment).

## Overview

Every variable in Monad is meant to carry a **multiplicity** controlling how many
times it may be used:

| Multiplicity | Syntax | Constraint | Meaning |
|-------------|--------|------------|---------|
| `Many` (ω) | `x : A` | none | Default; usable any number of times |
| `Linear` (1) | `!x : A` | exactly once | Cannot be copied or discarded |
| `Affine` (≤1) | `?x : A` | at most once | Usable 0 or 1 times |
| `Zero` (0) | `%x : A` | never at run time | Erased; type-level only |

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

## Usage Rules (design)

The intent is that these are checked at compile time, with no run-time overhead:

1. **Linear** (`!x`): must appear **exactly once** in the body
2. **Affine** (`?x`): must appear **at most once**
3. **Many** (`x`): unrestricted
4. **Zero** (`%x`): must not appear in run-time position at all

```monad
def ok (!x : I64) : I64 := x           // intended: passes
def unused (!x : I64) : I64 := 42      // intended: fails — never used
def overused (!x : I64) : I64 := x + x // intended: fails — used twice
def affine_ok (?x : I64) : I64 := 42   // intended: passes
def many_ok (x : I64) : I64 := x + x   // passes
```

Today **all five compile**, in both implementations — unless `--affine` is
passed, in which case exactly one row changes: the *unannotated* one.
`many_ok`'s `x + x` becomes a `copy_required` error unless `Copy I64`
resolves in that file's closure, because under the flag an unannotated
binder is affine, not `Many`. The annotated rows are untouched by the
flag — the annotation is dropped at `pt_lam` before the rule ever sees
it (see [The affine experiment](#the-affine-experiment)), so `unused`
and `overused` compile there too.

## Where This Actually Stands

Parsing is done. What is left is everything after it:

1. **Lowering keeps nothing.** The parser records a multiplicity on each
   parameter, and the pass that builds the core `pi`/`lam` terms has nowhere to
   put it — those terms have no multiplicity field. It is dropped there.
2. **Usage checking**, in both implementations. Counting machinery was written
   against an earlier version of the host's type checker. That checker has been
   replaced and the current one does not call it — every function type it builds
   uses `Many`. (An opt-in replacement exists —
   [the affine experiment](#the-affine-experiment); it is off by default,
   so this is still the state of the default path.)
3. **Codegen use**, in the self-hosted backend. Nothing consumes multiplicities.

So the annotations are documentation that the compiler carries as far as its own
parse tree.

## The affine experiment

The design above has a staged implementation in this tree. It is deliberately
**not** wired into the default path; it is reachable
through a flag, and only on the self-hosted CLI — the bootstrap host rejects
`--affine` as an unknown argument.

```text
monad check --affine <path>...
```

A rejection from the rule is an ordinary type error: it renders through the same
renderer and fails `check` the same way, so the flag *is* the switch between
"these annotations are documentation" and "these annotations are enforced".
Nothing fires without it.

What the flag turns on:

- **`Copy`** (`lang/src/typecheck/copy_class.mo`, with the class itself in
  `init/src/copy.mo`) decides which types may still be shared. Resolution is
  *fail-closed*: where it cannot tell, it denies sharing rather than granting it,
  because the opposite default would quietly disable the whole check. Instances
  are unconstrained — `Copy (Borrow A)` resolves, `Copy (Pair A B)` does not.
- **Usage counting** (`lang/src/typecheck/usage.mo`) counts each binder's uses,
  distinguishing one that takes ownership from one that only reads.
- **The affine rule** (`lang/src/typecheck/affine.mo`) combines the two into the
  *effective multiplicity* of a binder: `1` if annotated `!x` or the type is
  `#[linear]`, `0` if annotated `%x`, `ω` if `Copy A` resolves, and `≤1`
  otherwise. The last case is the departure from the table above, and it is the
  whole experiment: **an unannotated binder is affine, not `Many`**, so a second
  use of an ordinary parameter is an error under this flag. That reading is
  guarded by a test, because reading the parser's `Many` default as ω would pass
  every program while still looking like it worked.
- **Drop points** (`lang/src/typecheck/dropck.mo`) computes *where* a release
  would go. It is pure and unwired, and its per-branch walk measures ~90 s over
  the compiler's own closure — a recorded deferral, not a live path.

Three diagnostics come out of it, named for the fix rather than the count: a
binder used more than once but *owned* at most once wants a borrow or a `Copy`
instance; a binder owned twice really is moved twice and wants a rewrite; a
`!x` never used is the one case affine's weakening does not excuse.

Two caveats matter for reading anything the experiment reports. **Nothing frees
memory yet.** Codegen still emits no `monad_release`, `Borrow` is boxed rather
than erased, and `String` cannot be owned, so the GC described in
[Compiling and Running](./compiling.md#memory) is not going anywhere on this
branch. And the rule only sees the binders it can see: `!` and `%` are dropped
at `pt_lam` in some positions and macro-synthesized parameters are hardcoded to
`Many`, so the `Linear` and `Zero` rows of the table have no real-code coverage
at all — every number the experiment reports is about the affine row.

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
| Unrestricted | `Many` (default) | `Copy` types |
| Linear (exactly once) | `!x` | move semantics |
| Affine (at most once) | `?x` | `Drop` types |
| Erased | `%x` | (no equivalent) |
| Enforcement | type checker | borrow checker |
| Run-time cost | none | none |

## Roadmap

Roughly in order:

- ~~Wire `multiplicity_prefix` into the self-hosted definition- and
  lambda-parameter parsers~~ — done, destructured parameters included
- Carry the multiplicity through lowering, so `pi` and `lam` can hold one
- Reinstate usage checking in the current type checker
- Track let-bound variables, not just parameters
- Check arrow multiplicity at application sites
- Enforce multiplicities on constructor fields under pattern matching
- Subsumption: `Many` should subsume `Linear` and `Affine`
- Drive codegen's memory reclamation from multiplicities, replacing the GC
- `noalias` attributes on linear parameters in the emitted LLVM IR

[The affine experiment](#the-affine-experiment) covers part of this list and
none of the last two entries. It counts uses and it resolves sharing
(`Copy` plays the part of subsumption, from the other side: everything is
affine unless `Copy` says otherwise), but it never touches lowering — it reads
the multiplicity off the parse tree as it stands — and it computes drop points
without emitting anything from them.

Next, we'll explore **concurrency**.
