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

Today **all five compile**, in both implementations.

## Where This Actually Stands

Parsing is done. What is left is everything after it:

1. **Lowering keeps nothing.** The parser records a multiplicity on each
   parameter, and the pass that builds the core `pi`/`lam` terms has nowhere to
   put it — those terms have no multiplicity field. It is dropped there.
2. **Usage checking**, in both implementations. Counting machinery was written
   against an earlier version of the host's type checker. That checker has been
   replaced and the current one does not call it — every function type it builds
   uses `Many`.
3. **Codegen use**, in the self-hosted backend. Nothing consumes multiplicities.

So the annotations are documentation that the compiler carries as far as its own
parse tree.

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

Next, we'll explore **concurrency**.
