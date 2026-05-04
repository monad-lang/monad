# Linear Types

Monad supports **linear** and **affine** types for resource-safe programming, inspired by Rust's ownership system and Idris's Quantitative Type Theory (QTT).

## Overview

Every variable in Monad has a **multiplicity** that controls how many times it can be used:

| Multiplicity | Syntax | Constraint | Meaning |
|-------------|--------|------------|---------|
| `Many` (ω) | `x : A` | No restriction | Default; can be used any number of times |
| `Linear` (1) | `!x : A` | Exactly once | Cannot be copied or discarded |
| `Affine` (≤1) | `?x : A` | At most once | Can be used 0 or 1 time |

## Syntax

Multiplicity is declared with a prefix on the parameter name:

```monad
// Many (default) — no prefix
def add (a : I64) (b : I64) : I64 := a + b

// Linear — must be used exactly once
def process (!handle : FileHandle) : IO Unit := close handle

// Affine — may be used 0 or 1 time  
def log (?msg : String) : IO Unit :=
    match msg {
        some s => println s,
        none => pure ()
    }
```

Multiplicity annotations work in all parameter positions:

```monad
// Lambda parameters
\!x : I64 => x

// Implicit parameters
{!A : Type}

// Function definitions
def f (!x : I64) (?y : I64) (z : I64) : I64 := x
```

## Usage Rules

The type checker enforces these rules at compile time (no runtime overhead):

1. **Linear** (`!x`): Must appear **exactly once** in the function body
2. **Affine** (`?x`): Must appear **at most once** (0 or 1 occurrence)
3. **Many** (`x`): No restriction — can be used 0, 1, or many times

```monad
// ✓ Passes: x used exactly once
def ok (!x : I64) : I64 := x

// ✗ Fails: x not used
def unused (!x : I64) : I64 := 42

// ✗ Fails: x used twice
def overused (!x : I64) : I64 := x + x

// ✓ Passes: affine can be unused
def affine_ok (?x : I64) : I64 := 42

// ✓ Passes: many can be used many times  
def many_ok (x : I64) : I64 := x + x + x
```

## Nested Lambdas and Scope

Linear type checking is **per-function-boundary**. Each lambda's linear parameters are verified independently:

```monad
// ✓ Passes: x used in outer scope (after inner lambda)
def outer (!x : I64) : I64 :=
    let f := \y : I64 => y in
    x

// ✗ Fails: x used twice (once inside inner lambda, once outside)
def bad (!x : I64) : I64 :=
    (\y : I64 => x) + x
```

## Current Limitations

- Pattern matching with linear constructor fields is not yet enforced
- Arrow multiplicity (`Pi.mult`) is not yet checked at application sites
- Let-bound variables are not yet tracked for linearity
- No subtyping/subsumption rules (Many subsumes Linear/Affine)

## Comparison to Rust

| Concept | Monad | Rust |
|---------|-------|------|
| Unrestricted | Many (default) | `Copy` types |
| Linear (exactly once) | `!x` | Move semantics |
| Affine (at most once) | `?x` | `Drop` types |
| Enforcement | Type checker only | Borrow checker |
| Runtime cost | None | None |

## Future Work

- Subtyping: Many subsumes both Linear and Affine
- Pattern matching with linear constructor fields
- LLVM codegen: `noalias` attributes for linear parameters
- In-place update optimization for linear values
