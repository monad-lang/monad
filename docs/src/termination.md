# Termination Checking

Monad's design calls for recursive definitions to be checked for termination.

> [!WARNING]
> **The self-hosted compiler performs no termination analysis.** `#[terminating]`
> and `#[partial]` parse and are ignored; a definition that loops forever checks
> clean. The [bootstrap host](./bootstrap-host.md) *does* enforce this, on every
> `def`, by default.
>
> That makes this the divergence most likely to bite you: code that checks clean
> with `monad check` can be rejected by `monad-rs check` — which is what the
> project's own pre-commit hook and CI run.

## Why It Exists

In a dependently typed language, the type checker evaluates terms. A
non-terminating definition would make the checker loop, and — because a looping
definition can be given any type — would make the logic unsound. Only
definitions that provably terminate can be unfolded safely.

## The Rule: Structural Recursion

A recursive call is accepted when at least one argument is a **structural
subterm** of the corresponding parameter: something bound by pattern matching
*inside* that parameter, and therefore strictly smaller.

This is accepted, because `tail` comes out of destructuring `xs`:

```monad
def length {A : Type} (xs : List A) : I64 :=
    match xs {
        empty => 0,
        cons a tail => 1 + length tail
    }
```

So is this, recursing on `m` from `succ m`:

```monad
def double_nat (n : Nat) : Nat :=
    match n {
        zero => Nat.zero,
        succ m => Nat.succ (Nat.succ (double_nat m))
    }
```

Mutual recursion works too, as long as each step is structural:

```monad
def is_even (n : Nat) : Bool :=
    match n {
        zero => true,
        succ m => is_odd m
    }

def is_odd (n : Nat) : Bool :=
    match n {
        zero => false,
        succ m => is_even m
    }
```

## What Gets Rejected

Arithmetic recursion is the common case. `n - 1` is a *computed* value, not a
subterm of `n`, so the check cannot see that it decreases:

```monad,ignore
def countdown (n : I64) : I64 :=
    if n == 0 then 0 else countdown (n - 1)
```

Under the self-hosted compiler this checks clean. Under the bootstrap host:

```text
error: Termination check failed for 'countdown'
  Recursive call: (countdown (... n 1i64))
  Argument(s) (...) are not structural subterms of parameter(s) (n)
    — add #[terminating] if this function is well-founded
```

The error prints the recursive call after elaboration, so the subtraction shows
up as its desugared `Sub` instance dispatch. That is noisy, but the parameter
names at the end tell you what it wanted.

## The Attributes

Two attributes turn the check off for one definition. Both parse in the
self-hosted compiler, where they are no-ops, and both are honoured by the host —
so writing them is forward-compatible and costs nothing.

### `#[terminating]`

"I have checked this by hand; it is well-founded." Use it when the recursion
really does decrease but not structurally — the arithmetic case above.

```monad
#[terminating]
def factorial (n : I64) : I64 :=
    if n == 0
    then 1
    else n * factorial (n - 1)
```

### `#[partial]`

"This may not terminate, and that is intended." Use it for interpreters, driver
loops, and search that may not converge.

```monad
#[partial]
def spin (n : I64) : I64 := spin n
```

The difference is what you are telling the reader: `#[terminating]` is a claim
about the code, `#[partial]` is an admission. Neither is verified, so an
incorrect `#[terminating]` will hang the host's checker if the definition is ever
unfolded during type checking.

## Practical Guidance

Write as though the check were on, even though the self-hosted compiler does not
run it:

- Recursing over `List`, `Nat`, or any inductive type usually just works —
  recurse on what the `match` bound, not on something you computed.
- Counting down an `I64` needs `#[terminating]`. This is by far the most common
  case.
- Converting the loop counter to `Nat` makes the recursion structural and removes
  the need for the attribute, at the cost of unary arithmetic.
- The standard library uses both attributes freely; they are not a code smell.

The payoff is that your code keeps working under both implementations, and keeps
working when the self-hosted compiler gains the check.

## Limitations

Where the check *is* implemented, it is deliberately simple:

- No termination inference beyond the structural rule — no size measures, no
  lexicographic orderings, no user-supplied well-founded relations.
- The attributes are trusted, not verified.
- Accumulator-passing recursion where the decreasing argument is not the
  structurally-matched one is not recognised.

Next, we'll look at **linear types**.
