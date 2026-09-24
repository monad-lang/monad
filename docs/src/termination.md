# Termination Checking

Monad checks recursive definitions for termination. The check is structural,
and both compilers run it, on every `def`, by default.

> [!WARNING]
> **The check is structural, and both compilers enforce it.** A recursive call
> is accepted only when one of its arguments is a subterm bound by pattern
> matching *inside* the corresponding parameter, so recursion over `List`, `Nat`
> or any inductive type is fine while counting down an `I64` is not — that needs
> `#[terminating]` or `#[partial]`. It is the case you are most likely to hit.

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

Both compilers reject it, in the same words — below is the host's output, with
the elaborated call elided:

```text
error: Termination check failed for 'countdown'
  Recursive call: (countdown (... n 1i64))
  Argument(s) (...) are not structural subterms of parameter(s) (n)
    — add #[terminating] if this function is well-founded
```

The error prints the recursive call *after elaboration*, so the subtraction
arrives as its desugared `Sub` dispatch — and the two compilers spell that
dispatch differently (the host inlines the dictionary into a `match`, this
compiler keeps it as a call), so the middle line is the one line of the message
that differs between them. It is noisy either way, but the parameter names at
the end tell you what it wanted.

## The Attributes

Three attributes turn the check off for one definition, in both compilers.
They are the only way to write recursion the structural rule cannot see.

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

### `#[decreasing <measure>]`

`#[terminating]`, plus a note to the reader of *which* argument is meant to be
shrinking. Use it where "it terminates" alone would leave the next reader
guessing.

```monad
#[decreasing n]
def fact_acc (n : I64) (acc : I64) : I64 :=
    if n == 0 then acc else fact_acc (n - 1) (n * acc)
```

The named measure is **not checked** — not against the parameter list, not
against the recursive calls. It is documentation the compiler agrees to accept,
and it exempts the definition exactly as `#[terminating]` does.

The difference between the three is what you are telling the reader:
`#[terminating]` is a claim about the code, `#[decreasing x]` is the same claim
with its reason named, and `#[partial]` is an admission. Nothing verifies any of
them, so an incorrect `#[terminating]` passes both compilers — and a definition
the host's checker unfolds while type-checking will hang it.

## Practical Guidance

The rule is narrow, so most recursion falls into one of three cases:

- Recursing over `List`, `Nat`, or any inductive type usually just works —
  recurse on what the `match` bound, not on something you computed.
- Counting down an `I64` needs `#[terminating]`. This is by far the most common
  case.
- Converting the loop counter to `Nat` makes the recursion structural and removes
  the need for the attribute, at the cost of unary arithmetic.
- The standard library uses these attributes freely; they are not a code smell.

Code written this way is accepted by both compilers, and stays accepted if the
checker ever grows stricter than the structural rule.

## Limitations

In both implementations the check is deliberately simple:

- No termination inference beyond the structural rule — no size measures, no
  lexicographic orderings, no user-supplied well-founded relations.
- The attributes are trusted, not verified.
- Accumulator-passing recursion where the decreasing argument is not the
  structurally-matched one is not recognised.

Next, we'll look at **linear types**.
