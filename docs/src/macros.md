# Macros and Derive

Monad has a real macro system: `defmacro`, `quote`, and compile-time reflection.
It is not a bolted-on preprocessor — `#[derive]` is implemented *in Monad*, in
`std/derive.mo`, on top of these primitives. The compiler only supplies a few
reflection intrinsics.

This is the one area where the self-hosted compiler is *ahead* of the
[bootstrap host](./bootstrap-host.md): term macros work here and not there.
`#[derive …]` is the reverse, and is marked below.

## Quoting

`quote { ... }` turns a term into data instead of evaluating it:

```monad,ignore
quote { 1 + 2 }
```

## Defining a Macro

There are two forms of `defmacro`.

**Term macros** produce an expression:

```monad,ignore
defmacro double x := x + x
def y : I64 := double! 9
```

> **Self-hosted only.** Term macros are rejected by the bootstrap host, which
> fails with *"macro `double` did not return a Term value"*. Declaration macros
> (below) work on both.

**Declaration macros** produce a list of top-level declarations, using a
`decls { ... }` template:

```monad,ignore
defmacro derive_lens T := decls {
    reflect_type_info! T derive_lens_meta
}
```

A macro is invoked with a `!` suffix — `double! 9`, `derive_lens! Point`.

## Reflection as Data

The interesting half is `reflect_type_info!`, a compiler intrinsic that hands a
type's structure to an **ordinary Monad function** as an ordinary value. That
function computes a `List Decl`, and the compiler splices the result back into
the program.

The data model lives in `init/meta.mo`:

```monad,ignore
type FieldInfo {
    field_info (name : String) (typ : Expr) (attrs : List String)
}

type CtorInfo {
    ctor_info (name : String) (fields : List FieldInfo)
}

type TypeInfo {
    type_info (name : String) (ctors : List CtorInfo)
}
```

and a deliberately minimal mirror of the compiler's own term and declaration
surface:

```monad,ignore
type Expr {
    e_var (name : String),
    e_str (value : String),
    e_int (value : I64),
    e_bool (value : Bool),
    e_app (func : Expr) (arg : Expr),
    e_lam (param_name : String) (param_typ : Expr) (body : Expr),
    e_if (cond : Expr) (then_ : Expr) (else_ : Expr),
    e_match (scrutinee : Expr) (arms : List MatchArm),
    e_ctor (ctor_name : String) (args : List Expr)
}

type Decl {
    d_def (name : String) (params : List Param) (ret_typ : Expr) (body : Expr),
    d_instance (class_name : String) (target_typ : Expr) (methods : List Decl),
    d_error (message : String)
}
```

The payoff is that a "macro" is a normal function you can read, test, and debug.
A derive backend is written with `List.map`, `match`, and recursion — not with
quasi-quotation gymnastics:

```monad,ignore
pub def derive_lens_meta (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            match ctors {
                cons c tail =>
                    match tail {
                        empty => lens_decls_for_ctor type_name c,
                        cons _ _ => List.empty
                    },
                empty => List.empty
            }
    }
```

`d_error` is the escape hatch: returning one anywhere in the list fails macro
expansion with that message, which is how a derive rejects a type it cannot
handle.

## `#[derive ...]`

> **Works on both compilers.** The self-hosted compiler bridges the attribute
> to the same `std/derive.mo` macros the host calls
> (`derive_bridge_decls`, `lang/src/typecheck/macro_queue.mo`), so
> `#[derive BEq BOrd Debug Lens]` generates its instances either way. What you
> must do on both is *import the backend* — `#[derive BEq]` dispatches by name
> to a macro, and a macro that is not in scope is "macro `derive_beq` not
> found".

The attribute form dispatches to those macros by name. Arguments are
**space-separated bare names** — not `#[derive(BEq, BOrd)]`:

```monad
use std::derive {derive_beq, derive_bord, derive_debug, derive_lens}
use init::optics {Lens, set, view}
use std::debug {Debug}

#[derive BEq BOrd Debug Lens]
struct Point {
    x : I64,
    y : I64
}

#[test]
def test_equality : Bool :=
    let p1 : Point := { x := 1, y := 2 } in
    let p2 : Point := { x := 1, y := 2 } in
    let p3 : Point := { x := 1, y := 3 } in
    p1 == p2 && Bool.not (p1 == p3)

#[test]
def test_debug : Bool :=
    let p : Point := { x := 1, y := 2 } in
    Debug.debug p == "Point { x: 1, y: 2 }"

#[test]
def test_lens : Bool :=
    let p : Point := { x := 1, y := 2 } in
    view Point.x p == 1 && view Point.y (set Point.y 9 p) == 9
```

### What can be derived

| Target | Generates | Works on |
|--------|-----------|----------|
| `BEq` | structural equality | any type |
| `BOrd` | ordering, following declaration order | any type |
| `Debug` | Rust-style debug representation | any type |
| `Lens` | one `Lens` per field | single-constructor types only |

Derives work on multi-constructor types too:

```monad
use std::derive {derive_beq, derive_bord, derive_debug}
use std::debug {Debug}

#[derive BEq BOrd Debug]
type Suit {
    hearts,
    spades,
    number (rank : I64)
}

#[test]
def test_suit : Bool :=
    Suit.number 7 == Suit.number 7
        && Suit.hearts < Suit.spades
        && Debug.debug (Suit.number 7) == "Suit::number { rank: 7 }"
```

`Lens` is deliberately absent there — a lens focuses on one field of one shape.
For sum types, `init.optics` provides `Prism` instead.

### You must import the backend

`#[derive BEq]` dispatches to `derive_beq` by name, so the module defining it
has to be in scope:

```monad,ignore
use std::derive {derive_beq, derive_bord, derive_debug, derive_lens}
```

The compiler's unused-import analysis does not see macro-name dispatch as a
reference, so it will report these as unused. Keep them — removing the import
makes `#[derive BEq]` fail with "macro `derive_beq` not found".

## Writing Your Own Derive

Because a derive is just a `TypeInfo -> List Decl` function plus a two-line
`defmacro`, adding one is ordinary programming. `lang/cli.mo` does exactly this
for `#[derive_cli]`, generating an argv parser from a struct's fields and their
`#[arg]` annotations — the field attributes come through in `FieldInfo.attrs`.

## Limitations

- Only the four targets above are wired into the `#[derive ...]` attribute; your
  own macros are called with `!` syntax.
- `Expr` is not a full mirror of the compiler's `Term`: `Pi`, `Forall`, `Sort`,
  `Ann`, and `Quote` are excluded, because no shipped derive needs them.
- `TypeInfo` does not carry a type's generic parameters, per-field defaults, or
  field multiplicities.

`cli/src/main.mo` hand-writes its own argv parser rather than using
`#[derive_cli]`, and stays free of macro syntax on purpose: the self-hosted
parse/scope/typecheck suite re-parses that file through the self-hosted
pipeline, and it is the one file where an attribute would be load-bearing for
the bootstrap itself. `cli/src/tests/cli_derive_tests.mo` is the derived
equivalent.

## Summary

- `defmacro` defines term macros and declaration macros; `quote { }` makes syntax data
- `reflect_type_info!` passes a type's structure to an ordinary Monad function
- `#[derive BEq BOrd Debug Lens]` — space-separated, and the backend must be imported
- Derives are library code in `std/derive.mo`, not compiler built-ins
- Both compilers expand `#[derive …]`; term macros (`double!`) are
  self-hosted-only, which is the one divergence left in this area

Next, we'll look at **linear types**.
