# Reference

A quick reference for Monad syntax and built-in features. Anything marked
**not implemented** parses in some form but does not work — see the
[Maturity Matrix](./maturity.md).

## Keywords

```text
def, defmacro, let, in, use, open, class, struct, instance, type,
fn, ꟛ, match, if, then, else, infix, return, for, do, quote, with,
pub, priv
```

Reserved names: `Type`, `Prop`, `Pred`, `Sort`.

`for` is reserved but has no grammar rule — there is no loop syntax.

## Comments

```monad
// Single line comment

/* Multi-line
   comment */

def answer : I64 := 42
```

## Docstrings

```monad
/// Documentation for the following declaration
def greet (name : String) : String := "Hello, " ++ name
```

Docstrings are stored on declarations and retained through module loading, so
the [bootstrap host](./bootstrap-host.md)'s LSP server can surface them.

## Definitions

**Every `def` requires a type annotation.** There is no top-level inference.

```monad
use io {}
open IO {println}

// Basic function
def add (a : I64) (b : I64) : I64 := a + b

// Shared annotation for same-typed parameters
def mul (a b : I64) : I64 := a * b

// Implicit parameters
def identity {A : Type} (x : A) : A := x

// Class constraints
def twice [Add A] (x : A) : A := Add.add x x

// Field destructuring in a parameter
struct Coord { fst : I64, snd : I64 }
def sum_coord ({fst, snd} : Coord) : I64 := fst + snd

// Do-block body (alternative to `:=`)
def steps : IO Unit {
    println "one";
    println "two"
}
```

A parameter list can also be written as one brace block, which is the only
spelling that allows defaults:

```monad
def scale {factor : I64 := 2, p : I64} : I64 := factor * p
```

The block is all-or-nothing: no further `(…)` groups may follow it, and it takes
no multiplicity prefixes. A one-parameter block needs the `:=` default or a
trailing comma — `def f {x : I64} : I64 := x` is read as an implicit *type*
binder clause instead.

The default is applied by **both** compilers: omitting a parameter that
declares one is accepted, and the declared default stands in for it, so
`def scale {factor : I64 := 2, p : I64}` makes `scale { p := 4 }` equal 8.
See [The Bootstrap Host](./bootstrap-host.md) for what is still host-only.

## Visibility

```monad
pub def exported : I64 := 1
priv def internal : I64 := 2
def package_private : I64 := 3
```

Package-private is the default. `pub use module {*}` re-exports an import.

## Lambda Expressions

Three equivalent spellings:

```monad
def a : I64 -> I64 := fn x => x + 1
def b : I64 -> I64 := \ x => x + 1
def c : I64 -> I64 := ꟛ x => x + 1
```

A lambda gets its parameter type from the definition's signature, or from an
explicit parenthesised annotation:

```monad
def d : I64 -> I64 := fn (x : I64) => x + 1
```

## Backtick Operators — not implemented

```monad,ignore
x `f` y   // intended: f x y
```

The parser recognises the backtick form, but the expression parser only reduces
symbolic operators, so this never becomes an application. Write `f x y`.

## Let Expressions

One `let` binds one name; chain them for several:

```monad
def one : I64 := let x := 10 in x + 1

def two : I64 :=
    let x := 10 in
    let y := 20 in
    x + y

def three : I64 := let x : I64 := 10 in x + 1
```

Several bindings may share one `let`, separated by `;`. Each may carry its own
annotation, and each sees the bindings before it:

```monad
def multi : I64 := let x := 10; y : I64 := 20 in x + y
```

The `;` is required here; the bootstrap host also accepts it omitted. The form
desugars to nested lambdas, so the bindings are sequential and non-recursive.

## Literals

### Numeric

```monad
def a : I64 := 42        // I64 (default)
def b : I8 := 42i8
def c : I16 := 42i16
def d : I32 := 42i32
def e : U8 := 42u8
def f : U32 := 42u32
def g : U64 := 42u64
def h : F64 := 3.14      // F64 (default)
def i : F32 := 3.14f32
def j : I64 := 0xFF      // hex
def k : U32 := 0xFFu32   // hex with suffix
```

There are **no** binary or octal literals, and **no** `_` digit separators.

### Strings and characters

```monad
def s : String := "hello\n"
def raw : String := r"C:\Users\monad\main.mo"
def raw_hash : String := r#"{"name": "monad"}"#
def raw_hash3 : String := r###"a "## b"###
```

```monad
def c : Char := 'M'
def nl : Char := '\n'
def lam : Char := 'λ'
```

A char literal holds exactly one Unicode codepoint and takes the same escapes as
a string (`\n \r \t \b \f \\ \/ \" \'`). **`\u{XXXX}` is not accepted
self-hosted** — write the character itself; the bootstrap host does accept it.

`Char` has no operations of any kind — no equality, no `ToString`, no `Char.*`
functions — so a `Char` can be written, typed and passed, but not inspected.

Raw strings take their body verbatim — no `\` escape processing. The closing
delimiter is `"` followed by the same number of `#` as the opener, so escalating
the hash count lets any content be embedded.

Escapes in ordinary strings: `\n \r \t \b \f \\ \/ \" \' \u{XXXX}`, plus
backslash-newline line continuation. There are no octal escapes.

### Lists and tuples

```monad
def xs : List I64 := [1, 2, 3]
def pair : Pair I64 String := (1, "two")
```

List literals desugar through `FromListLiteral`; tuples desugar to right-nested
`Pair.pair`.

## Type Annotations

Any term can be annotated:

```monad
def x : I64 := (42 : I64)
def y : I64 := (42 : _)
```

## Field Access

```monad
struct Inner { v : I64 }
struct Outer { inner : Inner }

def get (o : Outer) : I64 := o.inner.v
```

Dot notation on a value is **field access only**. There is no UFCS method
dispatch: `s.length` does not mean `String.length s`, and naming something that
is not a declared field is an error. Use the qualified name.

## Match Expressions

```monad
type Shape {
    circle (radius : I64),
    rectangle (width : I64) (height : I64)
}

def area (s : Shape) : I64 :=
    match s {
        circle r => r * r,
        rectangle w h => w * h
    }
```

Patterns are one constructor deep. `_` is a wildcard. **Not supported**: nested
constructor patterns, literal patterns, guards, or-patterns, and exhaustiveness
checking.

Struct values also match on field names:

```monad
struct Point3 { x : I64, y : I64, z : I64 }

def xy (p : Point3) : I64 :=
    match p {
        {x, y, ..} => x + y
    }
```

## If Expressions

```monad
def sign (n : I64) : I64 := if n < 0 then 0 - 1 else 1
```

## Do Notation

```monad
use io {}
open IO {println}

def a : IO Unit := do {
    println "one";
    println "two"
}

def b : IO Unit {
    println "one";
    println "two"
}
```

| Statement | Syntax | Desugars to |
|-----------|--------|-------------|
| Bind | `let x <- action` | `Monad.bind action (fn x => ...)` |
| Let | `let x := value` | `let x := value in ...` |
| Return | `return value` | `Monad.pure value` |
| Expression | `expr` | `Monad.bind expr (fn _ => ...)` |

Separate statements with `;`.

## Struct Values

```monad
struct Point { x : I64, y : I64, z : I64 := 0 }

def p : Point := { x := 3, y := 4 }
def q : Point := { p with x := 10 }
```

Struct literals are not inferrable on their own — they need a type from context.

## Attributes

Attributes are written `#[name arg1 arg2]` — **space-separated arguments, no
parentheses or commas**:

```monad,ignore
#[native print_str]         // implemented in Rust; no body follows
#[test]                     // a test, run by `monad test`
#[terminating]              // assert well-foundedness; skip the termination check
#[partial]                  // this definition may not terminate
#[derive BEq BOrd Debug]    // generate instances via macros
#[derive_cli]               // generate an argv parser
#[cfg ...]                  // conditional compilation
```

Attributes come before visibility: `#[test] pub def ...`, not
`pub #[test] def ...`.

## Native Functions

```monad,ignore
#[native print_str]
def IO.println (s : String) : IO Unit

#[native "num_add"]
def I64.add (a b : I64) : I64
```

A native has no body. The attribute's argument is the runtime's identifier,
which need not match the Monad-side name.

## Infix Operators

```monad,ignore
infix (operator) := functionName
```

### Built-in Operators

| Operator | Precedence | Associativity | Bound to |
|----------|------------|---------------|----------|
| `\|>` | 5 | Left | `apply_fun` |
| `<\|` | 5 | Right | `fun_apply` |
| `>>=` | 10 | Right | `Monad.bind` |
| `.` | 12 | Right | path / field access (not bindable) |
| `<*>` | 15 | Left | — |
| `<\|>` | 20 | Left | — |
| `\|\|` | 25 | Right | `Bool.or` |
| `&&` | 30 | Right | `Bool.and` |
| `==` | 40 | Left | `BEq.beq` |
| `<` | 40 | Left | `BOrd.lt` |
| `>` | 40 | Left | `BOrd.gt` |
| `!=`, `=`, `<=`, `>=` | 40 | Left | — |
| `++` | 50 | Right | `Append.append` |
| `@` | 50 | Right | — |
| `>>`, `<<` | 60 | Left | — |
| `+` | 65 | Left | `HAdd.add` |
| `-` | 65 | Left | `Sub.sub` |
| `*` | 70 | Left | `HMul.mul` |
| `/` | 70 | Left | `Div.div` |

Operators marked — have a precedence but no binding in the prelude, so using
them is an error until you bind one yourself. `!=`, `<=`, and `>=` are commented
out in `init/prelude.mo` pending default-method support on `BEq`/`BOrd`.

`@` is deliberately left free for libraries to claim.

Note that `init/lib.mo` rebinds `infix (+) := I64.add`, shadowing the prelude's
class-based `HAdd.add` where `init` is in scope.

## Type Definitions

```monad
type Colour {
    red,
    green,
    blue
}

type Shape {
    circle (radius : I64),
    rectangle (width : I64) (height : I64)
}

type Tree A {
    leaf,
    node (left : Tree A) (value : A) (right : Tree A)
}

type Empty {}
```

A type can be placed in a universe explicitly, which is how propositions are
declared:

```monad
type Truthy : Prop {
    yes
}
```

## Struct Definitions

```monad
struct Point {
    x : I64,
    y : I64,
    z : I64 := 0,     // default value
    !name : String,   // linear field (`!`) or affine (`?`)
    ?tag : String
}
```

Multiplicity annotations are not enforced — see [Linear Types](./linear-types.md).

## Class Definitions

```monad
class Container (F : Type -> Type) {
    def wrap : A -> F A
    def size (fa : F A) : I64
}

class [Container F] Sized (F : Type -> Type) {
    def is_empty (fa : F A) : Bool
}

class Convert A B {
    def convert : A -> B
}
```

A class parameter may have a default (`class FromListLiteral (L : Type -> Type := List)`).
Methods may have default bodies, but an instance still has to list every method
it wants — empty instance bodies do not parse.

## Instance Definitions

```monad
type Colour { red, green, blue }

instance ToString Colour {
    def to_string (c : Colour) : String :=
        match c {
            red => "red",
            green => "green",
            blue => "blue"
        }
}

instance {A : Type} Append (List A) {
    def append (a b : List A) : List A := List.append a b
}
```

Instances may be named — one bare identifier self-hosted, a dotted path on the
bootstrap host:

```monad
type Colour2 { red2, green2 }

instance ColourEq : BEq Colour2 {
    def beq (a b : Colour2) : Bool := true
}
```

The name is recorded and nothing reads it: no syntax selects an instance by name
in either implementation.

## Multiplicities

Struct fields accept `!` (linear), `?` (affine) and `%` (erased) in both
implementations:

```monad
struct Res { !handle : String, ?tag : String, size : I64 }
```

Parameters accept them too — on definitions and on typed lambda parameters:

```monad
def f (!linear : I64) (?affine : I64) (%erased : I64) (many : I64) : I64 :=
    linear + affine + erased + many

def g : I64 -> I64 := fn (!x : I64) => x
```

The prefix applies to the whole group, so `(!x y : I64)` makes *both* names
linear. A destructured parameter takes one as well — `(!{fst, snd} : Coord)` —
though that spelling is self-hosted only; the bootstrap host rejects it.

> **Nothing enforces multiplicities in either implementation.** Lowering drops
> the annotation and every binder becomes `Many` — see
> [Linear Types](./linear-types.md).

## Modules

```monad
use io {IO}          // import, naming what you need
use io {*}           // import everything
use io {}            // load for qualified access and instances only
open IO {println}    // drop the prefix for these names
```

A bare `use io` with no braces parses but is deprecated. See
[Modules and Imports](./modules.md).

## Dot Macro

`x.y.z` is resolved at compile time. If `x` is a module path it becomes a single
qualified name (`List.append`); if `x` is a local value it becomes struct field
access. The disambiguation happens during lowering.

## Macros

`defmacro`, `quote { ... }`, macro calls (`name! args`), and compile-time
reflection are real and are how `#[derive]` is implemented. See
[Macros and Derive](./macros.md).

## Constraint Solver

Recursive instance constraints (e.g. `instance [Show A] Show (List A) { ... }`)
are handled by a constraint solver that uses a visiting set to detect cyclic
constraint dependencies. Resolution happens at evaluation time, so an
unsatisfiable constraint surfaces as a run-time `unresolved global:` error
rather than a check failure.

## Standard Library

The prelude types and classes are listed in [Types](./inductive-types.md#built-in-types)
and [Type Classes](./type-classes.md#the-standard-classes). For the module map
and each module's contents, see [The Standard Library](./stdlib.md).

For scale: the standard library is about 440 public definitions, 35 classes, and
132 instances across `init/` and `std/`, excluding their test modules.

## CLI

```bash
monad compile file.mo -o "$PWD/out"  # compile to a native binary
monad run file.mo                    # compile and execute
monad eval file.mo                   # interpret (pure programs only)
monad check file.mo                  # type-check, no execution
monad check init std lang            # directories are expanded recursively
monad test file.mo                   # compile and run this file's #[test] defs
monad test                           # the mote containing the working directory
monad test --workspace               # every mote in the enclosing workspace
monad pretty file.mo                 # parse and pretty-print
monad version                        # the git commit this binary was built from
```

`compile` and `run` take `--verbose`/`-v`, `--debug`/`-g` and `--release`;
`eval`, `check` and `test` take `--verbose`/`-v`. Debug info is on unless you
pass `--release`. Flags may go before or after the paths, `--output=NAME` is not
recognised (use a space), and a **relative** output name lands in
`/tmp/monad_out_<pid>`. See [Compiling and Running](./compiling.md), and
[The Bootstrap Host](./bootstrap-host.md) for the Rust implementation's
additional commands.
