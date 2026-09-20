# Monad Language Developer Guide

This document explains how to modify the Monad language codebase and write correct Monad code.

**IMPORTANT**: All development changes (code, tests, modules) should happen in the
**current worktree directory** (i.e., the working directory where `cargo` commands
are run). Do not switch to other worktrees (e.g., `../monad/`, `../monad-main/`)
unless explicitly instructed. The current worktree contains the branch and
codebase under active development — changes to other worktrees may target
a different branch and cause confusion.

## Project Structure

```
/home/anderscs/src/monad/
├── core/              # Rust compiler/interpreter
│   ├── src/
│   │   ├── parser.rs    # Lexer/parser
│   │   ├── term.rs     # AST and term definitions
│   │   ├── eval.rs     # Evaluator
│   │   │   ├── type.rs    # Type checker
│   │   │   ├── native.rs  # Native function implementations
│   │   │   └── constraint.rs # Constraint solver
│   │   └── main.rs     # CLI entry point (deprecated, use rust-cli/)
│   └── Cargo.toml
├── rust-cli/         # Rust bootstrap CLI crate -- the `monad-rs` binary
│   └── src/main.rs
├── wasm/             # WebAssembly bindings
├── init/             # Pure, portable core mote (see "init vs std" below)
│   ├── mote.toml      # manifest -- no dependencies; dev-dep on std for its tests
│   └── src/           # every mote keeps its modules under src/
│       ├── prelude.mo     # Basic types (Bool, List, Option, etc.)
│       ├── io.mo         # The `IO` type + `Monad IO` instance only -- no natives
│       ├── list.mo        # List.get and other List-specific extras
│       ├── string.mo      # String operations
│       ├── lib.mo          # Re-export hub (`pub use io {*}` etc.) -- bare `init` resolves here
│       └── tests.mo       # Standard library tests
├── std/              # OS-specific implementations and side effects (see below)
│   ├── mote.toml
│   └── src/
│       ├── path.mo         # Path type
│       ├── io.mo           # Path-typed file I/O natives (write_file/read_file/...)
│       ├── process.mo       # exec_cmd
│       ├── lib.mo           # Re-export hub -- bare `std` resolves here
│       └── test.mo        # Test utilities (Test.assert)
├── lang/             # The self-hosted compiler, written in Monad
│   └── src/codegen/    # LLVM backend, split by concern (emit.mo was 8.2k lines)
│       ├── util.mo       # shared list/instruction builders + str_map_* -- imported
│       │                 # by every other codegen module, depends on almost nothing
│       ├── symbols.mo    # how a Monad name becomes an LLVM symbol; def_symbol_name
│       │                 # and ref_symbol_name MUST agree and live together
│       ├── ctx.mo        # CodegenCtx + its tables; exists so emit.mo and tco.mo can
│       │                 # both have fresh_temp/fresh_label without importing each other
│       ├── free_names.mo # free_names_of_term (binder-AWARE) and
│       │                 # collect_referenced_names (binder-blind); pick deliberately
│       ├── tco.mo        # self-recursive tail call -> loop; one entry, apply_self_tco
│       ├── qualify.mo    # Stage 0c: every def gets its `module::name` symbol
│       ├── decls.mo      # decl-list helpers + reachability from an EXPLICIT root
│       ├── natives.mo    # native op table, native->runtime wiring, `declare`s
│       ├── ctors.mo      # constructor tags/arities -- their OWN key namespace,
│       │                 # keyed `bare#arity` because match dispatch only ever
│       │                 # has a bare name to offer
│       ├── validate.mo   # the four fail-fast gates; each exists because the
│       │                 # silent-miscompile it catches actually shipped once
│       ├── ir.mo         # the LLVM IR data types and their rendering
│       ├── emit.mo       # the term compiler and the multi-module pipeline
│       ├── runtime.c     # the C runtime linked into every compiled binary
│       └── runtime.mo    # LLVM IR for the natives that are generated, not written in C
├── examples/         # Example programs
├── bench/            # Standalone .mo micro-benchmarks (Bench.now/Bench.report,
│                     # #[test]-driven) -- deliberately NOT swept by the
│                     # pre-commit hook's `test init std lang examples`, since
│                     # benchmarks are for occasional manual measurement, not
│                     # every-commit correctness checking
├── slow_tests/       # Real #[test]s, deliberately NOT swept by the pre-commit
│                     # hook (same exclusion mechanism as bench/ -- outside its
│                     # fixed `init std lang examples` directory list). Five
│                     # files, moved here purely for cost (measured directly,
│                     # `cargo run --release -- test init std lang examples
│                     # slow_tests --json`, to be 684s of the corpus's 747.5s
│                     # total, 91.5% -- one single test (test_typecheck_lang_
│                     # main) alone was 544.5s, 72.9% of everything):
│                     #   - typecheck_init_tests.mo/typecheck_std_tests.mo/
│                     #     typecheck_lang_tests.mo all pass `check_deps=false`
│                     #     (target-only) to `elaborate_loaded_modules`
│                     #     (`lang/src/module.mo`) -- so checking `cli/src/main.mo`
│                     #     in test_typecheck_lang_main body-type-checks only
│                     #     `cli/src/main.mo`'s own top-level decls, NOT its
│                     #     dependencies' bodies (dependencies only
│                     #     contribute signatures to scope). `check_deps=true`
│                     #     exists (see `elaborate_loaded_modules`'s own doc
│                     #     comment) but is NOT currently used anywhere,
│                     #     including here or by the real `check`/`compile`/
│                     #     `test` CLI commands -- turning it on for
│                     #     `cli/src/main.mo`'s own full closure (≈2200 decls,
│                     #     including this self-hosted compiler's own
│                     #     richly-recursive AST types) caused unbounded
│                     #     memory growth (28GB+ RSS and still climbing);
│                     #     root cause under investigation, see
│                     #     `bootstrapping/check-deps-memory-blowup.md`.
│                     #     typecheck_init_tests.mo/typecheck_std_tests.mo
│                     #     are kept as separate per-file tests regardless
│                     #     of whether `check_deps=true` ever becomes safe to
│                     #     default on: a per-file failure here is far more
│                     #     useful for pinpointing WHICH file broke than one
│                     #     aggregate pass/fail.
│                     #   - parser_file_tests.mo/scope_all_tests.mo: not
│                     #     redundant with anything -- they exercise the
│                     #     parser/scope-builder directly, a different code
│                     #     path from type-checking.
│                     # Moved here specifically so a future CI (not yet
│                     # built, see self-hosted-compiler-perf.md's own
│                     # AGENTS.md item 9 follow-up note) can be the safety
│                     # net for this coverage, since local pre-commit no
│                     # longer affords it. Still real, runnable tests
│                     # (`cargo run -- test slow_tests`) -- just for
│                     # manual/CI use, not the fast local commit path.
└── plans/            # Symlink to external repo with design plans
```

### Standard library layout: `init/` vs `std/`

**`init/` is for pure, portable, core language structures — code that
must work in any environment, including wasm and embedded targets.**
**`std/` is where OS-specific implementations and side effects
belong** — file I/O, process execution, environment variables, and
anything else that touches the outside world. File I/O is the concrete
example that motivated codifying this: it used to live in `init/src/io.mo`
(natives included), and moved to `std/src/io.mo`, leaving `init/src/io.mo` with
only the pure `IO` monad wrapper type itself.

Both `init/` and `std/` have a `lib.mo` re-export hub (`pub use
submodule {*}` for each sibling file, mirroring the existing pattern),
and both are **ambient** — ordinary `.mo` files never need `use init
{...}`/`use std {...}` to reach anything either re-exports; a bare
`init`/`std` module reference resolves straight to `init/src/lib.mo`/
`std/src/lib.mo`, the same way Rust's own `std`/`core` crate name refers to
that crate's root file (`lang/src/module.mo`'s `resolve_module_file` has an
explicit special case for each, alongside the pre-existing one for
`prelude`).

### Motes keep their sources under `src/`

`init/`, `std/`, `lang/`, `slow_tests/` and `bench/` are **motes** (Monad's
packages), and a mote's modules live in its `src/` directory —
`lang/src/codegen/emit.mo`, not `lang/codegen/emit.mo`. Only the
*shape* changed, not the identity: `use lang::codegen::emit` names that
module, and compiled symbol names are unaffected (a module path is
`::`-separated on a `use` line and `.`-joined everywhere it is rendered).
The first segment of a `use` path names the mote; the rest is the path
within its `src/`.

Both compilers implement that mapping: `mote_relative_file` in
`lang/src/module.mo` and `ModulePath::to_mote_file_path` in
`core/src/term.rs` (tried after the literal join, so a search root that
already points into a mote's `src/` keeps working). A one-segment path is
the mote's library root — `use std` is `std/src/lib.mo`.

Directory arguments to `check`/`test` are unaffected (`test init std lang`
recurses), but a path argument names the real file: `test init/src/tests.mo`.

### `lib` is the mote's self-reference

`use lib::x` names the current mote's own `src/x.mo`, the way Rust's
`crate::x` does -- root-relative *within* the mote, so `use
lib::parser::core` from `lang/src/codegen/emit.mo` is unambiguous where a
bare `parser::core` would first try `lang/src/codegen/parser/core.mo`.

It is rewritten to the canonical mote-qualified path (`lang.parser.core`)
at load time, in both compilers, and never resolved as a file path
directly: a module path is also a module's IDENTITY, so `lib.parser.core`
left alone would be a second module distinct from the same file loaded
under its real name -- two copies in scope, and `lib.parser.core::f`
symbols out of codegen. See `resolve_lib_alias_decls` (`lang/src/module.mo`)
and `ModulePath::resolve_lib_alias` (`core/src/term.rs`).

`lib` is reserved: no mote may be named `lib`. A mote's directory name
should match its declared name -- resolution finds other motes by
directory convention (`<name>/src/...`), and only a mote's reference to
ITSELF is resolved through the manifest (`Mote.discover`,
`lang/src/mote.mo`), which is what lets `motes/demo` work.


### Visibility: `pub`, `priv`, and the default

```monad
pub def exported : I64 := 1    // visible everywhere
def package_private : I64 := 2 // visible inside this mote (the default)
priv def module_only : I64 := 3 // visible only in this file's module
```

`priv` is **enforced by the self-hosted compiler**: a `priv` declaration
is dropped from every other module's view, at the flatten that feeds scope
construction (`flatten_visible_module_decls`, `lang/src/module.mo`).
Visibility is declared on a type, class or instance as a whole --
constructors and methods inherit it, never carry their own.

The Rust host enforces `priv` only in `GlobalScopeData::from_module` /
`GlobalScope::from_decls` (`core/src/term/module.rs`), which the LSP and
`Scope` use but `monad-rs check` does NOT: `check` goes through
`core_check_module`'s `GroundTruth`, which flattens every loaded module
into one ungated namespace and enforces neither `priv` nor `use` filters
(its own doc comment says so). So a `priv` violation is caught by the
self-hosted `check` and by the LSP, and slips past `monad-rs check` --
closing that needs real per-module scoping in that checker, which is
tracked in `plans/implementations/visibility-declarations.md`.

The default is **package-private**, which today still resolves across
mote boundaries but **warns**: `check` reports every cross-mote reference
to an unmarked declaration. The corpus is clean, so a new warning means a
new cross-mote edge -- either mark the declaration `pub` or reconsider the
import. `scripts/mark-cross-mote-exports-pub.py` does the marking in bulk,
reading the corpus's own `use` filters to decide what actually crosses a
boundary. Turning the warning into an error is a follow-up; until then,
`pub` documents intent and keeps that flip cheap.


## Building and Running

```bash
# Build the compiler
cargo build --package monad-core

# Run a Monad file
cargo run -- run examples/hello.mo

# In devenv shell also monad-rs as an alias for cargo run:
monad-rs run examples/hello.mo

# Run with debug output
cargo run -- run examples/hello.mo -- --debug

# Run #[test] annotated definitions
cargo run -- test init/src/tests.mo

# Run the bootstrapped cli in cli/src/main.mo
bootstrap

# Compile to native binary in devenv shell
bootstrap compile examples/hello.mo

# Use the REPL (interactive, requires repl feature)
cargo run -- repl
```

### Use `--release` for self-hosted-compiler workloads

Running `cli/src/main.mo` (the self-hosted compiler) interprets a real
compiler pipeline on top of the reference compiler's own `core_eval` —
e.g. `cargo run -- run cli/src/main.mo -- check cli/src/main.mo` (self-hosted
compiler checking itself) took 223s in a debug build vs 99s
`--release` — a 2.2x speedup here (smaller than the 10-15x speedup
`--release` gives the reference compiler's own `check`/`run` on an
ordinary `.mo` file, since the self-hosted path's cost is dominated by
interpreter dispatch/allocation overhead that `-O` optimizes less
aggressively than typical Rust control flow). Prefer
`cargo build --release` + `target/release/monad-rs run cli/src/main.mo --
...` (or `cargo run --release -- run cli/src/main.mo -- ...`) over a plain
debug build for any workload that runs `cli/src/main.mo` against a large
file or corpus, rather than iterating on the reference compiler itself.

## Writing Monad Code

### File Structure
Monad source files use the `.mo` extension.

### Type Definitions

```monad
// Inductive type (algebraic data type)
type Maybe A {
    some (a: A),
    none
}

// Struct-like type (with field default and multiplicity)
struct Point {
    x : I64,
    y : I64,
    z : I64 := 0,   // default value
    !name : String  // linear field (!) or affine (?)
}

// Type with type parameter
type Either E A {
    left (e: E),
    right (a: A)
}
```

### Sort Universe Hierarchy

Monad has a cumulative Russell-style universe hierarchy. Every valid type lives at some
`Sort n` level. The hierarchy prevents paradoxes like Type : Type.

| Sort level | Surface syntax | Meaning |
|---|---|---|
| `Sort 0` | `Prop` | Universe of propositions (proofs, equality statements) |
| `Sort 1` | `Type` | Universe of small types (data, functions, i.e., `Bool`, `I64`, `List A`) |
| `Sort 2` | `Type 1` | Universe of larger types (`Sort 0`, `Sort 1`, type families) |
| `Sort n` | `Type (n-1)` | nth universe level |

**Formation rule**: `Sort n : Sort (n+1)` — every sort is itself a term of the next higher sort.

**Cumulativity**: A term of type `Sort n` can be used where `Sort m` is expected, for any `m ≥ n`.

#### Propositions vs Booleans

This is a critical distinction in dependent type theory:

| Concept | Type | Values | What it means |
|---|---|---|---|
| `Prop` (Sort 0) | `Sort 1` (Type) | Types like `True`, `Eq A a b` | A **type** of proofs / a proposition |
| `Bool` | `Sort 1` (Type) | `true`, `false` | A **computational** boolean |
| `True` (the proposition) | `Prop` (Sort 0) | `trivial` | The trivially true proposition (unit type in Prop) |
| `Eq A a b` | `Prop` (Sort 0) | `refl a` | Proof that `a = b` |

- **`True` is a TYPE, not a Bool value.** It lives in `Prop` (`Sort 0`). Its constructor is `trivial : True`. Use `True.trivial` to construct a trivial proof.
- **`Bool` is a computational type with values `true` and `false`** (note lowercase). `Bool : Type` (`Sort 1`).
- In test functions, the return type is `Bool` (a computational value that can be asserted), not `True` (a proof that cannot be evaluated at runtime).
- All definitions return types that live in `Sort 1` (Type) or higher unless explicitly annotated with `: Prop`.

```monad
// Bool is a regular inductive type in Sort 1 (Type)
type Bool {
    true,
    false
}

// True is a proposition in Sort 0 (Prop) — it's a TYPE, not a value
type True : Prop {
    trivial
}

// Eq is propositional equality in Sort 0 (Prop)
type Eq (A : Sort 1) (a : A) (b : A) : Prop {
    refl : Eq A a a
}
```

When writing Monad source files:
- Test files use `use std::test` (not `use prelude` — the prelude is auto-loaded as `'prelude`)
- The prelude is imported automatically — no explicit `use prelude` needed
- Module paths for the standard library: `std::test` for testing, `io` for IO, etc.

⚠️ **Reserved keywords cannot be used as field names** in `type` constructor parameters (`(name: Type)`) or `struct` field names (`name: Type`). The parser's `identifier` combinator rejects reserved keywords. Common offenders: `class`, `type`, `match`, `if`, `def`, `let`, `in`, `use`, `open`, `struct`, `instance`, `fn`, `do`, `return`, `for`, `quote`, `with`, `infix`, `else`, `then`. Use a synonym instead (e.g., `cls` for `class`, `kind` for `type`). The reserved keyword list is in `RESERVED_KEYWORDS` at `parser.rs:60-63`.

### Class Definitions (Type Classes)

```monad
// Similar to Haskell type classes
class Functor (F: Type -> Type) {
    def map (f: A -> B) : (F A) -> F B
}

// With constraints
class [Functor M] Monad (M: Type -> Type) {
    def bind (a: M A) (f: A -> M B) : M B
}

// With default implementation
class Show A {
    def show (a: A) : String := "<generic>"
}
```

### Instance Definitions

```monad
instance Functor Maybe {
    def map f m :=
        match m {
            some a => some (f a),
            none => none
        }
}

// With type arguments
instance [Add A] Add (List A) {
    ...
}

// Named instance
instance myShow : Show I64 {
    def show x := "int"
}
```

### Function Definitions

```monad
def add (a: I64) (b: I64) : I64 := a + b

def factorial (n: I64) : I64 :=
    if n == 0
    then 1
    else n * factorial (n - 1)

// With implicit parameters
def identity {A : Type} (x: A) : A := x

// Do block syntax (alternative to :=)
def greet (name : String) : IO Unit {
    println name
}

// Do block with multiple statements
def multi_step : IO Unit {
    println "Step 1";
    let value := 42;
    println "Done"
}
```

### Do Notation

Do notation provides syntactic sugar for monadic operations. It can be used with the `do { ... }` syntax or directly in function definitions using `{ ... }`.

```monad
// Standard do notation
def example : IO Unit := do {
    let x <- get_value;
    let y := x + 1;
    return y
}

// Do block in function definition (equivalent)
def example : IO Unit {
    let x <- get_value;
    let y := x + 1;
    return y
}
```

Do blocks support three kinds of statements:

| Statement | Syntax | Desugars To |
|-----------|--------|-------------|
| Bind | `let x <- monadic_expr` | `Monad.bind monadic_expr (fn x => ...)` |
| Let | `let x := value` | `let x := value in ...` |
| Return | `return value` | `Monad.pure value` |
| Expression | `expr` | `Monad.bind expr (fn _ => ...)` |

Multiple expressions must be separated by semicolons:

```monad
def multi : IO Unit {
    println "first";
    println "second"
}
```

Do notation does not (yet) support nested return statements.

<!-- TODO: Give accurate parser errors for this scenario. -->
<!-- TODO: Support more convenient do notation with nested return. -->

```monad
// WRONG return needs to be top level. Will cause cascading parse error.
def nested : IO Unit {
    println "first";
    if b then return a
    else return c
}

// CORRECT use a second do-block
def nested : IO Unit {
    println "first";
    if b then do {
        return a
    }
    else do {
        return c
    }
}

// CORRECT extract return
def nested : IO Unit {
    println "first";
    return if b then a
    else c
}
```

### Comments

```monad
// Line comment
/* Block comment */
```

### Docstrings

```monad
/// Documentation for the following declaration
def greet (name : String) : IO Unit {
    println name
}

/// Module-level documentation (at top of file)
```

Docstrings (`///`) are parsed and stored on declarations. They are retained through module loading for tooling and inspection.

### Lambda Expressions

```monad
fn x => x + 1
\ x => x + 1
ꟛ x => x + 1
```

### Backtick Operators

```monad
x `f` y   // Equivalent to f x y
```

Identifiers in backticks are treated as infix operators (like Haskell).

### Type Annotations

```monad
(expr : Type)
```

Any term can be annotated with its type using `(term : Type)` syntax.

### Let Expressions

`let` expressions come in two forms depending on context:

**Outside do-notation** (in `:=` def bodies): the `in` keyword is REQUIRED.

```monad
let x := 10 in
x + 1

// With type annotation
let x : I64 := 10 in
x + 1

// Chained lets: each let needs its own `in`, nesting rightward
let x := 10 in
let y := x + 5 in
x + y
```

**Inside do-blocks** (`{ ... }` def bodies): statements use `;` separation, NO `in`.

```monad
def example : I64 {
  let x : I64 := 10;
  let y : I64 := x + 5;
  x + y
}
```

**Common mistake**: using `:=` body syntax with multi-statement `let ... ; let ... ; expr` without `in`.
This is invalid. Either use `{ }` do-block syntax or nest with `in`.

```monad
// WRONG — no `in`, no `{ }`:
def example : I64 :=
  let x : I64 := 10;
  x + 1

// CORRECT — do-block:
def example : I64 {
  let x : I64 := 10;
  x + 1
}

// CORRECT — let ... in:
def example : I64 :=
  let x : I64 := 10 in
  x + 1
```

### Numeric Literals

```monad
42        // I64 (default)
42i8      // I8
42i16     // I16
42i32     // I32
42i64     // I64
42u8      // U8
42u16     // U16
42u32     // U32
42u64     // U64
3.14      // F64 (default)
3.14f32   // F32
3.14f64   // F64
0xFF      // I64, hex notation
0xFFu32   // U32, hex notation
```

### Raw String Literals

Rust-style raw strings take their body verbatim — no `\`-escape processing
— so backslash-heavy text (regex, JSON, Windows paths, embedded source) can
be written exactly as it should appear:

```monad
r"no escapes here: \n \" works literally"
r#"can contain " freely, even """ inside"#
r##"embed a "# that a one-hash closer would catch"##
r###"embed a "## too"###
```

The opener is `r`, then `n` (>= 0) `#` characters, then `"`. The closer is
the first `"` in the body followed by at least `n` `#` (exactly `n` are
consumed; extra `#` beyond `n` are left in the remainder, matching `rustc`).
So to embed the literal text `"##`, use `n = 3` (`r###"..."###`) since
`"##` (two hashes) is not a closer for `n = 3`. A raw string parses to the
same `Literal::Str` value an ordinary `"..."` string produces:

```monad
def regex : String := r#"\w+\s*"\s*\w+"#   // body: \w+\s*"\s*\w+
def path : String := r"C:\Users\monad\src\main.mo"   // backslashes literal
// r"\n" == "\\n"   // true — raw backslash-n == escaped backslash + n
```

`r` is a valid identifier, so the raw-string parser is tried ahead of the
identifier parser in both `core/src/parser.rs` (`term_inner`/`non_app_term`)
and `lang/src/parser.mo` (`atom_parsers`); a bare `r`, `regex`, or `r#` not
followed by `"` still parses as the identifier `r` / `regex`.

### Match Expressions

```monad
match value {
    some a => a,
    none => default
}
```

### Record / Struct Literals

```monad
{ x := 1, y := 2 }
```

### Operator Declarations

```monad
infix:13 (>>=) := Monad.bind
infix:20 (++) := List.append
```

### Module Imports

```monad
// Load a module, listing exactly the names needed.
// `::` separates module path segments -- `use` only.
use std::list {intercalate}
use io {IO}

// This mote's own library root (Rust's `crate`), root-relative
// within the mote.
use lib::codegen::emit {compile_db_module}

// Open a namespace: make defs available without their prefix.
// `open` names a NAMESPACE, not a file, so it keeps `.`.
open IO {println}
```

`::` is for `use` paths and nothing else. Dotted def names
(`String.length`), member access (`x.field`), constructor paths
(`List.cons`) and `open` paths all stay dotted -- the separator is what
tells a module path apart from a name path on sight.

`::` is also the only spelling a `use` path accepts: the corpus migration
is complete, so a dotted `use std.list` is a **parse error**, in both
parsers (`use_path_sep`, `lang/src/parser.mo`; `use_path_expression`,
`core/src/parser.rs`).

Mechanically that rejection is a TRUNCATED parse, not a hard failure, and
the distinction matters if you touch either parser. `separated_by` stops
at the first segment, so `use std.list {intercalate}` parses as the
ONE-segment path `std` with `.list {intercalate}` left as unconsumed
text; what makes it an error is that the file loader requires a parse to
consume its whole input. Both parsers behave this way on purpose, and
each has a test pinning the truncated shape
(`test_use_parser_rejects_dotted`, `lang/src/parser.mo`;
`test_use_rejects_dotted_path`, `core/src/parser/test/declarations.rs`).

Note the difference between the two, since it bites when porting a dotted
call site: `use std::list {intercalate}` binds the BARE name, so the call
site is `intercalate xs`, not `std.list.intercalate` -- a
module-qualified term reference is a separate spelling and is not what a
`use` line gives you.

That separate spelling is parsed but does NOT resolve yet in the
self-hosted compiler: `lower_name_ref`'s `nqn` arm throws the structure
away (`lower_name_global`), so a `std::list::intercalate` reference
reports `unknown variable`. The Rust host resolves the pure
`module::name` shape instead, but mis-lowers one with a dotted tail
(`std::list::List.cons` hits "infix operator (.) has no entry in the
lowering pass's infix table"). No corpus file needs the form, which is
why the migration above went to bare imported names -- reach for those,
not for a qualified term reference.

A `use` path also accepts a bare module name with no mote prefix when the
module lives under `motes/<member>/src/` -- the search path mirrors the
Rust host's (`build_default_search_paths`, `core/src/lib.rs`; the
self-hosted twin is `motes_src_paths`, `lang/src/module.mo`).

`{*}` imports/opens everything explicitly; a bare `use`/`open` (no braces) still parses but is deprecated in favor of an explicit filter.

### Native Functions

Call Rust functions from Monad using the `#[native "..."]` attribute:

```monad
#[native "add"]
def add (a: I64) (b: I64) : I64
```

## Attributes

Declarations can be annotated with `#[...]` attributes:

```monad
#[native "function_name"]   // Declare a Rust-native function
#[test]                     // Mark as a test (run via `cargo run -- test <file>`)
```

Attributes come before visibility: `#[test] pub def ...`, not `pub #[test] def ...`.

## Operators

All operators and their precedences:

| Operator | Precedence | Assoc | Description |
|----------|-----------|-------|-------------|
| `.` | 12 | Right | Dot macro (path concatenation / method call) |
| `\|>` | 5 | Left | Forward pipe (`x \|> f`) |
| `<\|` | 5 | Right | Backward pipe (`f <\| x`) |
| `>>=` | 10 | Right | Monad bind |
| `<*>` | 15 | Left | Applicative apply |
| `<\ | >` | 20 | Left | Alt/choice |
| `\|\|` | 25 | Right | Boolean OR |
| `&&` | 30 | Right | Boolean AND |
| `==`, `!=`, `=` | 40 | Left | Equality / assignment |
| `++` | 50 | Right | Append |
| `>>`, `<<` | 60 | Left | Shift / fork |
| `+`, `-` | 65 | Left | Add / subtract |
| `*`, `/` | 70 | Left | Multiply / divide |

## Method Call Syntax

```monad
x.fun        // Desugared to A.fun x (where A is the type of x)
x.fun args   // Desugared to A.fun args x
```

Method calls are desugared in the type checker at `type.rs:701-740`. The receiver type is extracted and prepended to the method name.

## Dot Macro

The `.` operator (`x.y.z`) is treated as a compile-time macro that concatenates module paths into a single `Var` reference (at `eval.rs:167-200`). This is how module paths like `List.append` work.

## Constraint Solver

Recursive instance constraints (e.g., `instance [Show A] Show (List A) { ... }`) are handled by the constraint solver at `core/src/eval/constraint.rs`. It uses a visiting set to detect and resolve cyclic constraint dependencies during instance resolution.

## Key Language Features

1. **Dependent Types**: Types can depend on values (using `{x : Type}` forall syntax)

2. **Type Classes**: Like Haskell, with automatic instance resolution

3. **Linear Types**: Compile-time enforcement via `!` (linear) and `?` (affine) multiplicity annotations on parameters (the syntax parses everywhere -- struct fields, def/lambda/destructured params -- and is dropped at lowering; nothing is enforced yet)

## Modifying the Compiler

### Parser (`core/src/parser.rs`)
- Add new syntax in the parser combinators
- Reserved keywords are defined in `RESERVED_KEYWORDS`

### List Literal Desugaring
List literals `[a, b, c]` are desugared in `desugar_list_literal` (parser.rs:620) to nested `FromListLiteral` calls:
```
[a, b, c]  =>  (FromListLiteral.cons a) ((FromListLiteral.cons b) ((FromListLiteral.cons c) FromListLiteral.empty))
```
The AST structure is `app(app(cons, elem), acc)` — **NOT** `app(cons, app(elem, acc))`.
For a single element: `[x]` => `app(app(cons, var("x")), empty)`

### Evaluator (`core/src/core_eval.rs` + `core_native.rs`)
The legacy tree-walking evaluator (`core/src/eval.rs`'s old `eval`/`eval_test`) has been removed — the closure-based `CoreTerm` evaluator is now the crate's only evaluator, reached via `check_all_modules_capturing_core` (`core_check_module.rs`) → `lower_core_ir::lower_program` → `core_eval::force_global`.
- Beta reduction/closure application happens in `core_eval.rs`'s `force_global`/`apply`
- Native functions are executed in `core_native.rs`'s `exec_native`
- To trace evaluation, add tracing in `core_eval.rs` rather than a stray `println!` — `run --debug` already prints the checked type (`Eval type ...`) before evaluating

### Type Checker (`core/src/core_check_module.rs` + `core_unify.rs`)
- Module-level type checking and de Bruijn/`MetaId`-based unification
- `core/src/eval/type.rs` still holds shared pre-lowering infra used by the checker above: `elaborate_decls` (implicit `Forall` insertion), `check_strict_positivity`, the `TypeError` type and its diagnostics rendering — despite the `eval/` path, this file is not part of the (removed) legacy evaluator

## Testing

```bash
# Run Rust tests
cargo test

# Run a specific test
cargo test core_check_module::
cargo test core_eval::
```

### Memory: whole-corpus checks and the test suite

A whole-corpus `monad-rs check` and `cargo test --release` are the two
heaviest things in this repo, and both run from the pre-commit hooks. A
bug that makes name resolution miss can turn either into unbounded
allocation that exhausts system memory and hard-restarts the machine —
this happened repeatedly on 2026-09-20, taking the desktop down with it
rather than just failing the run.

**The measurement that finds it**, and the way to run either safely:

```bash
systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 \
  cargo run --release -- check init std
```

Exit 137 means it was killed at the cap — that is the signal. A healthy
whole-corpus check (142 files) completes under 6 GB, and `init std` alone
completes under 4 GB. Bisect by narrowing the target, not by widening the
cap: `check init` is cheap, `check init std` is where a blow-up first
shows.

**One real instance, worth understanding before touching name
registration:** registering a global under a SECOND spelling in
`known_globals` is only safe when that atom also has a `Local` entry.
`known_globals` is inverted into `atom_paths` (one path per atom), and an
ordinary inductive's own bare name is deliberately absent from it — so
adding only a qualified spelling made that the atom's sole recorded path,
which then beat `structs.inductive_paths` in instance resolution,
the `known_instances` lookup missed, and resolution degraded into a
retry that ate 30+ GB. Alias the ATOM freely; be careful what you add to
`known_globals`.

Ordinary hygiene that also helps:

- **Do not run two cargo invocations at once.** Let one finish first,
  including background jobs you started and forgot.
- **Narrow the scope.** `cargo test -p monad-core --lib <name>` is cheap
  and usually enough; reserve the full run for a final check.
- **Bound the parallelism**: `cargo test -j 2 -- --test-threads=2`.

**A polling memory watchdog does NOT work** — sampling `/proc/meminfo`
every few seconds cannot catch a fast allocation spike; the OOM killer
fires between polls, and the false confidence is worse than no safeguard.
Use the `MemoryMax` cap instead, which is enforced by the kernel.

If you are an agent working in this repo: `git commit` runs the full test
suite and a whole-corpus check via hooks, so it is not a cheap operation.
If the user has said not to run tests, that includes committing — say so
rather than discovering it together.

## Development Workflow

Always use Test-Driven Development (TDD):
1. Write a **failing test** first
2. Implement the fix/feature
3. Run tests to confirm pass
4. Run `cargo fmt && cargo test` to ensure formatting and all tests pass
5. Make a **small, focused commit** with a descriptive message

Always make small, incremental changes. Each commit should be a single logical change.
After each commit, confirm the test suite still passes.

When a feature or bug fix is implemented, update the relevant plan in `plans/` to reflect the completed work. Mark completed tasks, add notes on the approach taken, and capture any design decisions or tradeoffs discovered during implementation.

When implementing a non-trivial new language feature or stdlib addition, add a corresponding example to `examples/` demonstrating its use. The example must pass `cargo run -- test examples/` — do not add broken examples. If an existing example already covers the feature, add a test case to the existing example file instead of creating a new one.

## Common Patterns

### Creating New Types

Add to `init/src/prelude.mo`:
```monad
type MyType {
    constructor (field: Type)
}
```

### Adding Native Functions

1. Add Rust implementation in `core/src/eval/native.rs`
2. Declare in a `.mo` file:
```monad
#[native "function_name"]
def function_name (args: Types) : ReturnType
```

## Standard Library

### `init/src/prelude.mo`
- Basic types: `Bool`, `I64`, `I8`, `I16`, `I32`, `I64`, `U8`, `U16`, `U32`, `U64`, `F32`, `F64`, `String`, `Void`, `Any`, `Nat`, `List`, `Option`
- Type classes: `Add`, `Sub`, `Mul`, `Div`, `BEq`, `BOrd`, `Functor`, `Applicative`, `Monad`, `Show`, `Append`, `FromListLiteral`, `DefaultValue`
- Operators: `+`, `-`, `*`, `/`, `==`, `!=`, `&&`, `||`, `++`, `|>`, `<|`, `>>=`, `<*>`, `<|>`
- Functions: `Bool.not`, `Bool.and`, `Bool.or`, `Option.get_or_default`, `List.is_empty`, `List.append`, `List.first`, `List.last`, `List.tail`, `List.flatten`, `fun_apply`, `apply_fun`

### `init/src/string.mo`
- `String.concat`, `String.length`, `String.get`, `String.is_empty`

### `init/src/init.mo`
- `From` class for type conversion

### `std/src/test.mo`
- `Test.assert` for assertion-based testing

### Module Dependency Boundaries

**`init/` must never depend on `std/`.** The `init/` directory contains core language definitions (prelude, io, types) that are foundational. The `std/` directory contains higher-level modules that depend on `init/`.

- `std/` modules may `use` `init/` modules (e.g., `use io`)
- `init/` modules must **NOT** `use` `std/` modules
- **Tests for `std/` modules go in `std/`**, not in `init/` — `init/src/tests.mo` must not import from `std/`

When adding a new `std/` module with tests, place the test file within `std/`:
```bash
cargo run -- test std/   # runs all std/ tests including new ones
```

## Style Conventions

- Use 2 spaces for indentation
- Lowercase identifiers for functions/variables
- Uppercase for types/type classes
- Prefer descriptive names
- Comment with `//` (never `--`)

### Readability and Ease of Refactoring (Monad code)

Optimize for a reader who has to change this code later, not just for it
to typecheck once. Concretely, in order of how often each comes up:

1. **Every single-constructor type should be a `struct`, not a `type`.**
   `type X { mk (f1:T1) (f2:T2) ... }` with exactly one constructor gives
   up named-field construction, dot-notation access, and struct-update
   syntax for no benefit over `struct X { f1:T1, f2:T2, ... }` — the two
   forms use IDENTICAL match/destructuring syntax
   (`X.mk pat1 pat2 => ...` or `TypeName.ctor_name` patterns work the
   same either way), so converting costs nothing at existing pattern-match
   call sites and only improves construction/access sites. When adding a
   *new* type, reach for `struct` first and only fall back to `type` if
   it genuinely needs more than one constructor.
   _(TODO: this should eventually be a `check` warning — "single-
   constructor `type` could be a `struct`" — rather than something to
   remember by convention. Not implemented yet.)_
2. **Prefer struct-literal + dot-notation + named-args over positional
   construction/destructuring** once a type is a `struct`: `{ f1 := v1,
   f2 := v2 }` to build, `value.field` to read a single field, and
   `{ base with field := v }` to update one field of an existing value
   (much clearer than reconstructing every positional argument by hand
   when only one changed — see `CodegenCtx`'s `fresh_temp`/
   `ctx_bind_local`/etc. in `lang/src/codegen/emit.mo` for the pattern).
   When you DO need to destructure several fields of a `struct` at once
   in a match arm, prefer the field-pattern form,
   `match v { { field1, field2, .. } => e }` (or `Ctor { field1,
   field2 } => e` for a named constructor), over positional
   `X.mk pat1 pat2 => e` — it self-documents which field is which at the
   call site instead of relying on declaration-order memory, survives a
   field being added/reordered without silently binding the wrong name
   to the wrong position, and `..` lets you ignore fields you don't need
   instead of naming a placeholder for each. `field := new_binder` renames
   a field to a different local name; a bare `field` puns (binds a local
   of the same name). Positional destructuring is still fine for an
   ordinary multi-constructor sum `type` (there are no field names to
   pun on there).
3. **Don't prefix field names with a type-specific abbreviation**
   (`cr_ctx`, `mcr_blocks`, `as_head`, `lname`) — the field is already
   namespaced by the struct/record it lives in (`result.ctx`, not
   `result.cr_ctx`); a prefix only adds noise to every call site. Plain,
   short field names (`ctx`, `val`, `blocks`, `head`, `args`) read better
   and are just as unambiguous, since Monad field access is always
   through a typed value (`x.field`), never a bare global name.
4. **Avoid nested `if`** — prefer `match` for genuine multi-way dispatch,
   and combine compound conditions with `&&`/`||` rather than nesting
   `if`s that test unrelated things one after another. A real two-way
   `then`/`else` split that IS the actual logic (not just chained checks)
   is fine as `if`; this is about avoidable nesting, not banning `if`.
5. **Remove dead/duplicated code as you find it** in a file you're
   already touching for readability — an unused helper or a hand-rolled
   duplicate of something already imported doesn't need its own separate
   change to justify removing it.
6. **Prefer a real `Map`/`HashMap` lookup over a hand-rolled
   `if String.beq x "a" then ... else if String.beq x "b" then ...` chain**
   for a genuine key→value dispatch table (a `String → SomeType` mapping
   with several branches) — self-documenting, no risk of a mistyped
   comparison silently falling through to the wrong branch or an
   unreachable duplicate key, and adding an entry is one line instead of
   an `else if`. This codebase's own `Map` typeclass has known
   instance-resolution bugs (see "Known Type Checker Issues" #3 below) —
   use the direct `str_map_empty`/`str_map_insert`/`str_map_lookup`
   bypass helpers (`lang/src/codegen/emit.mo`) or the equivalent
   `modpath_map_*` ones (`lang/src/scope.mo`) instead of the `Map` class
   directly. As with any `List`→`HashMap` swap in self-hosted code, this
   is a genuine, MEASURED win when the table is built once and looked up
   many times across a large corpus (this project's own precedent: the
   `filter_reachable`/`ctor_tags`/`CodegenCtx.arities` fixes) — but per
   "Known Type Checker Issues" #4's `BTreeMap`-regression lesson, still
   measure rather than assume for a table on a narrower or more
   expensive-per-call path; a small (single-digit-entry), rarely-changing
   dispatch table's readability win doesn't require a measured perf win
   to justify converting; a table that's rebuilt from scratch on every
   call (rather than built once and reused) is a different, much riskier
   shape — measure that one directly before converting.

**A known pitfall when applying rule 1 to an *existing* type with many
call sites**: the type-checker doesn't always desugar a bare struct
literal to a real constructor when it can't see a concrete expected type
at that exact point — two confirmed shapes:
  - a struct literal passed directly as a function ARGUMENT with no
    outer type annotation (e.g. `List.cons { field := val } rest`) can
    fail with a misleading `` `List.cons` has no field named `field` ``
    error. Workaround: bind it first with an explicit annotation
    (`let x : T := { field := val } in List.cons x rest`), which resolves
    correctly.
  - converting a type used as MANY struct literals across many nested
    `match` arms within one large function (confirmed at ~15+ call sites
    in one pass) can produce a runtime `MatchTraversalMismatch` from the
    Rust host's `lower_core_ir.rs` — a genuine, pre-existing checker/
    lowering desync bug (the type-checking pass and the lowering pass
    must visit `Match`/`if`/`StructUpdate` nodes in the same order to
    correctly replay queued constructor resolutions, and don't always
    agree at this scale). `check` stays completely silent about this —
    only running the actual test suite (`cargo run -- test ...`) surfaces
    it. If converting a type to `struct` reproduces this, the safe
    fallback is to keep it as a `type` (plain constructor-call syntax
    still works everywhere) rather than force the conversion — readability
    is not worth a silent runtime miscompile. Always re-run the real test
    suite (not just `check`) after a `type`→`struct` conversion for a
    widely-used type, for exactly this reason.
  - a bare struct literal under `return` (i.e. as `Monad.pure`'s
    argument), especially with a second literal nested inside it as a
    field value:
    `return { result := { path := fp, diagnostics := ds }, cache := c }`.
    The reference interpreter accepts it. The self-hosted checker
    rejects it ("cannot infer struct type for struct literal"), but
    `compile`/`check` typecheck only the TARGET file, so one written in
    a DEPENDENCY module is diagnosed nowhere — best-effort elaboration
    (`elaborate_module_decls_best_effort`) silently keeps the
    un-desugared decl and `compile_lit_ir` compiles the literal to a
    `void_val` placeholder. Same fix: bind each level to a local with an
    explicit type annotation first, or -- when the literal is the whole
    result -- move it into its own `def` with a DECLARED return type,
    which is what gives it an expected type (`mk_loaded_modules`/
    `mk_module_info` in `cli/src/main.mo`, `rebuild_target_scope` in
    `lang/src/module.mo`).

    **TODO: the self-hosted checker should support a struct literal in
    return position.** Every workaround above exists only because it
    cannot infer the type there. `return`'s expected type IS known --
    it is the enclosing `do` block's `IO A` payload, the same
    information a `let x : T := {...}` annotation supplies by hand --
    so the inference is available, just not threaded to the struct-
    literal case. Until it is, the workarounds are mandatory: the trap
    is silent in a dependency module (see above) and cost a bootstrap
    run as recently as the stage-6 DWARF work
    (`with_located_decls`/`locate_module_info`, caught only by
    `devenv tasks run monad:bootstrap-compile`, since the Rust host
    accepts what the self-hosted checker rejects).

**Adding a field to a `struct` breaks every POSITIONAL match on it, and
nothing catches it statically.** A pattern like `mk _ _ _ inds _ _ _ _ _`
binds one variable per field; against a struct that has since grown a
tenth field it still typechecks fine and then aborts at RUNTIME with
`expected 9 constructor fields, got 10` — no location, no def name, the
whole run dead rather than a diagnostic. Adding `def_sigs` to
`ScopeData` did exactly this to
`scope_data_find_all_inductives_by_constructor` (`lang/src/scope.mo`),
taking down the self-hosted `check` of both `lang/src/scope.mo` and
`lang/src/module.mo`. When you add a struct field, `grep` for positional
matches on that type (`grep -rnE 'mk( [a-z_][a-z_0-9]*){N,} =>'`) and
widen them; prefer a `{ .. }` field pattern or field access for new
code, which is immune. A test that CALLS such a function against a real
value (not just constructs one) is what catches it.

`lang/src/codegen/emit.mo`'s `validate_no_undesugared_struct_lits` now
fails the compile fast, naming the enclosing def, for any struct literal
that reaches codegen un-desugared — that third shape used to cost a
whole bootstrap-ladder rung before anyone saw it (the self-compiled
compiler printed `FAIL   (0 error(s))` and then blew the stack in
`print_diagnostics`, recursing on a garbage list tail).

### Rust Code Style

- Always use `use` statements at the top of the file instead of fully qualified paths
- Group `use` statements logically (standard library, external crates, local modules)
- Example: prefer `use crate::term::{Identifier, Term, param};` over `crate::term::Identifier`

## Workflow

When assumptions fail, tests break unexpectedly, or you hit hard errors:
1. **Explain the root cause** to the user before proceeding
2. **Ask for input** on how to resolve — don't silently pick a fix
3. Present options with tradeoffs when there are multiple approaches
4. Only proceed once the user confirms direction

## Troubleshooting & Known Issues

### Class Method Resolution in `def_refs`

**Problem**: Class methods (e.g., `BEq.beq`) were being added to `def_refs` with their type signature as the term. This caused `find_ref` to find them before instance resolution could happen in `find_any_ref`, resulting in "expected function found for {A : Type} -> ..." errors at evaluation time.

**Root cause**: Two places were adding class methods to `def_refs`:
1. `load_decl` (line ~558) — when loading `Decl::Type` for classes
2. `get_def_refs` (line ~1123) — via `get_class_method_defs`

**Fix**: Class constructors should NOT be added to `def_refs`. Only the class name itself should be in `def_refs`. Class methods should only be in `class_defs`, so that `find_any_ref` falls through to instance resolution.

**Key invariant**: `def_refs` should contain concrete terms (implementations), NOT type signatures. Class methods are abstract — their concrete terms come from instances.

### Instance Resolution Flow

When resolving a name like `BEq.beq` or `==`:
1. `resolve_name` → `find_any_name_ref` → `find_any_ref`
2. `find_any_ref` first tries `find_ref` (def_refs) — if found, returns immediately
3. If not in def_refs, tries `find_class_def` (class_defs) — if found, derives instance key and calls `find_instance`
4. `find_instance` matches the instance key against registered instances

**If a class method is in def_refs, step 2 returns the type signature term and instance resolution never happens.**

### Self-Hosted Checker: Class-Method Signatures, Instantiation, and Applied-Head Matching

Three separable things gate every class-method call in the self-hosted
checker (`lang/src/typecheck/infer.mo`), and the reason they are easy to
conflate is that a *class method* is not a `def`: nothing about it is
type-checked the way a call to a named `def` is.

1. **Resolution.** `type_check_free_var` errs on a dotted class-method
   name, falls back to `scope_find_class_def_by_name` (the BARE last
   segment, across all class defs), then `resolve_class_method` walks D5
   (a bound dict in `dict_env`) → the carrier derived from
   `expected_type` → `find_matching_instance` → `resolve_class_method_d4`.
2. **The signature.** `ScopeDef.sig` is `Term.hole` for EVERY def --
   `build_scope_def` sets it unconditionally, and that sentinel is
   load-bearing for dozens of call sites, so it cannot simply be filled
   in. The real declared signature lives in the `def_sigs` side-table
   (`ScopeData.def_sigs`, written in `lang/src/scope.mo`, read with
   `scope_find_def_sig`). `resolve_class_method_d4` read `.sig`, so it
   typed every class-method call as a hole *while its own doc comment
   claimed to return "the resolved concrete def's own real signature"*.
3. **Instantiation.** A promoted method's registered `Def.typ`
   (`promote_methods` copies it through unchanged) keeps its implicit
   type variables FREE: `FromListLiteral_List_cons` is registered as
   `A -> List A -> List A`, with no `forall` wrapper. Peeling that pi
   chain therefore reports a still-abstract return, which travels
   upward and meets the declared return in `type_check_cases` as
   `type mismatch: expected (List A), found (List U8)`. Note the
   direction of that message: `type_check_cases` calls
   `unify body_typ expected_type`, so **"expected" is the ARM BODY's
   type and "found" is the DECLARED return** -- the reverse of the
   intuitive reading, and worth checking before blaming a declared type.

Fixes 2 and 3 are `solve_typevars`-based and landed together: the
signature is solved against the ambient `expected_type` at the callee's
own position (`inst_sig`), and each further application solves `pi_arg`
against the argument's already-inferred type and substitutes through the
WHOLE remaining chain (not just the final return -- `cons e1 e2` solves
at the first argument and needs the second parameter's own `List A`
rewritten too). Both reuse the existing `solve_typevars` gate: a
`Term.hole` actual, or a shape mismatch, records nothing, so an
uninformative call leaves the signature untouched rather than rewriting
it wrongly.
`lang/src/typecheck/infer.mo`'s `test_extract_pi_ret_*` tests pin this
directly (two red before / green after, two pinning the no-record
gates), and they are deliberately unit-level rather than end-to-end:
the corpus cannot reach the new path until the applied-head match
lands, so an end-to-end test here would be one that cannot fail.

**Fixes 2 and 3 change no corpus file's verdict on their own.** Measured
with and without them: `check init std examples lang cli llvm runtime
motes slow_tests bench` reports 15 errors in the same 7 files either
way. They are a precondition, not a trigger: `FromListLiteral.cons` has
to RESOLVE (fix 1) before any signature is read at all, and the carrier
that makes it resolve -- `List (List A)`, derived from `List.flatten`'s
own parameter -- needs the applied-head match below. All three together
close `std/src/sha256.mo` at both `check` and `monad test` level.

**The applied-head match landed 2026-09-19 (P6), in both directions.**
`term_matches_carrier` (`lang/src/scope.mo`) used to require the carrier
to be an `App` when the instance's declared arg is applied, and the bare
names to be equal when it is bare -- so a bare instance arg (`instance
FromListLiteral List`) never matched an applied carrier
(`List (List U8)`), which is the only shape an expected-type-derived
carrier has. Both directions now peel one level down: the applied
carrier against the bare instance arg (`Term.app chead _ =>
term_matches_carrier wildcard_names ins_term chead`), and its mirror,
an applied instance arg (`Show (List A)`) against the bare head that
`infer_carrier_type` deliberately normalizes to -- gated on the
instance arg's own parameters being the class's wildcards, so a concrete
`Show (Option I64)` still cannot match a bare carrier. With fixes 1-3
this closes `std/src/sha256.mo` at both `check` and `monad test` level;
the full self-hosted sweep is 969/969 tests with 0 FAIL.

**The `ce_cycle 3` that arm used to trip was never dict recursion.** It
showed up on `cli/src/tests/cli_derive_self_hosted_tests.mo` (minimal
repro: `use lib::args {*}` plus a `derive_cli! DemoCommand` decl over a
two-field `type DemoCommand`, which stays `ok` without the arm) as
`meta_eval_invoke: applying the meta-def to its TypeInfo argument
failed: ce_cycle 3`. The real mechanism: `List.empty`'s qualifier is the
INDUCTIVE `List`, and the bare-name class-method fallback in
`type_check_free_var` (`lang/src/typecheck/infer.mo`) stripped that
qualifier and matched class `FromListLiteral`'s own `empty` method --
"resolving" the reference to the promoted def standing inside its own
body, a strict self-reference the evaluator's global force guard reports
as `ce_cycle`. `ref_names_class_method` now requires the qualifier to
name a CLASS before that fallback runs, so an inductive-qualified
reference (`List.empty`, `Option.some`, `Bool.true`) falls through to
the constructor path it means. Measured with both arms in place:
`cargo run --release -- test cli/src/tests/cli_derive_self_hosted_tests.mo`
is 5/5 PASS.

**What the match still does NOT close** (measured 2026-09-19, same day).
Of the six remaining `no instance found` gaps, matching now succeeds for
four -- what fails is downstream of it:

* `std/src/list_tests1.mo`/`list_tests2.mo`: a list literal's carrier is
  the bare head `List` (its desugared `FromListLiteral.cons` declares
  `A -> List A -> List A`), so the instance's OWN constraint (`[Show A]`
  on `instance [Show A] Show (List A)`) has no `A` to resolve against.
  A match has to yield bindings; nothing in the pass carries them.
* `std/src/map_tests.mo`/`test_map_full.mo`: `Map.empty` has no
  carrier-revealing argument at all, and the annotated binding
  (`let m : BTreeMap I64 String := Map.empty`, reproduced in isolation)
  is not handed to it as an expected carrier. Even with one, `instance
  [BOrd K] Map BTreeMap`'s `K` is bound only by the method's own
  signature (`empty : M K V`), so the `[BOrd K]` dict argument needs
  signature-vs-carrier bindings too.
* `std/src/base.mo`: `Bounded.max_bound` is nullary and `class Bounded`
  declares no default carrier. The expected type exists in the enclosing
  call -- `BEq.beq`'s `A`, pinned to `Ordering` by the sibling argument
  `gt` -- but `type_check_app` does not push a callee's instantiated Pi
  domain into its arguments (annotated LETS do get an expected type:
  `Enum.from_nat`'s `let f0 : Ordering := ...` in the same file passes).
  This is the same missing channel as the generic-`Add` gap below.

`std/src/derive_tests.mo` is NOT this family at all. Measured by probe:
`derive_debug! Point` + `Debug.debug pt` fails identically (and the
generated def's name carries no module prefix), while the same file with
a hand-written `instance Debug Point` passes -- a macro-DERIVED instance
is invisible to the codegen pass, i.e. the `reflect_type_info!` /
decl-gen family (P10), not instance resolution.

A `#[test]` def carrying a direct field access is a known miscompile
shape -- the def gets the FIELD's LLVM type as its return type (an
`i1`/`i64` llc failure, or an undefined `@P.mk`), visible only through
the COMPILED self-hosted runner, never the Rust one. It is
shape-dependent rather than absolute: this file's older tests read
`tt.typ` inline inside a `match` arm and pass. The new tests do not bet
on that -- they read the result type through an ordinary helper def
(`extract_pi_ret_result_typ`) and a typed accessor.

### BEq Type Signature Bug

The `BEq` class in `init/src/prelude.mo` originally had:
```monad
class BEq A {
    def beq : A -> B -> Bool  // WRONG: B is unbound
}
```
Should be:
```monad
class BEq A {
    def beq : A -> A -> Bool  // CORRECT
}
```

### Reserved Keywords in Field Names Cause Cascading Parse Errors

**Problem**: Using a reserved keyword (e.g., `class`) as a constructor field name in `type` or `struct` declarations causes a misleading parse error. The error appears at the *next* declaration with "unexpected: Eof", because the parser rejects the keyword inside `(name: Type)` syntax, fails to find the closing `}`, and consumes all remaining input looking for it.

**Root cause**: `cons_param` (`parser.rs:329`) and `struct_field_parser` (`parser.rs:1346`) both use `identifier`, which rejects reserved keywords. When a field like `(class: ModulePath)` is encountered, the keyword fails to parse, the branch backtracks, and `type_expression` consumes the `:` as a type annotation instead, leaving the `}` unsatisfied.

**Fix**: Rename the field (e.g., `class` → `cls`). See the warning under [Type Definitions](#type-definitions) for the full list of reserved keywords.

### Lambda Parameter Type Annotations Require Parens

**Problem**: Writing `fn s : String => s` (an annotated lambda parameter with no parens around `s : String`) produces a parse error — this is not, and never was, valid syntax. Note this is *not* about lambda expressions in argument position; it fails the same way as a standalone `def` body too.

**Root cause**: `lam_param` (`core/src/parser.rs:394`) parses a bare identifier as an unannotated param (`param(i, Hole)`), or an *entirely parenthesized* `(name : Type)`/`(name : Type := default)` for an annotated one — mirroring `def`'s own parameter syntax. There is no bare `name : Type` form.

**Fix**: Wrap the annotated parameter in parens:

```monad
// BROKEN — no parens around the annotated param:
fn s : String => s

// CORRECT:
fn (s : String) => s
```

Lambda expressions (both annotated-with-parens and unannotated) parse and
type-check fine as **direct arguments in function application**, including
to generic/polymorphic functions — confirmed with `map_parse`/`bind_parse`:

```monad
map_parse (fn (s : String) => s) (tag "x") "xy"   // works
map_parse (fn s => s) (tag "x") "xy"               // works
bind_parse (tag "x") (fn (s : String) => tag "y") "xy"  // works
```

### Struct Field Access via Dot Syntax

Writing `loc.offset` (or a chain, `line.span.offset`) on a *locally bound* value works and is sugar for a bare `{ }` match: `loc.offset` desugars to `match loc { {offset} => offset }`, resolved against `loc`'s type at type-check time — so it works for any single-constructor type (not just `struct`-declared ones), not a fixed "method call" scheme. This only applies when the left of the first `.` is a local binding (a `def`/lambda parameter, a `let`); a bare `Module.name`-shaped path (no local binding by that name in scope) still resolves as an ordinary qualified reference, exactly as before:
```monad
struct Location { offset : I64, line : I64, column : I64 }

def get_offset (loc : Location) : I64 := loc.offset   // works

// Equivalent, if you'd rather write it out:
def get_offset (loc : Location) : I64 :=
    match loc {
        { offset, .. } => offset
    }
```
Dot access on an arbitrary non-identifier expression (e.g. `(mk_point 1 2).x`) isn't supported yet — only a chain of bare identifiers starting from a local binding.

### Debug `println!` in Type Checker Masks Real Errors

**Problem**: `core/src/eval/type.rs` contains debug `println!()` statements in `match_resolve_type_inner` (line ~1596: `"{left} != {right} arg=... ret=... vars=..."`) and `check_free_vars` (line ~1479: `"{detected} != {current_type}"`). These produce noisy output during normal type checking and can mask the actual error when diagnosing parse/type failures.

**Fix**: Remove these `println!` calls before production use. They are leftover debugging aids and are not guarded by any log level.

## Parser Combinator Library (init/src/parser.mo)

### Status: In Progress

Working: `tag`, `eof`, `alt`/`<|>`, `many0`, `many1`, `char_in_string`, `is_digit`, `is_alpha`, `is_alphanumeric`, `is_space`, `is_ident_char`, `satisfy`, `char`, `digit`, `alpha`, `space`, `take_while`, `opt`, `preceded`, `terminated`, `delimited`, `recognize` — 23/23 tests pass.

The self-hosted parser at `lang/src/parser.mo` provides a self-contained copy of the foundation types (`ParseResult`, `ParseError`) and combinators (`tag`, `alt`, `many0`, `many1`, `take_while`), char predicates, keyword check, identifier parser, whitespace skimmer, and number parser — 7/7 tests pass.

Key patterns when writing self-hosted Monad code:
1. **Avoid long `||` chains** (>10 operations) — the operator precedence climber slows down exponentially. Use nested `if/else` chains or split into helper functions (see `is_alpha_lower`/`is_alpha_lower2` pattern in `lang/src/parser.mo`).
2. **Avoid deep `else if` chains** (>15 levels) — the parser depth causes extreme slowdown. Split into multiple helper functions (max ~14 `if/else` per function).
3. **Avoid `use` for `init/parser`** — module loading produces "duplicate key" warnings that break `String.starts_with` and other native functions in test contexts. Make the parser file self-contained instead.
4. **Use `open TypeName`** — constructor names (like `success`/`fail`) are not available without opening the type.
5. **Type checker limitation with `ParseResult`** — matches on `ParseResult A` must avoid nested matches on `ParseResult B` where `B != A` (different type variables). Use separate functions to extract values at each level.

### Known Type Checker Issues

1. **`open` doesn't propagate**: `open ParseResult` within `parser.mo` doesn't affect external modules. Inner opens are not applied to module exports. Functions using `open`-ed constructors must be defined inside the same module. Workaround: bind results to a typed parameter before matching (see `many0`/`many1` implementation pattern in `init/src/parser.mo`).
2. **Forall inference on polymorphic combinators**: The type checker correctly instantiates implicit forall parameters on functions like `map_parse` and `bind_parse`, whether called with a concrete named function (`map_parse id_str (tag "x") "xy"`) or an inline lambda, annotated or not (`map_parse (fn s => s) (tag "x") "xy"`) — confirmed directly. If a combinator call fails with "Variable mismatch, expected ... found {B : Type} -> {A : Type} -> ...", the cause is elsewhere (e.g. a genuine type mismatch); it is not a lambda-argument limitation.
3. **`Map.insert`/`Map.lookup` (typeclass method dispatch) can fail at
   runtime with `eval error: scope: scope: Map.lookup not found` inside
   deeply-recursive self-hosted-compiler code paths** — specifically
   observed when a self-hosted function using `Map`/`BOrd` class methods
   (`std/src/map.mo`'s `instance [BOrd K] Map BTreeMap`) gets called
   repeatedly through `lang.module`'s dynamic module-loading/dependency-
   walk (`load_module_with_dependencies`, exercised by
   `slow_tests/src/typecheck_lang_tests.mo`'s `test_typecheck_lang_main`, the
   only test that exercises that runtime path). Not reproduced when the
   same `BTreeMap` usage is type-checked directly (e.g. `lang/src/json.mo`
   alone) — the failure is specific to this recursive/dynamic-scope
   context, not to `BTreeMap`/`BOrd` in general. A workaround exists
   (bypass the `Map`/`BOrd` class methods and call
   `BTreeMap.insert_loop`/`BTreeMap.lookup_loop` directly with the
   ordering passed as **plain function values**, e.g. built from
   `String.lt`/`String.gt` rather than `BOrd.lt`/`BOrd.gt`) — but see the
   next item before reaching for it.
4. **`BTreeMap` is markedly SLOWER than a plain `List` + linear scan for
   the small collection sizes typical in this self-hosted compiler's own
   code, once everything runs through the tree-walking evaluator.**
   Measured directly: replacing `lang/src/module.mo`'s `List ModulePath` +
   `list_contains` cycle-detection sets with `BTreeMap ModulePath Unit`
   (using the plain-function-value workaround from the item above, to
   dodge the dispatch bug) took `test_typecheck_lang_main` from 2.1s to
   29s; additionally converting `elaborate.mo`'s `union_ids`/`id_member`
   the same way pushed it to 53s — a ~25x regression overall, not an
   improvement, despite the asymptotic complexity genuinely being better
   on paper (O(n log n) vs O(n²)). The self-hosted interpreter's per-call
   overhead for tree-node allocation/rebalancing dominates at the
   collection sizes actually seen here (module counts, free-variable
   lists — tens, not thousands), so the crossover point where `BTreeMap`
   would actually win is never reached in practice. **Do not replace
   `List`+linear-scan with `BTreeMap` in self-hosted (`lang/*.mo`) code
   without measuring end-to-end wall-clock time first** (e.g.
   `time cargo run -- test slow_tests/src/typecheck_lang_tests.mo`) — Big-O
   analysis alone is not a reliable guide to real performance here.
5. **`self-hosted-compiler-perf.md` phase-timing infra**: `lang/src/module.mo`'s
   `check_file_cached` now wraps its three phases (scope/dep resolution,
   strict parse, typecheck) with `Bench.now`/`Bench.report` calls gated
   on `verbose` — `run cli/src/main.mo -- check <files> --verbose` prints
   `scope=`/`parse=`/`check=` timings per file, silent otherwise. This
   is distinct from the Rust-level `--benchmark` flag (which only times
   the outer per-file load, not phases *inside* the self-hosted checker
   while it runs) — use this tool to answer "which phase dominates"
   before touching self-hosted-checker performance, the same way item 4
   above already demonstrates for data-structure choices.
6. **Measured, not worth it: flattening `HashMap`'s 16-way bucket
   dispatch** (`std/src/map.mo`'s `HashMap.get_bucket`/`set_bucket`,
   originally a single 16-deep `if U64.beq N idx` chain). Splitting it
   into two <=8-deep tiers (mirroring `lang/src/parser.mo`'s
   `is_alpha_lower`/`is_alpha_lower2` pattern, itself a real, proven win
   for *parser* code) was tried and measured directly with a dedicated
   isolated micro-benchmark (`bench/src/hashmap_bucket_dispatch.mo` — pure
   `get_bucket`/`set_bucket` call volume, decoupled from `HashMap`'s own
   hashing/allocation cost), reproduced across two independent runs at
   two sizes (n=50000/200000): unflattened `set_bucket` 485-489ms/
   1950-1956ms vs. flattened 638ms/2568ms; unflattened `get_bucket`
   461-468ms/1837-1840ms vs. flattened 512ms/2045ms — a consistent
   **~10-30% regression**, not an improvement. Root cause (inferred, not
   separately measured): splitting into `get_bucket_lo`/`hi`
   (`set_bucket_lo`/`hi`) trades fewer `U64.beq` comparisons per call for
   one extra function-call boundary plus an extra `U64.lt` dispatch check
   on *every* call, and this interpreter's per-call overhead outweighs
   the comparisons saved at this chain depth (16 is apparently still
   short enough that the `>15 levels` rule's *depth*-driven slowdown
   hasn't kicked in yet; splitting adds a *call*, which is the more
   expensive operation here). Reverted — `std/src/map.mo`'s `get_bucket`/
   `set_bucket` remain the original single 16-way chain. Kept
   `bench/src/hashmap_bucket_dispatch.mo` as standing infrastructure so this
   isn't re-investigated blind. A second data point (after item 4's
   BTreeMap regression) that a proven win in one part of this
   interpreter (parser recursion depth) doesn't automatically transfer to
   another (hot-path dispatch call count) — measure per case.
7. **Native `string_lt`/`string_gt`/`string_hash` fast paths**
   (`core/src/core_native.rs` + `init/src/string.mo`): `String.beq` already
   had a native path (`string_eq`, plain `&str == &str`); `String.lt`/
   `String.gt`/`String.hash` didn't — they were self-hosted `.mo` code
   that converted both operands through `String.to_list` (materializing
   a full `List U8` linked list) before comparing/folding, even though
   `Identifier`/`ModulePath`'s `BOrd`/`Hashable` instances
   (`lang/src/types.mo`) delegate to them on every scope-`HashMap` op. When a
   self-hosted function's cost is dominated by an allocation-heavy
   conversion rather than genuine self-hosted logic, check whether a
   native already exists for a sibling operation (here, `string_eq`)
   before assuming the self-hosted version is the only option. The
   self-hosted implementations were kept (renamed
   `..._selfhosted`/`bytes_lt_selfhosted`/etc., not deleted) as the
   intended long-term implementation to switch back to once more of the
   compiler is self-hosted and the interpreter itself is faster (see
   item 8) — this native fast path is explicitly temporary and
   pragmatic, not a retreat from self-hosting.
8. **Tail-call optimization in `core/src/core_eval.rs`**: `eval`'s `App`
   case called `apply`, whose `Closure` branch called
   `eval(&body, &extended, ...)` — a real recursive Rust call despite
   being syntactically a tail call; `Match`'s dispatch had the identical
   shape. Every self-recursive closure application (an ordinary
   accumulator-style `.mo` loop) grew the native Rust stack by a frame
   per iteration — confirmed by `bench/src/scope_lookup.mo` stack-
   overflowing at n≈1000 even under 64MB worker-thread stacks.
   `eval` is now a `loop` over owned `(cur_ir: IrRef, cur_env: EnvRef)`
   state — `App` applying to a `Closure`, and `Match` dispatching to an
   arm, `continue` the loop (reassign state, `Arc::clone`, O(1)) instead
   of recursing. Every *other* recursive `eval` call (an `App`'s
   `fun`/`arg`, a `Match`'s scrutinee, `Con`/`Ntv`'s argument list) stays
   real Rust recursion on purpose — bounded by *static* source-term
   nesting depth, not *dynamic* call count. This means genuinely
   non-tail-recursive `.mo` code (e.g. `len xs = match xs { cons _ t =>
   1 + len t, ... }`) still consumes O(N) Rust stack depth, same as any
   language with TCO — the 64MB worker-thread stack (`core/src/lib.rs`)
   stays in place as a backstop for that case, it did not become
   unnecessary. Standing proof this works:
   `core_eval::tests::test_tail_recursive_countdown_survives_a_million_iterations_on_default_stack`,
   a self-recursive `Global` closure driven to n=1,000,000 under a
   *default*-sized test-thread stack. Bonus, not the primary goal:
   `test_typecheck_lang_main` (the compiler typechecking its own ~50-file
   corpus) dropped from 600.5s to 409.6s (~32% faster) from fewer
   allocations (no per-call `apply`/`dispatch` Rust frame).
9. **Two independent, real fixes for `merge_scope_data`/`PreludeInitBase`
   found and landed in parallel (on separate branches, later reconciled
   by rebase) — both kept, since they address genuinely different parts
   of the same cost.** Item 8's phase timing found the SCOPE phase
   dominating per-file check time by up to ~90x over the CHECK phase
   (e.g. `init/src/id.mo`: scope~4.3s vs. check~0.05s) — NOT the CHECK phase
   where `union_ids`/`free_vars` (`lang/src/elaborate.mo`, `lang/src/types.mo`)
   live, confirming `union_ids` is not worth optimizing.
   - **Fix A** (`lang/src/module.mo`'s `load_module_with_dependencies_and_
     prelude_cached`): `extract_all_dependencies_go`'s `visited`
     accumulator was seeded with `base_covered` (the shared
     `PreludeInitBase`'s already-loaded module set) so the walk would
     skip re-visiting it — but that function returns `visited` verbatim
     once its to-visit queue empties, so every call returned the
     *entire* `base_covered` set back as "extra deps to load", and the
     caller reloaded (re-parsed, re-scope-built) all of prelude+init
     from scratch for every single file — precisely the O(N*D)
     redundancy `PreludeInitBase` was built to eliminate. Fixed by
     seeding `visiting` instead of `visited`: in this walk's
     non-backtracking shape (a dependency's own subtree is processed via
     the same sequential recursive call that continues on to its
     siblings, never popped) the two parameters are already functionally
     equivalent "seen" sets for skip purposes, so this changes nothing
     about what gets skipped, only what gets correctly returned as
     empty/small instead of the whole base.
   - **Fix B** (`lang/src/module.mo`'s `merge_scope_data`, `std/src/map.mo`):
     even with Fix A landed, `merge_scope_data base_sd merged_extra`
     still merges the two `ScopeData`s' `def_refs` `HashMap`s every
     file — the original implementation did this via `HashMap.to_list
     dr1` (a full walk+concat of every bucket) followed by one
     `Map.insert`-equivalent call per entry to fold it into the other
     side, effectively rebuilding a `HashMap` from scratch bucket-by-
     bucket-and-back on every call regardless of how large `dr1` was.
     Replaced with `HashMap.merge_buckets`: merges two `HashMap`s
     directly bucket-by-bucket via 16 `List.append` calls, needing NO
     re-hashing at all — safe specifically because both sides already
     hashed their keys with the same function, so a key in bucket `i` on
     one side is always in bucket `i` on the other. Needs no
     `[Hashable K, BOrd K]` constraint either (unlike the `to_list`+
     refold approach it replaces), so it also sidesteps the
     `[Constraint]`-annotated-function class-method-dispatch limitation
     `std/src/map.mo` already documents elsewhere — and needs no empty-`sd2`
     short-circuit either (a fixed 16 bucket-pair appends is already
     cheap enough regardless of size).
   - `bench/src/hashmap_bucket_dispatch.mo` (item 6) was tried FIRST as a
     general "flatten `HashMap`'s dispatch" fix and found not to help;
     these two much more targeted fixes (WHERE the redundant work
     happened, and HOW one specific merge was implemented) are what
     actually delivered the win — a reminder that a hot function's own
     internals aren't the only place a real win can hide; how often and
     against what it's actually called can matter just as much.
   - Combined effect, both fixes together, measured after reconciling
     them via rebase: `test_typecheck_lang_main` dropped from 545.05s
     (the item-8/TCO baseline) to **97.07s — an 82% reduction, ~5.6x
     faster** — essentially identical to Fix B's own standalone number
     (97.38s, measured before this rebase), not additionally improved by
     Fix A on this specific end-to-end metric. That's expected, not a
     sign Fix A is redundant: Fix B's bucket-merge is a fixed 16-append
     cost regardless of `merged_extra`'s size, so shrinking
     `merged_extra` (Fix A's effect) doesn't move `merge_scope_data`'s
     own cost further once it's already cheap — but Fix A still matters
     on its own terms, for the cost `merge_scope_data` never touches at
     all: `load_dependency_scopes` actually parsing/scope-building
     `extra_deps`' files. `test_typecheck_lang_main`'s own dependency
     shape (mostly prelude+init-covered, little genuine `lang/`-internal
     `extra_deps` per file) just doesn't happen to exercise that
     saving much; files with real non-base dependencies still benefit
     from Fix A the way its own commit measured directly (`std/src/show.mo`
     scope phase 4224ms → 712ms; `lang/src/module.mo` 418.8s → 367.3s).
     Full corpus `check init std examples`: 51 files, 181 errors,
     unchanged from before either fix (confirmed via a direct isolated
     stash comparison on this exact combined commit), completing in
     well under a minute where the pre-item-8 baseline could not finish
     within a 590s timeout at all. Remaining known gap, explicitly out
     of scope for both fixes: `PreludeInitBase` only covers prelude+
     init, not a file's dependencies on *other, non-base* corpus files
     during a multi-file run (real, non-base `use` dependencies within
     `lang/`/`std/` still pay a real, uncached reload cost) — a
     separate, larger architectural change (a whole-corpus, not just
     prelude+init, module-scope cache) and a natural next target for a
     future performance pass.
10. **Whole-corpus module-scope cache** (`ModuleScopeCache`,
    `lang/src/module.mo`). NOTE (2026-09-03): this item describes
    `ModuleScopeCache`, which is now superseded on the live path by
    `ModuleInfoCache` (caching `ModuleInfo`, i.e. the parse, rather
    than `ScopeData`) threaded through `elaborate_loaded_modules_cached`
    -- see item 24. `ModuleScopeCache` and the
    `load_module_with_dependencies_and_prelude_cached` path this item
    describes still exist but are no longer what `check`/`test` run on;
    `load_module_with_dependencies`, named below, was deleted outright.
    The reasoning about WHY caching is sound here (flat, not recursive,
    dependency loading) carries over unchanged and is why
    `ModuleInfoCache` is equally safe. Closes item 9's own remaining gap: a growing,
    whole-`run_check`-invocation cache of already-loaded non-base
    dependencies' `ScopeData`, threaded through `run_check_loop`/
    `check_file_cached`/`load_module_with_dependencies_and_prelude_
    cached` the same way `PreludeInitBase` is, except mutable rather
    than fixed. Fixes the exact redundancy item 9 measured but didn't
    address: `lang/src/types.mo` was independently loaded 54 separate
    times in one multi-file run (54 files `use lang.types`), now served
    from cache after the first. Keyed on `ModulePath` (grep-verified
    safe for the current corpus — only two bare, non-dotted `use`s
    exist anywhere, each resolved from exactly one `base_dir`, no
    observed collision; flagged as a structural, not observed, risk in
    the code, with resolved-path keying noted as a cheap fast-follow if
    it's ever needed). Correct because this codebase's dependency
    loading is flat, not recursive: each dependency's `ScopeData` is
    built from only its own decls, independent of who asked, so a
    cached value is bit-identical to a fresh load; cycle detection
    (`extract_all_dependencies_go`'s `visiting`/`visited`) is completely
    untouched — the cache only changes HOW an already-decided-necessary
    dependency's value gets produced, never WHICH dependencies a caller
    needs. Verified: 1274/1274 self-hosted tests passed (baseline
    unchanged), real speedup on repeated-dependency scenarios (a 4-file
    sample's scope-phase times dropped 13-47% per file as later files
    hit the cache for shared deps). Deliberately NOT measured against
    `slow_tests/src/typecheck_lang_tests.mo`'s `test_typecheck_lang_main` —
    that test is a single flat dependency-closure walk from one call
    site (`load_module_with_dependencies`, not the `..._and_prelude_
    cached` path this cache lives on), so it cannot exhibit cross-file
    redundancy by construction; its own regression (see item 11) is a
    separate story.
11. **`test_typecheck_lang_main` regression (97.07s → 257.61s since
    item 9): investigated as two candidate causes, one fixed (small,
    real win), one measured and found to be diffuse organic growth,
    not a single fixable hotspot.**
    - **Candidate 1, fixed**: `build_scope_from_decls` (`lang/
      scope.mo`) does a second full pass over every module's decls
      (`alias_decls_in_scope`, added by the open/use bare-name-aliasing
      commit) even when that module has no `use`/`open` declarations
      at all to alias — pure wasted work for the ~12% of the corpus
      that's true of (grep-counted). Measured directly (temporary
      `Bench.now`/`Bench.report` instrumentation, since reverted):
      `alias_decls_in_scope` is ~29% of `build_scope_from_decls`'s own
      cost on a representative sample — real, but `build_scope_from_
      decls`'s own cost is itself a minority of a file's total "scope"
      phase (most of which is I/O/parsing). Fixed with a cheap
      `decls_have_aliasable_decls` pre-check (O(decls), O(1) per decl —
      a bare tag match, no `ScopeData` work) that skips the whole
      second pass when it would do nothing. Small, safe, and
      correctness-preserving by construction (nothing to alias means
      the skipped pass would have been a no-op regardless) — not
      claimed to explain the bulk of the 97s→257s regression on its
      own, given it only fires for ~12% of module loads.
    - **Candidate 2, measured and NOT the cause — the CHECK phase's own
      per-declaration cost has grown, but not through the mechanism
      first suspected.** `lang/src/typecheck/infer.mo`'s `find_inductive_
      for_cases_by_constructor` (a linear scan over every inductive in
      the fully-merged scope, ~218+ `type` declarations corpus-wide)
      looked like a strong candidate by code-reading alone — the CHECK
      phase is now often 2-4x LARGER than the SCOPE phase for real
      files (`lang/src/pretty.mo`: scope≈15-29s, check≈57-83s across
      several runs), the opposite of this section's own item 9
      assumption (based on a tiny `init/src/id.mo` file where scope
      dominated ~90x over check). Instrumented directly (temporary
      counters on both the fast path and this fallback, since
      reverted) and ran against `lang/src/pretty.mo` (60 `match`
      expressions, the worst measured `check=` offender): **zero**
      calls to either path were logged — this function isn't even
      being reached by the self-hosted checker's current coverage for
      this file. The hypothesis is disproven, not just unconfirmed.
      Followed up with per-declaration timing instead (temporary,
      since reverted): costs are roughly UNIFORM (~600-900ms) across
      most of `pretty.mo`'s 103 declarations, not concentrated in a
      handful of outliers — consistent with organic, distributed
      complexity growth in `type_check`'s own per-declaration work
      (skolemization now extended to more decl kinds, match-case
      validation, struct-literal/struct-update checking, Pi-chain
      handling all landed since item 9's 97.07s measurement) rather
      than one identifiable, fixable hot path. **Do not chase a single
      fix here without new evidence** — this needs either a much
      deeper per-node profiling pass inside `type_check` itself (a
      separate, larger investigation) or acceptance that this is the
      accumulated cost of genuine feature growth. Recorded here so it
      isn't re-investigated blind from the same starting hypothesis.
12. **`SharedStr` (Arc-backed zero-copy string slicing) + parser/type-
    checker follow-ups — the parser's own cost model, never previously
    examined, turned out to hold the largest lever in this whole history.**
    Full writeup: `plans/implementations/shared-str-and-typecheck-
    optimization.md`. Three independent tracks, one root-cause Rust
    change plus two self-hosted-only tracks extending items 9-11's
    already-proven patterns:
    - **Track 1 (root cause, Rust)**: `IrLit::Str` (`core/src/core_ir.rs`)
      was a plain owned `String` — `string_slice`/`string_drop`
      (`core/src/core_native.rs`) both did `s.get(range).unwrap_or("")
      .to_string()`, a full byte copy on every call. The self-hosted
      parser (`lang/src/parser.mo`, `lang/src/parser/combinators.mo`) threads
      "the rest of the source file" through nearly every grammar
      function this way, consuming it a few bytes at a time — so parsing
      a file of length N cost `O(N)+O(N-1)+...+O(1) = O(N²)`, independent
      of grammar complexity. Fixed by a new `SharedStr` type
      (`core/src/shared_str.rs`): `Arc<str>` backing + a `(start, end)`
      byte-range view, so `slice`/`drop` become O(1) (bump a refcount,
      adjust two `usize`s) instead of copying. `Arc`, not `Rc` — the
      evaluator runs on real OS threads (`run_tests_parallel`,
      `force_global_with_timeout`'s per-call thread spawn,
      `std/concurrent`'s real-thread runtime; `Value` is asserted
      `Send + Sync` at compile time), the same tradeoff `Env`
      (`core_value.rs`) already made and documented. `read_file` is the
      key construction site: the whole file's content becomes ONE
      backing allocation, and every subsequent `slice`/`drop` during
      parsing shares it. Small, mechanical blast radius despite touching
      the runtime's value representation: 5 files, ~35 call sites total
      (`core_ir.rs`, `core_native.rs`, `lower_core_ir.rs`,
      `eval/meta_reflect.rs`, `lib.rs`) — most natives (`string_eq`,
      `string_hash`, `string_length`, ...) needed zero changes since they
      only ever read via a derived `&str`.
    - **Track 2 (self-hosted parser, `.mo`-only)**: `take_while`/
      `take_while_loop` (`lang/src/parser/combinators.mo`) used to build its
      matched-text accumulator via per-character `String.concat acc ch`
      — an independent, compounding O(L²) cost (for a token of length L)
      on top of Track 1's fix. Rewritten to track the original input
      alongside the shrinking remainder and take exactly ONE
      `String.slice` when the predicate first fails, instead of L
      accumulator concats — benefits every `take_while`-based scan
      (identifiers, numbers, whitespace/comment-skipping) at once, not
      just call sites that discard the matched text. Also: `is_digit`
      (`lang/src/parser/char_preds.mo`) rewritten from a fresh-list-plus-
      closure-plus-`List.any` scan to a plain `if/else` chain matching
      every sibling predicate in the file (the already-established,
      already-proven-faster pattern); `op_lookup_prec`/`op_lookup_rassoc`
      (`lang/src/parser/core.mo`) merged into one `op_lookup_entry` scan so
      `expr_climb_op_prec`/`expr_climb_op_rhs_ws` (`lang/src/parser.mo`) walk
      `op_table` once per operator token instead of twice.
    - **Track 3 (self-hosted type checker/scope/module, `.mo`-only,
      independent of 1/2)**: `ScopeData.inductives` (`lang/src/types.mo`)
      converted from `List Inductive` to `HashMap ModulePath Inductive`
      — the identical, already-proven move item 4/`def_refs` made
      (commit `532df61`). `scope_data_find_inductive`
      (`lang/src/scope.mo`) was a linear scan over every inductive in the
      merged scope (~218+ corpus-wide) reached on the PREFERRED,
      non-fallback path added by the match-case-validation (`0dbc3f2`)
      and struct-literal (`0303aee`) commits — both landed after item 9's
      97.07s baseline, and exactly the kind of "diffuse organic growth"
      item 11's own instrumentation was consistent with but didn't
      isolate (item 11 counted calls into the OLD fallback function,
      which this new preferred path bypasses entirely). `.classes`, the
      sibling field, stayed a `List` — confirmed no by-name lookup
      anywhere in the corpus, so no read-side benefit from converting
      it. Track B's `decls_have_aliasable_decls` no-op-skip guard
      (already landed, see item 11) was applied inside
      `build_scope_from_decls` but NOT at two sibling call sites in
      `lang/src/module.mo` (`load_module_with_dependencies`,
      `load_module_with_dependencies_and_prelude_cached`) that
      unconditionally re-ran the identical "outer aliasing" pass — the
      FIRST of these is exactly `test_typecheck_lang_main`'s own call
      path (item 10 explicitly noted it couldn't measure that test
      against the whole-corpus module-scope cache for this reason).
      Extended the same guard to both. Also added a `ys`-empty
      short-circuit to `list_append`/`merge_instances` (`lang/src/module.mo`,
      mirrored in `lang/src/scope.mo`) — `merge_scope_data`'s two real call
      sites always pass the large shared-base side first and the
      small/often-empty side second, the opposite of the ONLY existing
      fast path (`xs = List.empty`), so `class_defs`/`instances`/
      `classes`/`infixes`/`conflicts` were fully walked and reallocated
      on every file checked for zero benefit — same bug shape item 9's
      Fix B fixed for `def_refs`, just never extended past that one
      field.
    - **Measured** (release build, `--verbose` phase timing +
      `test_typecheck_lang_main` as the standing end-to-end benchmark,
      same methodology as items 8-11): parse-phase time roughly HALVED
      across every file size tried, Track 1+2 combined
      (`init/src/id.mo`: 78ms→35ms; `lang/src/pretty.mo`: 6681ms→2827ms;
      `lang/src/json.mo`: 4000ms→1901ms — a consistent ~55% reduction
      regardless of file size, confirmed via a real git-stash before/
      after rebuild, not just a single post-fix run). All three tracks
      combined: `test_typecheck_lang_main` (the item 8-11 regression
      benchmark) dropped from **262.30s to 105.31s — a 60% reduction,
      ~2.5x faster** — back down near item 9's original 97.07s baseline
      despite all the feature growth items 10/11 identified as the
      regression's cause. Verified: `cargo test` 625/625 (616 baseline +
      9 new `SharedStr` unit tests); full corpus
      `cargo run --release -- test init std lang examples slow_tests`
      1274/1274, identical to baseline; `cargo run --release -- check
      init std lang examples` unchanged at 2 pre-existing errors/7
      pre-existing warnings (confirmed via the same check against an
      unmodified baseline — none of these are new).
    - **Follow-up (Track 4): `string_body_loop`'s O(L²) accumulator,
      confirmed and fixed — gap partially closed, not fully.** The gap
      flagged above (parse-phase superlinearity: `init/src/id.mo` 28
      lines→35ms vs. `lang/src/pretty.mo` 885 lines→2827ms, ~80x time for
      ~32x lines) was traced to `lang/src/parser/string.mo`'s
      `string_body_loop` (string-literal body scanning), which built its
      accumulator via one `String.concat acc ch` per character — the
      exact pre-Track-2 `take_while` shape, deliberately left alone at
      the time because `\`-escapes genuinely change content
      byte-for-byte and can't collapse to a single final slice the way
      `take_while`'s non-escaping scan could. Fixed by tracking where the
      current *unescaped run* started (`run_start`) alongside the
      shrinking `input`, paying for one `String.slice` + `String.concat`
      per run boundary (a `\` or the closing `"`) instead of per
      character — a typical un-escaped string literal is now ONE slice,
      zero concats; a string with E escapes is O(E) concats instead of
      O(L). Measured: parse-phase time dropped further on top of Track
      1+2 (`lang/src/pretty.mo` 2827ms→2045ms, `lang/src/json.mo`
      1901ms→1706ms), and the scaling ratio improved (`id.mo` 28
      lines→33ms vs. `json.mo` 1213 lines→1706ms is now ~52x time for
      ~43x lines, close to linear — vs. `pretty.mo`'s remaining ~62x
      time for ~32x lines, still mildly superlinear, likely other
      per-character accumulation this pass didn't chase further). This
      did **not** move `test_typecheck_lang_main`'s end-to-end number
      (105.71s, within noise of the 105.31s Track 1-3 baseline) —
      confirms item 11's own conclusion still holds: for this benchmark
      the `check` phase dominates total cost by ~50-100x over `parse`
      (e.g. `lang/src/pretty.mo`: scope=21866ms, parse=2045ms,
      check=97276ms), so a parse-only fix, however real, is invisible at
      the end-to-end level. Verified: full corpus
      `cargo run --release -- test init std lang examples slow_tests`
      1274/1274 unchanged; `cargo run --release -- check init std lang
      examples` unchanged at 2 pre-existing errors/7 pre-existing
      warnings.
    - **Track 3d (from the original plan doc), measured and skipped**:
      `check_file_cached`'s duplicate file read (strict parse re-reads
      what `build_scope_with_deps_and_prelude_cached` already read once
      for the lenient parse, plus a handful of `file_exists` stats) is,
      per this pass's own `--verbose` numbers, on the order of a few
      syscalls against a `check`/`scope` cost measured in **tens of
      seconds per file** — orders of magnitude too small to register.
      Recorded as a deliberate no-op rather than re-investigated blind
      later; the actual lever, if this history continues, is item 11's
      already-identified one: a per-node profiling pass inside
      `type_check` itself.
13. **The "per-node profiling pass" item 11/12 called for, actually done —
    and it found something nobody was looking for.** No `perf`/
    `flamegraph`/`samply` exist in this sandbox (confirmed); `valgrind`
    does, and needs no special privileges (binary translation, not
    `perf_events`). Two independent investigations, one Rust-level (via
    `valgrind --tool=callgrind`) and one self-hosted-level (via targeted
    ablation), against `test_typecheck_lang_main` (the standing item
    8-12 benchmark, ~86-106s depending on machine load run-to-run — the
    variance itself turned out to matter, see below).
    - **Getting the target right matters**: `monad-rs check <file>` (bare
      CLI) goes through `core/src/lib.rs`'s `check_files` →
      `term::module::load_module_from_text_typed` — a *separate*, legacy
      Rust-native tree-walking checker kept for parity, **not** the
      self-hosted `lang/*.mo` checker. `monad-rs test <path>` is the
      correct profiling target — it runs a self-hosted `#[test]` def
      through the real `CoreIr` evaluator.
    - **Rust-level, via callgrind (headline finding)**: profiled a small
      scratch `#[test]` (`typecheck_file "std/src/map.mo"`, mirroring
      `typecheck_lang_tests.mo`'s own helper) two ways — once fully
      instrumented from process start, once with `--instr-atstart=no`
      plus a live `callgrind_control -i on <pid>` toggle fired exactly
      when self-hosted test execution begins (after Rust-native bootstrap
      compilation of the ~32 loaded modules completes), to cleanly
      separate "checking+lowering the self-hosted compiler's own source"
      from "the self-hosted checker actually running." The isolated,
      bootstrap-free profile is **83-99% `malloc_consolidate`/
      `_int_free_chunk`/`free`/`unlink_chunk`/`BTreeMap::drop`** — i.e.
      the whole counted window is dominated by tearing down ONE large
      heap structure, not by `core_eval`/`exec_native`/actual checking
      logic (which combined don't even clear the 99%-cumulative
      threshold). Root cause: `LoadedModules` (`core/src/term/module.rs`)
      is `#[derive(Clone)]` over `modules: Map<ModulePath, Module>`
      where `Module` itself holds SIX more `Map`(`=BTreeMap`) fields
      (`defs`, `inductives`, `macro_defs`, `decl_gens`, `infix`, plus an
      `instances: Vec`) — i.e. every loaded module's ENTIRE checked AST.
      `evaluate_one_test_file`/`check_files` (`core/src/lib.rs`) each
      **deep-clone this whole registry once per checked/tested FILE**
      (`base_loaded.clone()`/`master_loaded.clone()`), and drop it again
      at file-scope exit. This is a *deliberate* correctness fix, not an
      oversight — the doc comment at `evaluate_one_test_file` explains it
      prevents cross-test-file bare-name collisions (confirmed against a
      real corpus case: `init`'s `foldable_tests.mo`/
      `foldable_tests_fold.mo` both declare `test_foldr_sum`) — but its
      performance cost was never measured until now, and a plain
      `#[derive(Clone)]` over nested `BTreeMap`s of full AST trees is the
      most expensive way to buy that guarantee. A cheaper fix preserving
      the same isolation (each file's own additions stay local, the
      shared base is never mutated in place) would replace `Map`/
      `BTreeMap` here with something structurally-shared (e.g. `im::
      OrdMap`, or wrap each field in `Arc` for copy-on-write), making the
      per-file clone O(1) instead of O(total loaded-corpus AST size) —
      **not implemented this pass** (investigation only), but the
      highest-confidence, best-understood lead this whole history has
      produced. Cost scales with `files tested × total corpus size`, the
      same "gets worse as the corpus grows, never fixed" shape as several
      other items here — for a single huge file (`test_typecheck_lang_main`
      itself, one file with one `#[test]`) it's a bounded one-time tax
      (small relative to that benchmark's ~86-106s total); for the FULL
      multi-hundred-file test/check suite it is paid once per file and
      was not separately quantified at that scale this pass.
    - **Rust-level, ruled out**: the two hypotheses this investigation
      started from — `Value::clone()` on `Con`/`PartialNtv` being an
      uncontrolled deep recursive copy (`Con`/`PartialNtv` hold
      `args: Vec<Value>`, not `Arc<[Value]>`, so every self-hosted
      `List`/`HashMap`/record clone is structural, not O(1)), and
      `Env::get` (`core/src/core_value.rs`) being an O(lexical-depth)
      pointer-chain walk — are both real but **negligible** here:
      `Env::drop_slow` (the closest attributable symbol) totals 0.19% of
      instructions combined across both variants in the full
      (non-isolated) profile; no `<Value as Clone>::clone` symbol clears
      even the smallest visible line (~0.01%) in either profile. Ruled
      out as significant factors for this benchmark, dwarfed by the
      `LoadedModules` clone/drop cost by 3-4 orders of magnitude.
    - **Self-hosted-level, via ablation — all ruled out**: `CoreIr` nodes
      carry no spans/names, and `force_global` only fires once per
      memoized global (not once per call), so callgrind can't attribute
      cost to a *self-hosted* function name — a pure-functional language
      also has no cheap way to add call counters without threading state
      through every signature. Used ablation instead (temporarily stub
      the candidate to a trivial O(1) wrong-but-non-crashing
      implementation, measure the wall-time delta on
      `test_typecheck_lang_main`, revert): stubbed
      `find_class_def_in_list`, `find_instances_by_class`,
      `scope_data_find_inductive_by_constructor` (`lang/src/scope.mo`),
      `unify`'s `Similar.similar` structural-walk fallback
      (`lang/src/typecheck/unify.mo`), and `struct_lit_find_field`
      (`lang/src/typecheck/infer.mo`) all at once — every one of these was a
      linear-scan sibling of an already-`HashMap`-converted field
      (`class_defs`/`instances` never got the `def_refs`/`inductives`
      treatment) or an unmemoized nested scan, exactly the bug shapes
      items 4/9/12 already fixed elsewhere. Result: **85.93s vs. an
      86.72s clean baseline — no measurable effect**, well inside this
      benchmark's own ~20s run-to-run machine-load noise band (observed
      86.72s and 105.71s for the *same* unmodified binary across
      different points in this session). All five ruled out as
      contributors to this benchmark's cost. `scope_find_local`/
      `nth_type`'s O(nesting-depth) walk (candidate 6) was NOT ablated —
      unlike the other five, it fires on every free/bound variable
      reference including ordinary global references, and stubbing it
      would break most of the corpus rather than just degrade gracefully
      — left unmeasured rather than guessed at; by analogy to the other
      five siblings all measuring null, and item 6's own prior finding
      that flattening loses to per-call overhead at this interpreter's
      typical scope depths, it's judged low-priority but is explicitly
      **not confirmed either way**.
    - **Bottom line**: the item 11/12 hypothesis that `type_check`'s own
      per-node logic hides a diffuse-but-real cost was not confirmed by
      this pass — everything self-hosted-level that could safely be
      measured came back null. The real, confirmed, actionable lead this
      investigation produced is Rust-level and outside `lang/*.mo`
      entirely: `LoadedModules`'s clone-per-file cost.
    - **Follow-up: fixed.** `Module`'s six AST-bearing fields (`defs`,
      `inductives`, `macro_defs`, `decl_gens`, `infix`, `instances`) and
      `LoadedModules`'s own `modules: Map<ModulePath, Module>` were
      `Arc`-wrapped (`core/src/term/module.rs`) — the same tool already
      used repeatedly on this branch (`SharedStr`'s `Arc<str>`, `Env`'s
      `Arc<Env>` chain), no new dependency. All six fields are private to
      `module.rs`, so the blast radius was fully contained: one
      constructor (`fn module(...)`) wraps each freshly-built map/vec in
      `Arc::new(..)`; the one live outer-map mutator (`add_module`) and
      the REPL-only `add_decl`/`get_module_mut` paths switched to
      `Arc::make_mut` (copy-on-write, free in practice since those values
      are always uniquely-owned at the point of mutation); every
      read-only accessor (`.defs()`, `.get_def()`, `LoadedModules::
      modules()`, ...) needed **no changes** — `&Arc<Map<K,V>>` derefs to
      `&Map<K,V>` at existing call sites. `Module::clone()` went from
      O(that module's own checked-AST size) to O(1) (a handful of `Arc`
      bumps); `LoadedModules::clone()`'s outer `BTreeMap` clone is now
      O(number of loaded modules) values that are themselves O(1) to
      clone, rather than O(total loaded-corpus AST size). Two more
      whole-registry clone sites inside the recursive module loader
      (`module.rs`, threading `loaded` by value through
      `load_decl_uses_modules`) and REPL/test-support clones (`lib.rs`,
      `core_check_module.rs`) all became cheap for free, no call-site
      changes needed. **Measured**: `cargo run --release -- test init
      std lang examples slow_tests` (the full corpus, ~100+ files, each
      paying the per-file clone this fix targets) dropped from
      **215.55s to 173.51s — a ~19.5% wall-time reduction** (`git stash`
      before/after, both 1274/1274 passing, unchanged). As predicted,
      `test_typecheck_lang_main` alone (one file, one clone) barely
      moved (86.72s→87.68s, within noise) — confirms the fix targets the
      per-FILE-tested cost specifically, not per-node checking cost.
      `cargo test` (all crates) and `cargo run --release -- check init
      std lang examples` both unchanged (625/625 core tests, 1 ignored;
      2 pre-existing errors/7 warnings). **Not fully explained**: the
      ~19.5% win, while real and worth keeping, is smaller than the
      83-99%-of-one-profile-window headline number might suggest —
      plausible explanation, not independently confirmed: some of that
      isolated-window `malloc`/`BTreeMap`-drop cost may belong to
      `core_check_module.rs`'s own per-file capture-key registries (the
      `BTreeMap<Atom, ModulePath>` machinery also visible in the
      original profile), built fresh once per file by `build_core_program`
      regardless of `LoadedModules`'s own clone cost — a DIFFERENT
      structure this fix didn't touch. Flagged as a possible next target,
      not chased further this pass.
14. **Follow-up to item 13's flagged remainder: found and fixed —
    `global_atom_paths` (`core_check_module.rs`), a `BTreeMap<Atom,
    ModulePath>` holding every known global across the whole corpus
    loaded so far, was fully cloned once per checked top-level `def`
    (`check_one_def_new`, twice — once for the per-def working copy,
    again when storing into `CoreProgram`'s `CheckedCoreDef.atom_paths`)
    and once per instance method (`check_one_instance_new` calls
    `check_one_def_new` once per method). With ~3,800+ defs across the
    corpus and a map that grows toward corpus size as checking proceeds,
    this is an O(defs × corpus-size) cost — the same "gets worse as the
    corpus grows" shape as item 13's `LoadedModules` bug, just at
    per-*def* rather than per-*file* granularity. Unlike `LoadedModules`
    (cloned-then-never-mutated, where `Arc`+copy-on-write sufficed),
    `global_atom_paths` is cloned-then-immediately-extended with new
    entries every time, so `Arc::make_mut` would trigger a full copy on
    the first insert anyway — no free win available from the same tool.
    **Fix**: added the `im` crate and introduced `AtomPathMap =
    im::OrdMap<Atom, ModulePath>` (`core/src/lib.rs`), scoped to exactly
    this one type family (NOT the general-purpose `Map<K, V>` alias,
    which covers many unrelated tables with no equivalent hot-path
    pressure — `StructFields.inductive_paths`, textually the same type
    but a separate, once-per-module, never-cloned table, was deliberately
    left as plain `BTreeMap`). `im::OrdMap`'s `.clone()` is O(1)
    (ref-counted structural sharing) and its `.insert`/`.extend` are
    O(log n) persistent updates instead of full copies, with an API
    (`.get`/`.contains_key`/`.insert`/`.extend`/`FromIterator`) close
    enough to `BTreeMap`'s to be a drop-in replacement at every existing
    call site (`core_check_module.rs`, `core_program.rs`,
    `raise_core.rs`, 5 signatures in `core_check.rs`,
    `lower_core_ir.rs`) — no logic changes anywhere, ~15 type-annotation
    edits total. **Measured**: `cargo run --release -- test init std lang
    examples slow_tests` (the full corpus, 1387/1387 passing unchanged
    before/after — corpus has grown since item 13's 1274/1274 count)
    dropped from **307.62s to 244.14s wall (-20.6%)**, and — a cleaner
    signal since wall time is subject to scheduling noise — **772.36s to
    511.47s in summed CPU-seconds (-33.8%)**. `cargo test` (627/627 core
    tests, unchanged) and `cargo run --release -- check init std lang
    examples` (2 errors/7 warnings, unchanged) both confirm no behavior
    change. **Not confirmed on the isolated benchmark**: unlike item 13,
    this fix's win doesn't show up on `test_typecheck_lang_main` run
    alone (`git stash` before/after, same session: self-reported test
    time 133.16s → 130.69s, within run-to-run noise) — the opposite
    pattern from item 13, where the per-*file* `LoadedModules` fix helped
    the single-file benchmark barely at all but the per-*def*
    `global_atom_paths` cost apparently doesn't dominate that one
    benchmark's own cost either, even though its dependency closure
    (`cli/src/main.mo` pulling in essentially all of `lang/`) is large.
    Separately: this session's baseline isolated run measured 133.16s,
    not the ~7-minute figure commit `7350f96`'s message cited for the
    same test — a large, unexplained discrepancy, not reproduced or
    chased further here (plausibly machine-load variance between
    sessions, given item 13's own note of ~20s run-to-run noise on this
    same benchmark — though a 5x gap is far outside that band and
    deserves its own look before being written off). The full-corpus
    number is the one that matters for the original complaint ("bootstrap
    compile takes many minutes" — i.e. checking/testing many files in one
    session, not one giant file in isolation), and it moved for real.
15. **Follow-up: the literal `bootstrap compile <file>` command has its OWN,
    much bigger, entirely separate bug — a diamond-dependency re-parse
    blowup in the self-hosted loader, not touched by items 13/14.**
    NOTE (2026-09-03): the fix described here is still in place, but
    several functions this item names by hand no longer exist —
    `load_module_with_dependencies`, `extract_all_dependencies`, and
    `load_dependencies_with_info` were deleted or folded away during the
    2026-09-01/02 dedup pass (`extract_all_dependencies_go` survives).
    Read the mechanism below (a per-node re-walk of an
    already-complete dependency list) rather than the specific names;
    the same shape recurred twice more, see item 24.
    Prompted by a direct question ("does the self-hosted checker load
    modules once or several times?"). Found **two structurally different
    module-graph traversals** in `lang/src/module.mo`:
    - `extract_all_dependencies`/`extract_all_dependencies_go` (lines
      366-419) — a correct, single-flat-list, cycle-safe walk with a
      `visited` set checked BEFORE the expensive work (disk read + parse)
      at line 393/399. Backs `load_module_with_dependencies`, which backs
      `check` and `test_typecheck_lang_main`'s `typecheck_file` — i.e.
      everything items 13/14 measured. A module reachable via N import
      paths is loaded exactly once here; traced directly against
      `lang/src/types.mo` (47/57 `lang/*.mo` files import it) to confirm.
    - `load_dependencies_with_info` (lines 1958-1993) — backs
      `load_file_modules`, which is what `compile`, `pretty`, and `test`
      (the three self-hosted CLI subcommands OTHER than `check`) actually
      run on — confirmed by grep, `cli/src/main.mo` lines 63/243/374. Despite
      `load_file_modules` already computing the complete, deduplicated
      closure ONCE up front (line 1941), `load_dependencies_with_info`
      re-called `extract_all_dependencies` AGAIN (old line 1974, from a
      FRESH empty `visited` set) for every node the first time it's
      visited, to re-derive that node's own dependency list, then
      recursed into it — completely ignorant that the outer list already
      contains everything that re-walk would rediscover. Every module in
      the closure paid its own full parse-and-walk of its downward subtree
      once per ancestor that reached it in the recursion — a superlinear
      (Σ over the closure of each node's own subtree size) blowup, same
      shape as the already-fixed "54× `lang/src/types.mo` reload" cross-FILE
      bug (items 9-10's `ModuleScopeCache`), just a fresh instance of the
      same pattern inside an unrelated function, and entirely un-touched
      by anything in items 13/14 (which only improved `check`/
      `test_typecheck_lang_main`, both on the OTHER, already-correct
      traversal). This is the literal path `bootstrap compile <file>`
      (`devenv.nix`'s `bootstrap` script → `cli/src/main.mo compile` →
      `compile_file` → `load_file_modules`) runs on — the exact command
      named in the original "bootstrap compile takes many minutes"
      complaint, and item 14's own closing note ("the full-corpus number
      is what matters... not one giant file in isolation") turned out to
      be only half the story: the ONE-file `compile`/`pretty`/`test`
      commands had their own, much larger, independent bug the whole time.
    **Fix**: simplified `load_dependencies_with_info` to a flat fold over
    the already-complete `deps` list — one `load_module_with_info` per
    entry, no re-derivation, no per-node subtree re-walk — mirroring the
    already-correct `load_dependency_scopes` (line 884) shape exactly.
    Kept the existing `list_contains_module_info` dedup guard (line 1965):
    not a leftover, since `load_file_modules` manually prepends
    `[prelude_module_path, init_module_path]` ahead of the already-flattened
    list, which can genuinely duplicate an entry. Pure `.mo`-source change,
    `lang/src/module.mo` only — no Rust touched. **Also removed, while in the
    area**: 9 dead top-level defs in the same file, each verified (via
    whole-repo grep, `.mo`/`.rs`/`.md`) to have zero references anywhere
    outside their own definition — `init_module_file_path`,
    `std_module_path`, `examples_module_path`, `lang_module_path` (a set
    of directory-path-string builders, superseded by
    `resolve_module_file`'s search-path resolution and never called),
    `parse_all_decls_strict` (superseded by `try_parse_decls_strict`
    calling `decls_parser_strict` directly, never through this wrapper),
    `try_read_module_file_default`, `load_module_with_dependencies_default`,
    `load_module_decls_with_dependencies_default` (three unused `""`-base-dir
    convenience wrappers), and `get_module_info_file_path` (an unused
    `ModuleInfo` accessor — its sibling `get_module_info_decls` IS used and
    was left alone). **Measured** (`git stash` before/after, same session):
    `bootstrap pretty cli/src/main.mo` (chosen because `pretty` only calls
    `load_file_modules` then prints decls — no type-checking, no codegen —
    so it isolates this fix's effect from everything else) dropped from
    **746.01s to 130.21s wall (-82.5%)**, **647.47s to 127.40s CPU-seconds
    (-80.4%)** — a ~5.7x speedup. Output verified byte-identical before/after
    (the only diffs: a build timestamp and one internal gensym counter,
    `_anon#NNNN`, which naturally shifts since fewer atoms get minted along
    the way — not user-visible). Smoke-tested the real commands:
    `bootstrap compile examples/hello.mo` succeeds end-to-end
    ("Compilation finished"); `bootstrap test examples/structs.mo` correctly
    loads and SKIPs (no codegen needed, so it exercises the fixed loader
    without hitting unrelated bugs). `bootstrap test` on files that DO need
    codegen (`examples/tests.mo`, `pattern_matching.mo`, `iteration.mo`)
    hits pre-existing, unrelated `llc` codegen failures (void-typed
    values in generated LLVM IR) — confirmed via `git stash` that these
    fail identically without this fix, so they're not a regression, just
    a separate, already-broken area this pass didn't touch. `cargo test`
    (627/627) and `check init std lang examples` (2 errors/7 warnings)
    both unchanged, confirming no effect on the unrelated,
    already-correct `check` traversal.
16. **New "unused def" warning — Rust-native checker only, `monad-rs
    check`.** `module_warnings`/`collect_referenced_names`
    (`core/src/term/module.rs`) already existed for unused-*import*
    detection, per-file. Added a sibling, `unused_def_warnings`, but it
    genuinely needs the WHOLE loaded corpus (`LoadedModules`), not one
    file: a def used only by a sibling file would be a false "unused"
    positive checked one file at a time. Wired into `check_files`
    (`core/src/lib.rs`) as a pass run once after the per-file loop
    finishes (once `master_loaded` holds every checked file), matched
    back onto each warning's own originating `FileCheckResult` via a
    `ModulePath -> PathBuf` map built during that same loop (`Diagnostic`/
    `SourceRange` never carry a real file path at parse time in this
    codebase — that's threaded explicitly by callers — so a `ModulePath`,
    via `Module::path`, is the only reliable key to match a warning back
    to its file).
    Deliberately **not** wired into the test runner
    (`run_tests`/`run_tests_for_files`): that path loads each file
    independently, in parallel, from a shared read-only starting
    snapshot (`base_loaded.clone()`, O(1) thanks to item 13's Arc-wrap),
    never merging back into one final whole-corpus `LoadedModules` the
    way `check_files`'s sequential loop does — there is no single
    "everything loaded" structure to run a whole-program pass against
    without a real architectural change, out of scope here.
    Exemptions: `pub` (may be used by another mote, invisible to this
    checker), `#[test]`-attributed (called by the harness, not
    referenced by name), named `main` (the entry point). A third
    exemption was added after direct measurement, not anticipated up
    front: a synthesized typeclass-instance dictionary def
    (`instance-{class}-{args}`, `core/src/term.rs`'s `instance()`
    constructor) is found by the type system's own dictionary-resolution
    machinery (dispatched by TYPE, at typecheck/eval time), never
    through a named `Term::Var` reference — exempted the same way `main`
    is, a root the ordinary reachability model doesn't apply to.
    Matching a def's own name against the whole-corpus reference set
    deliberately does NOT reuse `referenced_contains_name`'s own
    broadest fallback (any referenced path anywhere ending in this
    identifier) — confirmed empirically that doing so suppressed nearly
    every real warning across this project's own ~100-file corpus (that
    fallback is calibrated for one file's small reference set, not
    a multi-hundred-file union). Only the two precise checks survive:
    exact full-path match, and bare-last-segment match (a same-module or
    post-`open` reference resolved to just the local name).
    **Known, accepted precision gap, found by direct testing, not
    theoretical**: a def that shares its bare name with something else
    also in scope (e.g. `lang/src/module.mo`'s own `file_exists`, which
    wraps an `open`ed `IO.file_exists` of the identical bare name) can
    read as unused even when genuinely called, if the checker's own
    elaboration resolves same-file bare references to a DIFFERENT
    same-named target than the literal local def — narrow (one
    confirmed instance in the real corpus), not chased further this
    pass; flagged here rather than silently shipped.
    **Verified** via a 5-case fixture (`pub` def, def used only by a
    sibling file, genuinely-unused private def, `#[test]` def, `main`) —
    all 5 behaved correctly, both as a manual end-to-end `monad-rs
    check` run (`examples/unused_def_fixture_a.mo`/`_b.mo`, not checked
    in) and as a new permanent unit test
    (`term::module::test::test_unused_def_warnings_five_cases`,
    `core/src/term/module/test.rs`). On the real corpus (`check init std
    lang examples`): 52 warnings, spot-checked several by hand (real
    dead utility functions, unused derive-generated constructors) after
    the instance-dictionary exemption cut an initial ~80 down by ~28
    false positives. `cargo test` 628/628 (627 + the new test); `check
    init std lang examples`'s 2 errors/7 pre-existing import warnings
    unchanged, confirming this is purely additive.
    **Self-hosted checker's own "unused def" warning is a separate,
    larger, not-yet-done piece of this same request** — no warning/
    severity concept exists in the self-hosted pipeline at all today,
    and `check`'s self-hosted command has no whole-corpus flat `Def`
    list the way `compile`/`test` already do via `load_file_modules` —
    see the module-loading investigation (this same session) for the
    concrete design (generalize `lang/src/codegen/emit.mo`'s existing
    `reachable_defs_from`/`collect_referenced_names` reachability pass,
    already rooted at `main`, to also root at every `pub`/`#[test]` def;
    "unused" is the complement of the final `visited` set).
17. **`Value::Con`/`Value::PartialNtv` args Arc-wrap — closes the last big
    deep-clone gap item 13 flagged but ruled out for the wrong benchmark.**
    Full writeup: `plans/implementations/value-con-arc-wrap-optimization.md`.
    Item 13's callgrind profile found `Value::clone()` on `Con`/
    `PartialNtv` "real but negligible" — but that was measured against
    `test_typecheck_lang_main`, dominated by the (then-unfixed)
    `LoadedModules` clone cost, not a workload that exercises list/ADT
    churn. A parallel session's own callgrind profile on a genuinely
    List/`Con`-heavy workload (`count_eq`/`build_list`, the self-hosted
    checker's own `Map`/`Scope`/`Option`/`List` shape) found the opposite:
    ~90% of eval cost (`Value::to_vec` clone ~32%, drop_glue ~16.5%,
    allocator churn ~42%) was exactly this. Root cause: `Value::Con { tag,
    args: Vec<Value> }` derived `Clone` structurally, so cloning one
    deep-copied its entire nested-`Con` structure (a list's `cons head
    tail`, `tail` itself a `Con`) — every ordinary variable read
    (`Env::get(...).cloned()`, `GlobalCache::get`'s `v.clone()`, both
    `core_eval.rs`) paid a full O(current-size) clone, reproducing
    `SharedStr`'s (item 12) exact O(N²) shape for arbitrary structured
    values, never just strings. **Fix**: `args: Vec<Value> ->
    Arc<Vec<Value>>` on both variants (not the whole `Value` enum, so
    every existing match arm stays unchanged) — same idiom as `SharedStr`/
    `Module`'s Arc-wrap. Mutating sites (`core_eval.rs`'s incremental
    application and `Match`-arm field-binding; `eval/meta_reflect.rs`'s
    macro-reflection reify helpers) use `Arc::make_mut` (copy-on-write).
    `eval/meta_reflect.rs`'s ~19 candidate sites collapsed to ~6 real
    edits in practice — nearly all of them already funneled through one
    shared `pop_front` helper, so changing its signature
    (`&mut Vec<Value> -> &mut Arc<Vec<Value>>`) fixed every call site with
    zero call-site changes. Added
    `test_partial_con_application_from_shared_value_does_not_leak_across_branches`
    (`core_eval.rs`) for the COW correctness hazard (two aliases of one
    memoized constructor global, via `GlobalCache`, each applying a
    different extra argument — neither may leak into the other or into
    the cache's own stored copy). **Measured** (same `count_eq`/
    `build_list` shape as `core_eval_bench.rs`'s `class_dispatch`, `git
    stash` before/after): n=500/2000/8000 went from 16ms/246ms/4076ms
    (quadratic — 4x n gives ~16x time) to 0ms/2ms/8ms (linear — 4x n gives
    ~4x time) — a 123x-509x speedup that GROWS with N, the actual
    signature of an algorithmic fix, not a constant-factor one. Added a
    permanent `class_dispatch_large` criterion benchmark
    (`core/benches/core_eval_bench.rs`, 5x `CLASS_DISPATCH`'s size) as
    standing infrastructure. Verified: `cargo test`/`cargo test --release`
    all green (676+ core tests + 6 integration suites); `cargo clippy --`
    exits 0, no new warnings; `cargo run --release -- test init std lang
    examples` 1287/1287 unchanged; `cargo run --release -- check init std
    lang examples` byte-identical (101 files, 2 errors, 62 warnings,
    confirmed via direct `git stash` comparison); `cargo run --release --
    test slow_tests` — same 29 pre-existing `test_typecheck_*` failures
    (a known, unrelated self-hosted-checker gap — see this file's
    Troubleshooting section on `Map`/`BOrd` dispatch inside
    `load_module_with_dependencies`), not a new regression. **Not yet
    re-measured**: the `check_deps=true` 28GB-RSS repro from
    `check-deps-memory-blowup.md` — not reachable from this branch (that
    flag lives on `checker/fix-coverage`, not merged here). This fix
    targets that investigation's leading hypothesis #1 directly; re-run
    that repro once `check_deps` is available here to confirm how much of
    it this closes.
18. **The self-hosted compiler's global name table is not module-scoped --
    duplicate top-level names across different `lang/*.mo` files silently
    collide**, confirmed both structurally and via a grep sweep
    (2026-09-01). The general problem is still open; the two concrete
    instances named below are now FIXED (2026-09-01, Phase 1 of
    `plans/bootstrapping/self-hosted-dedup-and-pipeline-cleanup.md`).
    Concrete confirmed instance, **FIXED**: `lang/src/types.mo` and
    `lang/src/module.mo` EACH declared their own, DIFFERENT `struct
    LoadedModules` (`{modules: List Module}` vs. `{main_module:
    ModuleInfo, all_modules: List ModuleInfo}`). `lang/src/types.mo`'s is now
    `ModuleRegistry`; `lang/src/module.mo` keeps `LoadedModules` (it is the
    one the real `load_file_modules` -> `elaborate_loaded_modules` ->
    codegen pipeline uses). **The collision was load-bearing, not
    harmless**: nine test files (`slow_tests/codegen_*`,
    `parser_return_prefix_identifier_tests.mo`,
    `lang/src/codegen/test/test_closure_capture_e2e.mo`) imported
    `LoadedModules` from `lang.types` while using it as
    `load_file_modules`' return type -- i.e. they only type-checked
    because the collision silently resolved their import to the OTHER
    file's struct. Renaming surfaced all nine; their imports were
    retargeted to `lang.module`. Second instance, **FIXED**:
    `string_find_last`/`string_find_last_loop` existed in both
    `lang/src/parser.mo` and `lang/src/codegen/emit.mo`; the `parser.mo` copy had
    ZERO callers and a real bug (passing an end index where
    `String.slice`'s third argument is a LENGTH), so whichever won
    registration order decided whether a correct or broken implementation
    was live. The dead, buggy copy was deleted; `emit.mo`'s correct,
    called version remains. A broader sweep (`grep -oE '^def [A-Za-z_][A-Za-z0-9_.]*'`
    across `lang/*.mo`, deduped) found **~862 other duplicated bare
    top-level def names** in the corpus (`sentinel` x6, `show_identifier`
    x4, `id_str`/`name_ref_to_string`/`module_path_last`/
    `string_find_last` x3 each, ...) -- this is a broad, pre-existing
    pattern, not an isolated case. First surfaced as a real mechanism
    while investigating the `join_identifiers`/`join_id_rest` self-compile
    hang (2026-08-31): `lang/src/types.mo`'s own dot-joining
    `join_identifiers` and `lang/src/codegen/emit.mo`'s `"__"`-joining
    `join_identifiers` collide the same way, and only ONE (whichever the
    global registration order happens to favor) actually gets compiled
    into a self-compiled binary, discoverable today only by grepping the
    output `.ll` by hand. **Not fixed this session** -- flagged here per
    direct request, for a future dedicated cleanup pass. A real fix needs
    either qualifying the global name table by module path (the
    principled fix, likely touches `lang/src/module.mo`'s scope-building and
    every name-resolution call site that currently assumes bare-name
    uniqueness) or renaming every colliding pair (mechanical but large,
    ~862+ names) -- either way, audit first which collisions are
    load-bearing accidents (two defs that happen to do the same thing, so
    the collision is harmless) vs. genuine bugs (two UNRELATED defs
    sharing a name, where the wrong one winning is a live correctness
    risk) before touching anything, since a blind rename sweep risks
    papering over real bugs by "fixing" the symptom (the collision) while
    leaving whichever def was silently losing the fight to become
    unreachable dead code instead of properly wired in.
19. **Item 18's audit, done -- every DIVERGENT collision found and fixed
    (2026-09-02).** A corpus-wide scan for the specific shape item 18
    warns about (a file that both `use`s a name AND declares its own)
    found 8 sites, and the split item 18 predicted turned out to be
    exactly the right one to make:
    - **Divergent (the two definitions produce DIFFERENT results, so
      which one won was a live correctness hazard) -- all four fixed:**
      `LoadedModules` (`lang/src/types.mo` `{modules}` vs `lang/src/module.mo`
      `{main_module, all_modules}`); `join_identifiers` (types joins with
      `.`, emit with `__` -- this one decided emitted LLVM SYMBOL NAMES,
      and is the pair from the 2026-08-31 self-compile hang; emit's is now
      `mangle_identifiers`); `show_identifier` (types returns text
      verbatim, emit strips `'` quotes, across 18 codegen call sites;
      emit's is now `symbol_identifier`); and `string_find_last` (the
      `lang/src/parser.mo` copy passed an END INDEX where `String.slice`'s
      third argument is a LENGTH -- it had zero callers, so it was
      deleted rather than repaired).
    - **Identical (harmless) -- deduped:** `show_identifier`/
      `show_operator` in `lang/src/parser.mo`, `list_reverse`/`list_rev_loop`
      in `lang/src/typecheck/infer.mo`, `ident_start` in
      `lang/src/parser/identifier.mo`.
    - **NOT deduped, deliberately:** `list_append`/`list_append_go`
      (`lang/src/module.mo` vs `lang/src/scope.mo`) LOOK like an obvious
      duplicate but are not interchangeable -- scope's declares an
      explicit `{A : Type}` binder, module's relies on implicit
      generalization, and the four call sites are on `merge_scope_data`'s
      measured hot path. Neither may fall back to prelude `List.append`
      either: both add the `ys`-empty short-circuit item 12 measured as
      load-bearing. This is the concrete example of item 18's own warning
      that a blind rename/dedup sweep can destroy a measured optimization.
    Item 18's ~862-name figure counts every duplicated bare name; the 8
    above are specifically the ones where a single file both imports and
    redefines, which is the subset where the hazard is live rather than
    theoretical. The general fix (module-scoping the name table) is still
    open.
20. **Deleting a def can silently truncate the self-hosted parse -- and
    `check` will not tell you (2026-09-02).** Removing a def while
    leaving its `#[partial]` attribute behind produces `#[partial]` ->
    `///` doc comment -> `#[partial]` -> `def`, and `decls_parser`
    (`lang/src/parser.mo`) stops dead there: a real instance dropped 13,719
    bytes of `lang/src/toml.mo` -- roughly half the file -- while
    `monad-rs check` reported **0 errors and 0 warnings**, because the
    Rust-native checker parses independently of the self-hosted parser.
    One attribute followed by a doc comment still parses; only TWO
    straddling a doc comment truncate. Only
    `slow_tests/src/parser_file_tests.mo`'s `file_fully_parses` tests catch
    this class. **After any def deletion, grep the touched files for an
    attribute immediately followed by `///`** (`#\[[a-z_]+\]\n(?=///)`)
    and run `parser_file_tests.mo`. This is the same "attribute
    artifacts" hazard the Rebase Resolution Workflow section already
    warns about, but the consequence (silent parse truncation, invisible
    to `check`) was not previously documented.
21. **`init/` and parts of `std/` are EMBEDDED IN THE BINARY**
    (`include_str!`, `core/src/term/module.rs`, `embed-stdlib` feature):
    `prelude`, `id`, `io`, `number`, `math`, `string`, `list`, `init/
    lib.mo`, plus `std/src/path.mo`, `std/src/io.mo`, `std/src/process.mo`,
    `std/src/lib.mo`. Edits to any of those are INVISIBLE until
    `cargo build --release`, and the failure mode is a silent
    `unbound variable` at every call site -- not a parse error, and not
    an error naming the file you just edited. Other `std/` files
    (`std/src/list.mo`, `std/src/base.mo`, ...) load from disk normally and need
    no rebuild. Also note `monad-rs check <file>` SKIPS `init/` entirely
    ("0 file(s) checked"), so it cannot be used to validate an `init/`
    edit -- run a `#[test]` instead.

22. **`MatchCase` is a BINDING FORM -- a fourth one, easy to miss
    (2026-09-02).** `Term.lam`/`forall`/`pi` are the obvious de Bruijn
    binders, but a match arm's own pattern bindings (`MatchCase.mc`'s
    `args`) bind over its BODY too: the body sits `List.length args`
    binders deeper than the enclosing `Literal.match_` node. All three
    walkers in `lang/src/typecheck/subst.mo` (`term_shift_go`,
    `term_permute_go`, `term_subst_go`) have always handled this
    (`cutoff + List.length args`), and `lang/src/typecheck/traverse.mo`'s
    depth-aware `match_case_map_children_at_depth` now does too -- but
    its depth-AGNOSTIC sibling `match_case_map_children` deliberately
    does not (a walk that tracks no depth has nothing to adjust). Any
    NEW depth-tracking walk over `Term` must account for it. The
    standing guard is `subst.mo`'s own
    `test_match_case_binder_depth_shift`, which caught exactly this
    mistake during the traverse.mo consolidation; it asserts through the
    public `term_shift` entry point, so it keeps working regardless of
    how the per-node helpers are factored.
23. **A `.mo` file can depend on another module without importing it,
    and only breaks when the module graph changes (2026-09-02).**
    `lang/src/typecheck/infer.mo` called `subst.mo`'s `term_permute` with no
    `use lang.typecheck.subst` anywhere -- it resolved only because
    `macro_expand.mo` happened to pull `subst` in via `macro_apply`, and
    the whole-program name table made it visible. Moving an unrelated
    function into a new module changed the load graph and broke 5 files
    at once with `unbound variable term_permute`. This is the same
    non-module-scoped-name-table root cause as item 18, seen from the
    other side: item 18 is about two definitions colliding, this is
    about one definition being found without being asked for. When
    extracting or moving a module, expect latent implicit dependencies
    to surface; the fix is always an explicit `use`, which is strictly
    more robust than the accident it replaces.

24. **The self-hosted pipeline's redundant work is STRUCTURAL, not
    algorithmic -- look for the same expensive pass running twice
    before optimizing any single pass's internals (2026-09-03).**
    `bootstrap compile examples/hello.mo --verbose` prints a full
    `Bench.report` phase breakdown; use it before guessing. It showed
    `elaborate_loaded_modules` at 5255ms of a 7747ms total (68%), with
    `check_module_with_scope` -- the phase whose name sounds expensive
    -- at 5ms. Two structural redundancies found and fixed there:
    - **The post-expansion scope rebuild** (`elaborate_loaded_modules_
      cached`, `lang/src/module.mo`): the function built a `Scope`, ran
      `expand_decls_graph`, then UNCONDITIONALLY rebuilt the `Scope`
      from the result. Since only `std/src/derive.mo` genuinely invokes
      `reflect_type_info!` in this corpus, the expansion is a no-op for
      almost every file and the rebuilt scope was identical to the one
      discarded -- a second full `build_scope_from_decls` over the whole
      dependency graph, measured at **1523ms of the 5255ms**.
      `expand_decls_graph` now returns a `GraphExpansion` with a
      `changed` flag; the caller reuses the existing scope when nothing
      was rewritten. `elaborate_loaded_modules` 5255ms -> 3847ms (-27%),
      total compile 7747ms -> 6510ms (-16%). Confirmed by an
      INTERLEAVED A/B (before, after, before, after, ... in one loop):
      5029/5109/5131ms -> 3594/3579/3626ms, a stable -29%. Interleaving
      matters on this machine -- parallel sessions running `cargo
      build`/`monad-rs test` push load average past 9 and make
      single-shot readings swing 5394-15023ms for the SAME binary.
      Measure A and B back-to-back in one loop rather than trusting two
      readings taken minutes apart, and check `uptime`/`ps` before
      believing any perf delta. Note the subtlety in
      computing `changed`: a `macro_call_d` whose name is NOT in the
      decl-gen registry passes through unchanged and must NOT count as
      an expansion (`has_decl_gen_expansion` checks registry membership,
      not just "is a macro call"), matching `decl_gen_subst_one`'s own
      "an unresolved macro name is not an error" rule.
    - **The uncached test loop** (`cli/src/main.mo`): `run_check_loop` had
      threaded a `ModuleInfoCache` since `b0c96a7`, but `run_test_loop`
      called the uncached `elaborate_loaded_modules`, so every file in
      one `monad test a.mo b.mo c.mo` re-read and re-parsed its whole
      closure. Threading the same cache: 20.99s -> 18.89s (-10%) on
      three load-dominated files, 12 of 24 dependency loads cached.
      `run_test_loop_codegen` CARRIES the cache without consulting it --
      that path loads nothing itself (that is what `preloaded` is for),
      it only hands the cache to the next file.
    **Proving a redundancy elimination is safe**: for anything feeding
    codegen, diff the generated LLVM IR rather than relying on tests --
    `compile examples/hello.mo` before and after must be byte-identical
    (it was, for the scope-rebuild change). Tests alone would not have
    distinguished "the rebuild was redundant" from "the rebuild was
    load-bearing but nothing covers it".
25. **CORRECTED (2026-09-04): the "`Bench.report` around a `let`
    measures nothing because the language is lazy" diagnosis was
    WRONG.** The original entry recorded that sub-timing
    `elaborate_class`'s three internal steps printed no sub-timings at
    all and left the enclosing total unchanged (1949ms vs 1941ms), and
    concluded a `let`-bound value is not forced where it is bound.
    Laziness is not the explanation: the evaluator is strict
    call-by-value. `core/src/core_eval.rs`'s `App` arm reduces both
    sides fully before applying ("Strict call-by-value: both sides are
    fully reduced to a Value before applying"), and `let x := v in b`
    desugars to `App(Lam b, v)` (`core/src/term.rs`), so a `let`-bound
    step IS forced exactly where it is bound.
    Demonstrated directly: `elaborate_loaded_modules_cached`
    (`lang/src/module.mo`) is now sub-timed by threading a `bench_step`
    timestamp through its pure `let` chain, and every span reports a
    real number that sums correctly (see item 27). Whatever went wrong
    in the `elaborate_class` attempt -- an untaken branch, a span around
    the wrong expression -- it was not thunking, and looking for a
    laziness fix there will waste time.
    The useful rule that survives is the ARITHMETIC one, which catches
    a bad span whatever its cause: sub-times must add up to the
    enclosing total that already prints. If they do not, or a span
    reports 0, the span is wrong -- fix it rather than reasoning about
    why.
26. **`HashMap`'s bucket chains tested key equality as `!lt && !gt` --
    two comparator calls per chain step, and for `ModulePath` that meant
    FOUR string constructions per step (2026-09-03).**
    `build_scope_from_decls` was the single largest self-hosted cost:
    1482ms of `elaborate_class`'s 1857ms (80%), itself 89% of codegen.
    The name misleads -- elaboration was 7% of that span; the cost was
    building the scope's `HashMap`s. With ~349 defs over a FIXED 16
    buckets (`std/src/map.mo`'s `Buckets16`), chains run ~22 deep, and
    `bucket_insert`/`bucket_lookup` tested equality as
    `!lt(k1,k2) && !gt(k1,k2)`. `lang/src/scope.mo`'s `modpath_lt`/
    `modpath_gt` BOTH call `show_module_path`, which rebuilds the path
    via `List.map` + `List.intercalate` -- so each chain step built four
    strings. **The chain is not sorted** (insert appends at the end and
    only replaces an existing equal key), so `lt`/`gt` were never
    serving as an ordering at all, only as an equality test.
    Fixed by adding `bucket_insert_eq`/`bucket_lookup_eq` taking a
    single `eq` predicate (additive -- the `lt`/`gt` versions stay for
    the generic `Map` instance) and pointing `modpath_map_*` at
    `modpath_str_eq` (`String.beq` of the two rendered paths: identical
    semantics, one render per side instead of two). `emit.mo`'s
    `str_map_*` got the same treatment with `String.beq` directly.
    Measured, interleaved A/B: `elaborate_class` 1767/1766/1767ms ->
    1037/1033/1033ms (**-41.5%**); `filter_reachable` 100ms -> 72ms
    (-29%); total `compile examples/hello.mo` 5976ms -> 4378ms (-27%).
    LLVM IR byte-identical, corpus 1402/1402.
    **Two substitutions that look right and are NOT** -- both found by
    probes that broke the build, so do not "simplify" to either:
    - `modpath_eq` (the existing one) delegates to `Similar.similar`,
      which does NOT agree with string comparison on aliases: swapping
      it in fails with `unknown variable 'println'`.
    - A structural segment-wise comparator is not order-equivalent to
      string comparison either (`.` sorts differently than segment
      boundaries) -- it broke typechecking outright.
    Note what was NOT done: widening past 16 buckets. Item 6 measured
    bucket-dispatch restructuring as a consistent 10-30% REGRESSION in
    this interpreter. The win here is in the per-step comparator, not
    the bucket count -- a reminder to attack what each step COSTS before
    attacking how many steps there are.

27. **`elaborate_loaded_modules` is dominated by READING AND PARSING,
    not by any of the whole-graph rewrite passes (2026-09-04).** Item 24
    established the phase total but not its shape. `lang/src/module.mo`'s
    `elaborate_loaded_modules_cached` now sub-times every step
    (`bench_step`, threaded through its pure `let` chain, gated on
    `verbose`). `check examples/hello.mo --verbose`, 12 modules, 0 cache
    hits:
      load_file_modules (read+parse)        2519ms   67%
      build_scope_from_decls                 907ms   24%
      names_of_decls                         190ms    5%
      resolve_infix_decls                     87ms  2.3%
      promote_instance_defs                   19ms  0.5%
      add_constraint_dict_params_decls         3ms
      expand_decls_graph                       4ms
      flatten_module_decls / target re-run /
        elaborate_def_typs                     3ms
      total                                 3732ms
    (Sums to 3732ms against item 24's ~3847ms for the same phase, which
    is the arithmetic check item 25 now insists on.)
    **Two span boundaries were corrected after review**, and the lesson
    generalises: the arithmetic check CANNOT catch a mislabelled
    boundary, because the sub-times still sum to the total either way.
    `names_of_decls`'s span had begun before the conditional
    post-expansion scope rebuild -- which is a SECOND whole-graph
    `build_scope_from_decls` (~1500ms) whenever `expansion.changed` --
    and `resolve_infix_decls`'s had begun before `collect_infixes`. Both
    now have their own spans. Re-measured with the corrected boundaries,
    the numbers above stand for this workload: the rebuild is 0ms
    (`examples/hello.mo` triggers no expansion, as only `std/src/derive.mo`
    invokes `reflect_type_info!`) and `collect_infixes` is 1ms. On a file
    that DOES expand, the old grouping would have silently reported
    ~1500ms of scope building as `names_of_decls`.
    Consequences for where to spend effort:
    - **Two thirds of the phase is the self-hosted parser running
      interpreted over prelude/init/std.** Nothing in the whole-graph
      rewrite family can touch it. `ModuleInfoCache` already removes
      this ACROSS files in one run; a single-file `check`/`compile`
      still pays it in full (0 hits, 12 misses here).
    - `resolve_infix_decls` is 87ms, so the `lookup_infix`
      re-rendering fix (the item-26-shaped cost-per-step win available
      there) is capped at well under that. Measured before it was
      built, not after -- this is exactly what item 24's "look for
      structure before optimizing internals" rule is for.
    - `names_of_decls` at 190ms is the larger of the two self-hosted
      algorithmic smells, and it IS O(n^2): it folds with `union_ids`
      whose `a` side is one element and `b` side the accumulated tail,
      so building the list costs O(n^2) `String.beq` with n roughly
      500-800 after promotion. Its only consumer is `free_vars` for the
      target file's own defs (2, for `hello.mo`).
    - `build_scope_from_decls` at 907ms remains the biggest single
      rewrite-family cost, and item 26 already attacked its comparator.
      Note it runs a SECOND time per `compile`, in
      `lang/src/codegen/emit.mo`, because `ElaboratedModules.
      elaborated_decls` has zero readers -- see that field.

28. **The parser's `take_while` allocated a one-character string PER
    INPUT CHARACTER; scanning a byte index instead cut the parse phase
    30% (2026-09-04).** Item 27 put `load_file_modules` (read+parse) at
    67% of `elaborate_loaded_modules` but not what shape that cost had.
    `take_while_loop` (`lang/src/parser/combinators.mo`) did, per character:
    `is_empty`, `utf8_char_width` (a `String.get` plus up to four
    `U8.lt`), `String.slice input 0 width` -- **an allocation** -- the
    predicate call on that fresh one-character string, and a
    `String.drop` to build the tail it recursed on. Two allocations per
    character. The predicates compounded it: `is_space` up to four
    `String.beq`, `is_digit` a ten-way chain, `is_ident_char` reaching
    `is_alphanumeric` -> `is_alpha` -> four helpers.
    **Fix**: `take_while_byte` scans a byte index with `String.get`
    (already a native returning `U8`) and slices exactly twice, at the
    token boundary -- two allocations per TOKEN, with numeric `U8.lt`/
    `U8.beq` range checks instead of string equality. **No new natives**
    (a deliberate constraint here); `String.get`/`slice`/`drop` and the
    `U8` ops all already existed. The `String`-taking `take_while` and
    every original predicate are KEPT, not replaced -- `lang/src/json.mo`,
    `lang/src/toml.mo` and the string-literal scanner have predicates of
    their own.
    Byte-wise scanning is correct for these classes precisely because
    they are all ASCII: a UTF-8 lead byte (>= 0xC0) and a continuation
    byte (0x80-0xBF) both fail every one of them, so a scan stops at a
    character boundary rather than splitting one. **A predicate that
    must ACCEPT non-ASCII cannot use this path** -- that is why the
    string-literal scanner was left alone.
    **Measured** with `bench/src/parser_take_while.mo`, added as standing
    infrastructure. It runs both scanners in ONE process (so machine
    load cannot distort the comparison -- this box runs a CI runner and
    load ranged 1.4-17.8 the day this landed) and asserts the two
    consume byte-identical input, so a byte scan that stopped early
    would fail the test rather than look faster:
      take_while is_space      long   122ms -> BYTE  79ms   -35%
      take_while is_ident_char long   250ms -> BYTE 161ms   -36%
      take_while is_space      short  141ms -> BYTE  94ms   -33%
      take_while is_ident_char short  263ms -> BYTE 176ms   -33%
    End to end, converting 5 call sites (`whitespace.mo` x4,
    `identifier.mo` x1), interleaved A/B on `check examples/hello.mo`:
    load+parse **1715/1694/1701ms -> 1205/1201/1178ms, -30%**.
    **That -30% came from 5 sites, but 9 more were still on the old path
    and this entry originally read as though the conversion were
    complete.** Review caught them: `take_while is_space` in
    `expr_climb_rest_ws`/`expr_climb_op_rhs_ws` and three sites in the
    type-expression climber -- i.e. once per operator-precedence step and
    per type atom, hotter than several of the sites that HAD been
    converted -- plus `take_while is_ident_char` in the type-constraint
    parser. All now converted (17 sites total). When recording a
    conversion, count the call sites that remain, not the ones changed. Adding
    `number.mo`'s 3 sites afterwards moved it no further than noise --
    digits are simply rarer in source than whitespace and identifiers --
    but was kept as consistent and harmless.
    Whole-invocation `check` only moved -3.5% (12.6s -> 12.1s): most of
    that wall time is the RUST host loading and type-checking
    `cli/src/main.mo` itself before the self-hosted compiler runs at all.
    Do not expect parse-phase wins to show up 1:1 in the total.


29. **`Char` is a stub: do not reach for it, and never scan with it
    (2026-09-04).** Raised as "why not use `Char` instead of `U8`" during
    item 28's work. Four independent reasons it does not work, found by
    checking rather than assuming:
    - **`String.get_char` is O(n) per call.** `core/src/core_native.rs`
      does `s.chars().collect::<Vec<char>>()` on every call and then
      indexes it, so a per-character loop built on it is quadratic in
      time AND allocation. `lang/src/parser/combinators.mo`'s
      `utf8_char_width` already documents this and deliberately uses
      `String.get` (an O(1) byte read) instead.
    - **Its `i` is a CHARACTER index, not a byte offset**, so it cannot
      drive byte-offset advancement even ignoring cost.
    - **`Char` has no operations at all** -- zero `Char.*` functions and
      no `BEq`/ordering instance anywhere in `init/`, `std/` or `lang/`.
      Nothing consumes a `Char` except two tests in
      `lang/src/parser/tests/test_string_get.mo`.
    - **The declared type contradicts the runtime representation.**
      `init/src/prelude.mo` declares `type Char { of_bytes (List U8) }`, but
      the native produces `Value::Lit(IrLit::Char(c))` -- a scalar
      literal, not a constructor application -- so destructuring
      `Char.of_bytes bs` hits `NotAConstructor` and a comparison cannot
      even be hand-written in `.mo`.
    Fixing the last two needs new natives, or changing `Char`'s runtime
    representation to a real `of_bytes (List U8)` (a heap list per
    character, far worse than what exists).
    **Worse, two of the three are not wired at all**: `string_to_chars`
    and `string_from_chars` are declared in `init/src/string.mo` but absent
    from `exec_native`'s dispatch table, so calling either fails at
    runtime -- exactly the hazard `validate_no_unwired_natives`
    (`lang/src/codegen/emit.mo`) exists to catch, which never fires only
    because nothing reaches them. `String.from_chars`'s parameter type
    `Chars` is not a type that exists anywhere in the corpus either.
    **There is also no correctness gap for `Char` to close in the
    parser.** The scanned classes are ASCII by the grammar's own
    definition -- `is_alpha_lower` is a-m, `is_alpha_lower2` n-z,
    `is_alpha_upper` A-M, `is_alpha_upper2` N-Z, each enumerated one
    letter at a time -- so item 28's byte range checks are exactly
    equivalent, and Monad identifiers cannot contain non-ASCII in the
    first place. Byte scanning stops precisely at character boundaries
    because a UTF-8 lead byte (>= 0xC0) and continuation bytes
    (0x80-0xBF) fail every ASCII predicate. The one scanner that must
    pass over arbitrary UTF-8, the string-literal scanner, is
    deliberately left on the `utf8_char_width` path.
    Left in place rather than removed (two tests use `get_char`, and it
    is declared API), with warning doc comments on all three natives
    pointing here.
    **Update (2026-09-13).** `'c'` char LITERALS now parse, type-check and
    compile self-hosted (`lang/parser/string.mo`'s `char_literal`), and
    `Literal.char` carries a real `Char` rather than the source text. None
    of that changes the four reasons above: the type still has zero
    operations, so a literal is something you can write, type and pass, and
    still not inspect. Do not read "char literals landed" as "`Char` is
    usable now".

30. **Record a source span at the parser's choke points, never at the
    construction sites (2026-09-05).** The parse stage's fourth and last
    commit gave `ParseTerm`/`ParseDecl` real positions. The obvious
    reading of "replace `pt_` with `pt_at` at each construction site" is
    wrong, and checking why is what made this cheap:
    - **Most construction sites cannot see their own start.** Of the 57
      `pt_*` and 20 `pd_*` sites in `lang/src/parser.mo`, the great majority
      sit in continuation helpers (`type_dep_body`, `open_build`,
      `struct_lit_fields_end`, ...) whose own `input` parameter is
      somewhere in the MIDDLE of the construct being built. Stamping
      `pt_at input rem` there compiles and produces a confidently WRONG
      position -- the worst possible outcome for a debugger, and one no
      type error would ever catch.
    - **Two functions see every construct.** `atom_term` is handed the
      exact start of every atom (all eleven `atom_parsers`, plus
      `lambda_parser` and `paren_expr`) and `decl_parser` the exact start
      of every declaration. One stamp in each -- via a
      `ParseResult`-level `term_at`/`decl_at` -- located the whole
      grammar. `scoped_open_inner_decl` is the single declaration that
      bypasses `decl_parser` and stamps its own.
    - **Compounds read their start back off their left operand.**
      Application chains and infix climbs are built bottom-up, so the
      text where they began is long consumed by the time the combined
      term exists -- but the left operand still carries its own span.
      `pt_from left rem kind` (`lang/src/types.mo`) is why locating a whole
      expression needed no threading, which is the same threading the
      de Bruijn `ctx` removal had just deleted. It yields an unknown span
      when the operand has none: a span from an unknown start to a real
      end is not a position.
    - **An unknown span is a correct answer, not a gap.** A `pt_hole`
      standing in for an omitted annotation, the cons cells
      `build_list_literal` synthesises, the `pt_pi` chain
      `build_param_pi_chain` folds out of a parameter list -- none were
      written anywhere. `parse_span_is_unknown` distinguishes them from
      a real position.
    **`decls_parser_with_locs` stopped being a parser.** It was a
    parallel traversal (`decls_skip_with_locs`/`decls_try_with_locs`)
    threading the whole file alongside the shrinking input to re-derive
    each declaration's position; it is now a projection over the span
    `decl_parser` already recorded, and the two can no longer disagree.
    Same arithmetic (`location_of_remaining_len`, factored out of
    `location_of_remaining`), 44 fewer lines, one traversal.
    **Cost, measured, as promised: +0.25%.** Interleaved A/B, four paired
    rounds, load 1.2: parse phase 1116.5ms -> 1119.25ms. Under the noise
    floor in magnitude, but B was slower in 4/4 paired rounds, so the
    sign is real and the honest number is "about a quarter of a percent",
    not "free". Set against item 28's -30% on the same phase.
    **A byte-identical IR oracle is narrower than it looks.** This one
    covered every representational change in the parse stage and stayed
    identical throughout -- including across a commit that silently
    dropped a de Bruijn binder. `examples/hello.mo` contains no dependent
    arrow, so the one construct that regressed was never compiled. An IR
    diff is strong evidence of a bug; IR equality is only evidence about
    the constructs the compiled file actually contains.
    **Equivalence oracle: LLVM IR for `compile examples/hello.mo`
    byte-identical** to the pre-parse-stage baseline, as it was after the
    two commits before this. Spans are pure addition; any IR diff would
    have been a bug. Tests 251/251 parser (8 new span assertions,
    each checking the exact substring a construct claims via `span_text`),
    1420/1420 overall, corpus 113 files / 0 errors.


31. **A `ctx`-threading removal has to be read call site by call site
    (2026-09-06).** Deleting the parser's de Bruijn `ctx` moved 371 call
    arguments. All but one were mechanical. The exception:
    `type_dep_arrow_tag` parsed its body under
    `type_expression (List.cons (Identifier.id name) ctx) ...` -- the one
    arrow in the grammar that BINDS -- so dropping the argument dropped
    the binder, and every use of `n` inside `(n : T) -> ... n ...`
    resolved to `sentinel`. `init/src/prelude.mo`'s `Eq.rec` is a live
    instance.
    **Every oracle stayed green.** The parser tests assert parse SUCCESS
    and the term parses fine with its binder unbound; `check` reports 0
    errors either way; the hello.mo IR stayed byte-identical because that
    file has no dependent arrow. A green suite is not evidence that a
    binder survived -- only reading the deleted sites is.
    The fix is `ParseTermKind.pi`'s `arg_name : Option Identifier`,
    mirroring the Rust reference's `Term::Pi { arg_name: Option<Name> }`
    (`core/src/term.rs`), whose `lower_core.rs` arm likewise pushes the
    name into scope only when it is `Some`. A nameless `pi` still does
    not extend `ctx`, matching `build_pi_chain`'s non-dependent fold --
    see item 27's note on the producer/consumer disagreement with
    `traverse.mo`.

32. **`do { }` is syntax, so `DoStmt` holds `ParseTerm` and desugars
    during lowering (2026-09-06).** There was briefly a `ParseDoStmt`
    (holding `ParseTerm`) lowered to a `DoStmt` (holding `Term`) and then
    handed to a separate `desugar_do`. Two types and two passes for a
    construct that does not survive lowering at all -- nothing downstream
    of the parser has ever seen a `DoStmt`.
    Merged to one type and one traversal in
    `lang/src/parser/lower_parse.mo`. The two jobs could not be cleanly
    separated anyway: each binder a statement introduces is in scope for
    the statements that FOLLOW it, so the desugaring's own `Term.lam`s
    ARE the context accumulation. Fusing them puts the `ctx` extension on
    the same line as the lambda that justifies it, instead of restating
    it in a parallel `do_stmt_extend_ctx` a reader has to keep in sync --
    which is exactly where the `expr_s` off-by-one used to live. The
    fused form also drops the extension in the case where no lambda is
    built (a trailing bare expression), which the parallel version
    over-extended harmlessly.

33. **Convert a single-constructor `type` to a `struct`, then stop
    matching it positionally (2026-09-06).** Item 1 of the style rules
    says every single-constructor type should be a `struct`. Eight
    `Parse*` types were converted; because a `struct` keeps both
    `X.mk a b` construction and `X.mk a b =>` patterns, the declaration
    change alone is call-site-free, and the `MatchTraversalMismatch`
    hazard did not fire (1436/1436).
    The conversion is only half the value. A positional pattern like
    `ParseInstance.mk name cls constraints args vis implicit_params defs`
    binds one variable per field and silently goes out of date: add a
    field and it still typechecks, then aborts at RUNTIME with `expected
    7 constructor fields, got 8`, with no location and no def name.
    Rewriting the eight lowering functions to read fields by name
    (`i.args`, `i.defs`) removes the arity coupling entirely and is
    shorter. Do both, not just the first.

34. **Resolving N source positions needs one pass, not N scans
    (2026-09-06).** `location_of_remaining_len` (`lang/src/parser/position.mo`)
    answers ONE position by scanning the consumed prefix. Per top-level
    declaration that is fine. Per TERM it is quadratic, and measurably so
    -- both paths in one process, same answers asserted equal:

    | input | bulk, one pass | per-offset |
    |---|---|---|
    | 100 lines / 100 offsets | 53 ms | 1122 ms |
    | 400 lines / 400 offsets | 213 ms | 22244 ms |

    4x the input costs the bulk path **4.0x** and the per-offset path
    **19.8x** (~4^2). Not a constant-factor difference -- a different
    exponent.
    Three things made the one-pass version simple, and each was a fact
    about this codebase rather than a general technique:
    - **The offsets arrive sorted for free.** `ParseSpan` stores REMAINING
      input length, so larger = earlier, and a pre-order left-to-right walk
      of the parse tree visits nodes in non-decreasing absolute offset. No
      sort is needed -- which matters, because `std/src/list.mo` has none.
    - **No index is possible anyway.** There is no `Array` in `std/` (no
      O(1) indexing) and no `Hashable I64`, so the obvious "binary-search a
      line-start table" is not available. Check what the standard library
      actually has before designing around it.
    - **Threading the running `Location` replaces the combine step.**
      `line_col_scan` needs `combine_line_col_scan` because its halves are
      independent. Resolving offsets does not: run the left half, then the
      right half FROM WHERE THE LEFT ENDED. The divide-and-conquer split is
      still required -- for recursion DEPTH, since the interpreter
      overflows around 1000-1500 frames and a linear walk is one frame per
      character -- but no monoid is.
    The oracle is the single-offset path it replaces: for any offset the
    two must agree exactly. They deliberately differ on an offset that is
    not a character boundary (bulk advances to the next one; single slices
    mid-character), which no real span ever is -- every scanner in the
    parser steps by `utf8_char_width` or by byte predicates that no UTF-8
    lead or continuation byte satisfies. A test that used a mid-character
    offset failed and was wrong, not the code.

35. **A `let` in front of an `if` is not a guard — this evaluator is
    strict (2026-09-07).** `lang/src/module.mo` had:

        let rebuilt_scope : Scope := { ... build_scope_from_decls ... };
        let did_change : Bool := expansion.changed;
        let scope2 := if did_change then rebuilt_scope else scope;

    which READS as conditional and is not. `let` binds eagerly, so the
    rebuild ran on every elaboration and the `if` only chose which
    already-computed scope to keep. Cost: **83.9s of a 232s self-hosted
    `check cli/src/main.mo`** -- 36% of the run -- duplicating a
    `build_scope_from_decls` that had just done the same work.
    `if` is the one form that does not evaluate the branch it does not
    take, so the fix is to move the call inside the branch.
    **The tell was in `--verbose` the whole time**: two adjacent phases
    costing almost exactly the same (81.9s `build_scope_from_decls`, 83.9s
    "post-expansion scope rebuild"), one of them named *rebuild*. Two
    phases with the same cost where one is supposed to be conditional is
    the signature. Look for it before reaching for a profiler.
    **But the annotated local was load-bearing for a second reason**, and
    removing it swapped one bug for another: a bare `{ ... }` inside the
    branch has no expected type to desugar against, survives to codegen as
    a `Literal.struct_lit`, and compiles to a void placeholder.
    `validate_no_undesugared_struct_lits` rejected it -- but only on a full
    self-compile, since the offending def was in `lang/src/module.mo`. The
    shape that satisfies both is NOT an annotated `let ... in` inside the
    branch -- the annotation does not reach the literal from there and the
    validator still rejects (verified: two full self-compiles, same error).
    What works is a small def whose DECLARED RETURN TYPE gives the literal
    an expected type, called from inside the branch: lazy because it is a
    call in a branch, desugared because the return type is the expected
    type. Same shape as `empty_loc_suffixes` (`llvm/src/ir.mo`), where
    a `let` annotation likewise failed to resolve a generic and a def's
    return annotation did.
    Corollary for perf work here: **attribute before fixing.** This looked
    like a regression from in-flight parser work; an interleaved A/B of
    branch vs `main` showed every phase identical within noise, including
    this one. The earlier 0ms reading that made it look new simply predated
    a rebase.

36. **`module cache: 0 hit(s), N miss(es)` on a single-file check is
    correct, not a bug (2026-09-07).** `collect_dep_module_infos`
    (`lang/src/module.mo`) skips anything already in `visited`, so within one
    file's dependency walk each module loads exactly once and the
    cross-file `ModuleInfoCache` has nothing to hit BY CONSTRUCTION. It
    exists for runs over many files, where the same dependency is reached
    from each: `check` over three examples reports 24 hits / 12 misses.
    Do not "fix" the zero.

37. **A profile taken on `examples/hello.mo` does not predict the
    self-compile, and item 26's extrapolation was wrong (2026-09-09).**
    Full self-compile 969811ms -> 281373ms (-71.0%), 16m01s -> 4m49s;
    `devenv tasks run monad:bootstrap-compile` 1176s of its 1200s
    timeout -> 320s.
    Item 26 measured `elaborate_class` at hello.mo scale and found
    `build_scope_from_decls` was 80% of it. Sub-timing the same phase at
    self-compile scale (4,020 defs vs 349) gave a completely different
    shape:
      build_scope_from_decls              69306ms   11%
      elaborate_module_decls_best_effort 165211ms   25%
      resolve_class_calls_decls          424646ms   64%  (45% of ALL)
    `resolve_class_calls_decls` had never been investigated, and at
    hello.mo scale it is 81ms of 2399ms (3.4%) -- invisible. It grew
    **5242x for an 11.5x larger input**. The rule: a candidate's SHARE at
    small scale says nothing about its share at large scale; what matters
    is how it SCALES. Profile the workload you actually care about, and
    when you cannot, compare two sizes and look at the ratio.
    The two fixes, both verified by byte-identical LLVM IR:
    - **`lookup_def_type` (`lang/src/scope.mo`)** walked a `List
      DefTypeEntry` linearly and fires on every `Term.app` node in the
      graph -- ~4,020 steps per application node, each rendering a
      `ModulePath` via `show_module_path`. Indexed into a `HashMap String
      Term` (`llvm/src/strmap.mo`'s `str_map_*` -- a leaf module, so
      `scope.mo` can import it with no cycle). -94%.
      Preserving the scan's exact answer is the delicate part: it matched
      full-dotted-name OR bare-last-segment, FIRST entry in decl order
      wins. So register each def under BOTH keys, earlier entries winning
      (`def_type_insert_first` -- plain `str_map_insert` replaces, giving
      last-wins, which is NOT the same function).
    - **`modpath_map_*` (`lang/src/scope.mo`)** stored `ModulePath` keys, and
      a `ModulePath` has no cheap hash or equality: both go through
      `show_module_path` (`List.intercalate "." (List.map
      show_identifier ids)`), rebuilt per call. `bucket_*_eq` invokes the
      comparator once PER CHAIN STEP, so one insert over ~4,200 keys /
      256 buckets rendered ~32 paths. Item 26 halved this (4 renders per
      step -> 2) but could not remove it, because while the STORED key is
      a `ModulePath` every comparison must re-derive it. Render once at
      the boundary, store the string, drop to `bucket_insert_str`/
      `bucket_lookup_str`. `check cli/src/main.mo` 140.7s -> 82.3s (-41.5%)
      -- but only -3.7% on hello.mo, the same small-scale blindness.
    Also landed, and worth knowing before profiling anything here: the
    workspace had **no `[profile.release]` at all** (so `codegen-units =
    16`, `lto = false`) and no `#[global_allocator]`. Adding `lto =
    "fat"` / `codegen-units = 1` is -5.0% and mimalloc a further -22.6%
    on interpreted workloads, -25.7% combined. Take any before/after
    numbers older than 2026-09-09 as measured on the slower binary.
38. **`U64.mod` was a SIGNED remainder, which collapsed half of every
    `HashMap` in the self-hosted compiler into ONE bucket. Full
    self-compile 275424ms -> 115193ms (-58.2%) from one line
    (2026-09-12).**
    `core/src/core_native.rs` had `"u64_mod" => int_binop(args, |a, b| ...
    a.wrapping_rem(b))`, and `int_binop` computes on the raw `i64`
    payload, so a signed remainder took the sign of its dividend.
    `String.hash` is djb2, which wraps, so ~half of all hashes have bit 63
    set and read back negative -- and `HashMap.bucket_of` (`std/src/map.mo`) is
    `U64.mod hash 256u64`. `Bucket16.get`'s dispatch is
    `if U64.beq 0u64 idx then b0 else ... else b15`, which does not REJECT
    a negative index, it FALLS THROUGH it into the last slot. Over the
    compiler's own 3,068 emitted symbol names: 1,618 hash negative and
    1,612 shared one bucket, against a worst bucket of 23 once the mod is
    unsigned. Fixed with a `uint_binop` path for `u64_div`/`u64_mod`;
    `add`/`sub`/`mul`/`xor`/`beq` are bit-identical either way and still
    share `int_binop`. Note `U64.lt`/`U64.gt` are STILL signed
    (`int_cmp`), which is a latent bug for values >= 2^63 -- not needed by
    `HashMap`, which compares bucket indices with `beq`, but do not assume
    the `U64` family is unsigned just because this one now is.
    **The code already recorded the divergence and dismissed it.**
    `runtime/src/natives.mo`'s `emit_u64_mod` uses `urem`, and its comment
    said bucketing is internal to `HashMap`, only self-consistency matters,
    and "`std/src/map.mo`'s own 0-15 bucket chain is simply never entered with
    a negative index". True, and the trap: not ENTERED, FALLEN THROUGH. So
    the compiled binary was always fine and only the INTERPRETER paid --
    which is the runtime CI's self-compile actually uses.
    Every map-backed phase fell 55-97% and every phase touching no map was
    unchanged, which is the diagnosis confirming itself:
    `build_scope_from_decls` 12308 -> 1014, `names_of_decls` 4220 -> 272,
    `qualify_modules` 25435 -> 5118, `elaborate_class` 71244 -> 26694,
    `filter_reachable` 13083 -> 2616, `compile_db_module` 33002 -> 12780,
    the call-target gate 47800 -> 1366; `load_file_modules` 45685 ->
    45317, `open_alias_resolve` 5476 -> 5348, `emit_module` 3886 -> 3921,
    `llc` 3184 -> 3225. `load_file_modules` is now 39% of the compile and
    the dominator.
    **The tell, and the transferable rule: a per-operation cost ~1000x its
    plausible floor means the DATA STRUCTURE is broken, not the loop.**
    One hashmap probe was costing 1.17ms (45443ms for ~38,800 probes of a
    3,068-key map). That was only visible because the probe loop was
    sub-timed separately from the whole-module walk wrapped around it --
    the walk was 387ms, i.e. the part that looked expensive was not.
    **Order-sensitivity this changes, covered but worth knowing:** bucket
    assignment changes `HashMap.to_list` order, and `scope_all_inductives`
    (`lang/src/lower_core_ir.mo`) feeds `find_inductive_by_case_name`, which
    takes the FIRST inductive owning a constructor of a given name -- its
    own comment calls reordering "a miscompile, not a slower build". That
    order was ALREADY arbitrary hash order, so this re-rolls dice rather
    than newly loading them, but it is why the oracle and the full corpus
    (including `slow_tests`) are the gate for a bucketing change, not
    reasoning.
39. **Bytes copied does not predict wall time when the inner operation is a
    native memcpy (2026-09-12).** `emit_instrs` (`llvm/src/ir.mo`) was
    the one function in its family still doing
    `String.concat a (recurse rest)`, the shape `emit_blocks`' own comment
    condemns. Quantified from the compiler's emitted module: 20,389 basic
    blocks, 3.55 MB of instruction text, ~1.7 GB recopied (~3.4 GB counting
    both concats per instruction) -- a ~500x amplification, and it was
    ranked the top defect on that basis. Converted to the chunk-list +
    `String.concat_list` form: worth about **0.5s**. `String.concat` is a
    native `memcpy` and there were only ~200k calls. What costs time in
    this interpreter is the NUMBER OF INTERPRETED STEPS and allocations,
    not bytes moved -- which is why item 38's bucket-chain scan beat this
    by two orders of magnitude. Keep the fix (it is strictly less work and
    the output is identical by construction), but size a quadratic by the
    count of interpreted operations it performs, not by the bytes it
    touches.
40. **Inserting a def between an attribute and its `def` -- or into the
    middle of a doc comment -- derails the self-hosted parse of the WHOLE
    file, and `monad-rs check <file>` reports 0 errors (2026-09-12).**
    Same family as item 20 ("deleting a def can silently truncate the
    self-hosted parse"), different trigger, and the diagnosis is much less
    obvious because the file you broke is not the file that complains: it
    surfaces as `unknown variable '<some other def in that file>'` in an
    unrelated IMPORTING file. Landing a helper between `#[partial]` and
    `def compile_loaded_modules_to_ir_with_debug` (`lang/src/codegen/emit.mo`)
    produced `unknown variable 'compile_db_module_with_debug'` and
    `'compile_loaded_modules_to_ir_with_debug'` in `cli/src/main.mo`, while
    `monad-rs check lang/src/codegen/emit.mo` stayed clean -- the Rust host and
    the self-hosted parser are different code paths.
    **Fast reproducer: `monad-rs run cli/src/main.mo check cli/src/main.mo`
    (~60s), not a self-compile.** The tell is the self-hosted checker
    echoing your doc-comment lines back as content. When adding a def by
    script, anchor above the whole doc-comment + attribute + `def` group,
    never on the `def` line alone.
41. **A `--release` profile says nothing about the DEFAULT path, and the
    default path had a 164x pathology nobody had ever profiled
    (2026-09-12).** Debug info is on by default (`--release` opts out,
    `cli/src/main.mo`), but every recorded profile -- including CI's
    `monad:bootstrap-compile` -- is a `--release` run. A `--verbose`
    self-compile WITHOUT `--release` took **28035824ms (7h48m)** against
    275424ms with it, every timed phase within noise, so ~7h44m (99.4%)
    sat in the one untimed span: `with_located_decls` (`cli/src/main.mo`),
    which re-reads and re-parses the whole dependency graph to attach
    `Term.ctx` position wrappers. It then FAILED
    (`no instance found for Append.append`), so the default path did not
    even work -- unnoticed because nobody waits eight hours.
    Root cause: `resolve_offsets_in_file` (`lang/src/parser/position.mo`)
    checked `is_ascending offsets` and otherwise fell back to
    `resolve_one_by_one`, its own doc comment calling it "the
    correct-but-quadratic path" -- a whole-file rescan per offset, taken
    silently. `build_loc_table` (`lang/src/parser.mo`) asserted pre-order
    collection yields ascending offsets. **It does not, and the
    counterexample is every infix expression in the language:** `a + b`
    parses to `app (app (+) a) b`, so a pre-order walk reaches the operator
    node -- whose span starts at the `+` -- before the operand `a` that
    precedes it in the source. Measured with `bench/src/parser_located.mo`
    (kept as the standing guard, and it runs in seconds rather than hours):
      init/src/id.mo      675 B,   30 spans  ascending YES   27ms ->     36ms
      lang/src/types.mo 73000 B, 1469 spans  ascending NO  1753ms -> 287766ms
    first inversion at span index 244. Fixed by SORTING
    (`sort_offsets_asc`, a local merge sort -- there is no `List.sort` in
    `std/`) and **deleting the fallback**: located parse of `lang/src/types.mo`
    287766ms -> 2012ms (-99.3%). An unreachable-by-hope slow path that
    nothing exercises is how this hid. Two rules: profile the mode users
    actually get, not only the one CI measures; and a "slow beats wrong"
    fallback needs something that FAILS when it is taken, or it becomes the
    fast path in the dark.

42. **Placement rule R3 protects an application's HEAD, not its ARGUMENTS,
    so argument-reading shape probes were the exposed `Term.ctx` surface --
    and the fix was to delete the debug/release divergence, not to patch it
    (2026-09-13).**
    `monad compile cli/src/main.mo` WITHOUT `--release` -- the default
    invocation -- failed with `no instance found for `Append.append``.
    Mechanism: `a ++ b` lowers to `app (app (var "++") a) b` with a bare
    callee and LOCATED operands, so recognition worked (`flatten_call_spine`
    peels, `class_method_ref` takes an `Identifier`) but `infer_carrier_type`
    (`lang/src/scope.mo`) -- which reads the ARGUMENTS to pick the instance --
    had no `Term.ctx` arm, returned `Option.none` for every argument, and
    the call was left unresolved. **It was a regression of a bug already
    fixed once:** that function's `Term.app` arm says in its own comment it
    is "the root cause of the `Append_append` self-compile bug", and the
    wrapper made the arm unreachable.
    The 2388-vs-2390 reachable-decl gap was the SAME cause, not a second
    bug: an unresolved call keeps the name `Append.append`, which matches no
    `Def`, so the promoted instance method and its dictionary never entered
    the reachability worklist. Both symptoms closed together, and the two
    modes now report an identical reachable count -- which is the check to
    use, since it is independent of the error message.
    **The fix was structural.** `parse_all_decls` (`lang/src/module.mo`) now
    uses `decls_parser_located` on EVERY path, so `check`, `test` and
    `compile` all see one term shape and `--release`/`--debug` gates only
    whether DWARF is EMITTED. `with_located_decls`/`locate_module_info*`
    are gone with it, and so is the second full parse the debug path used to
    pay. One word at the one production parse site; everything else followed.
    **Five probes needed `term_peel`, and the order they surfaced in is the
    lesson** -- each was found by a different gate, and no single gate found
    more than two:
      `infer_carrier_type`, `term_matches_carrier`  (`lang/src/scope.mo`)
          -- the SELF-COMPILE only. `term_matches_carrier` broke
          `class FromListLiteral (L : Type := List)` (`init/src/prelude.mo`),
          i.e. every list literal and `Map.empty`, because a class param's
          `default` lowers as a VALUE and so is itself wrapped.
      `scrutinee_type_args` (`lang/src/scope.mo`)      -- fixed pre-emptively.
      `named_call_fields_of` (`lang/src/typecheck/infer.mo`)
          -- `slow_tests/codegen_named_call_*_tests.mo`, 6 tests.
      `con_owner_name` (`lang/src/typecheck/infer.mo`)
          -- `slow_tests/src/typecheck_init_tests.mo`, as `ambiguous constructor
          `cons`: could resolve to either `Vec` or `List`` on
          `init/src/tests.mo`.
    Peeling at entry (`match term_peel t {`) needs `#[terminating]` when the
    function also recurses on a subterm: `f` is then a structural subterm of
    `term_peel t`, not of `t`, and the checker cannot see through it.
    **A small file CANNOT test the carrier-inference gaps, and this was
    verified rather than assumed.** With the peel removed from
    `infer_carrier_type` or `term_matches_carrier`, `examples/located_terms.mo`
    -- written specifically to contain those shapes -- still compiles clean.
    The type checker's own `resolve_class_method` is ctx-transparent for
    them and runs first; `lang/src/scope.mo`'s syntactic pass is only
    load-bearing for a def whose ELABORATION failed, which
    `elaborate_module_decls_best_effort` swallows silently and which needs
    self-compile scale to happen at all. So the self-compile in BOTH modes
    is now a CI job (`monad:bootstrap-compile`), and
    `tools/debug_transparency_oracle.sh` -- which existed, unwired, naming
    `class_method_ref` in its own header while this bug was live -- is now
    `monad:debug-oracle`. Note what the oracle can and cannot mean now that
    both modes are located: it checks that `--debug` adds `!dbg` and nothing
    else. The transparency gate for a change like this one is instead
    **`--release` IR byte-identical before vs after** (13/13 examples here).
    **Also landed, because the silence was half the problem:**
    `elaborate_module_decls_reporting` (`lang/src/module.mo`) returns the names
    of decls best-effort elaboration gave up on, and `--verbose` prints the
    count and first few. On the self-compile that is exactly one --
    `prelude::Lens` -- which had been invisible the whole time.
    **The cost is real and was accepted deliberately:** one located parse
    instead of one plain parse on every path. Interleaved A/B, two rounds,
    machine idle: `check cli/src/main.mo` **57.5s -> 86.8s (+51%)**;
    `load_file_modules` 45.3s -> 75.4s. The debug compile got FASTER (it
    stops parsing twice: 172.1s -> ~157s).
    **Where that delta goes was then measured, and my own guess above about
    it was wrong.** I had written that a located tree has ~2x the nodes and
    every downstream pass walks them, so that was "at least as likely the
    bulk". It is not. An interleaved `--verbose` phase-table A/B at load
    0.21 puts the ENTIRE +29.8s inside `load_file_modules` (45721-46276ms ->
    75718-75878ms) with every downstream phase flat (`resolve_infix_decls`
    +4%, `build_scope_from_decls` and `names_of_decls` unchanged). The cost
    is in PRODUCING the tree, not consuming it. Decomposed in one process by
    `bench/src/parser_locate_cost.mo` on `lang/src/types.mo` (73000 bytes, 1469
    spans): of 739ms of located overhead on a 1255ms baseline,
    `resolve_offsets_in_file` is **652ms (88%)** and `build_loc_table`'s
    `I64.to_string` rekeying -- my first suspect -- is 54ms.
    The reason that one function is slow is worth keeping: it walked EVERY
    character of the file, and per character `utf8_char_width`
    (`lang/src/parser/combinators.mo`) is `match String.get s 0`, where
    `string_get` returns a `Value::Con` -- **an `Option` allocation per
    character**. This also explains a rewrite that failed: recasting the
    loop as a byte-index scan assumed item 28's pathology (`String.slice`/
    `String.drop` allocating), which `SharedStr` had already made false --
    they are O(1) views -- so the "fix" swapped a free slice for another
    `String.get` and could not have won. Its end-to-end comparison was taken
    at load 9.4 against an hour-old baseline, so it did not even measure
    that; see item 24, which forbids exactly that mistake.

43. **In a self-hosted compiler, a hot loop's cost is whichever primitive it
    calls per step -- and the SAME primitive costs differently on the two
    runtimes (2026-09-13).**
    `resolve_offsets_in_file` (`lang/src/parser/position.mo`) was 88% of what
    locating every term cost. It walked every character of the file to turn
    byte offsets into line:column. Three separate lessons came out of fixing
    it, and the first two are corrections to my own reasoning:
    **(a) The per-step primitive, not the loop shape, was the cost.** Per
    character the walk called `utf8_char_width`, which is
    `match String.get s 0` -- and `string_get` returns a `Value::Con`, so the
    walk allocated an `Option` PER CHARACTER, ~8.9us each. Rearranging the loop
    could not help; a first attempt rewrote it as a byte-index scan on the
    theory that `String.slice`/`String.drop` allocate (item 28's pathology),
    which `SharedStr` had already made false -- they are O(1) views -- so the
    "fix" swapped a free slice for another `String.get`. **Check what the
    primitive does TODAY before reusing an old profile's conclusion about it.**
    **(b) The same call has different asymptotics interpreted vs compiled, and
    `lang/` runs BOTH ways.** Host `string_slice` is an O(1) `SharedStr` view;
    compiled `monad_string_slice` (`runtime/src/runtime.c`) does a `strlen`
    plus a malloc plus a memcpy per call. So the old per-character
    `String.slice s 0 width` was O(1) interpreted and QUADRATIC in every
    self-compiled build -- invisible to any host-side profile. `String.length`
    is the same trap (`strlen`, compiled), so hoist it out of loops.
    The fix takes one step per SPAN instead of per character, with two natives
    (`String.count_newlines`/`String.trailing_chars`) that take a LENGTH and
    scan in place, so nothing is sliced on either runtime: 652ms -> 70ms,
    measured on `lang/src/types.mo` by `bench/src/parser_locate_cost.mo`, and
    `check cli/src/main.mo` 87.1-88.1s -> 69.2s end to end (interleaved, three
    rounds, load 1.06-1.66). Note the gap between those two numbers: the
    652ms was 88% of the located overhead on ONE file, and extrapolating it
    predicted ~61s, but only 61% of the real regression came back. Item 37
    again -- a share at one scale does not carry to another, so measure the
    whole thing rather than scaling the microbenchmark.
    **(c) Do not delete the oracle you are testing against -- DEMOTE it.**
    `line_col_scan`/`single_location_at` are an independent second
    implementation of the same arithmetic, and `agrees_at_all` cross-checks the
    resolver against them. Rewiring both through the new natives at the same
    time would have left the rewrite unverifiable, so it was deferred. When it
    was then done, the way to keep the check was to make the slow
    character-at-a-time scanner (`line_col_scan_direct`) a TEST-ONLY reference
    implementation rather than deleting it, and add
    `test_line_col_scan_matches_reference` comparing the two. That preserves
    the independence where it matters -- the reference decides "what is a
    character" by stepping `utf8_char_width` over lead bytes, the natives by
    counting non-continuation bytes, so the two derivations agreeing is a real
    property and not a tautology. The general move: when a slow
    implementation is the only thing proving a fast one correct, its
    replacement should turn it into a test fixture, not remove it.
    Converting it was worth doing on its own merits even though its only live
    caller is cold: rendering a parse error in a 76KB source went **311.92ms
    -> 4.19ms** (74x), which is latency a user eats on every syntax error in a
    big file.
    A related fact worth knowing, found while writing the mid-character test:
    `String.slice` on a range that would SPLIT a UTF-8 character returns the
    EMPTY string (`get(start..end).unwrap_or("")`), so `single_location_at`
    silently answers 0/1/1 for any non-boundary offset. Verified, not assumed.

44. **A `\u{XXXX}` escape passes `monad-rs check` and `monad-rs test`, then
    kills the self-compile (2026-09-13).**
    The Rust reference string parser accepts unicode escapes; the self-hosted
    one (`escape_replacement`, `lang/src/parser/string.mo`) deliberately does not,
    for want of a hex-to-codepoint native. Its doc comment says so and adds
    "zero known corpus impact since no `\u{}` escape appears anywhere in the
    current corpus" -- which is an INVARIANT, not an observation. One
    `"\u{00e9}"` in a test fixture in `lang/src/parser/position.mo` broke it.
    **What makes this expensive is the failure shape.** Everything that goes
    through the Rust host is clean: `monad-rs check` reports 0 errors,
    `monad-rs test` passes, the corpus passes 1481/1481, and `--release` IR
    stays byte-identical. The self-hosted parse rejects the WHOLE module, so
    the first symptom is a self-compile dying at
    `compile_loaded_modules_to_ir` with `call to undefined symbol(s):
    location_of_remaining; resolve_offsets_in_file` -- the names of defs that
    plainly exist, in a file that plainly compiles. Same shape as item 40, and
    the same fast reproducer (~60s, not a full self-compile):
    `monad-rs run cli/src/main.mo check <file>`, which reports
    `did not fully parse (stopped before end of file)` and prints the
    offending text.
    Write the literal character instead. And note what found it: the
    `elaborate_module_decls_reporting` line added in item 42 went from 1
    un-elaborated decl to 15 and NAMED them -- `render_parse_error`,
    `build_loc_table`, `location_of_span`, all consumers of the broken
    module. Before that line existed this would have been a silent symbol
    error with nothing pointing at the cause.

## Committing Changes

### Commit Message Format

Do not include a `Claude-Session:` trailer (or link) in commit messages
for this repo.

### Pre-commit Hooks

Always commit with pre-commit hooks enabled. **Never** use `git commit --no-verify` — the pre-commit hooks ensure clippy, rustfmt, `cargo test`, and `cargo run --release -- test init std lang examples` all pass before each commit. If a hook fails:
1. Read the error message to identify the issue
2. Fix the underlying problem (code warnings, test failures, formatting)
3. Stage the fix and retry the commit

**IMPORTANT**: When `rustfmt` hook fails, the commit DID NOT succeed (the files
were modified by the hook but NOT committed). Always run `cargo fmt` manually
BEFORE committing. If the hook modifies files, the commit was rejected — run
`cargo fmt && git add <modified files> && git commit ...` to retry.

**DO NOT** assume the commit succeeded when you see "files were modified by
this hook" — that means the hook rejected the commit. Always check
`git log -1` after committing to verify.

### Pre-commit Checklist

Before committing, ensure:
```bash
cargo fmt
cargo build --package monad-core 2>&1 | grep -E "warning:|error"
cargo test
cargo run -- test init/
cargo run -- test std/
cargo run -- test lang/
```

## Coding Agent Guide

### Agent Skills

Look in `plans/.opencode/skills/` for skill documents. Read the relevant
skill before starting any task — they contain checklists, command templates,
and anti-patterns that prevent common errors. List available skills with:

```bash
ls plans/.opencode/skills/
```

### Problem-Solving Workflow

1. **Reproduce first** — Before any change, confirm you can reproduce the bug or observe the missing behavior. Run the exact command the user provides.

2. **Search evidence, not guesses** — When investigating a bug, anchor every hypothesis in code. Search for the error message string in the source. Search for the function name mentioned in stack traces. Never assume — verify.

3. **Isolate the failure** — Minimize the failing case. Reduce a complex Monad program to the smallest example that still fails. This tells you which language feature is involved and narrows which compiler pass to modify.

4. **Trace the pipeline** — A Monad program goes through: parsing → elaboration → type checking → evaluation. Identify which stage fails:
   - **Parser errors** mention `parse` or show unexpected tokens
   - **Elaboration errors** mention free variables or implicit binding
   - **Type errors** mention `TypeError` and expected/found types
   - **Eval errors** mention `CoreEvalError`, stack overflow, or missing native
   - **Panics** mean an `unreachable!()` was hit — often a missing case in a match

### Fast Iteration

```bash
# Fastest: build just the core crate (avoids CLI/WASM/LLVM)
cargo build -p monad-core 2>&1 | head -20

# Run a single test by name
cargo test core_check_module::some_test_name

# Run all parser tests
cargo test parser

# Run Monad stdlib tests (fast feedback on language semantics)
cargo run -- test init/src/tests.mo

# Run a specific example
cargo run -- run examples/specific.mo
```

Prefer `cargo test parser::test_do_parser` over `cargo test` when working
on the parser — it saves minutes per iteration.

### Finding the Right Code

| Symptom | Look In |
|---|---|
| Parse error / wrong syntax accepted | `core/src/parser.rs` — search for the relevant parse function |
| Wrong type inferred / type error missing | `core/src/eval/type.rs` — search for the type form |
| Wrong evaluation result / runtime error | `core/src/eval.rs` — search for the term variant |
| Native function wrong / missing | `core/src/eval/native.rs` — search for the function name |
| Term representation / new AST node | `core/src/term.rs` — add new `Term` variants here |
| Constraint solving / instance resolution | `core/src/eval/constraint.rs` |
| Module loading / use/open | `core/src/term/module.rs` |
| CLI flags / command handling | `rust-cli/src/main.rs` |

Use `rg` (ripgrep) to search — it respects `.gitignore` and is fast:

```bash
# Find where an error message is emitted
rg "expected function"

# Find all references to a function
rg "fn type_check_free_var"

# Find Monad code using a feature
rg "linear\|affine" init/ --include "*.mo"
```

### Common Bug Patterns in Compiler Development

**1. Missing match arm on a new Term variant.**

When you add a `Term::Foo` variant, every `match` on `Term` in the codebase
needs handling. The Rust compiler catches this — follow the compilation
errors. The most common locations: `eval.rs` (evaluation), `type.rs` (type
checking), `module.rs` (scope building), `term.rs` (Display, substitution).

**2. Forgetting to add a new Term variant to `substitute()` or
`free_vars()`.**

These are in `eval.rs` / `term.rs`. If substitution doesn't handle the new
variant, variables won't be replaced and evaluation will use stale bindings.
**Check these even if the Rust compiler doesn't force you to** (some
`substitute` impls have a catch-all `_ => term`).

**3. Adding a parser test but not testing the desugared AST.**

Parser tests compare against expected ASTs. If a test passes but produces
wrong output, check that the expected AST in the test matches what the
evaluator expects. The desugaring is often in a separate function from the
parser.

**4. Instance resolution loops.**

Recursive instances (`instance [Show A] Show (List A)`) can cause infinite
resolution. The constraint solver at `constraint.rs` has a visiting set.
If it doesn't, or the visiting set misses a path, the compiler hangs.
Always check the visiting set when modifying instance resolution.

**5. The evaluator and type checker use different `Scope` types.**

`eval.rs` uses `scope.resolve_name()` which goes through `GlobalScope`.
`type.rs` uses `find_var_ref_of` which walks the linked-list `Scope`.
A def that's visible to one may not be visible to the other. When a name
resolves in the type checker but not the evaluator (or vice versa), the
scope builder (`module.rs`) is usually the culprit.

### Writing Tests for Bug Fixes

1. **Add a parser test** (`core/src/parser/test/`) if the bug involves syntax
2. **Add an eval test** (`core/src/eval/test.rs`) if the bug involves evaluation
3. **Add a Monad test** — use `#[test]` in:
   - `init/src/tests.mo` for bugs involving core language semantics (prelude types, operators, etc.)
   - `std/<module>_test.mo` for bugs in `std/` modules (concurrency, collections, etc.)
   - Never add `std/`-dependent tests to `init/src/tests.mo` — `init/` must not depend on `std/`
4. **Test the failing case first** — confirm it fails before your fix, then
   confirm it passes after

Follow the existing test patterns exactly. Parser tests use the `similar!`
macro with `do_parser()`/`def_parser()`. Eval tests use `run_test()`/`run_test_err()`.

### Incremental Changes

Always take the smallest possible step:

1. One failing test → one fix → one commit
2. Don't refactor unrelated code while fixing a bug
3. Don't add new features while fixing a bug
4. If you need to refactor to fix, do it in a separate commit

When a change touches multiple files, commit after each file if the
intermediate state compiles and passes tests. This makes `git bisect`
precise.

### Debugging the Evaluator

When a Monad program produces the wrong result:

1. Add `--debug` to see evaluation steps: `cargo run -- run file.mo -- --debug`
2. Or insert `println` in the Rust evaluator at `eval.rs` around the
   relevant term case
3. Check that native functions match their declarations — the Monad type
   signature and the Rust handler must agree on argument count and types
4. Verify that substitution produces the expected term — many eval bugs
   are actually substitution bugs

### Rebase Resolution Workflow

When rebasing a feature branch onto upstream changes that touch the same
Monad source files, the safest resolution strategy is:

1. **Accept the upstream file as-is**: `git checkout --theirs <file>` to
   start from a clean upstream state. This avoids tedious per-hunk conflict
   resolution when large AST renames (e.g., `Term` → `TermV0`) sweep
   through the file.
2. **Reapply your edits on top**: Port each logical change set (function
   compactions, table conversions, etc.) onto the fresh upstream base.
3. **Audit for leftover artifacts**: Check for:
   - Double `#[partial]` annotations (both upstream and your stashed code
     may have had one → both land after checkout/reapply)
   - `#[partial]` on pure (non-parsing) helper functions (not needed)
   - Old helper functions that upstream renamed parameters on but you
     removed entirely (check with `rg -n 'helper_name' <file>`)
4. **Verify**: Run `cargo run -- test <file>` and verify all tests pass.
   If the number of tests changes, confirm the delta is expected (e.g.,
   upstream added tests to match new AST variants).
5. **Verify no unmerged files remain**: `git diff --name-only --diff-filter=U`

**Common artifacts after checkout/reapply**:
- Double `#[partial]`: the upstream `#[partial]` + your stashed `#[partial]`
  both survive. Remove duplicates.
- `#[partial]` on pure helpers: `num_to_term`, `op_check` don't need it.
- Old helper definitions that were supposed to be deleted but survived
  because upstream changed their parameter names (making the conflict
  resolution merge them back as "separate" definitions).

**`fn` lambda parameter syntax**: When reapplying compactions that use
`bind_parse`/`map_parse`, inline `fn` lambda arguments work fine
(including generic combinators) as long as annotated parameters are
parenthesized — `fn (s : String) => ...`, not `fn s : String => ...` (see
Known Issues above).
