# Monad language

> [!WARNING]
> Monad is in **alpha release** and under heavy development. Many features are not implemented yet and are not tested properly. Expect breaking changes, incomplete functionality, and potential bugs.
>
> The [Maturity Matrix](docs/src/maturity.md) says, area by area, what actually works today.

A purely functional systems programming language compatible with LLVM made just for fun.
It is inspired by the languages Rust, Haskell, Idris, Lean and Elm.

🌐 **[Homepage](https://monad-lang.org)** · **[Documentation](docs/src/introduction.md)** · **[Maturity Matrix](docs/src/maturity.md)**

## Feature goals

- Dependent types
- Quantitative and linear types (borrowing)
- Provably correct programs and invariants
  * Dependent types means you can guarantee with proofs in compile time that an implementation follows a specification.
  * It is an opt-in feature.
- Not a proof assistant.
  * It can represent proofs, but proof tooling will not be part of the core language.
- Managed side effects using monads
- Egonomic, expressive and efficient system programming
- Hygenic macros
- Practical programming
- Quantum lambda calculus support
- Minimal features
  * No clutter and unecessary features. Keep it simple.

## Quick start

### Devenv environment (recommended)

Use [devenv](https://devenv.sh) for a quick and reproducible environment:

```bash
# Install devenv (if not already installed)
# https://devenv.sh/getting-started/

# Enter the development shell
devenv shell

# This provides: Rust toolchain, clang, llvm, lld, wasm-pack, boehmgc, mdbook
```

If you prefer a manual setup, install:
- [Rust toolchain](https://rustup.rs) (stable)
- `clang` and `llc` (for native compilation via the LLVM backend)
- the Boehm GC development files (the compiled runtime links `-lgc`)

### Build

```bash
cargo build
```

### Build the self-hosted compiler

The compiler is written in Monad and compiles itself. The Rust crate is the
**bootstrap host** that produces the first binary:

```bash
cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$PWD/monad" --release
```

The `-o` must be **absolute**: a relative output name is resolved against the
compiler's own scratch directory, `/tmp/monad_out_<pid>`. The trailing
`--release` turns off DWARF debug info, which is on by default.

Prebuilt nightlies are published on every push to `main` and installed with
`scripts/monadup` (`monadup self-install`, then `monadup default`). They are
Linux x86_64 and are built inside the Nix devenv, so they link store paths and
will not run on a machine without them -- building from source is the portable
route. See [Compiling and Running](docs/src/compiling.md#getting-a-compiler).

### Compile and run a program

```bash
cat > /tmp/main.mo << 'EOF'
def main : I64 := 42
EOF

./monad compile /tmp/main.mo -o /tmp/monad_binary
/tmp/monad_binary
echo $?   # prints 42
```

`monad run /tmp/main.mo` does both steps in one go. (There is also `monad eval`,
an interpreter, but only eight pure natives are wired into it -- it cannot print.)
A program is always compiled to a native binary. `def main (args : List String) :
I64` works too: the C runtime converts `argc`/`argv` to a `List String` and
passes it to `main_monad`.

The backend wires a subset of the natives (no concurrency yet), and says so at
compile time rather than emitting a broken binary. See
[Compiling and Running](docs/src/compiling.md) for the full pipeline, the
fail-fast validation gates, and how memory is managed.

### Run a program with the bootstrap host

Faster to iterate with, since it skips `llc` and `clang`:

```bash
cargo run -- run examples/hello.mo
```

The host also carries the LSP and MCP servers, the REPL, and the package system
-- and it differs from the self-hosted compiler in a handful of places. See
[The Bootstrap Host](docs/src/bootstrap-host.md).

### Run the test suites

```bash
# Rust unit tests
cargo test

# The full .mo sweep, through the SELF-HOSTED runner -- builds the
# compiled binary first if needed. This is what CI runs.
scripts/check-monad-tests.sh

# Or via the Rust host, which is handy while debugging the runner itself
cargo run -- test init std lang

# Type-check without running
cargo run -- check init std examples lang

# Type-check every code block in docs/
scripts/check-docs.sh
```

### Bootstrap fixpoint

Once built, the compiler builds its own successor, and the binary that falls out
does the job it was built for. CI runs exactly this on every push.

```bash
./monad compile cli/src/main.mo -o "$PWD/monad-next" --release

# Then make the result type-check the compiler's own source
./monad-next check cli/src/main.mo
```

The self-hosted compiler's own subcommands are `compile`, `run`, `eval`,
`check`, `test`, `pretty`, and `version` -- run it with no arguments for usage.

### Architecture

| Component | Location | Description |
|-----------|----------|-------------|
| **Rust compiler** | `core/`, `rust-cli/` | Parser, type checker, evaluator, constraint solver, LSP + MCP servers |
| **Self-hosted codegen** | `lang/src/codegen/` | Monad terms -> LLVM IR |
| **LLVM backend** | `llvm/src/` | The IR data model, its `.ll` rendering, llc/clang glue |
| **C runtime** | `runtime/src/runtime.c` | Heap allocation (Boehm GC), constructor/string objects |
| **Standard library** | `init/src/`, `std/src/` | Prelude types, type classes, native-backed operations |
| **Self-hosted compiler** | `lang/src/` | Parser, evaluator, lowering pass (Monad-in-Monad) |

