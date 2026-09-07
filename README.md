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

### Run a Monad program (interpreted)

```bash
cargo run -- run examples/hello.mo
```

### Compile to a native binary

Native compilation lives in the **self-hosted** compiler (`lang/`), not in
`monad-rs` -- the Rust CLI interprets and type-checks, it does not compile.
The backend wires a subset of the natives (no concurrency yet), and says so at
compile time rather than emitting a broken binary.

```bash
# Write the program
cat > /tmp/main.mo << 'EOF'
def main : I64 := 42
EOF

# Compile it with the self-hosted compiler, run under the interpreter
cargo run --release -- run lang/main.mo compile /tmp/main.mo -o /tmp/monad_binary

# Run and verify the exit code
/tmp/monad_binary
echo $?   # prints 42
```

`def main (args : List String) : I64` works too: the C runtime converts
`argc`/`argv` to a `List String` and passes it to `main_monad`.

See [Compiling to Native](docs/src/compiling.md) for the full pipeline, the
fail-fast validation gates, and how memory is managed in compiled binaries.

### Run the test suites

```bash
# Rust unit tests
cargo test

# Monad standard library tests
cargo run -- test init std

# Self-hosted compiler tests
cargo run -- test lang

# Type-check without running
cargo run -- check init std examples lang

# Type-check every code block in docs/
scripts/check-docs.sh
```

### Bootstrap the compiler

The self-hosted compiler compiles itself, and the binary that falls out does
the job it was built for. CI runs exactly this on every push.

```bash
# Compile the compiler with itself (requires llc + clang)
cargo run --release -- run lang/main.mo compile lang/main.mo -o /tmp/monad

# Then make the result type-check the compiler's own source
/tmp/monad check lang/main.mo
```

The self-hosted compiler's own subcommands are `compile`, `check`, `test`, and
`pretty` -- run it with no arguments for usage.

### Architecture

| Component | Location | Description |
|-----------|----------|-------------|
| **Rust compiler** | `core/`, `cli/` | Parser, type checker, evaluator, constraint solver, LSP + MCP servers |
| **Self-hosted codegen** | `lang/codegen/` | Monad-in-Monad LLVM IR emitter + linker |
| **C runtime** | `lang/codegen/runtime.c` | Heap allocation (Boehm GC), constructor/string objects |
| **Standard library** | `init/`, `std/` | Prelude types, type classes, native-backed operations |
| **Self-hosted compiler** | `lang/` | Parser, evaluator, lowering pass (Monad-in-Monad) |

