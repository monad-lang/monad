# Monad language

> [!WARNING]
> Monad is in **alpha release** and under heavy development. Many features are not implemented yet and are not tested properly. Expect breaking changes, incomplete functionality, and potential bugs.

A purely functional systems programming language compatible with LLVM made just for fun.
It is inspired by the languages Rust, Haskell, Idris, Lean and Elm.

🌐 **[Homepage](https://monad-lang.org)** · **[Documentation](docs/src/introduction.md)**

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

# This provides: Rust toolchain, clang, llvm, lld, wasm-pack
```

If you prefer a manual setup, install:
- [Rust toolchain](https://rustup.rs) (stable)
- `clang` and `llc` (for native compilation via the LLVM backend)

### Build

```bash
cargo build
```

### Run a Monad program (interpreted)

```bash
cargo run -- run examples/hello.mo
```

### Compile to a native binary (experimental)

```bash
# Write the program
cat > /tmp/main.mo << 'EOF'
def main : I64 := 42
EOF

# Compile via the Rust LLVM codegen backend
cargo run -- compile /tmp/main.mo -o /tmp/monad_binary

# Run and verify the exit code
/tmp/monad_binary
echo $?   # prints 42
```

### Compile with command line arguments

`def main (args : List String) : I64` is supported via the self-hosted
codegen (`lang/codegen/`). The C runtime converts `argc`/`argv` to a
`List String` and passes it to `main_monad`.

### Run the test suites

```bash
# Rust unit tests
cargo test

# Monad standard library tests
cargo run -- test init std

# Self-hosted codegen tests
cargo run -- test lang
```

### Compile and run via the self-hosted codegen (experimental)

The self-hosted codegen compiles Monad `Def` AST nodes to LLVM IR, invokes
`llc`/`clang`, and runs the resulting binary.

```bash
# Run the self-hosted codegen test suite (all unit tests)
cargo run -- run lang/main.mo test-all

# The full pipeline (requires llc + clang):
# Test file: lang/codegen/test/test_link_e2e.mo
# Constructs `def main : I64 := 42` from AST, compiles to binary,
# executes it, and verifies exit code 42.
```

### Architecture

| Component | Location | Description |
|-----------|----------|-------------|
| **Rust compiler** | `core/`, `cli/` | Parser, type checker, evaluator, constraint solver |
| **Self-hosted codegen** | `lang/codegen/` | Monad-in-Monad LLVM IR emitter + linker |
| **C runtime** | `lang/codegen/runtime.c` | Heap allocation, ref counting, constructor/string objects |
| **Standard library** | `init/`, `std/` | Prelude types, type classes, native-backed operations |
| **Self-hosted compiler** | `lang/` | Parser, evaluator, lowering pass (Monad-in-Monad) |

