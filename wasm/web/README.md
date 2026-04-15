# Monad Web REPL

A web-based REPL for the Monad programming language.

## Prerequisites

- [Rust](https://rustup.rs/)
- [wasm-pack](https://rustwasm.github.io/wasm-pack/)

## Building

```bash
wasm-pack build --target web
```

This will generate the WASM package in the `pkg/` directory.

## Running


### Example Programs

Click the example buttons to load and run sample programs:

- **Basic**: Simple variable definitions
- **Add**: Function definitions with multiple arguments
- **Factorial**: Recursive function
- **Fibonacci**: Another recursive example
- **Map list**: Higher-order functions
- **Fold**: List folding
