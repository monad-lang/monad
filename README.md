# Monad

> [!WARNING]
> Monad is in **alpha release** and under heavy development. Many features are
> not implemented yet and are not tested properly. Expect breaking changes,
> incomplete functionality, and potential bugs.
>
> The [Maturity Matrix](https://monad-lang.org/maturity.html) says, area by
> area, what actually works today.

A purely functional, dependently typed systems programming language that
compiles to native binaries through LLVM. The compiler is written in Monad
and compiles itself.

Homepage: **[monad-lang.org](https://monad-lang.org)**

## Why Monad?

- **Dependent types** — types can depend on values, with a `Prop` universe
  and propositional equality for compile-time proofs
- **Type classes** — ad-hoc polymorphism with automatic instance resolution
- **Termination checking** — recursive definitions must be structurally
  decreasing unless you opt out
- **Hygienic macros** — `defmacro`, `quote`, and compile-time reflection;
  `#[derive]` is implemented in Monad, not in the compiler
- **LLVM native** — programs compile to fast native binaries, no VM
- **Self-hosting** — the compiler in `lang/` is written in Monad and compiles
  itself, reaching a fixpoint where the binary builds its own successor

## Install

```bash
curl -fsSL https://monad-lang.org/install | bash
export PATH="$HOME/.monad/bin:$PATH"
monadup default       # install the latest nightly and make it active
monadup doctor        # check the compiler and the LLVM/GC build prerequisites
monad version
```

`monadup` is a Monad-written binary. It manages nightly builds under
`~/.monad`; use `monadup list`, `monadup use <tag>`, `monadup update`, and
`monadup uninstall <tag>` to manage installed versions. `monadup env` prints
the resolved environment, `monadup doctor --json` is the machine-readable
health report an agent can act on, and `monadup new hello` scaffolds a project.

Nightlies are published for `x86_64-linux` and `aarch64-darwin` (built
natively), plus cross-built `aarch64-linux` and experimental `riscv64-linux`.
The Linux binaries are fully static and the macOS one links only libSystem;
compiling a Monad program still needs `llc`, `clang` and Boehm GC on the
machine, which `monadup doctor` checks for you.

### Build from source

```bash
git clone https://tangled.org/monad-lang.org/monad
cd monad
devenv shell          # provides Rust, clang, llc, Boehm GC, mdbook
cargo build --release
cargo run --release -- run cli/src/main.mo build cli/src/main.mo -o "$PWD/monad" --release
```

The compiler the flake builds is published to the project's Cachix cache. A
`nix build --accept-flake-config .#monad` reads it with no setup; `cachix use
monad-lang` opts in permanently by adding the substituter to your `nix.conf`, so
an unchanged rung is a substitution rather than a ~20 minute interpretation.

The `-o` must be **absolute**: a relative output name lands in the compiler's
scratch directory. The trailing `--release` turns off DWARF debug info, which
is on by default.

## Quick start

```monad,check
use std::io {}
open IO {println}

def main (args : List String) : IO Unit := println "Hello, World!"
```

Save that as `hello.mo`, then:

```bash
monad run hello.mo
```

`monad run` compiles and executes in one step — a Monad program is always a
native binary. To keep the binary, use `monad build` with an absolute output
path:

```bash
monad build hello.mo -o "$PWD/hello"
./hello
```

## Commands

```text
monad build [<path>] [name] [--bin <name>] [--output/-o <name>] [--verbose/-v] [--debug/-g] [--release]
        Parse, type-check and compile a source file, or a mote's [[bin]] target,
        to a native binary. --bin picks one of several.

monad install [<path>] [-o <name>] [--bin <name>] [--target <triple>] [--verbose/-v] [--no-cache]
        Build a RELEASE binary and install it to $MONAD_HOME/bin (default
        $HOME/.monad/bin), replacing the destination atomically.

monad run <path> [--verbose/-v] [--debug/-g] [--release]
        Compile and execute. The program's exit code becomes monad's.

monad eval <path> [--verbose/-v]
        Evaluate with the built-in interpreter. Pure programs only.

monad repl
        Interactive loop over the same interpreter; expressions print
        value : type and declarations/use persist in a session.

monad check [<path>...] [--workspace/-w] [--verbose/-v]
        Parse and type-check; no execution.

monad test [<path>...] [--workspace/-w] [--verbose/-v]
        Compile each file's #[test] defs and run them.

monad pretty <path>
        Parse and pretty-print a .mo source file.

monad version
        Print the git commit this binary was built from.
```

Running `monad` with no arguments prints usage. Directory arguments are
expanded recursively; with no path, commands operate on the mote containing
the working directory, and `--workspace` covers every mote in the workspace.

## Community

| Platform | Link |
|----------|------|
| Zulip (main forum) | https://monad-lang.zulipchat.com/ |
| Tangled (primary repo) | https://tangled.org/monad-lang.org/monad |
| GitHub (releases) | https://github.com/monad-lang/monad |
| Reddit | https://www.reddit.com/r/monad_lang/ |
| Discord | https://discord.gg/XDKk7PPH |

## Documentation

The full documentation lives at **[monad-lang.org](https://monad-lang.org)** —
built with mdBook from `docs/src/`, with every code block type-checked by CI.

Key pages:
- [Introduction](https://monad-lang.org/introduction.html)
- [Getting Started](https://monad-lang.org/getting-started.html)
- [Maturity Matrix](https://monad-lang.org/maturity.html)
- [Compiling and Running](https://monad-lang.org/compiling.html)
- [Reference](https://monad-lang.org/reference.html)

## License

Apache 2.0
