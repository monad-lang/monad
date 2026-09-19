# Compiling and Running

Monad compiles to native binaries through LLVM. The compiler is **written in
Monad**, lives in `lang/`, and compiles itself.

To run a program you compile it and execute the binary — `monad run` does both
in one step. There is also `monad eval`, a built-in interpreter, but only eight
pure natives are wired into it, so it is a tool for arithmetic-and-strings
programs rather than a way to run real ones.

## Getting a Compiler

The compiler is written in the language it compiles, so the first one has to
come from somewhere else. That is what the Rust [bootstrap
host](./bootstrap-host.md) is for:

```bash
cargo build --release
cargo run --release -- run lang/main.mo compile lang/main.mo -o "$PWD/monad"
```

That produces `monad`, a native binary that needs nothing else. Everything below
uses it.

The absolute `-o` is not decoration. A relative output name is resolved against
the compiler's default output directory, `/tmp/monad_out_<pid>` — see
[Where the binary lands](#where-the-binary-lands).

You will also need `llc`, `clang`, and the Boehm GC development files on the
system — `devenv shell` provides all three.

### Or install a nightly

Every push to `main` publishes a prerelease, and `scripts/monadup` installs one:

```bash
curl -fsSL https://raw.githubusercontent.com/monad-lang/monad/main/scripts/monadup -o monadup
chmod +x monadup
./monadup self-install
export PATH="$HOME/.monad/bin:$PATH"
monadup default       # install the latest nightly and make it active
monad version
```

`monadup list` / `use <tag>` / `update` / `uninstall <tag>` manage the installed
set under `~/.monad`. It needs `curl` and either `jq` or `python3`.

> **The nightly is built inside the Nix devenv** and links against store paths,
> so on a machine without those it will not run — `monadup` says so rather than
> leaving you to discover it. Until that is fixed, building from source is the
> portable route.

There is one artifact, `monad-nightly-x86_64-linux`: Linux x86_64 only.

## Your First Program

```monad
use io {}
open IO {println}

def main (args : List String) : IO Unit := println "Hello, World!"
```

```bash
monad run hello.mo
```

```
Hello, World!
```

Or compile it and keep the binary — with an absolute output path, for the reason
just above:

```bash
monad compile hello.mo -o "$PWD/hello"
./hello
```

## The Commands

```text
monad compile <path> [name] [--output/-o <name>] [--verbose/-v] [--debug/-g] [--release]
        Parse, type-check and compile a .mo source file to a native binary.

monad run <path> [--verbose/-v] [--debug/-g] [--release]
        Compile and then execute. The binary is always called `run_out`, so
        there is no -o; the program's exit code becomes monad's.

monad eval <path> [--verbose/-v]
        Evaluate with the built-in interpreter. Pure programs only.

monad pretty <path>
        Parse and pretty-print a .mo source file.

monad check <path>... [--verbose/-v]
        Parse and type-check; no execution.
        Any <path> that is a directory is expanded recursively to its *.mo files.

monad test [<path>...] [--workspace/-w] [--verbose/-v]
        Compile each file's own #[test] defs into a native binary and run it.
        With no <path>, tests the mote containing the working directory;
        --workspace tests every mote in the enclosing workspace.
        A file with no #[test]s is skipped rather than failed. A file that
        defines its own main is fine: that main is renamed out of the way
        and the generated test driver becomes the entry point.

monad version
        Print the git commit this binary was built from.
```

Running `monad` with no arguments prints this usage.

Flags are position-independent — `monad compile -v hello.mo` and
`monad compile hello.mo -v` are the same command. `--output`/`-o` takes its value
as a **separate argument**: `--output=NAME` is not recognised.

`monad test` with no paths enumerates motes, so it covers only directories that
have a `mote.toml` — `examples/` has none, and its files are reached by naming
them. Run mote- and workspace-wide invocations **from the workspace root**:
dependency resolution is relative to the working directory, so from inside
`llvm/` the `std` and `init` motes do not resolve.

> **`monad test` reads each driver's failure count from a result file the
> driver itself writes**, not from its exit code, so a file's test count is no
> longer capped at 255. A handful of files still cannot be run self-hosted at
> all (the async runtime, `#[derive]`, and a few checker/codegen bugs) — those
> are listed in `cli/src/test_gaps.mo`, reported as `GAP`, and covered by the
> [bootstrap host](./bootstrap-host.md) in CI instead.

> **`monad eval` is not a general interpreter.** Eight natives are wired into it
> — `i64_add`, `i64_sub`, `i64_mul`, `i64_eq`, `i64_lt`, `string_concat`,
> `string_eq`, `string_to_lowercase` — and everything else, `println` included,
> stops with `unknown native`. It evaluates the file's `main` and prints
> `Eval result <value>`. Use `monad run` for a real program.

### Where the binary lands

`compile` and `run` resolve the output name against a default output directory,
`/tmp/monad_out_<pid>` — the pid is there so parallel invocations cannot collide.
An **absolute** output name replaces that directory outright; a relative one is
placed inside it. So:

```bash
monad compile hello.mo -o hello          # -> /tmp/monad_out_1234/hello
monad compile hello.mo -o "$PWD/hello"   # -> ./hello
```

This surprises everyone once. When you want the binary in the working directory,
say so with an absolute path.

### Debug info and `--release`

DWARF debug info is emitted **by default**, with a distinct source location per
term. `--release` turns it off; an explicit `--debug`/`-g` turns it back on and
wins over `--release` in either order.

The cost of debug info is real: every module is re-parsed with source positions
before codegen. Pass `--release` for a build you are not going to debug — the
nightly and the CI bootstrap both do.

### `--verbose`

`--verbose`/`-v` is accepted by every command that does work. It prints each
module as it loads (before loading it, so a hang names the culprit), one line per
pipeline stage, and the elapsed time for each:

```text
  loading module: lang.parser
-> stage: load + elaborate modules
   load + elaborate modules 1843ms
-> stage: typecheck target
```

Success and failure lines print with or without it. Colour comes from
`std.ansi`, which honours `NO_COLOR` (always off), then `FORCE_COLOR` (on), then
`TERM=dumb` (off). There is no tty check, so piped output is coloured unless you
set `NO_COLOR=1`.

### `monad version`

Prints the git commit the binary was built from. The hash is baked in **at link
time by the compiler that built it**, read from the working directory it was
invoked in — build outside a git checkout and you get `unknown`.

## `main` and Exit Codes

`main` may return `IO Unit`, or `I64` — in which case it becomes the process
exit code:

```monad,ignore
def main : I64 := 42
```

```bash
monad compile main.mo -o "$PWD/main" && ./main; echo $?   # 42
```

It may also take the command line, which the C runtime builds from `argc`/`argv`:

```monad,ignore
def main (args : List String) : I64 := 0
```

## What the Pipeline Does

1. Parse and type-check the source — the same front end as `check`
2. Lower to the codegen IR and emit LLVM IR
3. Run `llc` to produce an object file
4. Link with `clang`, against the C runtime and `-lgc`

## Bootstrapping

Once you have a `monad` binary, it can build its own successor:

```bash
monad compile lang/main.mo -o "$PWD/monad-next" --release
./monad-next check lang/main.mo
```

CI runs exactly this on every push, and the second step is the one with teeth:
`compile` succeeding only says `llc` and `clang` were happy with the emitted IR.
Making the result type-check the compiler's own source — the largest input in the
tree — exercises the whole front end.

The bootstrap has reached a fixpoint: the compiler compiles itself, that binary
compiles itself again, and the output is identical.

## Memory

Compiled binaries use the **Boehm conservative garbage collector**, and this is
explicitly a stopgap.

Every heap object carries a header with a refcount, and `monad_retain` /
`monad_release` exist — but codegen never emits calls to them, so before the GC
was added nothing was ever freed. Measured on `check lang/main.mo`, that meant
5.99 GiB allocated of which 98.24% was garbage, and compiling `lang/main.mo` was
OOM-killed at 29.7 GB.

So `monad_alloc` calls `GC_malloc`, string buffers go through `GC_malloc_atomic`
(so the collector does not scan text bytes and mistake them for pointers), and
`monad_release` deliberately does *not* free — that would corrupt the Boehm heap.
The refcount field is currently vestigial.

The intended replacement is for the compiler to track ownership through the
[linear and affine multiplicities](./linear-types.md) the language is designed
around, at which point the allocator gets real frees and the GC dependency goes
away. That is blocked on multiplicity checking existing at all.

## Fail-Fast Gates

Before emitting anything, the backend runs four validation passes over the
reachable declarations. Each exists because the silent miscompile it catches
actually shipped once:

| Gate | Catches |
|------|---------|
| unwired natives | a bodyless `#[native X]` where `X` is wired nowhere — would compile to a "return Unit" stub and SIGSEGV at run time |
| undesugared struct literals | a struct literal elaboration never desugared — it used to compile to a void placeholder; today codegen aborts in a deliberately named function instead |
| symbol collisions | two definitions sharing an LLVM symbol — one is silently dropped and its callers re-pointed at the other |
| undefined symbols | a call to a symbol nothing defines — otherwise surfaces as `llc: undefined value` at the end of a 15–25 minute self-compile, naming one symbol and no call site |

All four run only on reachable declarations, so a problem in dead code cannot
block a build that never touches it.

## Native Coverage

There are 134 natives declared across `init/` and `std/`. The backend wires `I64` arithmetic and
comparison, string operations, `print_str`, the file and directory natives,
`get_env`, `current_time`, `process_id`, and `exec_cmd`.

Not wired: the entire concurrency surface — see
[Concurrency](./concurrency.md). A program that reaches one of those fails to
compile with a clear message rather than producing a broken binary.

Three natives are declared but unimplemented in both implementations —
`eq_rec`, `string_to_chars`, `string_from_chars` — and fail at run time with
`unknown native`.

A few natives are not written in C at all: `lang/codegen/runtime.mo` emits LLVM
IR directly for thirteen simple operations.

## Known Rough Edges

- Compiling a large program is slow — a full self-compile takes minutes.
- Deep recursion in compiled code can exhaust the stack; raise it with
  `ulimit -s` when compiling large inputs.
- `monad eval` reaches only eight natives (above), so it is not a substitute for
  `monad run`.
- `monad test` compiles one driver binary per test file and runs it; a file
  whose tests reach a native the backend does not wire (the concurrency ones
  especially) is skipped with that reason rather than run.
- A relative `-o` lands in `/tmp/monad_out_<pid>` (above).
- A struct literal the checker cannot give a type to — most often one written
  directly under `return` — is rejected with *"cannot infer struct type"*.
  Annotate it (`{ … : Point }`) or bind it to an annotated local first.

See the [Maturity Matrix](./maturity.md).
