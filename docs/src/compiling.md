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
cargo run --release -- run cli/src/main.mo build cli/src/main.mo -o "$PWD/monad"
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
set under `~/.monad`. It needs `curl`, `tar` and either `jq` or `python3`.

> **The nightly is built by the Nix flake** and links against store paths, so on
> a machine without those it will not run — `monadup` says so rather than leaving
> you to discover it. Until that is fixed, building from source is the portable
> route.

An install directory holds more than the compiler:

```
~/.monad/downloads/<tag>/
  monad-nightly-<platform>     the compiler
  commit.txt                   the commit it was built from
  init/  std/  llvm/  runtime/ the mote sources
  mote.toml                    those four, as a workspace
```

Those motes are what let you use the compiler on a program of your own —
`use std::map` and the C runtime both resolve out of that directory. Without
them, only a checkout of the compiler repository can compile anything. Nightlies
published before the sources asset existed install the binary alone and say so;
re-running `monadup install` adds the sources once a release ships them.

`MONAD_ROOT` points the compiler at a different set of sources, for a root that
is not a monadup install (an unpacked copy, or a checkout):

```bash
MONAD_ROOT=/path/to/tree-with-init-std-runtime monad check
```

Two artifacts, per platform: `monad-nightly-<platform>` (the compiler) and
`monad-src-<platform>.tar.gz` (the sources above). `x86_64-linux` and
`aarch64-darwin` are built and verified on the platform they are for;
`aarch64-linux` and `riscv64-linux` are cross-built from `x86_64-linux` and
verified under QEMU, and riscv64 is **experimental**. `monadup` reads the
machine with `uname -sm` and installs that pair, falling back to `x86_64-linux`
on a platform no release has published — which is every tag older than the
platform.

## Your First Program

```monad
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
monad build hello.mo -o "$PWD/hello"
./hello
```

## The Commands

```text
monad build [<path>] [name] [--bin <name>] [--output/-o <name>] [--target <triple>] [--verbose/-v] [--debug/-g] [--release] [--no-cache]
        Parse, type-check and compile a .mo source file to a native binary.
        <path> may also be a mote DIRECTORY, in which case one of its [[bin]]
        targets is built: `monad build cli` builds cli/src/main.mo as `monad`,
        the name that mote's [[bin]] declares. A mote that declares no [[bin]]
        table has one target anyway -- src/main.mo, named after the mote --
        and a library mote that declares none and has no src/main.mo is
        refused rather than guessed at.
        `--bin <name>` picks one when several of a mote's [[bin]] targets
        exist on disk -- which is what the refusal above counts, rather than
        what the manifest declares.
        With NO <path>, builds the mote containing the working directory --
        the same default `check` and `test` have. `monad build` and
        `monad build .` are one code path.
        `--target <triple>` builds for another target. The triple is the
        spelling `monad print-targets` lists, which is the spelling the
        emitter writes; a target whose ARCHITECTURE this llc does not register
        is rejected by name rather than by a backend error further down. The
        target is part of the build cache key, so one source built for two
        targets keeps two entries.
        It is not a C-compiler redirect. `runtime.c` and the link go through
        `clang` by bare name, so building for another target needs THAT
        target's `clang` first on PATH -- which is what the nightly's cross
        legs install as a shim. With the host's clang the failure is at the
        link, on the object it is handed (`file format not recognized`), and
        says nothing about what the target itself is missing.

        This verb was called `monad compile` until 2026-09-29. There is no
        alias: two verbs that both produce a binary differ only in which one
        you remember.

monad run <path> [--verbose/-v] [--debug/-g] [--release]
        Compile and then execute. The binary is always called `run_out`, so
        there is no -o; the program's exit code becomes monad's.

monad eval <path> [--verbose/-v]
        Evaluate with the built-in interpreter. Pure programs only.

monad pretty <path>
        Parse and pretty-print a .mo source file.

monad check [<path>...] [--workspace/-w] [--verbose/-v] [--no-cache]
        Parse and type-check; no execution.
        Any <path> that is a directory is expanded recursively to its *.mo files.
        With no <path>, checks the mote containing the working directory;
        --workspace checks every mote in the enclosing workspace.
        --no-cache (or MONAD_NO_CACHE) skips the cache; a single-file run always does.
        With no <path> and no mote above the working directory it prints why
        and exits 1, rather than reporting a pass for having checked nothing.

monad test [<path>...] [--workspace/-w] [--verbose/-v]
        Compile each file's own #[test] defs into a native binary and run it.
        Any <path> that is a directory is expanded recursively to its *.mo files.
        With no <path>, tests the mote containing the working directory;
        --workspace tests every mote in the enclosing workspace.
        A file with no #[test]s is skipped rather than failed. A file that
        defines its own main is fine: that main is renamed out of the way
        and the generated test driver becomes the entry point.

monad print-targets
        List the triples --target accepts, and what this llc can build for.
        Each is the spelling the emitter writes; `(llc ...)` adds the argv when
        llc needs more than the triple to select the target, which today means
        riscv64. Then this machine's own target, which is what no --target
        means, and llc's whole registered architecture list.

monad version
        Print the git commit this binary was built from.
```

Running `monad` with no arguments prints this usage.

Flags are position-independent — `monad build -v hello.mo` and
`monad build hello.mo -v` are the same command. `--output`/`-o` and `--target`
take their value as a **separate argument**: `--output=NAME` and
`--target=<triple>` are not recognised.

`monad test` with no paths covers the mote containing the working directory, so
it enumerates that mote's sources; `--workspace` covers every member. Pass
explicit paths for anything else. With no paths and no mote above the working
directory it says so and exits 1, exactly as `check` does — there is nothing to
test, and reporting a pass for it would read as one. Resolution keys off the mote doing the `use`,
so an invocation from inside a mote finds its own `init`/`std` dependencies —
there is no need to run it from the workspace root.

> **`monad test` reads each driver's failure count from a result file the
> driver itself writes**, not from its exit code, so a file's test count is no
> longer capped at 255. Every file in the corpus runs self-hosted; CI's sweep
> carries no exclusion list.

> **`monad eval` is not a general interpreter.** Eight natives are wired into it
> — `i64_add`, `i64_sub`, `i64_mul`, `i64_eq`, `i64_lt`, `string_concat`,
> `string_eq`, `string_to_lowercase` — and everything else, `println` included,
> stops with `unknown native`. It evaluates the file's `main` and prints
> `Eval result <value>`. Use `monad run` for a real program.

### Where the binary lands

`build` resolves the output name against the **target directory**: the nearest
`[build] target-dir` in a `.monad/config.toml` above the source, else plain
`target/`. `MONAD_TARGET_DIR` overrides that, and `--target-dir` overrides
both. The setting lives in the **tool's** config rather than in a mote's
`mote.toml`: where output goes is not a property of the thing being built, and
a script-mode file in no mote at all still needs an answer. This repository
holds two toolchains, so it names their output apart: cargo's is `target-rust/`
and monad's is `target-monad/` — they must not eat each other, because a
`cargo clean` must not delete a monad binary.

Debug info is on by default, so a plain build is a `debug` build:

```bash
monad build hello.mo -o hello            # -> target-monad/debug/hello
monad build hello.mo -o hello --release  # -> target-monad/release/hello
monad build hello.mo -o "$PWD/hello"     # -> ./hello
```

An **absolute** output name replaces the directory outright; a relative one —
including one with slashes in it — is placed inside it, because `-o` is a NAME,
not a path. A relative name that looks like a path is nested rather than
rejected:

```bash
monad build hello.mo -o sub/hello        # -> target-monad/debug/sub/hello
```

This surprises everyone once. When you want the binary somewhere specific, say
so with an absolute path.

`monad run` is the exception: it compiles to `/tmp/monad_out_<pid>`, the pid
being there so parallel invocations cannot collide.

### The build cache

Artifacts are **input-addressed**. `build` hashes the source file's own bytes,
its mote's whole declared closure, the compiler binary itself, the profile and
the target triple, and if the store already holds a binary under that hash it
copies it out instead of compiling — so rebuilding an unchanged tree is a file
copy, not a build, and `cached: <dest> (<hash>)` is what a hit prints.

The file's bytes are in the key because the closure alone does not name the
file. A `.mo` with no `mote.toml` above it roots at the directory it sits in, so
`one.mo` and `two.mo` side by side share a root and a closure digest — keyed on
that alone they shared an entry, and building `two.mo` after `one.mo` printed
`cached:` and handed back `one`'s binary. The directory is still hashed as well,
since a file's siblings are reachable from it and its `#![mote {…}]` dependency
list is a property of the file, not of the tree above it.

The key is the whole name: nothing you type with `-o` is part of it. Keeping that
true took a fix upstream of the cache. The intermediate `.ll` used to be named
after `-o`, and `llc` records its input file's name in the object it emits, so
two builds of one unchanged source under two output names differed by a byte.
The IR is now named by the cache key and kept in the store
(`<target-dir>/store/<hash>.ll`), which makes the artifact a function of the key
alone; the `.ll` your `-o` implies is still written beside the binary as a
convenience copy, for anyone reading the IR by hand. A cache hit writes it too —
from the copy in the store, and only when the bytes there differ — so a build
leaves the same two files behind whether or not it had to compile.

`check` caches the same way, one entry per file, under
`<target-dir>/check/<hash>`: a corpus check that takes minutes cold takes about
a second warm, and a hit replays the recorded output byte for byte.

Two properties are worth knowing before you trust it. The key covers the
compiler as well, so editing the compiler invalidates everything it built —
and where an input cannot be determined the cache turns itself **off** rather
than answering from a weaker key, because a stale binary is worse than a slow
build. On Darwin that is every build: one of the key's inputs is the running
compiler's own bytes, read from `/proc/<pid>/exe`, and a platform with no procfs
has no such input at all. `monad store` and `monad gc` are inert there for the
same reason. And the key is coarse by direction, not by accident: it covers the
file's entire declared closure, so a one-line edit can re-check more files than
it changed. Anything that needs the real work to happen — a gate that inspects
the emitted IR, say — says so with one of two switches, which mean the same
thing: nothing is read, and nothing is written.

```bash
monad build hello.mo --no-cache
MONAD_NO_CACHE=1 monad check init std
```

`--verbose` on `check` turns the cache off too: its trace is a record of what
the checker did, and a replayed entry has no trace to show.

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
monad build main.mo -o "$PWD/main" && ./main; echo $?   # 42
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
monad build cli/src/main.mo -o "$PWD/monad-next" --release
./monad-next check cli/src/main.mo
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
was added nothing was ever freed. Measured on `check cli/src/main.mo`, that meant
5.99 GiB allocated of which 98.24% was garbage, and compiling `cli/src/main.mo`
was OOM-killed at 29.7 GB.

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

The **undefined symbols** gate is a backstop, and one case used to reach it
that should never have: a class-method call naming a method its class does not
declare (`Map.get` — `class Map` declares `empty`/`insert`/`lookup`/`delete`).
The resolver rewrites a class-method reference to a mangled name built from the
class's *declared* method list, so such a call produced a name nothing emits and
landed here as `call to undefined symbol(s): std.map::Map_BTreeMap_get` — a
symbol and no call site. The gate's own reasoning assumes a *successful*
resolution implies the definition exists; `class_method_ref`
(`lang/src/scope.mo`) now requires the qualifier's class to declare the method,
so that assumption holds and the call is rejected during typecheck instead,
naming the reference exactly as written (`unknown variable 'Map.get'`).

## Native Coverage

There are 165 natives declared across `init/` and `std/`. The backend wires `I64` arithmetic and
comparison, string operations, `print_str`, the file and directory natives,
`get_env`, `current_time`, `process_id`, `exec_cmd`, the nine `tcp_*` socket
natives, and `std.bytebuf`'s `ByteBuf`.

Not wired: the entire concurrency surface — see
[Concurrency](./concurrency.md). A program that reaches one of those fails to
compile with a clear message rather than producing a broken binary.

The `tcp_*` natives are wired here and nowhere else. The Rust bootstrap host has
no TCP implementation, so a socket test cannot run under `cargo run -- test`;
`motes/moon` and `motes/moose` are exercised by the self-hosted runner.

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
