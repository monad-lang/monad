# Try Monad in the Browser

<https://monad-lang.org/try> evaluates a Monad program entirely in your
browser. The evaluator is the self-hosted compiler's own parser, scope
builder, typechecker, lowerer and interpreter, compiled to WebAssembly and
running in a Web Worker; the page is an Oak application.

It is **experimental and unoptimised**: the lowered program is interpreted
directly, with no optimisation passes and no native code, so it runs far
slower than a compiled binary. `/try` is a way to try the language, not a
way to measure it.

## The rule: define `main`

The scratchpad holds one complete module. The value of `main` is what the
page shows, together with its type — the same convention as `monad repl`
(`eval::run`, the shared evaluator, renders both):

```monad
def square (n : I64) : I64 := I64.mul n n

def main : I64 := square 12
```

The result pane shows `144 : I64`.

`main` must take no parameters. A module with no `main` is a type error, not
an empty result.

The prelude is not compiled into the evaluator. The page fetches the real
`init/src/*.mo` files the site serves (`sources.json` lists them) and hands
their text to the engine, so a program is checked against the same files the
repository ships — every non-test `init` module is reachable with
`use init::…`, not just the ones a hand-picked bundle carried.

The engine is `motes/try_engine` over `eval::run` — the same
typecheck/elaborate/lower/evaluate recipe `monad eval` and `monad repl`
use; only the loader (served sources instead of the filesystem) and the
policy (fuel/depth, clipping) differ.

Because those sources are assembled in memory, the /try engine skips the
compiler's module-load *gates* (manifest declarations and `use`
completeness): a package-private `init` helper can resolve here that
`monad check` would reject. Stick to the documented prelude API.

## What is available

The **ambient prelude** only: the modules `init` re-exports (I64/String/
List/Option/Bool/Pair/Result, type classes and their instances, `String`
and `List` helpers) plus `prelude` itself. You can define your own types,
structs, classes, instances and infix operators.

```monad
type Shape {
    circle (r : I64),
    square (s : I64),
}

def area (s : Shape) : I64 :=
    match s {
        circle r => I64.mul 3 (I64.mul r r),
        square x => I64.mul x x,
    }

def main : I64 := area (Shape.circle 2)
```

There is no filesystem, no network and no `use` of other motes. `use init::…`
resolves; `use std::…` is rejected with a message.

## What is not available (yet)

- **IO and effects.** Only pure evaluation exists, so `main` is a value, not
  an `IO` action. `IO.pure` cannot be run.
- **Floats.** Float literals are rejected by the evaluator's IR today
  (`monad build` compiles them; the IR interpreter does not yet).
- **Imports of other motes**, including `std`.
- **A long-lived session.** Each Run is a fresh worker and a fresh engine
  instance, so nothing accumulates — and a runaway program cannot leak
  memory past a reload.
- **Large results are clipped.** A value or error longer than 8 KiB is
  truncated at a character boundary and ends with `…`.

## Limits and safety

- **Step budget.** The interpreter stops after 2,000,000 evaluation steps
  with a "step limit" result.
- **Wall clock.** Loading the engine and evaluating each get a 30-second
  backstop; past it the worker is terminated and the run reports a timeout.
- **Call depth.** The interpreter stops at 200 nested user calls with a
  clear message. The step budget bounds *steps*, not depth, and the
  interpreter's codegen frames are large (~120 KiB of wasm stack per call),
  so the counter — not the stack — is what bounds recursion.
- **Cancel.** The engine runs in a Web Worker; Cancel terminates it
  immediately, even if the front end is still parsing.
- **Nothing leaves the browser.** The source is not sent anywhere; the
  wasm modules and the prelude sources are static files fetched from this
  site.
- **Memory.** One run grows the engine's wasm memory to roughly 170 MB: the
  web allocator never frees, and elaborating the prelude is the bulk of it.
  Each Run uses a fresh worker instance, and terminating it returns the
  memory to the browser.

## Ctrl/Cmd+Enter

Runs the current program. The editor keeps your caret and undo history
while you type; loading an example replaces the editor contents.

## Running the page locally

`devenv`'s `docs-serve` builds the two wasm modules and stages the served
prelude sources before Zola starts. If you serve the site another way, run
`scripts/build-try.sh` first and restart your server afterwards:
`docs/site/static/try/` holds a tracked page shell next to generated
wasm/host files, `sources.json` and the `sources/` tree, and a stale mix (a
new `worker.js` with an old `web_runtime.js`, or an engine built before a
module was added to `init/src`) makes every run fail to load.
