# The Standard Library

The standard library is split into two directories, and the split is a rule, not
a convention:

- **`init/`** — pure, portable core. Code that must work in any environment,
  including wasm and embedded targets. No OS-specific natives.
- **`std/`** — OS-specific implementations and genuine side effects.

`IO` the type lives in `init/`; `IO.println` lives in `std/`, because printing
touches the operating system.

Roughly 440 public definitions, 35 classes, and 132 instances across the two,
not counting their test modules.

## What Is Available Without Importing

Twelve modules load ambiently: the prelude, `id`, `io`, `number`, `math`,
`string`, `list`, the `init` hub, `std.path`, `std.io`, `std.process`, and the
`std` hub.

**Everything else needs an explicit import**, and the re-export hubs do not help:
`init/lib.mo` re-exports only `id`, `io`, `number`, `math`, `string`, `list`, and
`std/lib.mo` only `std.path`, `std.io`, `std.process`. So `init.foldable`,
`init.optics`, `init.meta`, and all of `std` beyond those three — `std.array`
included — are opt-in.

## `init/` — pure and portable

### `prelude` — ambient, not importable

The core types (`Bool`, `List`, `Option`, `Result`, `Pair`, `Nat`, `String`,
`Char`, `Unit`, `Void`, `Any`, `Vec`, `Eq`, `True`, the numeric primitives) and
the core classes (`Functor`, `Applicative`, `Monad`, `MonadState`, `MonadLift`,
`MonadLiftT`, `IndexedMonad`, `IndexedMonadState`, `IndexedMonadLift`,
`FromListLiteral`, `HAdd`, `Add`, `Sub`, `HMul`, `Div`, `Append`, `BEq`, `BOrd`,
`ToString`, `Hashable`).

`MonadState` and `IndexedMonadState` take the monad as their only parameter —
the state type is an implicit forall — so that instance resolution can key on a
concrete monad head. `examples/state_monad.mo` and `examples/indexed_monads.mo`
show both in use.

Functions: `Bool.not/and/or`, `List.is_empty/append/first/last/flatten/tail/map`,
`Option.get_or_default`, `Nat.add/sub/mul/eq`, `fun_apply`/`apply_fun`.

### `init` (`init/lib.mo`) — the hub

Re-exports the modules below, defines the `From` class, `BEq (Option A)`, and
rebinds `infix (+) := I64.add`.

### `init.number` / `init.math`

The numeric workhorse — about 600 lines of instances. For **each** of `I8`,
`I16`, `I32`, `I64`, `U8`, `U16`, `U32`, `U64`, `F32`, `F64`: `add`, `sub`,
`mul`, `div`, `beq`, `lt`, `gt`, `to_string` natives plus `Add`, `Sub`, `HMul`,
`Div`, `BEq`, `BOrd`, and `ToString` instances. Also `Hashable I64`/`U64`, `U32`
bitwise operations (`and`, `or`, `xor`, `shl`, `shr`), and width conversions.

### `init.string`

`String.beq`, `concat`, `concat_all`, `concat_list`, `length`, `is_empty`,
`slice`, `drop`, `get`, `get_char`, `to_lowercase`, `starts_with`, `ends_with`,
`contains`, `repeat`, `reverse`, `trim`, `find_last`, `to_list`/`from_list`,
`to_chars`/`from_chars` (**declared but not implemented** — these fail at run
time with `unknown native`), `hash`, plus `List.reverse` and `List.singleton`.
Instances: `BEq`, `BOrd`, `ToString`, `Add`, `Append`, `Hashable`.

### `init.list`

`List.get`. Most list operations are in the prelude or `std.list`.

### `init.id`

The identity monad: `Id A`, `Id.run`, and `Functor`/`Applicative`/`Monad`
instances. Useful as the trivial case when writing code generic over a monad.

### `init.foldable` — **not ambient**

`Semigroup` (`combine`), `Monoid` (`mempty`), `Foldable` (`foldr`, `foldl`),
`Traversable` (`traverse`). Instances for `List`, `Option`, and `String`.

### `init.optics` — **not ambient**

Van Laarhoven-style optics: the `Lens` and `Prism` types, with `lens`, `view`,
`set`, `over`, `preview`, `review`, `over_prism`, `set_prism`. `#[derive Lens]`
generates one lens per struct field.

### `init.meta` — **not ambient**

The reflection-as-data types (`TypeInfo`, `CtorInfo`, `FieldInfo`, `Expr`,
`MatchArm`, `Param`, `Decl`) that the macro system passes to derive backends.
See [Macros and Derive](./macros.md).

### `io`

`type IO A`, `def IO.pure`, and `instance Monad IO`. Nothing else — deliberately.
Construct with `IO.pure`; `IO.io` is the bare constructor and is meant to become
an implementation detail.

## `std/` — OS-specific

### `std.io` — ambient

`IO.println` and the filesystem: `read_file`, `write_file`, `file_exists`,
`is_dir`, `list_dir` (all `Path`-typed), plus `IO.get_env` and
`IO.current_time` (monotonic milliseconds — only differences are meaningful).

### `std.path` — ambient

A validated `Path` newtype: `Path.of` (the validating constructor),
`to_string`, `is_absolute`, `join`, `with_suffix`, `beq`, and `BEq Path`.

### `std.process` — ambient

`exec_cmd` and `process_id`.

### `std.list` — **not ambient**

`List.length`, `filter`, `any`, `all`, `sum`, `find_by`, `filter_map`,
`contains_by`, `intercalate`, `dedup_by`; instances `BEq (List A)` and
`Append (List A)`.

### `std.map` — **not ambient**

A real persistent-map implementation, not a stub:

- `BTreeMap K V` — AVL-balanced, with `insert`, `lookup`, `delete`, `fold`,
  `to_list`, and `instance [BOrd K] Map BTreeMap`
- `HashMap K V` — 256 buckets, with `instance [Hashable K, BOrd K] Map HashMap`
- `class Map (M := HashMap)` — `empty`, `insert`, `lookup`, `delete`

### `std.base` — **not ambient**

The `Ordering` type and the value classes: `Ord` (three-way `compare`),
`Semigroup`, `Monoid`, `Default`, `Enum`, `Bounded`, with instances for
`Ordering`, `String`, `Bool`, and every numeric width.

> Note that `Semigroup` and `Monoid` are declared **twice** — here and in
> `init.foldable` — with different method names. They are unrelated classes that
> share a name. Import one or the other, not both.

### `std.show` and `std.debug` — **not ambient**

`class Show A { def show : A -> String }` and
`class Debug A { def debug : A -> String }`. `Debug` is a Rust-style diagnostic
representation and quotes strings; `Show` is a display string. The prelude's
`ToString` is what the numeric types implement.

### `std.derive` — **not ambient**

`derive_beq_meta`, `derive_bord_meta`, `derive_debug_meta`, `derive_lens_meta`
and the `defmacro`s that wrap them. Must be imported for `#[derive ...]` to
resolve — see [Macros and Derive](./macros.md).

### `std.test` — **not ambient**

`Test.assert (condition : Bool) : Bool := condition`. That is the entire
assertion library — an identity function. There is no `assert_eq`, no failure
message, no matcher DSL. In practice most tests just return a `Bool`
expression directly, which is why `Test.assert` has only a handful of callers
across 1600 tests.

### `std.bench` — **not ambient**

`Bench.now`, `Bench.since`, `Bench.report`, `Bench.report_since` — all `IO`, over
the monotonic clock. Micro-benchmarks live in `bench/` and are deliberately
excluded from the ordinary test sweep.

### `std.array` — **not ambient**

`Array A`, a native-backed sequence with **O(1)** `length` and `get`, alongside a
mutable `ArrayBuilder A` for filling one under `IO`.

| Function | Cost | Notes |
|----------|------|-------|
| `Array.new n fill`, `Array.from_list`, `Array.empty` | O(n) | construction |
| `Array.length`, `Array.get` | O(1) | `get` returns `Option A`; out of range is `none`, never a crash |
| `Array.get_or a i fallback` | O(1) | total accessor |
| `Array.set a i v` | O(n) | persistent — copies, leaves `a` untouched, ignores an out-of-range index |
| `Array.push`, `Array.map`, `Array.foldl`, `Array.to_list` | O(n) | an `Array` is not a growable buffer |
| `Array.builder n fill`, `Array.set_in_place`, `Array.freeze` | see below | the mutable half, all under `IO` |

`Array.set_in_place` is O(1) in a compiled binary and O(n) under the bootstrap
host's interpreter, which copies on write. Both are correct; only the cost
differs, so a hot fill loop belongs in compiled code. `Array.freeze` deliberately
copies, so writing to the builder afterwards cannot disturb the frozen array.

`Array` implements **no classes at all** — `Array.map` and `Array.foldl` are
ordinary functions, not `Functor`/`Foldable` methods.

### `std.ansi` — **not ambient**

Terminal colours: the `Color`, `Style`, and `Modifier` types, with `red`,
`green`, `yellow`, `bold`, `dim`, `Ansi.fail`, `Ansi.pass`, `warn`, `colored`,
the `escape`/`color_fg_code`/`color_bg_code`/`style_code` builders, and an
environment-aware `colors_enabled` (`NO_COLOR` wins, then `FORCE_COLOR`, then
`TERM=dumb`).

> `Ansi.fail` and `Ansi.pass` were once bare `fail` and `pass`. The dotted names
> are load-bearing: a bare `fail` here captured `ParseResult.fail` elsewhere in
> the tree during module qualification and produced a segfault.

### `std.sha256` — **not ambient**

A complete SHA-256 implementation in pure Monad, with no natives, built on the
`U32` bitwise operations. A good demonstration that the numeric tower is real.

### `std.concurrent.fiber` / `std.concurrent.combine` — **not ambient**

Fibers and structured-concurrency combinators. Read
[Concurrency](./concurrency.md) before using them — the model is cooperative and
lazy, and they cannot be compiled at all.

## Gaps Worth Knowing About

- **Assertions.** `Test.assert` is an identity function; there is no equality
  assertion or failure message.
- **No `Iterator` class.** Iteration is `Foldable` or direct recursion.
- **No stdin.** `IO` can print and touch files, but cannot read a line.
- **`Traversable` has no instances at all** — the class is declared and nothing
  implements it.
- **Duplicate `Show`.** `std.list` declares a local `class Show A` alongside its
  import of `std.show`'s. Prefer `std.show`.
- **Three declared-but-unimplemented natives**: `eq_rec` (so `Eq.rec` cannot be
  called), `string_to_chars`, and `string_from_chars`.

See the [Maturity Matrix](./maturity.md) for the summary view.
