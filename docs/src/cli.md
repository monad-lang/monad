# Command-line reference

`monad --help` and `monad <command> --help` print this reference, generated
from the command declaration in `cli/src/cli.mo`. `monad help` prints the
same top-level text.

The parser is the `clap` mote's `#[derive Cli]`, so `--help`/`-h` and
`--version`/`-V` work at every level, `--long=value` is accepted, and an
unknown command or flag is a usage error on stderr with exit code 2 (an
argv that names no command also exits 2, with the usage screen).

```text
Monad is in alpha mode and under heavy development.
Expect breaking changes, bugs, and incomplete features.

Usage: monad build [<path>] [name] [--bin <name>] [--output/-o <name>] [--target <triple>] [--verbose/-v] [--debug/-g] [--release] [--no-cache]
         Compile a .mo source file, or a mote, to a native binary
         <path> may be a mote DIRECTORY, in which case its [[bin]] target is built
           (`monad build cli` builds cli/src/main.mo as `monad`)
         --bin <name> picks one when several [[bin]] targets exist on disk
           (a mote declares none, but builds `src/main.mo` as its own name, when
            `src/main.mo` exists and no [[bin]] table does)
         With no <path>, builds the mote containing the working directory
         --verbose/-v prints each module as it loads and one line per pipeline stage
         --debug/-g emits DWARF debug info (one source location per top-level def)
         --target <triple> builds for another target (`--target=<triple>` also parses)
           `monad print-targets` lists the spellings this compiler has measured
         --no-cache (or MONAD_NO_CACHE) compiles for real, reading and writing no store entry
       monad install [<path>] [-o <name>] [--bin <name>] [--target <triple>] [--verbose/-v] [--no-cache]
         Build a RELEASE binary (no debug info) and install it to $MONAD_HOME/bin/<name>
         <path> is build's: a mote directory (its [[bin]] name) or a .mo file (then -o names it)
         MONAD_HOME defaults to $HOME/.monad; the destination is replaced atomically, symlinks included
       monad run <path> [--verbose/-v] [--debug/-g] [--release] [--] [args...]  Compile and execute a .mo source file
         <path> may be a mote DIRECTORY (its [[bin]] target is built and run), like build's;
         the binary lands where build would put it and the second identical run prints `cached:`
         Everything after <path> is the compiled program's own argv. Flag-like arguments
         (`-x`, `--weird`) must follow `--`; plain words are forwarded without it.
       monad eval <path> [--verbose/-v]  Evaluate a .mo source file using the built-in interpreter (pure programs only)
       monad repl  Interactive read-eval-print loop (pure programs only)
         Expressions print `value : type`; declarations (def/type/struct/class/instance/use/open) persist
         `:help`, `:quit`, `:reset`, `:type <expr>`; a `def` body may continue on the next line
         Prompts go to stderr; results and diagnostics to stdout; EOF or :quit leaves
       monad pretty <path>  Parse and pretty print a .mo source file
       monad check [<path>...] [--workspace/-w] [--verbose/-v] [--no-cache]  Parse and typecheck .mo source files (no execution)
         Any <path> that's a directory is recursively expanded to its *.mo files
         With no <path>, checks the mote containing the working directory
         --workspace/-w checks every mote in the enclosing workspace
           (only directories that ARE motes: examples/ has no manifest)
         --verbose/-v prints a per-declaration progress trace while checking
         Results are cached under <target-dir>/check for multi-file runs, keyed on
           the file, its mote's whole declared closure, and the running compiler
         --no-cache (or MONAD_NO_CACHE) skips the cache; a single-file run always does
         The affine usage rule always runs: a binder used twice without a Copy
           instance is an error. A mote can opt into warnings for migration with
           `[affine] mode = "warn"` in its mote.toml; there is no off switch
       monad test [<path>...] [--workspace/-w] [--verbose/-v] [--jobs/-j <N>]  Compile and run each file's own #[test] defs as a native binary
         Any <path> that's a directory is recursively expanded to its *.mo files
         With no <path>, tests the mote containing the working directory
         --workspace/-w tests every mote in the enclosing workspace
           (only directories that ARE motes: examples/ has no manifest)
         --verbose/-v prints per-file timing and module-cache statistics
         --jobs/-j <N> keeps up to N files' compile-link-run tails in flight (default 4);
           --jobs 1 is the serial runner. Under the built-in interpreter the tails
           never overlap (forkIO is deferred to the await there), but the run is correct
         A file with no #[test]s is skipped, not failed
       monad clean [--all] [--target-dir <dir>]  Remove build output, keeping the store
         Removes every output directory under <target-dir> (the profile directories)
         --all removes <target-dir> itself, the store included
       monad gc [<path>...] [--workspace/-w] [--apply] [--target-dir <dir>]  Remove store entries the named files cannot reach
         Dry run by default; --apply removes them. Takes the same <path> forms as check
         Refuses to remove ANYTHING when it cannot derive a complete reachable set,
           because an incomplete one would delete the store itself
       monad fetch [<dir>] [--offline]  Resolve git dependencies into $MONAD_HOME/cache/git and write mote.lock
         The only verb that uses the network. `fetch` keeps the commit mote.lock already names,
           so a tag that moved upstream does not change a locked build
         --offline uses only what is already cached; a missing mirror is an error naming the URL
       monad update [<dir>] [--offline]  Like fetch, but re-resolve every tag/branch/HEAD pin
         Writes mote.lock from scratch; `fetch` is the one to run after a manifest edit
       build/check take --target-dir <dir>: where the store and the output directories live
         (clean/gc/store take the same flag). Without it the config and default decide
       build/check/test verify mote.lock before compiling, and take --locked, which also
         fails when a dependency's declared tag/branch/rev no longer matches the lock
         They accept --offline too, and ignore it: they never use the network
       monad store ls|verify [--target-dir <dir>]  List the store, or check its entries
         Each line is <kind> <key> <bytes> <state>; an artifact is its binary AND its IR
         verify is structural: an entry records neither the file nor the sources behind
           it, so it checks that an entry is complete and readable, not that its key
           is the right key. It exits non-zero on any incomplete entry
       monad print-targets  List the triples --target accepts, and what this llc can build for
         Each is the spelling the emitter writes; `(llc ...)` adds the argv when llc needs more
         A --target name whose architecture this llc does not register is rejected by name
       monad lsp  Speak the Language Server Protocol on stdin and stdout, until stdin ends
         Started by an editor, which is told nothing else: no arguments, no flags
       monad version  Print the git commit this binary was built from
```
