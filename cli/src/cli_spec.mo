/// The spec `main` parses against, and the thin facade the parser and tests
/// use.
///
/// It lives here, not in `cli.mo`, for the reason `motes/monadup/src/
/// dispatch.mo` documents: the derive's capture re-checks every def in the
/// expanded module before the generated decls exist, so a same-module consumer
/// fails with "unbound variable `spec_command`". A module loaded after
/// `cli.mo` has expanded is the supported shape.
use clap::help {Cli.help_text}
use clap::parse {Cli.run}
use clap::spec {Cli.CommandSpec, Cli.with_about, Cli.with_name, Cli.with_version}
use lib::cli {*}

/// One line per subcommand, rendered by the generated `--help`.
///
/// The derive has no constructor-level attribute (`CtorInfo` carries only a
/// name and its fields), so the descriptions are attached to the derived spec
/// here rather than beside each constructor.
pub def Command.abouts : List (Pair String String) := [
    Pair.pair "build" "Compile a .mo source file, or a mote, to a native binary",
    Pair.pair "install" "Build a release binary and install it under $MONAD_HOME/bin",
    Pair.pair "run" "Compile and execute a source file",
    Pair.pair "eval" "Evaluate a source file with the built-in interpreter (pure programs)",
    Pair.pair "repl" "Interactive read-eval-print loop on stdin/stdout",
    Pair.pair "pretty" "Parse and pretty-print a source file",
    Pair.pair "check" "Parse and typecheck source files, with no execution",
    Pair.pair "test" "Compile and run each file's own #[test] defs",
    Pair.pair "clean" "Remove build output, keeping the store",
    Pair.pair "gc" "Remove store entries the named files cannot reach",
    Pair.pair "store" "List the store, or check its entries",
    Pair.pair "fetch" "Resolve git dependencies into the cache and write mote.lock",
    Pair.pair "update" "Re-resolve every git pin, then write mote.lock",
    Pair.pair "print-targets" "List the triples --target accepts and what this llc can build for",
    Pair.pair "lsp" "Speak the Language Server Protocol on stdin/stdout",
    Pair.pair "version" "Print the git commit this binary was built from",
    Pair.pair "help" "Print usage",
]

def Command.about_lookup (xs : List (Pair String String)) (name : String) : String :=
    match xs {
        List.empty => "",
        List.cons p rest => match p {
            Pair.pair k v => if String.beq k name then v else Command.about_lookup rest name,
        },
    }

pub def Command.about_of (name : String) : String :=
    Command.about_lookup Command.abouts name

def Command.set_abouts (subs : List Cli.CommandSpec) : List Cli.CommandSpec :=
    match subs {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons { c with about := Command.about_of c.name } (Command.set_abouts rest),
    }

/// Attach the about texts to the derived spec's subcommands.
def Command.with_abouts (s : Cli.CommandSpec) : Cli.CommandSpec :=
    { s with subcommands := Command.set_abouts s.subcommands }

/// The public spec: the derived one plus the program name, about and version.
pub def Command.spec (version : String) : Cli.CommandSpec :=
    Cli.with_about "Monad is in alpha mode and under heavy development. Expect breaking changes, bugs, and incomplete features."
        (Cli.with_version version
            (Cli.with_name "monad" (Command.with_abouts spec_command)))

/// Parse `args`, decode and run `handler`. Help/version print and exit 0; a
/// usage error prints `error: ...` plus usage and exits 2.
pub def Command.parse_and_run (version : String) (args : List String) (handler : Command -> IO I64) : IO I64 :=
    Cli.run (Command.spec version) args decode_command handler

/// The generated help text for the `help` subcommand.
pub def Command.help_text (version : String) : String :=
    Cli.help_text (Command.spec version)

/// The argv parser used by the smoke tests. It keeps the old `Command`
/// return shape (anything the parser rejects is `Command.help`); the real
/// entry point uses `Command.parse_and_run`, which preserves the error and
/// the exit code.
pub def Command.from_args (args : List String) : Command :=
    match parse_command args {
        Result.ok c => c,
        Result.err _ => Command.help,
    }

/// The effective debug-info setting for the two verbs that build a binary:
/// on by default, `--release` opts out, an explicit `--debug` opts back in.
pub def Command.debug_of (cmd : Command) : Bool :=
    match cmd {
        Command.build _ _ _ debug release _ _ _ _ _ _ _ => if debug then true else Bool.not release,
        Command.run _ _ _ debug release => if debug then true else Bool.not release,
        Command.install _ _ _ _ _ _ => false,
        Command.eval _ _ => false,
        Command.repl => false,
        Command.pretty _ => false,
        Command.check _ _ _ _ _ _ _ => false,
        Command.test _ _ _ _ _ _ _ _ => false,
        Command.clean _ _ => false,
        Command.gc _ _ _ _ => false,
        Command.store _ _ => false,
        Command.fetch _ _ => false,
        Command.update _ _ => false,
        Command.print_targets => false,
        Command.lsp => false,
        Command.version => false,
        Command.help => false,
    }
