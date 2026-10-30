/// The compiler's command line, declared once and parsed by `#[derive Cli]`.
///
/// Kept out of `main.mo` for two reasons. The derive's capture re-checks and
/// lowers every def in the module being expanded before the generated decls
/// exist, so a same-module consumer fails with "unbound variable
/// `spec_command`" (motes/monadup/src/command.mo documents the same shape).
/// And `main.mo` stays free of macro/attribute syntax: it is the entry point
/// the self-hosted parse/scope/typecheck suites re-parse.
///
/// Field types are the derive's supported set: `Bool` (a flag), `String`,
/// `I64`, `Option String`, `Option I64`, `List String`. `Path` is deliberately
/// not used here -- dispatch converts the validated strings at the point
/// where a path is required.
use clap::args {*}

#[derive Cli]
pub type Command {
    /// Compile a `.mo` source file, or a mote directory, to a native binary.
    build
        (#[pos {help := "a .mo source file or a mote directory"}] file : Option String)
        (#[pos {help := "output name (legacy positional form of --output)"}] name : Option String)
        (#[arg {short := "v", help := "print each module as it loads and one line per stage"}] verbose : Bool)
        (#[arg {short := "g", help := "emit DWARF debug info"}] debug : Bool)
        (#[arg {short := "", help := "build without debug info"}] release : Bool)
        (#[arg {short := "", help := "compile for real, reading and writing no store entry"}] no_cache : Bool)
        (#[arg {short := "", help := "fail when a dependency's pin no longer matches mote.lock"}] locked : Bool)
        (#[opt {short := "", value_name := "DIR", help := "where the store and output directories live"}] target_dir : Option String)
        (#[opt {short := "", value_name := "NAME", help := "pick one [[bin]] target"}] bin : Option String)
        (#[opt {short := "", value_name := "TRIPLE", help := "build for another target"}] target : Option String)
        (#[arg {short := "", help := "accepted and ignored: build never uses the network"}] offline : Bool)
        (#[opt {short := "o", value_name := "NAME", help := "output name"}] output : Option String),
    /// Build a release binary and install it atomically under `$MONAD_HOME/bin`.
    install
        (#[pos {help := "a .mo source file or a mote directory"}] file : Option String)
        (#[opt {short := "o", value_name := "NAME", help := "installed name (required for a source file)"}] output : Option String)
        (#[opt {short := "", value_name := "NAME", help := "pick one [[bin]] target"}] bin : Option String)
        (#[arg {short := "v", help := "print each module as it loads"}] verbose : Bool)
        (#[arg {short := "", help := "compile for real, reading and writing no store entry"}] no_cache : Bool)
        (#[opt {short := "", value_name := "TRIPLE", help := "build for another target"}] target : Option String),
    /// Compile and execute a source file; everything after `--` is its argv.
    run
        (#[pos {help := "a .mo source file or a mote directory"}] file : String)
        (#[pos {help := "the program's own arguments (put flag-like ones after `--`)"}] args : List String)
        (#[arg {short := "v", help := "print each module as it loads"}] verbose : Bool)
        (#[arg {short := "g", help := "emit DWARF debug info"}] debug : Bool)
        (#[arg {short := "", help := "build without debug info"}] release : Bool),
    /// Evaluate a source file with the built-in interpreter (pure programs).
    eval
        (#[pos {help := "a .mo source file"}] file : String)
        (#[arg {short := "v", help := "print each module as it loads"}] verbose : Bool),
    /// Interactive read-eval-print loop on stdin/stdout.
    repl,
    /// Parse and pretty-print a source file.
    pretty (#[pos {help := "a .mo source file"}] file : String),
    /// Parse and typecheck source files, with no execution.
    check
        (#[pos {help := "files or directories; omitted means the current mote"}] files : List String)
        (#[arg {short := "v", help := "print a per-declaration progress trace"}] verbose : Bool)
        (#[arg {short := "w", help := "check every mote in the enclosing workspace"}] workspace : Bool)
        (#[arg {short := "", help := "skip the check cache"}] no_cache : Bool)
        (#[arg {short := "", help := "fail when a dependency's pin no longer matches mote.lock"}] locked : Bool)
        (#[opt {short := "", value_name := "DIR", help := "where the check cache lives"}] target_dir : Option String)
        (#[arg {short := "", help := "accepted and ignored: check never uses the network"}] offline : Bool),
    /// Compile and run each file's own `#[test]` defs.
    test
        (#[pos {help := "files or directories; omitted means the current mote"}] files : List String)
        (#[arg {short := "v", help := "print per-file timing and cache statistics"}] verbose : Bool)
        (#[arg {short := "w", help := "test every mote in the enclosing workspace"}] workspace : Bool)
        (#[arg {short := "", help := "fail when a dependency's pin no longer matches mote.lock"}] locked : Bool)
        (#[arg {short := "", help := "skip the test cache"}] no_cache : Bool)
        (#[opt {short := "", value_name := "DIR", help := "where the test cache lives"}] target_dir : Option String)
        (#[opt {short := "j", value_name := "N", help := "files in flight (default 4; 1 is serial)"}] jobs : Option I64)
        (#[arg {short := "", help := "accepted and ignored: test never uses the network"}] offline : Bool),
    /// Remove build output, keeping the store.
    clean
        (#[arg {short := "", help := "remove the target directory itself, store included"}] all : Bool)
        (#[opt {short := "", value_name := "DIR", help := "the target directory to clean"}] target_dir : Option String),
    /// Remove store entries the named files cannot reach.
    gc
        (#[pos {help := "files or directories; omitted means the current mote"}] files : List String)
        (#[arg {short := "w", help := "consider every mote in the enclosing workspace"}] workspace : Bool)
        (#[arg {short := "", help := "remove the entries (dry run by default)"}] apply : Bool)
        (#[opt {short := "", value_name := "DIR", help := "where the store lives"}] target_dir : Option String),
    /// List the store, or check its entries.
    store
        (#[pos {help := "ls or verify"}] sub : String)
        (#[opt {short := "", value_name := "DIR", help := "where the store lives"}] target_dir : Option String),
    /// Resolve git dependencies into the cache and write `mote.lock`.
    fetch
        (#[pos {help := "the mote directory (default: .)"}] dir : Option String)
        (#[arg {short := "", help := "use only what is already cached"}] offline : Bool),
    /// Re-resolve every git pin, then write `mote.lock`.
    update
        (#[pos {help := "the mote directory (default: .)"}] dir : Option String)
        (#[arg {short := "", help := "use only what is already cached"}] offline : Bool),
    /// List the triples `--target` accepts and what this llc can build for.
    print_targets,
    /// Speak the Language Server Protocol on stdin/stdout.
    lsp,
    /// Print the git commit this binary was built from.
    version,
    /// Print usage.
    help,
}
