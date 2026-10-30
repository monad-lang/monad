/// The command spec wrapper and the handler, deliberately in their own
/// module.
///
/// `Command.setup` consumes `spec_command`, which `#[derive Cli]` generates
/// in `command.mo`. The Rust host's `reflect_type_info!` capture re-checks
/// every non-`#[test]` def in the module being expanded (`rust/core/src/eval/
/// macro_expand.rs`), and the derive's generated decls do not exist yet at
/// that point -- so a same-module consumer fails with "unbound variable
/// `spec_command`". Keeping the consumers here, in a different module that
/// is loaded after `command.mo` has expanded, is the supported shape (the
/// generated `decode_command` is consumed from `main.mo` the same way).
use std::io {IO.write_stderr}
use clap::help {Cli.help_text}
use clap::parse {Cli.version_text}
use clap::spec {
    Cli.CommandSpec, Cli.with_about, Cli.with_name, Cli.with_version,
}
use lib::command {*}
use lib::install {*}
use lib::doctor {*}
use lib::env_report {*}
use lib::scaffold {*}

/// The public spec: the derived one plus the program name and version.
pub def Command.setup : Cli.CommandSpec :=
    Cli.with_about "manage Monad nightly toolchains"
        (Cli.with_version "0.1.0" (Cli.with_name "monadup" spec_command))

pub def Command.dispatch (cmd : Command) : IO I64 :=
    match cmd {
        Command.install tag => do {
            let ctx <- Install.context;
            match tag {
                Option.some t => Install.install_tag ctx t,
                Option.none => Install.install_latest ctx,
            }
        },
        Command.list => do {
            let ctx <- Install.context;
            Install.list ctx
        },
        Command.use_ tag => do {
            let ctx <- Install.context;
            Install.use_tag ctx tag
        },
        Command.default => do {
            let ctx <- Install.context;
            Install.default ctx
        },
        Command.uninstall tag => do {
            let ctx <- Install.context;
            Install.uninstall ctx tag
        },
        Command.update => do {
            let ctx <- Install.context;
            Install.update ctx
        },
        Command.self_install => do {
            let ctx <- Install.context;
            Install.self_install ctx
        },
        Command.upgrade => do {
            let ctx <- Install.context;
            Install.upgrade ctx
        },
        Command.doctor json no_network => Doctor.run no_network json,
        Command.env => EnvReport.run,
        Command.new name dir => do {
            let r <- Scaffold.create dir name;
            match r {
                Result.err e => do {
                    IO.write_stderr ("monadup: error: " ++ e ++ "\n");
                    return 1
                },
                Result.ok path => do {
                    IO.println ("monadup: created " ++ Path.to_string path);
                    IO.println ("  cd " ++ Path.to_string path);
                    IO.println "  monad run .";
                    return 0
                },
            }
        },
        Command.help => do {
            IO.println (Cli.help_text Command.setup);
            return 0
        },
        Command.version => do {
            IO.println (Cli.version_text Command.setup);
            return 0
        },
    }
