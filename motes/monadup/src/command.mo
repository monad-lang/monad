/// monadup's command ADT, generated parser, and dispatch.
use std::io {IO.write_stderr}
use clap::args {*}
use lib::install {*}
use lib::doctor {*}
use lib::env_report {*}
use lib::scaffold {*}

#[derive Cli]
type Command {
    install (tag : Option String),
    list,
    use_ (tag : String),
    default,
    uninstall (tag : String),
    update,
    self_install,
    upgrade,
    doctor (#[arg] json : Bool) (#[arg] no_network : Bool),
    env,
    new (name : String) (#[opt] dir : Option String),
    help,
    version,
}

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
                    IO.write_stderr (String.concat "monadup: error: " (String.concat e "\n"));
                    return 1
                },
                Result.ok path => do {
                    IO.println (String.concat "monadup: created " path);
                    IO.println (String.concat "  cd " path);
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
