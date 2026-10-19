/// monadup's command ADT and the parser `#[derive Cli]` generates from it.
///
/// The consumers of the generated decls (`Command.setup`, `Command.dispatch`)
/// live in `dispatch.mo`, not here: the Rust host's `reflect_type_info!`
/// capture re-checks every non-`#[test]` def in the expanded module before
/// the derive's decls exist, so a same-module consumer fails with "unbound
/// variable `spec_command`".
use clap::args {*}

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
