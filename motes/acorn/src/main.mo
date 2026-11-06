/// acorn's entry point: `acorn build [--config FILE] [--out DIR]`.
use std::io {IO.read_file, IO.write_stderr}
use std::path {Path, Path.of}
use clap::spec {
    Cli.ArgValue, Cli.CommandSpec, Cli.Parsed, Cli.command, Cli.option_default,
    Cli.option_optional, Cli.with_args, Cli.with_subcommands, Cli.with_version,
}
use clap::parse {Cli.run}
use lib::config {SiteConfig, SiteConfig.parse, SiteConfig.with_out}
use lib::site {Site.build}

def build_spec : Cli.CommandSpec :=
    Cli.with_args
        [Cli.option_default "config" "c" "FILE" "docs/site.toml" "the site configuration",
            Cli.option_optional "out" "o" "DIR" "the output directory (overrides `out` in the config)"]
        (Cli.command "build" "Render the site to static HTML")

def spec : Cli.CommandSpec :=
    Cli.with_subcommands [build_spec]
        (Cli.with_version "0.1.0" (Cli.command "acorn" "The monad-lang.org site generator"))

struct BuildArgs {
    config : String,
    out : Option String,
}

instance Copy BuildArgs {
    def copy (a : BuildArgs) : Pair BuildArgs BuildArgs := Pair.pair a a
}

/// Fold the parsed options into `BuildArgs` in one pass (`Cli.Parsed` is
/// affine, so it is destructured once rather than queried per option).
def apply_options (opts : List Cli.ArgValue) (acc : BuildArgs) : BuildArgs :=
    match opts {
        List.empty => acc,
        List.cons o rest => apply_options rest (apply_option o acc),
    }

def apply_option (o : Cli.ArgValue) (acc : BuildArgs) : BuildArgs :=
    match o {
        { name, value } =>
            if String.beq name "config" then { acc with config := value }
            else if String.beq name "out" then { acc with out := Option.some value }
            else acc,
    }

def decode (p : Cli.Parsed) : Result String BuildArgs :=
    match p {
        { options, .. } =>
            let start : BuildArgs := { config := "docs/site.toml", out := Option.none } in
            Result.ok (apply_options options start),
    }

def report_error (msg : String) : IO I64 := do {
    IO.write_stderr (String.concat "acorn: " (String.concat msg "\n"));
    return 1
}

def run_build (args : BuildArgs) : IO I64 :=
    match Path.of args.config {
        Result.err e => report_error e,
        Result.ok p => read_config p args.out,
    }

def read_config (p : Path) (out : Option String) : IO I64 := do {
    let text <- IO.read_file p;
    match text {
        Result.err e => report_error (String.concat args_path_msg e.message),
        Result.ok src => build_with (SiteConfig.parse src) out,
    }
}

def args_path_msg : String := "cannot read the config: "

def build_with (parsed : Result String SiteConfig) (out : Option String) : IO I64 :=
    match parsed {
        Result.err e => report_error e,
        Result.ok cfg => build_and_report (SiteConfig.with_out out cfg),
    }

def build_and_report (cfg : SiteConfig) : IO I64 := do {
    let built <- Site.build cfg;
    match built {
        Result.err e => report_error e,
        Result.ok n => do {
            IO.println (String.concat "acorn: wrote " (String.concat (I64.to_string n) (String.concat " files to " cfg.out_dir)));
            return 0
        },
    }
}

def main (args : List String) : IO I64 :=
    Cli.run spec args decode run_build
