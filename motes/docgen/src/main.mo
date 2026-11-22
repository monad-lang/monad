/// docgen's entry point: `docgen build <mote>... [--out DIR]`.
///
/// The extraction and rendering halves are `lib::extract` and `lib::render`;
/// this file is only the command surface and the write. Pages go through
/// acorn's `Site.write_pages`, so the same broken-link and duplicate-path
/// gate the book's build runs also guards the API pages.
use std::io {IO.println, IO.write_stderr}
use std::path {Path, Path.of}
use clap::spec {
    Cli.ArgValue, Cli.CommandSpec, Cli.Parsed, Cli.command, Cli.option_default,
    Cli.positional_multi, Cli.with_args, Cli.with_subcommands, Cli.with_version,
}
use clap::parse {Cli.run}
use lib::gen {DocGen.build}

def build_spec : Cli.CommandSpec :=
    Cli.with_args
        [Cli.option_default "out" "o" "DIR" "target/docs" "the docs base the mote sites are written under",
            Cli.positional_multi "motes" "the mote directories to document"]
        (Cli.command "build" "Render each named mote's docs site into <mote>/")

def spec : Cli.CommandSpec :=
    Cli.with_subcommands [build_spec]
        (Cli.with_version "0.1.0" (Cli.command "docgen" "Generate a mote API reference"))

struct BuildArgs {
    out : String,
    motes : List String,
}

instance Copy BuildArgs {
    def copy (a : BuildArgs) : Pair BuildArgs BuildArgs := Pair.pair a a
}

/// The motes to document: every positional after `build`.
def mote_args (positionals : List Cli.ArgValue) (acc : List String) : List String :=
    match positionals {
        List.empty => List.reverse acc,
        List.cons p rest => mote_args rest (List.cons p.value acc),
    }

def decode (p : Cli.Parsed) : Result String BuildArgs :=
    match p {
        { options, positionals, .. } =>
            let out : String := option_or options "out" "target/docs" in
            decode_motes out (mote_args positionals List.empty),
    }

/// The motes list, or the error when it is empty. Split out so the list is
/// matched where it is built, not read again in the caller.
def decode_motes (out : String) (motes : List String) : Result String BuildArgs :=
    let shared : Shared (List String) := Shared.of motes in
    match Shared.get shared {
        List.empty => Result.err "name at least one mote: docgen build <mote>...",
        List.cons _ rest => Result.ok { out := out, motes := motes },
    }

/// An option's value, or the fallback when it was not given.
def option_or (opts : List Cli.ArgValue) (name : String) (fallback : String) : String :=
    match opts {
        List.empty => fallback,
        List.cons o rest => if String.beq o.name name then o.value else option_or rest name fallback,
    }

def run_build (args : BuildArgs) : IO I64 := do {
    let wrote <- DocGen.build args.motes args.out false;
    match wrote {
        Result.err e => report_error e,
        Result.ok n => do {
            IO.println (String.concat "docgen: wrote "
                (String.concat (I64.to_string n) (String.concat " files under " args.out)));
            return 0
        },
    }
}

def report_error (msg : String) : IO I64 := do {
    IO.write_stderr (String.concat "docgen: " (String.concat msg "\n"));
    return 1
}

def main (args : List String) : IO I64 :=
    Cli.run spec args decode run_build
