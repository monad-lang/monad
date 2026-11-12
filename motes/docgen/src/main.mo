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
use acorn::config {SiteConfig}
use acorn::site {Built, Site.write_pages}
use lib::extract {DocExtract.extract_mote}
use lib::model {DocMote}
use lib::render {DocRender.hub_page, DocRender.mote_pages}

def build_spec : Cli.CommandSpec :=
    Cli.with_args
        [Cli.option_default "out" "o" "DIR" "target/docs" "the output root the api/ tree is written under",
            Cli.positional_multi "motes" "the mote directories to document"]
        (Cli.command "build" "Render the named motes' API reference into api/<mote>/")

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
        List.cons _ rest => Result.ok { out := out, motes := Shared.get shared },
    }

/// An option's value, or the fallback when it was not given.
def option_or (opts : List Cli.ArgValue) (name : String) (fallback : String) : String :=
    match opts {
        List.empty => fallback,
        List.cons o rest => if String.beq o.name name then o.value else option_or rest name fallback,
    }

def run_build (args : BuildArgs) : IO I64 :=
    extract_all args.motes List.empty args

/// Extract every named mote, accumulating in order, then build and write.
/// A mote that does not extract stops the whole run: a partial reference
/// that silently drops one mote is worse than a failed build.
def extract_all (motes : List String) (acc : List DocMote) (args : BuildArgs) : IO I64 :=
    match motes {
        List.empty => write_pages_for args.out (List.reverse acc),
        List.cons m rest => extract_one m rest acc args,
    }

/// One mote, read from the directory the caller named. A mote that does not
/// extract (a missing directory, an unparsable file) stops the run with its
/// name in the message.
#[terminating]
def extract_one (mote : String) (rest : List String) (acc : List DocMote) (args : BuildArgs)
    : IO I64 := do {
    let got <- DocExtract.extract_mote mote;
    match got {
        Result.err e => report_error (String.concat mote (String.concat ": " e)),
        Result.ok m => extract_all rest (List.cons m acc) args,
    }
}

/// Every mote extracted: render the module pages and the hub, then write
/// them all through acorn's gate.
def write_pages_for (out : String) (motes : List DocMote) : IO I64 := do {
    let cfg : SiteConfig := site_config out;
    let pages := all_pages cfg motes;
    let wrote <- Site.write_pages out pages;
    match wrote {
        Result.err e => report_error e,
        Result.ok n => do {
            IO.println (String.concat "docgen: wrote "
                (String.concat (I64.to_string n) (String.concat " files under " out)));
            return 0
        },
    }
}

/// The acorn configuration the pages render with. Only the fields the
/// document shell reads matter here; the book paths are unused by an API page.
def site_config (out : String) : SiteConfig :=
    { title := "Monad API reference", base_url := "/", book_src := "docs/src",
        book_dir := "docs", out_dir := out }

/// Every page: each mote's module pages, then the hub.
def all_pages (cfg : SiteConfig) (motes : List DocMote) : List Built :=
    let shared : Shared (List DocMote) := Shared.of motes in
    List.append (mote_page_lists cfg (Shared.get shared)) [DocRender.hub_page cfg (Shared.get shared)]

def mote_page_lists (cfg : SiteConfig) (motes : List DocMote) : List Built :=
    match motes {
        List.empty => List.empty,
        List.cons m rest => List.append (DocRender.mote_pages cfg m) (mote_page_lists cfg rest),
    }

def report_error (msg : String) : IO I64 := do {
    IO.write_stderr (String.concat "docgen: " (String.concat msg "\n"));
    return 1
}

def main (args : List String) : IO I64 :=
    Cli.run spec args decode run_build
