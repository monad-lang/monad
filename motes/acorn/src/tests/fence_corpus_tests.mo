/// Every `monad` fence in the book round-trips through the highlighter: the
/// spans' texts concatenate to the fence's text exactly. Run from the repo
/// root (the book is read from `docs/src`).
use std::io {IO.read_file, IO.list_dir}
use std::list {List.filter, List.length}
use std::path {Path, Path.of, Path.to_string}
use markdown::types {Markdown.Block, Markdown.Document}
use markdown::options {Markdown.site_options}
use markdown::parse {Markdown.parse_with}
use fmt::highlight {Span, Highlight.spans}
use lib::passes {FenceInfo, Passes.fence_info}

def round_trips (src : String) : Bool :=
    String.beq (String.concat_list (List.map (fn (s : Span) => s.text) (Highlight.spans src))) src

def is_monad (info : Option String) : Bool :=
    match info {
        Option.some i => lang_is_monad (Passes.fence_info i),
        Option.none => false,
    }

def lang_is_monad (f : FenceInfo) : Bool :=
    match f {
        { lang, .. } => String.beq lang "monad",
    }

/// The number of `monad` fences that do NOT round-trip, among `blocks`.
def bad_fences (blocks : List Markdown.Block) : I64 :=
    match blocks {
        List.empty => 0,
        List.cons b rest => bad_in b + bad_fences rest,
    }

#[terminating]
def bad_in (b : Markdown.Block) : I64 :=
    match b {
        Markdown.Block.block_code_block info literal =>
            if is_monad info && Bool.not (round_trips literal) then 1 else 0,
        Markdown.Block.block_quote inner => bad_fences inner,
        _ => 0,
    }

def bad_in_doc (d : Markdown.Document) : I64 :=
    match d {
        { blocks, .. } => bad_fences blocks,
    }

def bad_in_file (p : Path) : IO I64 := do {
    let read <- IO.read_file p;
    match read {
        Result.ok src => return (bad_in_doc (Markdown.parse_with Markdown.site_options src)),
        Result.err _ => return 1,
    }
}

def sum_bad (files : List Path) (acc : I64) : IO I64 :=
    match files {
        List.empty => return acc,
        List.cons f rest => sum_then f rest acc,
    }

#[terminating]
def sum_then (f : Path) (rest : List Path) (acc : I64) : IO I64 := do {
    let n <- bad_in_file f;
    sum_bad rest (acc + n)
}

def markdown_files (files : List Path) : List Path :=
    List.filter (fn (p : Path) => String.ends_with (Path.to_string p) ".md") files

#[test]
def test_every_book_fence_round_trips : IO Bool :=
    match Path.of "docs/src" {
        Result.err _ => return false,
        Result.ok dir => check_dir dir,
    }

def check_dir (dir : Path) : IO Bool := do {
    let files <- IO.list_dir dir;
    let md : Shared (List Path) := Shared.of (markdown_files files);
    let count : I64 := List.length (Shared.get md);
    let bad <- sum_bad (Shared.get md) 0;
    return (bad == 0 && count > 0)
}
