/// The one-call entry point: named mote directories to written pages.
///
/// `docgen build` (`main.mo`) and `monad doc` (`cli/src/main.mo`) both want
/// the same walk -- extract each mote, render its pages, write them all
/// through acorn's gate -- so it lives here rather than in either command.
/// Neither front end owns the behaviour; they differ only in how they spell
/// the arguments.
use std::io {IO.println}
use acorn::config {SiteConfig}
use acorn::site {Built, Site.write_pages}
use lib::extract {DocExtract.extract_mote}
use lib::model {DocMote}
use lib::render {DocRender.hub_page, DocRender.mote_pages}

/// The pages for a list of mote directories, written under `out`. Returns
/// the number of files written.
///
/// A mote that does not extract stops the whole run: a partial reference
/// that silently drops a mote is worse than a failed build, because the
/// missing module reads as "this mote has no such module".
pub def DocGen.build (motes : List String) (out : String) (include_private : Bool) : IO (Result String I64) := do {
    let extracted <- extract_all motes List.empty;
    match extracted {
        Result.err e => return (Result.err e),
        Result.ok ms => write_all_ms out (select_items include_private ms),
    }
}

/// What a page shows: `pub` declarations only, unless the caller asked for
/// the package-private and `priv` ones too.
#[partial]
def select_items (include_private : Bool) (motes : List DocMote) : List DocMote :=
    match motes {
        List.empty => List.empty,
        List.cons m rest =>
            List.cons (if include_private then m else DocMote.public_only m) (select_items include_private rest),
    }

#[terminating]
def extract_all (motes : List String) (acc : List DocMote) : IO (Result String (List DocMote)) :=
    match motes {
        List.empty => return (Result.ok (List.reverse acc)),
        List.cons m rest => extract_one m rest acc,
    }

#[terminating]
def extract_one (mote : String) (rest : List String) (acc : List DocMote)
    : IO (Result String (List DocMote)) := do {
    let got <- DocExtract.extract_mote mote;
    match got {
        Result.err e => return (Result.err (String.concat mote (String.concat ": " e))),
        Result.ok m => extract_all rest (List.cons m acc),
    }
}

def write_all_ms (out : String) (motes : List DocMote) : IO (Result String I64) := do {
    let cfg : SiteConfig := site_config out;
    let shared : Shared (List DocMote) := Shared.of motes;
    let pages : List Built := List.append (all_mote_pages cfg (Shared.get shared))
        [DocRender.hub_page cfg (Shared.get shared)];
    Site.write_pages out pages
}

/// The acorn configuration the pages render with. Only the fields the page
/// shell reads matter; the book paths are unused by an API page.
def site_config (out : String) : SiteConfig :=
    { title := "Monad API reference", base_url := "/", book_src := "docs/src",
        book_dir := "docs", out_dir := out }

#[terminating]
def all_mote_pages (cfg : SiteConfig) (motes : List DocMote) : List Built :=
    match motes {
        List.empty => List.empty,
        List.cons m rest => List.append (DocRender.mote_pages cfg m) (all_mote_pages cfg rest),
    }
