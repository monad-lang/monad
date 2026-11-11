/// Extraction: a mote's sources to the page model.
///
/// The compiler's own outline of a file -- `toolkit::decl_text`'s
/// `decl_texts_of_source`, built on `lang::module`'s `decl_ranges_of_source`
/// -- names every declaration and trims its text to what the user wrote.
/// This module adds the two things the outline does not carry: the `///`
/// doc comment above each declaration, and the declaration's visibility.
///
/// THE DOC-COMMENT SCAN is a backward walk over lines. The trimmed range
/// EXCLUDES the `///` comment but INCLUDES the `#[...]` attribute lines: a
/// declaration's span starts at its first attribute (or its first token when
/// it has none), so the walk begins one line above the span and skips
/// `#[...]` lines on its way up to the docs. It stops at the first line that
/// is neither. A plain `//` line stops the walk too: a comment between the
/// docs and the declaration is a deliberate separation, and reading past it
/// would attach the previous item's docs to this one.
///
/// THE SIGNATURE is the declaration's own text from its first attributed
/// token, cut at its header. A `def`'s page shows its parameters and return
/// type, not its body; a `type`'s or `class`'s page shows the whole
/// declaration, because its shape is its contract. The cut is the first line
/// that ends the header: a `:=` for a def with a body, a lone `:` for a
/// bodyless native, and the closing `}` for a type/class/instance. Files
/// here type-checked before docgen ever saw them, so the cut is a display
/// choice, not a parse.

use lang::module {module_name_from_path}
use lang::types {SourceRange}
use std::io {IO.list_dir, IO.read_file}
use std::path {Path, Path.of}
use toolkit::decl_text {
    DeclText, decl_text_kind, decl_text_name, decl_text_span, decl_texts_of_source,
}
use lib::model {DocItem, DocModule, DocMote}

/// The extraction entry point: every documented source file of `mote_dir`,
/// as one `DocMote`. `IO.list_dir` is one level and sorted, and its entries
/// are the FULL paths under `src/`, so a `tests` subdirectory's files carry
/// the segment the skip below keys on. Files named `*_tests.mo` are skipped
/// too -- they are the mote's own verification, not its API.
pub def DocExtract.extract_mote (mote_dir : String) : IO (Result String DocMote) :=
    match Path.of mote_dir {
        Result.err e => return (Result.err e),
        Result.ok p => DocExtract.extract_mote_at p,
    }

/// `extract_mote` with the mote directory already validated. The mote's
/// name is its directory's last segment -- the name a `use` path's first
/// segment must spell.
pub def DocExtract.extract_mote_at (mote_dir : Path) : IO (Result String DocMote) := do {
    let name : String := Path.file_name mote_dir;
    let src_dir : String := String.concat (Path.to_string mote_dir) "/src";
    match Path.of src_dir {
        Result.err e => return (Result.err e),
        Result.ok p => do {
            let listed <- IO.list_dir p;
            let files : List String := keep_source_files listed List.empty;
            let walked <- extract_files name src_dir files List.empty;
            match walked {
                Result.err e => return (Result.err e),
                Result.ok modules => return (Result.ok (DocMote.mk name modules)),
            }
        },
    }
}

/// `DocExtract.extract_mote` over one source file -- the shape the tests
/// drive, and what a caller holding a single file wants. `file` is the
/// module's identity (`init/src/string.mo`); the module path is derived
/// from it, so the function works on any file the caller names.
pub def DocExtract.extract_source (file : String) (src : String) : DocModule :=
    let module : String := module_name_from_path file in
    let lines : Shared (List String) := Shared.of (split_lines src) in
    let ds : List DeclText := decl_texts_of_source src in
    let items : List DocItem := doc_items file src lines ds List.empty in
    DocModule.mk module file (module_doc_of lines) (List.reverse items)

/// One `DocItem` per declaration, accumulated in reverse. The span's
/// `start.line` is the line the range begins on -- the first `#[...]`
/// attribute when the declaration has one, else the declaration itself -- so
/// `item_of` adds the attribute count to land on the declaration's own line.
#[partial]
def doc_items (file : String) (src : String) (lines : Shared (List String)) (ds : List DeclText)
    (acc : List DocItem) : List DocItem :=
    match ds {
        List.empty => acc,
        List.cons d rest =>
            let kind : String := decl_text_kind d in
            if is_api_kind kind
            then
                let item : DocItem := item_of file src lines (decl_text_name d) kind (decl_text_span d) in
                doc_items file src lines rest (List.cons item acc)
            else doc_items file src lines rest acc,
    }

/// Is this declaration part of the mote's API page? A `use`/`open` is the
/// file's wiring, not its surface, and a `mote` declaration is the manifest
/// itself. Everything else -- `def`, `struct`, `type`, `class`, `instance`,
/// `infix`, `defmacro` -- is what a reader of the module comes for.
def is_api_kind (kind : String) : Bool :=
    Bool.not (String.beq kind "use")
        && Bool.not (String.beq kind "open")
        && Bool.not (String.beq kind "mote")

/// One declaration's `DocItem` from its name, kind and span. The span is
/// destructured in one pattern and its three numbers are handed on, so no
/// field of a non-`Copy` `SourceRange` is read twice.
def item_of (file : String) (src : String) (lines : Shared (List String)) (name : String)
    (kind : String) (sp : SourceRange) : DocItem :=
    match sp {
        { start, end, .. } =>
            item_at file src lines name kind start.offset start.line end.offset,
    }

/// The item's body, with the span's numbers already extracted. Flat rather
/// than nested: a `DocItem` built in a deep match arm is the self-hosted
/// codegen hazard, and every value here is named before use.
def item_at (file : String) (src : String) (lines : Shared (List String)) (name : String)
    (kind : String) (off : I64) (line : I64) (eoff : I64) : DocItem :=
    let raw : String := String.slice src off (I64.sub eoff off) in
    let signature : String := signature_of raw in
    let doc : Option String := DocExtract.doc_comment_of lines line in
    let decl_line : I64 := I64.add line (count_attribute_lines raw) in
    DocItem.mk name kind (is_pub signature) doc signature file decl_line

/// The `///` doc comment above the declaration starting at `line`, or
/// `Option.none`. The backward walk: `line - 1`, `line - 2`, ... collecting
/// `///` lines and skipping `#[...]` lines, stopping at the first line that
/// is neither (a blank line, a `//` comment, another declaration).
///
/// The lines are the file's own, pre-split once per file by
/// `DocExtract.extract_source` and handed over as a `Shared` handle: the
/// walk reads the list at every step, and an owned `List` would be spent by
/// the first read.
pub def DocExtract.doc_comment_of (lines : Shared (List String)) (line : I64) : Option String :=
    doc_lines_before lines (I64.sub line 1) List.empty

/// Collect `///` lines from `line` upward (line numbers decreasing),
/// skipping `#[...]` lines. Because the walk moves UP and conses each line it
/// meets, `acc` ends up in reading order already -- `finish_doc_lines` joins
/// it as-is. The walk stops at the first line that is neither a doc comment
/// nor an attribute: a blank line, a plain `//`, or another declaration.
#[partial]
def doc_lines_before (lines : Shared (List String)) (line : I64) (acc : List String) : Option String :=
    match nth_line (Shared.get lines) line {
        Option.none => finish_doc_lines acc,
        Option.some text =>
            let trimmed : String := String.trim text in
            if String.starts_with "///" trimmed
            then doc_lines_before lines (I64.sub line 1) (List.cons trimmed acc)
            else if String.starts_with "#[" trimmed
            then doc_lines_before lines (I64.sub line 1) acc
            else finish_doc_lines acc,
    }

/// The module's own leading `///` block: the contiguous `///` lines at the
/// very top of the file, before any declaration. The walk stops at the first
/// non-`///` line, so a `//` banner comment above the docs ends it.
///
/// This walk moves DOWN and conses, so its accumulator ends up bottom-first;
/// `List.reverse` puts it back into reading order before joining.
def module_doc_of (lines : Shared (List String)) : Option String :=
    match doc_lines_at lines 1 List.empty {
        List.empty => Option.none,
        List.cons first rest =>
            let shared : Shared (List String) := Shared.of (List.cons first rest) in
            finish_doc_lines (List.reverse (Shared.get shared)),
    }

/// Collect the file's own leading `///` lines from `line` downward,
/// bottom-first. Unlike the declaration walk this collects ONLY `///` lines --
/// the module doc is the contiguous block at the top of the file, and any
/// other line ends it.
#[partial]
def doc_lines_at (lines : Shared (List String)) (line : I64) (acc : List String) : List String :=
    match nth_line (Shared.get lines) line {
        Option.none => acc,
        Option.some text =>
            let trimmed : String := String.trim text in
            if String.starts_with "///" trimmed
            then doc_lines_at lines (I64.add line 1) (List.cons trimmed acc)
            else acc,
    }

/// The `line`-th line, 1-based, of a pre-split list.
#[partial]
def nth_line (lines : List String) (line : I64) : Option String :=
    match lines {
        List.empty => Option.none,
        List.cons first rest =>
            if I64.beq line 1 then Option.some first else nth_line rest (I64.sub line 1),
    }

/// `Option.none` when nothing was collected; the joined lines otherwise.
/// `acc` is already in reading order for the declaration walk, which moves
/// UP and conses each line it meets; `module_doc_of` moves DOWN, so its
/// caller passes its own list reversed. Each line loses its `/// ` marker and
/// keeps its meaning: a lone `///` is the paragraph break it reads as, and
/// the whole result is trimmed so the block neither starts nor ends blank.
def finish_doc_lines (acc : List String) : Option String :=
    match acc {
        List.empty => Option.none,
        List.cons _ rest =>
            let shared : Shared (List String) := Shared.of acc in
            Option.some (String.trim (join_doc_lines (Shared.get shared) "")),
    }

#[partial]
def join_doc_lines (lines : List String) (acc : String) : String :=
    match lines {
        List.empty => acc,
        List.cons l rest => join_doc_lines rest (String.concat acc (String.concat (strip_doc_marker l) "\n")),
    }

/// `/// text` -> `text`; `///` -> `` (a paragraph break).
def strip_doc_marker (line : String) : String :=
    let rest : String := String.drop 3 line in
    if String.starts_with " " rest then String.drop 1 rest else rest

/// The declaration's visibility: its own trimmed text starts with the
/// whole word `pub` once any leading `#[...]` attribute lines are skipped.
/// The range starts at the first attribute, so a `#[test]`/`#[opaque]`
/// declaration's text begins with the attribute, not the visibility.
def is_pub (text : String) : Bool :=
    String.starts_with "pub " (after_attributes (split_lines text))

/// The declaration text with its leading `#[...]` attribute lines removed:
/// the first line that is not an attribute, and everything after it. A
/// well-formed declaration always has such a line.
#[partial]
def after_attributes (lines : List String) : String :=
    match lines {
        List.empty => "",
        List.cons l rest =>
            if String.starts_with "#[" (String.trim l)
            then after_attributes rest
            else join_lines (List.cons l rest) "",
    }

/// How many `#[...]` lines the declaration's text starts with. The span
/// begins at the first attribute, so the declaration's own line is the span's
/// line plus this count -- the line a reader's editor calls the declaration's.
#[partial]
def count_attribute_lines (text : String) : I64 :=
    count_attribute_lines_go (split_lines text) 0

#[partial]
def count_attribute_lines_go (lines : List String) (n : I64) : I64 :=
    match lines {
        List.empty => n,
        List.cons l rest =>
            if String.starts_with "#[" (String.trim l)
            then count_attribute_lines_go rest (I64.add n 1)
            else n,
    }

/// The lines joined with `\n`, so a multi-line signature keeps its shape.
#[partial]
def join_lines (lines : List String) (acc : String) : String :=
    match lines {
        List.empty => acc,
        List.cons l rest => join_lines rest (String.concat acc (String.concat l "\n")),
    }

/// The declaration's header: its text from its first post-attribute token,
/// cut at the header's last line. The leading `#[...]` attributes are
/// dropped -- a page shows the signature, not the attribute that produced it
/// (a `#[test]` def is not part of an API, and `#[opaque]` is an
/// implementation note).
def signature_of (text : String) : String :=
    let lines : List String := split_lines text in
    let body : String := after_attributes lines in
    cut_header_lines (split_lines body) List.empty

/// The text's lines, in order. Split on `\n`; a `\r` before it is kept by
/// the trim each line gets later, so CRLF sources work.
#[partial]
def split_lines (text : String) : List String :=
    split_lines_go (String.to_list text) List.empty List.empty

def nl : U8 := 10u8

#[partial]
def split_lines_go (bytes : List U8) (cur : List U8) (acc : List String) : List String :=
    match bytes {
        List.empty => List.reverse (List.cons (String.from_list (List.reverse cur)) acc),
        List.cons b rest =>
            if U8.beq b nl
            then split_lines_go rest List.empty (List.cons (String.from_list (List.reverse cur)) acc)
            else split_lines_go rest (List.cons b cur) acc,
    }

/// Walk the lines, keeping the header's own lines. The first line that
/// ends a header (`:=`, a lone `:`, a closing `}`) is the last kept line;
/// everything after it is the body, which the signature does not show. The
/// kept lines are joined with `\n` (not `String.concat_list`, which joins
/// with nothing and would run a multi-line header together), then trimmed.
#[partial]
def cut_header_lines (lines : List String) (kept : List String) : String :=
    match lines {
        List.empty => String.trim (join_lines (List.reverse kept) ""),
        List.cons l rest =>
            if header_ends_here l
            then String.trim (join_lines (List.reverse (List.cons l kept)) "")
            else cut_header_lines rest (List.cons l kept),
    }

/// Does this line end the header? A `:=` ends a def's header (the body
/// follows); a line whose trimmed form ends in `}` closes a shape; a line
/// ending in `:` alone is a bodyless native's whole signature.
def header_ends_here (line : String) : Bool :=
    let t : String := String.trim line in
    String.contains t ":="
    || String.ends_with t "}"
    || String.ends_with t ":"

/// Keep the `.mo` files that are not test files: `*_tests.mo` by name, and
/// anything whose path has a `tests` segment. `IO.list_dir` hands back the
/// full paths under `src/`, so the segment test sees them.
#[partial]
def keep_source_files (files : List Path) (acc : List String) : List String :=
    match files {
        List.empty => List.reverse acc,
        List.cons p rest =>
            let name : String := Path.to_string p in
            let kept : Bool := String.ends_with name ".mo" && Bool.not (is_test_file name) in
            keep_source_files rest (if kept then List.cons name acc else acc),
    }

/// A test file: `*_tests.mo` by name, or any path containing a `tests`
/// segment. `IO.list_dir` is one level but joins the parent, so
/// `src/tests/site_tests.mo` carries the segment; the name test catches
/// the `std/src/list_tests1.mo` layout.
def is_test_file (path : String) : Bool :=
    String.ends_with path "_tests.mo" || String.contains path "/tests/"

/// Read each file and extend the module list, stopping at the first
/// error. The list is accumulated by cons and reversed once at the end, so
/// a mote with a hundred modules costs one reverse, not a hundred appends;
/// the `DocMote` itself is built once, by the caller, from the result.
#[partial]
#[terminating]
def extract_files (name : String) (src_dir : String) (files : List String) (acc : List DocModule)
    : IO (Result String (List DocModule)) :=
    match files {
        List.empty => return (Result.ok (List.reverse acc)),
        List.cons f rest => extract_one_file name src_dir f rest acc,
    }

#[partial]
#[terminating]
def extract_one_file (name : String) (src_dir : String) (file : String) (rest : List String)
    (acc : List DocModule) : IO (Result String (List DocModule)) := do {
    let full : String := String.concat src_dir (String.concat "/" (file_base file));
    match Path.of full {
        Result.err e => return (Result.err e),
        Result.ok p => read_source name src_dir file rest acc p,
    }
}

/// The file exists and reads: build its module and extend the list.
#[terminating]
def read_source (name : String) (src_dir : String) (file : String) (rest : List String)
    (acc : List DocModule) (p : Path) : IO (Result String (List DocModule)) := do {
    let read <- IO.read_file p;
    match read {
        Result.err e => return (Result.err (String.concat "read " (String.concat (Path.to_string p) (String.concat ": " e.message)))),
        Result.ok src => read_and_extend name src_dir file rest acc src,
    }
}

/// The file read: build its module and continue the walk. Split out of
/// the match arm because an arm body of several statements needs its own
/// `do { ... }`; the nested-block-in-arm shape is the one the parser
/// rejects.
#[terminating]
def read_and_extend (name : String) (src_dir : String) (file : String) (rest : List String)
    (acc : List DocModule) (src : String) : IO (Result String (List DocModule)) := do {
    let base : String := file_base file;
    let rel : String := String.concat name (String.concat "/src/" base);
    let mod : DocModule := DocExtract.extract_source rel src;
    extract_files name src_dir rest (List.cons mod acc)
}

/// The file name's last segment: `src/string.mo` -> `string.mo`. The path
/// came from `IO.list_dir`, which joins the parent, so one `find_last`
/// suffices.
def file_base (path : String) : String :=
    let idx : I64 := String.find_last path "/" in
    if I64.beq idx -1 then path else String.slice path (idx + 1) (String.length path - idx - 1)
