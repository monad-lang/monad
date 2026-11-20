// Loading: the named motes' sources, and everything they import, as
// `Trellis.Source`s.
//
// A mote argument is a directory holding a `mote.toml` (`lang`,
// `motes/oak_ui`, `../x`), or a workspace member's name (`oak_ui` is looked
// for at `motes/oak_ui` too). Every `.mo` file under its `src/` is a module
// named `<mote>::<path>` (`src/lib.mo` is the mote itself), the spelling a
// `use` line has; `*_tests.mo` files and `tests/` directories are skipped
// unless asked for.
//
// Each file is parsed with the compiler's own strict parser
// (`module_info_of_source`, which also rewrites `lib::`), and its imports are
// followed by the compiler's own loader (`load_modules_from_main`) with one
// shared cache, so a dependency is read once however many files use it.
// Modules reached only that way (init, std, codegen, ...) are EXTERNAL: in
// the graph so references to them resolve, hidden in the UI by default.

use std::list {List.filter, List.any, List.intercalate}
use std::map {HashMap}
use std::io {IO.read_file, IO.is_dir, IO.file_exists}
use std::stream {StreamError}
use std::path {Path, Path.of}
use lang::types {ModulePath, Identifier, Decl, module_path_to_string_colon, show_name_path}
use lang::mote {Mote.manifest_at}
use lang::module {
    ModuleInfo, ModuleInfoCache, LoadedAndCache, ModuleSource, DeclRange,
    make_module_source, module_info_of_source, load_modules_from_main, module_info_cache_empty,
    module_info_cache_entries, expand_check_paths, decl_ranges_of_source,
}
use trellis_ui::smap {Smap.empty, Smap.insert, Smap.has}
use lib::extract {Trellis.Source, Trellis.Lines, Trellis.Lines.empty}
use lib::docs {Trellis.SourceDocs, Trellis.SourceDocs.empty, Trellis.docs_of_source}

/// A resolved mote argument: its manifest name and directory.
pub struct Trellis.Target {
    name : String,
    dir : String,
}

def trim_slash (s : String) : String :=
    if String.ends_with s "/" && String.length s > 1 then String.slice s 0 (String.length s - 1) else s

def manifest_name (dir : String) : IO (Option String) := do {
    match Path.of dir {
        Result.err _ => return Option.none,
        Result.ok p => do {
            let m <- Mote.manifest_at p;
            match m {
                Option.some manifest => return (Option.some manifest.name),
                Option.none => return Option.none,
            }
        },
    }
}

/// `arg` as a mote: itself, else `motes/<arg>`.
pub def Trellis.find_target (arg : String) : IO (Result String Trellis.Target) := do {
    let dir : String := trim_slash arg;
    let here <- manifest_name dir;
    match here {
        Option.some name => return (Result.ok { name := name, dir := dir }),
        Option.none => do {
            let alt : String := String.concat "motes/" dir;
            let there <- manifest_name alt;
            match there {
                Option.some name => return (Result.ok { name := name, dir := alt }),
                Option.none => return (Result.err (String.concat_list ["no mote at ", dir, " (or ", alt,
                    "): no mote.toml"])),
            }
        },
    }
}

def is_test_file (file : String) : Bool :=
    String.ends_with file "_tests.mo" || String.contains file "/tests/"

/// `<dir>/src/a/b.mo` as `<mote>::a::b`; `<dir>/src/lib.mo` as `<mote>`.
pub def Trellis.module_of_file (mote : String) (dir : String) (file : String) : String :=
    let prefix : String := String.concat dir "/src/" in
    let rel0 : String := if String.starts_with prefix file then String.drop (String.length prefix) file else file in
    let rel : String := if String.ends_with rel0 ".mo" then String.slice rel0 0 (String.length rel0 - 3) else rel0 in
    if String.beq rel "lib" then mote
    else String.concat_list [mote, "::", List.intercalate "::" (String.split rel "/")]

// ─── Lines ───

#[terminating]
def index_lines (rs : List DeclRange) (m : Trellis.Lines) : Trellis.Lines :=
    match rs {
        List.empty => m,
        List.cons r rest =>
            let name : String := show_name_path r.name in
            // The first declaration of a name wins (an instance's methods
            // share names with their class's).
            if Smap.has name m.starts then index_lines rest m
            else
                let next : Trellis.Lines := { starts := Smap.insert name (r.range.start.line + 1) m.starts,
                    ends := Smap.insert name (r.range.end.line + 1) m.ends } in
                index_lines rest next,
    }

def lines_of (src : String) : Trellis.Lines := index_lines (decl_ranges_of_source src) Trellis.Lines.empty

// ─── One target file ───

struct Walk {
    /// Read doc comments too (`--no-docs` turns it off).
    docs : Bool,
    sources : List Trellis.Source,
    own : HashMap String Bool,
    cache : ModuleInfoCache,
    errors : List String,
}

def module_path_of (s : String) : ModulePath := ModulePath.mk (List.map Identifier.id (String.split s "::"))

def load_file (t : Trellis.Target) (file : String) (w : Walk) : IO Walk :=
    match Path.of file {
        Result.err _ => return { w with errors := List.cons (String.concat "not a path: " file) w.errors },
        Result.ok path => load_path t file path w,
    }

def load_path (t : Trellis.Target) (file : String) (path : Path) (w : Walk) : IO Walk := do {
    let text <- IO.read_file path;
    match text {
        Result.err _ => return { w with errors := List.cons (String.concat "cannot read " file) w.errors },
        Result.ok src => do {
            let module : String := Trellis.module_of_file t.name t.dir file;
            let ms : ModuleSource := make_module_source (module_path_of module) t.name path src;
            match module_info_of_source ms {
                Result.err e => return { w with errors := List.cons e w.errors },
                Result.ok info => do {
                    let loaded <- load_modules_from_main info w.cache false;
                    let s : Trellis.Source :=
                        { module := module, mote := t.name, file := file, external := false,
                            decls := info.decl_list, lines := lines_of src,
                            docs := Trellis.docs_of_source w.docs module file src };
                    return { w with sources := List.cons s w.sources, own := Smap.insert module true w.own,
                        cache := loaded.cache }
                },
            }
        },
    }
}

#[partial]
def load_files (t : Trellis.Target) (files : List String) (w : Walk) : IO Walk :=
    match files {
        List.empty => return w,
        List.cons f rest => do {
            let w1 <- load_file t f w;
            load_files t rest w1
        },
    }

#[partial]
def load_targets (ts : List Trellis.Target) (tests : Bool) (w : Walk) : IO Walk :=
    match ts {
        List.empty => return w,
        List.cons t rest => do {
            let all <- expand_check_paths [String.concat t.dir "/src"];
            let files : List String := List.filter (fn (f : String) => tests || Bool.not (is_test_file f)) all;
            let w1 <- load_files t files w;
            load_targets rest tests w1
        },
    }

// ─── External modules (from the loader's cache) ───

def docs_of_read (on : Bool) (module : String) (file : String) (r : Result StreamError String) : Trellis.SourceDocs :=
    match r { Result.ok src => Trellis.docs_of_source on module file src, Result.err _ => Trellis.SourceDocs.empty }

def lines_of_read (r : Result StreamError String) : Trellis.Lines :=
    match r { Result.ok src => lines_of src, Result.err _ => Trellis.Lines.empty }

def mote_of_path (path : String) : String :=
    match String.split path "::" { List.cons h _ => h, List.empty => path }

#[partial]
def external_sources (docs : Bool) (infos : List ModuleInfo) (own : HashMap String Bool) (roots : List String)
    (acc : List Trellis.Source) : IO (List Trellis.Source) :=
    match infos {
        List.empty => return (List.reverse acc),
        List.cons info rest => do {
            let module : String := module_path_to_string_colon info.path;
            let mote : String := mote_of_path module;
            // A root mote's own module is loaded from its file already; a
            // cache entry for it would double it.
            if Smap.has module own || List.any (fn (r : String) => String.beq r mote) roots
            then external_sources docs rest own roots acc
            else do {
                let text <- IO.read_file info.file_path;
                let file : String := Path.to_string info.file_path;
                let s : Trellis.Source :=
                    { module := module, mote := mote, file := file, external := true,
                        decls := info.decl_list, lines := lines_of_read text,
                        docs := docs_of_read docs module file text };
                external_sources docs rest own roots (List.cons s acc)
            }
        },
    }

/// The result of a load: every source, and the files that failed to parse.
pub struct Trellis.Loaded {
    sources : List Trellis.Source,
    errors : List String,
}

/// Load `targets` and their import closure; `docs` also reads every
/// file's doc comments.
pub def Trellis.load (targets : List Trellis.Target) (tests : Bool) (docs : Bool) : IO Trellis.Loaded := do {
    let start : Walk := { docs := docs, sources := List.empty, own := Smap.empty,
        cache := module_info_cache_empty, errors := List.empty };
    let w <- load_targets targets tests start;
    let roots : List String := List.map (fn (t : Trellis.Target) => t.name) targets;
    let ext <- external_sources docs (module_info_cache_entries w.cache) w.own roots List.empty;
    return { sources := List.append (List.reverse w.sources) ext, errors := List.reverse w.errors }
}
