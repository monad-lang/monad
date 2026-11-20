// Doc comments and signatures: each module's leading `///` block, each
// declaration's `///` comment as markdown, and each declaration's header as
// the author wrote it (docgen's `DocItem.signature`), read with docgen's own scan
// (`DocExtract.extract_source_as`), so trellis and the docs site agree on
// what a declaration's docs are (attributes between the comment and the
// declaration are skipped; a plain `//` line separates).

use std::list {List.intercalate}
use std::map {HashMap}
use docgen::extract {DocExtract.extract_source_as}
use docgen::model {DocModule, DocItem}
use trellis_ui::smap {Smap.empty, Smap.insert, Smap.has}
use trellis_ui::seq {Seq.fold}

/// One file's docs: the module's own, each documented declaration's, and
/// each declaration's signature, by name (the first declaration of a name
/// wins, as for line numbers).
pub struct Trellis.SourceDocs {
    module_docs : String,
    decl_docs : HashMap String String,
    decl_sigs : HashMap String String,
}

pub def Trellis.SourceDocs.empty : Trellis.SourceDocs :=
    { module_docs := "", decl_docs := Smap.empty, decl_sigs := Smap.empty }

def doc_step (m : HashMap String String) (i : DocItem) : HashMap String String :=
    match i.doc {
        Option.none => m,
        Option.some text => if Smap.has i.name m then m else Smap.insert i.name text m,
    }

/// A signature longer than this many lines (a big `type`'s constructors)
/// is cut, ending in `…`; the source view shows the rest.
pub def Trellis.sig_lines : I64 := 30

#[terminating]
def take_lines (n : I64) (ls : List String) : List String :=
    match ls {
        List.empty => List.empty,
        List.cons l rest => if n <= 0 then List.empty else List.cons l (take_lines (n - 1) rest),
    }

def cut_sig (sig : String) : String :=
    let ls : List String := String.split sig "\n" in
    if List.length ls <= Trellis.sig_lines then sig
    else String.concat (List.intercalate "\n" (take_lines Trellis.sig_lines ls)) "\n    \u{2026}"

def sig_step (m : HashMap String String) (i : DocItem) : HashMap String String :=
    if Smap.has i.name m || String.is_empty i.signature then m else Smap.insert i.name (cut_sig i.signature) m

/// The docs and signatures of `src`, the source of `module` (read from
/// `file`). With `docs` off only the signatures are kept.
pub def Trellis.docs_of_source (docs : Bool) (module : String) (file : String) (src : String) : Trellis.SourceDocs :=
    let dm : DocModule := DocExtract.extract_source_as module file src in
    let own : String := match dm.doc { Option.some t => if docs then t else "", Option.none => "" } in
    { module_docs := own, decl_docs := if docs then Seq.fold doc_step Smap.empty dm.items else Smap.empty,
        decl_sigs := Seq.fold sig_step Smap.empty dm.items }
