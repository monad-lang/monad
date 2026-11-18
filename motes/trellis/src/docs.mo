// Doc comments: each module's leading `///` block and each declaration's
// `///` comment, as markdown, read with docgen's own scan
// (`DocExtract.extract_source_as`), so trellis and the docs site agree on
// what a declaration's docs are (attributes between the comment and the
// declaration are skipped; a plain `//` line separates).

use std::map {HashMap}
use docgen::extract {DocExtract.extract_source_as}
use docgen::model {DocModule, DocItem}
use trellis_ui::smap {Smap.empty, Smap.insert, Smap.has}
use trellis_ui::seq {Seq.fold}

/// One file's docs: the module's own, and each documented declaration's by
/// name (the first declaration of a name wins, as for line numbers).
pub struct Trellis.SourceDocs {
    module_docs : String,
    decl_docs : HashMap String String,
}

pub def Trellis.SourceDocs.empty : Trellis.SourceDocs := { module_docs := "", decl_docs := Smap.empty }

def item_step (m : HashMap String String) (i : DocItem) : HashMap String String :=
    match i.doc {
        Option.none => m,
        Option.some text => if Smap.has i.name m then m else Smap.insert i.name text m,
    }

/// The docs of `src`, the source of `module` (read from `file`).
pub def Trellis.docs_of_source (module : String) (file : String) (src : String) : Trellis.SourceDocs :=
    let dm : DocModule := DocExtract.extract_source_as module file src in
    let own : String := match dm.doc { Option.some t => t, Option.none => "" } in
    { module_docs := own, decl_docs := Seq.fold item_step Smap.empty dm.items }
