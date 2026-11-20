// A declaration's signature, highlighted, with each name in it that the
// extractor resolved turned into a link to the declaration it names.
//
// The extractor already resolves every name a signature writes (the `s`
// edges, import-aware; see `motes/trellis/src/extract.mo`), so nothing is
// resolved again here: a written name is matched against the names of the
// declaration's own signature targets. `Highlight.spans` cuts `Ui.GraphSpec`
// into `Ui`, `.`, `GraphSpec`; a dotted run is joined back first. A name
// matches a target by its full spelling, by its head (`List.cons` is an edge
// to `List`), or by its last segment (a bare `GraphSpec` inside a
// `with Ui { ... }` block).

use std::list {List.any, List.filter_map}
use std::map {HashMap}
use oak::typed {Oak.Node}
use oak::events {Html.on_click}
use oak::elements {Html.span, Html.button, Html.type_, Html.class_, Html.text, Html.title_attr}
use fmt::highlight {Span, HlClass, Highlight.spans, Highlight.css_class}
use lib::model {Trellis.Graph, Trellis.DeclNode, Trellis.Edge}
use lib::smap {Smap.empty, Smap.insert, Smap.get, Smap.has}
use lib::seq {Seq.fold, Seq.reverse}

/// The declarations `id`'s signature names, in edge order, each once.
pub def Trellis.sig_targets (g : Trellis.Graph) (id : String) : List Trellis.DeclNode :=
    let ids : List String := Seq.reverse (Seq.fold (fn (acc : List String) (e : Trellis.Edge) =>
        if String.beq e.from id && String.beq e.axis "s" && Bool.not (List.any (fn
            (x : String) => String.beq x e.to) acc)
        then List.cons e.to acc else acc) List.empty g.edges) in
    let wanted : HashMap String Bool := Seq.fold (fn (m : HashMap String Bool) (x : String) => Smap.insert x true m)
        Smap.empty ids in
    let found : HashMap String Trellis.DeclNode :=
        Seq.fold (fn (m : HashMap String Trellis.DeclNode) (d : Trellis.DeclNode) =>
            if Smap.has d.id wanted then Smap.insert d.id d m else m) Smap.empty g.decls in
    List.filter_map (fn (x : String) => Smap.get x found) ids

def last_segment (name : String) : String :=
    match List.reverse (String.split name ".") { List.cons l _ => l, List.empty => name }

def add_new (key : String) (id : String) (m : HashMap String String) : HashMap String String :=
    if Smap.has key m then m else Smap.insert key id m

/// Spelling -> decl id, full names first so they win over a last segment.
def name_index (targets : List Trellis.DeclNode) : HashMap String String :=
    let full : HashMap String String :=
        Seq.fold (fn (m : HashMap String String) (d : Trellis.DeclNode) => add_new d.name d.id m) Smap.empty targets in
    Seq.fold (fn (m : HashMap String String) (d : Trellis.DeclNode) => add_new (last_segment d.name) d.id m) full
        targets

def resolve (index : HashMap String String) (name : String) : Option String :=
    match Smap.get name index {
        Option.some id => Option.some id,
        Option.none =>
            // `List.cons` -> `List`, `Option.some` -> `Option`.
            let lead : String := String.slice name 0 (String.length name - String.length (last_segment name) - 1) in
            if String.is_empty lead then Option.none else Smap.get lead index,
    }

def is_word (s : String) : Bool :=
    match String.get s 0 {
        Option.none => false,
        Option.some b => let c : I64 := U8.to_i64 b in (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c == 95,
    }

/// A dotted run `w (. w)*` at the front of `rest`, after the word `acc`.
struct Run {
    name : String,
    cls : HlClass,
    rest : List Span,
}

def run_end (acc : String) (cls : HlClass) (rest : List Span) : Run := { name := acc, cls := cls, rest := rest }

#[terminating]
def take_run (acc : String) (cls : HlClass) (rest : List Span) : Run :=
    match rest {
        List.empty => run_end acc cls rest,
        List.cons dot after =>
            if Bool.not (String.beq dot.text ".") then run_end acc cls rest
            else
                match after {
                    List.empty => run_end acc cls rest,
                    List.cons w more =>
                        if is_word w.text then take_run (String.concat_list [acc, ".", w.text]) w.cls more
                        else run_end acc cls rest,
                },
    }

def styled {Msg : Type} (cls : HlClass) (text : String) : Oak.Node Msg :=
    let c : String := Highlight.css_class cls in
    if String.is_empty c then Html.text text else Html.span [Html.class_ [String.concat "tok-" c]] [Html.text text]

def piece {Msg : Type} (index : HashMap String String) (pick : String -> Msg) (r : Run) : Oak.Node Msg :=
    match resolve index r.name {
        Option.some id =>
            Html.button [Html.type_ "button", Html.class_ ["trellis-sig__ref"], Html.title_attr id,
                Html.on_click (pick id)] [Html.text r.name],
        Option.none => styled r.cls r.name,
    }

#[terminating]
def render {Msg : Type} (index : HashMap String String) (pick : String -> Msg) (spans : List Span)
    (acc : List (Oak.Node Msg)) : List (Oak.Node Msg) :=
    match spans {
        List.empty => List.reverse acc,
        List.cons s rest =>
            if is_word s.text
            then
                let r : Run := take_run s.text s.cls rest in
                render index pick r.rest (List.cons (piece index pick r) acc)
            else render index pick rest (List.cons (styled s.cls s.text) acc),
    }

/// `sig` highlighted, each resolved name a button sending `pick <decl id>`.
pub def Trellis.sig_view {Msg : Type} (sig : String) (targets : List Trellis.DeclNode) (pick : String -> Msg)
    : List (Oak.Node Msg) :=
    if String.is_empty sig then List.empty else render (name_index targets) pick (Highlight.spans sig) List.empty
