// Extraction: parsed modules to a `Trellis.Graph`.
//
// Pure. `load.mo` does the reading; this turns each module's parsed
// declarations into graph nodes and each reference into an edge.
//
// ## Nodes
//
// One node per declaration a reader would name: a `def`, `type`, `struct`,
// `class`, `instance` or `defmacro`. A constructor is not a node of its own:
// a reference to `Option.some` is an edge to `Option`. A class method is
// not one either: `Monad.bind` is an edge to `Monad`. `use`, `open`,
// `infix` and macro invocations declare nothing.
//
// ## References and resolution
//
// `lang::use_completeness::decl_refs` lists what each declaration WRITES, on
// two axes: the signature and the body. A written name is resolved to its
// declaring module here, import-aware, because names are not qualified
// before codegen:
//
// - a qualified reference (`std::list::List.map`) names its module;
// - a bare one (`unify`, `List.map`, `some`) is looked up in a global
//   index of every declared name (and constructor/method spelling). One
//   owner wins outright. Several owners are ranked: the referring module
//   itself, then a module it `use`s naming the name, then any module it
//   `use`s, then its own mote, then the ambient `init`/`std`/`prelude`.
//   A tie, or no owner at all, is UNRESOLVED and counted, never guessed.
//
// Locals never reach here (`decl_refs` skips bound variables). What stays
// unresolved is mostly method-call sugar (`x.f`, whose target needs the
// receiver's type), field names and class-method dispatch: the documented
// v1 limit of a parse-level graph.

use std::list {List.filter, List.any, List.intercalate}
use std::map {HashMap}
use lang::types {
    Decl, Def, Inductive, InductConstructor, Struct, Class, ClassDef, Instance, Attribute, Visibility,
    Identifier, NamePath, ModulePath, QualifiedName, Term, SortLevel, UseFilter, UseItem,
    show_identifier, show_name_path, module_path_to_string_colon,
}
use lang::use_completeness {Refs, DeclRefs, decl_refs}
use trellis_ui::smap {Smap.empty, Smap.insert, Smap.get, Smap.has}
use trellis_ui::model {Trellis.ModuleNode, Trellis.DeclNode, Trellis.Edge, Trellis.Graph, Trellis.decl_id}

/// One parsed module, as `load.mo` hands it over. `lines` maps a
/// declaration's name to its 1-based line.
pub struct Trellis.Source {
    module : String,
    mote : String,
    file : String,
    external : Bool,
    decls : List Decl,
    lines : HashMap String I64,
}

// ═══ Declarations to nodes ═══

/// A node-to-be: its name, kind, visibility, attributes and sort, and the
/// extra spellings that should resolve to it (constructors, methods).
struct Named {
    name : String,
    kind : String,
    vis : String,
    attrs : List String,
    sort : String,
    aliases : List String,
    refs : DeclRefs,
}

def vis_of (v : Visibility) : String :=
    match v { Visibility.pub_ => "pub", Visibility.priv_ => "priv", Visibility.package_private => "mote" }

def attr_name (a : Attribute) : String := show_identifier a.name

def attr_names (attrs : List Attribute) : List String := List.map attr_name attrs

/// The result sort of a declared type: the codomain after every `->`.
/// `Prop` for a proposition; empty for anything else (or no declaration).
#[terminating]
def result_sort (t : Term) : String :=
    match t {
        Term.pi _b _arg ret => result_sort ret,
        Term.sort level => match level { SortLevel.concrete n => if n == 0 then "Prop" else "", _ => "" },
        _ => "",
    }

def ctor_aliases (owner : String) (cs : List InductConstructor) : List String :=
    List.flatten (List.map (fn (c : InductConstructor) =>
        let bare : String := show_name_path c.name in
        [bare, String.concat_list [owner, ".", bare]]) cs)

def method_aliases (owner : String) (ms : List ClassDef) : List String :=
    List.map (fn (m : ClassDef) => String.concat_list [owner, ".", show_identifier m.name]) ms

def instance_name (ins : Instance) : String :=
    let own : String := show_identifier ins.name in
    String.concat "instance " (if String.is_empty own then show_name_path ins.cls else own)

#[partial]
def named_of (d : Decl) : Option Named :=
    match d {
        Decl.def_d def_ =>
            Option.some { name := show_name_path def_.name, kind := "def", vis := vis_of def_.vis,
                attrs := attr_names def_.attrs, sort := result_sort def_.typ, aliases := List.empty,
                    refs := decl_refs d },
        Decl.def_macro_d def_ =>
            Option.some { name := show_name_path def_.name, kind := "macro", vis := vis_of def_.vis,
                attrs := attr_names def_.attrs, sort := "", aliases := List.empty, refs := decl_refs d },
        Decl.inductive_d ind =>
            let name : String := show_name_path ind.name in
            Option.some { name := name, kind := "type", vis := vis_of ind.vis, attrs := attr_names ind.attrs,
                sort := result_sort ind.typ, aliases := ctor_aliases name ind.constructors, refs := decl_refs d },
        Decl.struct_d st =>
            let name : String := show_identifier st.name in
            Option.some { name := name, kind := "struct", vis := vis_of st.vis,
                attrs := attr_names st.attrs, sort := "", aliases := [String.concat name ".mk"], refs := decl_refs d },
        Decl.class_d cls =>
            let name : String := show_identifier cls.name in
            let sort : String := match cls.sort { Option.some t => result_sort t, Option.none => "" } in
            Option.some { name := name, kind := "class", vis := vis_of cls.vis, attrs := List.empty, sort := sort,
                aliases := method_aliases name cls.methods, refs := decl_refs d },
        Decl.instance_d ins =>
            Option.some { name := instance_name ins, kind := "instance", vis := vis_of ins.vis, attrs := List.empty,
                sort := "", aliases := List.empty, refs := decl_refs d },
        Decl.scoped_open_d _path _filter inner => named_of inner,
        _ => Option.none,
    }

#[partial]
def named_all (ds : List Decl) : List Named :=
    match ds {
        List.empty => List.empty,
        List.cons d rest =>
            match named_of d {
                Option.some n => List.cons n (named_all rest),
                Option.none => named_all rest,
            },
    }

// ═══ The global index ═══

/// A declared name's owner: the module and the node id it resolves to.
struct Owner {
    module : String,
    mote : String,
    id : String,
}

def add_owner (key : String) (o : Owner) (m : HashMap String (List Owner)) : HashMap String (List Owner) :=
    let existing : List Owner := match Smap.get key m { Option.some os => os, Option.none => List.empty } in
    if List.any (fn (x : Owner) => String.beq x.id o.id) existing then m
    else Smap.insert key (List.cons o existing) m

#[terminating]
def add_aliases (keys : List String) (o : Owner) (m : HashMap String (List Owner)) : HashMap String (List Owner) :=
    match keys {
        List.empty => m,
        List.cons k rest => add_aliases rest o (add_owner k o m),
    }

/// One module after naming: its source and its named declarations.
struct Parsed {
    src : Trellis.Source,
    named : List Named,
}

#[terminating]
def index_named (s : Trellis.Source) (ns : List Named) (m : HashMap String (List Owner)) : HashMap String
    (List Owner) :=
    match ns {
        List.empty => m,
        List.cons n rest =>
            let o : Owner := { module := s.module, mote := s.mote, id := Trellis.decl_id s.module n.name } in
            index_named s rest (add_aliases (List.cons n.name n.aliases) o m),
    }

#[terminating]
def build_index (ps : List Parsed) (m : HashMap String (List Owner)) : HashMap String (List Owner) :=
    match ps {
        List.empty => m,
        List.cons p rest => build_index rest (index_named p.src p.named m),
    }

// ═══ Import context ═══

/// What a module's `use` lines say: each used module with the names it
/// lists (empty for a bare `use m` or a glob).
struct Uses {
    paths : List String,
    named : HashMap String String,
}

def item_names (items : List UseItem) : List String :=
    List.flatten (List.map (fn (it : UseItem) =>
        match it {
            UseItem.use_name n => [show_identifier n],
            UseItem.use_rename n _alias => [show_identifier n],
            UseItem.use_sub n _items => [show_identifier n],
            UseItem.use_sub_rename n _alias _items => [show_identifier n],
            UseItem.use_glob => List.empty,
        }) items)

#[terminating]
def name_all (names : List String) (path : String) (m : HashMap String String) : HashMap String String :=
    match names {
        List.empty => m,
        List.cons n rest => name_all rest path (Smap.insert n path m),
    }

#[terminating]
def collect_uses (ds : List Decl) (u : Uses) : Uses :=
    match ds {
        List.empty => u,
        List.cons d rest =>
            match d {
                Decl.use_d path filter _public =>
                    let p : String := module_path_to_string_colon path in
                    let names : List String := match filter { UseFilter.use_items items => item_names items,
                        UseFilter.use_bare => List.empty } in
                    collect_uses rest { paths := List.cons p u.paths, named := name_all names p u.named },
                _ => collect_uses rest u,
            },
    }

def uses_of (ds : List Decl) : Uses := collect_uses ds { paths := List.empty, named := Smap.empty }

// ═══ Resolution ═══

/// The head segment of a dotted name (`List.map` -> `List`).
def head_of (name : String) : String :=
    match String.split name "." { List.cons h _ => h, List.empty => name }

/// The ambient motes, most basic first: a bare constructor both declare
/// (`cons`, `empty`) means the `init` one, which every module sees.
def ambient_rank (mote : String) : I64 :=
    if String.beq mote "init" then 22
    else if String.beq mote "prelude" then 21
    else if String.beq mote "std" then 20
    else 0

def in_list (x : String) (xs : List String) : Bool := List.any (fn (y : String) => String.beq x y) xs

/// How strongly module `here` (with `uses`) prefers owner `o` for `name`.
def rank (here : Trellis.Source) (uses : Uses) (name : String) (o : Owner) : I64 :=
    if String.beq o.module here.module then 100
    else if Smap.has name uses.named || Smap.has (head_of name) uses.named
        then (if in_list o.module uses.paths then 80 else if String.beq o.mote here.mote then 50 else 30)
    else if in_list o.module uses.paths then 60
    else if String.beq o.mote here.mote then 40
    else ambient_rank o.mote

/// The single best owner, or none when the best rank is shared.
#[terminating]
def best (here : Trellis.Source) (uses : Uses) (name : String) (os : List Owner) (top : Option Owner)
    (top_rank : I64) (tied : Bool) : Option Owner :=
    match os {
        List.empty => if tied then Option.none else top,
        List.cons o rest =>
            let r : I64 := rank here uses name o in
            if r > top_rank then best here uses name rest (Option.some o) r false
            else if r == top_rank then best here uses name rest top top_rank true
            else best here uses name rest top top_rank tied,
    }

def lookup (index : HashMap String (List Owner)) (key : String) : List Owner :=
    match Smap.get key index { Option.some os => os, Option.none => List.empty }

/// Resolve one bare spelling written in `here` (inside the declaration
/// `self_name`, whose `with` prefix a bare name may omit).
def resolve_bare (index : HashMap String (List Owner)) (here : Trellis.Source) (uses : Uses) (self_name : String)
    (name : String) : Option Owner :=
    let direct : List Owner := lookup index name in
    let candidates : List Owner :=
        if List.is_empty direct
        then
            // `with Ui { def graph ... graph_layout ... }`: a bare name in a
            // `with` block may mean the prefixed declaration.
            let prefix : String := head_of self_name in
            if String.beq prefix self_name then List.empty else lookup index (String.concat_list [prefix, ".", name])
        else direct in
    match candidates {
        List.empty => Option.none,
        List.cons only rest => if List.is_empty rest then Option.some only
            else best here uses name candidates Option.none (0 - 1) false,
    }

/// Resolve a qualified spelling: an owner declared in exactly that module.
def resolve_qualified (index : HashMap String (List Owner)) (qn : QualifiedName) : Option Owner :=
    let module : String := module_path_to_string_colon qn.qmod in
    let name : String := show_name_path qn.qname in
    match List.filter (fn (o : Owner) => String.beq o.module module) (lookup index name) {
        List.cons o _ => Option.some o,
        List.empty =>
            // A hub re-export (`std::list` naming a name declared in `init`):
            // fall back to a unique global owner.
            match lookup index name {
                List.cons only rest => if List.is_empty rest then Option.some only else Option.none,
                List.empty => Option.none,
            },
    }

// ═══ Edges ═══

/// Resolution totals: references seen, resolved.
struct Tally {
    refs : I64,
    resolved : I64,
    edges : List Trellis.Edge,
    seen : HashMap String Bool,
    unresolved : List String,
}

def is_letter (b : I64) : Bool := (b >= 65 && b <= 90) || (b >= 97 && b <= 122)

def is_upper (b : I64) : Bool := b >= 65 && b <= 90

def byte_at (s : String) (i : I64) : I64 :=
    match String.get s i { Option.some b => U8.to_i64 b, Option.none => 0 - 1 }

#[terminating]
def has_letter_from (s : String) (i : I64) (n : I64) : Bool :=
    if i >= n then false else if is_letter (byte_at s i) then true else has_letter_from s (i + 1) n

/// A spelling that cannot name a declaration: empty, a wildcard, an
/// operator, or a type-variable-shaped name (`A`, `K2`). Counting these as
/// unresolved would only hide the real misses.
def is_noise (written : String) : Bool :=
    let n : I64 := String.length written in
    n == 0 || String.beq written "_" || Bool.not (has_letter_from written 0 n)
        || (n <= 2 && is_upper (byte_at written 0))

def note (t : Tally) (from : String) (axis : String) (written : String) (owner : Option Owner) : Tally :=
    match owner {
        Option.none =>
            if is_noise written then t
            else { t with refs := t.refs + 1, unresolved := List.cons written t.unresolved },
        Option.some o =>
            let counted : Tally := { t with refs := t.refs + 1, resolved := t.resolved + 1 } in
            let key : String := String.concat_list [from, "\t", o.id, "\t", axis] in
            // A constructor alias and its type, or two spellings of one
            // name, are one edge.
            if String.beq o.id from || Smap.has key counted.seen then counted
            else
                let e : Trellis.Edge := { from := from, to := o.id, axis := axis } in
                { counted with edges := List.cons e counted.edges, seen := Smap.insert key true counted.seen },
    }

#[terminating]
def bare_edges (index : HashMap String (List Owner)) (here : Trellis.Source) (uses : Uses) (from : String)
    (self_name : String) (axis : String) (names : List NamePath) (t : Tally) : Tally :=
    match names {
        List.empty => t,
        List.cons n rest =>
            let written : String := show_name_path n in
            bare_edges index here uses from self_name axis rest (note t from axis written
                (resolve_bare index here uses self_name written)),
    }

#[terminating]
def qualified_edges (index : HashMap String (List Owner)) (from : String) (axis : String) (qns : List QualifiedName)
    (t : Tally) : Tally :=
    match qns {
        List.empty => t,
        List.cons qn rest =>
            let written : String := String.concat_list [module_path_to_string_colon qn.qmod, "::",
                show_name_path qn.qname] in
            qualified_edges index from axis rest (note t from axis written (resolve_qualified index qn)),
    }

def refs_edges (index : HashMap String (List Owner)) (here : Trellis.Source) (uses : Uses) (from : String)
    (self_name : String) (axis : String) (r : Refs) (t : Tally) : Tally :=
    qualified_edges index from axis r.qualified (bare_edges index here uses from self_name axis r.bare t)

#[terminating]
def module_edges (index : HashMap String (List Owner)) (here : Trellis.Source) (uses : Uses) (ns : List Named)
    (t : Tally) : Tally :=
    match ns {
        List.empty => t,
        List.cons n rest =>
            let from : String := Trellis.decl_id here.module n.name in
            let t1 : Tally := refs_edges index here uses from n.name "s" n.refs.signature t in
            module_edges index here uses rest (refs_edges index here uses from n.name "b" n.refs.body t1),
    }

#[terminating]
def all_edges (index : HashMap String (List Owner)) (ps : List Parsed) (t : Tally) : Tally :=
    match ps {
        List.empty => t,
        List.cons p rest => all_edges index rest (module_edges index p.src (uses_of p.src.decls) p.named t),
    }

// ═══ The graph ═══

/// How a declaration's docs page is addressed: `<base><mote>/<module>.html#<kind>.<name>`,
/// docgen's scheme (`motes/docgen/src/render.mo`). Empty without a base.
pub def Trellis.doc_href (base : String) (mote : String) (module : String) (kind : String) (name : String) : String :=
    if String.is_empty base then ""
    else
        let inner : String :=
            if String.beq module mote then "index"
            else if String.starts_with (String.concat mote "::") module
            then List.intercalate "/" (String.split (String.drop (String.length mote + 2) module) "::")
            else List.intercalate "/" (String.split module "::") in
        let page : String := if String.beq inner "index" then String.concat mote "/index.html"
            else String.concat_list [mote, "/", inner, ".html"] in
        String.concat_list [base, page, "#", kind, ".", name]

def line_of (s : Trellis.Source) (name : String) : I64 :=
    match Smap.get name s.lines { Option.some l => l, Option.none => 0 }

def node_of (docs : String) (s : Trellis.Source) (n : Named) : Trellis.DeclNode :=
    { id := Trellis.decl_id s.module n.name, name := n.name, module := s.module, mote := s.mote, kind := n.kind,
        vis := n.vis, line := line_of s n.name, attrs := n.attrs, sort := n.sort,
        doc := Trellis.doc_href docs s.mote s.module n.kind n.name, external := s.external }

def nodes_of (docs : String) (p : Parsed) : List Trellis.DeclNode := List.map (node_of docs p.src) p.named

def module_of (p : Parsed) : Trellis.ModuleNode :=
    { path := p.src.module, mote := p.src.mote, file := p.src.file, external := p.src.external }

def parse_all (ss : List Trellis.Source) : List Parsed :=
    List.map (fn (s : Trellis.Source) => { src := s, named := named_all s.decls }) ss

/// The extraction result: the graph, plus every unresolved spelling (most
/// recent first) for `--verbose`.
pub struct Trellis.Extracted {
    graph : Trellis.Graph,
    unresolved : List String,
}

/// Build the graph. `roots` are the motes the extraction was asked for;
/// `docs` is the docs base URL (empty for no links).
pub def Trellis.extract (roots : List String) (docs : String) (sources : List Trellis.Source) : Trellis.Extracted :=
    let ps : List Parsed := parse_all sources in
    let index : HashMap String (List Owner) := build_index ps Smap.empty in
    let t0 : Tally := { refs := 0, resolved := 0, edges := List.empty, seen := Smap.empty, unresolved := List.empty } in
    let t : Tally := all_edges index ps t0 in
    let g : Trellis.Graph :=
        { roots := roots, modules := List.map module_of ps, decls := List.flatten (List.map (nodes_of docs) ps),
            edges := List.reverse t.edges, refs := t.refs, resolved := t.resolved,
                unresolved := t.refs - t.resolved } in
    { graph := g, unresolved := t.unresolved }
