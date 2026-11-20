/// Extraction over in-memory modules: nodes per declaration kind, the
/// signature/body axes, import-aware resolution, constructors and methods
/// folded into their owners, and unresolved references counted.

use std::list {List.any, List.filter}
use lang::module {try_parse_decls_strict}
use lang::types {Decl}
use trellis_ui::model {Trellis.Graph, Trellis.DeclNode, Trellis.Edge, Trellis.ModuleNode}
use lib::extract {Trellis.Source, Trellis.Extracted, Trellis.extract, Trellis.doc_href, Trellis.Lines.empty}
use lib::load {Trellis.module_of_file}
use lib::docs {Trellis.docs_of_source}

def source (module : String) (mote : String) (external : Bool) (text : String) : Trellis.Source :=
    let decls : List Decl := match try_parse_decls_strict text Option.none { Result.ok ds => ds,
        Result.err _ => List.empty } in
    { module := module, mote := mote, file := "", external := external, decls := decls,
        lines := Trellis.Lines.empty, docs := Trellis.docs_of_source true module "" text }

def util : Trellis.Source := source "demo::util" "demo" false r#"
pub type Shape { circle (r : I64), square (s : I64) }
pub def area (s : Shape) : I64 := match s { Shape.circle r => r * r * 3, Shape.square x => x * x }
pub def helper (x : I64) : I64 := x + 1
class Sized A { def size (a : A) : I64 }
"#

def main_m : Trellis.Source := source "demo::main" "demo" false r#"
use demo::util {Shape, area, helper}
def total (xs : I64) : I64 := area (Shape.circle (helper xs))
def describe (s : Shape) : I64 := Sized.size s
def local_only (n : I64) : I64 := let y := n in mystery y
"#

def other : Trellis.Source := source "other::util" "other" true r#"
pub def helper (x : I64) : I64 := x
"#

def extracted : Trellis.Extracted := Trellis.extract ["demo"] "" [util, main_m, other]

// Field reads go through these: the bootstrap host does not resolve a field
// of a top-level def (`(decls_of g)`), only of a binder.
def graph_of (e : Trellis.Extracted) : Trellis.Graph := e.graph
def misses_of (e : Trellis.Extracted) : List String := e.unresolved
def decls_of (gr : Trellis.Graph) : List Trellis.DeclNode := gr.decls
def edges_of (gr : Trellis.Graph) : List Trellis.Edge := gr.edges
def modules_of (gr : Trellis.Graph) : List Trellis.ModuleNode := gr.modules
def miss_count (gr : Trellis.Graph) : I64 := gr.unresolved

def g : Trellis.Graph := graph_of extracted

def has_decl (id : String) (kind : String) : Bool :=
    List.any (fn (d : Trellis.DeclNode) => String.beq d.id id && String.beq d.kind kind) (decls_of g)

def has_edge (from : String) (to : String) (axis : String) : Bool :=
    List.any (fn (e : Trellis.Edge) => String.beq e.from from && String.beq e.to to && String.beq e.axis axis)
        (edges_of g)

#[test]
def test_one_node_per_declaration_kind : Bool :=
    has_decl "demo::util::Shape" "type" && has_decl "demo::util::area" "def"
        && has_decl "demo::util::Sized" "class" && has_decl "demo::main::total" "def"

#[test]
def test_use_line_beats_another_motes_owner : Bool :=
    // `helper` is declared in demo::util and other::util; main `use`s the first.
    has_edge "demo::main::total" "demo::util::helper" "b" && Bool.not
        (has_edge "demo::main::total" "other::util::helper" "b")

#[test]
def test_constructor_edges_go_to_the_type : Bool :=
    has_edge "demo::main::total" "demo::util::Shape" "b"

#[test]
def test_signature_axis : Bool :=
    has_edge "demo::main::describe" "demo::util::Shape" "s" && has_edge "demo::util::area" "demo::util::Shape" "s"

#[test]
def test_class_method_edge_goes_to_the_class : Bool :=
    has_edge "demo::main::describe" "demo::util::Sized" "b"

#[test]
def test_unknown_names_are_counted_not_guessed : Bool :=
    (miss_count g) >= 1 && List.any (fn (n : String) => String.beq n "mystery") (misses_of extracted)
        && Bool.not (List.any (fn
            (e : Trellis.Edge) => String.beq e.from "demo::main::local_only" && String.contains e.to "mystery")
            (edges_of g))

#[test]
def test_externals_are_marked : Bool :=
    List.any (fn (d : Trellis.DeclNode) => String.beq d.id "other::util::helper" && d.external) (decls_of g)

#[test]
def test_module_of_file : Bool :=
    String.beq (Trellis.module_of_file "lang" "lang" "lang/src/typecheck/infer.mo") "lang::typecheck::infer"
        && String.beq (Trellis.module_of_file "lang" "lang" "lang/src/lib.mo") "lang"

#[test]
def test_doc_href_follows_docgen : Bool :=
    String.beq
        (Trellis.doc_href "/docs/" "lang" "lang::typecheck::affine" "def" "check")
        "/docs/lang/typecheck/affine.html#def.check"
        && String.beq (Trellis.doc_href "" "lang" "lang::x" "def" "y") ""

def noisy : Trellis.Source := source "demo::noisy" "demo" false r#"
struct Pt { x : I64, y : I64 }
def make (a : I64) : Pt := Pt.mk a a
def twice (s : Shape) : I64 := match s { Shape.circle r => r, Shape.square x => x }
"#

def noisy_g : Trellis.Extracted := Trellis.extract ["demo"] "" [util, noisy]

#[test]
def test_struct_constructor_goes_to_the_struct : Bool :=
    List.any (fn
        (e : Trellis.Edge) => String.beq e.from "demo::noisy::make"
            && String.beq e.to "demo::noisy::Pt") (edges_of (graph_of noisy_g))

#[test]
def test_two_constructors_are_one_edge : Bool :=
    List.length (List.filter (fn (e : Trellis.Edge) =>
        String.beq e.from "demo::noisy::twice" && String.beq e.to "demo::util::Shape"
            && String.beq e.axis "b") (edges_of (graph_of noisy_g))) == 1

#[test]
def test_wildcards_and_type_variables_are_not_misses : Bool :=
    Bool.not (List.any (fn
        (n : String) => String.beq n "_" || String.beq n "A" || String.is_empty n) (misses_of noisy_g))

// ─── Doc comments ───

def documented : Trellis.Source := source "demo::doc" "demo" false r#"/// The demo module.
/// Second line.

/// Adds one to `x`.
#[inline]
pub def bump (x : I64) : I64 := x + 1

// A plain comment separates.
pub def bare (x : I64) : I64 := x

/// A point.
pub struct Point { x : I64 }

pub struct Opts { width : I64 := 80 }

#[inline]
pub def pad (s : String)
    (n : I64) : String := s
"#

def doc_graph : Trellis.Graph :=
    let e : Trellis.Extracted := Trellis.extract ["demo"] "" [documented] in
    e.graph

def docs_of (name : String) : String :=
    match List.filter (fn (d : Trellis.DeclNode) => String.beq d.name name) (decls_of doc_graph) {
        List.cons d _ => d.docs,
        List.empty => "<missing>",
    }

#[test]
def test_decl_docs_skip_attributes : Bool := String.beq (docs_of "bump") "Adds one to `x`."

#[test]
def test_undocumented_decl_has_no_docs : Bool := String.is_empty (docs_of "bare")

#[test]
def test_struct_docs : Bool := String.beq (docs_of "Point") "A point."

def sig_of (name : String) : String :=
    match List.filter (fn (d : Trellis.DeclNode) => String.beq d.name name) (decls_of doc_graph) {
        List.cons d _ => d.sig,
        List.empty => "<missing>",
    }

#[test]
def test_signature_stops_at_the_body : Bool := String.beq (sig_of "bump") "pub def bump (x : I64) : I64"

#[test]
def test_signature_spans_lines_and_drops_attributes : Bool :=
    String.beq (sig_of "pad") "pub def pad (s : String)\n(n : I64) : String"

#[test]
def test_a_field_default_does_not_end_the_signature : Bool :=
    String.beq (sig_of "Opts") "pub struct Opts { width : I64 := 80 }"

#[test]
def test_struct_signature_is_whole : Bool := String.beq (sig_of "Point") "pub struct Point { x : I64 }"

#[test]
def test_module_docs : Bool :=
    match (modules_of doc_graph) {
        List.cons m _ => String.contains m.docs "The demo module." && String.contains m.docs "Second line.",
        List.empty => false,
    }

def instances : Trellis.Source := source "demo::inst" "demo" false r#"
class Sized A { def size (a : A) : I64 }
instance Sized I64 { def size a := a }
instance Sized Bool { def size b := 1 }
"#

#[test]
def test_unnamed_instances_get_distinct_ids : Bool :=
    let e : Trellis.Extracted := Trellis.extract ["demo"] "" [instances] in
    let g : Trellis.Graph := e.graph in
    let ids : List String := List.map (fn (d : Trellis.DeclNode) => d.id)
        (List.filter (fn (d : Trellis.DeclNode) => String.beq d.kind "instance") (decls_of g)) in
    List.length ids == 2 && List.any (fn (i : String) => String.beq i "demo::inst::instance Sized I64") ids
        && List.any (fn (i : String) => String.beq i "demo::inst::instance Sized Bool") ids
