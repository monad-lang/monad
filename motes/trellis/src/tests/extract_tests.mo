/// Extraction over in-memory modules: nodes per declaration kind, the
/// signature/body axes, import-aware resolution, constructors and methods
/// folded into their owners, and unresolved references counted.

use std::list {List.any, List.filter}
use std::map {HashMap}
use lang::module {try_parse_decls_strict}
use lang::types {Decl}
use trellis_ui::smap {Smap.empty}
use trellis_ui::model {Trellis.Graph, Trellis.DeclNode, Trellis.Edge}
use lib::extract {Trellis.Source, Trellis.Extracted, Trellis.extract, Trellis.doc_href}
use lib::load {Trellis.module_of_file}

def no_lines : HashMap String I64 := Smap.empty

def source (module : String) (mote : String) (external : Bool) (text : String) : Trellis.Source :=
    let decls : List Decl := match try_parse_decls_strict text Option.none { Result.ok ds => ds,
        Result.err _ => List.empty } in
    { module := module, mote := mote, file := "", external := external, decls := decls, lines := no_lines }

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

def g : Trellis.Graph := extracted.graph

def has_decl (id : String) (kind : String) : Bool :=
    List.any (fn (d : Trellis.DeclNode) => String.beq d.id id && String.beq d.kind kind) g.decls

def has_edge (from : String) (to : String) (axis : String) : Bool :=
    List.any (fn (e : Trellis.Edge) => String.beq e.from from && String.beq e.to to && String.beq e.axis axis) g.edges

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
    g.unresolved >= 1 && List.any (fn (n : String) => String.beq n "mystery") extracted.unresolved
        && Bool.not (List.any (fn
            (e : Trellis.Edge) => String.beq e.from "demo::main::local_only" && String.contains e.to "mystery") g.edges)

#[test]
def test_externals_are_marked : Bool :=
    List.any (fn (d : Trellis.DeclNode) => String.beq d.id "other::util::helper" && d.external) g.decls

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
            && String.beq e.to "demo::noisy::Pt") noisy_g.graph.edges

#[test]
def test_two_constructors_are_one_edge : Bool :=
    List.length (List.filter (fn (e : Trellis.Edge) =>
        String.beq e.from "demo::noisy::twice" && String.beq e.to "demo::util::Shape"
            && String.beq e.axis "b") noisy_g.graph.edges) == 1

#[test]
def test_wildcards_and_type_variables_are_not_misses : Bool :=
    Bool.not (List.any (fn
        (n : String) => String.beq n "_" || String.beq n "A" || String.is_empty n) noisy_g.unresolved)
