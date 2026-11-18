/// The wire codec: a graph survives encode/decode, and a file that is not a
use std::list {List.any}
/// trellis graph is rejected by name.

use lib::model {
    Trellis.ModuleNode, Trellis.DeclNode, Trellis.Edge, Trellis.Graph, Trellis.Graph.encode, Trellis.Graph.decode,
    Trellis.decl_id, Trellis.DeclNode.is_proof,
}

def m1 : Trellis.ModuleNode := { path := "lang::typecheck::infer", mote := "lang",
    file := "lang/src/typecheck/infer.mo", external := false }
def m2 : Trellis.ModuleNode := { path := "std::list", mote := "std", file := "std/src/list.mo", external := true }

def d (m : Trellis.ModuleNode) (name : String) (kind : String) (attrs : List String)
    (sort : String) : Trellis.DeclNode :=
    { id := Trellis.decl_id m.path name, name := name, module := m.path, mote := m.mote, kind := kind,
        vis := "pub", line := 12, attrs := attrs, sort := sort, doc := "lang/typecheck/infer.html#def.check",
            external := m.external }

def sample : Trellis.Graph :=
    { roots := ["lang"], modules := [m1, m2],
        decls := [d m1 "check" "def" ["partial", "terminating"] "", d m1 "infer" "def" List.empty "",
            d m2 "List.map" "def" List.empty "", d m1 "refl_ok" "def" ["proof"] "Prop"],
        edges := [{ from := "lang::typecheck::infer::check", to := "lang::typecheck::infer::infer", axis := "b" },
            { from := "lang::typecheck::infer::infer", to := "std::list::List.map", axis := "s" }],
        refs := 10, resolved := 8, unresolved := 2 }

def round : Result String Trellis.Graph := Trellis.Graph.decode (Trellis.Graph.encode sample)

#[test]
def test_round_trip_counts : Bool :=
    match round {
        Result.err _ => false,
        Result.ok g =>
            List.length g.modules == 2 && List.length g.decls == 4 && List.length g.edges == 2
                && g.refs == 10 && g.unresolved == 2 && List.length g.roots == 1,
    }

#[test]
def test_round_trip_decl_fields : Bool :=
    match round {
        Result.err _ => false,
        Result.ok g =>
            match g.decls {
                List.empty => false,
                List.cons first _ =>
                    String.beq first.id "lang::typecheck::infer::check" && String.beq first.mote "lang"
                        && first.line == 12 && List.length first.attrs == 2
                        && String.beq first.doc "lang/typecheck/infer.html#def.check" && Bool.not first.external,
            },
    }

#[test]
def test_round_trip_edges_keep_ids_and_axis : Bool :=
    match round {
        Result.err _ => false,
        Result.ok g =>
            match List.reverse g.edges {
                List.empty => false,
                List.cons last _ =>
                    String.beq last.from "lang::typecheck::infer::infer" && String.beq last.to "std::list::List.map"
                        && String.beq last.axis "s",
            },
    }

#[test]
def test_external_comes_from_the_module : Bool :=
    match round {
        Result.err _ => false,
        Result.ok g => List.any (fn (x : Trellis.DeclNode) => x.external && String.beq x.mote "std") g.decls,
    }

#[test]
def test_proof_by_sort_or_attr : Bool :=
    Trellis.DeclNode.is_proof (d m1 "a" "def" List.empty "Prop") && Trellis.DeclNode.is_proof
        (d m1 "b" "def" ["proof"] "")
        && Bool.not (Trellis.DeclNode.is_proof (d m1 "c" "def" List.empty ""))

#[test]
def test_rejects_other_files : Bool :=
    match Trellis.Graph.decode "{\"schema\": 1}" {
        Result.err why => String.contains why "trellis",
        Result.ok _ => false,
    }
