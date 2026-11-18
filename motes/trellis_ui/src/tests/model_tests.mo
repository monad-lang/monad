/// The wire codec: a graph survives encode/decode, and a file that is not a
/// trellis graph is rejected by name.

use std::list {List.any, List.all}
use lib::model {
    Trellis.ModuleNode, Trellis.DeclNode, Trellis.Edge, Trellis.Graph, Trellis.Graph.encode, Trellis.Graph.decode,
    Trellis.decl_id, Trellis.DeclNode.is_proof, Trellis.escape_field,
}

def m1 : Trellis.ModuleNode := { path := "lang::typecheck::infer", mote := "lang",
    file := "lang/src/typecheck/infer.mo", external := false, docs := "The checker.\n\nSee `infer`." }
def m2 : Trellis.ModuleNode := { path := "std::list", mote := "std", file := "std/src/list.mo", external := true,
    docs := "" }

/// Docs with every character the wire format must carry through a field.
def check_docs : String := "Check `a\\b`, `\\n` and `\\\\`.\n\n```\nx\ty\n```\n"

def d (m : Trellis.ModuleNode) (name : String) (kind : String) (attrs : List String)
    (sort : String) : Trellis.DeclNode :=
    { id := Trellis.decl_id m.path name, name := name, module := m.path, mote := m.mote, kind := kind,
        vis := "pub", line := 12, attrs := attrs, sort := sort, href := "lang/typecheck/infer.html#def.check",
        docs := if String.beq name "check" then check_docs else "", external := m.external }

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
                        && String.beq first.href "lang/typecheck/infer.html#def.check" && Bool.not first.external,
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

#[test]
def test_round_trip_docs_as_one_field : Bool :=
    match round {
        Result.err _ => false,
        Result.ok g =>
            match g.decls {
                List.empty => false,
                List.cons first rest =>
                    String.beq first.docs check_docs
                        && List.all (fn (x : Trellis.DeclNode) => String.is_empty x.docs) rest
                        && List.any (fn (mo : Trellis.ModuleNode) => String.beq mo.docs "The checker.\n\nSee `infer`.")
                            g.modules,
            },
    }

#[test]
def test_version_1_still_decodes : Bool :=
    let v1 : String := "trellis\t1\nR\tlang\nM\tlang::m\tlang\tm.mo\t0\nD\t0\tf\tdef\tpub\t3\t\t\t\nS\t1\t1\t0" in
    match Trellis.Graph.decode v1 {
        Result.err _ => false,
        Result.ok g => match g.decls { List.cons x _ => String.is_empty x.docs && String.beq x.id "lang::m::f",
            List.empty => false },
    }

#[test]
def test_escaped_docs_are_one_line : Bool :=
    let e : String := Trellis.escape_field check_docs in
    Bool.not (String.contains e "\n") && Bool.not (String.contains e "\t")
