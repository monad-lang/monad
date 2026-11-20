// A small fixture graph for the trellis_ui suites (no #[test] defs here).
//
//   lang::typecheck::infer   check -> infer -> unify (lang::typecheck::unify)
//                            infer -> List.map (std::list, external)
//   lang::typecheck::unify   unify -> whnf ; whnf -> unify (a cycle)
//   lang::module             load (no edges)
//   lang::typecheck::infer   check_tests (#[test])
//   proofs::nat              add_zero (Prop), uses plus

use lib::model {Trellis.ModuleNode, Trellis.DeclNode, Trellis.Edge, Trellis.Graph, Trellis.decl_id}

def m (path : String) (mote : String) (external : Bool) : Trellis.ModuleNode :=
    { path := path, mote := mote, file := "", external := external, docs := "" }

def infer_m : Trellis.ModuleNode := m "lang::typecheck::infer" "lang" false
def unify_m : Trellis.ModuleNode := m "lang::typecheck::unify" "lang" false
def module_m : Trellis.ModuleNode := m "lang::module" "lang" false
def list_m : Trellis.ModuleNode := m "std::list" "std" true
def nat_m : Trellis.ModuleNode := m "proofs::nat" "proofs" false

def decl (mo : Trellis.ModuleNode) (name : String) (kind : String) (attrs : List String)
    (sort : String) : Trellis.DeclNode :=
    { id := Trellis.decl_id mo.path name, name := name, module := mo.path, mote := mo.mote, kind := kind,
        vis := "pub", line := 1, end_line := 1, attrs := attrs, sort := sort, href := "", docs := "",
        sig := if String.beq name "infer" then "pub def infer (t : Ty) : Ty :=" else "", external := mo.external }

def edge (a : String) (b : String) (axis : String) : Trellis.Edge := { from := a, to := b, axis := axis }

pub def fixture : Trellis.Graph :=
    { roots := ["lang", "proofs"], modules := [infer_m, unify_m, module_m, list_m, nat_m],
        decls := [decl infer_m "check" "def" List.empty "", decl infer_m "infer" "def" List.empty "",
            decl unify_m "unify" "def" List.empty "", decl unify_m "whnf" "def" List.empty "",
            decl module_m "load" "def" List.empty "", decl list_m "List.map" "def" List.empty "",
            decl infer_m "check_tests" "def" ["test"] "", decl nat_m "add_zero" "def" List.empty "Prop",
            decl nat_m "plus" "def" List.empty "", decl infer_m "Ty" "type" List.empty ""],
        edges := [edge "lang::typecheck::infer::check" "lang::typecheck::infer::infer" "b",
            edge "lang::typecheck::infer::infer" "lang::typecheck::unify::unify" "b",
            edge "lang::typecheck::infer::check" "lang::typecheck::unify::unify" "b",
            edge "lang::typecheck::infer::infer" "lang::typecheck::infer::Ty" "s",
            edge "lang::typecheck::infer::infer" "std::list::List.map" "b",
            edge "lang::typecheck::unify::unify" "lang::typecheck::unify::whnf" "b",
            edge "lang::typecheck::unify::whnf" "lang::typecheck::unify::unify" "b",
            edge "lang::typecheck::infer::check_tests" "lang::typecheck::infer::check" "b",
            edge "proofs::nat::add_zero" "proofs::nat::plus" "s"],
        refs := 9, resolved := 9, unresolved := 0 }
