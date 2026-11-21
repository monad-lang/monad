/// `meta_env_decls`: the defs reachable from the roots, elaborated once, in
/// input order, with every non-def kept, and a def that fails to elaborate
/// poisoned so lowering it fails instead of running its unelaborated body.
use lang::types {
    DebugName, Decl, Def, Identifier, Literal, ModulePath, NamePath, NumSuffix, Operator, Term, Visibility,
    sentinel, show_name_path,
}
use lang::meta_env {meta_env_decls}
use lang::lower_core_ir {lower_ctx_from_decls, lower_root}
use lang::typecheck::meta_eval {show_lower_error_debug}
use std::list {List.intercalate}

def ref (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

def mk_def (name : String) (body : Term) : Decl :=
    let d : Def := {
        name := NamePath.mk [Identifier.id name],
        typ := Term.hole,
        term := body,
        constraints := List.empty,
        attrs := List.empty,
        vis := Visibility.package_private,
        params := List.empty,
    } in
    Decl.def_d d

def name_of (d : Decl) : String := match d {
    Decl.def_d df => show_name_path df.name,
    _ => "<non-def>",
}

def names (ds : List Decl) : String := List.intercalate "," (List.map name_of ds)

def no_elab (d : Decl) : Result String Decl := Result.ok d

/// Stands in for elaboration resolving a class call: `uses_class` gains a
/// reference to `instance_method` its source never spelled.
def elab_adds_ref (d : Decl) : Result String Decl := match d {
    Decl.def_d df => add_ref_to_uses_class df.name df,
    Decl.infix_d op target vis => Result.ok (Decl.infix_d op target vis),
    _ => Result.err "the test graphs hold only defs and one infix",
}

def add_ref_to_uses_class (name : NamePath) (df : Def) : Result String Decl :=
    if String.beq (show_name_path name) "uses_class"
    then Result.ok (mk_def "uses_class" (ref "instance_method"))
    else Result.ok (Decl.def_d df)

def graph : List Decl := [
    mk_def "helper" (Term.hole),
    mk_def "unrelated" (ref "helper"),
    mk_def "meta_fn" (Term.app (ref "helper") (ref "println")),
    Decl.infix_d (Operator.mk "+") (NamePath.mk [Identifier.id "add"]) Visibility.pub_,
    mk_def "IO.println" (Term.hole),
    mk_def "instance_method" (Term.hole),
    mk_def "uses_class" (Term.hole),
]

#[test]
def test_keeps_reachable_defs_and_non_defs_in_order : Bool :=
    String.beq (names (meta_env_decls no_elab graph ["meta_fn"])) "helper,meta_fn,<non-def>,IO.println"

#[test]
def test_follows_references_elaboration_adds : Bool :=
    String.beq (names (meta_env_decls elab_adds_ref graph ["uses_class"])) "<non-def>,instance_method,uses_class"

#[test]
def test_no_roots_keeps_only_non_defs : Bool :=
    String.beq (names (meta_env_decls no_elab graph List.empty)) "<non-def>"

/// A bound local is not a reference: a lambda parameter named `helper`
/// keeps the `helper` def out.
#[test]
def test_bound_local_is_not_a_reference : Bool :=
    let local : Term := Term.var 0 (DebugName.named (Identifier.id "helper")) in
    let ds : List Decl := [mk_def "helper" (Term.hole), mk_def "root" local] in
    String.beq (names (meta_env_decls no_elab ds ["root"])) "root"

def one : Term := Term.lit (Literal.num 1 NumSuffix.i64)

/// Elaboration rejects `broken` and accepts everything else.
def elab_rejects_broken (d : Decl) : Result String Decl := match d {
    Decl.def_d df => reject_broken df.name df,
    Decl.infix_d op target vis => Result.ok (Decl.infix_d op target vis),
    _ => Result.err "the test graphs hold only defs and one infix",
}

def reject_broken (name : NamePath) (df : Def) : Result String Decl :=
    if String.beq (show_name_path name) "broken"
    then Result.err "type mismatch in broken"
    else Result.ok (Decl.def_d df)

def poison_graph : List Decl := [
    mk_def "broken" one,
    mk_def "uses_broken" (ref "broken"),
    mk_def "fine" one,
]

def env_root : ModulePath := ModulePath.mk [Identifier.id "meta_env_tests"]

/// What lowering `root` against `ds` reports: "ok", or the error.
def lower_outcome (ds : List Decl) (root : String) : String :=
    match lower_root (lower_ctx_from_decls env_root ds) (NamePath.mk [Identifier.id root]) {
        Result.ok _ => "ok",
        Result.err e => show_lower_error_debug e,
    }

/// A meta-def that reaches a def whose elaboration failed fails to lower,
/// and the error names the def and the elaboration error. Before, the
/// unelaborated body was lowered and evaluated silently.
#[test]
def test_reaching_a_failed_def_fails_with_its_error : Bool :=
    let env := meta_env_decls elab_rejects_broken poison_graph ["uses_broken"] in
    let out := lower_outcome env "uses_broken" in
    String.contains out "<elaboration failed> broken" && String.contains out "type mismatch in broken"

/// The same def, unelaborated, lowers fine: that is the silent path the
/// poison closes.
#[test]
def test_unpoisoned_body_would_have_lowered : Bool :=
    String.beq (lower_outcome poison_graph "uses_broken") "ok"

/// A failed def that is in the environment but never lowered does not
/// fail a meta-def that does not reach it.
#[test]
def test_unreached_failed_def_is_harmless : Bool :=
    let env := meta_env_decls elab_rejects_broken poison_graph ["uses_broken", "fine"] in
    String.beq (lower_outcome env "fine") "ok"

/// A reference the closure cannot match by name (`M.helper` through a
/// module alias) leaves the def out, and lowering then fails on the
/// unresolved name: a miss is an error, never a different def.
#[test]
def test_closure_miss_fails_lowering : Bool :=
    let ds : List Decl := [mk_def "helper" one, mk_def "root" (ref "M.helper")] in
    let env := meta_env_decls no_elab ds ["root"] in
    String.beq (names env) "root" && String.contains (lower_outcome env "root") "le_unresolved_name M.helper"
