/// Tests moved out of `codegen::qualify` so the production module stays readable.

use std::path {Path}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use std::bench {Bench.now}
use lang::types {
    Attribute, Decl, Def, Identifier, LocalScope, ModulePath, NamePath, Scope, StructField,
    TypeConstraint, binder_named, hole, lam, many, named, package_private, sentinel,
    module_path_to_string_colon, show_identifier, show_module_path, show_name_path, use_items, use_name, var,
}
use lang::module {ModuleInfo, bench_step, best_effort_failed, elaborate_module_decls_reporting}
use lang::scope {
    OpenAlias, alias_map_empty, alias_map_insert, alias_map_lookup,
    build_scope_from_decls, collect_open_aliases, modpath_eq, modpath_of, resolve_open_alias_decls,
}
use lib::free_names {collect_referenced_names, free_names_of_term}
use lib::symbols {bare_modpath, bare_npath, symbol_identifier}
use lang::name_text {unqualify_def_name}
use lib::util {join_semicolon_msgs}
use lib::test::support {list_contains_str, qtest_def}
use std::map {HashMap}
use std::list {List.intercalate}
use lib::errors {CodegenDiagnostic}
use lib::qualify {ambiguous_owner_msg, decl_def_name, identifier_names, qualify_modules, qualify_one_decl_name}
use lib::test::support {qtest_def}

/// The collision that crashed the self-compiled compiler: one bare name,
/// two modules. Both must survive, under distinct symbols.
#[test]
def test_qualify_same_name_in_two_modules_stays_distinct : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_def "shared" "x") List.empty);
    let b := qtest_module "b" (List.cons (qtest_def "shared" "y") List.empty);
    let r <- qualify_modules false (List.cons a (List.cons b List.empty));
    match r {
        Result.err _ => return false,
        Result.ok ms => do {
            let names := qtest_def_names ms;
            return (if list_contains_str names "a::shared"
                then list_contains_str names "b::shared"
                else false)
        },
    }
}

/// A local definition wins: `a`'s own `shared` is what `a` calls, even
/// though `b` declares the name too.
#[test]
def test_qualify_local_definition_wins : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_def "shared" "z")
        (List.cons (qtest_def "caller" "shared") List.empty));
    let b := qtest_module "b" (List.cons (qtest_def "shared" "y") List.empty);
    let r <- qualify_modules false (List.cons a (List.cons b List.empty));
    match r {
        Result.err _ => return false,
        Result.ok ms => return (list_contains_str (qtest_body_refs ms) "a::shared"),
    }
}

/// The dominant corpus shape: a bare cross-module call to a uniquely
/// named def, with no `use`/`open` naming it at all.
#[test]
def test_qualify_unique_owner_resolves_without_any_import : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_def "only_here" "w") List.empty);
    let b := qtest_module "b" (List.cons (qtest_def "caller" "only_here") List.empty);
    let r <- qualify_modules false (List.cons a (List.cons b List.empty));
    match r {
        Result.err _ => return false,
        Result.ok ms => return (list_contains_str (qtest_body_refs ms) "a::only_here"),
    }
}

/// An explicit `use X {n}` picks a winner when two modules declare `n`.
///
/// This test exists because that rule shipped DEAD: the alias's own
/// `qualified_name` is dot-joined (`b.shared`) while an emitted symbol
/// is `::`-joined (`b::shared`), and the comparison used the second
/// form, so it never matched anything. Nothing caught it, because the
/// import-set fallback happened to answer correctly for every ambiguous
/// name then in the corpus.
#[test]
def test_qualify_explicit_import_picks_the_declarer : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_def "shared" "x") List.empty);
    let b := qtest_module "b" (List.cons (qtest_def "shared" "y") List.empty);
    // `c` imports BOTH declarers, so the import-set fallback cannot
    // narrow it -- only the explicit `{shared}` item on `b` can. An
    // earlier version of this test imported `b` alone and passed even
    // with the rule reverted, which is exactly how the bug shipped.
    let use_a := Decl.use_d (bare_modpath "a") (UseFilter.use_items List.empty) false;
    let use_b := Decl.use_d (bare_modpath "b")
        (UseFilter.use_items (List.cons (UseItem.use_name (Identifier.id "shared")) List.empty)) false;
    let c := qtest_module "c" (List.cons use_a (List.cons use_b (List.cons (qtest_def "caller" "shared") List.empty)));
    let r <- qualify_modules false (List.cons a (List.cons b (List.cons c List.empty)));
    match r {
        Result.err _ => return false,
        Result.ok ms => return (list_contains_str (qtest_body_refs ms) "b::shared"),
    }
}

/// A struct field's DEFAULT is an executable term and must be qualified
/// like any body. The checker splices it into every struct literal that
/// omits the field, so leaving it bare while its target is renamed makes
/// those literals fail to elaborate -- and because codegen elaboration
/// is best-effort, that surfaces several stages later as an unrelated
/// gate firing. `lang/types.mo`'s `ScopeData.def_params` (defaulting to
/// `HashMap.map HashMap.empty_buckets`) is the real instance of this.
#[test]
def test_qualify_rewrites_struct_field_defaults : IO Bool := do {
    let helper := qtest_def "make_empty" "z";
    let fld := StructField.mk (Identifier.id "f") Term.hole
        (Option.some (Term.var sentinel (DebugName.named (Identifier.id "make_empty"))))
        Multiplicity.many;
    let st := Decl.struct_d (Struct.mk (Identifier.id "Holder") (List.cons fld List.empty) List.empty Visibility.package_private);
    let a := qtest_module "a" (List.cons helper (List.cons st List.empty));
    let r <- qualify_modules false (List.cons a List.empty);
    match r {
        Result.err _ => return false,
        Result.ok ms => return (list_contains_str (struct_default_ref_names ms) "a::make_empty"),
    }
}

/// One FILE registered under two module paths is not an ambiguity --
/// `init/string.mo` arrives as both `string` and `init.string`, and
/// treating those as rival declarers made every `String.*` reference in
/// the corpus unresolvable.
#[test]
def test_qualify_same_file_under_two_paths_is_not_ambiguous : IO Bool := do {
    let decls := List.cons (qtest_def "shared" "x") List.empty;
    let short_ := ModuleInfo.mk (bare_modpath "string") (Path.unsafe "init/src/string.mo") decls;
    let long_ := ModuleInfo.mk (bare_modpath "init.string") (Path.unsafe "init/src/string.mo") decls;
    let caller := qtest_module "user" (List.cons (qtest_def "caller" "shared") List.empty);
    let r <- qualify_modules false (List.cons short_ (List.cons long_ (List.cons caller List.empty)));
    match r {
        Result.err _ => return false,
        // The longer path wins, and the duplicate module is dropped
        // rather than compiled twice under two symbols.
        Result.ok ms => return (list_contains_str (qtest_body_refs ms) "init.string::shared"),
    }
}

/// Two declarers and no import saying which: refusing to guess is the
/// whole point -- silently picking one is what the old flat namespace
/// did, and what crashed the compiler.
#[test]
def test_qualify_ambiguous_reference_is_an_error : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_def "shared" "x") List.empty);
    let b := qtest_module "b" (List.cons (qtest_def "shared" "y") List.empty);
    let c := qtest_module "c" (List.cons (qtest_def "caller" "shared") List.empty);
    let r <- qualify_modules false (List.cons a (List.cons b (List.cons c List.empty)));
    match r {
        Result.err _ => return true,
        Result.ok _ => return false,
    }
}

/// `String.a` and `String_a` must not become one symbol. They did under
/// the old `replace_dots_with_underscores` mangling, which is why the
/// symbol is now the source name verbatim.
#[test]
def test_qualify_dotted_and_underscored_names_stay_distinct : IO Bool := do {
    let a := qtest_module "m" (List.cons (qtest_def "String.a" "x")
        (List.cons (qtest_def "String_a" "y") List.empty));
    let r <- qualify_modules false (List.cons a List.empty);
    match r {
        Result.err _ => return false,
        Result.ok ms => do {
            let names := qtest_def_names ms;
            return (if list_contains_str names "m::String.a"
                then list_contains_str names "m::String_a"
                else false)
        },
    }
}

// --- Collision matrix, item 5.0: type-level decls (inductive/struct/
// class) are NOT qualified by `qualify_one_decl_name` today -- its match
// has explicit arms only for `def_d`/`instance_d`/`infix_d`, falling
// through `_ => d` unchanged for everything else (see that function's
// own body, above). Two modules declaring the same-named type/struct/
// class collide exactly the way def names used to before this file
// existed (see this file's header comment, and the historical
// `inductive_bare_name` crash it cites) -- these probes are RED until
// item 5.1 extends `qualify_one_decl_name` to those variants.
//
// NOT covered here, deliberately: same-named CONSTRUCTOR in two
// different types. That class of ambiguity is a DIFFERENT mechanism --
// `Con`/`MatchCase` dispatch already keys by the owning inductive's
// `NamePath` (stage 11.4, `unify-check-compile-test-elaboration.md`),
// so a bare ctor-name collision across unrelated types is already
// disambiguated downstream regardless of whether the INDUCTIVE's own
// name is qualified here. Re-verify this still holds once 5.1 actually
// renames inductives (a ctor's `typ_name` must track the rename).
// Same-named CLASS + INSTANCE is also not a separate cell: `instance_d`
// is already qualified (see the explicit arm above) -- only the class
// itself is the gap, covered by the class probe below.

/// RED: both modules' `Foo` stay bare "Foo" after `qualify_modules` --
/// the second silently collides with the first instead of becoming
/// `a::Foo`/`b::Foo`.
#[test]
def test_qualify_same_named_type_in_two_modules_stays_distinct : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_type "Foo") List.empty);
    let b := qtest_module "b" (List.cons (qtest_type "Foo") List.empty);
    let r <- qualify_modules false (List.cons a (List.cons b List.empty));
    match r {
        Result.err _ => return false,
        Result.ok ms => do {
            let names := qtest_type_names ms;
            return (if list_contains_str names "a::Foo"
                then list_contains_str names "b::Foo"
                else false)
        },
    }
}

/// Same probe, module list reversed -- the collision (or its fix) must
/// not depend on load order.
#[test]
def test_qualify_same_named_type_module_order_swapped_stays_distinct : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_type "Foo") List.empty);
    let b := qtest_module "b" (List.cons (qtest_type "Foo") List.empty);
    let r <- qualify_modules false (List.cons b (List.cons a List.empty));
    match r {
        Result.err _ => return false,
        Result.ok ms => do {
            let names := qtest_type_names ms;
            return (if list_contains_str names "a::Foo"
                then list_contains_str names "b::Foo"
                else false)
        },
    }
}

/// RED: two same-named structs with genuinely DIFFERENT fields must both
/// survive, under their own qualified name, with their own field list
/// intact (not merged, not overwritten by the other's).
#[test]
def test_qualify_same_named_struct_with_different_fields_stays_distinct : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_struct "Holder" (List.cons (qtest_field "x") List.empty)) List.empty);
    let b := qtest_module "b" (List.cons (qtest_struct "Holder" (List.cons (qtest_field "y") List.empty)) List.empty);
    let r <- qualify_modules false (List.cons a (List.cons b List.empty));
    match r {
        Result.err _ => return false,
        Result.ok ms => do {
            let entries := qtest_struct_entries ms;
            return (if qtest_struct_has_entry entries "a::Holder" "x"
                then qtest_struct_has_entry entries "b::Holder" "y"
                else false)
        },
    }
}

/// RED: same shape as the type/struct probes, for `class_d`.
#[test]
def test_qualify_same_named_class_in_two_modules_stays_distinct : IO Bool := do {
    let a := qtest_module "a" (List.cons (qtest_class "Foo") List.empty);
    let b := qtest_module "b" (List.cons (qtest_class "Foo") List.empty);
    let r <- qualify_modules false (List.cons a (List.cons b List.empty));
    match r {
        Result.err _ => return false,
        Result.ok ms => do {
            let names := qtest_class_names ms;
            return (if list_contains_str names "a::Foo"
                then list_contains_str names "b::Foo"
                else false)
        },
    }
}

/// Item 5.1 regression: a lam's own ANNOTATION inside a def body names a
/// type decl that qualification renamed -- but the annotation is the
/// body-side twin of `Def.typ`'s pi-chain, which `resolve_open_alias_def`
/// deliberately never rewrites. Rewriting only the annotation minted a
/// qualified-vs-bare type mismatch that failed elaboration for every
/// match arm comparing a param against a constructor or a call (prelude's
/// own `Nat.add` was the live canary). The annotation stays source-spelled;
/// the read side tolerates the bare spelling (`scope_find_inductive`'s
/// unique-suffix fallback).
#[test]
def test_qualify_lam_annotation_stays_source_spelled : IO Bool := do {
    let body := Term.lam (binder_named (Identifier.id "x"))
        (Term.var sentinel (DebugName.named (Identifier.id "Foo"))) Term.hole;
    let df := Def.mk (bare_npath "f") Term.hole body
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private List.empty;
    let a := qtest_module "a" (List.cons (qtest_type "Foo") (List.cons (Decl.def_d df) List.empty));
    let r <- qualify_modules false (List.cons a List.empty);
    match r {
        Result.err _ => return false,
        Result.ok ms => do {
            let anns := qtest_lam_annotations ms;
            return (if list_contains_str anns "Foo"
                then Bool.not (list_contains_str anns "a::Foo")
                else false)
        },
    }
}

/// Item 5.1 regression (#15): post-qualify, a def whose whole body is a
/// bare-annotated lam still ELABORATES. The body is checked against a
/// hole, so the lam takes the inferring arm and the annotation is
/// type-checked AS A TERM -- its bare head (`Pair`, renamed to `a::Pair`
/// by the same qualification pass that leaves annotations source-spelled)
/// must resolve through the checker's free-var path, whose `def_refs`
/// lookup is exact-only. `resolve_free_var_def` retries the miss by
/// unique qualified suffix; pre-#15 every def of this shape failed with
/// `unknown variable 'Pair'` (`lang.mote::Mote.table_keys` was the
/// corpus canary).
#[test]
def test_qualify_bare_annotation_head_elaborates : IO Bool := do {
    let body := Term.lam (binder_named (Identifier.id "p"))
        (Term.var sentinel (DebugName.named (Identifier.id "Pair")))
        (Term.var 0 (DebugName.named (Identifier.id "p")));
    let df := Def.mk (bare_npath "g") Term.hole body
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private List.empty;
    let a := qtest_module "a" (List.cons (qtest_type "Pair") (List.cons (Decl.def_d df) List.empty));
    let r <- qualify_modules false (List.cons a List.empty);
    match r {
        Result.err _ => return false,
        Result.ok ms => return (match qtest_elab_failures_of_modules ms { List.empty => true, List.cons _ _ => false }),
    }
}

/// `::` separates the module from the name, so the source name is
/// recoverable exactly -- which is what the native tables, keyed on what
/// the source wrote, depend on.
#[test]
def test_unqualify_recovers_the_source_name : Bool :=
    if String.beq (unqualify_def_name "init.string::String.beq") "String.beq"
    then if String.beq (unqualify_def_name "plain_name") "plain_name"
        then String.beq (unqualify_def_name "cli.main::main") "main"
        else false
    else false

/// Diagnostics spell module paths the way source does (`a::b`), not with
/// the internal dot-joined key spelling.
#[test]
def test_ambiguous_owner_msg_spells_module_paths_with_colons : Bool :=
    let a : ModulePath := ModulePath.mk [Identifier.id "std", Identifier.id "io"] in
    let b : ModulePath := ModulePath.mk [Identifier.id "std", Identifier.id "fs"] in
    String.beq (CodegenDiagnostic.render (ambiguous_owner_msg a "read" [b]))
        "`read` is referenced from std::io but declared in std::fs -- add an explicit `use <module> {read}` to say which"

#[partial]
def qtest_module (name : String) (decls : List Decl) : ModuleInfo :=
    ModuleInfo.mk (bare_modpath name) (Path.unsafe "") decls

/// `def <name> := <body_ref>` -- a def whose whole body is one bare
/// reference, which is all these tests need to watch a reference move.
#[partial]
def qtest_def_names (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (qtest_names_of_decls (m.decl_list)) (qtest_def_names rest),
    }

#[partial]
def qtest_names_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match decl_def_name d {
            Option.some n => List.cons (show_name_path n) (qtest_names_of_decls rest),
            Option.none => qtest_names_of_decls rest,
        },
}

#[partial]
def qtest_body_refs (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (qtest_refs_of_decls (m.decl_list)) (qtest_body_refs rest),
    }

#[partial]
def qtest_refs_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.def_d dd =>
                match dd {
                    Def.mk {name := _n, typ := _t, term := term_, constraints := _c, attrs := _a, vis := _v, ..} =>
                        List.append (collect_referenced_names term_ List.empty) (qtest_refs_of_decls rest),
                },
            _ => qtest_refs_of_decls rest,
        },
}

#[partial]
def struct_default_ref_names (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (struct_default_ref_names_of_decls (m.decl_list)) (struct_default_ref_names rest),
    }

#[partial]
def struct_default_ref_names_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.struct_d st =>
                match st {
                    Struct.mk _n fields _attrs _v => List.append (struct_field_default_refs fields) (struct_default_ref_names_of_decls rest),
                },
            _ => struct_default_ref_names_of_decls rest,
        },
}

#[partial]
def struct_field_default_refs (fields : List StructField) : List String := match fields {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            StructField.mk _n _t default _m =>
                match default {
                    Option.some t => List.append (identifier_names (free_names_of_term List.empty t)) (struct_field_default_refs rest),
                    Option.none => struct_field_default_refs rest,
                },
        },
}

#[partial]
def qtest_type (name : String) : Decl :=
    Decl.inductive_d (Inductive.mk (bare_npath name) List.empty Term.hole List.empty List.empty Visibility.package_private)

#[partial]
def qtest_struct (name : String) (fields : List StructField) : Decl :=
    Decl.struct_d (Struct.mk (Identifier.id name) fields List.empty Visibility.package_private)

#[partial]
def qtest_class (name : String) : Decl :=
    Decl.class_d (Class.mk (Identifier.id name) List.empty List.empty List.empty Visibility.package_private Option.none)

#[partial]
def qtest_field (name : String) : StructField :=
    StructField.mk (Identifier.id name) Term.hole Option.none Multiplicity.many

#[partial]
def qtest_type_names (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (qtest_type_names_of_decls (m.decl_list)) (qtest_type_names rest),
    }

#[partial]
def qtest_type_names_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.inductive_d ind =>
                match ind {
                    Inductive.mk name _ _ _ _ _ => List.cons (show_name_path name) (qtest_type_names_of_decls rest),
                },
            _ => qtest_type_names_of_decls rest,
        },
}

#[partial]
def qtest_struct_entries (modules : List ModuleInfo) : List (Pair String (List String)) :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (qtest_struct_entries_of_decls (m.decl_list)) (qtest_struct_entries rest),
    }

#[partial]
def qtest_struct_entries_of_decls (decls : List Decl) : List (Pair String (List String)) := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.struct_d st =>
                match st {
                    Struct.mk name fields _attrs _vis =>
                        List.cons (Pair.pair (show_identifier name) (qtest_field_names fields)) (qtest_struct_entries_of_decls rest),
                },
            _ => qtest_struct_entries_of_decls rest,
        },
}

#[partial]
def qtest_field_names (fields : List StructField) : List String := match fields {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            StructField.mk name _typ _default _mult => List.cons (show_identifier name) (qtest_field_names rest),
        },
}

#[partial]
def qtest_struct_has_entry (entries : List (Pair String (List String))) (name : String) (field : String) : Bool :=
    match entries {
        List.empty => false,
        List.cons e rest =>
            match e {
                Pair.pair n fs => if String.beq n name
                    then list_contains_str fs field
                    else qtest_struct_has_entry rest name field,
            },
    }

#[partial]
def qtest_class_names (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (qtest_class_names_of_decls (m.decl_list)) (qtest_class_names rest),
    }

#[partial]
def qtest_class_names_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.class_d cls =>
                match cls {
                    Class.mk name _params _constraints _methods _vis _ => List.cons (show_identifier name) (qtest_class_names_of_decls rest),
                },
            _ => qtest_class_names_of_decls rest,
        },
}

#[partial]
def qtest_lam_annotations (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (qtest_lam_annotations_of_decls (m.decl_list)) (qtest_lam_annotations rest),
    }

#[partial]
def qtest_lam_annotations_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.def_d df =>
                match df {
                    Def.mk _n _typ term _c _a _v _p =>
                        match term {
                            Term.lam _b ann _body => List.append (identifier_names (free_names_of_term List.empty ann)) (qtest_lam_annotations_of_decls rest),
                            _ => qtest_lam_annotations_of_decls rest,
                        },
                },
            _ => qtest_lam_annotations_of_decls rest,
        },
}

/// The decls that fail to elaborate once the whole-program scope is
/// built from the QUALIFIED modules -- the pipeline shape
/// `compile_input_of_modules` runs after this pass.
#[partial]
def qtest_elab_failures_of_modules (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest =>
            let sd := build_scope_from_decls m.path m.decl_list in
            let scope : Scope := { module_id := m.path, scope := sd, parent := Option.none, incomplete_match_ok := false } in
            let locals : LocalScope := { vars := List.empty, parent := Option.none } in
            List.append (best_effort_failed (elaborate_module_decls_reporting scope m.decl_list locals))
                (qtest_elab_failures_of_modules rest),
    }
