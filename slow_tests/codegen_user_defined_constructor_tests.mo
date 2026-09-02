/// Regression tests for the user-defined-constructor-codegen-gap fix
/// (`plans/implementations/2026-08-29-user-defined-constructor-codegen-
/// gap.md`): `is_constructor_var`/`constructor_tag` (`lang/codegen/
/// emit.mo`) were closed, hardcoded whitelists of ~16 builtin
/// constructor names -- any OTHER constructor (every user-defined type,
/// AND any builtin constructor with 2+ params used directly, e.g.
/// `List.cons`) compiled to an ordinary call to a nonexistent global
/// (`llc: use of undefined value '@Foo_bar'`).
///
/// Fixed by: a dynamically-built `HashMap` (`build_constructor_tag_map`)
/// assigning every declared inductive's constructor a fresh, unique tag
/// (16+, past the hardcoded 0-15 builtin range) as a fallback for
/// `is_constructor_var`/`constructor_tag`; a real tag threaded into
/// `compile_constructor_decl`'s wrapper functions (previously hardcoded
/// to tag 0, colliding with `Unit.unit`); and generalizing
/// `try_compile_constructor_app_db` to flatten the WHOLE application
/// spine (any arity), not just a single immediately-applied argument.
///
/// Also fixed along the way: `string_find_last`/`extract_base_name`
/// (`lang/codegen/emit.mo`) had a genuine, previously-undiscovered
/// off-by-length bug (`String.slice`'s third argument is a LENGTH, not
/// an end index) that silently broke stripping a qualified name's own
/// type prefix -- the map lookups here would all have failed without it.
use io {IO}
open IO {println}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// The exact `Item.present`/`Item.absent` repro from the filed gap doc:
/// a user-defined, 2-constructor type, each with a field, referenced
/// both via constructor application AND match dispatch. Before the fix:
/// `llc: use of undefined value '@Item_present'`/`'@Item_absent'`, and
/// separately, match dispatch always took the first arm (both tag
/// comparisons resolved to the same fallback value).
#[test]
def test_user_defined_multi_constructor_type : IO Bool :=
    let source := r#"use io {IO}
type Item {
    present (val : I64),
    absent (unused : I64),
}
def describe (n : Item) : I64 :=
    match n {
        Item.present x => x,
        Item.absent _ => 99,
    }
def main (args : List String) : IO I64 := do {
    let a := describe (Item.present 42);
    let b := describe (Item.absent 0);
    return (I64.add a b)
}
"# in
    compile_source_run_expect source "test_user_defined_multi_constructor_type" 141

/// `List.cons`/`List.empty` used DIRECTLY (not via a stdlib helper) --
/// `List.cons` is a builtin 2-field constructor, hitting the exact same
/// bug as user-defined types once used outside the single-arg fast path.
/// Before the fix: `llc: use of undefined value '@List_cons'`.
#[test]
def test_builtin_multi_arg_constructor_list_cons : IO Bool :=
    let source := r#"use io {IO}
def main (args : List String) : IO I64 := do {
    let xs := List.cons 10 (List.cons 20 List.empty);
    match xs {
        List.cons a rest => match rest {
            List.cons b rest2 => return (I64.add a b),
            List.empty => return (-1),
        },
        List.empty => return (-2),
    }
}
"# in
    compile_source_run_expect source "test_builtin_multi_arg_constructor_list_cons" 30
