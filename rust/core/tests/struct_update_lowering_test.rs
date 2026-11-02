//! Regression test: a nested struct update must lower even when the INNER
//! base's type is never named in the enclosing def's own source or type.
//!
//! `desugar_struct_literals`' `StructUpdate` arm records a field-projection
//! `Match` per un-overridden field, resolved to the base's INDUCTIVE atom.
//! An ordinary inductive's own bare name is deliberately not a
//! `known_globals` entry (`register_inductive` records it only in
//! `structs.inductive_paths`), so when the def's own source never mentions
//! that type the atom was missing from the def's captured `atom_paths` and
//! `lower_program` failed with `UnresolvedAtom`.
//!
//! Reproduced while building `cli/src/main.mo`:
//! `lang.typecheck.type_kinds.scope_with_inds` updates a `ScopeData` base
//! (`scope_data_empty`) without naming `ScopeData` anywhere in its own
//! signature -- the whole rung-1 nightly build died at lowering with
//! `lower: UnresolvedAtom(Atom(5404266))`.

use monad_core::core_check_module::check_all_modules_capturing_core;
use monad_core::lower_core_ir::lower_program;
use monad_core::term::Decl;
use monad_core::term::module::{default_modules, load_decls_from_text_with_path};
use monad_core::term::{ModulePath, NamePath, SourceContext};

/// See `core_program_capture_test.rs`'s identical helper: the prelude's own
/// inductives are captured only when its raw decls are passed in explicitly.
fn prelude_decls() -> Vec<SourceContext<Decl>> {
  let text = include_str!("../../../init/src/prelude.mo");
  load_decls_from_text_with_path(text, &Default::default()).expect("parse init/src/prelude.mo")
}

const SOURCE: &str = r#"
use init

struct Inner { x : I64, y : I64 }
struct Outer { a : I64, inner : Inner }

def inner_base : Inner := { x := 1, y := 2 }

// `Inner` is named in `inner_base`'s signature, but NOT anywhere in
// `bump`: its inner update base (`inner_base`) only supplies the type by
// inference.
def bump (o : Outer) : Outer := { o with inner := { inner_base with x := 5 } }
"#;

#[test]
fn nested_struct_update_lowers_when_inner_base_type_is_not_named() {
  let loaded = default_modules().expect("default_modules");
  let path = ModulePath::top("'structupdatetest");
  let prelude_path = ModulePath::top("'prelude");
  let decls = load_decls_from_text_with_path(SOURCE, &Default::default()).expect("parse");

  let program = check_all_modules_capturing_core(
    &[(prelude_path, prelude_decls()), (path.clone(), decls)],
    &loaded,
  )
  .expect("check_all_modules_capturing_core");

  let bump_path = NamePath::top("bump");
  assert!(
    program.defs.contains_key(&bump_path),
    "expected `bump` captured, got keys: {:?}",
    program.defs.keys().collect::<Vec<_>>()
  );

  lower_program(&program).expect("lower_program");
}
