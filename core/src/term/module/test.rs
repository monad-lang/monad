use super::*;
// These tests exercise module-loading/scoping mechanics specifically
// against the OLD checker (unaffected by the new-checker-is-default
// cutover — see `Cargo.toml`'s `legacy-checker` feature) — imported here
// unconditionally rather than relying on `module.rs`'s own `use`, which is
// now gated behind that feature since production call sites no longer
// need it by default.
use crate::diag::Severity;
use crate::eval::r#type::type_check_module_decls;
use crate::parser::parse_file;

fn uses_of(source: &str) -> Vec<SourceContext<Use>> {
  parse_file(source.into())
    .unwrap()
    .decls
    .into_iter()
    .filter_map(|ctx| {
      let loc = ctx.loc.clone();
      let doc = ctx.doc.clone();
      match ctx.value {
        Decl::Use(u) => Some(SourceContext { loc, doc, value: u }),
        _ => None,
      }
    })
    .collect()
}

#[test]
fn test_bare_use_emits_warning() {
  let uses = uses_of("use IO\n");
  let warnings = bare_use_warnings(&uses, None);
  assert_eq!(warnings.len(), 1);
  assert_eq!(warnings[0].severity, Severity::Warning);
  assert!(warnings[0].message.contains("deprecated"));
  assert!(warnings[0].suggestions[0].message.contains("{*}"));
}

#[test]
fn test_braced_use_emits_no_warning() {
  let uses = uses_of("use IO {*}\n");
  assert!(bare_use_warnings(&uses, None).is_empty());
}
#[test]
fn test_simple_instance() {
  let mut loaded = LoadedModules::empty();

  let path = ModulePath::top("_");
  let parsed = parse_file(
    r#"
    class HAdd A B C {
      def add (a: A) (b : B) : C
    }
    type I64 {}

    @[native num_add]
    def I64.add (a b : I64) : I64

    instance HAdd I64 I64 I64 {
      def add (a b: I64) : I64 := I64.add a b
    }
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, parsed.decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let modu = module(
    path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  );
  loaded.add_module(modu);
  let global = loaded.global(&path).unwrap();
  let ins_key = InstanceKey::new(
    mpt("HAdd"),
    vec![],
    vec![
      param(id("A"), var("I64")),
      param(id("B"), var("I64")),
      param(id("C"), var("I64")),
    ],
  );
  global.find_instance(&ins_key).expect("instance not found");
}

#[test]
fn test_loaded_scopes_builds_all_scopes() {
  let mut loaded = LoadedModules::empty();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    type MyType {
      constructor
    }
    def my_def : MyType := MyType.constructor
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, parsed.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("scope should exist");

  assert!(global.find_ref(&mpt("my_def")).is_some());
  assert!(global.find_inductive(&mpt("MyType")).is_some());
}

#[test]
fn test_global_scope_data_includes_implicit_modules() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    use io
    open IO

    def test_def : IO Unit := println "test"
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, parsed.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("scope should exist");

  // Should have access to prelude types
  assert!(global.find_inductive(&mpt("Bool")).is_some());
  assert!(global.find_inductive(&mpt("Option")).is_some());
  assert!(global.find_inductive(&mpt("List")).is_some());
}

#[test]
fn test_global_scope_data_applies_opens() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    use io
    open IO

    def test_def : IO Unit := println "test"
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, parsed.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("scope should exist");

  // With open IO, println should be accessible directly
  assert!(global.find_ref(&mpt("println")).is_some());
}

#[test]
fn test_get_module_scope_returns_correct_scope() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    use io
    open IO

    def test_def : String := "hello"
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, parsed.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("scope should exist");

  // Should be able to get scope for prelude module
  let prelude_path = mpt("'prelude");
  let prelude_scope = global.get_module_scope(&prelude_path);
  assert!(prelude_scope.is_some());

  let prelude_scope = prelude_scope.unwrap();
  // Prelude scope should have prelude definitions
  assert!(prelude_scope.find_inductive(&mpt("Bool")).is_some());
  assert!(prelude_scope.find_inductive(&mpt("Option")).is_some());
}

#[test]
fn test_instance_resolution_module_restricted() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    use init
    use math

    def test_eq : Bool := 1 == 1
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, parsed.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("scope should exist");

  // Should find BEq instance for I64
  assert!(global.find_ref(&mpt("test_eq")).is_some());
}

#[test]
fn test_module_conflict_detection_bare_name_ambiguous() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_conflict_a");
  let path_b = ModulePath::top("test_conflict_b");

  let parsed_a = parse_file(
    r#"
    def shared_name : I64 := 1
    "#
    .into(),
  )
  .unwrap();
  let decls_a = type_check_module_decls(&path_a, parsed_a.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path_a.clone(),
    ParsedModule {
      decls: decls_a,
      module_doc: None,
    },
  ));

  let parsed_b = parse_file(
    r#"
    def shared_name : I64 := 2
    "#
    .into(),
  )
  .unwrap();
  let decls_b = type_check_module_decls(&path_b, parsed_b.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(
    path_b.clone(),
    ParsedModule {
      decls: decls_b,
      module_doc: None,
    },
  ));

  let path_c = ModulePath::top("test_conflict_c");
  let parsed_c = parse_file(&format!(
    r#"
    use {}
    use {}
    "#,
    path_a.as_str().unwrap(),
    path_b.as_str().unwrap(),
  ))
  .unwrap();
  let decls_c = type_check_module_decls(&path_c, parsed_c.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(
    path_c.clone(),
    ParsedModule {
      decls: decls_c,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path_c).expect("scope should exist");

  let result = global.find_any_ref(&mpt("shared_name"), &sort1());
  assert!(result.is_err());
  if let Err(ScopeError::AmbiguousName { name, candidates }) = result {
    assert_eq!(name, mpt("shared_name"));
    assert_eq!(candidates.len(), 2);
    assert!(
      candidates.contains(&path_a),
      "Expected {path_a} in candidates: {candidates:?}"
    );
    assert!(
      candidates.contains(&path_b),
      "Expected {path_b} in candidates: {candidates:?}"
    );
  } else {
    panic!("Expected AmbiguousName error, got: {result:?}");
  }

  let prefixed_a = path_a.clone().extend(mpt("shared_name"));
  assert!(global.find_ref(&prefixed_a).is_some());
  let prefixed_b = path_b.clone().extend(mpt("shared_name"));
  assert!(global.find_ref(&prefixed_b).is_some());
}

#[test]
fn test_selective_use_only_filter() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_sel_a");
  let parsed_a = parse_file(
    r#"
    def foo : I64 := 1
    def bar : I64 := 2
    "#
    .into(),
  )
  .unwrap();
  let decls_a = type_check_module_decls(&path_a, parsed_a.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path_a.clone(),
    ParsedModule {
      decls: decls_a,
      module_doc: None,
    },
  ));

  let path_b = ModulePath::top("test_sel_b");
  let parsed_b = parse_file(&format!("use {} {{foo}}", path_a.as_str().unwrap())).unwrap();
  let decls_b = type_check_module_decls(&path_b, parsed_b.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(
    path_b.clone(),
    ParsedModule {
      decls: decls_b,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path_b).expect("scope should exist");

  assert!(global.find_any_ref(&mpt("foo"), &sort1()).is_ok());
  assert!(global.find_any_ref(&mpt("bar"), &sort1()).is_err());
}

#[test]
fn test_use_glob_equivalent_to_bare() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_glob_a");
  let parsed_a = parse_file(
    r#"
    def foo : I64 := 1
    def bar : I64 := 2
    "#
    .into(),
  )
  .unwrap();
  let decls_a = type_check_module_decls(&path_a, parsed_a.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path_a.clone(),
    ParsedModule {
      decls: decls_a,
      module_doc: None,
    },
  ));

  let path_b = ModulePath::top("test_glob_b");
  let parsed_b = parse_file(&format!("use {} {{*}}", path_a.as_str().unwrap())).unwrap();
  let decls_b = type_check_module_decls(&path_b, parsed_b.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(
    path_b.clone(),
    ParsedModule {
      decls: decls_b,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path_b).expect("scope should exist");

  // `{*}` makes every name bare-accessible, same as old bare `use`.
  assert!(global.find_any_ref(&mpt("foo"), &sort1()).is_ok());
  assert!(global.find_any_ref(&mpt("bar"), &sort1()).is_ok());
}

#[test]
fn test_use_nested_submodule_makes_bare_name_and_qualified_access_available() {
  let loaded = default_modules().unwrap();

  let path_sub = ModulePath::new(vec![id("test_nest_c"), id("sub")]);
  let parsed_sub = parse_file(
    r#"
    def read : I64 := 1
    def write : I64 := 2
    "#
    .into(),
  )
  .unwrap();
  let decls_sub = type_check_module_decls(&path_sub, parsed_sub.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path_sub.clone(),
    ParsedModule {
      decls: decls_sub,
      module_doc: None,
    },
  ));

  let path_top = ModulePath::top("test_nest_c");
  let parsed_top = parse_file("def marker : I64 := 0".into()).unwrap();
  let decls_top = type_check_module_decls(&path_top, parsed_top.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(
    path_top.clone(),
    ParsedModule {
      decls: decls_top,
      module_doc: None,
    },
  ));

  let path_d = ModulePath::top("test_nest_d");
  let parsed_d = parse_file("use test_nest_c {sub {read}}".into()).unwrap();
  let decls_d = type_check_module_decls(&path_d, parsed_d.decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(
    path_d.clone(),
    ParsedModule {
      decls: decls_d,
      module_doc: None,
    },
  ));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path_d).expect("scope should exist");

  // `read` was explicitly selected -> bare-accessible.
  assert!(global.find_any_ref(&mpt("read"), &sort1()).is_ok());
  // `write` was not selected by the nested filter -> not bare-accessible.
  assert!(global.find_any_ref(&mpt("write"), &sort1()).is_err());
}
