use super::*;
#[test]
fn test_simple_instance() {
  let mut loaded = LoadedModules::empty();

  let path = ModulePath::top("_");
  let decls = parse_file(
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
  let decls = type_check_module_decls(&path, decls, &mut loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let modu = module(path.clone(), decls);
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
  let decls = parse_file(
    r#"
    type MyType {
      constructor
    }
    def my_def : MyType := MyType.constructor
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  loaded.add_module(module(path.clone(), decls));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("scope should exist");

  assert!(global.find_ref(&mpt("my_def")).is_some());
  assert!(global.find_inductive(&mpt("MyType")).is_some());
}

#[test]
fn test_global_scope_data_includes_implicit_modules() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let decls = parse_file(
    r#"
    use io
    open IO

    def test_def : IO Unit := println "test"
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(path.clone(), decls));

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
  let decls = parse_file(
    r#"
    use io
    open IO

    def test_def : IO Unit := println "test"
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(path.clone(), decls));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("scope should exist");

  // With open IO, println should be accessible directly
  assert!(global.find_ref(&mpt("println")).is_some());
}

#[test]
fn test_get_module_scope_returns_correct_scope() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let decls = parse_file(
    r#"
    use io
    open IO

    def test_def : String := "hello"
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(path.clone(), decls));

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
  let decls = parse_file(
    r#"
    use init
    use math

    def test_eq : Bool := 1 == 1
    "#
    .into(),
  )
  .unwrap();
  let decls = type_check_module_decls(&path, decls, &loaded)
    .inspect_err(|e| eprintln!("{e}"))
    .unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(path.clone(), decls));

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("scope should exist");

  // Should find BEq instance for I64
  assert!(global.find_ref(&mpt("test_eq")).is_some());
}
