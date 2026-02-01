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
