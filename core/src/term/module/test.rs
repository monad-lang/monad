use super::*;
// These tests exercise module-loading/scoping mechanics — most of them
// (everything above the "Visibility (`pub`/`priv`) enforcement" section
// below) only need SOME valid checked `Vec<Decl>` to feed into
// `GlobalScopeData::from_module`/`compute_organize_import_edits`/etc.,
// not anything specific to which checker produced it, so they were a
// clean import-rename once the OLD checker (`eval::r#type::
// type_check_module_decls`) was removed — this alias keeps every call
// site below unchanged. `type_check_module_decls_new` is the new default
// checker's own direct module-level entry point (`core_check_module.rs`).
use crate::core_check_module::type_check_module_decls_new as type_check_module_decls;
use crate::diag::Severity;
use crate::parser::parse_file;
use crate::term::organize_imports::{apply_text_edits, compute_organize_import_edits};

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

fn opens_of(source: &str) -> Vec<SourceContext<Open>> {
  parse_file(source.into())
    .unwrap()
    .decls
    .into_iter()
    .filter_map(|ctx| {
      let loc = ctx.loc.clone();
      let doc = ctx.doc.clone();
      match ctx.value {
        Decl::Open(o) => Some(SourceContext { loc, doc, value: o }),
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
fn test_bare_open_emits_warning() {
  let opens = opens_of("open IO\n");
  let warnings = bare_open_warnings(&opens, None);
  assert_eq!(warnings.len(), 1);
  assert_eq!(warnings[0].severity, Severity::Warning);
  assert!(warnings[0].message.contains("deprecated"));
  assert!(warnings[0].suggestions[0].message.contains("{*}"));
}

#[test]
fn test_glob_open_emits_no_warning() {
  let opens = opens_of("open IO {*}\n");
  assert!(bare_open_warnings(&opens, None).is_empty());
}

#[test]
fn test_filtered_open_emits_no_warning() {
  let opens = opens_of("open IO {println}\n");
  assert!(bare_open_warnings(&opens, None).is_empty());
}

#[test]
fn test_empty_open_filter_is_rejected() {
  let decls = parse_file("open IO {}\n".into()).unwrap().decls;
  match validate_open_filters(&decls) {
    Err(TypeError::EmptyOpenFilter { module_path, .. }) => {
      assert_eq!(module_path, mpt("IO"));
    }
    other => panic!("expected Err(TypeError::EmptyOpenFilter), got {other:?}"),
  }
}

#[test]
fn test_nonempty_open_filter_is_accepted() {
  let decls = parse_file("open IO {println}\n".into()).unwrap().decls;
  assert!(validate_open_filters(&decls).is_ok());
}

#[test]
fn test_glob_and_bare_open_are_accepted() {
  let decls = parse_file("open IO {*}\nopen Foo\n".into()).unwrap().decls;
  assert!(validate_open_filters(&decls).is_ok());
}

#[test]
fn test_empty_scoped_open_filter_is_rejected() {
  let decls = parse_file("open IO {} in def f : I64 := 1\n".into())
    .unwrap()
    .decls;
  match validate_open_filters(&decls) {
    Err(TypeError::EmptyOpenFilter { module_path, .. }) => {
      assert_eq!(module_path, mpt("IO"));
    }
    other => panic!("expected Err(TypeError::EmptyOpenFilter), got {other:?}"),
  }
}

fn module_of(source: &str) -> Module {
  let parsed = parse_file(source.into()).unwrap();
  module(
    ModulePath::top("_"),
    ParsedModule {
      decls: parsed.decls,
      module_doc: None,
    },
  )
}

#[test]
fn test_unused_use_name_warning() {
  let modu = module_of(
    r#"
    use fakemod {used_name, unused_name}

    def f : I64 := used_name
    "#,
  );
  let referenced = collect_referenced_names(&modu);
  let warnings = unused_use_name_warnings(modu.get_uses(), &referenced, None);
  assert_eq!(warnings.len(), 1);
  assert_eq!(warnings[0].severity, Severity::Warning);
  assert!(warnings[0].message.contains("unused_name"));
  assert!(!warnings[0].message.contains("used_name,"));
}

#[test]
fn test_qualified_reference_counts_as_used() {
  // `fakemod.q_name` (qualified) should count as a use of `q_name`, even
  // though `q_name` is never referenced as a bare name.
  let modu = module_of(
    r#"
    use fakemod {q_name}

    def f : I64 := fakemod.q_name
    "#,
  );
  let referenced = collect_referenced_names(&modu);
  let warnings = unused_use_name_warnings(modu.get_uses(), &referenced, None);
  assert!(warnings.is_empty());
}

#[test]
fn test_match_pattern_constructor_counts_as_used() {
  // A constructor referenced only in match-pattern position (never as a
  // call-position `Term::Var`) must still be recorded as "referenced" —
  // this is how `open`-imported constructors used only in match arms are
  // recognized (see `MatchCase::name` handling in `collect_referenced_names`).
  let modu = module_of(
    r#"
    type Color { red, green, blue }

    def f (c: Color) : Bool :=
        match c {
            red => true,
            green => false,
            blue => false
        }
    "#,
  );
  let referenced = collect_referenced_names(&modu);
  assert!(referenced.contains(&ModulePath::single(id("red"))));
  assert!(referenced.contains(&ModulePath::single(id("green"))));
  assert!(referenced.contains(&ModulePath::single(id("blue"))));
}

#[test]
fn test_organize_imports_use_minimal_names() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_organize_a");
  let parsed_a = parse_file(
    r#"
    def used_fn : I64 := 1
    def unused_fn : I64 := 2
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

  let path_b = ModulePath::top("test_organize_b");
  let source_b = format!(
    "use {}\n\ndef f : I64 := used_fn\n",
    path_a.as_str().unwrap()
  );
  let parsed_b = parse_file(source_b.as_str().into()).unwrap();
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

  let module_b = loaded.get_module(&path_b).unwrap();
  let edits = compute_organize_import_edits(module_b, &loaded);
  assert_eq!(edits.len(), 1);
  let new_source = apply_text_edits(&source_b, edits);
  assert!(
    new_source.contains("use test_organize_a {used_fn}"),
    "got: {new_source:?}"
  );
  assert!(!new_source.contains("unused_fn"));
  // Rewritten source must still parse.
  assert!(parse_file(new_source.as_str().into()).is_ok());
}

#[test]
fn test_organize_imports_deletes_fully_unused_use() {
  // A `use` whose target contributes nothing this file actually
  // references gets DELETED outright, not rewritten to a no-op `use X
  // {}` — the line (and its newline) disappears entirely.
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_organize_unused_a");
  let parsed_a = parse_file(
    r#"
    def never_used : I64 := 1
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

  let path_b = ModulePath::top("test_organize_unused_b");
  let source_b = format!("use {}\n\ndef f : I64 := 1\n", path_a.as_str().unwrap());
  let parsed_b = parse_file(source_b.as_str().into()).unwrap();
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

  let module_b = loaded.get_module(&path_b).unwrap();
  let edits = compute_organize_import_edits(module_b, &loaded);
  assert_eq!(edits.len(), 1);
  let new_source = apply_text_edits(&source_b, edits);
  assert_eq!(new_source, "\ndef f : I64 := 1\n", "got: {new_source:?}");
  assert!(!new_source.contains("use "));
  assert!(parse_file(new_source.as_str().into()).is_ok());
}

#[test]
fn test_organize_imports_open_and_use_together() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_organize_open_a");
  let parsed_a = parse_file(
    r#"
    def helper : I64 := 1
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

  // `open` on an external module needs a paired `use` to actually load
  // it (same as real .mo files always pair the two) — `open` alone only
  // affects bare-name *filtering* of an already-visible module.
  let path_b = ModulePath::top("test_organize_open_b");
  let source_b = format!(
    "use {}\nopen {}\n\ndef f : I64 := helper\n",
    path_a.as_str().unwrap(),
    path_a.as_str().unwrap()
  );
  let parsed_b = parse_file(source_b.as_str().into()).unwrap();
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

  let module_b = loaded.get_module(&path_b).unwrap();
  let edits = compute_organize_import_edits(module_b, &loaded);
  // One for the bare `use`, one for the bare `open`.
  assert_eq!(edits.len(), 2);
  let new_source = apply_text_edits(&source_b, edits);
  assert!(
    new_source.contains("use test_organize_open_a {helper}"),
    "got: {new_source:?}"
  );
  assert!(
    new_source.contains("open test_organize_open_a {helper}"),
    "got: {new_source:?}"
  );
  assert!(parse_file(new_source.as_str().into()).is_ok());
}

#[test]
fn test_organize_imports_open_local_inductive() {
  // `open TypeName {...}` targeting a type defined in the SAME file (no
  // paired `use` needed or possible) — the common real-world shape, e.g.
  // `lang/eval_term.mo` opening `EvalTerm`/`Region`/etc. it just declared.
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_organize_local_open");
  let source = r#"
type Color {
  red,
  green,
  blue,
}

open Color

def is_warm (c: Color) : Bool :=
  match c {
    red => true,
    green => false,
    blue => false
  }
"#;
  let parsed = parse_file(source.into()).unwrap();
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

  let modu = loaded.get_module(&path).unwrap();
  let edits = compute_organize_import_edits(modu, &loaded);
  assert_eq!(edits.len(), 1);
  let new_source = apply_text_edits(source, edits);
  assert!(
    new_source.contains("open Color {blue, green, red}"),
    "got: {new_source:?}"
  );
  assert!(parse_file(new_source.as_str().into()).is_ok());
}

#[test]
fn test_glob_use_never_flagged_unused() {
  let modu = module_of(
    r#"
    use fakemod {*}

    def f : I64 := 1
    "#,
  );
  let referenced = collect_referenced_names(&modu);
  let warnings = unused_use_name_warnings(modu.get_uses(), &referenced, None);
  assert!(warnings.is_empty());
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

    #[native num_add]
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

// --- Visibility (`pub`/`priv`) enforcement ---
//
// NOTE: these tests exercise the OLD checker's scope-resolution
// (`GlobalScopeData::from_module`/`type_check_module_decls`, the path this
// file's tests always use regardless of the `legacy-checker` Cargo
// feature's default — see the file-header comment). The NEW default
// checker (`core_check_module::type_check_module_decls_new`, used by
// `cargo run` without `--features legacy-checker`) does not go through
// `GlobalScopeData` at all — `ground_truth_from_loaded` flattens every
// loaded module's defs into one global namespace with no per-module
// scoping, so it does not respect `use {name}` selective filtering OR
// `priv` today. That's a pre-existing gap in the new checker's
// architecture, orthogonal to (and larger than) visibility — fixing it
// means giving the new checker real per-module scoped name resolution,
// which is out of scope here. `priv` is fully enforced wherever
// `GlobalScopeData` is the resolution path (this old checker, and the
// LSP's hover/definition, both of which use it directly).

#[test]
fn test_priv_def_invisible_from_other_module() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_vis_a");
  let parsed_a = parse_file(
    r#"
    priv def secret_val : I64 := 42
    pub def public_val : I64 := 7
    def default_val : I64 := 1
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

  let path_b = ModulePath::top("test_vis_b");
  let parsed_b = parse_file(&format!(r#"use {} {{*}}"#, path_a.as_str().unwrap())).unwrap();
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
  let global_a = loaded_scopes.global(&path_a).expect("scope should exist");
  let global_b = loaded_scopes.global(&path_b).expect("scope should exist");

  // Visible from within its own module...
  assert!(global_a.find_ref(&mpt("secret_val")).is_some());
  // ...but not from another module, even with `use {*}`.
  assert!(global_b.find_ref(&mpt("secret_val")).is_none());

  // `pub` and the default (package-private, currently == public) remain
  // visible from other modules.
  assert!(global_b.find_ref(&mpt("public_val")).is_some());
  assert!(global_b.find_ref(&mpt("default_val")).is_some());
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
