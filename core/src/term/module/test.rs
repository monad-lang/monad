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

/// Term-level name shorthand — scope keys are `NamePath`s since the
/// qualified-names split; `mpt` (glob-imported from the parent) stays the
/// `ModulePath` (file-level) builder, still used for module-path lookups.
fn npt(s: &str) -> crate::term::NamePath {
  crate::term::NamePath::top(s)
}

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
      assert_eq!(module_path, npt("IO"));
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
      assert_eq!(module_path, npt("IO"));
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

/// `lib` is the mote self-reference (Rust's `crate`). It is rewritten to
/// the canonical mote-qualified path at load time, because a module path is
/// also a module's identity -- `lib.helper` left alone would be a second
/// module distinct from `demo.helper`, the same file under two names.
#[test]
fn test_lib_alias_rewrites_to_the_mote_name() {
  let path = ModulePath::new(vec![
    Identifier::new("lib".to_string()),
    Identifier::new("helper".to_string()),
  ]);
  let resolved = path.resolve_lib_alias("demo").expect("lib head rewrites");
  assert_eq!(resolved.to_string(), "demo.helper");
}

/// A bare `use lib` is the mote itself, which resolves to its `src/lib.mo`
/// like any other one-segment mote reference.
#[test]
fn test_bare_lib_alias_is_the_mote_itself() {
  let path = ModulePath::top("lib");
  let resolved = path.resolve_lib_alias("demo").expect("bare lib rewrites");
  assert_eq!(resolved.to_string(), "demo");
}

#[test]
fn test_lib_alias_only_fires_on_the_head_segment() {
  let path = ModulePath::new(vec![
    Identifier::new("demo".to_string()),
    Identifier::new("lib".to_string()),
  ]);
  assert!(
    path.resolve_lib_alias("demo").is_none(),
    "`lib` is only an alias in head position"
  );
}

// ─── `use` qualification (validate_use_qualification) ───────────────

/// A real init source path, CWD-independent — cargo runs a test binary from
/// its own package directory, where a repo-relative `init/src` is not.
fn init_src(rel: &str) -> std::path::PathBuf {
  std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../init/src")).join(rel)
}

fn cli_src(rel: &str) -> std::path::PathBuf {
  std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../cli/src")).join(rel)
}

fn std_src(rel: &str) -> std::path::PathBuf {
  std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../std/src")).join(rel)
}

fn qualification_error(source: &str, file: Option<&std::path::Path>) -> Option<String> {
  let decls = parse_file(source.into()).expect("sample parses").decls;
  match validate_use_qualification(&decls, file) {
    Ok(()) => None,
    Err(LoadingError::Generic(m)) => Some(m),
    Err(other) => panic!("expected a Generic load error, got {other:?}"),
  }
}

/// The headline case: `io` is a module of `init`, not a mote, so a bare
/// `use io` names whichever `io.mo` sits beside the importing file.
#[test]
fn test_bare_module_use_is_rejected() {
  let err = qualification_error("use io {IO}\n", None).expect("bare `use io` must be rejected");
  assert!(err.contains("does not name a mote"), "{err}");
  assert!(err.contains("`use io`"), "{err}");
  assert!(err.contains("hint:"), "{err}");
}

/// The hint names the file's line to write: resolution's own precedence puts
/// `init/src/io.mo` first, so the owner is `init`.
#[test]
fn test_bare_module_use_hint_names_the_owning_mote() {
  let err = qualification_error("use io {IO}\n", Some(&init_src("helper.mo")))
    .expect("bare `use io` must be rejected");
  assert!(err.contains("write `use init::io`"), "{err}");
}

/// A bare name that names a module in the importing file's own directory is
/// reported against THAT mote, not the init fallback — the message has to
/// match what resolution would actually have picked.
///
/// This is the ambiguity the rule exists for, in its exact original form:
/// `std/src/ansi.mo`'s `use io` resolves to `std/src/io.mo`, while the same
/// line in `cli/src/main.mo` resolves to `init/src/io.mo`.
#[test]
fn test_bare_module_use_hint_prefers_the_importers_own_directory() {
  let err = qualification_error("use io {IO}\n", Some(&std_src("ansi.mo")))
    .expect("bare `use io` must be rejected");
  assert!(err.contains("write `use std::io`"), "{err}");
}

#[test]
fn test_bare_non_mote_module_use_is_rejected() {
  let err = qualification_error("use number {}\n", None).expect("`number` is not a mote");
  assert!(err.contains("does not name a mote"), "{err}");
}

/// The prelude is ambient: the loader seeds it into every file's closure, so
/// an explicit import is redundant — in either spelling.
#[test]
fn test_use_of_the_prelude_is_rejected_bare_and_qualified() {
  for source in ["use prelude\n", "use init::prelude {*}\n"] {
    let err = qualification_error(source, None).expect("naming the prelude must be rejected");
    assert!(err.contains("names the prelude, which is ambient"), "{err}");
    assert!(err.contains("delete the `use"), "{err}");
  }
}

/// A rule that rejected everything would pass every test above. `runtime` is
/// a mote, `lib` the reserved alias, and `std`/`init` the ambient pair —
/// all one segment, all legal.
#[test]
fn test_legal_single_segment_uses_are_accepted() {
  for source in [
    "use runtime {}\n",
    "use lib {IO}\n",
    "use std\n",
    "use init\n",
  ] {
    assert!(
      qualification_error(source, None).is_none(),
      "`{source}` must be accepted"
    );
  }
}

/// The multi-segment half of the same rule: a head that is a mote reference
/// is left to the declared-dependency gate.
#[test]
fn test_qualified_uses_are_accepted() {
  for source in [
    "use std::io {IO}\n",
    "use init::io {IO}\n",
    "use lang::codegen::emit {}\n",
  ] {
    assert!(
      qualification_error(source, None).is_none(),
      "`{source}` must be accepted"
    );
  }
}

/// A mote is recognized from the importing file's manifest too, so a
/// dependency declared but not yet on disk still counts — the same question
/// the self-hosted `head_names_mote` asks.
#[test]
fn test_declared_dependency_counts_as_a_mote() {
  let file = cli_src("main.mo");
  let decls = parse_file("use runtime {}\n".into()).expect("parses").decls;
  assert!(
    head_names_mote(Some(&file), "runtime"),
    "cli/mote.toml declares `runtime`, so `use runtime` names a mote"
  );
  // ...and the same probe is what makes the rejection above meaningful: a
  // name no manifest declares and no directory holds is still not a mote.
  assert!(validate_use_qualification(&decls, Some(&file)).is_ok());
  assert!(!head_names_mote(Some(&file), "io"));
}

// ─── `use` brace names must be declarations (validate_use_names) ─────
//
// The rule: `use M {n}` binds `n` only when `M` declares a top-level name
// that IS `n`. A dotted def is more than one segment here (`List.length`
// is `[List, length]`) and a brace item now spells those segments back out, so
// `use std::list {List.length}` binds and the bare tail `{length}` does not -- it used to be a
// silent no-op whose failure surfaced at the CALL site. These exercise the
// check through `validate_use_names`, the exact entry point
// `load_decl_uses_modules` uses, so they see what the loader sees.

/// One target module per declaration kind, at `probe::list`, plus the
/// interesting pair: a bare `length` ALONGSIDE the dotted `List.length`,
/// so an acceptance test cannot pass by matching the dotted name.
const USE_TARGET: &str = r#"
def List.length : I64 := 1
def length : I64 := 2
def f : I64 := 3
type T {
  mk (u : Unit)
}
struct S { x : I64 }
class C A { def c (a : A) : A }
instance MyInst : C String {
  def c (a : String) : String := a
}
defmacro dm T := decls { }
"#;

/// `import_src` as a file that `use`s a module `target_src` declares at
/// `path`. Returns the check's message, or `None` when it passes.
///
/// The target is parsed and registered directly rather than loaded from
/// disk: `validate_use_names` consults the loaded module's declaration
/// maps and nothing else, so no checking or resolution is needed. The
/// importer's own module is deliberately never registered -- the check
/// asks about the TARGET, never about the importer.
fn use_name_error_with(modules: &[(&[&str], &str)], import_src: &str) -> Option<String> {
  let mut loaded = default_modules().unwrap();
  for (path, target_src) in modules {
    let path = ModulePath::new(path.iter().map(|s| id(*s)).collect());
    let parsed = parse_file((*target_src).into()).expect("target parses");
    loaded.add_module(module(
      path,
      ParsedModule {
        decls: parsed.decls,
        module_doc: None,
      },
    ));
  }
  let decls = parse_file(import_src.into()).expect("import parses").decls;
  match validate_use_names(&decls, &loaded, Some(&init_src("helper.mo"))) {
    Ok(()) => None,
    Err(LoadingError::Generic(m)) => Some(m),
    Err(other) => panic!("expected a Generic load error, got {other:?}"),
  }
}

fn use_name_error(import_src: &str) -> Option<String> {
  use_name_error_with(&[(&["probe", "list"], USE_TARGET)], import_src)
}

/// A bare spelling is never a match for a dotted declaration: `length` is
/// not a declaration of the module -- `List.length` is -- so the entry
/// binds nothing and is an error AT THE `use` LINE, where the corpus used
/// to accumulate hundreds of dead names that read as if they did
/// something. The hint names the spelling that WOULD bind it.
///
/// The target declares the dotted def and NOTHING else, because
/// `USE_TARGET` deliberately also declares a bare `length`: without that
/// separation this test would pass on a check that compared tails.
#[test]
fn test_a_bare_spelling_does_not_import_a_dotted_def() {
  let err = use_name_error_with(
    &[(&["probe", "list"], "def List.length : I64 := 1\n")],
    "use probe::list {length}\n",
  )
  .expect("`length` must be rejected: only `List.length` is declared");
  assert!(err.contains("declares no `length`"), "{err}");
  assert!(err.contains("`List.length` is declared there"), "{err}");
  assert!(
    err.contains("write `use probe::list {List.length}`"),
    "{err}"
  );
}

/// The other half, and the point of the whole change: the full spelling
/// DOES bind the dotted def, so the name is reachable bare via the list
/// instead of only through the always-on flat scope.
#[test]
fn test_a_dotted_spelling_imports_the_dotted_def() {
  for src in [
    "use probe::list {List.length}\n",
    // A dotted prefix names the namespace's members -- how an inductive
    // drags its constructors in.
    "use probe::list {List}\n",
  ] {
    assert!(
      use_name_error_with(
        &[(
          &["probe", "list"],
          "def List.length : I64 := 1\ntype List { cons (u : Unit) }\n",
        )],
        src,
      )
      .is_none(),
      "`{src}` names a real declaration and must be accepted"
    );
  }
}

/// A typo has no dotted sibling to point at, so the hint has to fall back
/// to the module-load spelling -- and must not claim a dotted name exists.
#[test]
fn test_a_use_name_declared_nowhere_is_rejected() {
  let err = use_name_error("use probe::list {lenght}\n").expect("`lenght` is declared nowhere");
  assert!(err.contains("declares no `lenght`"), "{err}");
  assert!(
    err.contains("nothing in `probe::list` is declared as `lenght`"),
    "{err}"
  );
  assert!(!err.contains("is declared there"), "{err}");
}

/// The half a rule that rejected everything would pass without. Every
/// declaration KIND a brace list names in this corpus is covered -- def,
/// inductive, a constructor, struct, class, instance, defmacro -- plus the
/// bare `length` that sits next to `List.length`, which is what proves the
/// check compares against the DECLARED name and not the textual tail.
#[test]
fn test_every_declaration_kind_can_be_imported_by_its_own_name() {
  for src in [
    "use probe::list {f}\n",
    "use probe::list {T}\n",
    "use probe::list {mk}\n",
    "use probe::list {S}\n",
    "use probe::list {C}\n",
    "use probe::list {MyInst}\n",
    "use probe::list {dm}\n",
    "use probe::list {length}\n",
  ] {
    assert!(
      use_name_error(src).is_none(),
      "`{src}` names a real declaration and must be accepted"
    );
  }
}

/// The mirror of the acceptance test above, and the subtle half: a
/// `struct`'s synthesized `mk` is NOT a declared name on either compiler
/// -- `struct` is its own decl kind, and only an ordinary inductive names
/// constructors. `declared_names_of`'s `Generic` guard is what this pins;
/// without it, walking every inductive's constructors would accept this.
#[test]
fn test_a_structs_synthesized_constructor_is_not_importable() {
  let err = use_name_error_with(
    &[(&["probe", "list"], "struct S { x : I64 }\n")],
    "use probe::list {mk}\n",
  )
  .expect("`mk` is synthesized, not declared");
  assert!(err.contains("declares no `mk`"), "{err}");
  assert!(!err.contains("is declared there"), "{err}");
}

/// `{*}` and `{}` are deliberately unchanged: this is a resolution rule,
/// not import-list minimalism. A bare `use` (no braces) has no list to
/// check and is the deprecation warning's business, not this check's.
#[test]
fn test_a_glob_and_an_empty_list_are_accepted() {
  for src in [
    "use probe::list {*}\n",
    "use probe::list {}\n",
    "use probe::list\n",
  ] {
    assert!(use_name_error(src).is_none(), "`{src}` must be accepted");
  }
}

/// A rename is checked against the name it renames FROM. The alias is the
/// importer's own choice of spelling and is never looked up in the target,
/// so `{f as g}` is fine while `{g as f}` is not -- `g` is not a
/// declaration of the target.
#[test]
fn test_a_rename_checks_the_name_not_the_alias() {
  assert!(
    use_name_error("use probe::list {f as g}\n").is_none(),
    "`f` is declared; the alias is the importer's own"
  );
  let err = use_name_error("use probe::list {g as f}\n").expect("`g` is not declared");
  assert!(err.contains("declares no `g`"), "{err}");
}

/// A sub-list is checked against the module at the EXTENDED path, not
/// against the module that holds it. The two modules are registered with
/// DIFFERENT names (`g` on `probe::outer`, `f` on `probe::outer::inner`)
/// so a check that consulted the outer path would accept `inner {g}` and
/// fail here.
#[test]
fn test_a_sub_list_is_checked_against_the_extended_path() {
  let modules: &[(&[&str], &str)] = &[
    (&["probe", "outer"], "def g : I64 := 1\n"),
    (&["probe", "outer", "inner"], "def f : I64 := 1\n"),
  ];
  assert!(
    use_name_error_with(modules, "use probe::outer {inner {f}}\n").is_none(),
    "`f` is declared by probe::outer::inner"
  );

  let err = use_name_error_with(modules, "use probe::outer {inner {g}}\n")
    .expect("`g` is declared by probe::outer, not by probe::outer::inner");
  assert!(err.contains("declares no `g`"), "{err}");
  assert!(err.contains("probe::outer::inner"), "{err}");
}

/// A path that resolves to no LOADED module is left alone. That is an
/// ordinary module-not-found (or a `lib::` alias, rewritten later), which
/// the loader reports where it happens -- reporting it here would say it
/// twice, and with the wrong reason.
#[test]
fn test_a_use_of_an_unloaded_module_is_left_alone() {
  let loaded = default_modules().unwrap();
  let decls = parse_file("use probe::absent {whatever}\n".into())
    .expect("parses")
    .decls;
  assert!(validate_use_names(&decls, &loaded, None).is_ok());
}

/// A mote path reads as `<mote>/src/<rest>.mo`, which is what makes
/// `use lang.codegen.emit` find `lang/src/codegen/emit.mo`.
#[test]
fn test_mote_file_path_puts_sources_under_src() {
  let path = ModulePath::new(vec![
    Identifier::new("lang".to_string()),
    Identifier::new("codegen".to_string()),
    Identifier::new("emit".to_string()),
  ]);
  assert_eq!(
    path.to_mote_file_path(),
    std::path::PathBuf::from("lang/src/codegen/emit.mo")
  );
  assert_eq!(
    ModulePath::top("std").to_mote_file_path(),
    std::path::PathBuf::from("std/src/lib.mo"),
    "a one-segment path is the mote's library root"
  );
}

#[test]
fn test_pub_use_reexport_is_never_unused() {
  // A `pub use` is a re-export -- a mote's `lib.mo` hub is made entirely of
  // them, and its consumers live in other files. Nothing in this module
  // references the names, and that is not a defect.
  let modu = module_of(
    r#"
    pub use fakemod {reexported_name}
    "#,
  );
  let referenced = collect_referenced_names(&modu);
  let warnings = unused_use_name_warnings(modu.get_uses(), &referenced, None);
  assert!(
    warnings.is_empty(),
    "a pub use re-export must not be reported as unused: {warnings:?}"
  );
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
  assert!(referenced.contains(&NamePath::single(id("red"))));
  assert!(referenced.contains(&NamePath::single(id("green"))));
  assert!(referenced.contains(&NamePath::single(id("blue"))));
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

/// A dotted def has to be emitted under its own SPELLED name. A brace item
/// is matched against the declaration's full spelling, so `{length}` for
/// `List.length` would be an item that selects nothing — the codemod must
/// write `{List.length}`, which is the declaration, not its last segment.
#[test]
fn test_organize_imports_emits_a_dotted_spelling() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_organize_dotted_a");
  let parsed_a = parse_file(
    r#"
    def List.length : I64 := 1
    def plain : I64 := 2
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

  let path_b = ModulePath::top("test_organize_dotted_b");
  let source_b = format!(
    "use {}\n\ndef f : I64 := List.length\n",
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
    new_source.contains("use test_organize_dotted_a {List.length}"),
    "got: {new_source:?}"
  );
  assert!(!new_source.contains("plain"), "got: {new_source:?}");
  // Rewritten source must still parse — the emitted item is a dotted name
  // path, which the parser only accepts since the brace-item rule widened.
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

/// organize-imports emits the `::` spelling for `use` and keeps `.` for
/// `open` -- and what it emits must re-parse, which is what makes the two
/// separators a round trip rather than just a rendering choice.
#[test]
fn test_organize_imports_emits_colon_colon_for_use_only() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::new(vec![
    Identifier::new("colonmod".to_string()),
    Identifier::new("inner".to_string()),
  ]);
  let parsed_a = parse_file("def used_fn : I64 := 1\ndef unused_fn : I64 := 2\n".into()).unwrap();
  let decls_a = type_check_module_decls(&path_a, parsed_a.decls, &loaded).unwrap();
  let mut loaded = loaded;
  loaded.add_module(module(
    path_a.clone(),
    ParsedModule {
      decls: decls_a,
      module_doc: None,
    },
  ));

  let path_b = ModulePath::top("colon_consumer");
  // Bare `use` (no filter) is what organize-imports rewrites into an
  // explicit one -- which is where the rendering happens.
  let source_b = "use colonmod::inner\n\ndef f : I64 := used_fn\n";
  let parsed_b = parse_file(source_b.into()).unwrap();
  let decls_b = type_check_module_decls(&path_b, parsed_b.decls, &loaded).unwrap();
  loaded.add_module(module(
    path_b.clone(),
    ParsedModule {
      decls: decls_b,
      module_doc: None,
    },
  ));

  let module_b = loaded.get_module(&path_b).unwrap();
  let edits = compute_organize_import_edits(module_b, &loaded);
  let new_source = apply_text_edits(source_b, edits);
  assert!(
    new_source.contains("use colonmod::inner {used_fn}"),
    "a use path renders with `::`: {new_source:?}"
  );
  // What it emits has to parse -- the `::` spelling is accepted, so this
  // is a real round trip and not just a prettier string.
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
  // `lang/core_ir.mo` opening `CoreIr` it just declared.
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
    npt("HAdd"),
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

  assert!(global.find_ref(&npt("my_def")).is_some());
  assert!(global.find_inductive(&npt("MyType")).is_some());
}

#[test]
fn test_global_scope_data_includes_implicit_modules() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    use init::io
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
  assert!(global.find_inductive(&npt("Bool")).is_some());
  assert!(global.find_inductive(&npt("Option")).is_some());
  assert!(global.find_inductive(&npt("List")).is_some());
}

#[test]
fn test_global_scope_data_applies_opens() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    use init::io
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
  assert!(global.find_ref(&npt("println")).is_some());
}

#[test]
fn test_get_module_scope_returns_correct_scope() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    use init::io
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
  assert!(prelude_scope.find_inductive(&npt("Bool")).is_some());
  assert!(prelude_scope.find_inductive(&npt("Option")).is_some());
}

#[test]
fn test_instance_resolution_module_restricted() {
  let loaded = default_modules().unwrap();

  let path = ModulePath::top("test_mod");
  let parsed = parse_file(
    r#"
    use init
    use init::math

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
  assert!(global.find_ref(&npt("test_eq")).is_some());
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
  // The braces matter: a bare `use M` selects every name QUALIFIED only,
  // so it would leave the scope without a bare `shared_name` at all and
  // this test would be asserting a not-found, not an ambiguity.
  let parsed_c = parse_file(&format!(
    r#"
    use {} {{shared_name}}
    use {} {{shared_name}}
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

  let result = global.find_any_ref(&npt("shared_name"), &sort1());
  assert!(result.is_err());
  if let Err(ScopeError::AmbiguousName { name, candidates }) = result {
    assert_eq!(name, npt("shared_name"));
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

  let prefixed_a = crate::term::NamePath::from(path_a.clone()).append(vec![id("shared_name")]);
  assert!(global.find_ref(&prefixed_a).is_some());
  let prefixed_b = crate::term::NamePath::from(path_b.clone()).append(vec![id("shared_name")]);
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
  assert!(global_a.find_ref(&npt("secret_val")).is_some());
  // ...but not from another module, even with `use {*}`.
  assert!(global_b.find_ref(&npt("secret_val")).is_none());

  // `pub` and the default (package-private, currently == public) remain
  // visible from other modules.
  assert!(global_b.find_ref(&npt("public_val")).is_some());
  assert!(global_b.find_ref(&npt("default_val")).is_some());
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

  assert!(global.find_any_ref(&npt("foo"), &sort1()).is_ok());
  assert!(global.find_any_ref(&npt("bar"), &sort1()).is_err());
}

/// The completeness rule as the loader enforces it: a bare name reached
/// from a module the file did not select it from FAILS THE LOAD — which
/// is what makes the rule hold for every entry point (`run`, `test`,
/// `compile`, the LSP), not only for `check` — and putting the name in
/// a brace list clears it. Resolution itself is untouched — the scope
/// is still flat, which is exactly why the check has to exist: the load
/// is what distinguishes the two.
#[test]
fn test_unimported_name_fails_the_load_and_importing_it_clears_it() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::new(vec![id("test_cmp"), id("a")]);
  let parsed_a = parse_file(
    r#"
    def widget : I64 := 1
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

  let path_b = ModulePath::top("test_cmp_b");
  // Two segments: a single-segment `use X` is (correctly) rejected by
  // `validate_use_qualification` before the completeness gate ever runs.
  let a = module_path_spelling(&path_a);

  // `use A {}` is the qualified-only form: it names the module, not the
  // name, so reaching `widget` bare is the finding. The load itself still
  // type-checks (the flat scope resolves `widget` — that is the point);
  // only the completeness gate refuses it.
  let source = format!("use {a} {{}}\ndef use_it : I64 := widget\n");
  let mut loaded_b = loaded.clone();
  let err = load_module_from_text_at(&source, &path_b, None, &mut loaded_b)
    .expect_err("the load must fail on the unimported name");
  let message = err.to_string();
  assert!(message.contains("`widget` is not imported"), "{message}");
  assert!(
    message.contains(&a),
    "the message must name the module that declares it: {message}"
  );

  // The same reference, now selected by name: the load goes through.
  let selected = format!("use {a} {{widget}}\ndef use_it : I64 := widget\n");
  load_module_from_text_at(&selected, &path_b, None, &mut loaded)
    .expect("`{widget}` names it, so the load is complete");
}

/// A bare name the consumer binds from its OWN declaration is never a
/// name it "reaches from another module", however many loaded modules
/// happen to spell one the same way.
///
/// The case is `mk`: a `struct` is stored as an inductive whose single
/// constructor is `mk` (`term::stru`), the corpus pattern-matches it bare
/// (`match p { mk x y => ... }`), and half the corpus declares a struct.
/// A module that declares a GENERIC inductive with a constructor named
/// `mk` — `lang::parser::core`'s `OpEntry` is the one that did it — then
/// looks like the owner of a name the file declares itself, and the fix
/// the report suggests is an import of a module the file has no business
/// naming. The companion assertion is the discriminating half: the
/// genuinely-foreign `widget` must STILL fail the load, so the test
/// cannot pass by the check having gone silent.
#[test]
fn test_own_struct_constructor_is_not_an_unimported_name() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_mk_a");
  let parsed_a = parse_file(
    r#"
    def widget : I64 := 1
    pub type Box2 { mk (x : I64) }
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

  let path_b = ModulePath::top("test_mk_b");
  let a = path_a.as_str().unwrap().to_string();
  let source = format!(
    "struct S {{\n  x: I64,\n}}\n\n\
     def get_x (s : S) : I64 := match s {{ mk x => x }}\n\
     def use_widget : I64 := widget\n"
  );
  // The load FAILS on the genuinely-foreign `widget` — and its message
  // must not name `mk`: this file's own struct constructor is never a
  // name it "reaches from another module", however many loaded modules
  // happen to spell one the same way.
  let mut loaded_b = loaded.clone();
  let err = load_module_from_text_at(&source, &path_b, None, &mut loaded_b)
    .expect_err("`widget` must fail the completeness gate");
  let message = err.to_string();
  assert!(message.contains("`widget` is not imported"), "{message}");
  assert!(
    !message.contains("`mk` is not imported"),
    "`mk` is this file's own struct constructor, not `{a}`'s: {message}"
  );

  // The same file without the foreign reference loads clean — the
  // own-decl exemption is the only thing standing between the bare `mk`
  // pattern the corpus matches on and a false-positive gate failure.
  let clean = "struct S {\n  x: I64,\n}\n\ndef get_x (s : S) : I64 := match s { mk x => x }\n";
  load_module_from_text_at(&clean, &path_b, None, &mut loaded)
    .expect("an own `mk` never blocks the load");
}

#[test]
fn test_use_glob_binds_bare_names() {
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

  // `{*}` makes every name bare-accessible. NOT the same as a brace-less
  // `use M` / `use M {}`: those select every name QUALIFIED only, and the
  // test below pins that difference.
  assert!(global.find_any_ref(&npt("foo"), &sort1()).is_ok());
  assert!(global.find_any_ref(&npt("bar"), &sort1()).is_ok());
}

/// The other half of the rule above, and the reason `{}` is not "nothing":
/// a brace-less `use M` and an empty `use M {}` are synonyms, and both
/// select the module's names for QUALIFIED access only. Nothing is bound
/// bare — `M::foo` resolves, a bare `foo` does not.
#[test]
fn test_use_empty_braces_bind_nothing_bare() {
  let loaded = default_modules().unwrap();

  let path_a = ModulePath::top("test_empty_a");
  let parsed_a = parse_file(
    r#"
    def foo : I64 := 1
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

  for (path_b, spelling) in [
    (
      ModulePath::top("test_empty_brace_b"),
      format!("use {} {{}}", path_a.as_str().unwrap()),
    ),
    (
      ModulePath::top("test_empty_bare_b"),
      format!("use {}", path_a.as_str().unwrap()),
    ),
  ] {
    let parsed_b = parse_file(spelling.as_str().into()).unwrap();
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
    assert!(
      global.find_any_ref(&npt("foo"), &sort1()).is_err(),
      "`{spelling}` must not bind a bare `foo`"
    );
  }
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
  assert!(global.find_any_ref(&npt("read"), &sort1()).is_ok());
  // `write` was not selected by the nested filter -> not bare-accessible.
  assert!(global.find_any_ref(&npt("write"), &sort1()).is_err());
}

fn module_at(path: ModulePath, source: &str) -> Module {
  let parsed = parse_file(source.into()).unwrap();
  module(
    path,
    ParsedModule {
      decls: parsed.decls,
      module_doc: None,
    },
  )
}

/// Covers the five exemption/detection cases `unused_def_warnings`'s own
/// doc comment lists — mirrors the manual multi-file fixture this was
/// verified against directly (`examples/unused_def_fixture_a.mo`/`_b.mo`,
/// not checked in): a `pub` def, a def used only by a sibling module, a
/// genuinely-unused private def, a `#[test]` def, and `main`.
#[test]
fn test_unused_def_warnings_five_cases() {
  let mut loaded = LoadedModules::empty();
  loaded.add_module(module_at(
    ModulePath::top("fixture_a"),
    r#"
    pub def shared_helper (x : I64) : I64 := x + 1

    def only_used_by_sibling (x : I64) : I64 := x * 2

    def genuinely_dead_private_def (x : I64) : I64 := x - 1

    #[test]
    def fixture_a_test_never_called_directly : I64 := 1

    def main (args : List String) : I64 := 0
    "#,
  ));
  loaded.add_module(module_at(
    ModulePath::top("fixture_b"),
    r#"
    use fixture_a {only_used_by_sibling}

    def call_it (x : I64) : I64 := only_used_by_sibling x
    "#,
  ));

  let warnings = unused_def_warnings(&loaded);
  let unused_names: std::collections::HashSet<String> =
    warnings.iter().map(|(_, d)| d.message.clone()).collect();

  // `shared_helper` (pub), `only_used_by_sibling` (used cross-module),
  // `fixture_a_test_never_called_directly` (#[test]), and `main` must all
  // be exempt/detected-as-used -- only the two genuinely-dead private defs
  // should warn.
  assert_eq!(warnings.len(), 2, "unexpected warnings: {unused_names:?}");
  assert!(unused_names.contains("unused def `genuinely_dead_private_def`"));
  assert!(unused_names.contains("unused def `call_it`"));
}

// ─── cross-mote `pub` warnings across a GROUPED directory ────────────
//
// The target mote used to be resolved by joining the module path's first
// segment onto the cwd -- `Path::new("http").join("mote.toml")` -- which is
// true only for a mote that is a direct child of the cwd and named after
// its directory. Every mote under `motes/` (and every planned `pkgs/`
// library) therefore dropped out of the inventory with no warning, no note
// and no count; `plans/implementations/cross-mote-pub-unenforced-for-motes.md`.
// The resolution now goes through the workspace member list, so the target
// side is manifest-derived exactly like `here`.

/// A real source path inside a mote under the grouped `motes/` directory.
/// The file need not exist -- `mote_name_of_file` walks up to a `mote.toml`.
fn motes_src(mote: &str, rel: &str) -> std::path::PathBuf {
  std::path::PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../motes"))
    .join(mote)
    .join("src")
    .join(rel)
}

/// `import_src` as a real file at `file`, importing `target_src` registered
/// at `target_path`. The importer's own module is never registered, because
/// the check asks about the TARGET only.
fn cross_mote_warnings(
  import_src: &str,
  target_src: &str,
  target_path: &[&str],
  file: &std::path::PathBuf,
) -> Vec<Diagnostic> {
  let mut loaded = default_modules().unwrap();
  loaded.add_module(module_at(
    ModulePath::new(target_path.iter().map(|s| id(*s)).collect()),
    target_src,
  ));
  cross_mote_package_private_warnings(
    &module_at(ModulePath::top("importer"), import_src),
    &loaded,
    Some(file),
  )
}

/// The headline case. `motes/moose` imports `motes/http`, whose manifest is
/// at `motes/http/mote.toml` -- not at `<cwd>/http/mote.toml`, which is
/// where the old rule looked and, from a cargo test binary's cwd, never
/// found. A package-private `Body` must be inventoried.
#[test]
fn test_cross_mote_warning_resolves_a_grouped_mote() {
  let warnings = cross_mote_warnings(
    "use http::types {Body}\n\ndef f : I64 := 0\n",
    "struct Body { bytes : List U8 }\n",
    &["http", "types"],
    &motes_src("moose", "client.mo"),
  );
  assert_eq!(warnings.len(), 1, "unexpected: {warnings:?}");
  assert!(warnings[0].message.contains("`Body`"), "{:?}", warnings[0]);
  assert!(
    warnings[0].message.contains("from mote `http`"),
    "{:?}",
    warnings[0]
  );
}

/// The other direction: the same edge with the declaration marked `pub` is
/// silent, so the row above cannot pass by warning unconditionally.
#[test]
fn test_cross_mote_warning_is_silent_for_a_pub_declaration() {
  let warnings = cross_mote_warnings(
    "use http::types {Body}\n\ndef f : I64 := 0\n",
    "pub struct Body { bytes : List U8 }\n",
    &["http", "types"],
    &motes_src("moose", "client.mo"),
  );
  assert!(warnings.is_empty(), "unexpected: {warnings:?}");
}

/// A mote that IS a direct child of the repository root still warns -- the
/// case the old rule handled, pinned so the workspace walk cannot trade one
/// blind spot for another.
#[test]
fn test_cross_mote_warning_still_resolves_a_root_level_mote() {
  let warnings = cross_mote_warnings(
    "use std::io {Socket}\n\ndef f : I64 := 0\n",
    "struct Socket { fd : I64 }\n",
    &["std", "io"],
    &init_src("helper.mo"),
  );
  assert_eq!(warnings.len(), 1, "unexpected: {warnings:?}");
  assert!(
    warnings[0].message.contains("from mote `std`"),
    "{:?}",
    warnings[0]
  );
}

/// A name no manifest declares is not a mote, so no boundary is crossed --
/// `use io {IO}` names a MODULE of the importer's own mote, and importing
/// `std::io`'s `Socket` from a mote named `io` is a self-import, not an
/// edge. Without this the set lookup would make every first segment a mote.
#[test]
fn test_cross_mote_warning_ignores_a_name_that_is_no_mote() {
  let warnings = cross_mote_warnings(
    "use notamote::types {Thing}\n\ndef f : I64 := 0\n",
    "struct Thing { x : I64 }\n",
    &["notamote", "types"],
    &motes_src("moose", "client.mo"),
  );
  assert!(warnings.is_empty(), "unexpected: {warnings:?}");
}
