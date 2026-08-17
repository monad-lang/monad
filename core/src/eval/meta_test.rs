//! Phase 1 gate test for the reflection-as-data metaprogramming kernel
//! (`plans/review-and-reduce-the-greedy-nest.md`): a hand-written trivial
//! "meta" def (an ordinary `def`, not a `defmacro` template — no
//! `std/derive.mo` involvement) round-trips through `reflect_type_info!`
//! -> a real `TypeInfo` value -> a hand-written `Expr`/`Decl` computation
//! -> reify, and a disallowed native inside that computation fails with a
//! clear purity error, not a panic.

use crate::core_check_module::type_check_module_decls_new;
use crate::eval::macro_expand::expand_macros;
use crate::eval::r#type::elaborate_decls;
use crate::parser::parse_file;
use crate::term::module::{LoadedModules, ParsedModule, default_modules, module};
use crate::term::{Decl, Identifier, ModulePath, SearchPaths};

/// Load `init/meta.mo` (the real file, embedded via `include_str!` the
/// same way `default_modules()` embeds the always-loaded `init/*.mo`
/// package) into an otherwise ordinary `default_modules()` `LoadedModules`,
/// under module path `init.meta` — matching how `use init.meta {...}`
/// would resolve it (same convention as `init/optics.mo`: living in
/// `init/` doesn't make it part of the fixed, always-loaded default
/// package — `init_package_sources()`'s own path list is `prelude`/`id`/
/// `io`/`number`/`math`/`string`/`init`/`process` only — so it's an
/// ordinary two-segment `init.meta` module a file `use`s explicitly, just
/// like `std.meta` was before the move). Also sets `loaded`'s search
/// paths to the repo root (mirroring `core_check_module.rs`'s private
/// `repo_search_paths`/the CLI's own `build_default_search_paths`) —
/// `meta_compile::MetaEvalContext::build` goes through the exact same
/// whole-program capture path the real `run`/`test` commands use
/// (`lib.rs::build_core_program`), which RE-READS every loaded module's
/// source from disk via search paths EXCEPT the fixed default package
/// (needs UNCHECKED decls, not `loaded`'s own already-checked copies —
/// see that function's doc comment), so this test needs `init/meta.mo` to
/// be findable there too, exactly as it would be for any real file that
/// `use`s it.
fn loaded_with_init_meta() -> LoadedModules {
  let mut loaded = default_modules().unwrap();
  let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
  let repo_root = manifest_dir
    .parent()
    .expect("core crate's manifest dir has a parent directory");
  loaded.set_search_paths(SearchPaths::new(vec![repo_root.to_path_buf()]));
  let path = ModulePath::new(vec![
    Identifier::new("init".to_string()),
    Identifier::new("meta".to_string()),
  ]);
  let parsed = parse_file(include_str!("../../../init/meta.mo").into()).unwrap();
  let checked = type_check_module_decls_new(&path, parsed.decls, &loaded).unwrap();
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls: checked,
      module_doc: None,
    },
  ));
  loaded
}

fn expand_and_type_check_with(input: &str, loaded: &LoadedModules) -> Result<(), String> {
  let path = ModulePath::top("test_meta");
  let parsed = parse_file(input.into()).map_err(|e| format!("{e}"))?;
  type_check_module_decls_new(&path, parsed.decls, loaded)
    .map(|_| ())
    .map_err(|e| format!("{e}"))
}

/// Checks `expand_macros`'s own OUTPUT directly, rather than feeding the
/// expanded decls on into `main`/further type-checking — a `#[test]` in
/// the SAME file referencing the meta-generated `Point_marker` decl gets
/// deliberately EXCLUDED from `current_decls` (`expand_reflect_type_info_decl`'s
/// own filter — `#[test]` defs are the natural consumers of a derive's
/// own output, so including one here would fail with a spurious "unbound
/// variable" for something that only exists once the OUTER expansion
/// finishes), so a bare `def main` isn't representative of what this
/// path actually supports; checking `expand_macros`'s return value
/// directly is the more honest test. The real Phase 2+ use case
/// (`derive_lens` etc. living in the already-loaded, already-fully-checked
/// `std/derive.mo`) doesn't go through `current_decls` at all — only a
/// user's own same-file meta function does.
#[test]
fn test_reflect_type_info_round_trips_through_a_hand_written_meta_def() {
  let loaded = loaded_with_init_meta();
  let parsed = parse_file(
    r#"
    use init.meta {TypeInfo, Decl, Expr}

    struct Point { x : I64, y : I64 }

    def my_meta (info : TypeInfo) : List Decl :=
        match info {
            type_info name ctors =>
                [Decl.d_def (String.concat name "_marker") [] (Expr.e_var "String") (Expr.e_str name)]
        }

    reflect_type_info! Point my_meta
    "#
    .into(),
  )
  .unwrap();
  let elaborated = elaborate_decls(parsed.decls, &loaded);
  let path = ModulePath::top("test_meta");
  let expanded = expand_macros(elaborated, &loaded, &path);
  let expanded = match &expanded {
    Ok(e) => e,
    Err(e) => panic!("reflect_type_info! round-trip error: {e}"),
  };
  let found = expanded.iter().any(|ctx| match ctx.value() {
    Decl::Def(def) => def.name.to_string() == "Point_marker",
    _ => false,
  });
  assert!(
    found,
    "reflect_type_info! should build a TypeInfo value, invoke the named meta def, and reify \
     its List Decl result into a real `Point_marker` declaration — got: {expanded:#?}"
  );
}

#[test]
fn test_reflect_type_info_blocks_impure_natives_with_a_clear_error() {
  let loaded = loaded_with_init_meta();
  let r = expand_and_type_check_with(
    r#"
    use init.meta {TypeInfo, Decl}

    #[native "print_str"]
    def my_print (s : String) : I64

    struct Point { x : I64, y : I64 }

    def bad_meta (info : TypeInfo) : List Decl :=
        match info {
            type_info name ctors =>
                let ignored : I64 := my_print name in
                List.empty
        }

    reflect_type_info! Point bad_meta
    "#,
    &loaded,
  );
  let err = r.expect_err("a meta def calling an impure native must fail, not succeed");
  assert!(
    err.contains("print_str") && err.to_lowercase().contains("pure"),
    "expected a clear purity-sandbox error naming the blocked native, got: {err}"
  );
}

/// End-to-end regression test for the real `std/derive.mo` (loaded from
/// disk, exactly as any `use std.derive {derive_lens}` file would) rather
/// than a hand-written stand-in meta def — this is the actual Phase 2
/// target, and caught two real bugs no isolated unit test surfaced:
/// (1) `MetaEvalContext::build`'s whole-program capture pass re-checking
/// `loaded`'s own already-checked `Decl`s directly (instead of
/// `build_core_program`'s documented unchecked-decls-re-read-from-source
/// pattern) corrupted every generic def in `init`; (2) `current_path` not
/// matching the file's own registration in `loaded` meant
/// `build_core_program` re-read this file's ORIGINAL on-disk source
/// (still containing the triggering `derive_lens!` call) as if it were a
/// second, different module — recursing without bound (a real stack
/// overflow). Asserts on the exact generated shape, in particular that
/// `Point.x`'s `Decl::Def` name is a proper two-segment `ModulePath`
/// (`["Point", "x"]`) — a `mpt("Point.x")`-style single-segment name
/// with a literal `.` inside one `Identifier` (an earlier, real bug here
/// too) is invisible to any ordinary `Point.x` reference elsewhere, which
/// the parser resolves as a genuine two-segment qualified path.
#[test]
fn test_derive_lens_end_to_end_against_the_real_std_derive_mo() {
  let mut loaded = default_modules().unwrap();
  let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
  let repo_root = manifest_dir
    .parent()
    .expect("core crate's manifest dir has a parent directory");
  loaded.set_search_paths(SearchPaths::new(vec![repo_root.to_path_buf()]));
  let loaded = crate::term::module::load_module_files(
    &ModulePath::new(vec![
      Identifier::new("std".to_string()),
      Identifier::new("derive".to_string()),
    ]),
    loaded,
  )
  .unwrap();

  let parsed = parse_file(
    r#"
    use std.derive {derive_lens}

    struct Point { x : I64, y : I64 }

    derive_lens! Point
    "#
    .into(),
  )
  .unwrap();
  let elaborated = elaborate_decls(parsed.decls, &loaded);
  let path = ModulePath::top("test_derive_lens_e2e");
  let expanded = match expand_macros(elaborated, &loaded, &path) {
    Ok(d) => d,
    Err(e) => panic!("derive_lens! Point failed to expand: {e}"),
  };
  for expected in ["Point.x", "Point.y"] {
    let expected_path = ModulePath::new(
      expected
        .split('.')
        .map(|s| Identifier::new(s.to_string()))
        .collect(),
    );
    let found = expanded.iter().any(|ctx| match ctx.value() {
      Decl::Def(def) => def.name == expected_path,
      _ => false,
    });
    assert!(
      found,
      "expected a generated `{expected}` def with module path {expected_path:?} — got: {expanded:#?}"
    );
  }
}
