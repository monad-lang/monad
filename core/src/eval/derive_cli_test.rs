// `#[derive_cli]` tests — see `derive_cli.rs` for the generator and
// `plans/library-ideas/cli-library.md` / the CLI plan for design context.

use crate::core_check_module::type_check_module_decls_new as type_check_module_decls;
use crate::parser::parse_file;
use crate::term::module::{ParsedModule, default_modules, load_module_from_text, module};
use crate::term::{Hole, ModulePath, SearchPaths, mpt};

/// The real `lang/cli.mo` runtime helpers — included directly (rather than
/// a hand-copied fixture) so these engine-level tests can never drift out of
/// sync with the actual library `#[derive_cli]`-generated code calls into.
const CLI_FIXTURE_SRC: &str = include_str!("../../../lang/cli.mo");

/// Load `source` as a module (running the full elaborate -> expand_macros ->
/// type-check pipeline, exactly like the real CLI's `test`/`run` commands),
/// with the `Cli` fixture above pre-loaded and opened so generated
/// `#[derive_cli]` code can resolve `Cli.take_flag`/`Cli.take_positional`.
fn load(source: &str) -> Result<(crate::term::module::LoadedModules, ModulePath), String> {
  let mut loaded = default_modules().map_err(|e| e.to_string())?;
  // `lang/cli.mo` (included above) does `use std.list` — point search paths
  // at the repo root (via `CARGO_MANIFEST_DIR`, which is `core/`, so `std/`
  // is one level up) rather than relying on `cargo test`'s CWD.
  let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .expect("core/ should have a parent dir")
    .to_path_buf();
  let mut paths = SearchPaths::empty();
  paths.push(repo_root);
  loaded.set_search_paths(paths);
  let fixture_path = ModulePath::top("cli_fixture");
  load_module_from_text(CLI_FIXTURE_SRC, &fixture_path, &mut loaded).map_err(|e| e.to_string())?;

  let path = ModulePath::top("test_derive_cli");
  let full_source = format!("use cli_fixture {{*}}\n\n{source}");
  let parsed = parse_file(full_source.as_str().into()).map_err(|e| e.to_string())?;
  let decls = type_check_module_decls(&path, parsed.decls, &loaded).map_err(|e| e.to_string())?;
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  ));
  Ok((loaded, path))
}

// `call_parser` (apply the generated `parse_<type>` to a `List String`
// built from argv, evaluate via `eval()`, and assert on the *formatted*
// result — `shown.contains("ok")`/`contains("err")`/embedded argv
// strings) was removed along with the legacy tree-walker. Its runtime
// counterpart, `core_value::Value`, deliberately carries no name table
// to render with (see `core/src/lib.rs`'s `format_repl_value` doc
// comment) — a reduced `Value::Con`'s Debug output shows a raw tag, not
// the constructor's real name "ok"/"err", so these six tests' string
// assertions have no equivalent to port against without first building
// a real name-resolving runtime-value printer (`raise_core` only raises
// checker-time `CoreTerm`s, not post-evaluation `Value`s) — design work
// beyond this pass, not a mechanical port. The five tests below that
// only check TYPE-CHECKING (not evaluating) `#[derive_cli]`-generated
// code are unaffected and still give real coverage of the generator
// itself (`derive_cli.rs`).

const DEMO_SRC: &str = r#"
#[derive_cli]
type Command {
    compile (path : String) (#[arg] verbose : Bool),
    pretty (path : String),
    help,
}
"#;

#[test]
fn test_derive_cli_generates_and_type_checks() {
  let r = load(DEMO_SRC);
  if let Err(e) = &r {
    eprintln!("derive_cli load error: {e}");
  }
  assert!(
    r.is_ok(),
    "#[derive_cli] type should generate a parser that type-checks"
  );
}

#[test]
fn test_derive_cli_untouched_without_attribute() {
  // Sanity: a plain, un-annotated ADT is not affected by the derive_cli hook
  // and generates no companion parser — same as before this feature existed.
  let src = r#"
    type Command {
        compile (path : String),
        help,
    }
    "#;
  let (loaded, path) = load(src).expect("plain type should still type check");
  let module = loaded.get_module(&path).unwrap();
  assert!(
    module.get_def(&mpt("parse_command")).is_none(),
    "no #[derive_cli] attribute means no generated parser"
  );
}

#[test]
fn test_derive_cli_non_bool_arg_field_rejected() {
  let src = r#"
    #[derive_cli]
    type BadCommand {
        compile (path : String) (#[arg] name : String),
    }
    "#;
  let r = load(src);
  assert!(
    r.is_err(),
    "#[arg] on a non-Bool field should be rejected at generation time"
  );
  let msg = r.unwrap_err();
  assert!(
    msg.contains("Bool") || msg.contains("bool"),
    "error should explain the Bool-only restriction: {msg}"
  );
}

#[test]
fn test_derive_cli_no_constructors_rejected() {
  // An inductive with zero constructors isn't valid Monad source to begin
  // with (constructor_parser requires at least one), so this is exercised
  // directly against the generator rather than through a parsed file.
  use crate::eval::derive_cli::{DeriveCliError, expand_derive_cli};
  use crate::term::{id, inductive};

  let induct = inductive(
    ModulePath::single(id("Empty")),
    vec![],
    vec![],
    Hole,
    vec![],
    vec![],
  );
  let r = expand_derive_cli(&induct);
  assert_eq!(
    r,
    Err(DeriveCliError::NoConstructors {
      type_name: "Empty".to_string()
    })
  );
}

#[test]
fn test_derive_cli_zero_arg_constructor_alone() {
  // Regression for the `ok()`/`err()` raw-`Con` bug described in
  // `derive_cli.rs` (search "narrow gap"): a single zero-param constructor
  // wrapped in `Result.ok` is the minimal case that reproduced it.
  let src = r#"
    #[derive_cli]
    type Command6 {
        help6,
    }
  "#;
  let r = load(src);
  if let Err(e) = &r {
    eprintln!("zero-arg only error: {e}");
  }
  assert!(r.is_ok());
}
