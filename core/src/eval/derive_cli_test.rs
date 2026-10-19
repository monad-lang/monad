// `#[derive Cli]` tests — see `motes/clap/src/args.mo`'s `derive_cli_meta`/`derive_cli`
// for the generator (an ordinary `TypeInfo -> List Decl` Monad function
// invoked via `reflect_type_info!`, the same reflection-as-data
// metaprogramming kernel `std/derive.mo`'s four derives use — see
// `plans/review-and-reduce-the-greedy-nest.md`) and
// `plans/library-ideas/cli-library.md` / the CLI plan for design context.

use crate::core_check_module::type_check_module_decls_new as type_check_module_decls;
use crate::parser::parse_file;
use crate::term::module::{ParsedModule, default_modules, module};
use crate::term::{Identifier, ModulePath, NamePath, SearchPaths};

/// Load `source` as a module (running the full elaborate -> expand_macros ->
/// type-check pipeline, exactly like the real CLI's `test`/`run` commands),
/// with the real `motes/clap/src/args.mo` pre-loaded (via `load_module_files`, its
/// REAL on-disk path — not a synthetic name loaded from an `include_str!`
/// snippet, which the reflection-as-data port made insufficient here: since
/// `#[derive Cli]` now invokes `motes/clap/src/args.mo`'s own `derive_cli_meta`
/// through `reflect_type_info!`/`MetaEvalContext`, that whole-program
/// capture pass RE-READS every non-`init` loaded module's source from disk
/// via search paths — `lib.rs::build_core_program`'s documented
/// requirement, see `meta_compile.rs` — which only finds a module
/// registered under its real path, findable via `SearchPaths`, same as
/// `meta_test.rs`'s own `std/derive.mo` fixture) so generated
/// `#[derive Cli]` code can resolve `Cli.take_flag`/`Cli.take_positional`
/// (and `#[derive Cli]`'s own dispatch can resolve the `derive_cli`
/// decl-gen macro `motes/clap/src/args.mo` now defines).
fn load(source: &str) -> Result<(crate::term::module::LoadedModules, ModulePath), String> {
  let mut loaded = default_modules().map_err(|e| e.to_string())?;
  // `motes/clap/src/args.mo` does `use std.list`/`use init.meta` — point
  // search paths at the repo root (via `CARGO_MANIFEST_DIR`, which is `core/`,
  // so `std/`/`init/`/`motes/` are one level up) rather than relying on
  // `cargo test`'s CWD.
  //
  // `motes/` is a second root because `resolve_file_path` only ever tries
  // `<root>/<mote>/src/<rest>.mo`, never `<root>/motes/<mote>/...`: the repo
  // root alone resolves `std`/`init`, and `clap` needs the root the mote
  // actually sits directly under.
  let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .expect("core/ should have a parent dir")
    .to_path_buf();
  let motes_root = repo_root.join("motes");
  loaded.set_search_paths(SearchPaths::new(vec![repo_root, motes_root]));
  let loaded = crate::term::module::load_module_files(
    &ModulePath::new(vec![
      Identifier::new("clap".to_string()),
      Identifier::new("args".to_string()),
    ]),
    loaded,
  )
  .map_err(|e| e.to_string())?;

  let path = ModulePath::top("test_derive_cli");
  let full_source = format!("use clap::args {{*}}\n\n{source}");
  let parsed = parse_file(full_source.as_str().into()).map_err(|e| e.to_string())?;
  let decls = type_check_module_decls(&path, parsed.decls, &loaded).map_err(|e| e.to_string())?;
  let mut loaded = loaded;
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
// the constructor's real name "ok"/"err", so these four tests' string
// assertions have no equivalent to port against without first building
// a real name-resolving runtime-value printer (`raise_core` only raises
// checker-time `CoreTerm`s, not post-evaluation `Value`s) — design work
// beyond this pass, not a mechanical port. The tests below that only
// check TYPE-CHECKING (not evaluating) `#[derive Cli]`-generated code
// are unaffected and still give real coverage of the generator itself
// (`motes/clap/src/args.mo`'s `derive_cli_meta`) — and the actual end-to-end,
// argv-evaluating proof lives in `motes/clap/src/tests/cli_derive_tests.mo`, run
// through the real `test` command (see that file's own header comment).

const DEMO_SRC: &str = r#"
#[derive Cli]
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
    "#[derive Cli] type should generate a parser that type-checks"
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
    module.get_def(&NamePath::top("parse_command")).is_none(),
    "no #[derive Cli] attribute means no generated parser"
  );
}

#[test]
fn test_derive_cli_non_bool_arg_field_rejected() {
  let src = r#"
    #[derive Cli]
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

// `test_derive_cli_no_constructors_rejected` (the fifth test from before
// this port) is gone, not just renamed: it called the old Rust
// `expand_derive_cli` directly against a hand-built, zero-constructor
// `Inductive` — its OWN comment already conceded "an inductive with zero
// constructors isn't valid Monad source to begin with (constructor_parser
// requires at least one)", i.e. it was testing a shape unreachable from
// any real `.mo` file, in either the old generator or `derive_cli_meta`'s
// (still-present, still-defensive) empty-`ctors` `Decl.d_error` branch.
// Exercising this now would mean hand-building a `TypeInfo` `Value` and
// invoking `derive_cli_meta` directly through `MetaEvalContext` — real new
// test infrastructure nothing else in this file (or `meta_test.rs`) needs,
// for a case that stays unreachable in practice either way.

#[test]
fn test_derive_cli_zero_arg_constructor_alone() {
  // Regression for the `ok()`/`err()` raw-`Con` bug `derive_cli_meta`'s
  // own doc comment inherits from the Rust generator it replaced (search
  // "narrow gap" in `motes/clap/src/args.mo`): a single zero-param constructor
  // wrapped in `Result.ok` is the minimal case that reproduced it.
  let src = r#"
    #[derive Cli]
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

#[test]
fn test_derive_cli_rich_adt_generates_and_type_checks() {
  // Options (required/optional/defaulted/typed), attribute arguments, and
  // a multi-constructor ADT. The attribute string is
  // `arg(short:="v",help:="verbose")`, parsed by `motes/clap/src/attr.mo`.
  let src = r#"
    #[derive Cli]
    type Rich {
        run (path : String)
            (#[arg {short := "v", help := "verbose"}] verbose : Bool)
            (#[opt {short := "o"}] output : Option String)
            (#[opt {short := "n"}] count : I64),
        list (#[opt] all : Option String),
    }
  "#;
  let r = load(src);
  if let Err(e) = &r {
    eprintln!("rich ADT error: {e}");
  }
  assert!(r.is_ok(), "rich option ADT should type-check");
}

#[test]
fn test_derive_cli_struct_default_is_optional() {
  // Constructor params cannot carry `:=` defaults, but struct fields can
  // (`Inductive.defaults`); the struct form's type inference makes such a
  // positional optional and the decoder applies the default.
  let src = r#"
    #[derive Cli]
    struct DArgs { input : String, count : I64 := 3 }
  "#;
  let r = load(src);
  if let Err(e) = &r {
    eprintln!("struct-default error: {e}");
  }
  assert!(r.is_ok(), "struct field default should type-check");
}

#[test]
fn test_derive_cli_struct_form_generates_and_type_checks() {
  // `term::stru()` drops struct-field attributes, so this form is
  // type-inference only: Bool -> flag, everything else -> positional.
  // It must not dispatch on the synthetic `mk` constructor.
  let src = r#"
    #[derive Cli]
    struct SArgs { input : String, verbose : Bool }
  "#;
  let r = load(src);
  if let Err(e) = &r {
    eprintln!("struct-form error: {e}");
  }
  assert!(r.is_ok(), "struct form should type-check");
}

#[test]
fn test_derive_cli_unsupported_type_rejected() {
  let src = r#"
    #[derive Cli]
    type Bad { run (x : F64) }
  "#;
  let r = load(src);
  assert!(r.is_err(), "F64 positional should be rejected");
  let msg = r.unwrap_err();
  assert!(
    msg.contains("unsupported type"),
    "error should explain the unsupported type: {msg}"
  );
}

#[test]
fn test_derive_cli_short_collision_rejected() {
  let src = r#"
    #[derive Cli]
    type Coll { run (#[arg] verbose : Bool) (#[arg] version : Bool) }
  "#;
  let r = load(src);
  assert!(r.is_err(), "duplicate short flags should be rejected");
  let msg = r.unwrap_err();
  assert!(
    msg.contains("short flag"),
    "error should explain the short collision: {msg}"
  );
}

#[test]
fn test_derive_cli_duplicate_long_rejected() {
  let src = r#"
    #[derive Cli]
    type Dup {
      run (#[arg {long := "same", short := "a"}] first : Bool)
          (#[arg {long := "same", short := "b"}] second : Bool)
    }
  "#;
  let r = load(src);
  assert!(r.is_err(), "duplicate long flags should be rejected");
  let msg = r.unwrap_err();
  assert!(
    msg.contains("long flag"),
    "error should explain the long collision: {msg}"
  );
}

#[test]
fn test_derive_cli_bool_default_rejected() {
  let src = r#"
    #[derive Cli]
    struct BadFlag { verbose : Bool := true }
  "#;
  let r = load(src);
  assert!(r.is_err(), "a Bool flag with a default is unrepresentable");
  let msg = r.unwrap_err();
  assert!(
    msg.contains("cannot have a default"),
    "error should explain the Bool default: {msg}"
  );
}

#[test]
fn test_derive_cli_long_short_rejected() {
  let src = r#"
    #[derive Cli]
    type BadShort { run (#[arg {short := "vv"}] verbose : Bool) }
  "#;
  let r = load(src);
  assert!(r.is_err(), "a two-character short should be rejected");
  let msg = r.unwrap_err();
  assert!(
    msg.contains("longer than one character"),
    "error should explain the short length: {msg}"
  );
}
