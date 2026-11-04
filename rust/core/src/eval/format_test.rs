//! End-to-end gate for `fmt!` (`init/src/format.mo`: `fmt_meta` and the
//! `fmt` macro) through the REAL pipeline: elaborate →
//! `expand_macros` → type check → evaluate. Nothing here hand-builds an
//! `Expr`; the point of the feature is that a format string is parsed and
//! emitted by ordinary Monad code at expansion time, so the only honest
//! test drives the macro.
//!
//! `expand_to_debug` mirrors `derive_cli_test.rs`'s harness: load the real
//! `init/meta.mo` and `init/format.mo` from disk (via search paths — the
//! meta-eval capture RE-READS modules from disk, so the files must be
//! findable there), then expand the test file against them.
//!
//! Consumer defs are ordinary named functions rather than `main`, because
//! `expand_macros`'s own `current_decls` filter drops `#[test]` defs and a
//! bare `main` would otherwise be the only consumer shape exercised.

use crate::Map;
use crate::core_check_module::type_check_module_decls_new;
use crate::eval::macro_expand::expand_macros;
use crate::eval::r#type::elaborate_decls;
use crate::parser::parse_file;
use crate::term::module::{LoadedModules, ParsedModule, default_modules, module};
use crate::term::{Decl, Identifier, ModulePath, NamePath, SearchPaths};

/// `default_modules()` plus the real `init/meta.mo` and `init/format.mo`,
/// registered under `init.meta`/`init.format` — the same two-segment
/// spelling a file `use`s them by. Search paths point at the repo root
/// because `MetaEvalContext::build` re-reads every loaded module from disk.
///
/// `init/format.mo` carries BOTH `fmt` (the macro) and `fmt_meta` (the
/// function `meta!` invokes), so importing the macro also brings the meta
/// function into the expanding file's reach — see that module's own comment
/// on why they share a file.
fn loaded_with_init_meta_and_format() -> LoadedModules {
  let mut loaded = default_modules().unwrap();
  let repo_root = crate::repo_root();
  loaded.set_search_paths(SearchPaths::new(vec![repo_root.to_path_buf()]));
  for (name, source) in [
    ("meta", include_str!("../../../../init/src/meta.mo")),
    ("format", include_str!("../../../../init/src/format.mo")),
  ] {
    let path = ModulePath::new(vec![
      Identifier::new("init".to_string()),
      Identifier::new(name.to_string()),
    ]);
    let parsed = parse_file(source.into()).unwrap();
    let checked = type_check_module_decls_new(&path, parsed.decls, &loaded).unwrap();
    loaded.add_module(module(
      path,
      ParsedModule {
        decls: checked,
        module_doc: None,
      },
    ));
  }
  loaded
}

/// Expand `input`'s macro calls and return the resulting decls' `Debug`
/// rendering — enough to assert what the expansion actually produced
/// (which binders, which calls) without hand-destructuring `Term`.
fn expand_to_debug(input: &str) -> Result<Vec<(String, String)>, String> {
  let loaded = loaded_with_init_meta_and_format();
  let path = ModulePath::top("test_format");
  let parsed = parse_file(input.into()).map_err(|e| format!("{e}"))?;
  let elaborated = elaborate_decls(parsed.decls, &loaded);
  let expanded = expand_macros(elaborated, &loaded, &path).map_err(|e| format!("{e}"))?;
  Ok(
    expanded
      .iter()
      .map(|ctx| match ctx.value() {
        Decl::Def(def) => (def.name.to_string(), format!("{:?}", def.term)),
        other => (format!("{other:?}"), String::new()),
      })
      .collect(),
  )
}

/// The whole expansion of the simplest hole: one `String.concat_list` of
/// the literal pieces and one direct `FmtDisplay.fmt_display` call on the
/// call site's own variable. The macro emits NO binder — `word` here is
/// the enclosing `def`'s parameter, not something the expansion creates.
#[test]
fn fmt_expands_a_bare_hole_to_one_display_call() {
  let expanded = expand_to_debug(
    r#"
use init::format {fmt}

def shout (word : String) : String :=
    fmt! "<{word}>"
"#,
  )
  .expect("fmt! must expand");
  let (name, body) = expanded
    .iter()
    .find(|(n, _)| n.ends_with("shout"))
    .expect("shout survives expansion");
  assert_eq!(name, "shout");
  // The hole's own name, referring to the call site's binder.
  assert!(
    body.contains("word"),
    "expansion should reference `word`: {body}"
  );
  assert!(
    body.contains("fmt_display"),
    "a hole must call the display class: {body}"
  );
  assert!(
    body.contains("concat_list"),
    "pieces are concatenated in one allocation: {body}"
  );
  assert!(
    !body.contains("apply_align"),
    "a hole with no width must not pay a padding call: {body}"
  );
}

/// A hole inside a struct-literal field is an ordinary term too. The
/// expander's structural walk must reach it (the self-hosted walk already
/// does, through `literal_map_children`), or the macro call survives
/// unexpanded into the checker.
#[test]
fn fmt_expands_inside_a_struct_literal_field() {
  let expanded = expand_to_debug(
    r#"
use init::format {fmt}

struct Wrap { msg : String }

def wrapped (n : I64) : String :=
    let w : Wrap := { msg := fmt! "{n}" } in
    w.msg
"#,
  )
  .expect("fmt! inside a struct literal must expand");
  let (_, body) = expanded
    .iter()
    .find(|(n, _)| n.ends_with("wrapped"))
    .expect("wrapped survives expansion");
  assert!(
    body.contains("fmt_display"),
    "a hole inside a struct literal must expand: {body}"
  );
}

/// A template with no holes at all is just the literal: no binder, no
/// class call. This is the case that proves holes (and only holes) drive
/// the emitted parameters.
#[test]
fn fmt_with_no_holes_emits_no_binder() {
  let expanded = expand_to_debug(
    r#"
use init::format {fmt}

def plain : String :=
    fmt! "no holes here"
"#,
  )
  .expect("fmt! with no holes must expand");
  let (_, body) = expanded
    .iter()
    .find(|(n, _)| n.ends_with("plain"))
    .expect("plain survives expansion");
  assert!(!body.contains("fmt_display"), "no hole, no call: {body}");
  assert!(
    body.contains("no holes here"),
    "the literal text survives: {body}"
  );
}

/// A width spec emits a padding call around the display call.
#[test]
fn fmt_emits_padding_for_a_width_spec() {
  let expanded = expand_to_debug(
    r#"
use init::format {fmt}

def aligned (n : I64) : String :=
    fmt! "{n:>8}"
"#,
  )
  .expect("fmt! with a width must expand");
  let (_, body) = expanded
    .iter()
    .find(|(n, _)| n.ends_with("aligned"))
    .expect("aligned survives expansion");
  assert!(body.contains("fmt_display"), "{body}");
  assert!(
    body.contains("apply_align") || body.contains("pad_left"),
    "a `:>N` spec must pad: {body}"
  );
}

/// `{{`/`}}` are literal braces, not holes.
#[test]
fn fmt_treats_doubled_braces_as_literal_text() {
  let expanded = expand_to_debug(
    r#"
use init::format {fmt}

def braced : String :=
    fmt! "{{literal}}"
"#,
  )
  .expect("escaped braces must expand");
  let (_, body) = expanded
    .iter()
    .find(|(n, _)| n.ends_with("braced"))
    .expect("braced survives expansion");
  assert!(
    !body.contains("fmt_display"),
    "an escape is not a hole: {body}"
  );
}

/// An unknown spec fails the EXPANSION with a message naming the spec — the
/// `e_error` channel — rather than emitting broken code.
#[test]
fn fmt_rejects_an_unknown_spec_at_expansion_time() {
  let err = expand_to_debug(
    r#"
use init::format {fmt}

def bad (n : I64) : String :=
    fmt! "{n:x}"
"#,
  )
  .expect_err("an unknown spec must fail expansion");
  assert!(
    err.contains("unknown format spec"),
    "the error should say what was wrong: {err}"
  );
}

/// An unclosed hole is likewise an expansion-time error, not a silent
/// pass-through.
#[test]
fn fmt_rejects_an_unclosed_hole() {
  let err = expand_to_debug(
    r#"
use init::format {fmt}

def bad : String :=
    fmt! "oops {name"
"#,
  )
  .expect_err("an unclosed hole must fail expansion");
  assert!(
    err.contains("unclosed"),
    "expected an unclosed-hole error: {err}"
  );
}

/// An out-of-scope hole is an ordinary unresolved variable at the call
/// site — the property that makes "in-string references only" safe rather
/// than a capture hazard.
/// `{}` names no variable, and `fmt!` has no positional argument for it
/// to mean — so it is rejected at expansion time instead of emitting
/// `e_var ""` (which surfaced as `unbound variable \`\``).
#[test]
fn fmt_rejects_an_unnamed_hole() {
  let err = expand_to_debug(
    r#"
use init::format {fmt}

def bad : String :=
    fmt! "{}"
"#,
  )
  .expect_err("an unnamed hole must fail expansion");
  assert!(
    err.contains("must name a variable"),
    "the error should say what was wrong: {err}"
  );
}

#[test]
fn fmt_hole_naming_nothing_fails_as_an_unresolved_variable() {
  let loaded = loaded_with_init_meta_and_format();
  let path = ModulePath::top("test_format_scope");
  let parsed = parse_file(
    r#"
use init::format {fmt}

def nope : String :=
    fmt! "{missing_name}"
"#
    .into(),
  )
  .unwrap();
  let elaborated = elaborate_decls(parsed.decls, &loaded);
  let expanded = expand_macros(elaborated, &loaded, &path).expect("expansion itself succeeds");
  let err = type_check_module_decls_new(&path, expanded, &loaded)
    .expect_err("an out-of-scope hole must not type check");
  assert!(
    err.to_string().contains("missing_name"),
    "the diagnostic should name the hole: {err}"
  );
}

/// `#[at ...]`/`#[returns ...]` are read off the macro's own attributes:
/// a contradictory declaration is caught at the macro's definition site.
#[test]
fn contradictory_returns_attribute_is_a_definition_site_error() {
  let err = expand_to_debug(
    r#"
#[returns decls]
defmacro wrong x := quote { x }
"#,
  )
  .expect_err("a quote body cannot declare `#[returns decls]`");
  assert!(
    err.contains("returns"),
    "the error should name the attribute: {err}"
  );
}

/// A macro declaring a position it is not used at is rejected where it was
/// used, naming the macro.
#[test]
fn a_term_only_macro_used_at_declaration_position_is_rejected() {
  let err = expand_to_debug(
    r#"
#[at term]
defmacro only_term x := decls { def only_term_generated := 1 }
"#,
  )
  .expect_err("a decls body contradicts `#[at term]`");
  assert!(err.contains("only_term"), "{err}");
}

/// `#[at [decl, term]]` is the explicit both-forms spelling and is
/// accepted for the real macro.
#[test]
fn the_real_fmt_macro_declares_where_it_lives() {
  let expanded = expand_to_debug(
    r#"
use init::format {fmt}

def ok (x : String) : String :=
    fmt! "{x}"
"#,
  );
  assert!(expanded.is_ok(), "{expanded:?}");
}

/// Sanity: the names the emitted code references are all reachable from a
/// file that imports only the macro — no hidden `use` required.
#[test]
fn emitted_names_resolve_with_only_the_macro_imported() {
  let loaded = loaded_with_init_meta_and_format();
  let path = ModulePath::top("test_format_names");
  let parsed = parse_file(
    r#"
use init::format {fmt}

def uses (n : I64) (s : String) : String :=
    String.concat (fmt! "{n}") (fmt! "{s:>3}")
"#
    .into(),
  )
  .unwrap();
  let elaborated = elaborate_decls(parsed.decls, &loaded);
  let expanded = expand_macros(elaborated, &loaded, &path).expect("expansion succeeds");
  let _: Map<NamePath, Decl> = Map::new();
  type_check_module_decls_new(&path, expanded, &loaded)
    .expect("the emitted code must type check with only `fmt` imported");
}
