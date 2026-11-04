use std::cell::RefCell;

use crate::Map;
use crate::core_value::Value;
use crate::term::module::LoadedModules;
use crate::term::{
  AttrArg, Constructor, Decl, DeclGenDef, Def, GlobalRef, Identifier, Inductive, Literal,
  ModulePath, NamePath, NameRef, Named, Par, Param, SourceContext,
  Term::{self, Ann, App, Con, Ctx, Forall, Lam, Lit, Pi, Quote, Var},
  case_with_optional_field_pattern, instance, match_term, mpvar,
};

/// Names of the built-in macro-expansion intrinsics — recognized by the
/// expander itself rather than looked up in `macro_defs`/`decl_gen_defs`,
/// since they need read access to already-parsed definitions AND to the
/// real evaluator, which ordinary template-substitution macros never do.
///
/// `meta!` is the single remaining intrinsic (see
/// `expand_builtin_decl_intrinsic`'s doc comment for the full design): a
/// SUBJECT — a type name at declaration position, an expression at term
/// position — is reified into an ordinary Monad *value*
/// (`TypeInfo`/`Expr`, `init/meta.mo`), handed to an ordinary Monad
/// function (`std/derive.mo`'s `derive_lens_meta`, `init/format.mo`'s
/// `fmt_meta`, or a user's own), evaluated for real, and the result
/// reified back into a `Term` (term position) or a `List Decl`
/// (declaration position). This replaced an earlier five-intrinsic kernel
/// (`reflect_fields!`/`reflect_ctors!`/`reflect_ctor_fields!`/
/// `reflect_pairwise_ctors!`/`reflect_set_field!`) that instead composed
/// built-in per-constructor/per-field dispatch primitives in Rust; once all
/// four derives were ported off it, it was deleted outright rather than
/// kept alongside this one.
///
/// `reflect_type_info` is retained as an accepted ALIAS of `meta` for one
/// rollout window: the last published nightly resolves it by its hardcoded
/// spelling (`lang/src/module.mo`'s `is_reflect_type_info_call`), so the
/// compiler-source surface cannot switch to `meta!` until a nightly
/// carrying this rename has been published (AGENTS.md's two-step rollout).
/// Delete the alias once `init`/`std` no longer mention it.
const BUILTIN_INTRINSICS: &[&str] = &["meta", "reflect_type_info"];

fn is_builtin_intrinsic(name: &str) -> bool {
  BUILTIN_INTRINSICS.contains(&name)
}

/// Everything a term/quote walk needs beyond the term itself: the macro
/// tables, the type table the reflection intrinsic resolves against, and —
/// built LAZILY on the first `meta!` that actually needs it — the compiled
/// snapshot of the loaded program the meta function is evaluated in.
///
/// Bundled rather than threaded as five separate parameters through every
/// recursive call of `expand_term`/`resolve_quote`/`apply_macro`: the walk
/// is the same shape at every depth, and the evaluator snapshot is
/// expensive enough (`meta_compile::MetaEvalContext::build` re-checks and
/// lowers the whole loaded program) that it must be built at most once per
/// `expand_macros` run rather than once per intrinsic call.
struct ExpandCtx<'a> {
  macro_defs: &'a Map<NamePath, Def>,
  inductives: &'a Map<NamePath, Inductive>,
  loaded: &'a LoadedModules,
  current_path: &'a ModulePath,
  /// The file's own decls, already filtered to what a meta-evaluation
  /// capture may see (see `meta_capture_decls`).
  capture_decls: &'a [SourceContext<Decl>],
  meta_eval: RefCell<Option<super::meta_compile::MetaEvalContext>>,
}

impl<'a> ExpandCtx<'a> {
  /// Run `f` against the meta-evaluation snapshot, building it on first
  /// use. `invoke` runs the real `core_eval`, which never re-enters macro
  /// expansion, so the `RefCell` borrow below can never be taken twice.
  fn with_meta_context<T>(
    &self,
    f: impl FnOnce(&mut super::meta_compile::MetaEvalContext) -> Result<T, MacroError>,
  ) -> Result<T, MacroError> {
    let mut slot = self.meta_eval.borrow_mut();
    if slot.is_none() {
      *slot = Some(super::meta_compile::MetaEvalContext::build(
        self.loaded,
        self.current_path,
        self.capture_decls,
      )?);
    }
    f(slot.as_mut().expect("just built"))
  }
}

/// Collect `Inductive` definitions from loaded modules, keyed by name (`NamePath`).
/// Mirrors `collect_loaded_macro_defs` below.
fn collect_loaded_inductives(loaded: &LoadedModules) -> Map<NamePath, Inductive> {
  let mut all = Map::new();
  for module in loaded.modules() {
    for induct in module.inductives() {
      all.insert(induct.name().clone(), induct.clone());
    }
  }
  all
}

/// Resolve a macro-argument `Term` naming a type (e.g. the `T` a `defmacro
/// derive_lens (T : Type)` was called with, already substituted to a `Var`
/// or qualified path reference by the time expansion reaches it) back to
/// its `Inductive` definition.
fn resolve_inductive<'a>(
  term: &Term,
  inductives: &'a Map<NamePath, Inductive>,
) -> Option<&'a Inductive> {
  let name = match strip_ctx(term.clone()) {
    Var { name } => name.to_name_path(),
    _ => None,
  }?;
  inductives.get(&name)
}

/// Extract a plain name reference (`Var { name: Id(_) | P(_) }`) as an
/// `Identifier` — used to read a macro argument that's meant to *name*
/// something (a field, another macro) rather than be used as an ordinary
/// value.
fn term_as_identifier(term: &Term) -> Option<Identifier> {
  match strip_ctx(term.clone()) {
    Var {
      name: NameRef::Id(id),
    } => Some(id),
    Var {
      name: NameRef::Np(path),
    } => Some(path.last().clone()),
    _ => None,
  }
}

/// Read a `#[derive BEq BOrd Debug Lens]` attribute's target list off an
/// `Inductive`. Accepts both the bare-word form (`#[derive BEq BOrd]`,
/// each a separate positional `AttrArg::Ident`) and the bracketed-group
/// form (`#[derive [BEq, BOrd]]`, one `AttrArg::Group` of `Ident`s) — both
/// already parse today via `attr_arg_parser`, no reason to accept only
/// one. Returns an empty list (not an error) when there's no `derive`
/// attribute at all — the common case, an ordinary undecorated type.
pub(crate) fn derive_attribute_targets(induct: &Inductive) -> Result<Vec<String>, MacroError> {
  let Some(attr) = induct
    .attributes
    .iter()
    .find(|a| a.name.as_str() == "derive")
  else {
    return Ok(Vec::new());
  };
  fn flatten(arg: &AttrArg, out: &mut Vec<String>) -> Result<(), MacroError> {
    match arg {
      AttrArg::Ident(id) => {
        out.push(id.as_str().to_string());
        Ok(())
      }
      AttrArg::Group(items) => {
        for item in items {
          flatten(item, out)?;
        }
        Ok(())
      }
      other => Err(MacroError::Generic(format!(
        "#[derive ...] targets must be bare names (e.g. `BEq`), got: {other:?}"
      ))),
    }
  }
  let mut targets = Vec::new();
  for arg in &attr.args {
    flatten(arg, &mut targets)?;
  }
  Ok(targets)
}

/// A `#[derive ...]` target registered by a `defmacro` via
/// `#[derive_handler <Target> ...]` — the target name(s) the attribute
/// declared, pointing at the macro `#[derive <Target>]` dispatches to
/// (the annotated `defmacro` itself) and where it was defined (for
/// duplicate-registration diagnostics).
#[derive(Debug, Clone)]
pub(crate) struct DeriveHandler {
  macro_name: Identifier,
  site: String,
}

/// Read the bare target names a `defmacro`'s `#[derive_handler ...]`
/// attribute(s) declared. Accepts the same two arg shapes
/// `derive_attribute_targets` accepts for `#[derive ...]` (bare words
/// and bracketed groups); anything else is a registration error the
/// author sees at expansion of the registering module.
fn derive_handler_targets(gd: &DeclGenDef) -> Result<Vec<String>, MacroError> {
  fn flatten(arg: &AttrArg, out: &mut Vec<String>) -> Result<(), MacroError> {
    match arg {
      AttrArg::Ident(id) => {
        out.push(id.as_str().to_string());
        Ok(())
      }
      AttrArg::Group(items) => {
        for item in items {
          flatten(item, out)?;
        }
        Ok(())
      }
      other => Err(MacroError::Generic(format!(
        "#[derive_handler ...] targets must be bare names (e.g. `Lens`), got: {other:?}"
      ))),
    }
  }
  let mut targets = Vec::new();
  for attr in &gd.attributes {
    if attr.name.as_str() != "derive_handler" {
      continue;
    }
    for arg in &attr.args {
      flatten(arg, &mut targets)?;
    }
  }
  Ok(targets)
}

/// Where a `defmacro` says it may be invoked, as declared by its
/// `#[at ...]` attribute.
///
/// Both `defmacro` forms already parse attributes (the `decls`/DeclGen form
/// and the `quote` form), so this needs no parser change — the attribute
/// vocabulary is the expander's, exactly as `#[derive_handler ...]` is.
/// Accepted spellings mirror `#[derive ...]`'s:
///
/// - `#[at decl]`, `#[at term]` — one position;
/// - `#[at [decl, term]]` — both;
/// - absent — both, i.e. wherever the body form can actually expand.
#[derive(Debug, Clone, Copy)]
struct MacroPositions {
  decl: bool,
  term: bool,
}

impl MacroPositions {
  const BOTH: MacroPositions = MacroPositions {
    decl: true,
    term: true,
  };

  fn describe(self) -> String {
    match (self.decl, self.term) {
      (true, true) => "declaration or term position".to_string(),
      (true, false) => "declaration position only".to_string(),
      (false, true) => "term position only".to_string(),
      (false, false) => "nowhere (`#[at]` lists no position)".to_string(),
    }
  }
}

/// What a `defmacro` produces, as declared by its `#[returns ...]`
/// attribute: `#[returns expr]` or `#[returns decls]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MacroReturns {
  Expr,
  Decls,
}

impl MacroReturns {
  fn describe(self) -> &'static str {
    match self {
      MacroReturns::Expr => "an expression",
      MacroReturns::Decls => "declarations",
    }
  }
}

/// Flatten one `#[at ...]`/`#[returns ...]` argument into the bare names it
/// lists — the same two shapes `#[derive ...]` accepts.
fn attr_bare_names(attr: &crate::term::Attribute) -> Result<Vec<String>, MacroError> {
  fn flatten(
    attr: &crate::term::Attribute,
    arg: &AttrArg,
    out: &mut Vec<String>,
  ) -> Result<(), MacroError> {
    match arg {
      AttrArg::Ident(id) => {
        out.push(id.as_str().to_string());
        Ok(())
      }
      AttrArg::Group(items) => {
        for item in items {
          flatten(attr, item, out)?;
        }
        Ok(())
      }
      other => Err(MacroError::Generic(format!(
        "#[{} ...] takes bare names (e.g. `{}`), got: {other:?}",
        attr.name.as_str(),
        attr.name.as_str()
      ))),
    }
  }
  let mut names = Vec::new();
  for arg in &attr.args {
    flatten(attr, arg, &mut names)?;
  }
  Ok(names)
}

/// Read a `defmacro`'s `#[at ...]` declaration(s). Absent means
/// `MacroPositions::BOTH`: a macro that never says where it lives is
/// usable wherever its body form can expand, which is what every macro
/// written before this attribute existed relies on.
fn macro_positions(attributes: &[crate::term::Attribute]) -> Result<MacroPositions, MacroError> {
  let mut positions = MacroPositions {
    decl: false,
    term: false,
  };
  let mut declared = false;
  for attr in attributes {
    if attr.name.as_str() != "at" {
      continue;
    }
    declared = true;
    for name in attr_bare_names(attr)? {
      match name.as_str() {
        "decl" => positions.decl = true,
        "term" => positions.term = true,
        other => {
          return Err(MacroError::Generic(format!(
            "#[at ...] understands `decl` and `term`, got `{other}`"
          )));
        }
      }
    }
  }
  Ok(if declared {
    positions
  } else {
    MacroPositions::BOTH
  })
}

/// Read a `defmacro`'s `#[returns ...]` declaration, if it has one. Absent
/// means "infer from the body form", which `check_macro_declaration` then
/// verifies the attribute against.
fn macro_returns(
  attributes: &[crate::term::Attribute],
) -> Result<Option<MacroReturns>, MacroError> {
  let mut found: Option<MacroReturns> = None;
  for attr in attributes {
    if attr.name.as_str() != "returns" {
      continue;
    }
    let names = attr_bare_names(attr)?;
    let [only] = names.as_slice() else {
      return Err(MacroError::Generic(format!(
        "#[returns ...] takes exactly one of `expr`/`decls`, got {} names",
        names.len()
      )));
    };
    let this = match only.as_str() {
      "expr" => MacroReturns::Expr,
      "decls" => MacroReturns::Decls,
      other => {
        return Err(MacroError::Generic(format!(
          "#[returns ...] understands `expr` and `decls`, got `{other}`"
        )));
      }
    };
    if found.is_some_and(|prev| prev != this) {
      return Err(MacroError::Generic(
        "#[returns ...] may be declared only once".to_string(),
      ));
    }
    found = Some(this);
  }
  Ok(found)
}

/// The one place a macro's own `#[at]`/`#[returns]` declarations are
/// checked against what its body actually is. Runs at the macro's
/// DEFINITION site (`expand_macros`'s `Decl::DefMacro`/`Decl::DeclGen`
/// arm), so a contradictory attribute is an error in the file that wrote
/// it rather than a puzzling failure at some later call.
///
/// `body_form` — what the body actually produces — is not a judgement call:
/// `defmacro f x := decls { ... }` is a `Decl::DeclGen` (declarations),
/// while `defmacro f x := quote { ... }` is a `Decl::DefMacro` whose body
/// is a `quote` (an expression).
fn check_macro_declaration(
  name: &NamePath,
  attributes: &[crate::term::Attribute],
  body_form: MacroReturns,
) -> Result<(), MacroError> {
  macro_positions(attributes)?;
  if let Some(declared) = macro_returns(attributes)? {
    if declared != body_form {
      return Err(MacroError::Generic(format!(
        "macro `{name}` declares `#[returns {}]` but its body produces {}",
        match declared {
          MacroReturns::Expr => "expr",
          MacroReturns::Decls => "decls",
        },
        body_form.describe()
      )));
    }
  }
  Ok(())
}

/// Reject a TERM-position use of a macro whose `#[at ...]` excludes it.
/// Checked at the dispatch site rather than at expansion of the body, so
/// the diagnostic names the macro and the position the author actually
/// wrote.
fn require_position(def: &Def, body_form: MacroReturns) -> Result<(), MacroError> {
  let positions = macro_positions(&def.attributes)?;
  if positions.term {
    return Ok(());
  }
  let produced = match body_form {
    MacroReturns::Expr => "an expression",
    MacroReturns::Decls => "declarations",
  };
  Err(MacroError::Generic(format!(
    "macro `{}` is declared `{}` but was used at term position (it produces {produced})",
    def.name,
    positions.describe()
  )))
}

/// The declaration-position counterpart of `require_position`.
fn require_decl_position(
  name: &Identifier,
  attributes: &[crate::term::Attribute],
) -> Result<(), MacroError> {
  let positions = macro_positions(attributes)?;
  if positions.decl {
    return Ok(());
  }
  Err(MacroError::Generic(format!(
    "macro `{name}` is declared `{}` but was used at declaration position (it produces an expression)",
    positions.describe()
  )))
}

/// Insert one registration, erroring on a duplicate: two DIFFERENT macros
/// registering the same target name would otherwise resolve last-wins,
/// silently wrong across mote load order. The SAME macro re-registering
/// a target is idempotent, not a conflict — the same physical file can
/// sit in `loaded` under two module paths at once (a multi-file `check`
/// names the target module by its file path while dependents import it
/// by its mote-qualified path), and that double-load must not error.
fn register_derive_handler(
  registry: &mut Map<String, DeriveHandler>,
  target: &str,
  macro_name: Identifier,
  site: String,
) -> Result<(), MacroError> {
  if let Some(existing) = registry.get(target) {
    if existing.macro_name != macro_name {
      return Err(MacroError::Generic(format!(
        "duplicate derive target `{target}`: registered by macro `{}` in {} and macro `{macro_name}` in {site}",
        existing.macro_name, existing.site
      )));
    }
    return Ok(());
  }
  registry.insert(target.to_string(), DeriveHandler { macro_name, site });
  Ok(())
}

/// The `#[derive <Target>]` target registry: target name -> the macro
/// that implements it, built per `expand_macros` run from the current
/// module's own `defmacro` registrations plus every loaded module's —
/// mirroring how `decl_gen_defs` itself is collected (current module
/// takes priority, no program-level mutable state). The use-gate stays
/// where it always was: dispatch synthesizes an ordinary
/// `expand_macro_call`, so a target only resolves if its macro is in
/// `decl_gen_defs` (same as a hand-written `derive_beq! T` call).
fn derive_handler_registry(
  decls: &[SourceContext<Decl>],
  loaded: &LoadedModules,
  current_path: &ModulePath,
) -> Result<Map<String, DeriveHandler>, MacroError> {
  let mut registry: Map<String, DeriveHandler> = Map::new();
  let current_site = format!("module `{current_path}`");
  for ctx in decls {
    if let Decl::DeclGen(gd) = ctx.value() {
      for target in derive_handler_targets(gd)? {
        let macro_name = gd
          .name
          .segments()
          .last()
          .cloned()
          .expect("defmacro name is non-empty");
        register_derive_handler(&mut registry, &target, macro_name, current_site.clone())?;
      }
    }
  }
  for module in loaded.modules() {
    // The module currently being expanded can already sit in `loaded`
    // with a STALE copy of its own source (see `expand_macros`'s doc
    // comment) — its registrations come from the fresh `decls` walk
    // above, so the stale copy must not be counted as a second site.
    if module.path() == current_path {
      continue;
    }
    for (_path, gd_ctx) in module.decl_gens_map() {
      let gd = gd_ctx.value();
      for target in derive_handler_targets(gd)? {
        let macro_name = gd
          .name
          .segments()
          .last()
          .cloned()
          .expect("defmacro name is non-empty");
        register_derive_handler(
          &mut registry,
          &target,
          macro_name,
          format!("module `{}`", module.path()),
        )?;
      }
    }
  }
  Ok(registry)
}

/// Lenient target → macro-name map for pre-expansion analyses
/// (`module.rs`'s `collect_macro_call_names`): registrations from the
/// given decls plus every loaded module, first-wins, malformed entries
/// skipped. The strict duplicate/malformed errors belong to
/// `derive_handler_registry` (run by `expand_macros`); this is only for
/// unused-import analysis, which must never fail.
pub(crate) fn derive_handler_macro_names(
  decls: &[SourceContext<Decl>],
  loaded: &LoadedModules,
) -> Map<String, Identifier> {
  let mut names: Map<String, Identifier> = Map::new();
  let lenient_targets = |gd: &DeclGenDef, names: &mut Map<String, Identifier>| {
    if let Ok(targets) = derive_handler_targets(gd) {
      if let Some(macro_name) = gd.name.segments().last() {
        for target in targets {
          names.entry(target).or_insert_with(|| macro_name.clone());
        }
      }
    }
  };
  for ctx in decls {
    if let Decl::DeclGen(gd) = ctx.value() {
      lenient_targets(gd, &mut names);
    }
  }
  for module in loaded.modules() {
    for (_path, gd_ctx) in module.decl_gens_map() {
      lenient_targets(gd_ctx.value(), &mut names);
    }
  }
  names
}

/// Dispatch a built-in intrinsic invoked at **decl** position (i.e.
/// `meta! T meta_def_name` appearing where a `decls { ... }` template
/// expects a declaration — see `expand_macro_call`).
///
/// `meta!` is the ONE intrinsic (see `BUILTIN_INTRINSICS`): a macro whose
/// argument is read through the compiler's own parsed representation,
/// converted to a Monad value, handed to an ordinary Monad function at
/// expansion time, and reified back into real declarations (here) or a real
/// `Term` (`expand_builtin_term_intrinsic`). Position decides the output
/// type — this arm reifies a `List MetaDecl` — so the same intrinsic serves
/// `std/derive.mo`'s templates and `init/format.mo`'s `fmt!` without either
/// of them knowing about the other.
fn expand_builtin_decl_intrinsic(
  name: &Identifier,
  args: &[Term],
  ctx: &ExpandCtx,
) -> Result<Vec<Decl>, MacroError> {
  match name.as_str() {
    "meta" | "reflect_type_info" => expand_meta_decl(name, args, ctx),
    other => Err(MacroError::Generic(format!(
      "intrinsic `{other}` is not valid at declaration position"
    ))),
  }
}

/// A built-in intrinsic invoked at **term** position (appearing inside an
/// ordinary expression — see `expand_term`/`resolve_quote`): the same
/// `meta!` subject/function pair as the declaration-position form, with the
/// evaluated result reified as a `Term` instead of a `List MetaDecl`.
fn expand_builtin_term_intrinsic(
  name: &Identifier,
  args: &[Term],
  ctx: &ExpandCtx,
) -> Result<Term, MacroError> {
  match name.as_str() {
    "meta" | "reflect_type_info" => expand_meta_term(name, args, ctx),
    other => Err(MacroError::Generic(format!(
      "intrinsic `{other}` is not valid at term position"
    ))),
  }
}

/// `meta! subject meta_def_name` — the reflection-as-data kernel (see
/// `plans/review-and-reduce-the-greedy-nest.md` and, for the format-string
/// use, `init/format.mo`): build the subject's Monad *value* form, invoke
/// the named top-level `def` (`meta_def_name` — an ordinary Monad function,
/// e.g. `std/derive.mo`'s `derive_lens : TypeInfo -> List MetaDecl`, NOT a
/// `defmacro` template) with that value as its sole argument, via the real
/// production evaluator (`core_eval`, through `meta_compile::
/// MetaEvalContext`, sandboxed to `core_native::is_pure_native`'s allowlist
/// — no IO/concurrency), and reify the result back into real syntax.
///
/// Unlike every template-substitution macro, `meta_def_name` is invoked
/// through ordinary function CALL semantics (real evaluation, arbitrary
/// Monad computation — `List.map`/`match`/recursion), so it never needs to
/// be registered in `decl_gen_defs`/`macro_defs` at all.
fn expand_meta_decl(
  name: &Identifier,
  args: &[Term],
  ctx: &ExpandCtx,
) -> Result<Vec<Decl>, MacroError> {
  let (subject, meta_def_name) = meta_call_parts(name, args, ctx.inductives)?;
  let result_value = ctx.with_meta_context(|eval| {
    eval.invoke(
      &GlobalRef::Local(NamePath::single(meta_def_name)),
      vec![subject],
    )
  })?;
  super::meta_reflect::reify_decls_value_to_decls(result_value, ctx.inductives)
}

fn expand_meta_term(name: &Identifier, args: &[Term], ctx: &ExpandCtx) -> Result<Term, MacroError> {
  let (subject, meta_def_name) = meta_call_parts(name, args, ctx.inductives)?;
  let result_value = ctx.with_meta_context(|eval| {
    eval.invoke(
      &GlobalRef::Local(NamePath::single(meta_def_name)),
      vec![subject],
    )
  })?;
  super::meta_reflect::reify_value_to_term(result_value, ctx.inductives)
}

/// The two halves every `meta!` invocation shares, at either position: the
/// already-written subject term, reflected into the value form the meta
/// function expects, and the plain name of that function.
fn meta_call_parts(
  name: &Identifier,
  args: &[Term],
  inductives: &Map<NamePath, Inductive>,
) -> Result<(Value, Identifier), MacroError> {
  let [subject_arg, meta_def_name_arg] = args else {
    return Err(MacroError::Generic(format!(
      "{name}! expects 2 arguments (a subject and a meta-function name), got {}",
      args.len()
    )));
  };
  let subject = reflect_subject(name, subject_arg, inductives)?;
  let meta_def_name = term_as_identifier(meta_def_name_arg).ok_or_else(|| {
    MacroError::Generic(format!(
      "{name}!: second argument must name a top-level def"
    ))
  })?;
  Ok((subject, meta_def_name))
}

/// The single reflection step `meta!` performs, whatever the position:
/// a name reflecting to its `TypeInfo` value, or a string literal
/// reflecting to itself.
///
/// This is the one place position does NOT matter — `std/derive.mo`'s
/// derives want a type's structure, while `init/format.mo`'s `fmt!` wants
/// the format string it was handed. Both are "the argument, as data" and
/// the meta function's own type decides which it accepts, so adding a
/// subject kind is a single match arm here rather than a second intrinsic.
fn reflect_subject(
  name: &Identifier,
  term: &Term,
  inductives: &Map<NamePath, Inductive>,
) -> Result<Value, MacroError> {
  let stripped = strip_ctx(term.clone());
  if let Term::Lit {
    value: Literal::Str { value },
  } = &stripped
  {
    return Ok(super::meta_reflect::string_value(value));
  }
  match resolve_inductive(&stripped, inductives) {
    Some(induct) => super::meta_reflect::build_type_info_value(induct, inductives),
    None => Err(MacroError::Generic(format!(
      "{name}!: first argument must name a known type or be a string literal"
    ))),
  }
}

/// Filter the file's own decls down to what a meta-evaluation capture may
/// see, before `meta_compile::MetaEvalContext::build` receives them:
/// `Decl::Use`/`Decl::Open`/`Decl::Infix` (import/scope context — never
/// references anything not-yet-generated, safe to always include) and every
/// `Decl::Def` EXCEPT `#[test]`-attributed ones. `#[test]` defs are
/// specifically excluded because they're the natural CONSUMERS of a
/// derive's own output (e.g. a test calling the very lens `derive_lens!` is
/// about to generate) — re-checking one this early
/// (`build_core_program`'s capture pass type-checks every decl in the
/// batch) fails with a spurious "unbound variable" for something that will
/// exist by the time the OUTER expansion finishes, confirmed directly, not
/// hypothetical. Ordinary (non-`#[test]`) same-file helper defs a same-file
/// meta function calls are kept, so that case works too — every REAL target
/// (`std/derive.mo`'s own `derive_lens_meta`, `init/format.mo`'s
/// `fmt_meta`) lives in an already-loaded module and doesn't go through
/// this path at all, only a user's own same-file meta function does.
/// `Decl::MacroCall`/`Decl::Generated` are dropped regardless (the actual
/// recursion trigger, see `meta_compile.rs`).
///
/// A `Decl::Def` whose body still contains a MACRO CALL is dropped too —
/// the second actual recursion trigger, and the one that only became
/// reachable once `meta!` gained a term-position form.
///
/// The capture pass runs the real checker, which runs `expand_macros`,
/// which expands that def's macro calls again — and a term-position
/// `meta!` inside one of them re-enters `ExpandCtx::with_meta_context` from
/// inside the capture that context is building, forever (confirmed
/// directly: an unbounded stack overflow, not hypothetical). Matching only
/// the intrinsic's own name is NOT enough, which is the trap here: the def
/// being expanded holds `fmt! "{n}"`, a call to an ordinary `defmacro`
/// whose BODY is `meta!`, so the recursion arrives one expansion step later
/// and an intrinsic-only filter misses it. Any macro call at all is
/// therefore the right thing to exclude.
///
/// Dropping those defs is precise, not a loss: a macro call is unexpanded
/// by definition at this point, so such a def cannot be checked (or be a
/// meta FUNCTION, which `current_decls` exists for) until the outer
/// expansion finishes.
fn meta_capture_decls(decls: &[SourceContext<Decl>]) -> Vec<SourceContext<Decl>> {
  decls
    .iter()
    .filter(|ctx| match ctx.value() {
      Decl::Def(def) => !def.has_test_attr() && !term_has_macro_call(&def.term),
      Decl::Use(_) | Decl::Open(_) | Decl::Infix(_) => true,
      _ => false,
    })
    .cloned()
    .collect()
}

/// Whether `term` contains a macro call (`name! ...`, built-in or not) at
/// any depth. Used only by `meta_capture_decls` above; see its doc comment
/// for why such a def must stay out of a meta-evaluation capture.
fn term_has_macro_call(term: &Term) -> bool {
  fn is_macro_head(term: &Term) -> bool {
    matches!(
      strip_ctx(term.clone()),
      Var {
        name: NameRef::Macro(_)
      }
    )
  }
  match term {
    App { fun, arg } => is_macro_head(fun) || term_has_macro_call(fun) || term_has_macro_call(arg),
    Lam { body, .. } => term_has_macro_call(body),
    Quote { term } => term_has_macro_call(term),
    Ctx { term, .. } => term_has_macro_call(term),
    Ann { term, typ } => term_has_macro_call(term) || term_has_macro_call(typ),
    Pi { arg, ret, .. } => term_has_macro_call(arg) || term_has_macro_call(ret),
    Forall { typ, body, .. } => term_has_macro_call(typ) || term_has_macro_call(body),
    Lit {
      value: Literal::If { value, then, els },
    } => term_has_macro_call(value) || term_has_macro_call(then) || term_has_macro_call(els),
    Lit {
      value: Literal::Match { value, cases },
    } => term_has_macro_call(value) || cases.iter().any(|c| term_has_macro_call(&c.value)),
    Con(Constructor { args, .. }) => args.iter().flatten().any(term_has_macro_call),
    _ => false,
  }
}

/// Recursively strip Ctx wrappers from a term.
fn strip_ctx(term: Term) -> Term {
  match term {
    Ctx { term: t, .. } => strip_ctx(*t),
    other => other,
  }
}

/// Maximum macro expansion depth to prevent infinite recursion
const MAX_EXPANSION_DEPTH: u64 = 32;

/// Error type for macro expansion failures
#[derive(Debug, Clone, PartialEq)]
pub enum MacroError {
  DepthLimitExceeded,
  NonTermReturn { name: String },
  MacroNotFound { name: String },
  Generic(String),
}

impl std::fmt::Display for MacroError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      MacroError::DepthLimitExceeded => write!(f, "macro expansion depth limit exceeded"),
      MacroError::NonTermReturn { name } => {
        write!(f, "macro `{name}` did not return a Term value")
      }
      MacroError::MacroNotFound { name } => write!(f, "macro `{name}` not found"),
      MacroError::Generic(msg) => write!(f, "{msg}"),
    }
  }
}

impl From<&MacroError> for crate::diag::Diagnostic {
  fn from(err: &MacroError) -> Self {
    crate::diag::Diagnostic {
      severity: crate::diag::Severity::Error,
      message: err.to_string(),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
      module_path: None,
    }
  }
}

/// Collect macro definitions from loaded modules, keyed by name (`NamePath`).
fn collect_loaded_macro_defs(loaded: &LoadedModules) -> Map<NamePath, Def> {
  let mut all = Map::new();
  for module in loaded.modules() {
    for (path, ctx) in module.macro_defs_map() {
      all.insert(path.clone(), ctx.value().clone());
    }
  }
  all
}

/// Collect decl-gen macro definitions from loaded modules, keyed by
/// ModulePath — mirrors `collect_loaded_macro_defs` above, for
/// `defmacro name params := decls { ... }` macros instead of `quote { ... }`
/// ones. Needed for `#[derive ...]`/`derive_lens!`-style usage: the derive
/// macros themselves live once in `std/derive.mo`, `use`d from every file
/// that wants to derive something, not redefined per file.
fn collect_loaded_decl_gen_defs(loaded: &LoadedModules) -> Map<NamePath, DeclGenDef> {
  let mut all = Map::new();
  for module in loaded.modules() {
    for (path, ctx) in module.decl_gens_map() {
      all.insert(path.clone(), ctx.value().clone());
    }
  }
  all
}

/// Expand all macro calls in declarations.
/// Runs between elaboration and type checking.
///
/// `current_path` — the `ModulePath` of the file `decls` belongs to — is
/// needed for `reflect_type_info!`'s sake (`meta_compile::MetaEvalContext`,
/// via `expand_reflect_type_info_decl`): building a `MetaEvalContext`
/// re-checks (and captures `CoreIr` for) every module in `loaded` by
/// RE-READING each one's raw source from disk
/// (`lib.rs::build_core_program`'s documented requirement — see
/// `meta_compile.rs`). If the file currently being expanded is ALREADY
/// registered in `loaded` (as the real CLI's `test`/`run` commands do,
/// ahead of checking it, for cross-file/self-reference resolution), that
/// re-read pass would pick up its ORIGINAL on-disk source — still
/// containing the very `reflect_type_info!`/`derive_lens!` call this
/// whole thing is being invoked from — and recurse without bound
/// (confirmed directly as a real, unbounded stack overflow, not
/// hypothetical). `current_path` lets `MetaEvalContext::build` route that
/// one module through its `extra_modules` parameter instead, using the
/// macro-call-filtered, in-progress decls it already has in hand rather
/// than blindly re-reading the stale, not-yet-expanded file from disk.
pub fn expand_macros(
  decls: Vec<SourceContext<Decl>>,
  loaded: &LoadedModules,
  current_path: &ModulePath,
) -> Result<Vec<SourceContext<Decl>>, MacroError> {
  // A snapshot of the file's own original decls, kept around for
  // `reflect_type_info!`'s sake (`expand_reflect_type_info_decl`) — the
  // file currently being expanded isn't yet a `loaded` module of its own
  // (that only happens once a caller finishes checking it and calls
  // `LoadedModules::add_module`), so a same-file "meta" def needs this
  // in-memory copy to be findable by `meta_compile::MetaEvalContext`,
  // mirroring `lib.rs::build_core_program`'s own `extra_modules` handling
  // for the same reason.
  let current_decls = decls.clone();

  // Collect macros from current module
  let mut macro_defs: Map<NamePath, Def> = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::DefMacro(def) => Some((def.name.clone(), def.clone())),
      _ => None,
    })
    .collect();

  // Also collect macros from all loaded modules (cross-module support)
  // Current module's macros take priority
  for (path, def) in collect_loaded_macro_defs(loaded) {
    macro_defs.entry(path).or_insert(def);
  }

  // Collect DeclGen definitions from current module
  let mut decl_gen_defs: Map<NamePath, DeclGenDef> = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::DeclGen(gd) => Some((gd.name.clone(), gd.clone())),
      _ => None,
    })
    .collect();

  // Also collect decl-gen macros from all loaded modules (cross-module
  // support, e.g. `use std.derive {derive_lens}`) — current module's
  // definitions take priority, mirroring `macro_defs` above.
  for (path, gd) in collect_loaded_decl_gen_defs(loaded) {
    decl_gen_defs.entry(path).or_insert(gd);
  }

  // Collect `Inductive` definitions the reflection intrinsic
  // (`reflect_type_info!`) can resolve a type argument against — from the
  // current module's own decls (so a `#[derive ...]`'d
  // type can be reflected on in the same file it's declared in, the
  // primary use case) and from all loaded modules (cross-module derives).
  // Current module's definitions take priority, mirroring `macro_defs`
  // above.
  let mut inductives: Map<NamePath, Inductive> = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Type(induct) => Some((induct.name().clone(), induct.clone())),
      _ => None,
    })
    .collect();
  // Trim the loaded inductives to the same dep-closure the meta-eval
  // captures (`meta_compile::dep_closure_loaded`), not the whole
  // `loaded` set. `collect_loaded_inductives` keys each inductive by its
  // bare single-segment name (`induct.name()`) with last-wins, so feeding
  // it the entire `loaded` (for `check lang`, every `lang/*.mo`) makes
  // `lang/types.mo`'s `Decl`/`Param` and `lang/core_ir.mo`'s `MatchArm`
  // silently overwrite `init/meta.mo`'s same-named meta-language types —
  // and this `inductives` map is what `reify_decls_value_to_decls` uses to
  // map a result value's constructor tag back to a name, so the reify
  // would see `lang.types`'s `def_d` where `derive_cli_meta` built
  // `init.meta`'s `d_def`, failing `check lang` even after the eval-side
  // capture was scoped. Scoping here too makes the reify see exactly
  // `init.meta`'s `Decl`/`Param`/`MatchArm`/`Expr`. The current module's
  // own types (above) still take priority via `or_insert`. (The
  // meta-language types are `MetaDecl`/`MetaParam`/`MetaMatchArm` since
  // the whole-program-qualification rename, so the `lang`-side collision
  // is gone; the closure scoping stays as the general guard.)
  let closure_loaded = super::meta_compile::dep_closure_loaded(loaded, &current_decls)?;
  for (path, induct) in collect_loaded_inductives(&closure_loaded) {
    inductives.entry(path).or_insert(induct);
  }

  // The `#[derive <Target>]` target registry, built the same way
  // `decl_gen_defs` is (current module + loaded modules): every
  // `defmacro` carrying `#[derive_handler ...]` registers its bare
  // target name(s) as dispatching to itself. `#[derive Cli]` (clap's
  // `derive_cli` macro registers the target) goes through this same
  // table — the old `#[derive_cli]` special case is gone.
  let handler_registry = derive_handler_registry(&decls, loaded, current_path)?;

  // Expand macro calls and flatten generated declarations.
  //
  // This is a work queue, not a single pass: a `Decl::MacroCall`'s
  // expansion (or a `Decl::Generated` wrapper) can itself contain further
  // `Decl::MacroCall`s that need expanding — e.g. a decl-gen macro
  // template that calls the built-in `reflect_type_info!` intrinsic, or
  // (once nested) another decl-gen macro. Re-queueing the expansion
  // result at the front (rather than appending straight to `batch`)
  // reprocesses it through the same match arms until it bottoms out in
  // concrete decls, matching how `apply_macro`/`expand_term` already
  // recurse for term-level macros.
  // One expansion context for the whole run: the intrinsic's evaluator
  // snapshot is built lazily on the first `meta!` that needs it and reused
  // by every later one (see `ExpandCtx::with_meta_context`).
  let capture_decls = meta_capture_decls(&current_decls);
  let expand_ctx = ExpandCtx {
    macro_defs: &macro_defs,
    inductives: &inductives,
    loaded,
    current_path,
    capture_decls: &capture_decls,
    meta_eval: RefCell::new(None),
  };
  let mut queue: std::collections::VecDeque<SourceContext<Decl>> = flatten_generated(decls).into();
  let mut batch = Vec::new();
  let mut iterations: u64 = 0;
  // Generous safety net against runaway expansion loops (e.g. a decl-gen
  // macro that indirectly calls itself) — not a semantic nesting-depth
  // limit like `MAX_EXPANSION_DEPTH`, just a circuit breaker.
  const MAX_QUEUE_ITERATIONS: u64 = 10_000;

  while let Some(ctx) = queue.pop_front() {
    iterations += 1;
    if iterations > MAX_QUEUE_ITERATIONS {
      return Err(MacroError::DepthLimitExceeded);
    }
    let decl = ctx.value().clone();
    match decl {
      Decl::MacroCall { name, args } => {
        let expanded = expand_macro_call(&name, &args, &decl_gen_defs, &expand_ctx)?;
        for d in &expanded {
          if let Decl::DeclGen(gd) = d {
            decl_gen_defs.insert(gd.name.clone(), gd.clone());
          }
        }
        for d in expanded.into_iter().rev() {
          queue.push_front(SourceContext::no_ctx(d));
        }
      }
      Decl::Generated(inner) => {
        for d in inner.into_iter().rev() {
          queue.push_front(SourceContext::no_ctx(d));
        }
      }
      Decl::DefMacro(def) => {
        check_macro_declaration(&def.name, &def.attributes, MacroReturns::Expr)?;
        batch.push(ctx);
      }
      Decl::DeclGen(gd) => {
        check_macro_declaration(&gd.name, &gd.attributes, MacroReturns::Decls)?;
        batch.push(ctx);
      }
      Decl::Def(mut def) => {
        def.term = expand_term(def.term, &expand_ctx, 0)?;
        batch.push(ctx.map(|_| Decl::Def(def)));
      }
      Decl::Type(induct) => {
        let mut generated: Vec<Decl> = Vec::new();
        // `#[derive BEq BOrd Debug Lens]` (and any mote-registered
        // target, via `#[derive_handler ...]` on the implementing
        // `defmacro`) — generic dispatch to the corresponding
        // `derive_*!` decl-gen macro (`std/derive.mo` and friends) via
        // the ordinary `expand_macro_call` path, exactly as if the user
        // had written `derive_beq! Point` themselves. No code generation
        // happens here; this is purely a name lookup + macro-call
        // synthesis, same spirit as `#[derive(...)]` dispatching to
        // whichever expander (builtin or third-party) is registered under
        // each trait name in Rust. Requires the file to bring the
        // registering macro into scope (e.g. `use std.derive
        // {derive_beq, ...}` or a superset) — same as any other
        // cross-module decl-gen macro call; there is no implicit/auto
        // loading of `std.derive`. An unknown target errors with the
        // registered target names; a KNOWN target whose macro isn't in
        // `decl_gen_defs` fails there, same as a hand-written call.
        for target in derive_attribute_targets(&induct)? {
          let handler = handler_registry.get(&target).ok_or_else(|| {
            MacroError::Generic(format!(
              "unknown derive target `{target}` (registered targets: {})",
              if handler_registry.is_empty() {
                "none".to_string()
              } else {
                let mut names: Vec<&str> = handler_registry.keys().map(|k| k.as_str()).collect();
                names.sort();
                names.join(", ")
              }
            ))
          })?;
          let call_args = vec![mpvar(NamePath::from(induct.name().clone()))];
          let expanded =
            expand_macro_call(&handler.macro_name, &call_args, &decl_gen_defs, &expand_ctx)?;
          generated.extend(expanded);
        }
        // The type itself is pushed straight to `batch`, same as always —
        // NOT re-queued through this same arm again, or its still-present
        // `derive`/`derive_cli` attributes would trigger this whole block
        // a second time, regenerating (and re-queueing) the same instances
        // forever.
        batch.push(ctx.map(|_| Decl::Type(induct)));
        // The GENERATED decls, in contrast, DO need to be re-queued rather
        // than pushed straight to `batch` — `expand_macro_call`'s own
        // result can itself still contain further macro calls to expand
        // (the same reason `Decl::MacroCall`'s own expansion result gets
        // re-queued rather than appended directly), though in practice
        // every current derive (`derive_cli`/`derive_beq`/`derive_bord`/
        // `derive_debug`/`derive_lens`) bottoms out in concrete decls
        // straight away, via `reflect_type_info!`.
        for d in generated.into_iter().rev() {
          queue.push_front(SourceContext::no_ctx(d));
        }
      }
      Decl::ScopedOpen {
        path,
        filter,
        attributes,
        decl,
      } => {
        // Only the wrapped `Def`'s term can contain inline macro calls
        // (`open Module in type|struct|class|instance ...` never do) — but
        // still expand it here, or a `name!` call inside a scoped-open'd
        // def's body would silently never get expanded (it can't reach the
        // `Decl::Def` arm above, since it's nested inside `ScopedOpen`).
        let inner = match *decl {
          Decl::Def(mut def) => {
            def.term = expand_term(def.term, &expand_ctx, 0)?;
            Decl::Def(def)
          }
          other => other,
        };
        batch.push(ctx.map(|_| Decl::ScopedOpen {
          path,
          filter,
          attributes,
          decl: Box::new(inner),
        }));
      }
      // An instance's method bodies (`instance Debug T { def debug ... :=
      // reflect_debug! T self }`) can contain term-level macro calls —
      // both the reflection intrinsics and ordinary user macros — same as
      // any other def body, but `Decl::Ins` otherwise falls through the
      // catch-all below unexpanded (there's no `Decl::Def` wrapping to
      // reach on its own). This was already a latent gap for ordinary
      // macros before the derive-macros work (nothing previously put a
      // macro call inside an instance body); `derive_debug!`-generated
      // instances are the first thing to actually exercise it.
      Decl::Ins(mut ins) => {
        for def in ins.impls_map.values_mut() {
          def.term = expand_term(def.term.clone(), &expand_ctx, 0)?;
        }
        batch.push(ctx.map(|_| Decl::Ins(ins)));
      }
      other => {
        batch.push(ctx.map(|_| other));
      }
    }
  }

  Ok(flatten_generated_ctx(batch))
}

/// Flatten `Decl::Generated` wrappers in a list of decls.
fn flatten_generated(decls: Vec<SourceContext<Decl>>) -> Vec<SourceContext<Decl>> {
  let mut result = Vec::new();
  for ctx in decls {
    match ctx.value() {
      Decl::Generated(inner) => {
        for d in inner.clone() {
          result.push(SourceContext::no_ctx(d));
        }
      }
      _ => result.push(ctx),
    }
  }
  result
}

/// Flatten `Decl::Generated` wrappers in a list of context-wrapped decls.
fn flatten_generated_ctx(decls: Vec<SourceContext<Decl>>) -> Vec<SourceContext<Decl>> {
  flatten_generated(decls)
}

/// Expand a top-level macro call into declarations.
fn expand_macro_call(
  name: &Identifier,
  args: &[Term],
  decl_gen_defs: &Map<NamePath, DeclGenDef>,
  ctx: &ExpandCtx,
) -> Result<Vec<Decl>, MacroError> {
  if is_builtin_intrinsic(name.as_str()) {
    return expand_builtin_decl_intrinsic(name, args, ctx);
  }
  let path = NamePath::single(name.clone());
  let gen_def = decl_gen_defs
    .get(&path)
    .ok_or_else(|| MacroError::MacroNotFound {
      name: name.to_string(),
    })?;
  require_decl_position(name, &gen_def.attributes)?;

  if args.len() != gen_def.params.len() {
    return Err(MacroError::Generic(format!(
      "macro `{}` expects {} arguments, got {}",
      name,
      gen_def.params.len(),
      args.len()
    )));
  }

  // Substitute each parameter in each template declaration
  let mut expanded = gen_def.decls.clone();
  for (param, arg) in gen_def.params.iter().zip(args.iter()) {
    let param_name = &param.name;
    for decl in expanded.iter_mut() {
      *decl = subst_decl_var(decl.clone(), param_name, arg);
    }
  }

  Ok(expanded)
}

/// Substitute a variable in a declaration template (for decl-level macro expansion).
fn subst_decl_var(decl: Decl, name: &Identifier, replacement: &Term) -> Decl {
  match decl {
    Decl::Def(mut def) => {
      def.term = subst_macro(def.term, &NameRef::Id(name.clone()), replacement);
      def.typ = subst_macro(def.typ, &NameRef::Id(name.clone()), replacement);
      def.name = subst_path_component(def.name, name, replacement);
      Decl::Def(def)
    }
    Decl::DefMacro(mut def) => {
      def.term = subst_macro(def.term, &NameRef::Id(name.clone()), replacement);
      def.typ = subst_macro(def.typ, &NameRef::Id(name.clone()), replacement);
      def.name = subst_path_component(def.name, name, replacement);
      Decl::DefMacro(def)
    }
    // A decl-gen template's body can itself contain a nested macro call
    // (e.g. `derive_lens (T) := decls { reflect_type_info! T derive_lens_meta }`)
    // — substitute the outer macro's params into that call's own args too, or
    // they'd reach `expand_macro_call` still holding the literal param
    // name (`T`) instead of the caller's actual argument.
    Decl::MacroCall {
      name: call_name,
      args,
    } => Decl::MacroCall {
      name: call_name,
      args: args
        .into_iter()
        .map(|a| subst_macro(a, &NameRef::Id(name.clone()), replacement))
        .collect(),
    },
    // `instance Debug T { def debug (self : T) : String := ... }` — an
    // Instance's own `name`/`typ`/constructor are all DERIVED (by the
    // `instance(...)` builder) from `class_name`/`args`/`impls`, not
    // stored as independently-substitutable fields, so rebuild it from
    // substituted args + impls via the same builder the parser itself
    // uses — rather than trying to poke at private fields (`name`, `typ`,
    // `cons`) that only `term.rs` itself can see. Passing `name: None`
    // (auto-generate) is deliberate: it recomputes the instance's
    // auto-generated name from the SUBSTITUTED args (e.g.
    // `instance-Debug-Point`), not the template's original unsubstituted
    // `instance-Debug-T` — otherwise every derived instance of the same
    // class would collide on one stale, param-named identity.
    Decl::Ins(ins) => {
      let nr = NameRef::Id(name.clone());
      let args = ins
        .args
        .iter()
        .map(|a| subst_macro(a.clone(), &nr, replacement))
        .collect();
      let impls = ins
        .impls_map
        .values()
        .map(|d| {
          let mut d = d.clone();
          d.term = subst_macro(d.term.clone(), &nr, replacement);
          d.typ = subst_macro(d.typ.clone(), &nr, replacement);
          d
        })
        .collect();
      let mut new_ins = instance(
        None,
        ins.class_name.clone(),
        ins.constraints.clone(),
        ins.params.clone(),
        args,
        impls,
        ins.attributes.clone(),
      );
      new_ins.vis = ins.vis;
      Decl::Ins(new_ins)
    }
    other => other,
  }
}

/// Splice a macro parameter into a generated decl's own qualified NAME
/// (`ModulePath`) — e.g. `defmacro lens_field T field_name field_typ :=
/// decls { def T.field_name : ... := ... }`, called with `T` = `Point`,
/// `field_name` = `x`, needs to produce `def Point.x : ... := ...`.
///
/// A decl's name is parsed as a literal `ModulePath` (a fixed sequence of
/// `Identifier`s), not a `Term` — so it's never reached by ordinary
/// `subst_macro`, which only walks `Term`s. This only fires when
/// `replacement` is itself a simple name reference (a bare `Var`) — the
/// only shape that can sensibly become a path segment in another
/// declaration's name; anything else (an arbitrary computed value) leaves
/// the path untouched.
fn subst_path_component(path: NamePath, name: &Identifier, replacement: &Term) -> NamePath {
  let replacement_path = match strip_ctx(replacement.clone()) {
    Var {
      name: NameRef::Id(id),
    } => Some(NamePath::single(id)),
    Var {
      name: NameRef::Np(p),
    } => Some(p),
    _ => None,
  };
  let Some(replacement_path) = replacement_path else {
    return path;
  };
  let segments: Vec<Identifier> = path
    .to_vec()
    .into_iter()
    .flat_map(|seg| {
      if &seg == name {
        replacement_path.clone().to_vec()
      } else {
        vec![seg]
      }
    })
    .collect();
  NamePath::new(segments)
}

/// Walk a term and expand macro calls.
fn expand_term(term: Term, ctx: &ExpandCtx, depth: u64) -> Result<Term, MacroError> {
  if depth > MAX_EXPANSION_DEPTH {
    return Err(MacroError::DepthLimitExceeded);
  }
  match term {
    App { fun, arg } => {
      // Strip Ctx wrappers from fun for macro detection (Ctx carries source locations)
      let fun_inner = strip_ctx(*fun.clone());
      // Check for name! macro call
      if let Var {
        name: NameRef::Macro(name),
      } = &fun_inner
      {
        if is_builtin_intrinsic(name.as_str()) {
          let arg = expand_term(*arg, ctx, depth)?;
          return expand_builtin_term_intrinsic(name, &[arg], ctx);
        }
        let path = NamePath::single(name.clone());
        if let Some(def) = ctx.macro_defs.get(&path) {
          require_position(def, MacroReturns::Expr)?;
          let arg = expand_term(*arg, ctx, depth)?;
          return apply_macro(def, vec![arg], ctx, depth);
        }
      }
      // Check for chained name! a b macro call
      if let App { .. } = &fun_inner {
        if let Some((name, mut args)) = collect_macro_args(fun_inner, *arg.clone()) {
          if is_builtin_intrinsic(name.as_str()) {
            for a in args.iter_mut() {
              let old = std::mem::replace(a, Term::Hole);
              *a = expand_term(old, ctx, depth)?;
            }
            return expand_builtin_term_intrinsic(&name, &args, ctx);
          }
          let path = NamePath::single(name.clone());
          if let Some(def) = ctx.macro_defs.get(&path) {
            require_position(def, MacroReturns::Expr)?;
            for a in args.iter_mut() {
              let old = std::mem::replace(a, Term::Hole);
              *a = expand_term(old, ctx, depth)?;
            }
            return apply_macro(def, args, ctx, depth);
          }
        }
      }
      // Not a macro call (or macro not found) — recurse normally
      Ok(App {
        fun: Box::new(expand_term(*fun, ctx, depth)?),
        arg: Box::new(expand_term(*arg, ctx, depth)?),
      })
    }
    Lam { param, body } => Ok(Lam {
      param,
      body: Box::new(expand_term(*body, ctx, depth)?),
    }),
    Quote { term } => Ok(Quote {
      term: Box::new(resolve_quote(*term, ctx, depth)?),
    }),
    Ctx { loc, term, module } => Ok(Ctx {
      loc,
      term: Box::new(expand_term(*term, ctx, depth)?),
      module,
    }),
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Ok(Pi {
      arg_name,
      arg: Box::new(expand_term(*arg, ctx, depth)?),
      ret: Box::new(expand_term(*ret, ctx, depth)?),
      mult,
    }),
    Forall { name, typ, body } => Ok(Forall {
      name,
      typ: Box::new(expand_term(*typ, ctx, depth)?),
      body: Box::new(expand_term(*body, ctx, depth)?),
    }),
    Ann { term, typ } => Ok(Ann {
      term: Box::new(expand_term(*term, ctx, depth)?),
      typ: Box::new(expand_term(*typ, ctx, depth)?),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = expand_term(*value, ctx, depth)?;
      let cases = cases
        .into_iter()
        .map(|c| {
          let value = expand_term(*c.value, ctx, depth)?;
          Ok(case_with_optional_field_pattern(
            c.name,
            c.args,
            c.field_pattern,
            value,
          ))
        })
        .collect::<Result<Vec<_>, MacroError>>()?;
      Ok(match_term(value, cases))
    }
    Lit {
      value: Literal::If { value, then, els },
    } => {
      let value = expand_term(*value, ctx, depth)?;
      let then = expand_term(*then, ctx, depth)?;
      let els = expand_term(*els, ctx, depth)?;
      Ok(Term::Lit {
        value: Literal::If {
          value: Box::new(value),
          then: Box::new(then),
          els: Box::new(els),
        },
      })
    }
    Con(Constructor {
      typ_name,
      args,
      name,
      num_args,
    }) => {
      let args: Vec<Option<Term>> = args
        .into_iter()
        .map(|a| a.map(|t| expand_term(t, ctx, depth)).transpose())
        .collect::<Result<Vec<_>, MacroError>>()?;
      Ok(Con(Constructor {
        name,
        typ_name,
        args,
        num_args,
      }))
    }
    other => Ok(other),
  }
}

/// Resolve unquote calls inside a Quote body and expand any macro calls.
fn resolve_quote(term: Term, ctx: &ExpandCtx, depth: u64) -> Result<Term, MacroError> {
  if depth > MAX_EXPANSION_DEPTH {
    return Err(MacroError::DepthLimitExceeded);
  }
  match term {
    App { fun, arg } => {
      // Strip Ctx wrappers from fun for macro/unquote detection
      let fun_inner = strip_ctx(*fun.clone());
      // Check for unquote
      if let Var {
        name: NameRef::Id(n),
      } = &fun_inner
        && n.as_str() == "unquote"
      {
        // unquote(arg): splice arg into the output, then expand it
        let arg = resolve_quote(*arg, ctx, depth)?;
        // The spliced result may contain macro calls
        expand_term(arg, ctx, depth)
      } else {
        // Check for name! macro call
        if let Var {
          name: NameRef::Macro(name),
        } = &fun_inner
        {
          if is_builtin_intrinsic(name.as_str()) {
            let arg = resolve_quote(*arg, ctx, depth)?;
            return expand_builtin_term_intrinsic(name, &[arg], ctx);
          }
          let path = NamePath::single(name.clone());
          if let Some(def) = ctx.macro_defs.get(&path) {
            require_position(def, MacroReturns::Expr)?;
            let arg = resolve_quote(*arg, ctx, depth)?;
            return apply_macro(def, vec![arg], ctx, depth + 1);
          }
        }
        // Check for chained name! a b macro call
        if let App { .. } = &fun_inner {
          if let Some((name, mut args)) = collect_macro_args(fun_inner, *arg.clone()) {
            if is_builtin_intrinsic(name.as_str()) {
              for a in args.iter_mut() {
                let old = std::mem::replace(a, Term::Hole);
                *a = resolve_quote(old, ctx, depth)?;
              }
              return expand_builtin_term_intrinsic(&name, &args, ctx);
            }
            let path = NamePath::single(name.clone());
            if let Some(def) = ctx.macro_defs.get(&path) {
              require_position(def, MacroReturns::Expr)?;
              for a in args.iter_mut() {
                let old = std::mem::replace(a, Term::Hole);
                *a = resolve_quote(old, ctx, depth)?;
              }
              return apply_macro(def, args, ctx, depth + 1);
            }
          }
        }
        // Not a macro call — recurse
        Ok(App {
          fun: Box::new(resolve_quote(*fun, ctx, depth)?),
          arg: Box::new(resolve_quote(*arg, ctx, depth)?),
        })
      }
    }
    Lam { param, body } => Ok(Lam {
      param,
      body: Box::new(resolve_quote(*body, ctx, depth)?),
    }),
    Quote { term } => {
      // Nested quote — don't resolve unquotes (they belong to the inner quote)
      Ok(Quote {
        term: Box::new(resolve_quote(*term, ctx, depth)?),
      })
    }
    Ctx { loc, term, module } => Ok(Ctx {
      loc,
      term: Box::new(resolve_quote(*term, ctx, depth)?),
      module,
    }),
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Ok(Pi {
      arg_name,
      arg: Box::new(resolve_quote(*arg, ctx, depth)?),
      ret: Box::new(resolve_quote(*ret, ctx, depth)?),
      mult,
    }),
    Forall { name, typ, body } => Ok(Forall {
      name,
      typ: Box::new(resolve_quote(*typ, ctx, depth)?),
      body: Box::new(resolve_quote(*body, ctx, depth)?),
    }),
    Ann { term, typ } => Ok(Ann {
      term: Box::new(resolve_quote(*term, ctx, depth)?),
      typ: Box::new(resolve_quote(*typ, ctx, depth)?),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = resolve_quote(*value, ctx, depth)?;
      let cases = cases
        .into_iter()
        .map(|c| {
          let value = resolve_quote(*c.value, ctx, depth)?;
          Ok(case_with_optional_field_pattern(
            c.name,
            c.args,
            c.field_pattern,
            value,
          ))
        })
        .collect::<Result<Vec<_>, MacroError>>()?;
      Ok(match_term(value, cases))
    }
    Lit {
      value: Literal::If { value, then, els },
    } => {
      let value = resolve_quote(*value, ctx, depth)?;
      let then = resolve_quote(*then, ctx, depth)?;
      let els = resolve_quote(*els, ctx, depth)?;
      Ok(Term::Lit {
        value: Literal::If {
          value: Box::new(value),
          then: Box::new(then),
          els: Box::new(els),
        },
      })
    }
    Con(Constructor {
      typ_name,
      args,
      name,
      num_args,
    }) => {
      let args: Vec<Option<Term>> = args
        .into_iter()
        .map(|a| a.map(|t| resolve_quote(t, ctx, depth)).transpose())
        .collect::<Result<Vec<_>, MacroError>>()?;
      Ok(Con(Constructor {
        name,
        typ_name,
        args,
        num_args,
      }))
    }
    other => Ok(other),
  }
}

/// Collect arguments from a chained App, checking if it's a macro call.
/// Returns None if not a macro call.
/// Returns Some((name, args)) if it is, with args in left-to-right order.
fn collect_macro_args(fun: Term, arg: Term) -> Option<(Identifier, Vec<Term>)> {
  let fun = strip_ctx(fun);
  match fun {
    Var {
      name: NameRef::Macro(name),
    } => Some((name, vec![arg])),
    App {
      fun: inner_fun,
      arg: inner_arg,
    } => {
      let (name, mut args) = collect_macro_args(*inner_fun, *inner_arg)?;
      args.push(arg);
      Some((name, args))
    }
    _ => None,
  }
}

/// Apply macro to args, producing the expanded term.
fn apply_macro(
  def: &Def,
  args: Vec<Term>,
  ctx: &ExpandCtx,
  depth: u64,
) -> Result<Term, MacroError> {
  if depth > MAX_EXPANSION_DEPTH {
    return Err(MacroError::DepthLimitExceeded);
  }

  // Peel off one Lam per arg and substitute
  let mut body = def.term.clone();
  for arg in args {
    body = match body {
      Lam { param, body: b } => match param {
        Par::P(p) => subst_macro(*b, &NameRef::Id(p.name.clone()), &arg),
        Par::I { .. } => {
          return Err(MacroError::Generic("macro with implicit parameter".into()));
        }
      },
      _ => {
        return Err(MacroError::Generic("too many arguments for macro".into()));
      }
    };
  }

  // Strip Ctx wrappers and find the Quote body
  let body = strip_ctx(body);
  match body {
    Quote { term } => {
      // Hygiene: rename macro-introduced binders with gensym names
      let term = alpha_rename_body(*term);
      let expanded = resolve_quote(term, ctx, depth)?;
      expand_term(expanded, ctx, depth + 1)
    }
    _ => Err(MacroError::NonTermReturn {
      name: def.name.to_string(),
    }),
  }
}

/// Rename a variable reference in a term (like substitute but replaces with
/// a Var of the new name instead of an arbitrary term).
fn rename_macro_var(term: Term, old: &Identifier, new: &Identifier) -> Term {
  match term {
    Var {
      name: NameRef::Id(n),
    } if &n == old => Var {
      name: NameRef::Id(new.clone()),
    },
    Lam { param: p, body: b } => {
      let should_skip = match &p {
        Par::P(p_name) => &p_name.name == old,
        _ => false,
      };
      if should_skip {
        Lam { param: p, body: b }
      } else {
        Lam {
          param: p,
          body: Box::new(rename_macro_var(*b, old, new)),
        }
      }
    }
    App { fun, arg } => {
      // Don't rename inside unquote — those are user-supplied terms
      if let Var {
        name: NameRef::Id(n),
      } = &*fun
        && n.as_str() == "unquote"
      {
        App { fun, arg }
      } else {
        App {
          fun: Box::new(rename_macro_var(*fun, old, new)),
          arg: Box::new(rename_macro_var(*arg, old, new)),
        }
      }
    }
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Pi {
      arg_name,
      arg: Box::new(rename_macro_var(*arg, old, new)),
      ret: Box::new(rename_macro_var(*ret, old, new)),
      mult,
    },
    Forall {
      name: n,
      typ,
      body: b,
    } => {
      if &n == old {
        Forall {
          name: n,
          typ,
          body: b,
        }
      } else {
        Forall {
          name: n,
          typ: Box::new(rename_macro_var(*typ, old, new)),
          body: Box::new(rename_macro_var(*b, old, new)),
        }
      }
    }
    Quote { term: t } => Quote {
      term: Box::new(rename_macro_var(*t, old, new)),
    },
    Ctx {
      loc,
      term: t,
      module,
    } => Ctx {
      loc,
      term: Box::new(rename_macro_var(*t, old, new)),
      module,
    },
    Ann { term: t, typ } => Ann {
      term: Box::new(rename_macro_var(*t, old, new)),
      typ: Box::new(rename_macro_var(*typ, old, new)),
    },
    Con(Constructor {
      typ_name,
      args,
      name: n,
      num_args,
    }) => Con(Constructor {
      name: n,
      typ_name,
      num_args,
      args: args
        .into_iter()
        .map(|a| a.map(|t| rename_macro_var(t, old, new)))
        .collect(),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = rename_macro_var(*value, old, new);
      let cases = cases
        .into_iter()
        .map(|c| {
          case_with_optional_field_pattern(
            c.name,
            c.args,
            c.field_pattern,
            rename_macro_var(*c.value, old, new),
          )
        })
        .collect();
      match_term(value, cases)
    }
    Lit {
      value: Literal::If { value, then, els },
    } => Term::Lit {
      value: Literal::If {
        value: Box::new(rename_macro_var(*value, old, new)),
        then: Box::new(rename_macro_var(*then, old, new)),
        els: Box::new(rename_macro_var(*els, old, new)),
      },
    },
    other => other,
  }
}

/// Rename all local binders (Lam, Forall params) in a term with gensym names.
/// This prevents macro-introduced bindings from capturing user variables.
fn alpha_rename_body(term: Term) -> Term {
  match term {
    Lam { param: p, body: b } => {
      let (new_param, new_body) = match p {
        Par::P(param) => {
          let new_name = Identifier::gensym(param.name.as_str());
          let body = rename_macro_var(*b, &param.name, &new_name);
          (
            Par::P(Param {
              name: new_name,
              typ: Box::new(alpha_rename_body(*param.typ)),
              mult: param.mult,
              default: param.default.clone(),
              attrs: param.attrs.clone(),
            }),
            alpha_rename_body(body),
          )
        }
        Par::I { typ, mult } => (
          Par::I {
            typ: Box::new(alpha_rename_body(*typ)),
            mult,
          },
          alpha_rename_body(*b),
        ),
      };
      Lam {
        param: new_param,
        body: Box::new(new_body),
      }
    }
    App { fun, arg } => {
      // Don't rename inside unquote — those are user-supplied terms
      if let Var {
        name: NameRef::Id(n),
      } = &*fun
        && n.as_str() == "unquote"
      {
        App { fun, arg }
      } else {
        App {
          fun: Box::new(alpha_rename_body(*fun)),
          arg: Box::new(alpha_rename_body(*arg)),
        }
      }
    }
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Pi {
      arg_name,
      arg: Box::new(alpha_rename_body(*arg)),
      ret: Box::new(alpha_rename_body(*ret)),
      mult,
    },
    Forall {
      name: n,
      typ,
      body: b,
    } => {
      let new_name = Identifier::gensym(n.as_str());
      let body = alpha_rename_body(rename_macro_var(*b, &n, &new_name));
      Forall {
        name: new_name,
        typ: Box::new(alpha_rename_body(*typ)),
        body: Box::new(body),
      }
    }
    Quote { term: t } => Quote {
      term: Box::new(alpha_rename_body(*t)),
    },
    Ctx {
      loc,
      term: t,
      module,
    } => Ctx {
      loc,
      term: Box::new(alpha_rename_body(*t)),
      module,
    },
    Ann { term: t, typ } => Ann {
      term: Box::new(alpha_rename_body(*t)),
      typ: Box::new(alpha_rename_body(*typ)),
    },
    Con(Constructor {
      typ_name,
      args,
      name: n,
      num_args,
    }) => Con(Constructor {
      name: n,
      typ_name,
      num_args,
      args: args
        .into_iter()
        .map(|a| a.map(|t| alpha_rename_body(t)))
        .collect(),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = alpha_rename_body(*value);
      let cases = cases
        .into_iter()
        .map(|c| {
          case_with_optional_field_pattern(
            c.name,
            c.args,
            c.field_pattern,
            alpha_rename_body(*c.value),
          )
        })
        .collect();
      match_term(value, cases)
    }
    Lit {
      value: Literal::If { value, then, els },
    } => Term::Lit {
      value: Literal::If {
        value: Box::new(alpha_rename_body(*value)),
        then: Box::new(alpha_rename_body(*then)),
        els: Box::new(alpha_rename_body(*els)),
      },
    },
    other => other,
  }
}

/// Substitute variable references in a term WITHOUT capture-avoiding rename
/// of lambda binders. This is used for macro parameter substitution where
/// the outer lambda wrapping the macro body is being consumed, not protected.
/// Substitute into a lambda/pi parameter's own type ANNOTATION (e.g. `fn
/// (v : field_typ) => ...`'s `field_typ`) — independent of whether the
/// param's NAME shadows the substitution target for the body, since a
/// param's type and a param's name occupy different scopes (the type
/// annotation is evaluated in the OUTER scope, before the param itself is
/// bound).
fn subst_par_typ(p: Par, name: &NameRef, replacement: &Term) -> Par {
  match p {
    Par::P(mut param) => {
      param.typ = Box::new(subst_macro(*param.typ, name, replacement));
      Par::P(param)
    }
    Par::I { typ, mult } => Par::I {
      typ: Box::new(subst_macro(*typ, name, replacement)),
      mult,
    },
  }
}

fn subst_macro(term: Term, name: &NameRef, replacement: &Term) -> Term {
  match term {
    Var { name: n } if &n == name => replacement.clone(),
    Lam { param: p, body: b } => {
      let p = subst_par_typ(p, name, replacement);
      let should_skip = match (&p, name) {
        (Par::P(p_name), NameRef::Id(n)) => &p_name.name == n,
        _ => false,
      };
      if should_skip {
        Lam { param: p, body: b }
      } else {
        Lam {
          param: p,
          body: Box::new(subst_macro(*b, name, replacement)),
        }
      }
    }
    App { fun, arg } => App {
      fun: Box::new(subst_macro(*fun, name, replacement)),
      arg: Box::new(subst_macro(*arg, name, replacement)),
    },
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Pi {
      arg_name,
      arg: Box::new(subst_macro(*arg, name, replacement)),
      ret: Box::new(subst_macro(*ret, name, replacement)),
      mult,
    },
    Forall {
      name: n,
      typ,
      body: b,
    } => {
      if let NameRef::Id(id) = name
        && &n == id
      {
        Forall {
          name: n,
          typ,
          body: b,
        }
      } else {
        Forall {
          name: n,
          typ: Box::new(subst_macro(*typ, name, replacement)),
          body: Box::new(subst_macro(*b, name, replacement)),
        }
      }
    }
    Quote { term: t } => Quote {
      term: Box::new(subst_macro(*t, name, replacement)),
    },
    Ctx {
      loc,
      term: t,
      module,
    } => Ctx {
      loc,
      term: Box::new(subst_macro(*t, name, replacement)),
      module,
    },
    Ann { term: t, typ } => Ann {
      term: Box::new(subst_macro(*t, name, replacement)),
      typ: Box::new(subst_macro(*typ, name, replacement)),
    },
    Con(Constructor {
      typ_name,
      args,
      name: n,
      num_args,
    }) => Con(Constructor {
      name: n,
      typ_name,
      num_args,
      args: args
        .into_iter()
        .map(|a| a.map(|t| subst_macro(t, name, replacement)))
        .collect(),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = subst_macro(*value, name, replacement);
      let cases = cases
        .into_iter()
        .map(|c| {
          case_with_optional_field_pattern(
            c.name,
            c.args,
            c.field_pattern,
            subst_macro(*c.value, name, replacement),
          )
        })
        .collect();
      match_term(value, cases)
    }
    Lit {
      value: Literal::If { value, then, els },
    } => Term::Lit {
      value: Literal::If {
        value: Box::new(subst_macro(*value, name, replacement)),
        then: Box::new(subst_macro(*then, name, replacement)),
        els: Box::new(subst_macro(*els, name, replacement)),
      },
    },
    other => other,
  }
}
