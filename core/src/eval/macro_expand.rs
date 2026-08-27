use crate::Map;
use crate::term::module::LoadedModules;
use crate::term::{
  AttrArg, Constructor, Decl, DeclGenDef, Def, Identifier, Inductive, Literal, ModulePath, NameRef,
  Named, Par, Param, SourceContext,
  Term::{self, Ann, App, Con, Ctx, Forall, Lam, Lit, Pi, Quote, Var},
  case_with_optional_field_pattern, id, instance, match_term, mpvar,
};

/// Names of the built-in macro-expansion reflection intrinsics — recognized
/// by the expander itself rather than looked up in `macro_defs`/
/// `decl_gen_defs`, since they need read access to already-parsed
/// `Inductive` definitions (field/constructor reflection), which ordinary
/// template-substitution macros never do.
///
/// `reflect_type_info!` (decl position; see `expand_reflect_type_info_decl`'s
/// own doc comment for the full design) is the sole remaining member — the
/// reflection-as-data metaprogramming kernel (see
/// `plans/review-and-reduce-the-greedy-nest.md`): a type's structure is
/// exposed as an ordinary Monad *value* (`TypeInfo`, `init/meta.mo`), and an
/// ordinary Monad function (`std/derive.mo`'s `derive_lens_meta`/
/// `derive_debug_meta`/`derive_beq_meta`/`derive_bord_meta`, or a user's own)
/// computes a `List Decl` value from it, via real evaluation — not template
/// substitution. This replaced an earlier five-intrinsic kernel
/// (`reflect_fields!`/`reflect_ctors!`/`reflect_ctor_fields!`/
/// `reflect_pairwise_ctors!`/`reflect_set_field!`) that instead composed
/// built-in per-constructor/per-field dispatch primitives in Rust; once all
/// four derives were ported off it, it was deleted outright rather than
/// kept alongside this one.
const BUILTIN_INTRINSICS: &[&str] = &["reflect_type_info"];

fn is_builtin_intrinsic(name: &str) -> bool {
  BUILTIN_INTRINSICS.contains(&name)
}

/// Collect `Inductive` definitions from loaded modules, keyed by `ModulePath`.
/// Mirrors `collect_loaded_macro_defs` below.
fn collect_loaded_inductives(loaded: &LoadedModules) -> Map<ModulePath, Inductive> {
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
  inductives: &'a Map<ModulePath, Inductive>,
) -> Option<&'a Inductive> {
  let name = match strip_ctx(term.clone()) {
    Var { name } => name.to_path(),
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
      name: NameRef::P(path),
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

/// Map a `#[derive ...]` target name to the `std/derive.mo` decl-gen macro
/// that implements it.
pub(crate) fn derive_macro_name(target: &str) -> Option<&'static str> {
  match target {
    "BEq" => Some("derive_beq"),
    "BOrd" => Some("derive_bord"),
    "Debug" => Some("derive_debug"),
    "Lens" => Some("derive_lens"),
    _ => None,
  }
}

/// Dispatch a built-in reflection intrinsic invoked at **decl** position
/// (i.e. `reflect_type_info! T meta_def_name` appearing where a
/// `decls { ... }` template expects a declaration — see `expand_macro_call`).
fn expand_builtin_decl_intrinsic(
  name: &Identifier,
  args: &[Term],
  inductives: &Map<ModulePath, Inductive>,
  loaded: &LoadedModules,
  current_decls: &[SourceContext<Decl>],
  current_path: &ModulePath,
) -> Result<Vec<Decl>, MacroError> {
  match name.as_str() {
    "reflect_type_info" => {
      expand_reflect_type_info_decl(args, inductives, loaded, current_decls, current_path)
    }
    other => Err(MacroError::Generic(format!(
      "intrinsic `{other}` is not valid at declaration position"
    ))),
  }
}

/// `reflect_type_info! T meta_def_name` — the reflection-as-data kernel
/// (see `plans/review-and-reduce-the-greedy-nest.md`): builds a `TypeInfo`
/// *value* (`meta_reflect::build_type_info_value`) from `T`'s already-
/// parsed `Inductive`, then invokes the named top-level `def`
/// (`meta_def_name` — an ordinary Monad function, e.g. `std/derive.mo`'s
/// `derive_lens : TypeInfo -> List Decl`, NOT a `defmacro` template) with
/// that value as its sole argument, via the real production evaluator
/// (`core_eval`, through `meta_compile::MetaEvalContext`, sandboxed to
/// `core_native::is_pure_native`'s allowlist — no IO/concurrency). The
/// result is reified (`meta_reflect::reify_decls_value_to_decls`) back
/// into real declarations to splice in.
///
/// Unlike every other intrinsic in this file, `meta_def_name` is invoked
/// through ordinary function CALL semantics (real evaluation, arbitrary
/// Monad computation — `List.map`/`match`/recursion), not macro-call
/// template substitution — it never needs to be registered in
/// `decl_gen_defs`/`macro_defs` at all.
fn expand_reflect_type_info_decl(
  args: &[Term],
  inductives: &Map<ModulePath, Inductive>,
  loaded: &LoadedModules,
  current_decls: &[SourceContext<Decl>],
  current_path: &ModulePath,
) -> Result<Vec<Decl>, MacroError> {
  let [type_arg, meta_def_name_arg] = args else {
    return Err(MacroError::Generic(format!(
      "reflect_type_info! expects 2 arguments (a type and a meta-function name), got {}",
      args.len()
    )));
  };
  let induct = resolve_inductive(type_arg, inductives).ok_or_else(|| {
    MacroError::Generic("reflect_type_info!: first argument must name a known type".into())
  })?;
  let meta_def_name = term_as_identifier(meta_def_name_arg).ok_or_else(|| {
    MacroError::Generic("reflect_type_info!: second argument must name a top-level def".into())
  })?;
  let type_info_value = super::meta_reflect::build_type_info_value(induct, inductives)?;
  // Rebuilt fresh on every call rather than cached across the enclosing
  // `expand_macros` run — simpler and correct, at the cost of re-checking
  // the whole loaded program once per `reflect_type_info!`/derive
  // invocation in a file that uses several; revisit if that proves to
  // matter in practice (thread a cache through `expand_macros`'s work
  // queue the same way `decl_gen_defs` already is).
  //
  // Forwarded to `MetaEvalContext::build`'s `current_decls`: `Decl::Use`/
  // `Decl::Open`/`Decl::Infix` (import/scope context — never references
  // anything not-yet-generated, safe to always include) and every
  // `Decl::Def` EXCEPT `#[test]`-attributed ones. `#[test]` defs are
  // specifically excluded because they're the natural CONSUMERS of a
  // derive's own output (e.g. a test calling the very lens
  // `derive_lens!` is about to generate) — re-checking one this early
  // (`build_core_program`'s capture pass type-checks every decl in the
  // batch) fails with a spurious "unbound variable" for something that
  // will exist by the time the OUTER expansion finishes, confirmed
  // directly, not hypothetical. Ordinary (non-`#[test]`) same-file
  // helper defs a same-file meta function calls are kept, so that case
  // works too — every REAL target (`std/derive.mo`'s own
  // `derive_lens_meta`/etc.) lives in an already-loaded module and
  // doesn't go through this path at all, only a user's own same-file
  // meta function does. `Decl::MacroCall`/`Decl::Generated` are dropped
  // regardless (the actual recursion trigger, see `meta_compile.rs`).
  let meta_def_decls: Vec<SourceContext<Decl>> = current_decls
    .iter()
    .filter(|ctx| match ctx.value() {
      Decl::Def(def) => !def.has_test_attr(),
      Decl::Use(_) | Decl::Open(_) | Decl::Infix(_) => true,
      _ => false,
    })
    .cloned()
    .collect();
  let mut ctx = super::meta_compile::MetaEvalContext::build(loaded, current_path, &meta_def_decls)?;
  let result_value = ctx.invoke(&ModulePath::single(meta_def_name), vec![type_info_value])?;
  super::meta_reflect::reify_decls_value_to_decls(result_value, inductives)
}

/// A built-in reflection intrinsic invoked at **term** position (appearing
/// inside an ordinary expression — see `expand_term`/`resolve_quote`).
/// `reflect_type_info!` (`BUILTIN_INTRINSICS`'s sole remaining member) is
/// decl-position only, so any term-position use is always invalid — kept as
/// a real, named dispatch point (rather than folded into the generic "macro
/// not found" fallback) so that gets a clear, specific error.
fn expand_builtin_term_intrinsic(name: &Identifier, _args: &[Term]) -> Result<Term, MacroError> {
  Err(MacroError::Generic(format!(
    "intrinsic `{name}` is not valid at term position"
  )))
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

/// Collect macro definitions from loaded modules, keyed by ModulePath.
fn collect_loaded_macro_defs(loaded: &LoadedModules) -> Map<ModulePath, Def> {
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
fn collect_loaded_decl_gen_defs(loaded: &LoadedModules) -> Map<ModulePath, DeclGenDef> {
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
  let mut macro_defs: Map<ModulePath, Def> = decls
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
  let mut decl_gen_defs: Map<ModulePath, DeclGenDef> = decls
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
  let mut inductives: Map<ModulePath, Inductive> = decls
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
  // own types (above) still take priority via `or_insert`.
  let closure_loaded = super::meta_compile::dep_closure_loaded(loaded, &current_decls)?;
  for (path, induct) in collect_loaded_inductives(&closure_loaded) {
    inductives.entry(path).or_insert(induct);
  }

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
        let expanded = expand_macro_call(
          &name,
          &args,
          &decl_gen_defs,
          &inductives,
          loaded,
          &current_decls,
          current_path,
        )?;
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
      Decl::DefMacro(_) | Decl::DeclGen(_) => {
        batch.push(ctx);
      }
      Decl::Def(mut def) => {
        def.term = expand_term(def.term, &macro_defs, &inductives, 0)?;
        batch.push(ctx.map(|_| Decl::Def(def)));
      }
      Decl::Type(induct) => {
        let mut generated: Vec<Decl> = Vec::new();
        // `#[derive_cli]` — dispatches to the `derive_cli` decl-gen macro
        // (`lang/cli.mo`), the same reflection-as-data mechanism every
        // other derive uses (via `derive_cli_meta`, an ordinary
        // `TypeInfo -> List Decl` function invoked through
        // `reflect_type_info!`), through ordinary macro-call synthesis —
        // same spirit as, and now literally the same code shape as, the
        // `#[derive BEq BOrd Debug Lens]` loop just below. Requires the
        // file to `use lang.cli {derive_cli}` (or a superset, e.g.
        // `use lang.cli {*}`), same convention as any other cross-module
        // decl-gen macro call.
        if induct.has_attr("derive_cli") {
          let call_args = vec![mpvar(induct.name().clone())];
          let expanded = expand_macro_call(
            &id("derive_cli"),
            &call_args,
            &decl_gen_defs,
            &inductives,
            loaded,
            &current_decls,
            current_path,
          )?;
          generated.extend(expanded);
        }
        // `#[derive BEq BOrd Debug Lens]` — generic dispatch to the
        // corresponding `derive_*!` decl-gen macro (`std/derive.mo`) via
        // the ordinary `expand_macro_call` path, exactly as if the user
        // had written `derive_beq! Point` themselves. No code generation
        // happens here; this is purely a name lookup + macro-call
        // synthesis, same spirit as `#[derive(...)]` dispatching to
        // whichever expander (builtin or third-party) is registered under
        // each trait name in Rust. Requires the file to `use std.derive
        // {derive_beq, ...}` (or a superset) — same as any other
        // cross-module decl-gen macro call; there is no implicit/auto
        // loading of `std.derive`.
        for target in derive_attribute_targets(&induct)? {
          let macro_name = derive_macro_name(&target).ok_or_else(|| {
            MacroError::Generic(format!(
              "unknown derive target `{target}` (expected one of: BEq, BOrd, Debug, Lens)"
            ))
          })?;
          let call_args = vec![mpvar(induct.name().clone())];
          let expanded = expand_macro_call(
            &id(macro_name),
            &call_args,
            &decl_gen_defs,
            &inductives,
            loaded,
            &current_decls,
            current_path,
          )?;
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
        module_path,
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
            def.term = expand_term(def.term, &macro_defs, &inductives, 0)?;
            Decl::Def(def)
          }
          other => other,
        };
        batch.push(ctx.map(|_| Decl::ScopedOpen {
          module_path,
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
          def.term = expand_term(def.term.clone(), &macro_defs, &inductives, 0)?;
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
  decl_gen_defs: &Map<ModulePath, DeclGenDef>,
  inductives: &Map<ModulePath, Inductive>,
  loaded: &LoadedModules,
  current_decls: &[SourceContext<Decl>],
  current_path: &ModulePath,
) -> Result<Vec<Decl>, MacroError> {
  if is_builtin_intrinsic(name.as_str()) {
    return expand_builtin_decl_intrinsic(
      name,
      args,
      inductives,
      loaded,
      current_decls,
      current_path,
    );
  }
  let path = ModulePath::single(name.clone());
  let gen_def = decl_gen_defs
    .get(&path)
    .ok_or_else(|| MacroError::MacroNotFound {
      name: name.to_string(),
    })?;

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
fn subst_path_component(path: ModulePath, name: &Identifier, replacement: &Term) -> ModulePath {
  let replacement_path = match strip_ctx(replacement.clone()) {
    Var {
      name: NameRef::Id(id),
    } => Some(ModulePath::single(id)),
    Var {
      name: NameRef::P(p),
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
  ModulePath::new(segments)
}

/// Walk a term and expand macro calls.
fn expand_term(
  term: Term,
  macro_defs: &Map<ModulePath, Def>,
  inductives: &Map<ModulePath, Inductive>,
  depth: u64,
) -> Result<Term, MacroError> {
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
          let arg = expand_term(*arg, macro_defs, inductives, depth)?;
          return expand_builtin_term_intrinsic(name, &[arg]);
        }
        let path = ModulePath::single(name.clone());
        if let Some(def) = macro_defs.get(&path) {
          let arg = expand_term(*arg, macro_defs, inductives, depth)?;
          return apply_macro(def, vec![arg], macro_defs, inductives, depth);
        }
      }
      // Check for chained name! a b macro call
      if let App { .. } = &fun_inner {
        if let Some((name, mut args)) = collect_macro_args(fun_inner, *arg.clone()) {
          if is_builtin_intrinsic(name.as_str()) {
            for a in args.iter_mut() {
              let old = std::mem::replace(a, Term::Hole);
              *a = expand_term(old, macro_defs, inductives, depth)?;
            }
            return expand_builtin_term_intrinsic(&name, &args);
          }
          let path = ModulePath::single(name.clone());
          if let Some(def) = macro_defs.get(&path) {
            for a in args.iter_mut() {
              let old = std::mem::replace(a, Term::Hole);
              *a = expand_term(old, macro_defs, inductives, depth)?;
            }
            return apply_macro(def, args, macro_defs, inductives, depth);
          }
        }
      }
      // Not a macro call (or macro not found) — recurse normally
      Ok(App {
        fun: Box::new(expand_term(*fun, macro_defs, inductives, depth)?),
        arg: Box::new(expand_term(*arg, macro_defs, inductives, depth)?),
      })
    }
    Lam { param, body } => Ok(Lam {
      param,
      body: Box::new(expand_term(*body, macro_defs, inductives, depth)?),
    }),
    Quote { term } => Ok(Quote {
      term: Box::new(resolve_quote(*term, macro_defs, inductives, depth)?),
    }),
    Ctx { loc, term, module } => Ok(Ctx {
      loc,
      term: Box::new(expand_term(*term, macro_defs, inductives, depth)?),
      module,
    }),
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Ok(Pi {
      arg_name,
      arg: Box::new(expand_term(*arg, macro_defs, inductives, depth)?),
      ret: Box::new(expand_term(*ret, macro_defs, inductives, depth)?),
      mult,
    }),
    Forall { name, typ, body } => Ok(Forall {
      name,
      typ: Box::new(expand_term(*typ, macro_defs, inductives, depth)?),
      body: Box::new(expand_term(*body, macro_defs, inductives, depth)?),
    }),
    Ann { term, typ } => Ok(Ann {
      term: Box::new(expand_term(*term, macro_defs, inductives, depth)?),
      typ: Box::new(expand_term(*typ, macro_defs, inductives, depth)?),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = expand_term(*value, macro_defs, inductives, depth)?;
      let cases = cases
        .into_iter()
        .map(|c| {
          let value = expand_term(*c.value, macro_defs, inductives, depth)?;
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
      let value = expand_term(*value, macro_defs, inductives, depth)?;
      let then = expand_term(*then, macro_defs, inductives, depth)?;
      let els = expand_term(*els, macro_defs, inductives, depth)?;
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
        .map(|a| {
          a.map(|t| expand_term(t, macro_defs, inductives, depth))
            .transpose()
        })
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
fn resolve_quote(
  term: Term,
  macro_defs: &Map<ModulePath, Def>,
  inductives: &Map<ModulePath, Inductive>,
  depth: u64,
) -> Result<Term, MacroError> {
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
        let arg = resolve_quote(*arg, macro_defs, inductives, depth)?;
        // The spliced result may contain macro calls
        expand_term(arg, macro_defs, inductives, depth)
      } else {
        // Check for name! macro call
        if let Var {
          name: NameRef::Macro(name),
        } = &fun_inner
        {
          if is_builtin_intrinsic(name.as_str()) {
            let arg = resolve_quote(*arg, macro_defs, inductives, depth)?;
            return expand_builtin_term_intrinsic(name, &[arg]);
          }
          let path = ModulePath::single(name.clone());
          if let Some(def) = macro_defs.get(&path) {
            let arg = resolve_quote(*arg, macro_defs, inductives, depth)?;
            return apply_macro(def, vec![arg], macro_defs, inductives, depth + 1);
          }
        }
        // Check for chained name! a b macro call
        if let App { .. } = &fun_inner {
          if let Some((name, mut args)) = collect_macro_args(fun_inner, *arg.clone()) {
            if is_builtin_intrinsic(name.as_str()) {
              for a in args.iter_mut() {
                let old = std::mem::replace(a, Term::Hole);
                *a = resolve_quote(old, macro_defs, inductives, depth)?;
              }
              return expand_builtin_term_intrinsic(&name, &args);
            }
            let path = ModulePath::single(name.clone());
            if let Some(def) = macro_defs.get(&path) {
              for a in args.iter_mut() {
                let old = std::mem::replace(a, Term::Hole);
                *a = resolve_quote(old, macro_defs, inductives, depth)?;
              }
              return apply_macro(def, args, macro_defs, inductives, depth + 1);
            }
          }
        }
        // Not a macro call — recurse
        Ok(App {
          fun: Box::new(resolve_quote(*fun, macro_defs, inductives, depth)?),
          arg: Box::new(resolve_quote(*arg, macro_defs, inductives, depth)?),
        })
      }
    }
    Lam { param, body } => Ok(Lam {
      param,
      body: Box::new(resolve_quote(*body, macro_defs, inductives, depth)?),
    }),
    Quote { term } => {
      // Nested quote — don't resolve unquotes (they belong to the inner quote)
      Ok(Quote {
        term: Box::new(resolve_quote(*term, macro_defs, inductives, depth)?),
      })
    }
    Ctx { loc, term, module } => Ok(Ctx {
      loc,
      term: Box::new(resolve_quote(*term, macro_defs, inductives, depth)?),
      module,
    }),
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Ok(Pi {
      arg_name,
      arg: Box::new(resolve_quote(*arg, macro_defs, inductives, depth)?),
      ret: Box::new(resolve_quote(*ret, macro_defs, inductives, depth)?),
      mult,
    }),
    Forall { name, typ, body } => Ok(Forall {
      name,
      typ: Box::new(resolve_quote(*typ, macro_defs, inductives, depth)?),
      body: Box::new(resolve_quote(*body, macro_defs, inductives, depth)?),
    }),
    Ann { term, typ } => Ok(Ann {
      term: Box::new(resolve_quote(*term, macro_defs, inductives, depth)?),
      typ: Box::new(resolve_quote(*typ, macro_defs, inductives, depth)?),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = resolve_quote(*value, macro_defs, inductives, depth)?;
      let cases = cases
        .into_iter()
        .map(|c| {
          let value = resolve_quote(*c.value, macro_defs, inductives, depth)?;
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
      let value = resolve_quote(*value, macro_defs, inductives, depth)?;
      let then = resolve_quote(*then, macro_defs, inductives, depth)?;
      let els = resolve_quote(*els, macro_defs, inductives, depth)?;
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
        .map(|a| {
          a.map(|t| resolve_quote(t, macro_defs, inductives, depth))
            .transpose()
        })
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
  macro_defs: &Map<ModulePath, Def>,
  inductives: &Map<ModulePath, Inductive>,
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
      let expanded = resolve_quote(term, macro_defs, inductives, depth)?;
      expand_term(expanded, macro_defs, inductives, depth + 1)
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
