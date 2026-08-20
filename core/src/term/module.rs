#[cfg(test)]
pub mod test;

use super::*;
use crate::Set;
use crate::diag::{Diagnostic, Severity, Suggestion};
use crate::eval::r#type::{
  TypeError, UsageEnv, derive_instance_key, render_type_error_with_source,
};
use crate::parser::ModuleContext;
use crate::term::{
  Inductive, Instance, InstanceKey, ModulePath, SourceContext, Term, TypeConstraint,
};
use crate::{
  parser::parse_file_with_path,
  term::{
    Decl, Identifier,
    NameRef::{self},
  },
};
use std::collections::HashSet;
use std::fs::read_to_string;
use std::sync::Arc;
use std::time::Instant;
use std::{fmt::Display, hash::Hash};

fn default_source_range() -> &'static SourceRange {
  use std::sync::OnceLock;
  static DEFAULT: OnceLock<SourceRange> = OnceLock::new();
  DEFAULT.get_or_init(SourceRange::default)
}

#[derive(Debug, Clone, PartialEq)]
pub enum ScopeError {
  Type(Box<TypeError>),
  PathNotFound(ModulePath),
  IdNotFound(Identifier),
  OperatorNotDefined(Operator),
  InstanceNotFound(InstanceKey),
  AmbiguousName {
    name: ModulePath,
    candidates: Vec<ModulePath>,
  },
  Generic(String),
}

impl From<TypeError> for ScopeError {
  fn from(value: TypeError) -> Self {
    ScopeError::Type(Box::new(value))
  }
}

fn nref_error(nref: NameRef) -> ScopeError {
  use ScopeError::*;
  match nref {
    NameRef::P(module_path) => PathNotFound(module_path),
    Id(identifier) => IdNotFound(identifier),
    NameRef::Macro(identifier) => Generic(format!("macro {identifier} not found")),
    NameRef::Op(operator) => OperatorNotDefined(operator),
    NameRef::Index(i) => Generic(format!("index var {i} not resolved")),
  }
}

impl Display for ScopeError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use ScopeError::*;
    match self {
      PathNotFound(module_path) => {
        write!(f, "{} not found", module_path)
      }
      InstanceNotFound(instance_key) => {
        write!(f, "instance not found {}", instance_key)
      }
      AmbiguousName { name, candidates } => {
        let modules = candidates
          .iter()
          .map(|c| format!("{name} available as {c}"))
          .collect::<Vec<String>>()
          .join(", ");
        write!(f, "ambiguous name `{name}`, {}", modules)
      }
      Generic(s) => write!(f, "{s}"),
      OperatorNotDefined(s) => write!(f, "operator {s} not defined"),
      Type(type_error) => write!(f, "scope type: {type_error}"),
      IdNotFound(identifier) => write!(f, "id {identifier} not found"),
    }
  }
}

impl From<&ScopeError> for crate::diag::Diagnostic {
  fn from(err: &ScopeError) -> Self {
    use crate::diag::{Diagnostic, Severity};
    Diagnostic {
      severity: Severity::Error,
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

#[derive(Clone, Debug, PartialEq)]
pub enum LocalVar<'a> {
  Owned { name: &'a Identifier, typ: Term },
  Borrowed { name: &'a Identifier, typ: &'a Term },
  Index { typ: &'a Term },
  Forall { name: &'a Identifier, typ: &'a Term },
}

impl<'a> LocalVar<'a> {
  pub fn name(&self) -> Option<&Identifier> {
    use LocalVar::*;
    match self {
      Owned { name, .. } => Some(name),
      Borrowed { name, .. } => Some(name),
      Forall { name, .. } => Some(name),
      Index { .. } => None,
    }
  }
}

impl<'a> Typed for LocalVar<'a> {
  fn typ(&self) -> &Term {
    use LocalVar::*;
    match self {
      Owned { typ, .. } => typ,
      Borrowed { typ, .. } => typ,
      Forall { typ, .. } => typ,
      Index { typ } => typ,
    }
  }
}

impl<'a> AsVarRef for LocalVar<'a> {
  fn as_var_ref(&self) -> VarRef<'_> {
    VarRef::Local { typ: self.typ() }
  }
}

pub fn local_var<'a>(name: &'a Identifier, typ: &'a Term) -> LocalVar<'a> {
  LocalVar::Borrowed { name, typ }
}
pub fn local_forall<'a>(name: &'a Identifier, typ: &'a Term) -> LocalVar<'a> {
  LocalVar::Forall { name, typ }
}
pub fn local_index_var<'a>(typ: &'a Term) -> LocalVar<'a> {
  LocalVar::Index { typ }
}
pub fn local_var_owned<'a>(name: &'a Identifier, typ: Term) -> LocalVar<'a> {
  LocalVar::Owned { name, typ }
}

/// Owner struct of loaded modules
#[derive(Debug, Clone)]
pub struct LoadedModulesConfig {
  pub test_mode: bool,
  pub benchmark: bool,
}

impl Default for LoadedModulesConfig {
  fn default() -> Self {
    Self {
      test_mode: false,
      benchmark: false,
    }
  }
}

// `modules` is `Arc`-wrapped -- `LoadedModules` is deep-cloned once per
// checked/tested FILE (`core/src/lib.rs`'s `evaluate_one_test_file`/
// `check_files`, deliberately, to keep each file's capturing check
// isolated from every other file's -- see those call sites' own doc
// comments), and a plain `#[derive(Clone)]` over a `BTreeMap` of every
// loaded module's entire checked AST measured (via `valgrind
// --tool=callgrind`, AGENTS.md item 13) as 83-99% of an isolated
// profile window -- the single largest cost anywhere in this whole
// pipeline. `Module`'s own large fields are `Arc`-wrapped too (below),
// so this makes the outer map's clone itself close to free as well
// (bump one refcount) rather than merely cheaper (one B-tree-node touch
// per loaded module). The one live mutator (`add_module`) uses
// `Arc::make_mut` (copy-on-write); every read path is unaffected since
// `&Arc<Map<K,V>>` derefs to `&Map<K,V>` at every existing call site.
#[derive(Debug, Clone)]
pub struct LoadedModules {
  modules: Arc<Map<ModulePath, Module>>,
  builtins: Builtins,
  pub config: LoadedModulesConfig,
  search_paths: SearchPaths,
}

impl Display for LoadedModules {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    writeln!(f, "Loaded Modules:")?;
    for module in self.modules.values() {
      writeln!(f, "{}", module)?;
    }
    Ok(())
  }
}

impl LoadedModules {
  pub fn modules(&self) -> Vec<&Module> {
    self.modules.values().collect()
  }
  pub fn from(modules: Vec<Module>) -> Self {
    let modules = modules.into_iter().map(|m| (m.path().clone(), m)).collect();
    let builtins = Builtins::new();
    LoadedModules {
      modules: Arc::new(modules),
      builtins,
      config: Default::default(),
      search_paths: SearchPaths::empty(),
    }
  }
  pub fn test_mode(&self) -> bool {
    self.config.test_mode
  }
  pub fn set_test_mode(&mut self, test_mode: bool) {
    self.config.test_mode = test_mode;
  }
  pub fn search_paths(&self) -> &SearchPaths {
    &self.search_paths
  }
  pub fn set_search_paths(&mut self, paths: SearchPaths) {
    self.search_paths = paths;
  }
  pub fn get_module_mut(&mut self, path: &ModulePath) -> Option<&mut Module> {
    Arc::make_mut(&mut self.modules).get_mut(path)
  }
  pub fn get_module(&self, path: &ModulePath) -> Option<&Module> {
    self.modules.get(path)
  }

  pub fn extend(&mut self, ms: LoadedModules) {
    let other = Arc::unwrap_or_clone(ms.modules);
    Arc::make_mut(&mut self.modules).extend(other);
  }
  /// Use type_check_module to add modules
  pub fn add_module(&mut self, module: Module) {
    Arc::make_mut(&mut self.modules).insert(module.path().clone(), module);
  }
  pub fn global<'a>(&'a self, for_module: &'a ModulePath) -> Option<GlobalScope<'a>> {
    GlobalScope::for_module(for_module, self)
  }

  pub fn empty() -> LoadedModules {
    LoadedModules {
      modules: Arc::new(Map::new()),
      builtins: Builtins::new(),
      config: Default::default(),
      search_paths: SearchPaths::empty(),
    }
  }

  pub fn add_modules(&mut self, loaded_modules: Map<ModulePath, Module>) {
    Arc::make_mut(&mut self.modules).extend(loaded_modules);
  }

  pub fn builtins(&self) -> &Builtins {
    &self.builtins
  }

  pub(crate) fn scope_of_decls<'a>(
    &'a self,
    path: &'a ModulePath,
    decls: &'a Vec<SourceContext<Decl>>,
  ) -> GlobalScope<'a> {
    GlobalScope::from_decls(path, decls, self)
  }

  pub fn scopes(&self) -> LoadedScopes<'_> {
    LoadedScopes::new(self, self.config.test_mode)
  }
}
#[derive(Debug, Clone)]
pub struct Builtins {
  path: ModulePath,
  loc: SourceRange,
  sort_0: Term,
  sort_1: Term,
  pub(crate) type_map: Map<u64, Term>,
  pub(crate) prelude_path: ModulePath,
}
impl Default for Builtins {
  fn default() -> Self {
    Self::new()
  }
}

impl Builtins {
  pub fn new() -> Self {
    Builtins {
      path: mpt("'builtins"),
      loc: Default::default(),
      sort_0: sort0(),
      sort_1: sort1(),
      type_map: Map::new(),
      prelude_path: mpt("'prelude"),
    }
  }
  pub fn get_sort_u_term(&mut self, level: u64) -> &Term {
    if !self.type_map.contains_key(&level) {
      self.type_map.insert(level, sort_u(level));
    }
    self.type_map.get(&level).unwrap()
  }

  fn get_sort_0(&self) -> DefRef<'_> {
    DefRef {
      module: &self.path,
      name: mpt("Prop"),
      full_path: mpt("Prop"),
      term: &self.sort_0,
      typ: &self.sort_0,
      loc: &self.loc,
      vis: Visibility::Pub,
    }
  }

  fn get_sort_1(&self) -> DefRef<'_> {
    DefRef {
      module: &self.path,
      name: mpt("Type"),
      full_path: mpt("Type"),
      term: &self.sort_1,
      typ: &self.sort_1,
      loc: &self.loc,
      vis: Visibility::Pub,
    }
  }

  fn get_pred(&self) -> DefRef<'_> {
    DefRef {
      module: &self.path,
      name: mpt("Pred"),
      full_path: mpt("Pred"),
      term: &self.sort_0,
      typ: &self.sort_0,
      loc: &self.loc,
      vis: Visibility::Pub,
    }
  }
}

/// Owned scope data for a module, built from the module and its dependencies
#[derive(Debug, Clone)]
pub struct GlobalScopeData {
  pub module_path: ModulePath,
  def_refs: Map<ModulePath, (Term, Term, ModulePath)>,
  class_defs: Map<ModulePath, (Identifier, Term, ModulePath)>,
  instances: Map<ModulePath, Vec<Instance>>,
  inductives: Map<ModulePath, Inductive>,
  classes: Map<ModulePath, Inductive>,
  infixes: Map<Operator, Infix>,
  conflicts: Map<ModulePath, Vec<ModulePath>>,
}

impl GlobalScopeData {
  pub fn from_module(module: &Module, loaded: &LoadedModules, test_mode: bool) -> Self {
    let builtins = &loaded.builtins;

    // Collect opens from current module and prelude
    let mut opens: Vec<&Open> = module
      .get_opens()
      .iter()
      .map(|ctx| ctx.value())
      .filter(|o| test_mode || !o.has_cfg_test_attr())
      .collect();
    let prelude = loaded.get_module(&builtins.prelude_path);
    if let Some(prelude) = prelude {
      opens = opens
        .into_iter()
        .chain(prelude.get_opens().iter().map(|ctx| ctx.value()))
        .collect();
    }

    // Build visible modules set: current + used + implicit
    let mut visible_modules: Map<&ModulePath, &Module> = Map::new();
    visible_modules.insert(module.path(), module);

    // Include explicitly used modules
    for use_decl in module.get_uses() {
      if !test_mode && use_decl.has_cfg_test_attr() {
        continue;
      }
      if let Some(mo) = loaded.get_module(&use_decl.module_path) {
        visible_modules.insert(mo.path(), mo);
      }
    }

    // Include default implicit modules: prelude, init
    let default_names: Vec<ModulePath> =
      vec![builtins.prelude_path.clone(), ModulePath::top("init")];
    for default_name in &default_names {
      if let Some(mo) = loaded.get_module(default_name) {
        visible_modules.insert(mo.path(), mo);
      }
    }

    // Include re-exported modules from all visible modules
    {
      let re_exports: Vec<(ModulePath, ModulePath)> = visible_modules
        .values()
        .flat_map(|modu| {
          modu
            .get_pub_uses()
            .into_iter()
            .map(|use_| (modu.path().clone(), use_.module_path.clone()))
        })
        .collect();
      for (through_module, re_export_path) in re_exports {
        let _ = through_module; // TODO: prefix re-exported defs with through_module path
        if let Some(mo) = loaded.get_module(&re_export_path) {
          visible_modules.insert(mo.path(), mo);
        }
      }
    }

    // Flatten each `use` declaration's filter (including nested sub-module
    // imports, e.g. `use io {file {read}}`) into a map from module path to
    // the bare names it's allowed to contribute. `UseFilter::Bare` (no
    // braces, deprecated) allows everything, matching pre-brace-syntax
    // behavior.
    let mut filter_map: Map<ModulePath, AllowedNames> = Map::new();
    for use_decl in module.get_uses() {
      if !test_mode && use_decl.has_cfg_test_attr() {
        continue;
      }
      match &use_decl.filter {
        UseFilter::Bare => {
          merge_allowed(
            &mut filter_map,
            use_decl.module_path.clone(),
            AllowedNames::All,
          );
        }
        UseFilter::Items(items) => {
          for item in items {
            for (path, allowed) in item.flatten(&use_decl.module_path) {
              merge_allowed(&mut filter_map, path, allowed);
            }
          }
        }
      }
    }

    // Make sub-modules named in a nested `use` filter (e.g. `io.file` from
    // `use io {file {read}}`) visible for qualified access too, not just
    // the top-level `use`d module.
    for sub_path in filter_map.keys() {
      if !visible_modules.contains_key(sub_path)
        && let Some(mo) = loaded.get_module(sub_path)
      {
        visible_modules.insert(mo.path(), mo);
      }
    }

    // Build def_refs from all visible modules
    let mut def_refs: Map<ModulePath, (Term, Term, ModulePath)> = Map::new();
    let mut bare_names: Map<ModulePath, ModulePath> = Map::new();
    let mut conflicts: Map<ModulePath, Vec<ModulePath>> = Map::new();

    for (_mod_path, modu) in &visible_modules {
      let is_current = modu.path() == module.path();
      let allowed = filter_map.get(modu.path());
      let is_used = allowed.is_some();

      for d in modu.get_def_refs(&opens, test_mode) {
        let bare_name = d.name.clone();

        let included = match allowed {
          Some(AllowedNames::All) => true,
          Some(AllowedNames::Only(names)) => names.contains(bare_name.last()),
          None => true,
        };

        if !included {
          continue;
        }

        // `priv` declarations are invisible from every module except the
        // one that defines them — see `visibility-declarations.md`.
        if !is_current && d.vis == Visibility::Priv {
          continue;
        }

        if !is_current && is_used {
          let prefixed_name = modu.path().clone().extend(bare_name.clone());
          def_refs.insert(
            prefixed_name,
            (d.typ.clone(), d.term.clone(), d.module.clone()),
          );

          match bare_names.get(&bare_name) {
            Some(prev_module) if prev_module != modu.path() => {
              def_refs.remove(&bare_name);
              conflicts
                .entry(bare_name.clone())
                .or_default()
                .push(prev_module.clone());
              conflicts
                .entry(bare_name)
                .or_default()
                .push(modu.path().clone());
            }
            None => {
              bare_names.insert(bare_name.clone(), modu.path().clone());
              def_refs.insert(bare_name, (d.typ.clone(), d.term.clone(), d.module.clone()));
            }
            _ => {}
          }
        } else {
          def_refs.insert(
            d.name.clone(),
            (d.typ.clone(), d.term.clone(), d.module.clone()),
          );
        }
      }
    }

    def_refs.insert(
      mpt("Type"),
      (
        builtins.get_sort_1().typ.clone(),
        builtins.get_sort_1().term.clone(),
        builtins.get_sort_1().module.clone(),
      ),
    );
    def_refs.insert(
      mpt("Prop"),
      (
        builtins.get_sort_0().typ.clone(),
        builtins.get_sort_0().term.clone(),
        builtins.get_sort_0().module.clone(),
      ),
    );
    def_refs.insert(
      mpt("Pred"),
      (
        builtins.get_sort_0().typ.clone(),
        builtins.get_sort_0().term.clone(),
        builtins.get_sort_0().module.clone(),
      ),
    );

    // Build class_defs from all visible modules
    let class_defs: Map<ModulePath, (Identifier, Term, ModulePath)> = visible_modules
      .iter()
      .flat_map(|(_path, modu)| {
        modu
          .get_class_def_refs(&opens)
          .into_iter()
          .map(|d| {
            (
              d.full_name.clone(),
              (d.name.clone(), d.typ.clone(), module.path().clone()),
            )
          })
          .collect::<Vec<_>>()
      })
      .collect();

    // Build instances from all visible modules
    let instances: Map<ModulePath, Vec<Instance>> = visible_modules
      .iter()
      .flat_map(|(_path, modu)| {
        modu
          .instances
          .iter()
          .map(|ins| (ins.class_name.clone(), ins.value().clone()))
      })
      .fold(Map::new(), merge_push_instance);

    // Build inductives from all visible modules
    let inductives: Map<ModulePath, Inductive> = visible_modules
      .iter()
      .flat_map(|(_path, modu)| {
        modu
          .inductives()
          .into_iter()
          .map(|ind| (ind.name.clone(), ind.clone()))
      })
      .collect();

    // Build classes from all visible modules
    let classes: Map<ModulePath, Inductive> = visible_modules
      .iter()
      .flat_map(|(_path, modu)| {
        modu
          .classes()
          .into_iter()
          .map(|class| (class.name.clone(), class.clone()))
      })
      .collect();

    // Build infixes from all visible modules
    let infixes: Map<Operator, Infix> = visible_modules
      .iter()
      .flat_map(|(_path, modu)| {
        modu
          .infix()
          .into_iter()
          .map(|ctx| (ctx.value.operator.clone(), ctx.value().clone()))
      })
      .collect();

    GlobalScopeData {
      module_path: module.path().clone(),
      def_refs,
      class_defs,
      instances,
      inductives,
      classes,
      infixes,
      conflicts,
    }
  }
}

/// Merge a flattened `(ModulePath, AllowedNames)` entry into a filter map,
/// unioning `Only` name sets and letting `All` dominate.
fn merge_allowed(map: &mut Map<ModulePath, AllowedNames>, path: ModulePath, allowed: AllowedNames) {
  match map.get_mut(&path) {
    None => {
      map.insert(path, allowed);
    }
    Some(AllowedNames::All) => {}
    Some(existing) => match allowed {
      AllowedNames::All => *existing = AllowedNames::All,
      AllowedNames::Only(names) => {
        if let AllowedNames::Only(existing_names) = existing {
          existing_names.extend(names);
        }
      }
    },
  }
}

fn merge_push_instance<K, V>(mut map: Map<K, Vec<V>>, (key, value): (K, V)) -> Map<K, Vec<V>>
where
  K: Display + Eq + Ord + Hash + Clone,
{
  if let Some(v) = map.get_mut(&key) {
    v.push(value);
  } else {
    map.insert(key, vec![value]);
  }
  map
}

/// Owner of all loaded scope data, built eagerly from LoadedModules
pub struct LoadedScopes<'a> {
  loaded: &'a LoadedModules,
  scopes: Map<ModulePath, GlobalScopeData>,
}

impl<'a> LoadedScopes<'a> {
  pub fn new(loaded: &'a LoadedModules, test_mode: bool) -> Self {
    let mut scopes = Map::new();
    let module_paths: Vec<ModulePath> = loaded.modules.keys().cloned().collect();
    for path in module_paths {
      if let Some(module) = loaded.get_module(&path) {
        let data = GlobalScopeData::from_module(module, loaded, test_mode);
        scopes.insert(path, data);
      }
    }
    Self { loaded, scopes }
  }

  pub fn global(&'a self, path: &'a ModulePath) -> Option<GlobalScope<'a>> {
    let data = self.scopes.get(path)?;
    let all_scopes = self.scopes.iter().collect();
    Some(GlobalScope::from_data(path, data, self.loaded, all_scopes))
  }
}

/// Scope for a module
#[derive(Debug, Clone)]
pub struct GlobalScope<'a> {
  modules: Map<&'a ModulePath, &'a Module>,
  loaded: &'a LoadedModules,
  current_path: &'a ModulePath,
  def_refs: Map<ModulePath, DefRef<'a>>,
  pub(crate) class_defs: Map<ModulePath, ClassDefRef<'a>>,
  pub(crate) instances: Map<&'a ModulePath, Vec<&'a Instance>>,
  inductives: Map<&'a ModulePath, &'a Inductive>,
  classes: Map<&'a ModulePath, &'a Inductive>,
  infixes: Map<&'a Operator, &'a Infix>,
  all_scopes: Map<&'a ModulePath, &'a GlobalScopeData>,
  conflicts: Map<ModulePath, Vec<ModulePath>>,
}

impl<'a> GlobalScope<'a> {
  pub fn from_decls(
    path: &'a ModulePath,
    decls: &'a Vec<SourceContext<Decl>>,
    loaded: &'a LoadedModules,
  ) -> GlobalScope<'a> {
    let test_mode = loaded.config.test_mode;
    let uses: Vec<&Use> = decls
      .iter()
      .filter_map(|ctx| match ctx.value() {
        Decl::Use(u) if test_mode || !u.has_cfg_test_attr() => Some(u),
        _ => None,
      })
      .collect();
    let mut opens: Vec<&Open> = decls
      .iter()
      .filter_map(|ctx| match ctx.value() {
        Decl::Open(u) if test_mode || !u.has_cfg_test_attr() => Some(u),
        _ => None,
      })
      .collect();
    let builtins = &loaded.builtins;
    let prelude = loaded.get_module(&builtins.prelude_path);
    let mut implicit: Map<&ModulePath, &Module> = Map::new();
    if let Some(prelude) = prelude {
      opens = opens
        .into_iter()
        .chain(prelude.get_opens().iter().map(|ctx| ctx.value()))
        .collect();
      implicit.insert(&builtins.prelude_path, prelude);
    }
    let default_implicit = vec![ModulePath::top("init")];
    for name in default_implicit {
      if let Some(mo) = loaded.get_module(&name) {
        implicit.insert(mo.path(), mo);
      }
    }
    let mut modules = Self::load_modules(&uses, loaded);
    modules.extend(implicit);
    // Include re-exported modules from all visible modules
    {
      let re_exports: Vec<(ModulePath, ModulePath)> = modules
        .values()
        .flat_map(|modu| {
          modu
            .get_pub_uses()
            .into_iter()
            .map(|use_| (modu.path().clone(), use_.module_path.clone()))
        })
        .collect();
      for (_through_module, re_export_path) in re_exports {
        if let Some(mo) = loaded.get_module(&re_export_path) {
          modules.insert(mo.path(), mo);
        }
      }
    }

    let empty_all_scopes: Map<&ModulePath, &GlobalScopeData> = Map::new();
    let used_set: Set<ModulePath> = uses.iter().map(|u| u.module_path.clone()).collect();
    let mut global = GlobalScope::from_modules(
      path,
      modules,
      opens.clone(),
      loaded,
      empty_all_scopes,
      &used_set,
      loaded.test_mode(),
    );
    for ctx in decls {
      global.load_decl(ctx, &opens, path);
    }
    global
  }
  fn load_modules(uses: &Vec<&Use>, loaded: &'a LoadedModules) -> Map<&'a ModulePath, &'a Module> {
    let modules: Map<&ModulePath, &Module> = uses
      .iter()
      .map(|u| {
        let m = loaded
          .get_module(&u.module_path)
          .expect("uses unloaded module");
        (m.path(), m)
      })
      .collect();
    modules
  }
  pub fn for_module(path: &'a ModulePath, loaded: &'a LoadedModules) -> Option<GlobalScope<'a>> {
    let builtins = &loaded.builtins;
    let current_module = loaded.modules.iter().find(|(k, _)| k == &path)?.1;

    // Collect opens from current module and prelude only
    let test_mode = loaded.config.test_mode;
    let mut opens: Vec<&Open> = current_module
      .get_opens()
      .iter()
      .map(|ctx| ctx.value())
      .filter(|o| test_mode || !o.has_cfg_test_attr())
      .collect();
    let prelude = loaded.get_module(&builtins.prelude_path);
    if let Some(prelude) = prelude {
      opens = opens
        .into_iter()
        .chain(prelude.get_opens().iter().map(|ctx| ctx.value()))
        .collect();
    }

    // Collect explicitly used modules
    let uses: Vec<&Use> = current_module
      .get_uses()
      .iter()
      .map(|ctx| ctx.value())
      .filter(|u| test_mode || !u.has_cfg_test_attr())
      .collect();
    let used_set: Set<ModulePath> = uses.iter().map(|u| u.module_path.clone()).collect();

    let mut modules: Map<&ModulePath, &Module> = Map::new();

    // Always include current module
    modules.insert(path, current_module);

    // Include explicitly used modules
    for use_decl in uses {
      if let Some(mo) = loaded.get_module(&use_decl.module_path) {
        modules.insert(&use_decl.module_path, mo);
      }
    }

    // Include default implicit modules: prelude, init
    let default_names: Vec<ModulePath> =
      vec![builtins.prelude_path.clone(), ModulePath::top("init")];
    for default_name in default_names {
      if let Some(mo) = loaded.get_module(&default_name) {
        let mo_path = mo.path();
        modules.insert(mo_path, mo);
      }
    }
    // Include re-exported modules from all visible modules
    {
      let re_exports: Vec<(ModulePath, ModulePath)> = modules
        .values()
        .flat_map(|modu| {
          modu
            .get_pub_uses()
            .into_iter()
            .map(|use_| (modu.path().clone(), use_.module_path.clone()))
        })
        .collect();
      for (_through_module, re_export_path) in re_exports {
        if let Some(mo) = loaded.get_module(&re_export_path) {
          modules.insert(mo.path(), mo);
        }
      }
    }

    let empty_all_scopes: Map<&ModulePath, &GlobalScopeData> = Map::new();
    Some(GlobalScope::from_modules(
      path,
      modules,
      opens,
      loaded,
      empty_all_scopes,
      &used_set,
      loaded.test_mode(),
    ))
  }
  fn from_modules(
    current_path: &'a ModulePath,
    modules: Map<&'a ModulePath, &'a Module>,
    opens: Vec<&'a Open>,
    loaded: &'a LoadedModules,
    all_scopes: Map<&'a ModulePath, &'a GlobalScopeData>,
    used_modules: &Set<ModulePath>,
    test_mode: bool,
  ) -> Self {
    let builtins = &loaded.builtins;

    let mut def_refs: Map<ModulePath, DefRef<'a>> = Map::new();
    let mut bare_names: Map<ModulePath, ModulePath> = Map::new();
    let mut conflicts: Map<ModulePath, Vec<ModulePath>> = Map::new();

    for (mp_mod, module) in &modules {
      let is_current = **mp_mod == *current_path;
      let is_used = !is_current && used_modules.contains(mp_mod);

      for d in module.get_def_refs(&opens, test_mode) {
        // `priv` declarations are invisible from every module except the
        // one that defines them — see `visibility-declarations.md`.
        // `PackagePrivate` (the default) and `Pub` are unfiltered here (no
        // package-boundary enforcement exists yet).
        if !is_current && d.vis == Visibility::Priv {
          continue;
        }
        if is_used {
          let prefixed_name = module.path().clone().extend(d.name.clone());
          let prefixed_def = DefRef {
            name: prefixed_name,
            full_path: d.full_path.clone(),
            typ: d.typ,
            term: d.term,
            module: d.module,
            loc: d.loc,
            vis: d.vis,
          };
          def_refs.insert(prefixed_def.name.clone(), prefixed_def);

          let bare_name = d.name.clone();
          match bare_names.get(&bare_name) {
            Some(prev_mod) if prev_mod != module.path() => {
              def_refs.remove(&bare_name);
              conflicts
                .entry(bare_name.clone())
                .or_default()
                .extend([prev_mod.clone(), module.path().clone()]);
            }
            None => {
              bare_names.insert(bare_name.clone(), module.path().clone());
              def_refs.insert(bare_name, d);
            }
            _ => {}
          }
        } else {
          def_refs.insert(d.name.clone(), d);
        }
      }
    }

    def_refs.insert(mpt("Type"), builtins.get_sort_1());
    def_refs.insert(mpt("Prop"), builtins.get_sort_0());
    def_refs.insert(mpt("Pred"), builtins.get_pred());

    let class_defs = modules
      .iter()
      .flat_map(|(_path, module)| module.get_class_def_refs(&opens).into_iter())
      .map(|d| (d.full_name.clone(), d))
      .collect();
    let classes = modules
      .iter()
      .flat_map(|(_path, module)| {
        module
          .classes()
          .into_iter()
          .map(|class| (&class.name, class))
      })
      .collect();
    let inductives = modules
      .iter()
      .flat_map(|(_path, module)| module.inductives().into_iter().map(|ind| (&ind.name, ind)))
      .collect();
    let instances = modules
      .iter()
      .flat_map(|(_path, module)| {
        module
          .instances
          .iter()
          .map(|ins| (&ins.class_name, ins.value()))
      })
      .fold(Map::new(), merge_push);
    let infixes = modules
      .iter()
      .flat_map(|(_path, module)| module.infix())
      .map(|d| (&d.value.operator, d.value()))
      .collect();

    GlobalScope {
      infixes,
      modules,
      loaded,
      current_path,
      def_refs,
      class_defs,
      instances,
      classes,
      inductives,
      all_scopes,
      conflicts,
    }
  }

  fn from_data(
    current_path: &'a ModulePath,
    data: &'a GlobalScopeData,
    loaded: &'a LoadedModules,
    all_scopes: Map<&'a ModulePath, &'a GlobalScopeData>,
  ) -> Self {
    // Build borrowed DefRefs from owned data
    let def_refs: Map<ModulePath, DefRef<'a>> = data
      .def_refs
      .iter()
      .map(|(name, (typ, term, module))| {
        (
          name.clone(),
          DefRef {
            name: name.clone(),
            full_path: name.clone(),
            typ,
            term,
            module,
            loc: default_source_range(),
            // `data.def_refs` never contains `Priv` entries from other
            // modules to begin with (filtered out in `from_module`), so
            // any placeholder non-`Priv` value is safe here.
            vis: Visibility::Pub,
          },
        )
      })
      .collect();

    // Build borrowed ClassDefRefs from owned data
    let class_defs: Map<ModulePath, ClassDefRef<'a>> = data
      .class_defs
      .iter()
      .filter_map(|(name, (short_name, typ, _module_path))| {
        // Extract class name from full name (first component)
        let class_name = if name.len() > 1 {
          let ids = name.clone().to_vec();
          ModulePath::new(ids[..1].to_vec())
        } else {
          name.clone()
        };
        let class = data
          .classes
          .get(&class_name)
          .or_else(|| data.classes.values().find(|c| c.name == class_name))?;
        Some((
          name.clone(),
          ClassDefRef {
            full_name: name.clone(),
            name: short_name,
            typ,
            class,
          },
        ))
      })
      .collect();

    // Build borrowed references from owned data
    let inductives: Map<&'a ModulePath, &'a Inductive> = data.inductives.iter().collect();

    let classes: Map<&'a ModulePath, &'a Inductive> = data.classes.iter().collect();

    let instances: Map<&'a ModulePath, Vec<&'a Instance>> = data
      .instances
      .iter()
      .map(|(class_name, instances)| (class_name, instances.iter().collect()))
      .collect();

    let infixes: Map<&'a Operator, &'a Infix> = data.infixes.iter().collect();

    let conflicts = data.conflicts.clone();

    GlobalScope {
      infixes,
      modules: Map::new(),
      loaded,
      current_path,
      def_refs,
      class_defs,
      instances,
      classes,
      inductives,
      all_scopes,
      conflicts,
    }
  }

  pub fn get_module_scope(&self, module_path: &'a ModulePath) -> Option<GlobalScope<'a>> {
    let data = self.all_scopes.get(module_path)?;
    let all_scopes = self.all_scopes.clone();
    Some(GlobalScope::from_data(
      module_path,
      data,
      self.loaded,
      all_scopes,
    ))
  }

  pub fn scope(&'a self) -> Scope<'a> {
    Scope::new(self)
  }

  pub fn builtins(&self) -> &Builtins {
    &self.loaded.builtins
  }
  pub fn current_path(&self) -> &ModulePath {
    self.current_path
  }

  pub fn prelude(&self) -> Option<&Module> {
    self.get_module(&self.loaded.builtins.prelude_path)
  }
  pub fn instances(&self) -> Vec<(&ModulePath, &Vec<&Instance>)> {
    self.instances.iter().map(|(c, i)| (*c, i)).collect()
  }

  pub fn get_module(&self, path: &ModulePath) -> Option<&Module> {
    self.modules.get(path).copied()
  }

  pub fn inductives(&self) -> Vec<&Inductive> {
    self.inductives.values().copied().collect()
  }
  pub fn classes(&self) -> Vec<&Inductive> {
    self.classes.values().copied().collect()
  }
  pub fn modules(&self) -> Vec<&Module> {
    self.modules.values().copied().collect()
  }
  pub fn all_known_names(&self) -> Set<&ModulePath> {
    let mut names: Set<&ModulePath> = self.def_refs.keys().collect();
    names.extend(self.inductives.keys().copied());
    names.extend(self.class_defs.keys());
    names
  }

  pub fn infix(&self) -> Vec<(&Operator, &SourceContext<Infix>)> {
    self
      .modules
      .values()
      .flat_map(|v| v.infix.iter().collect::<Vec<_>>())
      .collect()
  }

  pub fn find_class_def(&'_ self, name: &ModulePath) -> Option<&'_ ClassDefRef<'_>> {
    self.class_defs.get(name)
  }

  pub fn find_inductive(&self, name: &ModulePath) -> Option<&Inductive> {
    let inductive = self.inductives.get(name)?;
    Some(inductive)
  }

  pub fn find_instance(&self, ins_key: &InstanceKey) -> Option<&Instance> {
    let mut visiting = Set::default();
    self.find_instance_with_visiting(ins_key, &mut visiting)
  }

  pub fn find_instance_with_visiting(
    &self,
    ins_key: &InstanceKey,
    visiting: &mut Set<String>,
  ) -> Option<&Instance> {
    let class = &self.find_inductive(&ins_key.class)?;
    let instance = self.instances.get(&ins_key.class).and_then(|instances| {
      instances
        .iter()
        .find(|ins| ins.matches(ins_key, class, self, visiting))
    })?;
    Some(instance)
  }
  pub fn find_infix(&self, op: &Operator) -> Result<&Infix, ScopeError> {
    let infix = self
      .infixes
      .get(op)
      .ok_or_else(|| ScopeError::OperatorNotDefined(op.clone()))?;
    Ok(infix)
  }
  pub fn find_ref(&'_ self, name: &ModulePath) -> Option<&DefRef<'_>> {
    self.def_refs.get(name)
  }
  /// Search for a term in ANY module scope (transitive dependencies).
  /// Returns the term from the def if found in any loaded module.
  pub fn find_term_transitive(&self, name: &ModulePath) -> Option<&Term> {
    if let Some(def) = self.def_refs.get(name) {
      return Some(def.term);
    }
    for (_mod_path, mod_data) in self.all_scopes.iter() {
      if let Some((_typ, term, _module)) = mod_data.def_refs.get(name) {
        return Some(term);
      }
    }
    None
  }
  /// Try to resolve a class method reference for the given name and type.
  /// Returns the instance definition reference, or an error.
  fn resolve_class_method<'s>(
    &'s self,
    _name: &ModulePath,
    typ: &Term,
    def: &'s ClassDefRef<'s>,
  ) -> Result<VarRef<'s>, ScopeError> {
    let key = derive_instance_key(def, typ)?;
    let instance = self
      .find_instance(&key)
      .ok_or_else(|| ScopeError::InstanceNotFound(key.clone()))?;
    let ins_def_name = instance.name.clone().extend(def.name.clone().to_path());
    let ins_def: &'s DefRef<'s> = self
      .find_ref(&ins_def_name)
      .ok_or(ScopeError::PathNotFound(ins_def_name))?;
    let method_constraints = def.method_constraints();
    Ok(VarRef::UpdateRef {
      new_path: &ins_def.name,
      typ: ins_def.typ,
      term: ins_def.term,
      method_constraints,
    })
  }

  pub fn find_any_ref(&'_ self, name: &ModulePath, typ: &Term) -> Result<VarRef<'_>, ScopeError> {
    if let Some(candidates) = self.conflicts.get(name) {
      return Err(ScopeError::AmbiguousName {
        name: name.clone(),
        candidates: candidates.clone(),
      });
    }
    if let Some(def) = self.find_ref(name) {
      Ok(def.to_var_ref())
    } else if let Some(def) = self.find_class_def(name) {
      let result = self.resolve_class_method(name, typ, def);
      // Fallback: if IndexedMonad resolution fails, try Monad
      if result.is_err() && is_indexed_monad_method(name) {
        if let Some(monad_name) = to_monad_name(name) {
          if let Some(monad_def) = self.find_class_def(&monad_name) {
            return self.resolve_class_method(&monad_name, typ, monad_def);
          }
        }
      }
      result
    } else {
      Err(ScopeError::PathNotFound(name.clone()))
    }
  }
  pub fn find_any_name_ref(&'_ self, nref: &NameRef, typ: &Term) -> Result<VarRef<'_>, ScopeError> {
    if let Some(i) = nref.clone().to_path() {
      let var = self.find_any_ref(&i, typ)?;
      Ok(var)
    } else if let NameRef::Op(op) = nref {
      let infix = self.find_infix(op)?;
      let var = self.find_any_ref(&infix.name, typ)?;
      Ok(var)
    } else if let NameRef::Macro(name) = nref {
      let path = ModulePath::single(name.clone());
      let var = self.find_any_ref(&path, typ)?;
      Ok(var)
    } else {
      Err(nref_error(nref.clone()))
    }
  }

  /// Resolve a class method name to the first available instance's implementation term.
  /// Used by the evaluator when the type checker cannot resolve a class method to a
  /// concrete instance (e.g., constrained instances with abstract type variables).
  pub fn resolve_class_method_instance(&self, name: &ModulePath) -> Option<&Term> {
    let class_def = self.find_class_def(name)?;
    let class_name = class_def.class.name();
    let instances = self.instances.get(class_name)?;
    for instance in instances.iter() {
      if instance.impls_map.contains_key(class_def.name) {
        let method_name = instance
          .name
          .clone()
          .extend(ModulePath::single(class_def.name.clone()));
        let def = self.find_ref(&method_name)?;
        return Some(def.term);
      }
    }
    None
  }

  pub fn find_any_name_ref_with_constraints(
    &'_ self,
    nref: &NameRef,
    typ: &Term,
    constraints: &[TypeConstraint],
  ) -> Result<VarRef<'_>, ScopeError> {
    if let Some(i) = nref.clone().to_path() {
      let var = self.find_any_ref_with_constraints(&i, typ, constraints)?;
      Ok(var)
    } else if let NameRef::Op(op) = nref {
      let infix = self.find_infix(op)?;
      let var = self.find_any_ref_with_constraints(&infix.name, typ, constraints)?;
      Ok(var)
    } else if let NameRef::Macro(name) = nref {
      let path = ModulePath::single(name.clone());
      let var = self.find_any_ref_with_constraints(&path, typ, constraints)?;
      Ok(var)
    } else {
      Err(nref_error(nref.clone()))
    }
  }

  pub fn find_any_ref_with_constraints(
    &'_ self,
    name: &ModulePath,
    typ: &Term,
    constraints: &[TypeConstraint],
  ) -> Result<VarRef<'_>, ScopeError> {
    if let Some(candidates) = self.conflicts.get(name) {
      return Err(ScopeError::AmbiguousName {
        name: name.clone(),
        candidates: candidates.clone(),
      });
    }
    if let Some(def) = self.find_ref(name) {
      Ok(def.to_var_ref())
    } else if let Some(def) = self.find_class_def(name) {
      let result = self.resolve_class_method_with_constraints(name, typ, def, constraints);
      if result.is_err() && is_indexed_monad_method(name) {
        if let Some(monad_name) = to_monad_name(name) {
          if let Some(monad_def) = self.find_class_def(&monad_name) {
            return self.resolve_class_method_with_constraints(
              &monad_name,
              typ,
              monad_def,
              constraints,
            );
          }
        }
      }
      result
    } else {
      Err(ScopeError::PathNotFound(name.clone()))
    }
  }

  fn resolve_class_method_with_constraints(
    &'_ self,
    _name: &ModulePath,
    typ: &Term,
    def: &ClassDefRef,
    constraints: &[TypeConstraint],
  ) -> Result<VarRef<'_>, ScopeError> {
    let maybe_key = derive_instance_key(def, typ);
    // Check constraints for a matching class — produce a ClassMethod ref
    // for runtime resolution even if derive_instance_key failed.
    for constraint in constraints {
      if *constraint.class() == *def.class.name() {
        if let Some(ty) = constraint.vars().first() {
          let class_param_name = def.class.params.first().map(|p| p.name.clone());
          let param_name = class_param_name.unwrap_or_else(|| ty.clone());
          let constrained_key = InstanceKey::new(
            constraint.class().clone(),
            vec![],
            vec![crate::term::param(
              param_name,
              Term::Var {
                name: NameRef::Id(ty.clone()),
              },
            )],
          );
          if let Some(instance) = self.find_instance(&constrained_key) {
            let ins_def_name = instance.name.clone().extend(def.name.clone().to_path());
            let ins_def = self
              .find_ref(&ins_def_name)
              .ok_or(ScopeError::PathNotFound(ins_def_name))?;
            return Ok(ins_def.to_update_ref());
          }
          // No concrete instance found for the type variable, but the
          // constraint guarantees one exists. Produce a ClassMethod ref
          // for runtime resolution.
          let method_name = def.name.clone();
          let class_name = def.class.name().clone();
          return Ok(VarRef::ClassMethod {
            class_name,
            method_name,
            type_var: ty.clone(),
            typ: typ.clone(),
          });
        }
      }
    }
    // No matching constraint found, try the concrete key (if it was derived)
    if let Ok(key) = maybe_key {
      if let Some(instance) = self.find_instance(&key) {
        let ins_def_name = instance.name.clone().extend(def.name.clone().to_path());
        let ins_def = self
          .find_ref(&ins_def_name)
          .ok_or(ScopeError::PathNotFound(ins_def_name))?;
        return Ok(ins_def.to_update_ref());
      }
      Err(ScopeError::InstanceNotFound(key.clone()))
    } else {
      Err(maybe_key.unwrap_err().into())
    }
  }

  fn load_decl<'o>(
    &mut self,
    ctx: &'a SourceContext<Decl>,
    opens: &Vec<&'o Open>,
    module: &'a ModulePath,
  ) {
    self.load_decl_inner(ctx.value(), &ctx.loc, opens, module);
  }

  /// Core of `load_decl`, taking the declaration and its source location
  /// separately so `Decl::ScopedOpen` can recurse into its boxed inner
  /// declaration with a locally-synthesized `Open` chained onto `opens`
  /// (the synthesized `Open` only needs to live for this call, not for
  /// `'a`, hence the independent `'o` lifetime).
  fn load_decl_inner<'o>(
    &mut self,
    decl: &'a Decl,
    loc: &'a SourceRange,
    opens: &Vec<&'o Open>,
    module: &'a ModulePath,
  ) {
    match decl {
      Decl::ScopedOpen {
        module_path,
        filter,
        decl: inner,
        ..
      } => {
        let synthetic_open = Open {
          source_location: loc.clone(),
          module_path: module_path.clone(),
          filter: filter.clone(),
          attributes: vec![],
        };
        let augmented_opens: Vec<&Open> = opens
          .iter()
          .copied()
          .chain(std::iter::once(&synthetic_open))
          .collect();
        self.load_decl_inner(inner, loc, &augmented_opens, module);
      }
      Decl::Def(def) | Decl::DefMacro(def) => {
        let name = &def.name;
        let names = name.open(opens);
        let def_refs: Map<ModulePath, DefRef> = names
          .iter()
          .map(|name| DefRef {
            name: name.clone(),
            full_path: def.name.clone(),
            typ: &def.typ,
            term: &def.term,
            module,
            loc,
            vis: def.vis,
          })
          .chain([DefRef {
            name: name.clone(),
            full_path: name.clone(),
            typ: &def.typ,
            term: &def.term,
            module,
            loc,
            vis: def.vis,
          }])
          .map(|d| (d.name.clone(), d))
          .collect();
        self.def_refs.extend(def_refs);
      }
      Decl::Type(ind) => {
        self.inductives.insert(&ind.name, ind);
        let def_refs: Map<ModulePath, DefRef> = ind
          .constructors
          .iter()
          .flat_map(|cons| {
            let name = &cons.name;

            let names = name.open(opens);
            let refs = names
              .iter()
              .map(|name| DefRef {
                name: name.clone(),
                full_path: cons.name.clone(),
                typ: &cons.typ,
                term: &cons.term,
                module,
                loc,
                vis: ind.vis,
              })
              .chain([DefRef {
                name: name.clone(),
                full_path: name.clone(),
                typ: &cons.typ,
                term: &cons.term,
                module,
                loc,
                vis: ind.vis,
              }])
              .collect::<Vec<DefRef>>();

            if ind.variant == InductiveVariant::Class {
              let class_refs = cons
                .params
                .iter()
                .flat_map(|class_def| {
                  let def_name = ind.name.clone().extend(class_def.name.clone().to_path());
                  let names = def_name.open(opens);
                  names
                    .into_iter()
                    .map(|path| class_def_ref(path, &class_def.name, &class_def.typ, ind))
                    .chain([class_def_ref(
                      def_name,
                      &class_def.name,
                      &class_def.typ,
                      ind,
                    )])
                    .collect::<Vec<ClassDefRef>>()
                })
                .map(|c| (c.full_name.clone(), c))
                .collect::<Vec<(ModulePath, ClassDefRef)>>();
              self.class_defs.extend(class_refs);
              vec![]
            } else {
              refs
            }
          })
          .chain([DefRef {
            name: ind.name.clone(),
            full_path: ind.name.clone(),
            typ: &ind.typ,
            term: &ind.term,
            module,
            loc,
            vis: ind.vis,
          }])
          .map(|d| (d.name.clone(), d))
          .collect();

        self.def_refs.extend(def_refs);
      }
      Decl::Ins(instance) => {
        if let Some(v) = self.instances.get_mut(&instance.class_name) {
          v.push(instance);
        } else {
          self.instances.insert(&instance.class_name, vec![instance]);
        }
        let def_refs: Map<ModulePath, DefRef> = instance
          .impls_map
          .iter()
          .map(|(name, imp)| {
            let full_name = instance
              .name
              .clone()
              .extend(ModulePath::single(name.clone()));

            DefRef {
              name: full_name.clone(),
              full_path: full_name,
              typ: &imp.typ,
              vis: instance.vis,
              term: &imp.term,
              module,
              loc,
            }
          })
          .map(|d| (d.name.clone(), d))
          .collect();
        self.def_refs.extend(def_refs);
      }
      Decl::Infix(infix) => {
        self.infixes.insert(&infix.operator, infix);
      }
      _ => (),
    };
  }
}

#[derive(Debug, Clone)]
pub enum Scope<'a> {
  Top {
    global: &'a GlobalScope<'a>,
    module_path: &'a ModulePath,
    usage_env: UsageEnv,
    constraints: Vec<TypeConstraint>,
  },
  Sub {
    local: LocalVar<'a>,
    parent: Box<Scope<'a>>,
    module_path: &'a ModulePath,
    usage_env: UsageEnv,
    constraints: Vec<TypeConstraint>,
  },
}

impl<'a> Scope<'a> {
  pub fn new(global: &'a GlobalScope<'a>) -> Scope<'a> {
    Scope::Top {
      global,
      module_path: global.current_path(),
      usage_env: UsageEnv::new(),
      constraints: Vec::new(),
    }
  }

  /// Get a reference to the usage environment
  pub fn usage_env(&self) -> &UsageEnv {
    match self {
      Scope::Top { usage_env, .. } => usage_env,
      Scope::Sub { usage_env, .. } => usage_env,
    }
  }

  /// Get a mutable reference to the usage environment
  pub fn usage_env_mut(&mut self) -> &mut UsageEnv {
    match self {
      Scope::Top { usage_env, .. } => usage_env,
      Scope::Sub { usage_env, .. } => usage_env,
    }
  }
  pub fn constraints(&self) -> &[TypeConstraint] {
    match self {
      Scope::Top { constraints, .. } => constraints,
      Scope::Sub { constraints, .. } => constraints,
    }
  }

  pub fn with_constraints(&self, cs: Vec<TypeConstraint>) -> Scope<'a> {
    match self {
      Scope::Top {
        global,
        module_path,
        usage_env,
        ..
      } => Scope::Top {
        global,
        module_path,
        usage_env: usage_env.clone(),
        constraints: cs,
      },
      Scope::Sub {
        local,
        parent,
        module_path,
        usage_env,
        ..
      } => Scope::Sub {
        local: local.clone(),
        parent: parent.clone(),
        module_path,
        usage_env: usage_env.clone(),
        constraints: cs,
      },
    }
  }

  /// Extract term of NameRef
  pub fn resolve_name(&self, nref: &NameRef) -> Result<&Term, ScopeError> {
    let global = self.global();
    if let Some(name) = nref.clone().to_path() {
      if let Some(def) = global.find_ref(&name) {
        Ok(def.term)
      } else if let Some(_class_def) = global.find_class_def(&name) {
        if let Some(term) = global.resolve_class_method_instance(&name) {
          Ok(term)
        } else {
          Ok(_class_def.typ())
        }
      } else {
        Err(ScopeError::PathNotFound(name))
      }
    } else if let NameRef::Op(op) = nref {
      let infix = global.find_infix(op)?;
      if let Some(def) = global.find_ref(&infix.name) {
        Ok(def.term)
      } else if let Some(_class_def) = global.find_class_def(&infix.name) {
        if let Some(term) = global.resolve_class_method_instance(&infix.name) {
          Ok(term)
        } else {
          Ok(_class_def.typ())
        }
      } else {
        Err(ScopeError::PathNotFound(infix.name.clone()))
      }
    } else {
      Err(ScopeError::Generic(format!("{nref} not found")))
    }
  }

  pub fn find_inductive(&self, name: &ModulePath) -> Result<&Inductive, ScopeError> {
    let ind = self
      .global()
      .find_inductive(name)
      .ok_or_else(|| ScopeError::PathNotFound(name.clone()))?;
    Ok(ind)
  }

  pub fn find_local(&'a self, local_name: &Identifier) -> Option<&'a LocalVar<'a>> {
    match self {
      Scope::Top { global: _, .. } => None,
      Scope::Sub { local, parent, .. } => {
        if let Some(name) = local.name()
          && name == local_name
        {
          Some(local)
        } else {
          parent.find_local(local_name)
        }
      }
    }
  }

  /// Named local variables
  pub fn locals(&'a self) -> Map<&'a Identifier, &'a LocalVar<'a>> {
    match self {
      Scope::Top { global: _, .. } => Map::new(),
      Scope::Sub { local, parent, .. } => {
        let mut loc = parent.locals();
        if let Some(name) = local.name() {
          loc.insert(name, local);
        }
        loc
      }
    }
  }
  pub fn local_foralls(&'a self) -> Map<&'a Identifier, &'a LocalVar<'a>> {
    match self {
      Scope::Top { global: _, .. } => Map::new(),
      Scope::Sub { local, parent, .. } => {
        let mut loc = parent.local_foralls();
        if let LocalVar::Forall { .. } = local
          && let Some(name) = local.name()
        {
          loc.insert(name, local);
        }
        loc
      }
    }
  }
  pub fn local_bindings(&self) -> Map<Identifier, Term> {
    self
      .locals()
      .into_iter()
      .map(|(name, var)| (name.clone(), var.typ().clone()))
      .collect()
  }

  pub fn find_var_ref_of(
    &'a self,
    nref: &NameRef,
    given_type: &Term,
  ) -> Result<VarRef<'a>, ScopeError> {
    use Scope::{Sub, Top};
    match self {
      Sub { local, parent, .. } => {
        if let Some(name) = nref.as_id()
          && let Some(local_name) = local.name()
          && name == local_name
        {
          Ok(local.into())
        } else {
          parent.find_var_ref_of(nref, given_type)
        }
      }
      Top { global, .. } => {
        let def = global.find_any_name_ref(nref, given_type)?;
        Ok(def)
      }
    }
  }

  pub fn with_param(&self, param: &'a Par) -> Scope<'a> {
    let mult = param.multiplicity();
    let mut usage_env = self.usage_env().clone();
    let constraints = self.constraints().to_vec();
    let module_path = self.module_path();
    match param {
      Par::P(param) => {
        usage_env.register(param.name.clone(), mult.clone());
        Scope::Sub {
          local: local_var(&param.name, param.typ.as_ref()),
          parent: Box::new(self.clone()),
          module_path,
          usage_env,
          constraints,
        }
      }
      Par::I { typ, .. } => {
        // Anonymous implicit param - no name to register
        Scope::Sub {
          local: local_index_var(typ.as_ref()),
          parent: Box::new(self.clone()),
          module_path,
          usage_env,
          constraints,
        }
      }
    }
  }
  pub fn with_local_var(&self, name: &'a Identifier, typ: &'a Term) -> Scope<'a> {
    let mut usage_env = self.usage_env().clone();
    usage_env.register(name.clone(), Multiplicity::Many);
    Scope::Sub {
      local: local_var(name, typ),
      parent: Box::new(self.clone()),
      module_path: self.module_path(),
      usage_env,
      constraints: self.constraints().to_vec(),
    }
  }
  pub fn with_forall(&self, name: &'a Identifier, typ: &'a Term) -> Scope<'a> {
    Scope::Sub {
      local: local_forall(name, typ),
      parent: Box::new(self.clone()),
      module_path: self.module_path(),
      usage_env: self.usage_env().clone(),
      constraints: self.constraints().to_vec(),
    }
  }
  pub fn with_local_index_var(&self, typ: &'a Term) -> Scope<'a> {
    Scope::Sub {
      local: local_index_var(typ),
      parent: Box::new(self.clone()),
      module_path: self.module_path(),
      usage_env: self.usage_env().clone(),
      constraints: self.constraints().to_vec(),
    }
  }
  pub fn with_type_owned(&self, name: &'a Identifier, typ: Term) -> Scope<'a> {
    Scope::Sub {
      local: local_var_owned(name, typ),
      parent: Box::new(self.clone()),
      module_path: self.module_path(),
      usage_env: self.usage_env().clone(),
      constraints: self.constraints().to_vec(),
    }
  }

  pub fn global(&self) -> &GlobalScope<'a> {
    match self {
      Scope::Top { global, .. } => global,
      Scope::Sub { parent, .. } => parent.global(),
    }
  }
  pub fn module_path(&self) -> &'a ModulePath {
    match self {
      Scope::Top { module_path, .. } => module_path,
      Scope::Sub { module_path, .. } => module_path,
    }
  }
}

pub fn find_builtin(_name: &ModulePath) -> Option<&Decl> {
  None
}

#[derive(Clone, Debug)]
pub enum LoadingError {
  Generic(String),
  Type(TypeError),
}

impl Display for LoadingError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      LoadingError::Generic(s) => write!(f, "{s}"),
      LoadingError::Type(type_error) => write!(f, "{type_error}"),
    }
  }
}

impl From<String> for LoadingError {
  fn from(value: String) -> Self {
    LoadingError::Generic(value)
  }
}
impl From<TypeError> for LoadingError {
  fn from(value: TypeError) -> Self {
    LoadingError::Type(value)
  }
}

fn load_decl_uses_modules(
  decls: &[SourceContext<Decl>],
  loaded: LoadedModules,
  in_progress: &mut Set<ModulePath>,
) -> Result<LoadedModules, LoadingError> {
  let test_mode = loaded.config.test_mode;
  let mut uses = decls.iter().filter_map(|ctx| match ctx.value() {
    Decl::Use(u) if test_mode || !u.has_cfg_test_attr() => Some(u),
    _ => None,
  });
  let loaded = uses.try_fold(
    loaded,
    |loaded, use_| -> Result<LoadedModules, LoadingError> {
      let loaded = if loaded.get_module(&use_.module_path).is_none() {
        load_module_files_inner(&use_.module_path, loaded, in_progress)?
      } else {
        loaded
      };

      Ok(loaded)
    },
  )?;
  Ok(loaded)
}

pub fn load_module_files(
  path: &ModulePath,
  loaded: LoadedModules,
) -> Result<LoadedModules, LoadingError> {
  let mut in_progress = crate::empty_set();
  load_module_files_inner(path, loaded, &mut in_progress)
}

pub fn load_module_files_inner(
  path: &ModulePath,
  loaded: LoadedModules,
  in_progress: &mut Set<ModulePath>,
) -> Result<LoadedModules, LoadingError> {
  if !in_progress.insert(path.clone()) {
    return Err(format!("module cycle detected: {}", path).into());
  }
  let result = load_module_files_impl(path, loaded, in_progress);
  in_progress.remove(path);
  result
}

fn load_module_files_impl(
  path: &ModulePath,
  loaded: LoadedModules,
  in_progress: &mut Set<ModulePath>,
) -> Result<LoadedModules, LoadingError> {
  if let Some(_) = loaded.get_module(path) {
    return Ok(loaded);
  }
  let parse_start = Instant::now();
  let search_paths = loaded.search_paths().clone();
  let decls = load_decls(path, &search_paths)?;
  let parse_dur = parse_start.elapsed();
  let mut loaded = load_decl_uses_modules(&decls, loaded, in_progress)?;
  let decls = filter_cfg_test_decls(decls, loaded.config.test_mode);
  validate_open_filters(&decls)?;
  let tc_start = Instant::now();
  let decls = crate::core_check_module::type_check_module_decls_new(path, decls, &loaded)?;
  let tc_dur = tc_start.elapsed();
  if loaded.config.benchmark {
    eprintln!(
      "  [{}] parse={} typeck={}",
      path,
      format_duration(parse_dur),
      format_duration(tc_dur),
    );
  }
  let mo = module(
    path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  );
  loaded.add_module(mo);
  Ok(loaded)
}

pub fn load_decls(
  path: &ModulePath,
  search_paths: &SearchPaths,
) -> Result<Vec<SourceContext<Decl>>, String> {
  let file_path = path
    .resolve_file_path(search_paths)
    .or_else(|| {
      let p = path.to_file_path();
      if p.exists() { Some(p) } else { None }
    })
    .ok_or_else(|| format!("module not found: {path}"))?;
  let text = read_to_string(&file_path).map_err(|e| e.to_string())?;
  load_decls_from_text_with_path(
    &text,
    &ModuleContext {
      file: Some(file_path),
      path: path.clone(),
    },
  )
}

pub fn load_decls_from_text(text: &str) -> Result<Vec<SourceContext<Decl>>, String> {
  load_decls_from_text_with_path(text, &Default::default())
}

pub fn load_decls_from_text_with_path(
  text: &str,
  context: &ModuleContext,
) -> Result<Vec<SourceContext<Decl>>, String> {
  let parsed = parse_file_with_path(text, &context).map_err(|e| format!("{e}"))?;
  Ok(parsed.decls)
}

fn filter_cfg_test_decls(
  decls: Vec<SourceContext<Decl>>,
  test_mode: bool,
) -> Vec<SourceContext<Decl>> {
  if test_mode {
    return decls;
  }
  decls
    .into_iter()
    .filter(|ctx| match ctx.value() {
      Decl::Use(u) => !u.has_cfg_test_attr(),
      Decl::Open(o) => !o.has_cfg_test_attr(),
      _ => true,
    })
    .collect()
}

pub fn load_module_from_text(
  text: &str,
  path: &ModulePath,
  loaded: &mut LoadedModules,
) -> Result<(), LoadingError> {
  let file_path = path.to_file_path();
  let module_context = ModuleContext::new(path.clone(), Some(file_path));
  let parse_start = Instant::now();
  let init_decls = load_decls_from_text_with_path(text, &module_context)
    .map_err(|e| format!("parse error for {}: {e}", path))?;
  let parse_dur = parse_start.elapsed();
  let mut in_progress = crate::empty_set();
  *loaded = load_decl_uses_modules(&init_decls, loaded.clone(), &mut in_progress)?;
  let init_decls = filter_cfg_test_decls(init_decls, loaded.config.test_mode);
  if let Err(e) = validate_open_filters(&init_decls) {
    let file_path = path.to_file_path();
    let rendered = render_type_error_with_source(text, &e, false, Some(&file_path));
    return Err(LoadingError::Generic(rendered));
  }
  let tc_start = Instant::now();
  // The De-Bruijn/MetaId-based checker — see
  // plans/implementations/typechecker-de-bruijn-core.md and
  // plans/implementations/core-term-closure-evaluator.md (the old
  // name-keyed-unifier checker this replaced has been removed entirely).
  let init_decls_result =
    crate::core_check_module::type_check_module_decls_new(&path, init_decls, loaded);
  let init_decls = init_decls_result.map_err(|e| {
    let file_path = path.to_file_path();
    let rendered = render_type_error_with_source(text, &e, false, Some(&file_path));
    LoadingError::Generic(rendered)
  })?;
  let tc_dur = tc_start.elapsed();
  if loaded.config.benchmark {
    eprintln!(
      "  [{}] parse={} typeck={}",
      path,
      format_duration(parse_dur),
      format_duration(tc_dur),
    );
  }
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls: init_decls,
      module_doc: None,
    },
  ));
  Ok(())
}

/// Like `load_module_from_text`, but for a caller (`check_files`) that
/// wants the STRUCTURED `TypeError` a type-check failure produced —
/// `LoadingError::Type(e)`, not `load_module_from_text`'s own
/// `LoadingError::Generic(rendered_string)` — so it can turn each
/// individual error into its own positioned `Diagnostic` instead of one
/// opaque pre-rendered text blob. A separate function rather than a
/// parameter on `load_module_from_text` itself: that function's callers
/// (`Run`/`Test`/`Repl`, via `load_module`/`load_module_files`) all just
/// `Display` the error as one human-readable string today, and changing
/// its own error branch would flow through to `LoadingError::Type`'s
/// plainer `Display` (no source-context box) for those, an unrelated UX
/// regression this function avoids entirely by never touching the
/// original. Everything before the type-check step is intentionally
/// identical to `load_module_from_text` (parsing/scope logic is shared,
/// unchanged, and not what this function exists to affect).
pub fn load_module_from_text_typed(
  text: &str,
  path: &ModulePath,
  loaded: &mut LoadedModules,
) -> Result<(), LoadingError> {
  let file_path = path.to_file_path();
  let module_context = ModuleContext::new(path.clone(), Some(file_path));
  let init_decls = load_decls_from_text_with_path(text, &module_context)
    .map_err(|e| format!("parse error for {}: {e}", path))?;
  let mut in_progress = crate::empty_set();
  *loaded = load_decl_uses_modules(&init_decls, loaded.clone(), &mut in_progress)?;
  let init_decls = filter_cfg_test_decls(init_decls, loaded.config.test_mode);
  validate_open_filters(&init_decls)?;
  let init_decls_result =
    crate::core_check_module::type_check_module_decls_new(&path, init_decls, loaded);
  let init_decls = init_decls_result.map_err(LoadingError::Type)?;
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls: init_decls,
      module_doc: None,
    },
  ));
  Ok(())
}

/// Returns the path to the `init/` stdlib directory when loading from filesystem.
#[cfg(not(feature = "embed-stdlib"))]
fn stdlib_dir() -> std::path::PathBuf {
  if let Ok(dir) = std::env::var("MONAD_STDLIB") {
    return std::path::PathBuf::from(dir);
  }
  // CARGO_MANIFEST_DIR is core/ — parent is the workspace root, then init/
  std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .expect("CARGO_MANIFEST_DIR has no parent")
    .join("init")
}

/// `(module path, source text)` pairs for the `init` package, in
/// dependency order (`prelude`/`id`/`io`/`number` have no deps; `math`
/// depends on `number`; `string` depends on `math`; `init` depends on
/// `io`/`number`/`math`/`string`; `process` is last) — the same order
/// `init_module` below loads them in, factored out so a caller that needs
/// the raw `Decl`s (not just an already-checked `Module`) can get them
/// without hand-duplicating this path/order list. Respects `embed-stdlib`
/// exactly like `init_module` does: compiled-in text when that feature is
/// on, read from disk at runtime (via `stdlib_dir()`) otherwise.
pub fn init_package_sources() -> Result<Vec<(ModulePath, String)>, LoadingError> {
  let names = [
    "'prelude", "id", "io", "number", "math", "string", "init", "process",
  ];

  #[cfg(feature = "embed-stdlib")]
  let texts: [&str; 8] = [
    include_str!("../../../init/prelude.mo"),
    include_str!("../../../init/id.mo"),
    include_str!("../../../init/io.mo"),
    include_str!("../../../init/number.mo"),
    include_str!("../../../init/math.mo"),
    include_str!("../../../init/string.mo"),
    include_str!("../../../init/init.mo"),
    include_str!("../../../init/process.mo"),
  ];
  #[cfg(feature = "embed-stdlib")]
  let sources = names
    .into_iter()
    .zip(texts)
    .map(|(name, text)| (ModulePath::top(name), text.to_string()))
    .collect();

  #[cfg(not(feature = "embed-stdlib"))]
  let sources = {
    let dir = stdlib_dir();
    let files = [
      "prelude.mo",
      "id.mo",
      "io.mo",
      "number.mo",
      "math.mo",
      "string.mo",
      "init.mo",
      "process.mo",
    ];
    let mut sources = Vec::with_capacity(names.len());
    for (name, file) in names.into_iter().zip(files) {
      let text = std::fs::read_to_string(dir.join(file)).map_err(|e| {
        LoadingError::Generic(format!(
          "failed to read {}: {}",
          dir.join(file).display(),
          e
        ))
      })?;
      sources.push((ModulePath::top(name), text));
    }
    sources
  };

  Ok(sources)
}

pub fn init_module(mut loaded: LoadedModules) -> Result<LoadedModules, LoadingError> {
  for (path, text) in init_package_sources()? {
    load_module_from_text(&text, &path, &mut loaded)?;
  }
  Ok(loaded)
}

/// The on-disk source files backing the embedded/default modules
/// (`init_module` above), as canonicalized paths. Used by `check_files`/
/// `run_tests`/`organize_imports_for_files` to recognize "this CLI argument
/// literally is one of the always-loaded default modules" precisely — by
/// comparing actual files, not by comparing the last segment of a module
/// path, which false-positives on any file that merely happens to share a
/// name with a default module (e.g. `lang/parser/number.mo` vs the
/// top-level `number` default module).
///
/// Not feature-gated: the `init/` directory is part of the repo regardless
/// of whether `embed-stdlib` baked its contents into the binary at compile
/// time, so the same path list is valid for both build configurations.
pub fn default_module_source_files() -> Vec<std::path::PathBuf> {
  let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .expect("CARGO_MANIFEST_DIR has no parent")
    .join("init");
  [
    "prelude.mo",
    "id.mo",
    "io.mo",
    "number.mo",
    "math.mo",
    "string.mo",
    "init.mo",
    "process.mo",
  ]
  .iter()
  .filter_map(|name| dir.join(name).canonicalize().ok())
  .collect()
}

pub(crate) fn format_duration(d: std::time::Duration) -> String {
  let nanos = d.as_nanos();
  if nanos < 1_000 {
    format!("{nanos}ns")
  } else if nanos < 1_000_000 {
    format!("{:.0}µs", d.as_micros())
  } else if nanos < 1_000_000_000 {
    format!("{:.2}ms", d.as_secs_f64() * 1000.0)
  } else {
    format!("{:.2}s", d.as_secs_f64())
  }
}

pub fn default_modules() -> Result<LoadedModules, LoadingError> {
  let prelude = LoadedModules::empty();
  init_module(prelude)
}

pub struct ParsedModule {
  pub decls: Vec<SourceContext<Decl>>,
  pub module_doc: Option<Documentation>,
}

// `inductives`/`defs`/`macro_defs`/`decl_gens`/`infix`/`instances` are all
// `Arc`-wrapped -- these are the fields that actually hold real AST
// (every checked `Def`/`Inductive`/`Instance`/`DeclGenDef`/`Infix`'s full
// `Term` tree), so a plain `#[derive(Clone)]` on this struct used to be a
// genuine deep clone of a module's entire checked body. `Module` gets
// cloned as a side effect of `LoadedModules` being cloned once per
// checked/tested file (see `LoadedModules`'s own doc comment) -- wrapping
// these in `Arc` makes `Module::clone()` itself O(1) (a handful of
// refcount bumps) instead of O(this module's own AST size). `uses`/
// `opens`/`scoped_opens`/`doc`/`path` stay plain -- they hold lightweight
// decl metadata (paths/filters), not full ASTs, and there's no evidence
// (from the `valgrind` profiling that motivated this) that they
// contribute measurably, so they're left alone rather than churned on
// spec. The one live mutator (`add_decl`, REPL-only) uses
// `Arc::make_mut` (copy-on-write); every read path is unaffected since
// `&Arc<Map<K,V>>`/`&Arc<Vec<T>>` deref to `&Map<K,V>`/`&[T]` at every
// existing call site.
#[derive(Clone, Debug, PartialEq)]
pub struct Module {
  path: ModulePath,
  inductives: Arc<Map<ModulePath, SourceContext<Inductive>>>,
  uses: Vec<SourceContext<Use>>,
  opens: Vec<SourceContext<Open>>,
  defs: Arc<Map<ModulePath, SourceContext<Def>>>,
  macro_defs: Arc<Map<ModulePath, SourceContext<Def>>>,
  /// Decl-gen macros (`defmacro name params := decls { ... }`) — kept
  /// alongside `macro_defs` (rather than folded into it, since
  /// `DeclGenDef` isn't a `Def`) so `use`-ing a module makes its decl-gen
  /// macros callable too, not just the file that defines them. Previously
  /// `Decl::DeclGen` was dropped entirely at module-storage time (see the
  /// historical comment in `add_decl`), which meant decl-gen macros only
  /// ever worked within the single file that declared them.
  decl_gens: Arc<Map<ModulePath, SourceContext<DeclGenDef>>>,
  infix: Arc<Map<Operator, SourceContext<Infix>>>,
  instances: Arc<Vec<SourceContext<Instance>>>,
  doc: Option<Documentation>,
  /// `open Module [{filter}] in <decl>` scopes recorded for defs/types/
  /// instances that are otherwise stored normally in the maps above. The
  /// `SourceContext<Decl>` is the (unwrapped) inner declaration this open
  /// applies to, used to look up which def a scoped open covers.
  pub(crate) scoped_opens: Vec<(Open, SourceContext<Decl>)>,
}

/// Bare `use Module` (no braces) is deprecated in favor of explicit
/// `use Module {...}` selection. Scans a file's own `use` declarations
/// (not transitively-loaded dependencies — callers should only run this
/// against the directly-requested top-level file's `Module::get_uses()`,
/// to avoid duplicate warnings for a shared module every dependent file
/// happens to `use`) and returns one warning `Diagnostic` per bare `use`.
pub fn bare_use_warnings(
  uses: &[SourceContext<Use>],
  path: Option<&std::path::PathBuf>,
) -> Vec<Diagnostic> {
  uses
    .iter()
    .filter_map(|ctx| {
      let u = ctx.value();
      if u.filter != UseFilter::Bare {
        return None;
      }
      Some(Diagnostic {
        severity: Severity::Warning,
        message: format!("bare `use {}` without braces is deprecated", u.module_path),
        location: Some(u.source_location.clone()),
        path: path.cloned(),
        suggestions: vec![Suggestion {
          message: format!("use `use {} {{*}}` instead", u.module_path),
        }],
        ..Default::default()
      })
    })
    .collect()
}

/// Bare `open Module` (no braces at all) is deprecated in favor of explicit
/// `open Module {*}` — mirrors `bare_use_warnings`. Note `open Module
/// {name1, name2}` (an `OpenFilter::Only` selection) is not bare and does
/// not warn; only the fully-implicit "no braces" form does.
pub fn bare_open_warnings(
  opens: &[SourceContext<Open>],
  path: Option<&std::path::PathBuf>,
) -> Vec<Diagnostic> {
  opens
    .iter()
    .filter_map(|ctx| {
      let o = ctx.value();
      if o.filter != OpenFilter::All {
        return None;
      }
      Some(Diagnostic {
        severity: Severity::Warning,
        message: format!("bare `open {}` without braces is deprecated", o.module_path),
        location: Some(o.source_location.clone()),
        path: path.cloned(),
        suggestions: vec![Suggestion {
          message: format!("use `open {} {{*}}` instead", o.module_path),
        }],
        ..Default::default()
      })
    })
    .collect()
}

/// `open Module {}` — an explicit but empty name filter — is a hard error,
/// not just a deprecation warning like `bare_open_warnings` above: unlike
/// a bare `open Module`, there's no non-empty spelling to suggest instead,
/// since (per `docs/src/reference.md`'s own "access by path always works"
/// rule) an empty filter imports nothing a plain `use Module {...}` didn't
/// already provide. Scans both plain `Decl::Open` and (recursively, since
/// `decl` can itself be another `ScopedOpen`) `Decl::ScopedOpen`, over the
/// raw parsed decls — called once per file, before `unwrap_scoped_opens`
/// flattens `ScopedOpen` away, from each of `load_module_from_text`/
/// `load_module_from_text_typed`/the recursive dependency loader.
pub fn validate_open_filters(decls: &[SourceContext<Decl>]) -> Result<(), TypeError> {
  fn check_one(
    module_path: &ModulePath,
    filter: &OpenFilter,
    loc: &SourceRange,
  ) -> Result<(), TypeError> {
    match filter {
      OpenFilter::Only(names) if names.is_empty() => Err(TypeError::EmptyOpenFilter {
        module_path: module_path.clone(),
        loc: loc.clone(),
      }),
      _ => Ok(()),
    }
  }
  // `ScopedOpen` carries no `source_location` of its own (unlike `Open`)
  // — `fallback_loc` (the enclosing `SourceContext`'s own location) is
  // the closest thing available to point a diagnostic at, and is what
  // `decl` recurses with for any `ScopedOpen` nested inside it too.
  fn check_decl(decl: &Decl, fallback_loc: &SourceRange) -> Result<(), TypeError> {
    match decl {
      Decl::Open(o) => check_one(&o.module_path, &o.filter, &o.source_location),
      Decl::ScopedOpen {
        module_path,
        filter,
        decl,
        ..
      } => {
        check_one(module_path, filter, fallback_loc)?;
        check_decl(decl, fallback_loc)
      }
      _ => Ok(()),
    }
  }
  for ctx in decls {
    check_decl(ctx.value(), &ctx.loc)?;
  }
  Ok(())
}

/// Walk a `Par` (lambda/pi parameter) for referenced names — its type, and
/// (for explicit `Par::P` params) its default value expression, if any.
fn collect_par_names(par: &Par, names: &mut Set<ModulePath>) {
  match par {
    Par::P(param) => collect_param_names(param, names),
    Par::I { typ, .. } => collect_term_names(typ, names),
  }
}

fn collect_param_names(param: &Param, names: &mut Set<ModulePath>) {
  collect_term_names(&param.typ, names);
  if let Some(default) = &param.default {
    collect_term_names(default, names);
  }
}

fn collect_literal_names(lit: &Literal, names: &mut Set<ModulePath>) {
  match lit {
    Literal::Str { .. }
    | Literal::Char { .. }
    | Literal::Num { .. }
    | Literal::Float { .. }
    | Literal::Foreign(_) => {}
    Literal::Term(t) => collect_term_names(t, names),
    Literal::Match { value, cases } => {
      collect_term_names(value, names);
      for case in cases {
        // The pattern's constructor name is a bare `Identifier` here (not a
        // `Term::Var`) — this is how `open`-imported constructors used only
        // in match arms (never as a call-position reference) get counted.
        names.insert(ModulePath::single(case.name.clone()));
        collect_term_names(&case.value, names);
      }
    }
    Literal::If { value, then, els } => {
      collect_term_names(value, names);
      collect_term_names(then, names);
      collect_term_names(els, names);
    }
    Literal::StructLit { fields, type_name } => {
      for t in fields.values() {
        collect_term_names(t, names);
      }
      if let Some(tn) = type_name {
        collect_term_names(tn, names);
      }
    }
    Literal::StructUpdate { base, fields } => {
      names.insert(ModulePath::single(base.clone()));
      for t in fields.values() {
        collect_term_names(t, names);
      }
    }
  }
}

/// Collect every name referenced as a free variable anywhere in `term`
/// (its own name if it's a `Var`, plus everything nested inside it). Runs
/// on the raw parsed AST — see `collect_referenced_names` for why.
fn collect_term_names(term: &Term, names: &mut Set<ModulePath>) {
  match term {
    Term::Forall { typ, body, .. } => {
      collect_term_names(typ, names);
      collect_term_names(body, names);
    }
    Term::Pi { arg, ret, .. } => {
      collect_term_names(arg, names);
      collect_term_names(ret, names);
    }
    Term::Var { name } => {
      if let Some(p) = name.to_path() {
        names.insert(p);
      }
    }
    Term::Lam { param, body } => {
      collect_par_names(param, names);
      collect_term_names(body, names);
    }
    Term::App { fun, arg } => {
      collect_term_names(fun, names);
      collect_term_names(arg, names);
    }
    Term::Ann { term, typ } => {
      collect_term_names(term, names);
      collect_term_names(typ, names);
    }
    Term::Lit { value } => collect_literal_names(value, names),
    Term::Ntv { native } => {
      for arg in native.args() {
        if let Some(t) = arg {
          collect_term_names(t, names);
        }
      }
    }
    Term::Con(c) => {
      names.insert(c.typ_name.clone());
      for arg in &c.args {
        if let Some(t) = arg {
          collect_term_names(t, names);
        }
      }
    }
    Term::Ctx { term, .. } => collect_term_names(term, names),
    Term::Sort { .. } | Term::Hole => {}
    Term::Quote { term } => collect_term_names(term, names),
  }
}

/// Collect every name referenced anywhere in a module's own declarations —
/// as a free variable (`Term::Var`), a match-pattern constructor
/// (`MatchCase::name`), a type-constraint class, or an infix target.
///
/// Intended to run on the raw parsed AST, before lowering/de-Bruijn-
/// indexing (the same timing as `bare_use_warnings`) — a conservative
/// approximation where a local binding that shadows an imported name
/// makes that import look "used" even where every real reference is
/// shadowed. This can only cause false negatives (misses some genuinely-
/// dead imports), never false positives — the correct bias for both
/// `unused_use_name_warnings` (a spurious warning is worse than a missed
/// one) and the `organize-imports` codemod's minimal-set computation (a
/// superset is safe; a subset that omits an actually-used name would break
/// compilation).
///
/// IMPORTANT: in the real pipeline (`check_one_source`,
/// `organize_imports_for_files`), the `Module` this actually runs on has
/// already been through `load_module_from_text_typed` — i.e. it's the
/// POST-elaboration term tree, not the pristine parse. Elaboration
/// resolves a bare reference like `println` to its *declaring* def's own
/// full name (`IO.println`, since that's how `io.mo` itself wrote it) —
/// which is not necessarily `<use-target-module>.<name>`. Callers matching
/// against this set MUST therefore check by an entry's LAST segment (see
/// `referenced_contains_name`), not just the bare name or
/// `<module>.<name>` qualification, or they'll wrongly conclude an
/// actually-used name is unreferenced. A fully scope-aware, pre-
/// elaboration-only version is future work — deliberately not done here.
pub fn collect_referenced_names(module: &Module) -> Set<ModulePath> {
  let mut names = Set::default();
  for ctx in module.defs() {
    let def = ctx.value();
    collect_term_names(&def.term, &mut names);
    collect_term_names(&def.typ, &mut names);
    for tc in &def.type_constraints {
      names.insert(tc.class().clone());
    }
  }
  for ctx in module.get_macro_defs() {
    let def = ctx.value();
    collect_term_names(&def.term, &mut names);
    collect_term_names(&def.typ, &mut names);
  }
  for ind in module.inductives() {
    collect_term_names(ind.typ(), &mut names);
    for tc in &ind.constraints {
      names.insert(tc.class().clone());
    }
    for cons in ind.constructors() {
      collect_term_names(cons.typ(), &mut names);
      for p in cons.params() {
        collect_param_names(p, &mut names);
      }
    }
    for default in ind.defaults.values() {
      collect_term_names(default, &mut names);
    }
    for tcs in ind.method_constraints.values() {
      for tc in tcs {
        names.insert(tc.class().clone());
      }
    }
  }
  for ctx in module.instances() {
    let inst = ctx.value();
    names.insert(inst.class_name.clone());
    for tc in &inst.constraints {
      names.insert(tc.class().clone());
    }
    for arg in &inst.args {
      collect_term_names(arg, &mut names);
    }
    for def in inst.impls_map.values() {
      collect_term_names(&def.term, &mut names);
      collect_term_names(&def.typ, &mut names);
      for tc in &def.type_constraints {
        names.insert(tc.class().clone());
      }
    }
  }
  for ctx in module.infix() {
    names.insert(ctx.value().name().clone());
  }
  names
}

/// Whether `referenced` (from `collect_referenced_names`) shows evidence
/// that `name` was used, allowing for post-elaboration qualification: a
/// bare match, a qualified match under `context_path` (e.g. `<use-target>.
/// <name>`), OR — the case elaboration actually produces, see
/// `collect_referenced_names`'s doc comment — any entry whose LAST
/// segment is `name`, regardless of its prefix (`IO.println` still counts
/// as evidence `println` was used, even though `IO` isn't `context_path`
/// at all). That last check is deliberately broad: a coincidental same-
/// name def from a genuinely unrelated module would also pass it, but
/// that only ever causes a *safe* over-inclusion (a name listed in a
/// `use`/`open` brace list that turns out not to be strictly needed —
/// harmless), never the unsafe direction (omitting a name that's
/// genuinely needed, which would break compilation).
pub fn referenced_contains_name(
  referenced: &Set<ModulePath>,
  context_path: &ModulePath,
  name: &Identifier,
) -> bool {
  let bare = ModulePath::single(name.clone());
  let qualified = context_path.append(vec![name.clone()]);
  referenced.contains(&bare)
    || referenced.contains(&qualified)
    || referenced.iter().any(|p| p.last() == name)
}

/// Unused names in `use`-filter selections: for every `UseFilter::Items`
/// filter, flags any `UseItem::Name`/`Rename` entry never referenced in
/// `referenced` (checked both bare and fully-qualified) — see
/// `collect_referenced_names` for how `referenced` is built and its
/// conservative-approximation tradeoff. `UseFilter::Bare` (no explicit
/// list) has nothing to flag. Glob items and bare sub-module names are not
/// themselves checked (there's no single name to be "unused"); names
/// nested inside a `SubModule`/`SubModuleRename` filter are checked via the
/// same recursive flattening `UseItem::flatten` does.
pub fn unused_use_name_warnings(
  uses: &[SourceContext<Use>],
  referenced: &Set<ModulePath>,
  path: Option<&std::path::PathBuf>,
) -> Vec<Diagnostic> {
  uses
    .iter()
    .flat_map(|ctx| {
      let u = ctx.value();
      let UseFilter::Items(items) = &u.filter else {
        return Vec::new();
      };
      let mut flat: Map<ModulePath, AllowedNames> = Map::new();
      for item in items {
        for (k, v) in item.flatten(&u.module_path) {
          merge_allowed(&mut flat, k, v);
        }
      }
      flat
        .into_iter()
        .filter_map(|(module_path, allowed)| {
          let AllowedNames::Only(names) = allowed else {
            return None;
          };
          // Only a single-name entry (the common case for a leaf import)
          // can be pinpointed as "this specific name is unused" — report
          // the whole `use` line's location since `UseItem` doesn't carry
          // its own per-item span.
          let unused: Vec<&Identifier> = names
            .iter()
            .filter(|name| !referenced_contains_name(referenced, &module_path, name))
            .collect();
          if unused.is_empty() {
            return None;
          }
          let names_str = unused
            .iter()
            .map(|n| n.as_str())
            .collect::<Vec<_>>()
            .join(", ");
          Some(Diagnostic {
            severity: Severity::Warning,
            message: format!("unused import `{names_str}` from `{module_path}`"),
            location: Some(u.source_location.clone()),
            path: path.cloned(),
            suggestions: vec![Suggestion {
              message: format!("remove `{names_str}` from `use {}`", u.module_path),
            }],
            ..Default::default()
          })
        })
        .collect::<Vec<_>>()
    })
    .collect()
}

/// Whole-*program* "unused def" warning: a `def` that's `Priv`/
/// `PackagePrivate` (not `Pub` — a `pub` def may be consumed by another
/// mote entirely, invisible to this checker), not `#[test]`-attributed
/// (called by the test harness, never referenced by name from any def
/// body), and not named `main` (the entry point, never self-referential),
/// whose own `ModulePath` never shows up as a reference anywhere across
/// EVERY module currently loaded. Unlike `module_warnings`/
/// `collect_referenced_names` (deliberately per-file, since an unused
/// *import* is a property of the one file that wrote it), this genuinely
/// needs the whole corpus: a def used only by a sibling module would be a
/// false "unused" positive if checked one file at a time.
///
/// Matching deliberately does NOT reuse `referenced_contains_name`'s own
/// third, broadest fallback (any referenced path anywhere ending in this
/// identifier) — that one is calibrated for ONE file's typically-small
/// reference set (checking one specific already-known imported name), and
/// applying the same "matches literally anywhere in the whole loaded
/// program" rule across a large multi-hundred-file corpus made it match
/// almost every def by coincidence (confirmed empirically: it suppressed
/// every real warning in this project's own ~100-file corpus). Only two
/// checks survive here: the def's own exact qualified path (a reference
/// written/resolved fully-qualified), and its bare last segment as a
/// single-segment path (a reference resolved to just the local name,
/// e.g. after `open`) — the same two precise forms
/// `referenced_contains_name` itself checks before falling back to its
/// broad third rule.
/// Returns each warning paired with the `ModulePath` of the module it
/// belongs to — `SourceRange`/`Diagnostic::path` is never populated at
/// parse time in this codebase (the file path is threaded explicitly by
/// callers instead, e.g. `module_warnings`'s own `path` parameter), so a
/// caller that wants a real `PathBuf` on each `Diagnostic` (`check_files`
/// does, to fold these into its own per-file `FileCheckResult`s) needs
/// its own `ModulePath -> PathBuf` mapping to attach one — `Module::path`
/// is what identifies WHICH loaded module each returned warning came
/// from.
pub fn unused_def_warnings(loaded: &LoadedModules) -> Vec<(ModulePath, Diagnostic)> {
  let all_modules = loaded.modules();
  let mut referenced: Set<ModulePath> = Set::default();
  for module in &all_modules {
    referenced.extend(collect_referenced_names(module));
  }
  let main_name = id("main");
  all_modules
    .iter()
    .flat_map(|module| {
      module
        .defs()
        .into_iter()
        .filter_map(|ctx| {
          let def = ctx.value();
          // Synthesized typeclass-instance dictionary def (`instance()`,
          // `core/src/term.rs`'s `instance-{class}-{args}` naming
          // convention) — confirmed a real, non-hypothetical false-positive
          // source: an instance is found and applied by the type system's
          // own dictionary-resolution machinery (matching on TYPE, at
          // typecheck/eval time), never through a named `Term::Var`
          // reference a programmer wrote, so `collect_referenced_names`
          // structurally can never see it as "used" even when it's the
          // sole implementation backing every `==`/`show`/etc. call on
          // that type — exempted the same way `main` is (a root the
          // ordinary reachability model doesn't apply to).
          let is_instance_dict = def.name.last().as_str().starts_with("instance-");
          if def.vis == Visibility::Pub
            || def.has_test_attr()
            || def.name.last() == &main_name
            || is_instance_dict
          {
            return None;
          }
          let bare = ModulePath::single(def.name.last().clone());
          let used = referenced.contains(&def.name) || referenced.contains(&bare);
          if used {
            return None;
          }
          Some((
            module.path().clone(),
            Diagnostic {
              severity: Severity::Warning,
              message: format!("unused def `{}`", def.name),
              location: Some(ctx.loc.clone()),
              ..Default::default()
            },
          ))
        })
        .collect::<Vec<_>>()
    })
    .collect()
}

/// All non-fatal, style/deprecation-level warnings for a successfully
/// loaded module, combined: bare `use`, bare `open`, and unused
/// `use`-filter names (`unused_use_name_warnings`). This is the single
/// entry point every warning-surfacing call site (`run`, the test runner,
/// `check_files`/`check_source`, the LSP) should call, so new warning
/// kinds only need wiring in once. Does NOT include `unused_def_warnings`
/// — that one is whole-*program*, not per-module, so it's called
/// separately, once per whole loaded corpus, not once per file — see its
/// own doc comment.
pub fn module_warnings(module: &Module, path: Option<&std::path::PathBuf>) -> Vec<Diagnostic> {
  let mut warnings = bare_use_warnings(module.get_uses(), path);
  warnings.extend(bare_open_warnings(module.get_opens(), path));
  warnings.extend(unused_use_name_warnings(
    module.get_uses(),
    &collect_referenced_names(module),
    path,
  ));
  warnings
}

/// Recursively unwrap `Decl::ScopedOpen` wrappers, recording each one's
/// `Open` + inner declaration into `scoped_opens` and returning the
/// declarations with `ScopedOpen` replaced by their inner decl, so normal
/// decl-kind filtering (by `Decl::Def`, `Decl::Type`, etc.) still applies.
pub(crate) fn unwrap_scoped_opens(
  decls: Vec<SourceContext<Decl>>,
  scoped_opens: &mut Vec<(Open, SourceContext<Decl>)>,
) -> Vec<SourceContext<Decl>> {
  decls
    .into_iter()
    .map(|ctx| unwrap_scoped_open(ctx, scoped_opens))
    .collect()
}

fn unwrap_scoped_open(
  ctx: SourceContext<Decl>,
  scoped_opens: &mut Vec<(Open, SourceContext<Decl>)>,
) -> SourceContext<Decl> {
  match ctx.value {
    Decl::ScopedOpen {
      module_path,
      filter,
      attributes,
      decl,
    } => {
      let open = Open {
        source_location: ctx.loc.clone(),
        module_path,
        filter,
        attributes,
      };
      let inner_ctx = SourceContext {
        loc: ctx.loc,
        doc: ctx.doc,
        value: *decl,
      };
      let inner_ctx = unwrap_scoped_open(inner_ctx, scoped_opens);
      scoped_opens.push((open, inner_ctx.clone()));
      inner_ctx
    }
    other => SourceContext {
      loc: ctx.loc,
      doc: ctx.doc,
      value: other,
    },
  }
}

impl Module {
  pub fn defs(&self) -> Vec<&SourceContext<Def>> {
    self.defs.values().collect()
  }
  pub fn get_macro_defs(&self) -> Vec<&SourceContext<Def>> {
    self.macro_defs.values().collect()
  }
  pub fn macro_defs_map(&self) -> &Map<ModulePath, SourceContext<Def>> {
    &self.macro_defs
  }
  pub fn decl_gens_map(&self) -> &Map<ModulePath, SourceContext<DeclGenDef>> {
    &self.decl_gens
  }
  /// Convert module back to Decls again
  pub fn to_decls(self) -> Vec<SourceContext<Decl>> {
    let inductives = self
      .inductives
      .values()
      .map(|ctx| ctx.clone().map(Decl::Type));
    let instances = self.instances.iter().map(|ctx| ctx.clone().map(Decl::Ins));
    let infix = self
      .infix
      .values()
      .map(|ctx| ctx.with(Decl::Infix(ctx.value().clone())));
    let uses = self.uses.into_iter().map(|ctx| ctx.map(Decl::Use));
    let opens = self.opens.into_iter().map(|ctx| ctx.map(Decl::Open));
    let decl_gens = Arc::unwrap_or_clone(self.decl_gens)
      .into_values()
      .map(|ctx| ctx.map(Decl::DeclGen));
    self
      .defs
      .values()
      .map(|ctx| ctx.clone().map(Decl::Def))
      .chain(
        self
          .macro_defs
          .values()
          .map(|ctx| ctx.clone().map(Decl::DefMacro)),
      )
      .chain(decl_gens)
      .chain(uses)
      .chain(opens)
      .chain(inductives)
      .chain(instances)
      .chain(infix)
      .collect()
  }
  pub fn infix(&self) -> Vec<&SourceContext<Infix>> {
    self.infix.values().collect()
  }
  pub fn classes(&self) -> Vec<&Inductive> {
    self
      .inductives
      .values()
      .map(|ctx| ctx.value())
      .filter(|i| i.variant == InductiveVariant::Class)
      .collect()
  }
  pub fn inductives(&self) -> Vec<&Inductive> {
    self.inductives.values().map(|ctx| ctx.value()).collect()
  }
  pub fn path(&self) -> &ModulePath {
    &self.path
  }
  pub fn get_def(&self, name: &ModulePath) -> Option<&SourceContext<Def>> {
    self.defs.get(name)
  }

  pub fn get_infix(&self, op: &Operator) -> Option<&Infix> {
    self.infix.get(op).map(|ctx| ctx.value())
  }
  pub fn get_uses(&self) -> &Vec<SourceContext<Use>> {
    &self.uses
  }
  pub fn get_opens(&self) -> &Vec<SourceContext<Open>> {
    &self.opens
  }
  pub fn get_pub_uses(&self) -> Vec<&Use> {
    self
      .uses
      .iter()
      .filter_map(|ctx| {
        if ctx.value().public {
          Some(ctx.value())
        } else {
          None
        }
      })
      .collect()
  }

  pub fn add_decl(&mut self, decl: Decl) {
    match decl {
      Decl::ScopedOpen {
        module_path,
        filter,
        attributes,
        decl,
      } => {
        let open = Open {
          source_location: Default::default(),
          module_path,
          filter,
          attributes,
        };
        self
          .scoped_opens
          .push((open, SourceContext::no_ctx((*decl).clone())));
        self.add_decl(*decl);
      }
      Decl::Use(u) => self.uses.push(SourceContext::no_ctx(u)),
      Decl::Open(o) => self.opens.push(SourceContext::no_ctx(o)),
      Decl::Infix(inf) => {
        Arc::make_mut(&mut self.infix).insert(inf.operator.clone(), SourceContext::no_ctx(inf));
      }
      Decl::Def(def) => {
        Arc::make_mut(&mut self.defs).insert(def.name.clone(), SourceContext::no_ctx(def));
      }
      Decl::DefMacro(def) => {
        Arc::make_mut(&mut self.macro_defs).insert(def.name.clone(), SourceContext::no_ctx(def));
      }
      Decl::DeclGen(gd) => {
        Arc::make_mut(&mut self.decl_gens).insert(gd.name.clone(), SourceContext::no_ctx(gd));
      }
      Decl::MacroCall { .. } => {
        panic!("MacroCall should be expanded before add_decl");
      }
      Decl::Generated(inner) => {
        for d in inner {
          self.add_decl(d);
        }
      }
      Decl::Type(ind) => {
        Arc::make_mut(&mut self.inductives).insert(ind.name.clone(), SourceContext::no_ctx(ind));
      }
      Decl::Ins(_ins) => {
        todo!()
        // if let Some(map) = self.instances.get_mut(&ins.class_name) {
        //   let key = ins.to_instance_key(self);
        //   map.insert(, ins);
        // } else {
        //   let class_name = ins.class_name.clone();
        //   let map = Map::from([(ins.to_instance_key(), ins)]);
        //   self.instances.insert(class_name, map);
        // }
      }
    }
  }

  fn get_def_refs<'a>(&'a self, opens: &Vec<&'a Open>, test_mode: bool) -> Vec<DefRef<'a>> {
    let instance_defs: Vec<DefRef> = self
      .instances
      .iter()
      .flat_map(|instance| {
        instance.impls_map.iter().map(|(name, imp)| {
          let name = instance
            .name
            .clone()
            .extend(ModulePath::single(name.clone()));

          DefRef {
            module: &self.path,
            loc: &instance.loc,
            name: name.clone(),
            full_path: name,
            typ: &imp.typ,
            term: &imp.term,
            vis: instance.vis,
          }
        })
      })
      .collect();
    let ind_defs: Vec<DefRef> = self
      .inductives
      .iter()
      .flat_map(|(_, ctx)| {
        let ind = ctx.value();
        if ind.variant == InductiveVariant::Class {
          vec![DefRef {
            name: ind.name.clone(),
            full_path: ind.name.clone(),
            typ: &ind.typ,
            term: &ind.term,
            module: &self.path,
            loc: &ctx.loc,
            vis: ind.vis,
          }]
        } else {
          ind
            .constructors
            .iter()
            .flat_map(|cons| {
              let name = &cons.name;

              let names = name.open(opens);
              names
                .iter()
                .map(|name| DefRef {
                  name: name.clone(),
                  full_path: cons.name.clone(),
                  typ: &cons.typ,
                  term: &cons.term,
                  module: &self.path,
                  loc: &ctx.loc,
                  vis: ind.vis,
                })
                .chain([DefRef {
                  name: name.clone(),
                  full_path: name.clone(),
                  typ: &cons.typ,
                  term: &cons.term,
                  module: &self.path,
                  loc: &ctx.loc,
                  vis: ind.vis,
                }])
                .collect::<Vec<DefRef>>()
            })
            .chain([DefRef {
              name: ind.name.clone(),
              full_path: ind.name.clone(),
              typ: &ind.typ,
              term: &ind.term,
              module: &self.path,
              loc: &ctx.loc,
              vis: ind.vis,
            }])
            .collect()
        }
      })
      .collect();
    self
      .defs
      .iter()
      .filter(|(_, def)| test_mode || !def.value().has_test_attr())
      .flat_map(|(name, def)| {
        let full_name = name.clone();
        let names = name.open(opens);
        names
          .iter()
          .map(|name| DefRef {
            name: name.clone(),
            full_path: full_name.clone(),
            typ: &def.typ,
            term: &def.term,
            module: &self.path,
            loc: &def.loc,
            vis: def.vis,
          })
          .chain([DefRef {
            name: name.clone(),
            full_path: full_name.clone(),
            typ: &def.typ,
            term: &def.term,
            module: &self.path,
            loc: &def.loc,
            vis: def.vis,
          }])
          .collect::<Vec<DefRef>>()
      })
      .chain(instance_defs)
      .chain(ind_defs)
      .collect()
  }

  fn get_class_def_refs(&'_ self, opens: &Vec<&Open>) -> Vec<ClassDefRef<'_>> {
    self
      .classes()
      .iter()
      .flat_map(|class| {
        let cons = class
          .constructors
          .first()
          .expect("At least one constructor of class");
        cons
          .params
          .iter()
          .flat_map(|class_def| {
            let def_name = class.name.clone().extend(class_def.name.clone().to_path());
            let names = def_name.open(opens);
            names
              .into_iter()
              .map(|path| class_def_ref(path, &class_def.name, &class_def.typ, class))
              .chain([class_def_ref(
                def_name,
                &class_def.name,
                &class_def.typ,
                class,
              )])
              .collect::<Vec<ClassDefRef>>()
          })
          .collect::<Vec<ClassDefRef>>()
      })
      .collect()
  }

  pub fn instances(&self) -> &Vec<SourceContext<Instance>> {
    &self.instances
  }
}

pub fn extract_constructors(
  d: &SourceContext<Decl>,
) -> Vec<(ModulePath, SourceContext<InductConstructor>)> {
  match &d.value {
    Decl::Type(Inductive {
      constructors,
      variant: InductiveVariant::Generic,
      ..
    }) => constructors
      .iter()
      .flat_map(|c| {
        let cons_name = c.name().clone();
        let path_cons = d.with(c.clone());
        vec![(cons_name, path_cons)]
      })
      .collect(),
    _ => vec![],
  }
}

/// Merge fold
pub fn merge_push<K, V>(mut map: Map<K, Vec<V>>, (key, value): (K, V)) -> Map<K, Vec<V>>
where
  K: Display + Eq + Ord + Hash + Clone,
{
  if let Some(v) = map.get_mut(&key) {
    v.push(value);
  } else {
    map.insert(key, vec![value]);
  }
  map
}

pub fn merge_detect<K, V>(mut map: Map<K, V>, (k, v): (K, V)) -> Result<Map<K, V>, String>
where
  K: Display + Eq + Ord + Hash + Clone,
{
  let r = map.insert(k.clone(), v);
  match r {
    None => Ok(map),
    Some(_) => Err(format!("duplicate definition in module: {}", k)),
  }
}
fn merge_dup_detect<K, V>(map: Map<K, V>, (k, v): (K, V)) -> Map<K, V>
where
  K: Display + Eq + Ord + Hash + Clone,
{
  match merge_detect(map, (k, v)) {
    Ok(m) => m,
    Err(e) => panic!("{e}"),
  }
}

pub fn names_of_decls(decls: &[SourceContext<Decl>]) -> HashSet<ModulePath> {
  decls
    .iter()
    .map(|ctx| ctx.value().to_ref().clone())
    .collect()
}

/// Create a new module
pub fn module(path: ModulePath, parsed: ParsedModule) -> Module {
  let mut scoped_opens: Vec<(Open, SourceContext<Decl>)> = Vec::new();
  let decls = unwrap_scoped_opens(parsed.decls, &mut scoped_opens);
  let defs = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Def(def) => Some((def.name.clone(), ctx.with(def.clone()))),
      _ => None,
    })
    .fold(Map::new(), merge_dup_detect);
  let macro_defs = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::DefMacro(def) => Some((def.name.clone(), ctx.with(def.clone()))),
      _ => None,
    })
    .fold(Map::new(), merge_dup_detect);
  let decl_gens = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::DeclGen(gd) => Some((gd.name.clone(), ctx.with(gd.clone()))),
      _ => None,
    })
    .fold(Map::new(), merge_dup_detect);
  let inductives = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Type(induct) => {
        let name = induct.name.clone();
        Some((name, ctx.with(induct.clone())))
      }
      _ => None,
    })
    .fold(Map::new(), merge_dup_detect);
  let uses = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Use(u) => Some(ctx.with(u.clone())),
      _ => None,
    })
    .collect();
  let opens = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Open(u) => Some(ctx.with(u.clone())),
      _ => None,
    })
    .collect();
  let infix = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Infix(
        infix @ Infix {
          operator,
          name: _,
          vis: _,
        },
      ) => Some((operator.clone(), ctx.with(infix.clone()))),
      _ => None,
    })
    .fold(Map::new(), merge_dup_detect);
  let instances = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Ins(instance) => Some(ctx.with(instance.clone())),
      _ => None,
    })
    .collect();

  Module {
    instances: Arc::new(instances),
    path,
    defs: Arc::new(defs),
    macro_defs: Arc::new(macro_defs),
    decl_gens: Arc::new(decl_gens),
    inductives: Arc::new(inductives),
    uses,
    opens,
    infix: Arc::new(infix),
    doc: parsed.module_doc,
    scoped_opens,
  }
}
impl Display for Module {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let path = self.path();
    let defs = self
      .defs()
      .iter()
      .enumerate()
      .map(|(i, ctx)| format!("\t{i}. {} : {}", ctx.value().name, ctx.typ))
      .collect::<Vec<String>>()
      .join("\n");
    let uses = self
      .get_uses()
      .iter()
      .map(|ctx| format!("{}", ctx.module_path))
      .collect::<Vec<String>>()
      .join(", ");
    let opens = self
      .get_opens()
      .iter()
      .map(|ctx| format!("{}", ctx.module_path))
      .collect::<Vec<String>>()
      .join(", ");
    let classes = self
      .classes()
      .iter()
      .map(|class| format!("{}", class.name))
      .collect::<Vec<String>>()
      .join(", ");
    let instances = self
      .instances()
      .iter()
      .map(|ins| format!("{}", ins.name))
      .collect::<Vec<String>>()
      .join(", ");
    write!(
      f,
      "{path} :> \n\tuses = {uses}\n\topens = {opens}\n\tdefs =\n{defs}\n\tclasses = {classes}\n\tinstances = {instances}"
    )
  }
}
impl<'a> Display for GlobalScope<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    writeln!(f, "modules:")?;
    for m in self.modules() {
      writeln!(f, "{m}")?;
    }
    writeln!(
      f,
      "inductives: {}",
      self
        .inductives
        .keys()
        .map(|o| format!("{o}"))
        .collect::<Vec<String>>()
        .join(", ")
    )?;
    write!(
      f,
      "defs refs:\n{}\n",
      self
        .def_refs
        .iter()
        .enumerate()
        .map(|(i, (o, r))| format!("\t{i}. {o}: {}", r.typ))
        .collect::<Vec<String>>()
        .join("\n")
    )?;
    write!(
      f,
      "class defs:\n{}\n",
      self
        .class_defs
        .iter()
        .enumerate()
        .map(|(i, (o, r))| format!("\t{i}. {o}: {}", r.typ))
        .collect::<Vec<String>>()
        .join("\n")
    )?;
    write!(
      f,
      "infix:\n{}\n",
      self
        .infix()
        .iter()
        .enumerate()
        .map(|(i, (_, m))| format!("\t{i}. {m}"))
        .collect::<Vec<String>>()
        .join("\n")
    )
  }
}
impl<'a> Display for Scope<'a> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    writeln!(f, "global: {}", self.global())?;
    write!(
      f,
      "locals: {}",
      self
        .locals()
        .iter()
        .map(|(i, l)| format!("{i} : {}", l.typ()))
        .collect::<Vec<String>>()
        .join(", ")
    )
  }
}

/// Check if a ModulePath refers to an IndexedMonad class method (e.g., `IndexedMonad.bind`).
fn is_indexed_monad_method(name: &ModulePath) -> bool {
  let prefix = ModulePath::single(Identifier::new("IndexedMonad".to_string()));
  name.is_prefix(&prefix)
}

/// Convert an IndexedMonad method name to the corresponding Monad method name.
/// e.g., `IndexedMonad.bind` -> `Monad.bind`
fn to_monad_name(name: &ModulePath) -> Option<ModulePath> {
  let prefix = ModulePath::single(Identifier::new("IndexedMonad".to_string()));
  let rest = name.remove_prefix(&prefix)?;
  Some(ModulePath::single(Identifier::new("Monad".to_string())).extend(rest))
}
