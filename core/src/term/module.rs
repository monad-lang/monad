#[cfg(test)]
pub mod test;

use super::*;
use crate::Set;
use crate::eval::native::{NativeFun, load_native_funs};
use crate::eval::r#type::{TypeError, UsageEnv, derive_instance_key, type_check_module_decls};
use crate::term::{Inductive, Instance, InstanceKey, ModulePath, SourceContext, Term};
use crate::{
  parser::parse_file,
  term::{
    Decl, Identifier,
    NameRef::{self},
  },
};
use std::collections::HashSet;
use std::fs::read_to_string;
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
      Generic(s) => write!(f, "{s}"),
      OperatorNotDefined(s) => write!(f, "operator {s} not defined"),
      Type(type_error) => write!(f, "scope type: {type_error}"),
      IdNotFound(identifier) => write!(f, "id {identifier} not found"),
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
pub struct LoadedModules {
  modules: Map<ModulePath, Module>,
  builtins: Builtins,
  native: Map<Identifier, NativeFun>,
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
    let native = load_native_funs();
    LoadedModules {
      modules,
      builtins,
      native,
    }
  }
  pub fn get_module_mut(&mut self, path: &ModulePath) -> Option<&mut Module> {
    self.modules.get_mut(path)
  }
  pub fn get_module(&self, path: &ModulePath) -> Option<&Module> {
    self.modules.get(path)
  }

  pub fn extend(&mut self, ms: LoadedModules) {
    self.modules.extend(ms.modules);
  }
  /// Use type_check_module to add modules
  pub fn add_module(&mut self, module: Module) {
    self.modules.insert(module.path().clone(), module);
  }
  pub fn global<'a>(&'a self, for_module: &'a ModulePath) -> Option<GlobalScope<'a>> {
    GlobalScope::for_module(for_module, self)
  }

  pub fn empty() -> LoadedModules {
    let native = load_native_funs();
    LoadedModules {
      native,
      modules: Map::new(),
      builtins: Builtins::new(),
    }
  }

  pub fn add_modules(&mut self, loaded_modules: Map<ModulePath, Module>) {
    self.modules.extend(loaded_modules);
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
    LoadedScopes::new(self)
  }
}
#[derive(Debug, Clone)]
pub struct Builtins {
  path: ModulePath,
  loc: SourceRange,
  type_0: Term,
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
      type_0: type0(),
      type_map: Map::new(),
      prelude_path: mpt("'prelude"),
    }
  }
  pub fn get_type_u_term(&mut self, universe: u64) -> &Term {
    if self.type_map.contains_key(&universe) {
      self.type_map.insert(universe, type_u(universe));
    }
    self.type_map.get(&universe).unwrap()
  }

  fn get_type_0(&self) -> DefRef<'_> {
    DefRef {
      module: &self.path,
      name: mpt("Type"),
      term: &self.type_0,
      typ: &self.type_0,
      loc: &self.loc, // TODO fix
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
}

impl GlobalScopeData {
  pub fn from_module(module: &Module, loaded: &LoadedModules) -> Self {
    let builtins = &loaded.builtins;

    // Collect opens from current module and prelude
    let mut opens: Vec<&Open> = module.get_opens().iter().map(|ctx| ctx.value()).collect();
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
      if let Some(mo) = loaded.get_module(&use_decl.module_path) {
        visible_modules.insert(mo.path(), mo);
      }
    }

    // Include default implicit modules: prelude, init, io, math, string, number
    let default_names: Vec<ModulePath> = vec![
      builtins.prelude_path.clone(),
      ModulePath::top("init"),
      ModulePath::top("io"),
      ModulePath::top("math"),
      ModulePath::top("string"),
      ModulePath::top("number"),
    ];
    for default_name in &default_names {
      if let Some(mo) = loaded.get_module(default_name) {
        visible_modules.insert(mo.path(), mo);
      }
    }

    // Build def_refs from all visible modules
    let def_refs: Map<ModulePath, (Term, Term, ModulePath)> = visible_modules
      .iter()
      .flat_map(|(_mod_path, modu)| {
        modu
          .get_def_refs(&opens)
          .into_iter()
          .flat_map(|d| {
            // For defs from other modules (not current), add with module prefix
            let is_current = modu.path() == module.path();
            let is_used = module
              .get_uses()
              .iter()
              .any(|u| &u.module_path == modu.path());

            if !is_current && is_used {
              // Used module: add with module prefix
              let prefixed_name = modu.path().clone().extend(d.name.clone());
              vec![
                (
                  d.name.clone(),
                  (d.typ.clone(), d.term.clone(), d.module.clone()),
                ),
                (
                  prefixed_name,
                  (d.typ.clone(), d.term.clone(), d.module.clone()),
                ),
              ]
            } else {
              // Current module or implicit: just use original name
              vec![(
                d.name.clone(),
                (d.typ.clone(), d.term.clone(), d.module.clone()),
              )]
            }
          })
          .collect::<Vec<_>>()
      })
      .chain([(
        mpt("Type"),
        (
          builtins.get_type_0().typ.clone(),
          builtins.get_type_0().term.clone(),
          builtins.get_type_0().module.clone(),
        ),
      )])
      .collect();

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
    }
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
  pub fn new(loaded: &'a LoadedModules) -> Self {
    let mut scopes = Map::new();
    let module_paths: Vec<ModulePath> = loaded.modules.keys().cloned().collect();
    for path in module_paths {
      if let Some(module) = loaded.get_module(&path) {
        let data = GlobalScopeData::from_module(module, loaded);
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
  class_defs: Map<ModulePath, ClassDefRef<'a>>,
  instances: Map<&'a ModulePath, Vec<&'a Instance>>,
  inductives: Map<&'a ModulePath, &'a Inductive>,
  classes: Map<&'a ModulePath, &'a Inductive>,
  infixes: Map<&'a Operator, &'a Infix>,
  all_scopes: Map<&'a ModulePath, &'a GlobalScopeData>,
}

impl<'a> GlobalScope<'a> {
  pub fn from_decls(
    path: &'a ModulePath,
    decls: &'a Vec<SourceContext<Decl>>,
    loaded: &'a LoadedModules,
  ) -> GlobalScope<'a> {
    let uses: Vec<&Use> = decls
      .iter()
      .filter_map(|ctx| match ctx.value() {
        Decl::Use(u) => Some(u),
        _ => None,
      })
      .collect();
    let mut opens: Vec<&Open> = decls
      .iter()
      .filter_map(|ctx| match ctx.value() {
        Decl::Open(u) => Some(u),
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
    let default_implicit = vec![
      ModulePath::top("init"),
      ModulePath::top("io"),
      ModulePath::top("math"),
      ModulePath::top("string"),
      ModulePath::top("number"),
    ];
    for name in default_implicit {
      if let Some(mo) = loaded.get_module(&name) {
        implicit.insert(mo.path(), mo);
      }
    }
    let mut modules = Self::load_modules(&uses, loaded);
    modules.extend(implicit);

    let empty_all_scopes: Map<&ModulePath, &GlobalScopeData> = Map::new();
    let mut global =
      GlobalScope::from_modules(path, modules, opens.clone(), loaded, empty_all_scopes);
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
    let mut opens: Vec<&Open> = current_module
      .get_opens()
      .iter()
      .map(|ctx| ctx.value())
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
      .collect();

    let mut modules: Map<&ModulePath, &Module> = Map::new();

    // Always include current module
    modules.insert(path, current_module);

    // Include explicitly used modules
    for use_decl in uses {
      if let Some(mo) = loaded.get_module(&use_decl.module_path) {
        modules.insert(&use_decl.module_path, mo);
      }
    }

    // Include default implicit modules: prelude, init, io, math, string, number
    let default_names: Vec<ModulePath> = vec![
      builtins.prelude_path.clone(),
      ModulePath::top("init"),
      ModulePath::top("io"),
      ModulePath::top("math"),
      ModulePath::top("string"),
      ModulePath::top("number"),
    ];
    for default_name in default_names {
      if let Some(mo) = loaded.get_module(&default_name) {
        let mo_path = mo.path();
        modules.insert(mo_path, mo);
      }
    }

    let empty_all_scopes: Map<&ModulePath, &GlobalScopeData> = Map::new();
    Some(GlobalScope::from_modules(
      path,
      modules,
      opens,
      loaded,
      empty_all_scopes,
    ))
  }
  fn from_modules(
    current_path: &'a ModulePath,
    modules: Map<&'a ModulePath, &'a Module>,
    opens: Vec<&'a Open>,
    loaded: &'a LoadedModules,
    all_scopes: Map<&'a ModulePath, &'a GlobalScopeData>,
  ) -> Self {
    let builtins = &loaded.builtins;
    let def_refs = modules
      .iter()
      .flat_map(|(_path, module)| module.get_def_refs(&opens).into_iter())
      .chain([builtins.get_type_0()])
      .map(|d| (d.name.clone(), d))
      .collect();
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
            typ,
            term,
            module,
            loc: default_source_range(),
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

  pub fn get_native(&self, native_name: &Identifier) -> Option<&NativeFun> {
    self.loaded.native.get(native_name)
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
    self.def_refs.keys().collect()
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
    let class = &self.find_inductive(&ins_key.class)?;
    let instance = self.instances.get(&ins_key.class).and_then(|instances| {
      instances
        .iter()
        .find(|ins| ins.matches(ins_key, class, self))
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
  pub fn find_any_ref(&'_ self, name: &ModulePath, typ: &Term) -> Result<VarRef<'_>, ScopeError> {
    if let Some(def) = self.find_ref(name) {
      Ok(def.to_var_ref())
    } else if let Some(def) = self.find_class_def(name) {
      let key = derive_instance_key(def, typ)?;
      let instance = self
        .find_instance(&key)
        .ok_or(ScopeError::InstanceNotFound(key))?;
      let ins_def_name = instance.name.clone().extend(def.name.clone().to_path());
      let ins_def = self
        .find_ref(&ins_def_name)
        .ok_or(ScopeError::PathNotFound(ins_def_name))?;
      Ok(ins_def.to_update_ref())
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

  fn load_decl(
    &mut self,
    ctx: &'a SourceContext<Decl>,
    opens: &Vec<&'a Open>,
    module: &'a ModulePath,
  ) {
    match ctx.value() {
      Decl::Def(def) | Decl::DefMacro(def) => {
        let name = &def.name;
        let names = name.open(opens);
        let def_refs: Map<ModulePath, DefRef> = names
          .iter()
          .map(|name| DefRef {
            name: name.clone(),
            typ: &def.typ,
            term: &def.term,
            module,
            loc: &ctx.loc,
          })
          .chain([DefRef {
            name: name.clone(),
            typ: &def.typ,
            term: &def.term,
            module,
            loc: &ctx.loc,
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
                typ: &cons.typ,
                term: &cons.term,
                module,
                loc: &ctx.loc,
              })
              .chain([DefRef {
                name: name.clone(),
                typ: &cons.typ,
                term: &cons.term,
                module,
                loc: &ctx.loc,
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
            typ: &ind.typ,
            term: &ind.term,
            module,
            loc: &ctx.loc,
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
              name: full_name,
              typ: &imp.typ,
              term: &imp.term,
              module,
              loc: &ctx.loc,
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
    usage_env: UsageEnv,
  },
  Sub {
    local: LocalVar<'a>,
    parent: Box<Scope<'a>>,
    usage_env: UsageEnv,
  },
}

impl<'a> Scope<'a> {
  pub fn new(global: &'a GlobalScope<'a>) -> Scope<'a> {
    Scope::Top {
      global,
      usage_env: UsageEnv::new(),
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
  /// Extract term of NameRef
  pub fn resolve_name(&self, nref: &NameRef) -> Result<&Term, ScopeError> {
    let global = self.global();
    if let Some(name) = nref.clone().to_path() {
      if let Some(def) = global.find_ref(&name) {
        Ok(def.term)
      } else if let Some(class_def) = global.find_class_def(&name) {
        Ok(class_def.typ())
      } else {
        Err(ScopeError::PathNotFound(name))
      }
    } else if let NameRef::Op(op) = nref {
      let infix = global.find_infix(op)?;
      if let Some(def) = global.find_ref(&infix.name) {
        Ok(def.term)
      } else if let Some(class_def) = global.find_class_def(&infix.name) {
        Ok(class_def.typ())
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
    match param {
      Par::P(param) => {
        usage_env.register(param.name.clone(), mult.clone());
        Scope::Sub {
          local: local_var(&param.name, param.typ.as_ref()),
          parent: Box::new(self.clone()),
          usage_env,
        }
      }
      Par::I { typ, .. } => {
        // Anonymous implicit param - no name to register
        Scope::Sub {
          local: local_index_var(typ.as_ref()),
          parent: Box::new(self.clone()),
          usage_env,
        }
      }
    }
  }
  pub fn with_local_var(&self, name: &'a Identifier, typ: &'a Term) -> Scope<'a> {
    Scope::Sub {
      local: local_var(name, typ),
      parent: Box::new(self.clone()),
      usage_env: self.usage_env().clone(),
    }
  }
  pub fn with_forall(&self, name: &'a Identifier, typ: &'a Term) -> Scope<'a> {
    Scope::Sub {
      local: local_forall(name, typ),
      parent: Box::new(self.clone()),
      usage_env: self.usage_env().clone(),
    }
  }
  pub fn with_local_index_var(&self, typ: &'a Term) -> Scope<'a> {
    Scope::Sub {
      local: local_index_var(typ),
      parent: Box::new(self.clone()),
      usage_env: self.usage_env().clone(),
    }
  }
  pub fn with_type_owned(&self, name: &'a Identifier, typ: Term) -> Scope<'a> {
    Scope::Sub {
      local: local_var_owned(name, typ),
      parent: Box::new(self.clone()),
      usage_env: self.usage_env().clone(),
    }
  }

  pub fn global(&self) -> &GlobalScope<'a> {
    match self {
      Scope::Top { global, .. } => global,
      Scope::Sub {
        local: _, parent, ..
      } => parent.global(),
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
) -> Result<LoadedModules, LoadingError> {
  let mut uses = decls.iter().filter_map(|ctx| match ctx.value() {
    Decl::Use(u) => Some(u),
    _ => None,
  });
  let loaded = uses.try_fold(
    loaded,
    |loaded, use_| -> Result<LoadedModules, LoadingError> {
      let loaded = if loaded.get_module(&use_.module_path).is_none() {
        load_module_files(&use_.module_path, loaded)?
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
  let decls = load_decls(path)?;
  let mut loaded = load_decl_uses_modules(&decls, loaded)?;
  let decls = type_check_module_decls(path, decls, &loaded)?;
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

pub fn load_decls(path: &ModulePath) -> Result<Vec<SourceContext<Decl>>, String> {
  let text = read_to_string(path.to_file_path()).map_err(|e| e.to_string())?;
  load_decls_from_text(&text)
}

pub fn load_decls_from_text(text: &str) -> Result<Vec<SourceContext<Decl>>, String> {
  let parsed = parse_file(text).map_err(|e| format!("{e}"))?;
  Ok(parsed.decls)
}

pub fn load_module_from_text(
  text: &str,
  path: ModulePath,
  loaded: &mut LoadedModules,
) -> Result<(), LoadingError> {
  let init_decls =
    load_decls_from_text(text).map_err(|e| format!("parse error for {}: {e}", path))?;
  let init_decls = type_check_module_decls(&path, init_decls, loaded)?;
  loaded.add_module(module(
    path,
    ParsedModule {
      decls: init_decls,
      module_doc: None,
    },
  ));
  Ok(())
}

pub fn init_module(mut loaded: LoadedModules) -> Result<LoadedModules, LoadingError> {
  let prelude_path = ModulePath::top("'prelude");
  let io_path = ModulePath::top("io");
  let init_path = ModulePath::top("init");
  let math_path = ModulePath::top("math");
  let string_path = ModulePath::top("string");
  let number_path = ModulePath::top("number");

  let prelude_text = include_str!("../../../init/prelude.mo");
  let io_text = include_str!("../../../init/io.mo");
  let math_text = include_str!("../../../init/math.mo");
  let init_text = include_str!("../../../init/init.mo");
  let string_text = include_str!("../../../init/string.mo");
  let number_text = include_str!("../../../init/number.mo");

  load_module_from_text(prelude_text, prelude_path, &mut loaded)?;
  load_module_from_text(io_text, io_path, &mut loaded)?;
  load_module_from_text(number_text, number_path, &mut loaded)?;
  load_module_from_text(math_text, math_path, &mut loaded)?;
  load_module_from_text(init_text, init_path, &mut loaded)?;
  load_module_from_text(string_text, string_path, &mut loaded)?;

  Ok(loaded)
}

pub fn default_modules() -> Result<LoadedModules, LoadingError> {
  let prelude = LoadedModules::empty();
  init_module(prelude)
}

pub struct ParsedModule {
  pub decls: Vec<SourceContext<Decl>>,
  pub module_doc: Option<Documentation>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Module {
  path: ModulePath,
  inductives: Map<ModulePath, SourceContext<Inductive>>,
  uses: Vec<SourceContext<Use>>,
  opens: Vec<SourceContext<Open>>,
  defs: Map<ModulePath, SourceContext<Def>>,
  macro_defs: Map<ModulePath, SourceContext<Def>>,
  infix: Map<Operator, SourceContext<Infix>>,
  instances: Vec<SourceContext<Instance>>,
  doc: Option<Documentation>,
}

impl Module {
  pub fn defs(&self) -> Vec<&SourceContext<Def>> {
    self.defs.values().collect()
  }
  pub fn get_macro_defs(&self) -> Vec<&SourceContext<Def>> {
    self.macro_defs.values().collect()
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

  pub fn add_decl(&mut self, decl: Decl) {
    match decl {
      Decl::Use(u) => self.uses.push(SourceContext::no_ctx(u)),
      Decl::Open(o) => self.opens.push(SourceContext::no_ctx(o)),
      Decl::Infix(inf) => {
        self
          .infix
          .insert(inf.operator.clone(), SourceContext::no_ctx(inf));
      }
      Decl::Def(def) => {
        self
          .defs
          .insert(def.name.clone(), SourceContext::no_ctx(def));
      }
      Decl::DefMacro(def) => {
        self
          .macro_defs
          .insert(def.name.clone(), SourceContext::no_ctx(def));
      }
      Decl::Type(ind) => {
        self
          .inductives
          .insert(ind.name.clone(), SourceContext::no_ctx(ind));
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

  fn get_def_refs<'a>(&'a self, opens: &Vec<&'a Open>) -> Vec<DefRef<'a>> {
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
            name,
            typ: &imp.typ,
            term: &imp.term,
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
            typ: &ind.typ,
            term: &ind.term,
            module: &self.path,
            loc: &ctx.loc,
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
                  typ: &cons.typ,
                  term: &cons.term,
                  module: &self.path,
                  loc: &ctx.loc,
                })
                .chain([DefRef {
                  name: name.clone(),
                  typ: &cons.typ,
                  term: &cons.term,
                  module: &self.path,
                  loc: &ctx.loc,
                }])
                .collect::<Vec<DefRef>>()
            })
            .chain([DefRef {
              name: ind.name.clone(),
              typ: &ind.typ,
              term: &ind.term,
              module: &self.path,
              loc: &ctx.loc,
            }])
            .collect()
        }
      })
      .collect();
    self
      .defs
      .iter()
      .flat_map(|(name, def)| {
        let names = name.open(opens);
        names
          .iter()
          .map(|name| DefRef {
            name: name.clone(),
            typ: &def.typ,
            term: &def.term,
            module: &self.path,
            loc: &def.loc,
          })
          .chain([DefRef {
            name: name.clone(),
            typ: &def.typ,
            term: &def.term,
            module: &self.path,
            loc: &def.loc,
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

pub fn merge_detect<K, V>(mut map: Map<K, V>, (k, v): (K, V)) -> Map<K, V>
where
  K: Display + Eq + Ord + Hash + Clone,
{
  let r = map.insert(k.clone(), v);
  if r.is_some() {
    eprintln!("duplicate key {}", k);
  }
  map
}

pub fn names_of_decls(decls: &[SourceContext<Decl>]) -> HashSet<ModulePath> {
  decls
    .iter()
    .map(|ctx| ctx.value().to_ref().clone())
    .collect()
}

/// Create a new module
pub fn module(path: ModulePath, parsed: ParsedModule) -> Module {
  let decls = parsed.decls;
  let defs = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Def(def) => Some((def.name.clone(), ctx.with(def.clone()))),
      _ => None,
    })
    .fold(Map::new(), merge_detect);
  let macro_defs = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::DefMacro(def) => Some((def.name.clone(), ctx.with(def.clone()))),
      _ => None,
    })
    .fold(Map::new(), merge_detect);
  let inductives = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Type(induct) => {
        let name = induct.name.clone();
        Some((name, ctx.with(induct.clone())))
      }
      _ => None,
    })
    .fold(Map::new(), merge_detect);
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
      Decl::Infix(infix @ Infix { operator, name: _ }) => {
        Some((operator.clone(), ctx.with(infix.clone())))
      }
      _ => None,
    })
    .fold(Map::new(), merge_detect);
  let instances = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Ins(instance) => Some(ctx.with(instance.clone())),
      _ => None,
    })
    .collect();

  Module {
    instances,
    path,
    defs,
    macro_defs,
    inductives,
    uses,
    opens,
    infix,
    doc: parsed.module_doc,
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
