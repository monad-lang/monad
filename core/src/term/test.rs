use crate::eval::r#type::{FreeVar, FreeVars};
use crate::term::module::Module;

use super::*;
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;

pub trait Similar<O = Self> {
  fn similar(&self, other: &O) -> bool;
}
impl<K, V> Similar for HashMap<K, V>
where
  V: Similar,
  K: Eq + Hash,
{
  fn similar(&self, other: &Self) -> bool {
    self.len() == other.len()
      && self
        .iter()
        .all(|(i, d)| other.get(i).is_some_and(|od| od.similar(d)))
  }
}
impl<K, V> Similar for Map<K, V>
where
  V: Similar,
  K: Ord + Eq + Hash,
{
  fn similar(&self, other: &Self) -> bool {
    self.len() == other.len()
      && self
        .iter()
        .all(|(i, d)| other.get(i).is_some_and(|od| od.similar(d)))
  }
}

impl<T: Similar> Similar for Vec<T> {
  fn similar(&self, other: &Self) -> bool {
    self.iter().zip(other.iter()).all(|(a, b)| a.similar(b))
  }
}
impl<T: Similar> Similar for Box<T> {
  fn similar(&self, other: &Box<T>) -> bool {
    (**self).similar(&**other)
  }
}
impl<T: Similar> Similar<T> for Box<T> {
  fn similar(&self, other: &T) -> bool {
    (**self).similar(other)
  }
}
impl<T: Similar, E> Similar for Result<T, E> {
  fn similar(&self, other: &Self) -> bool {
    match (self, other) {
      (Ok(s), Ok(o)) => s.similar(o),
      _ => false,
    }
  }
}
impl<'a> Similar for FreeVar<'a> {
  fn similar(&self, other: &Self) -> bool {
    use FreeVar::*;
    match (self, other) {
      (Unknown { typ: t1 }, Unknown { typ: t2 }) => t1.similar(t2),
      (Detected { typ: ty1, term: t1 }, Detected { typ: ty2, term: t2 }) => {
        ty1.similar(ty2) && t1.similar(t2)
      }
      _ => false,
    }
  }
}

impl<'a> Similar for FreeVars<'a> {
  fn similar(&self, other: &Self) -> bool {
    self.free_vars().similar(other.free_vars()) && self.keep_vars().similar(other.keep_vars())
  }
}

impl Similar for Identifier {
  fn similar(&self, other: &Identifier) -> bool {
    self == other
  }
}

impl Similar for Param {
  fn similar(&self, other: &Param) -> bool {
    self.name == other.name && self.typ.similar(&other.typ)
  }
}
impl Similar for Par {
  fn similar(&self, other: &Par) -> bool {
    match (self, other) {
      (Par::P(param), Par::P(o_param)) => param.similar(o_param),
      (Par::I { typ: t1, .. }, Par::I { typ: t2, .. }) => t1.similar(t2),
      _ => false,
    }
  }
}

impl Similar for TypeConstraint {
  fn similar(&self, other: &TypeConstraint) -> bool {
    self == other
  }
}
impl Similar for ClassDef {
  fn similar(&self, other: &ClassDef) -> bool {
    self.name == other.name
      && self.typ.similar(&other.typ)
      && self.default.similar(&other.default)
      && self.constraints.similar(&other.constraints)
      && self.doc == other.doc
      && self.attributes == other.attributes
  }
}
impl Similar for Infix {
  fn similar(&self, other: &Infix) -> bool {
    self.name == other.name && self.operator == other.operator
  }
}

impl Similar for Inductive {
  fn similar(&self, other: &Inductive) -> bool {
    self.name == other.name
      && self.variant == other.variant
      && self.typ.similar(&other.typ)
      && self.constraints.similar(&other.constraints)
      && self.params.similar(&other.params)
      && self.constructors.similar(&other.constructors)
      && self.attributes == other.attributes
  }
}
impl Similar for InductConstructor {
  fn similar(&self, other: &InductConstructor) -> bool {
    self.name == other.name && self.typ.similar(&other.typ) && self.params.similar(&other.params)
  }
}

impl Similar for StructField {
  fn similar(&self, other: &StructField) -> bool {
    self.name == other.name
      && self.typ.similar(&other.typ)
      && self.default_value.similar(&other.default_value)
  }
}

impl<T: Similar> Similar for &T {
  fn similar(&self, other: &&T) -> bool {
    (**self).similar(other)
  }
}
impl<T: Similar> Similar for Arc<T> {
  fn similar(&self, other: &Arc<T>) -> bool {
    (**self).similar(other)
  }
}
impl<T: Similar> Similar<Arc<T>> for T {
  fn similar(&self, other: &Arc<T>) -> bool {
    self.similar(&**other)
  }
}
impl<T: Similar> Similar for Option<T> {
  fn similar(&self, other: &Option<T>) -> bool {
    match (self, other) {
      (Some(s), Some(o)) => s.similar(o),
      (None, None) => true,
      _ => false,
    }
  }
}
#[macro_export]
macro_rules! similar {
  ($a:expr,$b:expr $(,)?) => {
    let a = $a;
    let b = $b;
    if !crate::term::test::Similar::similar(&a, &b) {
      pretty_assertions::assert_eq!(a, b)
    }
  };
}

impl Similar for MatchCase {
  fn similar(&self, other: &Self) -> bool {
    self.name == other.name
      && self.args.similar(&other.args)
      && (*self.value).similar(&*other.value)
  }
}

impl Similar for Literal {
  fn similar(&self, other: &Self) -> bool {
    use Literal::{If, Match, StructLit, StructUpdate};
    match (self, other) {
      (Literal::Term(t1), Literal::Term(t2)) => t1.similar(t2),
      (
        Match {
          value: v1,
          cases: c1,
        },
        Match {
          value: v2,
          cases: c2,
        },
      ) => (*v1).similar(&**v2) && c1.iter().zip(c2).all(|(a, b)| a.similar(b)),
      (
        If {
          value: v1,
          then: t1,
          els: e1,
        },
        If {
          value: v2,
          then: t2,
          els: e2,
        },
      ) => (*v1).similar(&**v2) && (*t1).similar(&**t2) && (*e1).similar(&**e2),
      (
        StructLit {
          fields: f1,
          type_name: t1,
        },
        StructLit {
          fields: f2,
          type_name: t2,
        },
      ) => {
        f1.len() == f2.len()
          && f1
            .iter()
            .all(|(k, v)| f2.get(k).map(|v2| v.similar(v2)).unwrap_or(false))
          && match (t1, t2) {
            (None, None) => true,
            (Some(a), Some(b)) => a.similar(b),
            _ => false,
          }
      }
      (
        StructUpdate {
          base: b1,
          fields: f1,
        },
        StructUpdate {
          base: b2,
          fields: f2,
        },
      ) => {
        b1 == b2
          && f1.len() == f2.len()
          && f1
            .iter()
            .all(|(k, v): (&Identifier, &Term)| f2.get(k).map(|v2| v.similar(v2)).unwrap_or(false))
      }
      _ => self == other,
    }
  }
}

impl Similar for Term {
  fn similar(&self, other: &Self) -> bool {
    use Term::{Ctx, Forall, Lam, Lit, Pi, Var};
    match (self, other) {
      (Ctx { term, .. }, Ctx { term: o_term, .. }) => (*term).similar(&**o_term),
      (Ctx { term, .. }, _) => (*term).similar(other),
      (_, Ctx { term, .. }) => (*other).similar(&**term),
      (
        Lam {
          param: p1,
          body: b1,
        },
        Lam {
          param: p2,
          body: b2,
        },
      ) => p1.similar(p2) && (*b1).similar(&**b2),
      (Term::App { fun: f1, arg: a1 }, Term::App { fun: f2, arg: a2 }) => {
        (*f1).similar(&**f2) && (*a1).similar(&**a2)
      }
      (Lit { value: v1 }, Lit { value: v2 }) => v1.similar(v2),
      (
        Pi {
          arg: a1,
          ret: r1,
          arg_name: n1,
          mult: m1,
        },
        Pi {
          arg: a2,
          ret: r2,
          arg_name: n2,
          mult: m2,
        },
      ) => (*a1).similar(&**a2) && (*r1).similar(&**r2) && n1 == n2 && m1 == m2,
      (Var { name: n1 }, Var { name: n2 }) => n1 == n2,
      (
        Forall {
          name: n1,
          typ: t1,
          body: b1,
        },
        Forall {
          name: n2,
          typ: t2,
          body: b2,
        },
      ) => n1 == n2 && t1.similar(t2) && b1.similar(b2),
      (
        Var {
          name: NameRef::Id(i),
        },
        Sort { level: _ },
      ) if i.as_str() == "Type" || i.as_str() == "Prop" || i.as_str() == "Sort" => true,
      (
        Sort { level: _ },
        Var {
          name: NameRef::Id(i),
        },
      ) if i.as_str() == "Type" || i.as_str() == "Prop" || i.as_str() == "Sort" => true,
      (Term::Quote { term: t1 }, Term::Quote { term: t2 }) => t1.similar(t2),
      _ => self == other,
    }
  }
}
impl<T: Similar> Similar for SourceContext<T> {
  fn similar(&self, other: &Self) -> bool {
    self.value.similar(&other.value)
  }
}

impl<T: Similar> Similar<T> for SourceContext<T> {
  fn similar(&self, other: &T) -> bool {
    other.similar(&self.value)
  }
}

impl Similar for Instance {
  fn similar(&self, other: &Self) -> bool {
    self.class_name == other.class_name
      && self.constraints.similar(&other.constraints)
      && self.args.similar(&other.args)
      && self.impls_map.similar(&other.impls_map)
      && self.attributes == other.attributes
  }
}

impl Similar for Def {
  fn similar(&self, other: &Self) -> bool {
    self.name == other.name
      && self.typ.similar(&other.typ)
      && self.term.similar(&other.term)
      && self.type_constraints.similar(&other.type_constraints)
      && self.attributes == other.attributes
  }
}
impl Similar for Use {
  fn similar(&self, other: &Self) -> bool {
    self.module_path == other.module_path
      && self.filter == other.filter
      && self.public == other.public
      && self.attributes == other.attributes
  }
}
impl Similar for Open {
  fn similar(&self, other: &Self) -> bool {
    self.module_path == other.module_path
      && self.filter == other.filter
      && self.attributes == other.attributes
  }
}
impl Similar for Decl {
  fn similar(&self, other: &Self) -> bool {
    match (self, other) {
      (Decl::Def(def), Decl::Def(odef)) => def.similar(odef),
      (Decl::DefMacro(def), Decl::DefMacro(odef)) => def.similar(odef),
      (Decl::Type(inductive), Decl::Type(o_ind)) => inductive.similar(o_ind),
      (Decl::Use(u1), Decl::Use(u2)) => u1.similar(u2),
      (Decl::Open(o1), Decl::Open(o2)) => o1.similar(o2),
      (Decl::Infix(i1), Decl::Infix(i2)) => i1.similar(i2),
      (Decl::Ins(i1), Decl::Ins(i2)) => i1.similar(i2),
      _ => self == other,
    }
  }
}

impl Similar for Module {
  fn similar(&self, other: &Self) -> bool {
    self
      .defs()
      .into_iter()
      .collect::<Vec<_>>()
      .similar(&other.defs().into_iter().collect::<Vec<_>>())
      && self.inductives().similar(&other.inductives())
  }
}

pub fn decl_use(name_path: Vec<&str>) -> Decl {
  let ids = name_path.iter().map(|s| id(s)).collect();
  Decl::Use(Use {
    source_location: Default::default(),
    module_path: ModulePath::new(ids),
    filter: UseFilter::All,
    public: false,
    attributes: vec![],
  })
}

pub fn decl_open(name_path: Vec<&str>) -> Decl {
  let ids = name_path.iter().map(|s| id(s)).collect();
  Decl::Open(Open {
    source_location: Default::default(),
    module_path: ModulePath::new(ids),
    filter: OpenFilter::All,
    attributes: vec![],
  })
}

pub fn decl_inductive(
  name: ModulePath,
  constraints: Vec<TypeConstraint>,
  params: Vec<Param>,
  typ: Term,
  constructors: Vec<InductConstructor>,
) -> Decl {
  Decl::Type(inductive(
    name,
    constraints,
    params,
    typ,
    constructors,
    vec![],
  ))
}

pub fn decl_inductive_with_doc(
  name: ModulePath,
  constraints: Vec<TypeConstraint>,
  params: Vec<Param>,
  typ: Term,
  constructors: Vec<InductConstructor>,
  _doc: Option<Documentation>,
) -> Decl {
  Decl::Type(inductive(
    name,
    constraints,
    params,
    typ,
    constructors,
    vec![],
  ))
}

pub fn decl_infix(operator: Operator, name: ModulePath) -> Decl {
  Decl::Infix(Infix { operator, name })
}

pub fn decl_def(name: ModulePath, type_cons: Vec<TypeConstraint>, typ: Term, term: Term) -> Decl {
  Decl::Def(def(name, type_cons, typ, term, vec![]))
}

pub fn defs_class(
  name: ModulePath,
  constraints: Vec<TypeConstraint>,
  args: Vec<Param>,
  funs: Vec<ClassDef>,
) -> Decl {
  Decl::Type(class(name, constraints, args, funs, vec![]))
}

pub fn defs_class_with_doc(
  name: ModulePath,
  constraints: Vec<TypeConstraint>,
  args: Vec<Param>,
  funs: Vec<ClassDef>,
  _doc: Option<Documentation>,
) -> Decl {
  Decl::Type(class(name, constraints, args, funs, vec![]))
}

#[test]
fn term_similar() {
  let loc: SourceRange = Default::default();
  let module: ModuleContext = Default::default();
  let a = app(
    ctx(var("a"), loc.clone(), module.clone()),
    ctx(var("b"), loc.clone(), module.clone()),
  );
  let b = app(var("a"), var("b"));
  similar!(b, a);
  let a = app(
    ctx(var("a"), loc.clone(), module.clone()),
    ctx(var("b"), loc.clone(), module.clone()),
  );
  let b = app(var("a"), var("b"));
  similar!(b, a);
}

#[test]
fn test_module_path_remove_prefix() {
  let p = mp(vec!["a", "b", "cfun"]);

  assert!(p.is_prefix(&mp(vec!["a", "b"])));
  assert!(!p.is_prefix(&mp(vec!["a", "b", "cfun"])));
  assert_eq!(p.remove_prefix(&mp(vec!["a", "b"])), Some(mp(vec!["cfun"])));
}

#[test]
fn test_module_cycle_detection_direct() {
  use crate::empty_set;
  use crate::term::module::{LoadedModules, load_module_files_inner};

  let path = ModulePath::top("self_cycle");
  let loaded = LoadedModules::empty();
  let mut in_progress: crate::Set<ModulePath> = empty_set();

  in_progress.insert(path.clone());
  let result = load_module_files_inner(&path, loaded, &mut in_progress);
  assert!(result.is_err());
  let err = result.unwrap_err().to_string();
  assert!(err.contains("cycle"), "Expected cycle error, got: {err}");
}

#[test]
fn test_module_cycle_detection_indirect() {
  use crate::empty_set;
  use crate::term::module::{LoadedModules, load_module_files_inner};

  let path_a = ModulePath::top("cycle_a");
  let path_b = ModulePath::top("cycle_b");
  let loaded = LoadedModules::empty();
  let mut in_progress: crate::Set<ModulePath> = empty_set();

  in_progress.insert(path_a.clone());
  in_progress.insert(path_b.clone());
  let result = load_module_files_inner(&path_a, loaded, &mut in_progress);
  assert!(result.is_err());
  let err = result.unwrap_err().to_string();
  assert!(err.contains("cycle"), "Expected cycle error, got: {err}");
}

#[test]
fn test_no_cycle_detection_normal() {
  use crate::empty_set;
  use crate::term::module::{LoadedModules, load_module_files_inner};

  let path = ModulePath::top("normal_module");
  let loaded = LoadedModules::empty();
  let mut in_progress: crate::Set<ModulePath> = empty_set();

  let result = load_module_files_inner(&path, loaded, &mut in_progress);
  assert!(in_progress.is_empty());
  assert!(result.is_err());
  let err = result.unwrap_err().to_string();
  assert!(
    !err.contains("cycle"),
    "Expected no cycle error, got: {err}"
  );
}

#[test]
fn test_merge_detect_accepts_unique() {
  use crate::Map;
  use crate::term::module::merge_detect;

  let mut map: Map<ModulePath, Term> = Map::new();
  let path_a = mpt("a");
  let path_b = mpt("b");
  let term_a = var("x");
  let term_b = var("y");

  map = merge_detect(map, (path_a.clone(), term_a.clone())).unwrap();
  map = merge_detect(map, (path_b.clone(), term_b.clone())).unwrap();
  assert_eq!(map.get(&path_a), Some(&term_a));
  assert_eq!(map.get(&path_b), Some(&term_b));
}

#[test]
fn test_merge_detect_rejects_duplicate() {
  use crate::Map;
  use crate::term::module::merge_detect;

  let path = mpt("duplicate");
  let map: Map<ModulePath, Term> = Map::new();
  let map = merge_detect(map, (path.clone(), var("x"))).unwrap();
  let result = merge_detect(map, (path.clone(), var("y")));
  assert!(result.is_err());
  assert!(result.unwrap_err().contains("duplicate"));
}

#[test]
fn test_search_paths_empty() {
  let sp = SearchPaths::empty();
  assert!(sp.is_empty());
}

#[test]
fn test_search_paths_new_and_push() {
  let mut sp = SearchPaths::new(vec![PathBuf::from("/a")]);
  assert!(!sp.is_empty());
  sp.push(PathBuf::from("/b"));
  assert_eq!(sp.0.len(), 2);
}

#[test]
fn test_search_paths_default_is_empty() {
  let sp = SearchPaths::default();
  assert!(sp.is_empty());
}

fn random_tmp_dir(label: &str) -> PathBuf {
  let prefix = format!("monad-test-{}-{:x}", label, std::process::id());
  PathBuf::from("/tmp").join(prefix)
}

#[test]
fn test_resolve_file_path_finds_in_first_dir() {
  let dir1 = random_tmp_dir("s1a");
  let dir2 = random_tmp_dir("s1b");

  let sp = SearchPaths::new(vec![dir1.clone(), dir2]);

  std::fs::create_dir_all(&dir1).unwrap();
  std::fs::write(dir1.join("test_mod.mo"), "").unwrap();

  let mp = mpt("test_mod");
  let found = mp.resolve_file_path(&sp);
  assert!(found.is_some());

  std::fs::remove_dir_all(&dir1).unwrap();
}

#[test]
fn test_resolve_file_path_finds_in_second_dir_when_first_missing() {
  let dir1 = random_tmp_dir("s2a");
  let dir2 = random_tmp_dir("s2b");

  let sp = SearchPaths::new(vec![dir1, dir2.clone()]);

  std::fs::create_dir_all(&dir2).unwrap();
  std::fs::write(dir2.join("test_mod.mo"), "").unwrap();

  let mp = mpt("test_mod");
  let found = mp.resolve_file_path(&sp);
  assert!(found.is_some());
  assert!(found.unwrap().starts_with(dir2.to_str().unwrap()));

  std::fs::remove_dir_all(&dir2).unwrap();
}

#[test]
fn test_resolve_file_path_none_when_not_in_any_dir() {
  let dir1 = random_tmp_dir("nonexistent-1");
  let dir2 = random_tmp_dir("nonexistent-2");

  let sp = SearchPaths::new(vec![dir1, dir2]);

  let mp = mpt("no_such_module");
  let found = mp.resolve_file_path(&sp);
  assert!(found.is_none());
}

#[test]
fn test_resolve_file_path_empty_search_paths_returns_none() {
  let sp = SearchPaths::empty();
  let mp = mpt("anything");
  let found = mp.resolve_file_path(&sp);
  assert!(found.is_none());
}
