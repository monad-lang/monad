pub mod module;
#[cfg(test)]
pub mod test;

use crate::{Map, parser::locate::Info, term::module::GlobalScope, vec_fmt};
use std::{
  fmt::Display,
  hash::Hash,
  iter::repeat,
  path::{Component, Path, PathBuf},
};

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Location {
  /// Offset relative to the start of a line
  pub line_offset: usize,

  /// The line number of the fragment relatively to the input of the
  /// parser. It starts at line 1.
  pub line: u32,
}

impl<X> From<Info<X>> for Location {
  fn from(value: Info<X>) -> Self {
    Location {
      line_offset: value.line_offset,
      line: value.line,
    }
  }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct SourceRange {
  pub start: Location,
  pub end: Location,
}

impl SourceRange {
  pub(crate) fn new(start: Location, end: Location) -> Self {
    Self { start, end }
  }
}

impl Default for Location {
  fn default() -> Self {
    Self {
      line_offset: Default::default(),
      line: Default::default(),
    }
  }
}
impl Default for SourceRange {
  fn default() -> Self {
    Self {
      start: Default::default(),
      end: Default::default(),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Identifier(String);

impl Identifier {
  pub fn new(s: String) -> Self {
    Identifier(s)
  }
  pub fn as_str(&self) -> &str {
    &self.0
  }
  pub fn rename(&self) -> Identifier {
    Identifier(self.0.clone() + "~")
  }
  pub fn to_path(self) -> ModulePath {
    ModulePath::single(self)
  }
}

impl From<Identifier> for ModulePath {
  fn from(value: Identifier) -> Self {
    value.to_path()
  }
}

impl Display for Identifier {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.0)
  }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Operator(String);

impl From<&str> for Operator {
  fn from(value: &str) -> Self {
    Operator(value.into())
  }
}

impl Display for Operator {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl Operator {
  pub fn new(s: String) -> Self {
    Operator(s)
  }
  pub fn as_str(&self) -> &str {
    &self.0
  }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum NameRef {
  P(ModulePath),
  Id(Identifier),
  Op(Operator),
  Index(usize),
}

impl NameRef {
  pub fn is_name(&self) -> bool {
    match self {
      Id(_) => true,
      NameRef::P(_) => true,
      _ => false,
    }
  }
  pub fn as_id(&self) -> Option<&Identifier> {
    match self {
      Id(id) => Some(id),
      NameRef::P(p) if p.len() == 1 => Some(p.last()),
      _ => None,
    }
  }

  pub fn to_path(&self) -> Option<ModulePath> {
    match self {
      NameRef::P(module_path) => Some(module_path.clone()),
      Id(identifier) => Some(ModulePath::single(identifier.clone())),
      _ => None,
    }
  }

  pub fn is_id(&self) -> bool {
    match self {
      Id(_) => true,
      _ => false,
    }
  }
}

impl From<ModulePath> for NameRef {
  fn from(value: ModulePath) -> Self {
    NameRef::P(value)
  }
}
impl From<Operator> for NameRef {
  fn from(value: Operator) -> Self {
    NameRef::Op(value)
  }
}
impl From<Identifier> for NameRef {
  fn from(value: Identifier) -> Self {
    NameRef::Id(value)
  }
}

use NameRef::Id;

impl Display for NameRef {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      NameRef::Id(identifier) => write!(f, "{}", identifier),
      NameRef::Op(op) => write!(f, "({op})"),
      NameRef::Index(i) => write!(f, "'{i}"),
      NameRef::P(module_path) => write!(f, "{module_path}"),
    }
  }
}

pub fn id(s: &str) -> Identifier {
  Identifier(s.to_string())
}
pub fn mpt(s: &str) -> ModulePath {
  ModulePath::top(s)
}

pub fn type_u(universe: u64) -> Term {
  Term::Type { universe }
}

pub fn type0() -> Term {
  Term::Type { universe: 0 }
}

pub fn pi_var(name: Identifier, arg: Term, ret: Term) -> Term {
  Term::Pi {
    arg_name: Some(name),
    arg: Box::new(arg),
    ret: Box::new(ret),
  }
}

pub fn type_count_args(typ: &Term) -> u8 {
  let mut args = 0;
  let mut t = typ;
  while let Pi {
    arg: _,
    ret,
    arg_name: _,
  } = t
  {
    t = ret;
    args += 1;
  }
  args
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeConstraint {
  class: ModulePath,
  vars: Vec<Identifier>,
}

impl Display for TypeConstraint {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.class)
  }
}

impl TypeConstraint {
  pub fn vars(&self) -> &Vec<Identifier> {
    &self.vars
  }
  pub fn class(&self) -> &ModulePath {
    &self.class
  }
}

pub fn type_constraint(class: ModulePath, vars: Vec<Identifier>) -> TypeConstraint {
  TypeConstraint { class, vars }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructField {
  name: Identifier,
  typ: Term,
  default_value: Option<Term>,
}

pub fn stru_field(name: Identifier, typ: Term, default_value: Option<Term>) -> StructField {
  StructField {
    name,
    typ,
    default_value,
  }
}

fn inductive_term(name: ModulePath, params: Vec<Param>) -> Term {
  let mut term = Var {
    // TODO record values
    name: name.into(),
  };
  if !params.is_empty() {
    term = lams(params, term);
  }
  term
}

pub fn stru(
  name: ModulePath,
  constraints: Vec<TypeConstraint>,
  params: Vec<Param>,
  fields: Vec<StructField>,
  attributes: Vec<Attribute>,
) -> Inductive {
  let typ = params_to_inductive_type(&params, type0());
  let con_params = fields
    .into_iter()
    .map(|d| {
      param(
        d.name, d.typ, // TODO default value
      )
    })
    .collect();
  let constructors = vec![induct_constructor(
    name.clone(),
    name.last().clone(),
    mpvar(name.clone()),
    con_params,
  )];
  let term = inductive_term(name.clone(), params.clone());
  Inductive {
    name,
    params,
    constructors,
    constraints,
    typ,
    variant: InductiveVariant::Struct,
    term,
    attributes,
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InductConstructor {
  inductive_name: ModulePath,
  name: ModulePath,
  term: Term,
  pub(crate) typ: Term,
  pub(crate) params: Vec<Param>,
}

impl Named for InductConstructor {
  fn name(&self) -> &ModulePath {
    &self.name
  }
}

impl InductConstructor {
  pub fn typ(&self) -> &Term {
    &self.typ
  }
}

pub fn induct_constructor(
  inductive_name: ModulePath,
  name: Identifier,
  typ: Term,
  params: Vec<Param>,
) -> InductConstructor {
  let num_args = params.len();
  let mut term = Term::Con(Constructor {
    typ_name: inductive_name.clone(),
    args: repeat(None).take(num_args).collect(),
    name: name.clone(),
    num_args,
  });
  if !params.is_empty() {
    term = lam_indecies(params.clone(), term);
  }
  let name = inductive_name.clone().extend(name.into());
  InductConstructor {
    inductive_name,
    name,
    term,
    typ,
    params,
  }
}

fn params_to_inductive_type(params: &Vec<Param>, typ: Term) -> Term {
  let typ = if params.is_empty() {
    type0()
  } else {
    pi_typs(
      params
        .into_iter()
        .map(|p| p.typ.to_owned().replace_hole(|| type0()))
        .collect(),
      typ,
    )
  };
  typ
}

pub fn inductive(
  name: ModulePath,
  constraints: Vec<TypeConstraint>,
  params: Vec<Param>,
  typ: Term,
  constructors: Vec<InductConstructor>,
  attributes: Vec<Attribute>,
) -> Inductive {
  let typ = params_to_inductive_type(&params, typ.replace_hole(type0));

  let term = inductive_term(name.clone(), params.clone());
  Inductive {
    variant: InductiveVariant::Generic,
    name,
    constraints,
    params,
    typ,
    constructors,
    term,
    attributes,
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassDef {
  pub(crate) name: Identifier,
  pub(crate) typ: Term,
  pub default: Option<Term>,
  pub attributes: Vec<Attribute>,
}

pub fn class_def(
  name: Identifier,
  typ: Term,
  default: Option<Term>,
  attributes: Vec<Attribute>,
) -> ClassDef {
  ClassDef {
    name,
    typ,
    default,
    attributes,
  }
}

pub fn class(
  name: ModulePath,
  constraints: Vec<TypeConstraint>,
  params: Vec<Param>,
  defs: Vec<ClassDef>,
  attributes: Vec<Attribute>,
) -> Inductive {
  let typ = params_to_inductive_type(&params, type0());
  let con_typs = defs.iter().map(|d| d.typ.clone()).collect();
  let con_params = defs
    .into_iter()
    .map(|d| {
      param(
        d.name, d.typ, // TODO default value
      )
    })
    .collect();
  let constructor = induct_constructor(
    name.clone(),
    name.last().clone(),
    pi_typs(con_typs, mpvar(name.clone())),
    con_params,
  );
  let constructors = vec![constructor];
  let term = inductive_term(name.clone(), params.clone());
  Inductive {
    variant: InductiveVariant::Class,
    name,
    params,
    constructors,
    constraints,
    typ,
    term,
    attributes,
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Instance {
  name: ModulePath,
  pub(crate) class_name: ModulePath,
  pub(crate) constraints: Vec<TypeConstraint>,
  pub(crate) args: Vec<Term>,
  pub(crate) impls_map: Map<Identifier, Def>,
  cons: Constructor,
  typ: Term,
  pub attributes: Vec<Attribute>,
}

impl Instance {
  pub fn as_constructor(&self) -> &Constructor {
    &self.cons
  }

  /// Check instance if match the InstanceKey
  pub fn matches(&self, key: &InstanceKey, class: &Inductive, _global: &GlobalScope) -> bool {
    if key.args.len() != self.args.len() {
      return false;
    }
    // TODO constraints
    let res = key.args.iter().all(|key_arg| {
      if let Some((index, _c_param)) = class
        .params
        .iter()
        .enumerate()
        .find(|(_i, c_param)| c_param.name == key_arg.name)
      {
        let arg = self
          .args
          .get(index)
          .expect("instance args did not match class");
        arg == &*key_arg.typ
      } else {
        true // irrelevant
      }
    });
    res
  }
}

pub fn instance(
  name: Option<ModulePath>,
  class_name: ModulePath,
  constraints: Vec<TypeConstraint>,
  args: Vec<Term>,
  impls: Vec<Def>,
  attributes: Vec<Attribute>,
) -> Instance {
  let num_args = impls.len();
  let impls_map = impls
    .iter()
    .map(|d| (d.name.last().clone(), d.clone()))
    .collect();

  let typ = apps(mpvar(class_name.clone()), args.clone());
  let name = name.unwrap_or_else(|| {
    mpt(&format!(
      "instance-{}-{}",
      class_name,
      args
        .iter()
        .map(|a| format!("{a}"))
        .collect::<Vec<String>>()
        .join("-")
    ))
  });
  let cons = Constructor {
    name: class_name.last().clone(),
    typ_name: class_name.clone(),
    num_args,
    args: impls.iter().map(|def| Some(def.term.clone())).collect(),
  };
  Instance {
    name,
    class_name,
    args,
    cons,
    impls_map,
    constraints,
    typ,
    attributes,
  }
}

impl Typed for Instance {
  fn typ(&self) -> &Term {
    &self.typ
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum InductiveVariant {
  Struct,
  Class,
  Generic,
}

/// Inductive type
#[derive(Clone, Debug, PartialEq)]
pub struct Inductive {
  variant: InductiveVariant,
  name: ModulePath,
  pub(crate) constraints: Vec<TypeConstraint>,
  pub(crate) params: Vec<Param>,
  term: Term,
  typ: Term,
  pub(crate) constructors: Vec<InductConstructor>,
  pub attributes: Vec<Attribute>,
}

pub trait AsVarRef {
  fn as_var_ref<'a>(&'a self) -> VarRef<'a>;
}

impl Typed for Inductive {
  fn typ(&self) -> &Term {
    &self.typ
  }
}
impl Inductive {
  pub fn find_cons(&self, id: &Identifier) -> Option<&InductConstructor> {
    self.constructors.iter().find(|c| c.name.last() == id)
  }
  pub fn params(&self) -> &Vec<Param> {
    &self.params
  }
  pub fn variant(&self) -> &InductiveVariant {
    &self.variant
  }
}

pub trait Named {
  fn name(&self) -> &ModulePath;
}

impl Named for Inductive {
  fn name(&self) -> &ModulePath {
    &self.name
  }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum Par {
  P(Param),
  I { typ: Box<Term> },
}

impl Par {
  pub fn typ(&self) -> &Term {
    match self {
      Par::P(param) => &param.typ,
      Par::I { typ } => typ,
    }
  }

  pub fn with_type(&self, typ: Term) -> Par {
    use Par::*;
    match self {
      P(param_) => P(param(param_.name.clone(), *param_.typ.clone())),
      I { typ: _ } => I { typ: Box::new(typ) },
    }
  }
}

impl Display for Par {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Par::P(p) => write!(f, "{p}"),
      Par::I { typ } => write!(f, "(' : {typ})"),
    }
  }
}
#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Param {
  pub name: Identifier,
  pub typ: Box<Term>,
}

impl Typed for Param {
  fn typ(&self) -> &Term {
    &self.typ
  }
}

impl Display for Param {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.typ.is_known() {
      write!(f, "({} : {})", self.name, self.typ)
    } else {
      write!(f, "{}", self.name)
    }
  }
}

pub fn par(s: &str) -> Param {
  param(id(s), Hole)
}

pub fn param(name: Identifier, typ: Term) -> Param {
  Param {
    name,
    typ: Box::new(typ),
  }
}

pub fn dpar(s: &str, typ: Term) -> Param {
  param(id(s), typ)
}

pub fn mpvar(name: ModulePath) -> Term {
  Var {
    name: NameRef::P(name),
  }
}
pub fn ty(name: Identifier) -> Term {
  Var {
    name: NameRef::Id(name),
  }
}
pub fn mpv(s: &str) -> Term {
  mpvar(mpt(s))
}

pub fn typ(s: &str) -> Term {
  ty(id(s))
}

pub fn forall(param: Param, body: Term) -> Term {
  assert!(
    param.typ.is_known(),
    "Holes not allowed in implicit arguments"
  );
  Forall {
    name: param.name,
    typ: param.typ,
    body: Box::new(body),
  }
}

pub fn foralls(params: Vec<Param>, mut body: Term) -> Term {
  for param in params.into_iter().rev() {
    body = forall(param, body);
  }
  body
}

pub fn pi_typs(typs: Vec<Term>, last: Term) -> Term {
  let mut res = last;
  for typ in typs.into_iter().rev() {
    res = pi(typ, res);
  }
  res
}

pub fn pi(arg: Term, ret: Term) -> Term {
  Term::Pi {
    arg_name: None,
    arg: Box::new(arg),
    ret: Box::new(ret),
  }
}
pub fn pi_name(arg_name: Option<Identifier>, arg: Term, ret: Term) -> Term {
  Term::Pi {
    arg_name,
    arg: Box::new(arg),
    ret: Box::new(ret),
  }
}

pub fn app2(s: &str, s2: &str) -> Term {
  app(var(s), var(s2))
}
#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct MapTerm {
  pub(crate) value: Map<Identifier, Term>,
}

impl Display for MapTerm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{{\n")?;
    for (key, value) in self.value.iter() {
      write!(f, "{key} := {value},\n")?;
    }
    write!(f, "}}")
  }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct MatchCase {
  pub(crate) name: Identifier,
  pub(crate) args: Vec<Identifier>,
  pub(crate) value: Box<Term>,
}

impl Display for MatchCase {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let args = self
      .args
      .iter()
      .map(|i| i.as_str())
      .collect::<Vec<&str>>()
      .join(" ");
    write!(f, "{} {} => {}", self.name, args, self.value)
  }
}
pub fn case(name: Identifier, args: Vec<Identifier>, value: Term) -> MatchCase {
  MatchCase {
    name,
    args,
    value: Box::new(value),
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum NumSuffix {
  I8,
  I16,
  I32,
  I64,
  U8,
  U16,
  U32,
  U64,
  F32,
  F64,
}

impl NumSuffix {
  pub fn type_name(&self) -> &'static str {
    match self {
      NumSuffix::I8 => "I8",
      NumSuffix::I16 => "I16",
      NumSuffix::I32 => "I32",
      NumSuffix::I64 => "I64",
      NumSuffix::U8 => "U8",
      NumSuffix::U16 => "U16",
      NumSuffix::U32 => "U32",
      NumSuffix::U64 => "U64",
      NumSuffix::F32 => "F32",
      NumSuffix::F64 => "F64",
    }
  }

  pub fn is_float(&self) -> bool {
    matches!(self, NumSuffix::F32 | NumSuffix::F64)
  }

  pub fn is_int(&self) -> bool {
    !self.is_float()
  }

  pub fn from_suffix(s: &str) -> Option<NumSuffix> {
    match s {
      "i8" => Some(NumSuffix::I8),
      "i16" => Some(NumSuffix::I16),
      "i32" => Some(NumSuffix::I32),
      "i64" => Some(NumSuffix::I64),
      "u8" => Some(NumSuffix::U8),
      "u16" => Some(NumSuffix::U16),
      "u32" => Some(NumSuffix::U32),
      "u64" => Some(NumSuffix::U64),
      "f32" => Some(NumSuffix::F32),
      "f64" => Some(NumSuffix::F64),
      _ => None,
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub struct F64Wrap(pub f64);

impl PartialEq for F64Wrap {
  fn eq(&self, other: &Self) -> bool {
    self.0.to_bits() == other.0.to_bits()
  }
}

impl Eq for F64Wrap {}

impl std::hash::Hash for F64Wrap {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.0.to_bits().hash(state)
  }
}

impl PartialOrd for F64Wrap {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self.0.to_bits().partial_cmp(&other.0.to_bits())
  }
}

impl Ord for F64Wrap {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.0.to_bits().cmp(&other.0.to_bits())
  }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum Literal {
  Str {
    value: String,
  },
  Num {
    value: i64,
    suffix: NumSuffix,
  },
  Float {
    value: F64Wrap,
    suffix: NumSuffix,
  },
  Map {
    value: MapTerm,
  },
  Match {
    value: Box<Term>,
    cases: Vec<MatchCase>,
  },
  // TODO remove and use only match
  If {
    value: Box<Term>,
    then: Box<Term>,
    els: Box<Term>,
  },
}

pub fn match_term(value: Term, cases: Vec<MatchCase>) -> Term {
  Term::Lit {
    value: Literal::Match {
      value: Box::new(value),
      cases,
    },
  }
}
pub fn if_term(value: Term, then: Term, els: Term) -> Term {
  Term::Lit {
    value: Literal::If {
      value: Box::new(value),
      then: Box::new(then),
      els: Box::new(els),
    },
  }
}

impl Display for Literal {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Literal::Str { value } => write!(f, "{value:?}"),
      Literal::Num { value, suffix } => write!(f, "{value}{}", suffix.type_name().to_lowercase()),
      Literal::Float { value, suffix } => {
        if suffix == &NumSuffix::F64 {
          write!(f, "{}", value.0)
        } else {
          write!(f, "{}{}", value.0, suffix.type_name().to_lowercase())
        }
      }
      Literal::Map { value } => write!(f, "{value}"),
      Literal::Match { value, cases } => {
        let cs = cases
          .iter()
          .map(|c| format!("{c}"))
          .collect::<Vec<String>>()
          .join(",\n ");
        write!(f, "match {value} {{\n {}\n}}", cs)
      }
      Literal::If { value, then, els } => write!(f, "if {value} then {then} else {els}"),
    }
  }
}

pub fn map_term(value: Map<Identifier, Term>) -> Term {
  Term::Lit {
    value: Literal::Map {
      value: MapTerm { value },
    },
  }
}

/// Constructor Term for inductive type
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Constructor {
  pub(crate) name: Identifier,
  pub(crate) typ_name: ModulePath,
  pub(crate) num_args: usize,
  pub(crate) args: Vec<Option<Term>>,
}

pub fn constructor(name: Identifier, typ_name: ModulePath, args: Vec<Option<Term>>) -> Constructor {
  let num_args = args.len();
  Constructor {
    name,
    typ_name,
    num_args,
    args,
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypingContext {
  missing_args: Vec<Identifier>,
}

/// Result from typechecking
#[derive(Clone, Debug, PartialEq)]
pub struct TypedTerm {
  pub term: Term,
  typ: Term,
}

impl Typed for TypedTerm {
  fn typ(&self) -> &Term {
    &self.typ
  }
}
impl TypedTerm {
  pub fn term(&self) -> &Term {
    &self.term
  }
  pub fn to_tuple(self) -> (Term, Term) {
    (self.term, self.typ)
  }
  pub fn mut_term(&mut self) -> &mut Term {
    &mut self.term
  }

  pub fn mut_type(&mut self) -> &mut Term {
    &mut self.typ
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum VarRef<'a> {
  /// A local variable
  Local { typ: &'a Term },
  /// A free var ref
  Free { term: &'a Term, typ: &'a Term },
  /// Indicates that the existing ref needs to be updated
  UpdateRef {
    new_path: &'a ModulePath,
    term: &'a Term,
    typ: &'a Term,
  },
}
impl<'a> Typed for VarRef<'a> {
  fn typ(&self) -> &Term {
    match self {
      VarRef::Local { typ } => &typ,
      VarRef::Free { term: _, typ } => &typ,
      VarRef::UpdateRef {
        new_path: _,
        typ,
        term: _,
      } => &typ,
    }
  }
}

pub fn free_var_ref<'a>(term: &'a Term, typ: &'a Term) -> VarRef<'a> {
  VarRef::Free { term, typ }
}
pub fn typed_term(term: Term, typ: Term) -> TypedTerm {
  TypedTerm { term, typ }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum Term {
  /// Implicit type arguments
  Forall {
    name: Identifier,
    typ: Box<Term>,
    body: Box<Term>,
  },
  /// Function type
  Pi {
    arg_name: Option<Identifier>,
    arg: Box<Term>,
    ret: Box<Term>,
  },
  /// Variable
  Var {
    name: NameRef,
  },
  /// Lambda
  Lam {
    param: Par,
    body: Box<Term>,
  },
  /// Lambda application
  App {
    fun: Box<Term>,
    arg: Box<Term>,
  },
  // Type annotation
  Ann {
    term: Box<Term>,
    typ: Box<Term>,
  },
  /// Literal value
  Lit {
    value: Literal,
  },
  /// Native term
  Ntv {
    native: Native,
  },
  /// Inductive constructor
  Con(Constructor),
  /// Meta info about a term
  Ctx {
    loc: SourceRange,
    term: Box<Term>,
  },
  /// Propositions
  Prop,
  /// Type of types
  Type {
    universe: u64,
  },
  /// Hole, bottom
  Hole,
}

impl Term {
  pub fn is_known(&self) -> bool {
    match self {
      Hole => false,
      _ => true,
    }
  }

  pub fn replace_hole(self, f: impl FnOnce() -> Term) -> Term {
    match self {
      Hole => f(),
      t => t,
    }
  }
  pub fn is_forall(&self) -> bool {
    match self {
      Forall {
        name: _,
        typ: _,
        body: _,
      } => true,
      Ctx { loc: _, term } => term.is_forall(),
      Pi {
        arg,
        ret: _,
        arg_name: _,
      } => arg.is_forall(),
      _ => false,
    }
  }
  pub fn is_type(&self) -> bool {
    match self {
      Term::Type { universe: _ } => true,
      Var { name } if name.is_name() => name.to_path().unwrap() == mpt("Type"),
      Pi {
        arg: _,
        ret: _,
        arg_name: _,
      } => true,
      Forall {
        name: _,
        typ: _,
        body: _,
      } => true,
      Ctx { loc: _, term } => term.is_type(),
      _ => false,
    }
  }
  pub fn is_lam(&self) -> bool {
    match self {
      Term::Lam { param: _, body: _ } => true,
      _ => false,
    }
  }
  pub fn is_lit(&self) -> bool {
    match self {
      Term::Lit { value: _ } => true,
      _ => false,
    }
  }
  pub fn is_num(&self) -> bool {
    matches!(
      self,
      Term::Lit {
        value: Literal::Num { .. }
      } | Term::Lit {
        value: Literal::Float { .. }
      }
    )
  }
  pub fn is_str(&self) -> bool {
    match self {
      Term::Lit {
        value: Literal::Str { value: _ },
      } => true,
      _ => false,
    }
  }
  pub fn is_map(&self) -> bool {
    match self {
      Term::Lit {
        value: Literal::Map { value: _ },
      } => true,
      _ => false,
    }
  }

  pub fn node_type(&self) -> &str {
    match self {
      Var { name: _ } => "var",
      Lam { param: _, body: _ } => "lam",
      App { fun: _, arg: _ } => "app",
      Lit { value } => match value {
        Literal::Str { .. } => "str",
        Literal::Num { .. } => "num",
        Literal::Float { .. } => "float",
        Literal::Map { .. } => "map",
        Literal::Match { .. } => "match",
        Literal::If { .. } => "if",
      },
      Ntv { native: _ } => "ntv",
      Con(_) => "con",
      Ctx { loc: _, term: _ } => "ctx",
      Forall {
        name: _,
        typ: _,
        body: _,
      } => "for",
      Pi {
        arg: _,
        ret: _,
        arg_name: _,
      } => "pi",
      Prop => "prop",
      Type { universe: _ } => "type",
      Hole => "hole",
      Ann { .. } => "ann",
    }
  }
}

pub trait Typed {
  /// Type of the given value
  fn typ(&self) -> &Term;
}

pub use Term::{Ann, App, Con, Ctx, Forall, Hole, Lam, Lit, Ntv, Pi, Prop, Type, Var};

impl Display for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Var { name } => write!(f, "{name}"),
      Lam { param, body } => write!(f, "(fn {param} => {body})"),
      App { fun, arg } => write!(f, "({fun} {arg})"),
      Lit { value } => write!(f, "{value}"),
      Type { universe } => {
        if universe > &0 {
          write!(f, "Type {universe}")
        } else {
          write!(f, "Type")
        }
      }
      Ntv { native: _ } => write!(f, "native"),
      Con(Constructor {
        typ_name,
        args,
        name,
        num_args: _,
      }) => {
        if !args.is_empty() {
          let args = args
            .iter()
            .map(|a| match a {
              Some(a) => format!("{a}"),
              None => "_".into(),
            })
            .collect::<Vec<String>>()
            .join(" ");
          write!(f, "({typ_name}.{name} {args})")
        } else {
          write!(f, "{typ_name}.{name}")
        }
      }
      Ctx { loc: _, term } => write!(f, "{term}"),
      Pi { arg, ret, arg_name } => {
        if let Some(name) = arg_name {
          write!(f, "({name} : {arg} -> {ret})")
        } else {
          write!(f, "({arg} -> {ret})")
        }
      }
      Forall { name, typ, body } => write!(f, "{{{name} : {typ}}} -> {body}"),
      Prop => write!(f, "Prop"),
      Hole => write!(f, "_"),
      Ann { term, typ } => write!(f, "{term} : {typ}"),
    }
  }
}

pub fn ok(term: Term) -> Term {
  constructor_term(id("ok"), mpt("Result"), vec![term])
}

pub fn err(term: Term) -> Term {
  constructor_term(id("err"), mpt("Result"), vec![term])
}

pub fn b_true() -> Term {
  constructor_term(id("true"), mpt("Bool"), vec![])
}

pub fn b_false() -> Term {
  constructor_term(id("false"), mpt("Bool"), vec![])
}

pub fn none() -> Term {
  constructor_term(id("none"), mpt("Option"), vec![])
}
/// Unit.unit
pub fn unit() -> Term {
  constructor_term(id("unit"), mpt("Unit"), vec![])
}

/// pure : A -> IO A
pub fn io_term(term: Term) -> Term {
  constructor_term(id("io"), mpt("IO"), vec![term])
}

pub fn some(term: Term) -> Term {
  constructor_term(id("some"), mpt("Option"), vec![term])
}

pub fn opr(left: Term, operator: NameRef, right: Term) -> Term {
  app(app(Term::Var { name: operator }, left), right)
}
#[cfg(test)]
pub fn oper(left: Term, operator: &str, right: Term) -> Term {
  app(
    app(
      Term::Var {
        name: NameRef::Op(Operator(operator.into())),
      },
      left,
    ),
    right,
  )
}

pub fn ctx(term: Term, loc: SourceRange) -> Term {
  Term::Ctx {
    loc,
    term: Box::new(term),
  }
}
pub fn app(fun: Term, arg: Term) -> Term {
  Term::App {
    fun: Box::new(fun),
    arg: Box::new(arg),
  }
}

pub fn apps(fun: Term, args: Vec<Term>) -> Term {
  assert!(args.len() >= 1);
  let mut term = fun;
  for arg in args {
    term = app(term, arg);
  }
  term
}

pub fn lam_index(typ: Term, body: Term) -> Term {
  Term::Lam {
    param: Par::I { typ: Box::new(typ) },
    body: Box::new(body),
  }
}

pub fn lam_indecies(params: Vec<Param>, body: Term) -> Term {
  assert!(params.len() >= 1);
  let mut body = body;
  for param in params.into_iter().rev() {
    body = Term::Lam {
      param: Par::I { typ: param.typ },
      body: Box::new(body),
    }
  }
  body
}

pub fn lam(param: Param, body: Term) -> Term {
  lam_par(Par::P(param), body)
}

pub fn lam_par(param: Par, body: Term) -> Term {
  Term::Lam {
    param,
    body: Box::new(body),
  }
}

pub fn lams(params: Vec<Param>, body: Term) -> Term {
  assert!(params.len() >= 1);
  let mut body = body;
  for param in params.into_iter().rev() {
    body = lam(param, body);
  }
  body
}

pub fn constructor_term(name: Identifier, typ_name: ModulePath, args: Vec<Term>) -> Term {
  Term::Con(constructor(
    name,
    typ_name,
    args.into_iter().map(Some).collect(),
  ))
}

pub fn list_empty() -> Term {
  constructor_term(id("empty"), mpt("List"), vec![])
}
pub fn list_cons(head: Term, tail: Term) -> Term {
  app(app(pvar(vec!["List", "cons"]), head), tail)
}

pub fn to_list_term(v: Vec<Term>) -> Term {
  let init = list_empty();
  let l = |tail: Term, head: Term| list_cons(head, tail);
  v.into_iter().rev().fold(init, l)
}

pub fn strings_to_list_term(v: Vec<String>) -> Term {
  let init = list_empty();
  let l = |tail: Term, head: String| list_cons(str(&head), tail);
  v.into_iter().rev().fold(init, l)
}

pub struct LetVar {
  pub(crate) name: Identifier,
  pub(crate) typ: Term,
  pub(crate) value: Term,
}

pub fn lets(vars: Vec<LetVar>, body: Term) -> Term {
  assert!(vars.len() >= 1);
  let mut body = body;
  for var in vars.into_iter().rev() {
    let lam_term = lam(param(var.name, var.typ), body);
    body = app(lam_term, var.value);
  }
  body
}

pub fn let_term(name: Identifier, typ: Term, value: Term, body: Term) -> Term {
  let lam_term = lam(param(name, typ), body);
  app(lam_term, value)
}

pub fn ann(term: Term, typ: Term) -> Term {
  Ann {
    term: Box::new(term),
    typ: Box::new(typ),
  }
}

/// Free variable
pub fn var(s: &str) -> Term {
  Term::Var {
    name: NameRef::Id(id(s)),
  }
}
pub fn var_id(id: Identifier) -> Term {
  Term::Var {
    name: NameRef::Id(id),
  }
}
pub fn pvar(s: Vec<&str>) -> Term {
  Term::Var {
    name: NameRef::P(ModulePath::new(s.iter().map(|i| id(i)).collect())),
  }
}

pub fn bvar(index: usize) -> Term {
  Term::Var {
    name: NameRef::Index(index),
  }
}

pub fn str(s: &str) -> Term {
  Term::Lit {
    value: Literal::Str {
      value: s.to_string(),
    },
  }
}

pub fn num(value: i64) -> Term {
  Term::Lit {
    value: Literal::Num {
      value,
      suffix: NumSuffix::I64,
    },
  }
}

pub fn num_suffix(value: i64, suffix: NumSuffix) -> Term {
  Term::Lit {
    value: Literal::Num { value, suffix },
  }
}

pub fn float(value: f64) -> Term {
  Term::Lit {
    value: Literal::Float {
      value: F64Wrap(value),
      suffix: NumSuffix::F64,
    },
  }
}

pub fn float_suffix(value: f64, suffix: NumSuffix) -> Term {
  Term::Lit {
    value: Literal::Float {
      value: F64Wrap(value),
      suffix,
    },
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Def {
  pub(crate) name: ModulePath,
  pub(crate) typ: Term,
  pub term: Term,
  pub(crate) type_constraints: Vec<TypeConstraint>,
  pub attributes: Vec<Attribute>,
}

impl Def {
  pub fn to_typed_term(self) -> TypedTerm {
    typed_term(self.term, self.typ)
  }
}
impl AsVarRef for Def {
  fn as_var_ref<'a>(&'a self) -> VarRef<'a> {
    free_var_ref(&self.term, &self.typ)
  }
}

pub fn def(
  name: ModulePath,
  type_cons: Vec<TypeConstraint>,
  typ: Term,
  term: Term,
  attributes: Vec<Attribute>,
) -> Def {
  Def {
    name,
    type_constraints: type_cons,
    typ,
    term,
    attributes,
  }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Native {
  pub native_name: Identifier,
  pub(crate) num_args: usize,
  pub(crate) args: Vec<Option<Term>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AttrArg {
  Ident(Identifier),
  Str(String),
  Num(i64),
  Named {
    name: Identifier,
    value: Box<AttrArg>,
  },
  Group(Vec<AttrArg>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Attribute {
  pub name: Identifier,
  pub args: Vec<AttrArg>,
}

/// Construct a def with a native body from attribute args
pub fn def_with_native(
  native_name: Identifier,
  name: ModulePath,
  params: Vec<Param>,
  return_typ: Term,
  attributes: Vec<Attribute>,
) -> Result<Def, String> {
  let typ = if params.is_empty() {
    return_typ
  } else {
    pi_typs(
      params.iter().map(|p| *p.typ.clone()).collect::<Vec<_>>(),
      return_typ,
    )
  };
  let num_args = params.len();
  let body = Term::Ntv {
    native: Native {
      native_name,
      num_args,
      args: repeat(None).take(num_args).collect(),
    },
  };

  let term = lam_indecies(params, body);
  Ok(def(name, vec![], typ, term, attributes))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModulePath(Vec<Identifier>);

impl From<PathBuf> for ModulePath {
  fn from(value: PathBuf) -> Self {
    let mut p: Vec<String> = value
      .components()
      .filter_map(|f| match f {
        Component::Normal(f) => Some(f.to_str().expect("valid path").to_owned()),
        _ => None,
      })
      .collect();
    let last = p.last_mut().expect("Nonempty path");
    *last = Path::new(&last)
      .file_stem()
      .and_then(|os| os.to_str().to_owned())
      .unwrap_or(last)
      .to_owned();
    let p = p.into_iter().map(Identifier).collect();
    ModulePath::new(p)
  }
}

impl Display for ModulePath {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "{}",
      self
        .0
        .iter()
        .map(|i| i.as_str())
        .collect::<Vec<&str>>()
        .join(".")
    )
  }
}

impl ModulePath {
  pub fn to_name_ref(self) -> NameRef {
    if self.0.len() == 1 {
      Id(self.last().clone())
    } else {
      NameRef::P(self)
    }
  }
  pub fn to_vec(self) -> Vec<Identifier> {
    self.0
  }
  pub fn extend(mut self, mut path: ModulePath) -> ModulePath {
    self.0.append(&mut path.0);
    ModulePath(self.0)
  }
  pub fn append(&self, mut ids: Vec<Identifier>) -> ModulePath {
    let mut path = self.0.clone();
    path.append(&mut ids);
    ModulePath(path)
  }
  pub fn single(id: Identifier) -> ModulePath {
    ModulePath(vec![id])
  }
  pub fn top(s: &str) -> ModulePath {
    ModulePath(vec![id(s)])
  }
  pub fn new(l: Vec<Identifier>) -> Self {
    if l.is_empty() {
      panic!("NamePath can not be empty");
    }
    ModulePath(l)
  }
  pub fn as_identifier(&self) -> Option<&Identifier> {
    match self.0.as_slice() {
      [id] => Some(id),
      _ => None,
    }
  }
  pub fn len(&self) -> usize {
    self.0.len()
  }
  pub fn as_str(&self) -> Option<&str> {
    self.as_identifier().map(|i| i.as_str())
  }
  pub fn last(&self) -> &Identifier {
    self.0.last().unwrap()
  }
  pub fn to_file_path(&self) -> PathBuf {
    let mut p = PathBuf::new();
    let mut iter = self.0.iter().peekable();
    while let Some(i) = iter.next() {
      if iter.peek().is_some() {
        p.push(i.as_str())
      } else {
        p.push(i.as_str().to_string() + ".mo");
      }
    }
    p
  }

  pub fn open(&self, opens: &Vec<&Open>) -> Vec<ModulePath> {
    opens
      .iter()
      .filter_map(|open| self.remove_prefix(&open.module_path))
      .collect()
  }
  /// Check if ModulePath is a prefix
  /// # Examples
  /// ```rust
  /// use monad_core::term::mp;
  /// let p = mp(vec!["a", "b", "cfun"]);
  /// assert!(p.is_prefix(&mp(vec!["a", "b"])));
  /// assert!(p.is_prefix(&mp(vec!["a"])));
  /// assert!(!p.is_prefix(&mp(vec!["a", "b", "cfun"])));
  /// assert!(!p.is_prefix(&mp(vec!["cfun"])));
  /// ```
  pub fn is_prefix(&self, prefix: &ModulePath) -> bool {
    if prefix.len() < self.len() {
      let matches = prefix.0.iter().zip(self.0.iter()).all(|(a, b)| a == b);
      matches
    } else {
      false
    }
  }
  /// Remove a prefix and return a new path if possible
  /// # Examples
  /// ```rust
  /// use monad_core::term::mp;
  /// let p = mp(vec!["a", "b", "cfun"]);
  /// assert_eq!(p.remove_prefix(&mp(vec!["a", "b"])), Some(mp(vec!["cfun"])));
  /// assert_eq!(p.remove_prefix(&mp(vec!["cfun"])), None);
  /// ```
  pub fn remove_prefix(&self, prefix: &ModulePath) -> Option<ModulePath> {
    if self.is_prefix(prefix) {
      let (_, tail) = self.0.split_at(prefix.len());
      let mp = ModulePath::new(tail.into());
      Some(mp)
    } else {
      None
    }
  }
}

pub fn mp(v: Vec<&str>) -> ModulePath {
  ModulePath::new(v.iter().map(|i| id(i)).collect())
}

#[derive(Debug, Clone, PartialEq)]
pub struct Use {
  pub source_location: SourceRange,
  pub(crate) module_path: ModulePath,
}

impl Use {
  pub fn module_path(&self) -> &ModulePath {
    &self.module_path
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Open {
  pub source_location: SourceRange,
  pub(crate) module_path: ModulePath,
}

impl Open {
  pub fn module_path(&self) -> &ModulePath {
    &self.module_path
  }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct InstanceKey {
  pub(crate) class: ModulePath,
  type_cons: Vec<TypeConstraint>,
  pub(crate) args: Vec<Param>,
}

impl Display for InstanceKey {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let args = self
      .args
      .iter()
      .map(|param| format!("({} => {})", param.name, param.typ))
      .collect::<Vec<String>>()
      .join(" ");
    write!(
      f,
      "instance key for {} with args {args} and constraints [{}]",
      self.class,
      vec_fmt(&self.type_cons)
    )
  }
}

impl InstanceKey {
  pub fn new(class: ModulePath, type_cons: Vec<TypeConstraint>, args: Vec<Param>) -> Self {
    Self {
      class,
      type_cons,
      args,
    }
  }
}

/// Wrapper for adding meta info
#[derive(Clone, PartialEq, Debug)]
pub struct SourceContext<V> {
  pub(crate) loc: SourceRange,
  pub(crate) value: V,
}

impl<V> std::ops::Deref for SourceContext<V> {
  type Target = V;

  fn deref(&self) -> &Self::Target {
    &self.value
  }
}

impl<V: Display> Display for SourceContext<V> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "{} at {}:{}",
      self.value, self.loc.start.line, self.loc.start.line_offset
    )
  }
}

impl<V> SourceContext<V> {
  pub fn new(loc: SourceRange, value: V) -> Self {
    Self { loc, value }
  }
  pub fn map<R>(self, f: impl FnOnce(V) -> R) -> SourceContext<R> {
    let value = f(self.value);
    SourceContext {
      loc: self.loc,
      value,
    }
  }

  pub fn no_ctx(value: V) -> Self {
    SourceContext {
      loc: Default::default(),
      value,
    }
  }
  pub fn with<B>(&self, v: B) -> SourceContext<B> {
    SourceContext {
      loc: self.loc.clone(),
      value: v,
    }
  }

  pub fn value(&self) -> &V {
    &self.value
  }
}

/// Class function reference
#[derive(Clone, Debug, PartialEq)]
pub struct ClassDefRef<'a> {
  full_name: ModulePath,
  pub name: &'a Identifier,
  pub typ: &'a Term,
  pub class: &'a Inductive,
}

pub fn class_def_ref<'a>(
  full_name: ModulePath,
  name: &'a Identifier,
  typ: &'a Term,
  class: &'a Inductive,
) -> ClassDefRef<'a> {
  ClassDefRef {
    full_name,
    name,
    typ,
    class,
  }
}
impl<'a> Named for ClassDefRef<'a> {
  fn name(&self) -> &ModulePath {
    &self.full_name
  }
}

impl<'a> ClassDefRef<'a> {
  pub fn typ(&self) -> &Term {
    &self.typ
  }

  pub fn with_path(&self, path: ModulePath) -> ClassDefRef<'_> {
    ClassDefRef {
      full_name: path,
      name: self.name,
      typ: self.typ,
      class: self.class,
    }
  }
}
#[derive(Debug, Clone)]
pub struct DefRef<'a> {
  module: &'a ModulePath,
  loc: &'a SourceRange,
  name: ModulePath,
  typ: &'a Term,
  term: &'a Term,
}

impl<'a> Typed for DefRef<'a> {
  fn typ(&self) -> &Term {
    self.typ
  }
}

impl<'a> DefRef<'a> {
  pub fn with_name(&self, name: ModulePath) -> DefRef<'_> {
    DefRef {
      name,
      typ: self.typ,
      term: self.term,
      loc: self.loc,
      module: self.module,
    }
  }

  pub fn to_var_ref(&self) -> VarRef<'_> {
    VarRef::Free {
      term: self.term,
      typ: self.typ,
    }
  }

  fn to_update_ref(&self) -> VarRef<'_> {
    VarRef::UpdateRef {
      new_path: &self.name,
      typ: self.typ,
      term: self.term,
    }
  }
}

impl<'a, T: AsVarRef> From<&'a T> for VarRef<'a> {
  fn from(value: &'a T) -> Self {
    value.as_var_ref()
  }
}

impl<'a> AsVarRef for DefRef<'a> {
  fn as_var_ref(&self) -> VarRef<'a> {
    VarRef::Free {
      term: self.term,
      typ: self.typ,
    }
  }
}

impl<'a> Named for DefRef<'a> {
  fn name(&self) -> &ModulePath {
    &self.name
  }
}
#[derive(Clone, Debug, PartialEq)]
pub struct Infix {
  operator: Operator,
  name: ModulePath,
}

impl Display for Infix {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let Infix { operator, name } = self;
    write!(f, "({operator}) := {name}")
  }
}

pub fn infix(operator: Operator, name: ModulePath) -> Infix {
  Infix { operator, name }
}

/// Declarations in a module
#[derive(Clone, Debug, PartialEq)]
pub enum Decl {
  Use(Use),
  Open(Open),
  Def(Def),
  Type(Inductive),
  /// Instance
  Ins(Instance),
  Infix(Infix),
}

impl Decl {
  pub fn to_ref(&self) -> &ModulePath {
    match self {
      Decl::Def(def) => &def.name,
      Decl::Type(induct) => induct.name(),
      Decl::Infix(i) => &i.name,
      Decl::Use(use_) => &use_.module_path,
      Decl::Ins(instance) => &instance.name,
      Decl::Open(open) => &open.module_path,
    }
  }
}
