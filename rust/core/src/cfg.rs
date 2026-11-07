//! `#[cfg ...]` predicates over mote features.
//!
//! Grammar (`plans/implementations/attributes-deprecated-and-cfg.md`):
//! `#[cfg P1 P2 ...]` is an implicit `all`, where each `P` is a flag
//! (`test`), a key/value block (`{feature := "sys"}`), or a combinator
//! group (`[not P]`, `[all P...]`, `[any P...]`).
//!
//! The `test` flag is evaluated by the existing test-mode filters, so the
//! load-time filter here drops a declaration only when its predicate is
//! false whether or not `test` holds.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::RwLock;

use crate::term::{AttrArg, Attribute, Decl};

#[derive(Debug, Clone, PartialEq)]
pub enum CfgPred {
  Flag(String),
  KeyValue(String, String),
  Not(Box<CfgPred>),
  All(Vec<CfgPred>),
  Any(Vec<CfgPred>),
}

/// Enabled features, as `(mote, feature)` pairs.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct CfgSet {
  features: BTreeSet<(String, String)>,
}

impl CfgSet {
  /// Parse a `MONAD_FEATURES`/`--features` list: comma- or
  /// whitespace-separated `mote/feature` items.
  pub fn parse_features(spec: &str) -> Result<CfgSet, String> {
    let mut features = BTreeSet::new();
    for item in spec.split(|c: char| c == ',' || c.is_whitespace()) {
      if item.is_empty() {
        continue;
      }
      match item.split_once('/') {
        Some((mote, feat)) if !mote.is_empty() && !feat.is_empty() && !feat.contains('/') => {
          features.insert((mote.to_owned(), feat.to_owned()));
        }
        _ => {
          return Err(format!(
            "malformed feature `{item}`: expected `mote/feature`"
          ));
        }
      }
    }
    Ok(CfgSet { features })
  }

  pub fn enable(&mut self, mote: &str, feature: &str) {
    self.features.insert((mote.to_owned(), feature.to_owned()));
  }

  /// This set plus `mote`'s manifest features: its `default` (when
  /// declared), and every plain feature an enabled one lists in `table`
  /// (`[features]`), transitively. `dep:x` and `x/f` items name
  /// dependencies, not this mote's features, and are not followed here.
  pub fn with_manifest_features(
    &self,
    mote: &str,
    table: &BTreeMap<String, Vec<String>>,
  ) -> CfgSet {
    let mut out = self.clone();
    let mut work: Vec<String> = self
      .features
      .iter()
      .filter(|(m, _)| m == mote)
      .map(|(_, f)| f.clone())
      .collect();
    if table.contains_key("default") {
      work.push("default".to_owned());
    }
    while let Some(f) = work.pop() {
      for item in table.get(&f).into_iter().flatten() {
        if !item.contains(':') && !item.contains('/') && !out.has_feature(mote, item) {
          work.push(item.clone());
        }
      }
      out.enable(mote, &f);
    }
    out
  }

  pub fn has_feature(&self, mote: &str, feature: &str) -> bool {
    self
      .features
      .contains(&(mote.to_owned(), feature.to_owned()))
  }
}

static ACTIVE: RwLock<Option<CfgSet>> = RwLock::new(None);

/// The process-wide feature set: what `set_active` installed, else
/// `MONAD_FEATURES`, else empty.
pub fn active() -> CfgSet {
  if let Some(set) = ACTIVE.read().unwrap().as_ref() {
    return set.clone();
  }
  let set = match std::env::var("MONAD_FEATURES") {
    Ok(spec) => CfgSet::parse_features(&spec).unwrap_or_else(|e| {
      eprintln!("warning: MONAD_FEATURES: {e}");
      CfgSet::default()
    }),
    Err(_) => CfgSet::default(),
  };
  *ACTIVE.write().unwrap() = Some(set.clone());
  set
}

pub fn set_active(set: CfgSet) {
  *ACTIVE.write().unwrap() = Some(set);
}

impl CfgPred {
  /// The predicate of one `#[cfg ...]` attribute.
  pub fn parse(args: &[AttrArg]) -> Result<CfgPred, String> {
    let preds = args
      .iter()
      .map(Self::parse_one)
      .collect::<Result<Vec<_>, _>>()?;
    Ok(match <[CfgPred; 1]>::try_from(preds) {
      Ok([p]) => p,
      Err(preds) => CfgPred::All(preds),
    })
  }

  fn parse_one(arg: &AttrArg) -> Result<CfgPred, String> {
    match arg {
      AttrArg::Ident(id) => Ok(CfgPred::Flag(id.as_str().to_owned())),
      AttrArg::Named { name, value } => match value.as_ref() {
        AttrArg::Str(v) => Ok(CfgPred::KeyValue(name.as_str().to_owned(), v.clone())),
        _ => Err(format!("cfg: `{}` needs a string value", name.as_str())),
      },
      AttrArg::Group(items) => {
        let Some((AttrArg::Ident(head), rest)) = items.split_first() else {
          return Err("cfg: a `[...]` group must start with `not`, `all` or `any`".into());
        };
        let rest = rest
          .iter()
          .map(Self::parse_one)
          .collect::<Result<Vec<_>, _>>()?;
        match head.as_str() {
          "not" => match <[CfgPred; 1]>::try_from(rest) {
            Ok([p]) => Ok(CfgPred::Not(Box::new(p))),
            Err(_) => Err("cfg: `not` takes exactly one predicate".into()),
          },
          "all" => Ok(CfgPred::All(rest)),
          "any" => Ok(CfgPred::Any(rest)),
          other => Err(format!(
            "cfg: unknown combinator `{other}` (expected `not`, `all` or `any`)"
          )),
        }
      }
      AttrArg::Str(_) | AttrArg::Num(_) => {
        Err("cfg: expected a flag, `{key := \"value\"}` or a `[...]` group".into())
      }
    }
  }

  /// Evaluate for a declaration in `mote`. Unknown flags and keys are
  /// false, as in Rust.
  pub fn eval(&self, set: &CfgSet, mote: Option<&str>, test: bool) -> bool {
    match self {
      CfgPred::Flag(f) => f == "test" && test,
      CfgPred::KeyValue(k, v) => k == "feature" && mote.is_some_and(|m| set.has_feature(m, v)),
      CfgPred::Not(p) => !p.eval(set, mote, test),
      CfgPred::All(ps) => ps.iter().all(|p| p.eval(set, mote, test)),
      CfgPred::Any(ps) => ps.iter().any(|p| p.eval(set, mote, test)),
    }
  }

  fn mentions_feature(&self) -> bool {
    match self {
      CfgPred::Flag(_) => false,
      CfgPred::KeyValue(k, _) => k == "feature",
      CfgPred::Not(p) => p.mentions_feature(),
      CfgPred::All(ps) | CfgPred::Any(ps) => ps.iter().any(Self::mentions_feature),
    }
  }
}

/// The attributes a declaration carries, if its variant has any.
pub fn decl_attributes(decl: &Decl) -> &[Attribute] {
  match decl {
    Decl::Use(u) => &u.attributes,
    Decl::Open(o) => &o.attributes,
    Decl::ScopedOpen { attributes, .. } => attributes,
    Decl::Def(d) | Decl::DefMacro(d) => &d.attributes,
    Decl::Type(t) => &t.attributes,
    Decl::Ins(i) => &i.attributes,
    Decl::DeclGen(g) => &g.attributes,
    _ => &[],
  }
}

/// Whether any `#[cfg]` on `attrs` names a feature. Callers use this to
/// skip the manifest lookup for the common case.
pub fn mentions_feature(attrs: &[Attribute]) -> bool {
  attrs
    .iter()
    .filter(|a| a.name.as_str() == "cfg")
    .any(|a| CfgPred::parse(&a.args).is_ok_and(|p| p.mentions_feature()))
}

/// Keep a declaration unless one of its `#[cfg]`s is false both with and
/// without `test`. `#[cfg test]` alone is always kept here: the test-mode
/// filters own it.
///
/// A malformed predicate keeps the declaration and warns, matching
/// `CfgEnv.keep` (`lang/src/cfg.mo`). Dropping it would silently delete
/// code over a typo, and failing the load would make one bad attribute a
/// whole-file error; the unknown-attribute diagnostic in
/// `plans/implementations/attributes-deprecated-and-cfg.md` is where a typo
/// gets reported.
pub fn keep(attrs: &[Attribute], set: &CfgSet, mote: Option<&str>) -> bool {
  for a in attrs.iter().filter(|a| a.name.as_str() == "cfg") {
    match CfgPred::parse(&a.args) {
      Ok(p) => {
        if !p.eval(set, mote, true) && !p.eval(set, mote, false) {
          return false;
        }
      }
      Err(e) => eprintln!("warning: {e}; keeping the declaration"),
    }
  }
  true
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::parser::parse_file;

  fn decl_names(src: &str, set: &CfgSet) -> Vec<String> {
    let decls = parse_file(src).expect("parses").decls;
    decls
      .iter()
      .filter(|d| keep(decl_attributes(d.value()), set, Some("m")))
      .map(|d| match d.value() {
        Decl::Def(d) => d.name.to_string(),
        Decl::Use(u) => format!("use {}", u.module_path()),
        _ => "?".into(),
      })
      .collect()
  }

  const SRC: &str = r#"
#[cfg {feature := "x"}]
def a : I64 := 1

#[cfg [not {feature := "x"}]]
def b : I64 := 2

#[cfg test]
def c : I64 := 3

#[cfg [any {feature := "x"} {feature := "y"}]]
def d : I64 := 4

#[cfg [all {feature := "x"} {feature := "y"}]]
def e : I64 := 5

#[cfg {feature := "x"}]
use std::io {}
"#;

  #[test]
  fn cfg_feature_off() {
    assert_eq!(decl_names(SRC, &CfgSet::default()), vec!["b", "c"]);
  }

  #[test]
  fn cfg_feature_on() {
    let set = CfgSet::parse_features("m/x").unwrap();
    assert_eq!(decl_names(SRC, &set), vec!["a", "c", "d", "use std.io"]);
  }

  #[test]
  fn cfg_feature_of_another_mote_is_off() {
    let set = CfgSet::parse_features("other/x, m/y").unwrap();
    assert_eq!(decl_names(SRC, &set), vec!["b", "c", "d"]);
  }

  #[test]
  fn cfg_manifest_defaults_expand() {
    let table: BTreeMap<String, Vec<String>> = [
      ("default".to_owned(), vec!["y".to_owned()]),
      ("y".to_owned(), vec!["x".to_owned(), "dep:z".to_owned()]),
      ("x".to_owned(), vec![]),
    ]
    .into_iter()
    .collect();
    let set = CfgSet::default().with_manifest_features("m", &table);
    assert!(set.has_feature("m", "x") && set.has_feature("m", "y"));
    assert!(!set.has_feature("m", "dep:z"));
    assert_eq!(
      decl_names(SRC, &set),
      vec!["a", "c", "d", "e", "use std.io"]
    );
  }

  #[test]
  fn cfg_malformed() {
    assert!(CfgSet::parse_features("x").is_err());
    let decls = parse_file("#[cfg [maybe test]]\ndef a : I64 := 1\n")
      .unwrap()
      .decls;
    // Malformed keeps, like the self-hosted `CfgEnv.keep`.
    assert!(keep(
      decl_attributes(decls[0].value()),
      &CfgSet::default(),
      None
    ));
  }
}
