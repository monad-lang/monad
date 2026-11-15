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

/// Enabled features, as `(mote, feature)` pairs, plus the ones a `not`
/// token SUBTRACTED. `suppressed` is kept rather than applied eagerly so
/// `with_manifest_features` can consult it: `default` is added there, after
/// `parse_features` has run, and subtracting it is the whole reason the
/// token exists.
///
/// Mirrors `CfgEnv.for_mote` (`lang/src/cfg.mo`); the two must agree, and
/// the same test names pin both.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct CfgSet {
  features: BTreeSet<(String, String)>,
  suppressed: BTreeSet<(String, String)>,
}

impl CfgSet {
  /// Parse a `MONAD_FEATURES`/`--features` list: comma- or
  /// whitespace-separated `mote/feature` items.
  ///
  /// A `not` TOKEN before an item subtracts it instead of adding it:
  ///
  /// ```text
  /// MONAD_FEATURES="not cli/default"        // the whole default set off
  /// MONAD_FEATURES="not cli/lsp, cli/doc"   // lsp off, doc on
  /// ```
  ///
  /// `not` is Monad's own negation vocabulary -- the same word
  /// `#[cfg [not {feature := "on"}]]` uses and `CfgPred::Not` implements --
  /// and it is a separate whitespace/comma-delimited token, so the split
  /// below carries it through with no lexer change. It is lowercase-only,
  /// matching the predicate grammar's own comparison. A trailing `not`
  /// with nothing after it is dropped rather than treated as an item, so a
  /// stray token cannot silently suppress the wrong thing.
  pub fn parse_features(spec: &str) -> Result<CfgSet, String> {
    let mut features = BTreeSet::new();
    let mut suppressed = BTreeSet::new();
    let mut negating = false;
    for item in spec.split(|c: char| c == ',' || c.is_whitespace()) {
      if item.is_empty() {
        continue;
      }
      if item == "not" {
        negating = true;
        continue;
      }
      let target = if negating {
        &mut suppressed
      } else {
        &mut features
      };
      negating = false;
      match item.split_once('/') {
        Some((mote, feat)) if !mote.is_empty() && !feat.is_empty() && !feat.contains('/') => {
          target.insert((mote.to_owned(), feat.to_owned()));
        }
        _ => {
          return Err(format!(
            "malformed feature `{item}`: expected `mote/feature`"
          ));
        }
      }
    }
    Ok(CfgSet {
      features,
      suppressed,
    })
  }

  pub fn enable(&mut self, mote: &str, feature: &str) {
    self.features.insert((mote.to_owned(), feature.to_owned()));
  }

  /// Whether `feature` of `mote` was subtracted by a `not` token. A
  /// subtracted name is never in the answer, whichever route it would have
  /// taken in.
  fn is_suppressed(&self, mote: &str, feature: &str) -> bool {
    self
      .suppressed
      .contains(&(mote.to_owned(), feature.to_owned()))
  }

  /// This set plus `mote`'s manifest features: its `default` (when
  /// declared), and every plain feature an enabled one lists in `table`
  /// (`[features]`), transitively. `dep:x` and `x/f` items name
  /// dependencies, not this mote's features, and are not followed here.
  ///
  /// THE SUPPRESSION IS APPLIED TWICE, and both halves are load-bearing --
  /// dropping from `work` alone is a bug `cfg_not_ordinary_feature_wins`
  /// caught:
  ///
  ///   * BEFORE expansion, so `not cli/default` stops `default` from being
  ///     expanded at all. Filtering only the output would delete the name
  ///     `default` while leaving everything it pulled in -- the opposite
  ///     of turning it off.
  ///   * AFTER expansion, so `not cli/x` still wins when `x` is reachable
  ///     transitively (`default` -> `y` -> `x`). Dropping it from `work`
  ///     cannot help there: `x` is not IN `work`, it is derived from it,
  ///     and the loop below would put it straight back.
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
      .filter(|f| !self.is_suppressed(mote, f))
      .collect();
    if table.contains_key("default") && !self.is_suppressed(mote, "default") {
      work.push("default".to_owned());
    }
    while let Some(f) = work.pop() {
      for item in table.get(&f).into_iter().flatten() {
        if !item.contains(':')
          && !item.contains('/')
          && !out.has_feature(mote, item)
          && !self.is_suppressed(mote, item)
        {
          work.push(item.clone());
        }
      }
      out.enable(mote, &f);
    }
    // Second application: a feature already in `features` because a caller
    // put it there, rather than because `work` derived it, is filtered here.
    let dropped: Vec<(String, String)> = out
      .suppressed
      .iter()
      .filter(|(m, _)| m == mote)
      .cloned()
      .collect();
    for pair in dropped {
      out.features.remove(&pair);
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

  // ─── The `not` off-switch ────────────────────────────────────────────
  //
  // The same cases `lang/src/cfg_tests.mo` pins, on the same table, so the
  // two readers cannot drift. `not` SUBTRACTS, and a subtracted name is
  // never in the answer whichever route it would have taken in.

  fn table() -> BTreeMap<String, Vec<String>> {
    [
      ("default".to_owned(), vec!["y".to_owned()]),
      ("y".to_owned(), vec!["x".to_owned(), "dep:z".to_owned()]),
      ("x".to_owned(), vec![]),
      ("w".to_owned(), vec![]),
    ]
    .into_iter()
    .collect()
  }

  fn features(spec: &str) -> Vec<String> {
    CfgSet::parse_features(spec)
      .unwrap()
      .with_manifest_features("m", &table())
      .features
      .iter()
      .filter(|(m, _)| m == "m")
      .map(|(_, f)| f.clone())
      .collect()
  }

  #[test]
  fn cfg_not_default_turns_it_off() {
    assert!(features("not m/default").is_empty());
  }

  #[test]
  fn cfg_not_other_mote_is_inert() {
    assert_eq!(features("not other/q"), vec!["default", "x", "y"]);
  }

  #[test]
  fn cfg_not_ordinary_feature_wins_over_default() {
    assert_eq!(features("not m/x"), vec!["default", "y"]);
  }

  #[test]
  fn cfg_not_mixes_with_additive() {
    assert_eq!(features("not m/default, m/w"), vec!["w"]);
  }

  #[test]
  fn cfg_not_dangling_is_ignored() {
    assert_eq!(features("not"), vec!["default", "x", "y"]);
  }

  #[test]
  fn cfg_not_comma_separated() {
    assert!(features("not,m/default").is_empty());
  }

  #[test]
  fn cfg_not_double_is_not_a_feature() {
    assert!(features("not not m/default").is_empty());
  }

  /// The off-switch reaches a `#[cfg]` predicate, which is the point.
  #[test]
  fn cfg_not_default_filters_decls() {
    let set = CfgSet::parse_features("not m/default")
      .unwrap()
      .with_manifest_features("m", &table());
    assert_eq!(decl_names(SRC, &set), vec!["b", "c"]);
  }
}
