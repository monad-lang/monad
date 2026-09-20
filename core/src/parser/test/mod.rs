use super::*;
use crate::{
  Map, similar,
  term::{
    AttrArg, Attribute, Decl, LetVar, Literal, ModulePath, NamePath, NameRef, Named, Native,
    NumSuffix, Par, QualifiedName, Term, Visibility, app, app2, dpar, forall, induct_constructor,
    mpt, mpv, num, num_suffix, oper, par, pi, pi_var, pvar, str, stru_field,
    test::{decl_def, decl_inductive, decl_infix, decl_open, decl_use, defs_class},
    typ, var,
  },
};

pub fn parse_type(input: &str) -> Term {
  let t = type_top_expression::<()>(input.into()).finish().unwrap().1;
  t
}

/// Term-level name shorthand — decl names (`def`/`class`/`inductive`/
/// constructor owner) are `NamePath`s since the qualified-names split;
/// `mpt`/`mp` stay the `ModulePath` (file-level) builders.
fn npt(s: &str) -> NamePath {
  NamePath::top(s)
}

mod attributes;
mod basics;
mod declarations;
mod do_notation;
mod docstrings;
mod expressions;
mod lists;
mod numbers;
mod position;
mod regression;
mod tuples;
mod types;
