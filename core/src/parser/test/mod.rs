use super::*;
use crate::{
  Map, similar,
  term::{
    AttrArg, Attribute, Decl, LetVar, Literal, Named, Native, Par, Term, Visibility, app, app2,
    dpar, forall, induct_constructor, mp, mpt, mpv, num, oper, par, pi, pi_var, pvar, str,
    stru_field,
    test::{decl_def, decl_inductive, decl_infix, decl_open, decl_use, defs_class},
    typ, var,
  },
};

pub fn parse_type(input: &str) -> Term {
  let t = type_top_expression::<()>(input.into()).finish().unwrap().1;
  t
}

mod attributes;
mod basics;
mod declarations;
mod do_notation;
mod docstrings;
mod expressions;
mod lists;
mod position;
mod regression;
mod tuples;
mod types;
