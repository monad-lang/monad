use std::fmt::Display;

use crate::{
  Map,
  term::{Identifier, Litteral, Native, Term, id, module::Scope, unit},
};

#[derive(Debug, Clone, PartialEq)]
pub enum NativeError {
  MissingArgs,
  NotFound(Identifier),
  Custom(String),
}
impl Display for NativeError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      NativeError::MissingArgs => write!(f, "Missing args"),
      NativeError::NotFound(identifier) => write!(f, "native {identifier} not found"),
      NativeError::Custom(c) => write!(f, "{c}"),
    }
  }
}

pub fn println(terms: Vec<Term>) -> Result<Term, String> {
  if terms.len() < 2
    && let Term::Lit {
      value: Litteral::Str { value: s },
    } = &terms[0]
  {
    println!("{}", s);
  }
  Ok(unit())
}

pub fn num_add(terms: Vec<Term>) -> Result<Term, String> {
  if terms.len() >= 2 {
    if let Term::Lit {
      value: Litteral::Num { value: a },
    } = &terms[0]
      && let Term::Lit {
        value: Litteral::Num { value: b },
      } = &terms[1]
    {
      let value = a + b;
      Ok(Term::Lit {
        value: Litteral::Num { value },
      })
    } else {
      Err(format!(
        "add error: wrong type of args first={} second={}",
        terms[0], terms[1]
      ))
    }
  } else {
    Err("add error: too few args".into())
  }
}

pub type NativeFun = fn(Vec<Term>) -> Result<Term, String>;

pub fn load_native_funs() -> Map<Identifier, NativeFun> {
  let v: Vec<(Identifier, NativeFun)> = vec![(id("println"), println), (id("num_add"), num_add)];
  v.into_iter().collect()
}

pub fn native_execute(native: Native, scope: &Scope) -> Result<Term, NativeError> {
  let native_fun = scope
    .global()
    .get_native(&native.native_name)
    .ok_or_else(|| NativeError::NotFound(native.native_name.clone()))?;
  let args: Vec<Term> = native.args.into_iter().filter_map(|f| f).collect();
  if args.len() == native.num_args {
    (native_fun)(args).map_err(NativeError::Custom)
  } else {
    Err(NativeError::MissingArgs)
  }
}
