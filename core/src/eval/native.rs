use std::fmt::Display;

use crate::{
  Map,
  term::{Identifier, Litteral, Native, Term, id, io_term, module::Scope, unit},
};

#[derive(Debug, Clone, PartialEq)]
pub enum NativeError {
  MissingArgs { expected: usize, actual: usize },
  NotFound(Identifier),
  Custom(String),
}

use NativeError::*;

impl Display for NativeError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      MissingArgs { expected, actual } => {
        write!(
          f,
          "Too few args expected at least {} found {}",
          expected, actual
        )
      }
      NotFound(identifier) => write!(f, "native {identifier} not found"),
      Custom(c) => write!(f, "{c}"),
    }
  }
}

fn extract_string_at(terms: &Vec<Term>, index: usize) -> Result<String, NativeError> {
  if terms.len() > index {
    if let Term::Lit {
      value: Litteral::Str { value: s },
    } = &terms[index]
    {
      Ok(s.clone())
    } else {
      Err(Custom(format!("wrong type of args first={}", terms[index])))
    }
  } else {
    Err(MissingArgs {
      expected: index + 1,
      actual: terms.len(),
    })
  }
}
pub fn println(terms: Vec<Term>) -> Result<Term, NativeError> {
  let s = extract_string_at(&terms, 0)?;
  println!("{}", s);
  Ok(io_term(unit()))
}

fn extract_num_pair(terms: Vec<Term>) -> Result<(i64, i64), NativeError> {
  if terms.len() >= 2 {
    if let Term::Lit {
      value: Litteral::Num { value: a },
    } = &terms[0]
      && let Term::Lit {
        value: Litteral::Num { value: b },
      } = &terms[1]
    {
      Ok((*a, *b))
    } else {
      Err(Custom(format!(
        "wrong type of args first={} second={}",
        terms[0], terms[1]
      )))
    }
  } else {
    Err(MissingArgs {
      expected: 2,
      actual: terms.len(),
    })
  }
}

pub fn num_add(terms: Vec<Term>) -> Result<Term, NativeError> {
  let (a, b) = extract_num_pair(terms)?;
  let value = a + b;
  Ok(Term::Lit {
    value: Litteral::Num { value },
  })
}
pub fn num_mul(terms: Vec<Term>) -> Result<Term, NativeError> {
  let (a, b) = extract_num_pair(terms)?;
  let value = a * b;
  Ok(Term::Lit {
    value: Litteral::Num { value },
  })
}
pub fn num_sub(terms: Vec<Term>) -> Result<Term, NativeError> {
  let (a, b) = extract_num_pair(terms)?;
  let value = a - b;
  Ok(Term::Lit {
    value: Litteral::Num { value },
  })
}

pub type NativeFun = fn(Vec<Term>) -> Result<Term, NativeError>;

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
    (native_fun)(args)
  } else {
    Err(NativeError::MissingArgs {
      expected: native.num_args,
      actual: args.len(),
    })
  }
}
