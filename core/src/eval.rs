pub mod native;
#[cfg(test)]
pub mod test;
pub mod r#type;

use std::fmt::Display;

use crate::eval::native::{NativeError, native_execute};
use crate::eval::r#type::TypeError;
use crate::term::Term::Forall;
use crate::term::module::{Scope, ScopeError};
use crate::term::{
  Constructor, Identifier, ModulePath, Native, Par, SourceRange, ann, case, forall, if_term, lam,
  lam_index, let_term, match_term, mpt, param, pi_name,
};
use crate::term::{
  Literal,
  NameRef::{self, Id, Index},
  Param,
  Term::{self, Ann, App, Con, Ctx, Lam, Let, Lit, Ntv, Pi, Type, Var},
  apps, id,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
  Scope(ScopeError),
  Eval { message: String },
  Type(TypeError),
  Native(NativeError),
  Context { loc: SourceRange, err: Box<Error> },
}

impl From<TypeError> for Error {
  fn from(value: TypeError) -> Self {
    Error::Type(value)
  }
}
impl From<ScopeError> for Error {
  fn from(value: ScopeError) -> Self {
    Error::Scope(value)
  }
}
impl From<NativeError> for Error {
  fn from(value: NativeError) -> Self {
    Error::Native(value)
  }
}

impl Display for Error {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Error::Scope(scope_error) => write!(f, "scope: {scope_error}"),
      Error::Eval { message } => write!(f, "eval: {message}"),
      Error::Type(type_error) => write!(f, "type: {type_error}"),
      Error::Native(native_error) => write!(f, "native: {native_error}"),
      Error::Context { loc, err } => {
        write!(f, "{err} at {}:{}", loc.start.line, loc.start.line_offset)
      }
    }
  }
}

fn err(message: String) -> Error {
  Error::Eval { message }
}

#[derive(Clone, PartialEq, Default)]
pub struct EvalOptions {
  pub debug: bool,
}

fn resolve_name<'a>(name: &'a NameRef, scope: &'a Scope<'a>) -> Result<&'a Term, Error> {
  let term = scope.resolve_name(name)?;
  Ok(term)
}

/// Run a beta reduction
pub fn eval(mut main_term: Term, scope: &Scope, options: &EvalOptions) -> Result<Term, Error> {
  loop {
    main_term = apply_dot_macro(main_term);
    main_term = match main_term {
      App { fun, arg } => eval_app(*fun, *arg, scope, &options)?,
      Let {
        name,
        value,
        body,
        typ: _,
      } => substitute(*body, &Id(name), &value),
      Var { name } => resolve_name(&name, scope)?.clone(),
      Ntv { native } => native_execute(native, scope).map_err(|e| Error::Native(e))?,
      Lit {
        value: Literal::Match { value, cases },
      } => {
        let value = eval(*value, scope, &options)?;
        if let Con(Constructor {
          name,
          typ_name: _,
          args,
          num_args,
        }) = &value
        {
          if let Some(case) = cases.iter().find(|case| name == &case.name)
            && case.args.len() == *num_args
          {
            let mut term = *case.value.clone();
            for (ide, arg) in case.args.clone().into_iter().zip(args) {
              if let Some(arg) = arg {
                term = substitute(term, &Id(ide), &arg);
              } else {
                return Err(err(format!("incomplete con {}", value)));
              }
            }
            term
          } else {
            return Err(err(format!("no matching branch for: {}", value)));
          }
        } else {
          return Err(err(format!("can only match on inductives, found: {value}")));
        }
      }
      Lit {
        value: Literal::If { value, then, els },
      } => {
        let value = eval(*value, scope, &options)?;
        let b = recognize_bool(&value)?;
        if b { *then } else { *els }
      }
      Ctx { loc: _, term } => *term,
      _ => break,
    };
    if options.debug {
      println!("debug: {}", main_term);
    }
  }
  Ok(main_term)
}

pub fn recognize_bool(value: &Term) -> Result<bool, Error> {
  if let Con(Constructor {
    name,
    typ_name,
    args: _,
    num_args: _,
  }) = &value
  {
    if typ_name == &mpt("Bool") {
      if name == &id("true") {
        return Ok(true);
      } else if name == &id("false") {
        return Ok(false);
      }
    }
  }
  Err(err(format!("expected Bool found: {value}")))
}

fn substitute_lam(param: Par, body: Term, arg: &Term) -> Term {
  match param {
    Par::P(param) => {
      let term = substitute(body, &Id(param.name.clone()), arg);
      term
    }
    Par::I { typ: _ } => {
      let term = substitute(body, &Index(1), arg);
      term
    }
  }
}
fn native_apply_arg(mut native: Native, index: usize, term: Term) -> Option<Term> {
  if index > 0 && index <= native.num_args {
    let index = native.num_args - index;
    native.args[index] = Some(term);
    Some(Term::Ntv { native })
  } else {
    None
  }
}

fn apply_dot_macro(term: Term) -> Term {
  use NameRef::{Id, Op, P};
  if let App {
    ref fun,
    arg: ref arg2,
  } = term
    && let App {
      fun: oper,
      arg: arg1,
    } = &**fun
    && let Var { name: Op(op) } = &**oper
    && op.as_str() == "."
    && let Var { name: name_ref1 } = &**arg1
    && let Var { name: name_ref2 } = &**arg2
  {
    match (name_ref1.clone(), name_ref2.clone()) {
      (Id(name1), Id(name2)) => Var {
        name: P(ModulePath::new(vec![name1, name2])),
      },
      (P(path), Id(name2)) => Var {
        name: P(path.append(vec![name2])),
      },
      (P(path1), P(path2)) => Var {
        name: P(path1.append(path2.to_vec())),
      },
      (Id(name1), P(path2)) => Var {
        name: P(ModulePath::new(vec![name1]).append(path2.to_vec())),
      },
      _ => term,
    }
  } else {
    term
  }
}

fn unwrap_decl_lambda(arg: Term, name: &NameRef, scope: &Scope) -> Result<Term, Error> {
  let term = scope.resolve_name(&name).map_err(Error::Scope)?;
  match term {
    Lam { param, body } => Ok(substitute_lam(param.clone(), *body.clone(), &arg)),
    _ => Err(err(format!("expected lambda def found {term}"))),
  }
}

fn eval_app(fun: Term, arg: Term, scope: &Scope, options: &EvalOptions) -> Result<Term, Error> {
  let fun = eval(fun, scope, options)?;
  let arg = eval(arg, scope, options)?;
  if options.debug {
    println!("eval_app: fun={} arg={}", fun, arg);
  }
  match fun {
    Var { name } => unwrap_decl_lambda(arg, &name, scope),
    Lam { param, body } => Ok(substitute_lam(param, *body, &arg)),
    Ntv { native } => {
      let index = native.args.iter().filter(|a| a.is_some()).count() + 1;
      if let Some(result) = native_apply_arg(native, index, arg) {
        let result_eval = eval(result, scope, options)?;
        Ok(result_eval)
      } else {
        Err(err(format!(
          "native function applied to too many arguments"
        )))
      }
    }
    App {
      fun: fun2,
      arg: arg_internal,
    } => {
      let f = eval_app(*fun2, *arg_internal, scope, options)?;
      let f2 = eval_app(f, arg, scope, options)?;
      Ok(f2)
    }
    _ => Err(err(format!(
      "expected function found {} {}",
      fun.node_type(),
      fun
    ))),
  }
}

pub fn rename_variable(body: Term, new_name: Identifier, old_name: Identifier) -> Term {
  let new_body = substitute(
    body,
    &NameRef::Id(old_name),
    &Var {
      name: NameRef::Id(new_name),
    },
  );
  new_body
}

fn substitute(term: Term, nref: &NameRef, new_term: &Term) -> Term {
  match term {
    Lam { param, body } => match param {
      Par::P(param) => {
        if let Id(old_name) = nref
          && &param.name == old_name
        {
          let new_name = param.name.rename();
          let new_param = Param {
            name: new_name.clone(),
            typ: param.typ.clone(),
          };
          let new_body = rename_variable(*body, new_name, old_name.clone());
          let term = substitute(new_body, nref, &new_term);
          lam(new_param, term)
        } else {
          let term = substitute(*body, nref, new_term);
          lam(param.clone(), term)
        }
      }
      Par::I { typ } => {
        if let Index(i) = nref {
          let term = substitute(*body, &Index(i + 1), new_term);
          lam_index(*typ, term)
        } else {
          let term = substitute(*body, nref, new_term);
          lam_index(*typ, term)
        }
      }
    },
    Var { ref name } => {
      if name == nref {
        new_term.clone()
      } else {
        term.clone()
      }
    }
    Pi { arg, ret, arg_name } => {
      let arg = substitute(*arg, nref, new_term);
      let ret = substitute(*ret, nref, new_term);
      pi_name(arg_name, arg, ret)
    }
    App { fun, arg } => apps(
      substitute(*fun, nref, &new_term),
      vec![substitute(*arg, nref, &new_term)],
    ),
    Ntv { ref native } => {
      if let Index(index) = nref {
        native_apply_arg(native.clone(), *index, new_term.clone()).unwrap_or(term)
      } else {
        term
      }
    }
    Con(Constructor {
      ref typ_name,
      ref args,
      ref name,
      num_args,
    }) => {
      if let Index(i) = nref
        && i > &0usize
        && i <= &num_args
      {
        let mut args = args.clone();
        let index = num_args - *i;
        args[index] = Some(new_term.clone());
        Con(Constructor {
          name: name.clone(),
          typ_name: typ_name.clone(),
          args,
          num_args,
        })
      } else {
        term
      }
    }
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = substitute(*value, nref, new_term);
      let cases = cases
        .into_iter()
        .map(|c| {
          case(
            c.name.clone(),
            c.args.clone(),
            substitute(*c.value, nref, new_term),
          )
        })
        .collect();
      match_term(value, cases)
    }
    Lit {
      value: Literal::If { value, then, els },
    } => {
      let value = substitute(*value, nref, new_term);
      let then = substitute(*then, nref, new_term);
      let els = substitute(*els, nref, new_term);
      if_term(value, then, els)
    }
    Lit { value: _ } => term,
    Ctx { loc, term } => Ctx {
      loc,
      term: Box::new(substitute(*term, nref, new_term)),
    },
    Forall { name, typ, body } => {
      let typ = substitute(*typ, nref, new_term);
      let body = substitute(*body, nref, new_term);
      forall(param(name, typ), body)
    }
    Let {
      name,
      typ,
      value,
      body,
    } => {
      let typ = substitute(*typ, nref, new_term);
      let value = substitute(*value, nref, new_term);
      let body = substitute(*body, nref, new_term);
      let_term(name, typ, value, body)
    }
    Term::Prop => term,
    Type { universe: _ } => term,
    Term::Hole => term,
    Ann { term, typ } => {
      let term = substitute(*term, nref, new_term);
      let typ = substitute(*typ, nref, new_term);
      ann(term, typ)
    }
  }
}
