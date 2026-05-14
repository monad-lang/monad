pub mod constraint;
pub mod macro_expand;
#[cfg(test)]
pub mod macro_test;
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
  lam_index, match_term, mpt, param, pi_name,
};
use crate::term::{
  Literal,
  NameRef::{self, Id, Index},
  Param,
  Term::{self, Ann, App, Con, Ctx, Lam, Lit, Ntv, Pi, Quote, Sort, Var},
  apps, id,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
  Scope(ScopeError),
  Eval(EvalError),
  Type(TypeError),
  Native(NativeError),
  Context { loc: SourceRange, err: Box<Error> },
}

#[derive(Debug, Clone, PartialEq)]
pub enum EvalError {
  IncompleteConstructor { value: Term },
  NoMatchingBranch { value: Term },
  NotAnInductive { value: Term },
  NotABool { value: Term },
  NotALambda { term: Term },
  NotAFunction { term: Term },
  StructLiteralNotDesugared,
  StructUpdateNotDesugared,
  NativeArgumentOverflow,
}

impl Display for EvalError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      EvalError::IncompleteConstructor { value } => {
        write!(f, "incomplete constructor application: {value}")
      }
      EvalError::NoMatchingBranch { value } => {
        write!(f, "no matching branch for: {value}")
      }
      EvalError::NotAnInductive { value } => {
        write!(f, "can only match on inductives, found: {value}")
      }
      EvalError::NotABool { value } => {
        write!(f, "expected Bool found: {value}")
      }
      EvalError::NotALambda { term } => {
        write!(f, "expected lambda definition found: {term}")
      }
      EvalError::NotAFunction { term } => {
        write!(f, "expected function found: {term}")
      }
      EvalError::StructLiteralNotDesugared => {
        write!(
          f,
          "struct literal reached evaluator without being desugared"
        )
      }
      EvalError::StructUpdateNotDesugared => {
        write!(f, "struct update reached evaluator without being desugared")
      }
      EvalError::NativeArgumentOverflow => {
        write!(f, "native function applied to too many arguments")
      }
    }
  }
}

impl From<&EvalError> for crate::diag::Diagnostic {
  fn from(err: &EvalError) -> Self {
    crate::diag::Diagnostic {
      severity: crate::diag::Severity::Error,
      message: err.to_string(),
      location: None,
      path: None,
      sub_diagnostics: vec![],
      suggestions: vec![],
      context_name: None,
    }
  }
}

impl Display for Error {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Error::Scope(scope_error) => write!(f, "scope: {scope_error}"),
      Error::Eval(eval_error) => write!(f, "eval: {eval_error}"),
      Error::Type(type_error) => write!(f, "type: {type_error}"),
      Error::Native(native_error) => write!(f, "native: {native_error}"),
      Error::Context { loc, err } => {
        write!(f, "{err} at {}:{}", loc.start.line, loc.start.column)
      }
    }
  }
}

fn wrap_error(error: Error, loc: Option<SourceRange>) -> Error {
  match loc {
    Some(loc) => Error::Context {
      loc,
      err: Box::new(error),
    },
    None => error,
  }
}

pub fn recognize_bool(value: &Term, loc: Option<SourceRange>) -> Result<bool, Error> {
  if let Con(Constructor {
    name,
    typ_name,
    args: _,
    num_args: _,
  }) = &value
    && typ_name == &mpt("Bool")
  {
    if name == &id("true") {
      return Ok(true);
    } else if name == &id("false") {
      return Ok(false);
    }
  }
  Err(wrap_error(
    Error::Eval(EvalError::NotABool {
      value: value.clone(),
    }),
    loc,
  ))
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

impl From<&Error> for crate::diag::Diagnostic {
  fn from(err: &Error) -> Self {
    match err {
      Error::Scope(se) => {
        let mut diag: crate::diag::Diagnostic = se.into();
        if diag.message.starts_with("scope: ") {
          diag.message = diag.message["scope: ".len()..].to_string();
        }
        diag
      }
      Error::Eval(ee) => {
        let mut diag: crate::diag::Diagnostic = ee.into();
        diag.message = format!("eval: {}", diag.message);
        diag
      }
      Error::Type(te) => te.into(),
      Error::Native(ne) => {
        let mut diag: crate::diag::Diagnostic = ne.into();
        diag.message = format!("native: {}", diag.message);
        diag
      }
      Error::Context { loc, err } => {
        let mut diag: crate::diag::Diagnostic = err.as_ref().into();
        diag.location = Some(loc.clone());
        diag
      }
    }
  }
}

#[derive(Clone, PartialEq, Default)]
pub struct EvalOptions {
  pub debug: bool,
  pub use_colors: bool,
}

fn resolve_name<'a>(name: &'a NameRef, scope: &'a Scope<'a>) -> Result<&'a Term, Error> {
  let term = scope.resolve_name(name)?;
  Ok(term)
}

/// Run a beta reduction
pub fn eval(main_term: Term, scope: &Scope, options: &EvalOptions) -> Result<Term, Error> {
  eval_inner(main_term, scope, options, None)
}

fn eval_inner(
  mut main_term: Term,
  scope: &Scope,
  options: &EvalOptions,
  mut current_loc: Option<SourceRange>,
) -> Result<Term, Error> {
  loop {
    main_term = apply_dot_macro(main_term);
    main_term = match main_term {
      Ctx { loc, term } => {
        if current_loc.is_none() {
          current_loc = Some(loc);
        }
        *term
      }
      App { fun, arg } => {
        let loc = current_loc.take();
        eval_app(*fun, *arg, scope, options, loc)?
      }
      Var { name } => {
        let mut term = resolve_name(&name, scope)?.clone();
        // Strip forall wrappers — the type checker has already instantiated
        // forall parameters for class methods, but the stored term retains them
        while let Term::Forall { body, .. } = term {
          term = *body;
        }
        term
      }
      Ntv { native } => {
        let loc = current_loc.take();
        native_execute(native, scope).map_err(|e| wrap_error(Error::Native(e), loc))?
      }
      Lit {
        value: Literal::Match { value, cases },
      } => {
        let loc = current_loc.take();
        let value = eval_inner(*value, scope, options, loc.clone())?;
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
              if ide.as_str() == "_" {
                continue;
              }
              if let Some(arg) = arg {
                term = substitute(term, &Id(ide), arg);
              } else {
                return Err(wrap_error(
                  Error::Eval(EvalError::IncompleteConstructor {
                    value: value.clone(),
                  }),
                  loc.clone(),
                ));
              }
            }
            term
          } else {
            return Err(wrap_error(
              Error::Eval(EvalError::NoMatchingBranch {
                value: value.clone(),
              }),
              loc.clone(),
            ));
          }
        } else {
          return Err(wrap_error(
            Error::Eval(EvalError::NotAnInductive {
              value: value.clone(),
            }),
            loc.clone(),
          ));
        }
      }
      Lit {
        value: Literal::If { value, then, els },
      } => {
        let loc = current_loc.take();
        let value = eval_inner(*value, scope, options, loc.clone())?;
        let b = recognize_bool(&value, loc)?;
        if b { *then } else { *els }
      }
      Quote { term } => Term::Lit {
        value: Literal::Term(term),
      },
      Lit {
        value: Literal::StructLit { .. },
      } => {
        let loc = current_loc.take();
        return Err(wrap_error(
          Error::Eval(EvalError::StructLiteralNotDesugared),
          loc,
        ));
      }
      Lit {
        value: Literal::StructUpdate { .. },
      } => {
        let loc = current_loc.take();
        return Err(wrap_error(
          Error::Eval(EvalError::StructUpdateNotDesugared),
          loc,
        ));
      }
      _ => break,
    };
    if options.debug {
      println!("debug: {}", main_term);
    }
  }
  Ok(main_term)
}

fn substitute_lam(param: Par, body: Term, arg: &Term) -> Term {
  match param {
    Par::P(param) => substitute(body, &Id(param.name.clone()), arg),
    Par::I { typ: _, .. } => substitute(body, &Index(1), arg),
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

pub fn apply_dot_macro(term: Term) -> Term {
  // Quote bodies are data — do not expand dots inside them
  if let Quote { .. } = term {
    return term;
  }
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

/// Recursively apply the dot macro to all subterms
pub fn apply_dot_macro_recursive(term: Term) -> Term {
  use crate::term::{
    Literal,
    Term::{Ann, App, Ctx, Lam, Lit, Pi},
  };
  let term = match term {
    App { fun, arg } => {
      let fun = apply_dot_macro_recursive(*fun);
      let arg = apply_dot_macro_recursive(*arg);
      App {
        fun: Box::new(fun),
        arg: Box::new(arg),
      }
    }
    Lam { param, body } => {
      let body = apply_dot_macro_recursive(*body);
      Lam {
        param,
        body: Box::new(body),
      }
    }
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = apply_dot_macro_recursive(*value);
      let cases = cases
        .into_iter()
        .map(|c| case(c.name, c.args, apply_dot_macro_recursive(*c.value)))
        .collect();
      Lit {
        value: Literal::Match {
          value: Box::new(value),
          cases,
        },
      }
    }
    Lit {
      value: Literal::If { value, then, els },
    } => {
      let value = apply_dot_macro_recursive(*value);
      let then = apply_dot_macro_recursive(*then);
      let els = apply_dot_macro_recursive(*els);
      Lit {
        value: Literal::If {
          value: Box::new(value),
          then: Box::new(then),
          els: Box::new(els),
        },
      }
    }
    Forall { name, typ, body } => {
      let typ = apply_dot_macro_recursive(*typ);
      let body = apply_dot_macro_recursive(*body);
      Forall {
        name,
        typ: Box::new(typ),
        body: Box::new(body),
      }
    }
    Pi {
      arg,
      ret,
      arg_name,
      mult,
    } => {
      let arg = apply_dot_macro_recursive(*arg);
      let ret = apply_dot_macro_recursive(*ret);
      Pi {
        arg: Box::new(arg),
        ret: Box::new(ret),
        arg_name,
        mult,
      }
    }
    Ann { term, typ } => {
      let term = apply_dot_macro_recursive(*term);
      let typ = apply_dot_macro_recursive(*typ);
      Ann {
        term: Box::new(term),
        typ: Box::new(typ),
      }
    }
    Lit {
      value: Literal::StructLit { fields },
    } => {
      let fields = fields
        .into_iter()
        .map(|(k, v)| (k, apply_dot_macro_recursive(v)))
        .collect();
      Term::Lit {
        value: Literal::StructLit { fields },
      }
    }
    Lit {
      value: Literal::StructUpdate { base, fields },
    } => {
      let fields = fields
        .into_iter()
        .map(|(k, v)| (k, apply_dot_macro_recursive(v)))
        .collect();
      Term::Lit {
        value: Literal::StructUpdate { base, fields },
      }
    }
    Ctx { loc, term } => {
      let term = apply_dot_macro_recursive(*term);
      Ctx {
        loc,
        term: Box::new(term),
      }
    }
    t => t,
  };
  apply_dot_macro(term)
}

fn unwrap_decl_lambda(
  arg: Term,
  name: &NameRef,
  scope: &Scope,
  loc: Option<SourceRange>,
) -> Result<Term, Error> {
  let term = scope.resolve_name(name).map_err(Error::Scope)?;
  match term {
    Lam { param, body } => Ok(substitute_lam(param.clone(), *body.clone(), &arg)),
    _ => Err(wrap_error(
      Error::Eval(EvalError::NotALambda { term: term.clone() }),
      loc,
    )),
  }
}

fn eval_app(
  fun: Term,
  arg: Term,
  scope: &Scope,
  options: &EvalOptions,
  loc: Option<SourceRange>,
) -> Result<Term, Error> {
  let fun = eval_inner(fun, scope, options, loc.clone())?;
  let arg = eval_inner(arg, scope, options, loc.clone())?;
  if options.debug {
    println!("eval_app: fun={} arg={}", fun, arg);
  }
  match fun {
    Var { name } => unwrap_decl_lambda(arg, &name, scope, loc.clone()),
    Lam { param, body } => Ok(substitute_lam(param, *body, &arg)),
    Ntv { native } => {
      let index = native.args.iter().filter(|a| a.is_some()).count() + 1;
      if let Some(result) = native_apply_arg(native, index, arg) {
        let result_eval = eval_inner(result, scope, options, loc.clone())?;
        Ok(result_eval)
      } else {
        Err(wrap_error(
          Error::Eval(EvalError::NativeArgumentOverflow),
          loc.clone(),
        ))
      }
    }
    App {
      fun: fun2,
      arg: arg_internal,
    } => {
      let f = eval_app(*fun2, *arg_internal, scope, options, loc.clone())?;
      let f2 = eval_app(f, arg, scope, options, loc.clone())?;
      Ok(f2)
    }
    _ => Err(wrap_error(
      Error::Eval(EvalError::NotAFunction { term: fun.clone() }),
      loc.clone(),
    )),
  }
}

pub fn rename_variable(body: Term, new_name: Identifier, old_name: Identifier) -> Term {
  substitute(
    body,
    &NameRef::Id(old_name),
    &Var {
      name: NameRef::Id(new_name),
    },
  )
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
            mult: param.mult.clone(),
            default: param.default.clone(),
          };
          let new_body = rename_variable(*body, new_name, old_name.clone());
          let term = substitute(new_body, nref, new_term);
          lam(new_param, term)
        } else {
          let term = substitute(*body, nref, new_term);
          lam(param.clone(), term)
        }
      }
      Par::I { typ, .. } => {
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
    Pi {
      arg, ret, arg_name, ..
    } => {
      let arg = substitute(*arg, nref, new_term);
      let ret = substitute(*ret, nref, new_term);
      pi_name(arg_name, arg, ret)
    }
    App { fun, arg } => apps(
      substitute(*fun, nref, new_term),
      vec![substitute(*arg, nref, new_term)],
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
      } else if let Id(_) = nref {
        let args = args
          .iter()
          .map(|a| a.as_ref().map(|a| substitute(a.clone(), nref, new_term)))
          .collect();
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
          // Skip substitution in case body if any pattern arg shadows nref
          if c
            .args
            .iter()
            .any(|a| Some(a.clone()) == nref.as_id().cloned())
          {
            c
          } else {
            case(
              c.name.clone(),
              c.args.clone(),
              substitute(*c.value, nref, new_term),
            )
          }
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
    Lit {
      value: Literal::StructLit { fields },
    } => {
      let fields = fields
        .into_iter()
        .map(|(k, v)| (k, substitute(v, nref, new_term)))
        .collect();
      Term::Lit {
        value: Literal::StructLit { fields },
      }
    }
    Lit {
      value: Literal::StructUpdate { base, fields },
    } => {
      let fields = fields
        .into_iter()
        .map(|(k, v)| (k, substitute(v, nref, new_term)))
        .collect();
      Term::Lit {
        value: Literal::StructUpdate { base, fields },
      }
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
    Sort { .. } => term,
    Term::Hole => term,
    Ann { term, typ } => {
      let term = substitute(*term, nref, new_term);
      let typ = substitute(*typ, nref, new_term);
      ann(term, typ)
    }
    Quote { term } => {
      let term = substitute(*term, nref, new_term);
      Term::Quote {
        term: Box::new(term),
      }
    }
  }
}
