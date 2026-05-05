use crate::Map;
use crate::term::module::LoadedModules;
use crate::term::{
  Constructor, Decl, Def, Identifier, Literal, ModulePath, NameRef, Par, SourceContext,
  Term::{self, Ann, App, Con, Ctx, Forall, Lam, Lit, Pi, Quote, Var},
  app, apps, case, forall, lam, match_term, param, pi_name,
};

/// Recursively strip Ctx wrappers from a term.
fn strip_ctx(term: Term) -> Term {
  match term {
    Ctx { term: t, .. } => strip_ctx(*t),
    other => other,
  }
}

/// Maximum macro expansion depth to prevent infinite recursion
const MAX_EXPANSION_DEPTH: u64 = 32;

/// Error type for macro expansion failures
#[derive(Debug, Clone)]
pub enum MacroError {
  DepthLimitExceeded,
  NonTermReturn { name: String },
  MacroNotFound { name: String },
  Generic(String),
}

impl std::fmt::Display for MacroError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      MacroError::DepthLimitExceeded => write!(f, "macro expansion depth limit exceeded"),
      MacroError::NonTermReturn { name } => {
        write!(f, "macro `{name}` did not return a Term value")
      }
      MacroError::MacroNotFound { name } => write!(f, "macro `{name}` not found"),
      MacroError::Generic(msg) => write!(f, "{msg}"),
    }
  }
}

/// Expand all macro calls in declarations.
/// Runs between elaboration and type checking.
pub fn expand_macros(
  decls: Vec<SourceContext<Decl>>,
  _loaded: &LoadedModules,
) -> Result<Vec<SourceContext<Decl>>, MacroError> {
  let macro_defs: Map<ModulePath, Def> = decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::DefMacro(def) => Some((def.name.clone(), def.clone())),
      _ => None,
    })
    .collect();

  decls
    .into_iter()
    .map(|ctx| expand_decl(ctx, &macro_defs))
    .collect()
}

fn expand_decl(
  ctx: SourceContext<Decl>,
  macro_defs: &Map<ModulePath, Def>,
) -> Result<SourceContext<Decl>, MacroError> {
  let decl = ctx.value().clone();
  match decl {
    Decl::DefMacro(_) => Ok(ctx),
    Decl::Def(mut def) => {
      def.term = expand_term(def.term, macro_defs, 0)?;
      Ok(ctx.map(|_| Decl::Def(def)))
    }
    other => Ok(ctx.map(|_| other)),
  }
}

/// Walk a term and expand macro calls.
fn expand_term(
  term: Term,
  macro_defs: &Map<ModulePath, Def>,
  depth: u64,
) -> Result<Term, MacroError> {
  if depth > MAX_EXPANSION_DEPTH {
    return Err(MacroError::DepthLimitExceeded);
  }
  match term {
    App { fun, arg } => {
      // Check for name! macro call
      if let Var {
        name: NameRef::Macro(name),
      } = &*fun
      {
        let path = ModulePath::single(name.clone());
        if let Some(def) = macro_defs.get(&path) {
          let arg = expand_term(*arg, macro_defs, depth)?;
          return apply_macro(def, vec![arg], macro_defs, depth);
        }
      }
      // Check for chained name! a b macro call
      if let App { .. } = &*fun {
        let child_fun = fun.clone();
        let child_arg = arg.clone();
        if let Some((name, mut args)) = collect_macro_args(*child_fun, *child_arg) {
          let path = ModulePath::single(name.clone());
          if let Some(def) = macro_defs.get(&path) {
            for a in args.iter_mut() {
              let old = std::mem::replace(a, Term::Hole);
              *a = expand_term(old, macro_defs, depth)?;
            }
            // Now args has the original fun and arg, so we continue with the next iteration
            // but the macro has already been looked up, so this won't match again
            return apply_macro(def, args, macro_defs, depth);
          }
        }
      }
      // Not a macro call (or macro not found) — recurse normally
      Ok(App {
        fun: Box::new(expand_term(*fun, macro_defs, depth)?),
        arg: Box::new(expand_term(*arg, macro_defs, depth)?),
      })
    }
    Lam { param, body } => Ok(Lam {
      param,
      body: Box::new(expand_term(*body, macro_defs, depth)?),
    }),
    Quote { term } => Ok(Quote {
      term: Box::new(resolve_quote(*term, macro_defs, depth)?),
    }),
    Ctx { loc, term } => Ok(Ctx {
      loc,
      term: Box::new(expand_term(*term, macro_defs, depth)?),
    }),
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Ok(Pi {
      arg_name,
      arg: Box::new(expand_term(*arg, macro_defs, depth)?),
      ret: Box::new(expand_term(*ret, macro_defs, depth)?),
      mult,
    }),
    Forall { name, typ, body } => Ok(Forall {
      name,
      typ: Box::new(expand_term(*typ, macro_defs, depth)?),
      body: Box::new(expand_term(*body, macro_defs, depth)?),
    }),
    Ann { term, typ } => Ok(Ann {
      term: Box::new(expand_term(*term, macro_defs, depth)?),
      typ: Box::new(expand_term(*typ, macro_defs, depth)?),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = expand_term(*value, macro_defs, depth)?;
      let cases = cases
        .into_iter()
        .map(|c| {
          let value = expand_term(*c.value, macro_defs, depth)?;
          Ok(case(c.name, c.args, value))
        })
        .collect::<Result<Vec<_>, MacroError>>()?;
      Ok(match_term(value, cases))
    }
    Lit {
      value: Literal::If { value, then, els },
    } => {
      let value = expand_term(*value, macro_defs, depth)?;
      let then = expand_term(*then, macro_defs, depth)?;
      let els = expand_term(*els, macro_defs, depth)?;
      Ok(Term::Lit {
        value: Literal::If {
          value: Box::new(value),
          then: Box::new(then),
          els: Box::new(els),
        },
      })
    }
    Con(Constructor {
      typ_name,
      args,
      name,
      num_args,
    }) => {
      let args: Vec<Option<Term>> = args
        .into_iter()
        .map(|a| a.map(|t| expand_term(t, macro_defs, depth)).transpose())
        .collect::<Result<Vec<_>, MacroError>>()?;
      Ok(Con(Constructor {
        name,
        typ_name,
        args,
        num_args,
      }))
    }
    other => Ok(other),
  }
}

/// Resolve unquote calls inside a Quote body and expand any macro calls.
fn resolve_quote(
  term: Term,
  macro_defs: &Map<ModulePath, Def>,
  depth: u64,
) -> Result<Term, MacroError> {
  if depth > MAX_EXPANSION_DEPTH {
    return Err(MacroError::DepthLimitExceeded);
  }
  match term {
    App { fun, arg } => {
      // Check for unquote
      if let Var {
        name: NameRef::Id(n),
      } = &*fun
        && n.as_str() == "unquote"
      {
        // unquote(arg): splice arg into the output, then expand it
        let arg = resolve_quote(*arg, macro_defs, depth)?;
        // The spliced result may contain macro calls
        expand_term(arg, macro_defs, depth)
      } else {
        // Check for name! macro call
        if let Var {
          name: NameRef::Macro(name),
        } = &*fun
        {
          let path = ModulePath::single(name.clone());
          if let Some(def) = macro_defs.get(&path) {
            let arg = resolve_quote(*arg, macro_defs, depth)?;
            return apply_macro(def, vec![arg], macro_defs, depth + 1);
          }
        }
        // Check for chained name! a b macro call
        if let App { .. } = &*fun {
          let child_fun = fun.clone();
          let child_arg = arg.clone();
          if let Some((name, mut args)) = collect_macro_args(*child_fun, *child_arg) {
            let path = ModulePath::single(name.clone());
            if let Some(def) = macro_defs.get(&path) {
              for a in args.iter_mut() {
                let old = std::mem::replace(a, Term::Hole);
                *a = resolve_quote(old, macro_defs, depth)?;
              }
              return apply_macro(def, args, macro_defs, depth + 1);
            }
          }
        }
        // Not a macro call — recurse
        Ok(App {
          fun: Box::new(resolve_quote(*fun, macro_defs, depth)?),
          arg: Box::new(resolve_quote(*arg, macro_defs, depth)?),
        })
      }
    }
    Lam { param, body } => Ok(Lam {
      param,
      body: Box::new(resolve_quote(*body, macro_defs, depth)?),
    }),
    Quote { term } => {
      // Nested quote — don't resolve unquotes (they belong to the inner quote)
      Ok(Quote {
        term: Box::new(resolve_quote(*term, macro_defs, depth)?),
      })
    }
    Ctx { loc, term } => Ok(Ctx {
      loc,
      term: Box::new(resolve_quote(*term, macro_defs, depth)?),
    }),
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Ok(Pi {
      arg_name,
      arg: Box::new(resolve_quote(*arg, macro_defs, depth)?),
      ret: Box::new(resolve_quote(*ret, macro_defs, depth)?),
      mult,
    }),
    Forall { name, typ, body } => Ok(Forall {
      name,
      typ: Box::new(resolve_quote(*typ, macro_defs, depth)?),
      body: Box::new(resolve_quote(*body, macro_defs, depth)?),
    }),
    Ann { term, typ } => Ok(Ann {
      term: Box::new(resolve_quote(*term, macro_defs, depth)?),
      typ: Box::new(resolve_quote(*typ, macro_defs, depth)?),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = resolve_quote(*value, macro_defs, depth)?;
      let cases = cases
        .into_iter()
        .map(|c| {
          let value = resolve_quote(*c.value, macro_defs, depth)?;
          Ok(case(c.name, c.args, value))
        })
        .collect::<Result<Vec<_>, MacroError>>()?;
      Ok(match_term(value, cases))
    }
    Lit {
      value: Literal::If { value, then, els },
    } => {
      let value = resolve_quote(*value, macro_defs, depth)?;
      let then = resolve_quote(*then, macro_defs, depth)?;
      let els = resolve_quote(*els, macro_defs, depth)?;
      Ok(Term::Lit {
        value: Literal::If {
          value: Box::new(value),
          then: Box::new(then),
          els: Box::new(els),
        },
      })
    }
    Con(Constructor {
      typ_name,
      args,
      name,
      num_args,
    }) => {
      let args: Vec<Option<Term>> = args
        .into_iter()
        .map(|a| a.map(|t| resolve_quote(t, macro_defs, depth)).transpose())
        .collect::<Result<Vec<_>, MacroError>>()?;
      Ok(Con(Constructor {
        name,
        typ_name,
        args,
        num_args,
      }))
    }
    other => Ok(other),
  }
}

/// Check if a term has a macro call somewhere in a chain of Apps.
fn has_macro_in_chain(term: &Term) -> bool {
  match term {
    Var {
      name: NameRef::Macro(_),
    } => true,
    App { fun, arg: _ } => has_macro_in_chain(fun),
    _ => false,
  }
}

/// Collect arguments from a chained App, checking if it's a macro call.
/// Returns None if not a macro call.
/// Returns Some((name, args)) if it is, with args in left-to-right order.
fn collect_macro_args(fun: Term, arg: Term) -> Option<(Identifier, Vec<Term>)> {
  match fun {
    Var {
      name: NameRef::Macro(name),
    } => Some((name, vec![arg])),
    App {
      fun: inner_fun,
      arg: inner_arg,
    } => {
      let (name, mut args) = collect_macro_args(*inner_fun, *inner_arg)?;
      args.push(arg);
      Some((name, args))
    }
    _ => None,
  }
}

/// Apply macro to args, producing the expanded term.
fn apply_macro(
  def: &Def,
  args: Vec<Term>,
  macro_defs: &Map<ModulePath, Def>,
  depth: u64,
) -> Result<Term, MacroError> {
  if depth > MAX_EXPANSION_DEPTH {
    return Err(MacroError::DepthLimitExceeded);
  }

  // Peel off one Lam per arg and substitute
  let mut body = def.term.clone();
  for arg in args {
    body = match body {
      Lam { param, body: b } => match param {
        Par::P(p) => subst_macro(*b, &NameRef::Id(p.name.clone()), &arg),
        Par::I { .. } => {
          return Err(MacroError::Generic("macro with implicit parameter".into()));
        }
      },
      _ => {
        return Err(MacroError::Generic("too many arguments for macro".into()));
      }
    };
  }

  // Strip Ctx wrappers and find the Quote body
  let body = strip_ctx(body);
  match body {
    Quote { term } => {
      let expanded = resolve_quote(*term, macro_defs, depth)?;
      expand_term(expanded, macro_defs, depth + 1)
    }
    _ => Err(MacroError::NonTermReturn {
      name: def.name.to_string(),
    }),
  }
}

/// Substitute variable references in a term WITHOUT capture-avoiding rename
/// of lambda binders. This is used for macro parameter substitution where
/// the outer lambda wrapping the macro body is being consumed, not protected.
fn subst_macro(term: Term, name: &NameRef, replacement: &Term) -> Term {
  match term {
    Var { name: n } if &n == name => replacement.clone(),
    Lam { param: p, body: b } => {
      let should_skip = match (&p, name) {
        (Par::P(p_name), NameRef::Id(n)) => &p_name.name == n,
        _ => false,
      };
      if should_skip {
        Lam { param: p, body: b }
      } else {
        Lam {
          param: p,
          body: Box::new(subst_macro(*b, name, replacement)),
        }
      }
    }
    App { fun, arg } => App {
      fun: Box::new(subst_macro(*fun, name, replacement)),
      arg: Box::new(subst_macro(*arg, name, replacement)),
    },
    Pi {
      arg_name,
      arg,
      ret,
      mult,
    } => Pi {
      arg_name,
      arg: Box::new(subst_macro(*arg, name, replacement)),
      ret: Box::new(subst_macro(*ret, name, replacement)),
      mult,
    },
    Forall {
      name: n,
      typ,
      body: b,
    } => {
      if let NameRef::Id(id) = name
        && &n == id
      {
        Forall {
          name: n,
          typ,
          body: b,
        }
      } else {
        Forall {
          name: n,
          typ: Box::new(subst_macro(*typ, name, replacement)),
          body: Box::new(subst_macro(*b, name, replacement)),
        }
      }
    }
    Quote { term: t } => Quote {
      term: Box::new(subst_macro(*t, name, replacement)),
    },
    Ctx { loc, term: t } => Ctx {
      loc,
      term: Box::new(subst_macro(*t, name, replacement)),
    },
    Ann { term: t, typ } => Ann {
      term: Box::new(subst_macro(*t, name, replacement)),
      typ: Box::new(subst_macro(*typ, name, replacement)),
    },
    Con(Constructor {
      typ_name,
      args,
      name: n,
      num_args,
    }) => Con(Constructor {
      name: n,
      typ_name,
      num_args,
      args: args
        .into_iter()
        .map(|a| a.map(|t| subst_macro(t, name, replacement)))
        .collect(),
    }),
    Lit {
      value: Literal::Match { value, cases },
    } => {
      let value = subst_macro(*value, name, replacement);
      let cases = cases
        .into_iter()
        .map(|c| case(c.name, c.args, subst_macro(*c.value, name, replacement)))
        .collect();
      match_term(value, cases)
    }
    Lit {
      value: Literal::If { value, then, els },
    } => Term::Lit {
      value: Literal::If {
        value: Box::new(subst_macro(*value, name, replacement)),
        then: Box::new(subst_macro(*then, name, replacement)),
        els: Box::new(subst_macro(*els, name, replacement)),
      },
    },
    other => other,
  }
}
