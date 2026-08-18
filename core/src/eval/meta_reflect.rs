//! Conversions between the compiler's own `Inductive`/`Term` and the
//! Monad-level reflection/mini-AST values `init/meta.mo` defines
//! (`TypeInfo`/`CtorInfo`/`FieldInfo`/`Expr`/`MatchArm`/`Param`/`Decl`) —
//! see `plans/review-and-reduce-the-greedy-nest.md`.
//!
//! Two directions:
//! - `build_type_info_value`/`term_to_expr_value`: `Inductive`/`Term` ->
//!   `core_value::Value`, pure data construction, no evaluation needed —
//!   used to build a "meta" function's argument.
//! - `reify_value_to_term`/`reify_decls_value_to_decls`: the inverse, for
//!   a "meta" function's (post-evaluation) computed result -> real
//!   `core::term::Term`/`Decl` to splice into the program being expanded.
//!
//! Constructor tags for `init/meta.mo`'s own types (and for `Bool`/`List`)
//! are resolved from the already-parsed `Inductive`s — declaration order
//! IS the tag, the same convention `core_program::CoreInductiveInfo`
//! documents and `lower_core_ir`'s own tag assignment follows, since both
//! ultimately derive from the same surface `Decl::Type` data — via the
//! `inductives` map `macro_expand.rs` already threads through every
//! reflection intrinsic, not re-derived through a second type-check pass.
//! Top-level Monad names (types AND constructors) are bare/single-segment
//! `ModulePath`s regardless of which module declares them (confirmed
//! empirically — there is no per-module qualification in `Inductive.name()`),
//! so every lookup here uses `mpt(...)`.

use crate::Map;
use crate::core_ir::IrLit;
use crate::core_value::Value;
use crate::term::{
  Decl, Identifier, Inductive, Literal, ModulePath, NameRef, Named, NumSuffix, Term, case, id,
  if_term, instance, lams, match_term, mpt, param, pi_typs, pvar, str,
};

use super::macro_expand::MacroError;

fn find_inductive<'a>(
  inductives: &'a Map<ModulePath, Inductive>,
  name: &str,
) -> Result<&'a Inductive, MacroError> {
  inductives.get(&mpt(name)).ok_or_else(|| {
    MacroError::Generic(format!(
      "meta: type `{name}` not found — is `init.meta`/`init` loaded?"
    ))
  })
}

fn ctor_tag(induct: &Inductive, ctor_name: &str) -> Result<u32, MacroError> {
  induct
    .constructors()
    .iter()
    .position(|c| c.name().last().as_str() == ctor_name)
    .map(|i| i as u32)
    .ok_or_else(|| {
      MacroError::Generic(format!(
        "meta: `{}` has no constructor named `{ctor_name}`",
        induct.name()
      ))
    })
}

fn ctor_name_for_tag(induct: &Inductive, tag: u32) -> Result<String, MacroError> {
  induct
    .constructors()
    .get(tag as usize)
    .map(|c| c.name().last().as_str().to_string())
    .ok_or_else(|| {
      MacroError::Generic(format!(
        "meta: `{}` has no constructor at tag {tag}",
        induct.name()
      ))
    })
}

fn str_value(s: &str) -> Value {
  Value::Lit(IrLit::Str(s.into()))
}

fn expect_str(v: Value) -> Result<String, MacroError> {
  match v {
    Value::Lit(IrLit::Str(s)) => Ok(s.as_str().to_string()),
    other => Err(MacroError::Generic(format!(
      "meta: expected a String value, got: {other:?}"
    ))),
  }
}

fn expect_int(v: Value) -> Result<i64, MacroError> {
  match v {
    Value::Lit(IrLit::Num(n, _)) => Ok(n),
    other => Err(MacroError::Generic(format!(
      "meta: expected an I64 value, got: {other:?}"
    ))),
  }
}

fn expect_bool(inductives: &Map<ModulePath, Inductive>, v: Value) -> Result<bool, MacroError> {
  let induct = find_inductive(inductives, "Bool")?;
  match v {
    Value::Con { tag, .. } => {
      let name = ctor_name_for_tag(induct, tag)?;
      match name.as_str() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => Err(MacroError::Generic(format!(
          "meta: expected a Bool value, got constructor `{other}`"
        ))),
      }
    }
    other => Err(MacroError::Generic(format!(
      "meta: expected a Bool value, got: {other:?}"
    ))),
  }
}

fn list_value(
  inductives: &Map<ModulePath, Inductive>,
  items: Vec<Value>,
) -> Result<Value, MacroError> {
  let induct = find_inductive(inductives, "List")?;
  let empty_tag = ctor_tag(induct, "empty")?;
  let cons_tag = ctor_tag(induct, "cons")?;
  let mut acc = Value::Con {
    tag: empty_tag,
    args: vec![],
  };
  for item in items.into_iter().rev() {
    acc = Value::Con {
      tag: cons_tag,
      args: vec![item, acc],
    };
  }
  Ok(acc)
}

fn value_to_list(
  inductives: &Map<ModulePath, Inductive>,
  v: Value,
) -> Result<Vec<Value>, MacroError> {
  let induct = find_inductive(inductives, "List")?;
  let empty_tag = ctor_tag(induct, "empty")?;
  let cons_tag = ctor_tag(induct, "cons")?;
  let mut items = Vec::new();
  let mut cur = v;
  loop {
    match cur {
      Value::Con { tag, mut args } if tag == cons_tag && args.len() == 2 => {
        let tail = args.pop().unwrap();
        let head = args.pop().unwrap();
        items.push(head);
        cur = tail;
      }
      Value::Con { tag, ref args } if tag == empty_tag && args.is_empty() => break,
      other => {
        return Err(MacroError::Generic(format!(
          "meta: expected a List value, got: {other:?}"
        )));
      }
    }
  }
  Ok(items)
}

/// `NameRef` -> the plain (possibly dotted) name string an `e_var`/
/// `e_ctor` value carries — the inverse of `pvar`/`id`'s own segment
/// splitting.
fn name_to_string(name: &NameRef) -> String {
  match name {
    NameRef::Id(id) => id.as_str().to_string(),
    NameRef::P(path) => path.to_string(),
    other => other.to_string(),
  }
}

/// The inverse of `name_to_string` — a plain (possibly dotted) name
/// string back into a `Var` term, qualified (`pvar`) if it contains a
/// `.`, a bare `Var{Id}` otherwise.
fn name_ref_term(name: &str) -> Term {
  if name.contains('.') {
    pvar(name.split('.').collect())
  } else {
    Term::Var {
      name: NameRef::Id(id(name)),
    }
  }
}

/// A plain (possibly dotted) name string -> a proper multi-segment
/// `ModulePath` — needed for a generated `Decl.d_def`'s own NAME (e.g.
/// `"Point.x"`), not just for referencing an existing name
/// (`name_ref_term`). `mpt`/`ModulePath::top` alone would build a
/// single-segment path whose one `Identifier` literally contains a `.`
/// character — a real bug found and fixed here: something registered
/// that way is invisible to any ordinary `Point.x` reference elsewhere,
/// which the parser resolves as a genuine two-segment qualified path
/// (`NameRef::P(ModulePath(["Point", "x"]))`), a different key entirely.
fn name_to_module_path(name: &str) -> ModulePath {
  ModulePath::new(name.split('.').map(id).collect())
}

fn strip_ctx(term: Term) -> Term {
  match term {
    Term::Ctx { term, .. } => strip_ctx(*term),
    other => other,
  }
}

/// `Term` -> `Expr` value. Only handles the subset a field's TYPE
/// annotation (the only current caller) actually uses — qualified/bare
/// variable references and application chains (e.g. `List I64`,
/// `Lens Point I64`), plus string/int literals for completeness with the
/// reify direction. Anything else (`Pi`/`Forall`/`Sort`/`Ann`/`Ntv`/
/// `Hole`/`Quote`) errors — `Expr`'s own design deliberately excludes
/// them, see `init/meta.mo`'s doc comment.
pub fn term_to_expr_value(
  t: &Term,
  inductives: &Map<ModulePath, Inductive>,
) -> Result<Value, MacroError> {
  let expr_induct = find_inductive(inductives, "Expr")?;
  match strip_ctx(t.clone()) {
    Term::Var { name } => {
      let tag = ctor_tag(expr_induct, "e_var")?;
      Ok(Value::Con {
        tag,
        args: vec![str_value(&name_to_string(&name))],
      })
    }
    Term::App { fun, arg } => {
      let tag = ctor_tag(expr_induct, "e_app")?;
      let f = term_to_expr_value(&fun, inductives)?;
      let a = term_to_expr_value(&arg, inductives)?;
      Ok(Value::Con {
        tag,
        args: vec![f, a],
      })
    }
    Term::Lit {
      value: Literal::Str { value },
    } => {
      let tag = ctor_tag(expr_induct, "e_str")?;
      Ok(Value::Con {
        tag,
        args: vec![str_value(&value)],
      })
    }
    Term::Lit {
      value: Literal::Num { value, .. },
    } => {
      let tag = ctor_tag(expr_induct, "e_int")?;
      Ok(Value::Con {
        tag,
        args: vec![Value::Lit(IrLit::Num(value, NumSuffix::I64))],
      })
    }
    other => Err(MacroError::Generic(format!(
      "meta: cannot represent `{other}` as an Expr value (unsupported term shape)"
    ))),
  }
}

/// `Inductive` -> `TypeInfo` value — the reflection primitive
/// (`reflect_type_info!`)'s core: walk `induct`'s constructors/fields
/// directly (pure data construction, no evaluation).
pub fn build_type_info_value(
  induct: &Inductive,
  inductives: &Map<ModulePath, Inductive>,
) -> Result<Value, MacroError> {
  let type_info_tag = ctor_tag(find_inductive(inductives, "TypeInfo")?, "type_info")?;
  let ctor_info_tag = ctor_tag(find_inductive(inductives, "CtorInfo")?, "ctor_info")?;
  let field_info_tag = ctor_tag(find_inductive(inductives, "FieldInfo")?, "field_info")?;

  let mut ctor_values = Vec::new();
  for ctor in induct.constructors() {
    let mut field_values = Vec::new();
    for field in ctor.params() {
      let name_v = str_value(field.name.as_str());
      let typ_v = term_to_expr_value(&field.typ, inductives)?;
      let attr_values: Vec<Value> = field
        .attrs
        .iter()
        .map(|a| str_value(a.name.as_str()))
        .collect();
      let attrs_v = list_value(inductives, attr_values)?;
      field_values.push(Value::Con {
        tag: field_info_tag,
        args: vec![name_v, typ_v, attrs_v],
      });
    }
    let fields_list = list_value(inductives, field_values)?;
    let ctor_name_v = str_value(ctor.name().last().as_str());
    ctor_values.push(Value::Con {
      tag: ctor_info_tag,
      args: vec![ctor_name_v, fields_list],
    });
  }
  let ctors_list = list_value(inductives, ctor_values)?;
  let name_v = str_value(induct.name().last().as_str());
  Ok(Value::Con {
    tag: type_info_tag,
    args: vec![name_v, ctors_list],
  })
}

/// `Expr` value -> real `Term`, recursively. The reify direction of
/// `term_to_expr_value`, but complete over all of `Expr`'s constructors
/// (a "meta" function's computed result can use any of them, not just
/// the subset `term_to_expr_value` itself produces for field types).
pub fn reify_value_to_term(
  v: Value,
  inductives: &Map<ModulePath, Inductive>,
) -> Result<Term, MacroError> {
  let expr_induct = find_inductive(inductives, "Expr")?;
  match v {
    Value::Con { tag, mut args } => {
      let ctor_name = ctor_name_for_tag(expr_induct, tag)?;
      match ctor_name.as_str() {
        "e_var" => {
          let name = expect_str(pop_front(&mut args)?)?;
          Ok(name_ref_term(&name))
        }
        "e_str" => Ok(str(&expect_str(pop_front(&mut args)?)?)),
        "e_int" => {
          let n = expect_int(pop_front(&mut args)?)?;
          Ok(Term::Lit {
            value: Literal::Num {
              value: n,
              suffix: NumSuffix::I64,
            },
          })
        }
        "e_bool" => {
          let b = expect_bool(inductives, pop_front(&mut args)?)?;
          Ok(Term::Var {
            name: NameRef::Id(id(if b { "true" } else { "false" })),
          })
        }
        "e_app" => {
          let f = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          let a = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          Ok(Term::App {
            fun: Box::new(f),
            arg: Box::new(a),
          })
        }
        "e_lam" => {
          let param_name = expect_str(pop_front(&mut args)?)?;
          let param_typ = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          let body = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          Ok(lams(vec![param(id(&param_name), param_typ)], body))
        }
        "e_if" => {
          let cond = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          let then_ = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          let else_ = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          Ok(if_term(cond, then_, else_))
        }
        "e_match" => {
          let scrutinee = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          let arms_list = value_to_list(inductives, pop_front(&mut args)?)?;
          let mut cases = Vec::new();
          for arm_v in arms_list {
            cases.push(reify_match_arm(arm_v, inductives)?);
          }
          Ok(match_term(scrutinee, cases))
        }
        "e_ctor" => {
          let ctor_name = expect_str(pop_front(&mut args)?)?;
          let arg_values = value_to_list(inductives, pop_front(&mut args)?)?;
          let mut arg_terms = Vec::new();
          for av in arg_values {
            arg_terms.push(reify_value_to_term(av, inductives)?);
          }
          // Qualified `Var` + application, NOT a raw `Con` node — the
          // type checker only correctly instantiates a constructor's
          // type parameters through the `Var`+`App` path (same
          // load-bearing detail `derive_cli.rs` documents).
          Ok(crate::term::apps(name_ref_term(&ctor_name), arg_terms))
        }
        other => Err(MacroError::Generic(format!(
          "meta: unknown Expr constructor `{other}`"
        ))),
      }
    }
    other => Err(MacroError::Generic(format!(
      "meta: expected an Expr value, got: {other:?}"
    ))),
  }
}

fn pop_front(args: &mut Vec<Value>) -> Result<Value, MacroError> {
  if args.is_empty() {
    return Err(MacroError::Generic(
      "meta: constructor value has fewer fields than expected".into(),
    ));
  }
  Ok(args.remove(0))
}

fn reify_match_arm(
  v: Value,
  inductives: &Map<ModulePath, Inductive>,
) -> Result<crate::term::MatchCase, MacroError> {
  let induct = find_inductive(inductives, "MatchArm")?;
  match v {
    Value::Con { tag, mut args } => {
      let ctor_name = ctor_name_for_tag(induct, tag)?;
      if ctor_name != "match_arm" {
        return Err(MacroError::Generic(format!(
          "meta: expected a MatchArm value, got constructor `{ctor_name}`"
        )));
      }
      let arm_ctor_name = expect_str(pop_front(&mut args)?)?;
      let binders_list = value_to_list(inductives, pop_front(&mut args)?)?;
      let mut binders = Vec::new();
      for b in binders_list {
        binders.push(id(&expect_str(b)?));
      }
      let body = reify_value_to_term(pop_front(&mut args)?, inductives)?;
      Ok(case(id(&arm_ctor_name), binders, body))
    }
    other => Err(MacroError::Generic(format!(
      "meta: expected a MatchArm value, got: {other:?}"
    ))),
  }
}

/// One `Param` value -> `(name, type Term)`.
fn reify_param_value(
  v: Value,
  inductives: &Map<ModulePath, Inductive>,
) -> Result<(Identifier, Term), MacroError> {
  let induct = find_inductive(inductives, "Param")?;
  match v {
    Value::Con { tag, mut args } => {
      let ctor_name = ctor_name_for_tag(induct, tag)?;
      if ctor_name != "meta_param" {
        return Err(MacroError::Generic(format!(
          "meta: expected a Param value, got constructor `{ctor_name}`"
        )));
      }
      let name = expect_str(pop_front(&mut args)?)?;
      let typ = reify_value_to_term(pop_front(&mut args)?, inductives)?;
      Ok((id(&name), typ))
    }
    other => Err(MacroError::Generic(format!(
      "meta: expected a Param value, got: {other:?}"
    ))),
  }
}

/// A `d_def` value -> a real `Def` — shared by top-level `def`s and
/// `instance` methods (both are `d_def`-shaped).
fn reify_def_value(
  v: Value,
  inductives: &Map<ModulePath, Inductive>,
) -> Result<crate::term::Def, MacroError> {
  let induct = find_inductive(inductives, "Decl")?;
  match v {
    Value::Con { tag, mut args } => {
      let ctor_name = ctor_name_for_tag(induct, tag)?;
      if ctor_name != "d_def" {
        return Err(MacroError::Generic(format!(
          "meta: expected a Decl.d_def value, got constructor `{ctor_name}`"
        )));
      }
      let name = expect_str(pop_front(&mut args)?)?;
      let params_list = value_to_list(inductives, pop_front(&mut args)?)?;
      let mut params = Vec::new();
      for pv in params_list {
        params.push(reify_param_value(pv, inductives)?);
      }
      let ret_typ = reify_value_to_term(pop_front(&mut args)?, inductives)?;
      let body = reify_value_to_term(pop_front(&mut args)?, inductives)?;
      let param_terms: Vec<crate::term::Param> = params
        .iter()
        .map(|(n, t)| param(n.clone(), t.clone()))
        .collect();
      let param_typs: Vec<Term> = params.iter().map(|(_, t)| t.clone()).collect();
      let full_typ = pi_typs(param_typs, ret_typ);
      let full_body = if param_terms.is_empty() {
        body
      } else {
        lams(param_terms, body)
      };
      Ok(crate::term::def(
        name_to_module_path(&name),
        vec![],
        full_typ,
        full_body,
        vec![],
      ))
    }
    other => Err(MacroError::Generic(format!(
      "meta: expected a Decl.d_def value, got: {other:?}"
    ))),
  }
}

/// One `Decl` value -> a real `core::term::Decl`.
fn reify_decl_value(v: Value, inductives: &Map<ModulePath, Inductive>) -> Result<Decl, MacroError> {
  let induct = find_inductive(inductives, "Decl")?;
  match &v {
    Value::Con { tag, .. } => {
      let ctor_name = ctor_name_for_tag(induct, *tag)?;
      match ctor_name.as_str() {
        "d_def" => Ok(Decl::Def(reify_def_value(v, inductives)?)),
        "d_instance" => {
          let Value::Con { args, .. } = v else {
            unreachable!()
          };
          let mut args = args;
          let class_name = expect_str(pop_front(&mut args)?)?;
          let target_typ = reify_value_to_term(pop_front(&mut args)?, inductives)?;
          let methods_list = value_to_list(inductives, pop_front(&mut args)?)?;
          let mut impls = Vec::new();
          for mv in methods_list {
            impls.push(reify_def_value(mv, inductives)?);
          }
          let ins = instance(
            None,
            mpt(&class_name),
            vec![],
            vec![],
            vec![target_typ],
            impls,
            vec![],
          );
          Ok(Decl::Ins(ins))
        }
        "d_error" => {
          let Value::Con { args, .. } = v else {
            unreachable!()
          };
          let mut args = args;
          let message = expect_str(pop_front(&mut args)?)?;
          Err(MacroError::Generic(message))
        }
        other => Err(MacroError::Generic(format!(
          "meta: unknown Decl constructor `{other}`"
        ))),
      }
    }
    other => Err(MacroError::Generic(format!(
      "meta: expected a Decl value, got: {other:?}"
    ))),
  }
}

/// A `List Decl` value -> real `Vec<Decl>` — the top-level reify entry
/// point for a decl-position "meta" invocation (e.g. `derive_lens`'s
/// result).
pub fn reify_decls_value_to_decls(
  v: Value,
  inductives: &Map<ModulePath, Inductive>,
) -> Result<Vec<Decl>, MacroError> {
  let values = value_to_list(inductives, v)?;
  let mut decls = Vec::new();
  for dv in values {
    decls.push(reify_decl_value(dv, inductives)?);
  }
  Ok(decls)
}
