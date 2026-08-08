//! `#[derive_cli]` — a clap-style attribute derive for CLI argument parsing.
//!
//! `#[derive_cli] type Command { compile (path : String) (#[arg] verbose : Bool), ... }`
//! generates a companion `parse_<typename> : List String -> Result String Command`
//! that dispatches on the first argv token (matched against each constructor's
//! own name) and, within a constructor, treats every `#[arg]`-annotated
//! (`Bool`-typed, v1) param as a `--<name>` flag and every other param as a
//! required positional consumed in declaration order.
//!
//! Unlike the `defmacro ... := decls { ... }` decl-level macro system (see
//! `macro_expand.rs`), which only ever substitutes call arguments into a
//! fixed template, this runs directly against the already-parsed `Inductive`
//! — full reflective access to its real name, constructors, and each
//! constructor's params (and their attributes), no quote/unquote or hygiene
//! needed. It's ordinary Rust code building a `Def` with the same
//! term-building helpers `stru`/`inductive_parser` already use.
//!
//! Generated code calls into a small runtime helper library (`Cli.take_flag`,
//! `Cli.take_positional` — see `lang/cli.mo`) rather than inlining argv
//! string-munging logic directly as raw terms.

use crate::term::{Attribute, Def};
use crate::term::{
  Identifier, InductConstructor, Inductive, ModulePath, NameRef, Named, Param,
  Term::{self, Var},
  app, apps, case, def, id, if_term, lam, match_term, param, pi_typs, pvar, str,
};

/// `Result.ok <term>` — built via a qualified `Var` reference resolved
/// through ordinary scope lookup (`apps(pvar([...]), ...)`), like every
/// other constructor reference in this generator, rather than the `ok()`
/// term-builder's raw pre-resolved `Con` node. The two looked identical when
/// printed, but the checker only correctly instantiates `Result`'s type
/// parameters from surrounding context through the former — seemingly the
/// same narrow gap as `ctor.term()` above, just for library `Con` builders.
fn ok(term: Term) -> Term {
  apps(pvar(vec!["Result", "ok"]), vec![term])
}
fn err(term: Term) -> Term {
  apps(pvar(vec!["Result", "err"]), vec![term])
}

/// Attribute marking a constructor param as a flag rather than a positional.
const ARG_ATTR: &str = "arg";

#[derive(Debug, Clone, PartialEq)]
pub enum DeriveCliError {
  /// The type has no constructors — nothing to dispatch on.
  NoConstructors { type_name: String },
  /// `#[arg]` was used on a non-`Bool` field. v1 only supports boolean
  /// flags; richer `#[arg(...)]` option/default support is future work
  /// (see the plan's Phase 0a scope note).
  NonBoolArgField { constructor: String, field: String },
}

impl std::fmt::Display for DeriveCliError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      DeriveCliError::NoConstructors { type_name } => {
        write!(f, "#[derive_cli]: `{type_name}` has no constructors")
      }
      DeriveCliError::NonBoolArgField { constructor, field } => write!(
        f,
        "#[derive_cli]: `{constructor}`'s field `{field}` is annotated `#[arg]` but is not \
         `Bool` — only boolean flags are supported (v1)"
      ),
    }
  }
}

fn v(name: Identifier) -> Term {
  Var {
    name: NameRef::Id(name),
  }
}

fn has_arg_attr(attrs: &[Attribute]) -> bool {
  attrs.iter().any(|a| a.name.as_str() == ARG_ATTR)
}

fn is_bool_type(t: &Term) -> bool {
  matches!(t, Term::Var { name } if name.as_id().map(|i| i.as_str()) == Some("Bool"))
}

/// One "unwrap a value out of the remaining argv" step in a constructor's
/// generated parse body, built inside-out (see `build_ctor_parser`).
enum Step {
  /// `match Cli.take_flag "<long>" <in_args> { pair <out_flag> <out_rest> => body }`
  Flag {
    long: String,
    out_flag: Identifier,
    out_rest: Identifier,
    in_args: Identifier,
  },
  /// `match Cli.take_positional <in_args> { pair <opt_var> <out_rest> =>
  ///    match <opt_var> { some <out_val> => body, none => Result.err "..." } }`
  Positional {
    ctor_display: String,
    field_display: String,
    opt_var: Identifier,
    out_val: Identifier,
    out_rest: Identifier,
    in_args: Identifier,
  },
}

fn fresh(prefix: &str, counter: &mut u64) -> Identifier {
  let n = *counter;
  *counter += 1;
  id(&format!("{prefix}{n}"))
}

/// Build the term that parses one constructor's params out of `tl` (the argv
/// remaining after the subcommand token itself) and, on success, applies the
/// constructor to the parsed values in their original declared order.
fn build_ctor_parser(
  type_short: &str,
  ctor: &InductConstructor,
  tl: &Identifier,
  counter: &mut u64,
) -> Result<Term, DeriveCliError> {
  let ctor_display = ctor.name().last().as_str().to_string();
  let params: &Vec<Param> = ctor.params();

  let mut is_flag = Vec::with_capacity(params.len());
  for p in params {
    let flagged = has_arg_attr(&p.attrs);
    if flagged && !is_bool_type(&p.typ) {
      return Err(DeriveCliError::NonBoolArgField {
        constructor: ctor_display,
        field: p.name.as_str().to_string(),
      });
    }
    is_flag.push(flagged);
  }

  let mut steps: Vec<Step> = Vec::new();
  let mut bound: Vec<Identifier> = vec![id(""); params.len()];
  let mut cur = tl.clone();

  // Flags first — they're position-independent in argv, so peel them all off
  // (in declared order, for deterministic generated code) before touching
  // positionals.
  for (i, p) in params.iter().enumerate() {
    if is_flag[i] {
      let out_flag = fresh("f", counter);
      let out_rest = fresh("a", counter);
      steps.push(Step::Flag {
        long: p.name.as_str().to_string(),
        out_flag: out_flag.clone(),
        out_rest: out_rest.clone(),
        in_args: cur.clone(),
      });
      bound[i] = out_flag;
      cur = out_rest;
    }
  }
  // Then positionals, consumed in declared order from whatever's left.
  for (i, p) in params.iter().enumerate() {
    if !is_flag[i] {
      let opt_var = fresh("o", counter);
      let out_val = fresh("p", counter);
      let out_rest = fresh("a", counter);
      steps.push(Step::Positional {
        ctor_display: ctor_display.clone(),
        field_display: p.name.as_str().to_string(),
        opt_var,
        out_val: out_val.clone(),
        out_rest: out_rest.clone(),
        in_args: cur.clone(),
      });
      bound[i] = out_val;
      cur = out_rest;
    }
  }

  // Reference the constructor by its qualified name (`Command.compile`) and
  // apply it via ordinary application — the same shape the parser produces
  // for hand-written `Command.compile p f`, resolved through normal scope
  // lookup. (Reusing `ctor.term()`'s pre-built curried closure directly here
  // instead was tried first and worked as far as term construction, but the
  // type checker lost track of it through the nested destructuring matches
  // below; qualified-name application sidesteps that and matches how every
  // other piece of generated/hand-written code in this codebase references
  // constructors.)
  let ctor_ref = pvar(vec![type_short, &ctor_display]);
  let ordered_vars: Vec<Term> = bound.into_iter().map(v).collect();
  let applied = if ordered_vars.is_empty() {
    ctor_ref
  } else {
    apps(ctor_ref, ordered_vars)
  };
  let mut body = ok(applied);

  for step in steps.into_iter().rev() {
    body = match step {
      Step::Flag {
        long,
        out_flag,
        out_rest,
        in_args,
      } => {
        // `Cli.take_flag` returns the dedicated, non-generic
        // `Cli.FlagResult` rather than a `Pair Bool (List String)` —
        // reusing the polymorphic `Pair A B` here made the type checker
        // lose track of `A`/`B` through these nested destructuring matches
        // (a real but narrow checker gap: `Pair`, `Option`, and `Result`
        // all happen to name their first type param `A`). A dedicated
        // concrete result type sidesteps needing that fix.
        //
        // No per-field short-flag config in v1 (`#[arg]` is a bare
        // attribute, see `ARG_ATTR`) — `lang/cli.mo`'s `Cli.take_flag` still
        // takes a `short` param (shared signature with hand-written call
        // sites in `lang/main.mo`), so pass `""` to mean "long form only".
        let scrut = apps(
          pvar(vec!["Cli", "take_flag"]),
          vec![str(&long), str(""), v(in_args)],
        );
        match_term(
          scrut,
          vec![case(id("flag_result"), vec![out_flag, out_rest], body)],
        )
      }
      Step::Positional {
        ctor_display,
        field_display,
        opt_var,
        out_val,
        out_rest,
        in_args,
      } => {
        let scrut = apps(pvar(vec!["Cli", "take_positional"]), vec![v(in_args)]);
        let missing_msg = format!("{ctor_display}: missing required argument '{field_display}'");
        let inner = match_term(
          v(opt_var.clone()),
          vec![
            case(id("some"), vec![out_val], body),
            case(id("none"), vec![], err(str(&missing_msg))),
          ],
        );
        match_term(
          scrut,
          vec![case(id("pos_result"), vec![opt_var, out_rest], inner)],
        )
      }
    };
  }

  Ok(body)
}

/// Generate `parse_<lowercased type name> : List String -> Result String
/// <TypeName>` for a `#[derive_cli]`-annotated `Inductive`.
pub fn expand_derive_cli(induct: &Inductive) -> Result<Def, DeriveCliError> {
  let type_path = induct.name().clone();
  let type_short = type_path.last().clone();

  if induct.constructors().is_empty() {
    return Err(DeriveCliError::NoConstructors {
      type_name: type_short.as_str().to_string(),
    });
  }

  let args_param = id("args");
  let hd = id("hd");
  let tl = id("tl");
  let mut counter: u64 = 0;

  let unknown_subcommand = err(apps(
    pvar(vec!["String", "concat"]),
    vec![str("unknown subcommand: "), v(hd.clone())],
  ));

  let mut else_chain = unknown_subcommand;
  for ctor in induct.constructors().iter().rev() {
    let ctor_name = ctor.name().last().as_str().to_string();
    let cond = apps(
      pvar(vec!["String", "beq"]),
      vec![v(hd.clone()), str(&ctor_name)],
    );
    let then_body = build_ctor_parser(type_short.as_str(), ctor, &tl, &mut counter)?;
    else_chain = if_term(cond, then_body, else_chain);
  }

  let match_body = match_term(
    v(args_param.clone()),
    vec![
      case(id("cons"), vec![hd, tl], else_chain),
      case(id("empty"), vec![], err(str("missing subcommand"))),
    ],
  );

  let list_string = app(v(id("List")), v(id("String")));
  let result_type = app(
    app(v(id("Result")), v(id("String"))),
    crate::term::mpvar(type_path),
  );
  let fn_typ = pi_typs(vec![list_string.clone()], result_type);
  let fn_body = lam(param(args_param, list_string), match_body);

  let fn_name_str = format!("parse_{}", type_short.as_str().to_lowercase());
  let fn_name = ModulePath::single(id(&fn_name_str));

  Ok(def(fn_name, vec![], fn_typ, fn_body, vec![]))
}
