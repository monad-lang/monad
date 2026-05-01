mod error;
pub mod locate;
mod string;
#[cfg(test)]
pub mod test;

use std::fmt::Display;

use crate::{
  parser::error::{ParseError, ReplParserError},
  term::{
    AttrArg, Attribute, ClassDef, Decl, Def, Identifier, InductConstructor, Inductive, Infix,
    Instance, LetVar, Literal, MatchCase, ModulePath, NameRef, NumSuffix, Open, Operator, Param,
    SourceContext, SourceRange, StructField,
    Term::{self, Hole, Var},
    TypeConstraint, Use, app, apps, case, class, class_def, ctx, def, def_with_native,
    float_suffix, forall, foralls, id, if_term, induct_constructor, inductive, infix, instance,
    lam, lams, lets, map_term, match_term, mpvar, num_suffix, opr, param, pi_name, pi_typs, pvar,
    stru, stru_field, ty, type_constraint, var_id,
  },
};
use locate::{LocatedSpan, info};
use nom::{
  Finish, IResult, Parser,
  branch::alt,
  bytes::complete::{tag, take_until, take_while},
  character::complete::{alpha1, char, i64, multispace1, not_line_ending},
  combinator::{eof, map, opt, recognize, success, verify},
  multi::{fold_many0, many0, many1},
  sequence::{delimited, preceded, separated_pair, terminated},
};
use string::parse_string;

pub use error::{OwnedError, ParseFileError, ParseTermError};
pub type Span<'a, X = ()> = LocatedSpan<&'a str, X>;
type E<'a, X = ()> = ParseError<Span<'a, X>>;
type Res<'a, O, X = ()> = IResult<Span<'a, X>, O, E<'a, X>>;

impl<'a> From<ParseError<Span<'a>>> for OwnedError {
  fn from(value: ParseError<Span>) -> Self {
    ParseError {
      input: value.input.into(),
      expected: value.expected,
      errors: value.errors,
    }
  }
}

pub fn set_res_extra<X: Clone, Y: Clone, T>(res: Res<T, X>, extra: Y) -> Res<T, Y> {
  res
    .map(|(i, o)| (i.map_extra(|_| extra.clone()), o))
    .map_err(|e| e.map(|e| e.map_input(|i| i.map_extra(|_| extra))))
}

const RESERVED_KEYWORDS: &[&str] = &[
  "def", "let", "in", "use", "open", "class", "struct", "instance", "type", "fn", "ꟛ", "match",
  "if", "then", "else", "infix", "return", "for", "do",
];
const RESERVED_NAMES: &[&str] = &["Type", "Pred"];

fn is_reserved_keyword(s: &str) -> bool {
  RESERVED_KEYWORDS.contains(&s)
}
fn is_reserved_name(s: &str) -> bool {
  RESERVED_NAMES.contains(&s)
}

/// Accepts letters/num/_ as identifier
fn identifier<X: Clone>(input: Span<X>) -> Res<Identifier, X> {
  let (input, name) = verify(
    recognize((
      alt((alpha1, tag("_"))),
      take_while(|c: char| c.is_alphanumeric() || c == '_'),
    )),
    |id: &str| !is_reserved_keyword(id),
  )
  .parse(input)?;
  Ok((input, id(name.into_fragment())))
}

fn name<X: Clone>(input: Span<X>) -> Res<Identifier, X> {
  verify(identifier, |id| !is_reserved_name(id.as_str())).parse(input)
}

fn line_comment<X: Clone>(input: Span<X>) -> Res<Span<X>, X> {
  preceded(tag("//"), not_line_ending).parse(input)
}

fn block_comment<X: Clone>(input: Span<X>) -> Res<Span<X>, X> {
  delimited(tag("/*"), take_until("*/"), tag("*/")).parse(input)
}

fn ws0<X: Clone>(input: Span<X>) -> Res<Span<X>, X> {
  recognize(many0(alt((multispace1, line_comment, block_comment)))).parse(input)
}

fn ws1<X: Clone>(input: Span<X>) -> Res<Span<X>, X> {
  recognize(many1(alt((multispace1, line_comment, block_comment)))).parse(input)
}

fn variable<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, term) = alt((
    map(path_expression, |p| Var {
      name: NameRef::P(p),
    }),
    simple_var,
  ))
  .parse(input)?;
  Ok((input, term))
}

fn operator_parens<X: Clone>(input: Span<X>) -> Res<Operator, X> {
  delimited(char('('), infix_symbol, char(')')).parse(input)
}

fn operator_var<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, op) = operator_parens(input)?;
  Ok((
    input,
    Term::Var {
      name: NameRef::Op(op),
    },
  ))
}

fn simple_var<X: Clone>(input: Span<X>) -> Res<Term, X> {
  map(identifier, |i| {
    if i.as_str() == "_" {
      Term::Hole
    } else {
      var_id(i)
    }
  })
  .parse(input)
}

fn forall_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  map(
    preceded(
      (char('{'), ws0),
      (
        terminated(identifier, (ws0, char(':'), ws0)),
        type_expression,
        preceded((ws0, char('}'), ws0, tag("->"), ws0), type_top_expression),
      ),
    ),
    |(name, typ, body)| forall(param(name, typ), body),
  )
  .parse(input)
}

fn type_base_expression<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((application, variable, type_parens)).parse(input)
}

fn pi_type_expression<X: Clone>(input: Span<X>) -> Res<Term, X> {
  map(
    separated_pair(
      alt((
        map(
          delimited(
            (char('('), ws0),
            separated_pair(identifier, (ws0, char(':'), ws0), type_base_expression),
            (ws0, char(')')),
          ),
          |(n, t)| (Some(n), t),
        ),
        map(type_base_expression, |t| (None, t)),
      )),
      (ws0, tag("->"), ws0),
      type_expression,
    ),
    |((arg_name, arg), ret)| pi_name(arg_name, arg, ret),
  )
  .parse(input)
}

fn type_parens<X: Clone>(input: Span<X>) -> Res<Term, X> {
  delimited(
    terminated(tag("("), ws0),
    type_expression,
    preceded(ws0, tag(")")),
  )
  .parse(input)
}

fn type_expression<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let extra = input.extra().clone();
  let input = input.map_extra(|_| ());
  set_res_extra(
    alt((pi_type_expression, type_base_expression)).parse(input),
    extra,
  )
}

fn type_top_expression<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((forall_parser, type_expression)).parse(input)
}

fn type_annotation<X: Clone>(input: Span<X>) -> Res<Term, X> {
  preceded((char(':'), ws0), type_expression).parse(input)
}

fn def_type_annotation<X: Clone>(input: Span<X>) -> Res<Term, X> {
  preceded((char(':'), ws0), type_top_expression).parse(input)
}

fn opt_type_annotation<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((type_annotation, success(Hole))).parse(input)
}

fn string_literal<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let extra = input.extra().clone();
  let input = input.map_extra(|_| ());
  let (input, value) = set_res_extra(
    parse_string(input.into_fragment())
      .map_err(|e| e.map(|f: nom::error::Error<&str>| f.into()))
      .map(|(i, v)| (Span::new(i), v)),
    extra,
  )?;
  Ok((
    input,
    Term::Lit {
      value: Literal::Str { value },
    },
  ))
}

fn num_suffix_parser<X: Clone>(input: Span<X>) -> Res<NumSuffix, X> {
  let suffixes = alt((
    tag("i8"),
    tag("i16"),
    tag("i32"),
    tag("i64"),
    tag("u8"),
    tag("u16"),
    tag("u32"),
    tag("u64"),
    tag("f32"),
    tag("f64"),
  ));
  let (input, s) = recognize(opt(suffixes)).parse(input)?;
  let suffix = if s.fragment().is_empty() {
    NumSuffix::I64
  } else {
    NumSuffix::from_suffix(s.fragment()).unwrap_or(NumSuffix::I64)
  };
  Ok((input, suffix))
}

fn num_literal<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, value) = i64(input)?;
  let (input, suffix) = num_suffix_parser(input)?;
  Ok((input, num_suffix(value, suffix)))
}

fn float_literal<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, s) = recognize((
    opt(char('-')),
    take_while(|c: char| c.is_ascii_digit()),
    char('.'),
    take_while(|c: char| c.is_ascii_digit()),
  ))
  .parse(input)?;
  let value: f64 = s.fragment().parse().unwrap_or(0.0);
  let (input, suffix) = float_suffix_parser(input)?;
  Ok((input, float_suffix(value, suffix)))
}

fn float_suffix_parser<X: Clone>(input: Span<X>) -> Res<NumSuffix, X> {
  let (input, s) = recognize(opt(alt((tag("f32"), tag("f64"))))).parse(input)?;
  let suffix = if s.fragment().is_empty() {
    NumSuffix::F64
  } else {
    NumSuffix::from_suffix(s.fragment()).unwrap_or(NumSuffix::F64)
  };
  Ok((input, suffix))
}

fn lam_param<X: Clone>(input: Span<X>) -> Res<Param, X> {
  alt((
    map(identifier, |i| param(i, Hole)),
    delimited(
      (char('('), ws0),
      map(
        separated_pair(identifier, ws0, opt_type_annotation),
        |(name, typ)| param(name, typ),
      ),
      (ws0, char(')')),
    ),
  ))
  .parse(input)
}

fn cons_param<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  alt((
    map(identifier, |t| vec![param(id(""), ty(t))]),
    delimited(
      (char('('), ws0),
      alt((
        map(
          separated_pair(many1(terminated(identifier, ws0)), ws0, type_annotation),
          |(ids, typ)| ids.into_iter().map(|i| param(i, typ.clone())).collect(),
        ),
        map(type_expression, |t| vec![param(id(""), t)]),
      )),
      (ws0, char(')')),
    ),
  ))
  .parse(input)
}
fn cons_params<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  fold_many0(
    terminated(cons_param, ws0),
    Vec::new,
    |mut acc: Vec<_>, mut items: Vec<_>| {
      acc.append(&mut items);
      acc
    },
  )
  .parse(input)
}

fn implicit_param<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  delimited(
    (char('{'), ws0),
    map(
      separated_pair(many1(terminated(identifier, ws0)), ws0, type_annotation),
      |(ids, typ)| ids.into_iter().map(|i| param(i, typ.clone())).collect(),
    ),
    (ws0, char('}')),
  )
  .parse(input)
}

fn implicit_params<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  fold_many0(
    terminated(implicit_param, ws0),
    Vec::new,
    |mut acc: Vec<_>, mut items: Vec<_>| {
      acc.append(&mut items);
      acc
    },
  )
  .parse(input)
}

fn def_param<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  delimited(
    (char('('), ws0),
    map(
      separated_pair(many1(terminated(identifier, ws0)), ws0, type_annotation),
      |(ids, typ)| ids.into_iter().map(|i| param(i, typ.clone())).collect(),
    ),
    (ws0, char(')')),
  )
  .parse(input)
}
fn def_params<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  fold_many0(
    terminated(def_param, ws0),
    Vec::new,
    |mut acc: Vec<_>, mut items: Vec<_>| {
      acc.append(&mut items);
      acc
    },
  )
  .parse(input)
}

fn single_term<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((variable, literal, parens)).parse(input)
}

fn application<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, fun) = alt((variable, parens)).parse(input)?;
  let (input, args) = many1(preceded(ws1, single_term)).parse(input)?;

  Ok((input, apps(fun, args)))
}

fn lambda<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = alt((tag("\\"), terminated(tag("fn"), ws1), tag("ꟛ"))).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = many1(terminated(lam_param, ws0)).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("=>")(input)?;
  let (input, _) = ws0(input)?;
  let (input, body) = term(input)?;

  Ok((input, lams(params, body)))
}

fn assignment_operator<X: Clone>(input: Span<X>) -> Res<(), X> {
  map(preceded(ws0, tag(":=")), |_| ()).parse(input)
}

fn parens<X: Clone>(input: Span<X>) -> Res<Term, X> {
  delimited(terminated(tag("("), ws0), term, preceded(ws0, tag(")"))).parse(input)
}

fn match_case_parser<X: Clone>(input: Span<X>) -> Res<MatchCase, X> {
  map(
    separated_pair(
      separated_pair(identifier, ws0, many0(terminated(identifier, ws0))),
      (ws0, tag("=>"), ws0),
      term,
    ),
    |((name, args), value)| case(name, args, value),
  )
  .parse(input)
}

fn match_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = tag("match")(input)?;
  let (input, _) = ws1(input)?;
  let (input, value) = term(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("{")(input)?;
  let (input, cases) =
    many1(delimited(ws0, match_case_parser, (ws0, opt(char(','))))).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("}").parse(input)?;

  Ok((input, match_term(value, cases)))
}

enum DoStatement {
  Let { name: Identifier, value: Term },
  Bind { name: Identifier, value: Term },
  Return { value: Term },
  Expr { value: Term },
}

fn do_statement<X: Clone>(input: Span<X>) -> Res<DoStatement, X> {
  alt((
    map(
      preceded((tag("return"), ws1), (term, opt(char(';')))),
      |(value, _)| DoStatement::Return { value },
    ),
    map(
      (
        tag("let"),
        ws1,
        name,
        ws0,
        tag("<-"),
        ws0,
        term,
        opt(char(';')),
      ),
      |(_, _, name, _, _, _, value, _)| DoStatement::Bind { name, value },
    ),
    map(
      (
        tag("let"),
        ws1,
        name,
        ws0,
        assignment_operator,
        ws0,
        term,
        opt(char(';')),
      ),
      |(_, _, name, _, _, _, value, _)| DoStatement::Let { name, value },
    ),
    map((term, opt(char(';'))), |(value, _)| DoStatement::Expr {
      value,
    }),
  ))
  .parse(input)
}

fn do_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = tag("do")(input)?;
  let (input, _) = ws1(input)?;
  let (input, _) = char('{')(input)?;
  let (input, _) = ws0(input)?;

  let (input, stmts) = many0(preceded(ws0, do_statement)).parse(input)?;

  let (input, _) = ws0(input)?;
  let (input, _) = char('}')(input)?;

  let body = desugar_do_statements(stmts);
  Ok((input, body))
}

fn desugar_do_statements(stmts: Vec<DoStatement>) -> Term {
  let mut stmts_iter = stmts.into_iter().rev();

  let mut body = match stmts_iter.next() {
    Some(DoStatement::Return { value }) => value,
    Some(DoStatement::Expr { value }) => value,
    Some(DoStatement::Let { name, value }) => lets(
      vec![LetVar {
        name,
        typ: Term::Hole,
        value,
      }],
      Term::Hole,
    ),
    Some(DoStatement::Bind { name, value }) => {
      let body = Term::Hole;
      let lambda_body = lets(
        vec![LetVar {
          name: name.clone(),
          typ: Term::Hole,
          value: Term::Hole,
        }],
        body,
      );
      let lambda = lam(param(name, Term::Hole), lambda_body);
      app(pvar(vec!["Monad", "bind"]), app(value, lambda))
    }
    None => Term::Hole,
  };

  for stmt in stmts_iter {
    match stmt {
      DoStatement::Return { value } => {
        body = app(pvar(vec!["Monad", "pure"]), value);
      }
      DoStatement::Expr { value } => {
        let underscore = param(id("_"), Term::Hole);
        let lambda = lam(underscore, body);
        body = app(pvar(vec!["Monad", "bind"]), app(value, lambda));
      }
      DoStatement::Let { name, value } => {
        body = lets(
          vec![LetVar {
            name,
            typ: Term::Hole,
            value,
          }],
          body,
        );
      }
      DoStatement::Bind { name, value } => {
        let lambda = lam(param(name, Term::Hole), body);
        body = app(pvar(vec!["Monad", "bind"]), app(value, lambda));
      }
    }
  }

  body
}

fn ann_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  delimited(
    (char('('), ws0),
    map(
      separated_pair(term, (ws0, char(':'), ws0), type_expression),
      |(term, typ)| Term::Ann {
        term: Box::new(term),
        typ: Box::new(typ),
      },
    ),
    (ws0, char(')')),
  )
  .parse(input)
}

fn if_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = tag("if")(input)?;
  let (input, _) = ws1(input)?;
  let (input, value) = term(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("then")(input)?;
  let (input, _) = ws1(input)?;
  let (input, then) = term(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("else")(input)?;
  let (input, _) = ws1(input)?;
  let (input, els) = term(input)?;

  Ok((input, if_term(value, then, els)))
}

fn let_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = tag("let")(input)?;
  let (input, _) = ws1(input)?;
  let (input, let_vars) = many1(map(
    preceded(
      ws0,
      (
        terminated(
          (name, preceded(ws0, opt_type_annotation)),
          (ws0, assignment_operator),
        ),
        delimited(ws0, term, (ws0, opt(char(';')))),
      ),
    ),
    |((name, typ), value)| LetVar { name, typ, value },
  ))
  .parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("in")(input)?;
  let (input, _) = ws1(input)?;
  let (input, term) = term(input)?;

  Ok((input, lets(let_vars, term)))
}

fn infix_symbol<X: Clone>(input: Span<X>) -> Res<Operator, X> {
  let (input, op) = alt((
    tag(">>="),
    tag("<*>"),
    tag("<|>"),
    tag("=="),
    tag("!="),
    tag(">>"),
    tag("<<"),
    tag("|>"),
    tag("<|"),
    tag("++"),
    tag("&&"),
    tag("||"),
    tag("="),
    tag("*"),
    tag("/"),
    tag("+"),
    tag("-"),
    tag("."),
  ))
  .parse(input)?;

  Ok((input, Operator::new(op.into_fragment().into())))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Associativity {
  Left,
  Right,
}

fn operator_precedence(op: &Operator) -> Option<(u8, Associativity)> {
  match op.as_str() {
    "|>" => Some((5, Associativity::Left)),
    "<|" => Some((5, Associativity::Right)),
    ">>=" => Some((10, Associativity::Right)),
    "." => Some((12, Associativity::Right)),
    "<*>" => Some((15, Associativity::Left)),
    "<|>" => Some((20, Associativity::Left)),
    "||" => Some((25, Associativity::Right)),
    "&&" => Some((30, Associativity::Right)),
    "==" | "!=" | "=" => Some((40, Associativity::Left)),
    "++" => Some((50, Associativity::Right)),
    ">>" | "<<" => Some((60, Associativity::Left)),
    "+" | "-" => Some((65, Associativity::Left)),
    "*" | "/" => Some((70, Associativity::Left)),
    _ => None,
  }
}

fn operator<X: Clone>(input: Span<X>) -> Res<NameRef, X> {
  alt((
    map(infix_symbol, NameRef::Op),
    map(delimited(char('`'), identifier, char('`')), |i| {
      NameRef::Id(i)
    }),
  ))
  .parse(input)
}

fn path_expression<X: Clone>(input: Span<X>) -> Res<ModulePath, X> {
  map(
    separated_pair(
      terminated(identifier, ws0),
      tag("."),
      preceded(
        ws0,
        alt((
          path_expression,
          map(identifier, |i| ModulePath::new(vec![i])),
        )),
      ),
    ),
    |(left, right)| ModulePath::new(vec![left]).extend(right),
  )
  .parse(input)
}

fn base_term<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((
    do_parser,
    let_parser,
    if_parser,
    match_parser,
    type_expression,
    ann_parser,
    variable,
    operator_var,
    literal,
    lambda,
    application,
    parens,
  ))
  .parse(input)
}

fn parse_expr<X: Clone>(input: Span<X>, min_prec: u8) -> Res<Term, X> {
  let (input, mut lhs) = base_term(input)?;
  let (mut input, _) = ws0(input)?;

  loop {
    let peek_input = input.clone();
    let (_, op_name) = match operator(peek_input) {
      Ok(r) => r,
      Err(_) => break,
    };

    let NameRef::Op(op) = op_name else { break };
    let Some((prec, assoc)) = operator_precedence(&op) else {
      break;
    };

    if prec < min_prec {
      break;
    }

    let (new_input, _) = operator(input)?;
    let (new_input, _) = ws0(new_input)?;

    let next_prec = match assoc {
      Associativity::Left => prec + 1,
      Associativity::Right => prec,
    };

    let (new_input, rhs) = parse_expr(new_input, next_prec)?;
    let (new_input, _) = ws0(new_input)?;

    lhs = opr(lhs, NameRef::Op(op), rhs);
    input = new_input;
  }

  Ok((input, lhs))
}

fn binop<X: Clone>(input: Span<X>) -> Res<Term, X> {
  parse_expr(input, 0)
}

fn literal<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((
    list_literal,
    string_literal,
    float_literal,
    num_literal,
    struct_val_parser,
  ))
  .parse(input)
}

fn list_literal<X: Clone>(input: Span<X>) -> Res<Term, X> {
  delimited(
    (char('['), ws0),
    map(
      many0(terminated(term, (ws0, opt(char(',')), ws0))),
      |elements: Vec<Term>| desugar_list_literal(elements),
    ),
    (ws0, char(']')),
  )
  .parse(input)
}

fn desugar_list_literal(elements: Vec<Term>) -> Term {
  let empty = pvar(vec!["FromListLiteral", "empty"]);
  elements.into_iter().rev().fold(empty, |acc, elem| {
    app(app(pvar(vec!["FromListLiteral", "cons"]), elem), acc)
  })
}

pub fn term<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, start) = info(input)?;
  let (input, term) = binop(input)?;
  let (input, end) = info(input)?;
  let loc = SourceRange::new(start.into(), end.into());
  Ok((input, ctx(term, loc)))
}

fn def_name<X: Clone>(input: Span<X>) -> Res<ModulePath, X> {
  alt((path_expression, map(name, ModulePath::single))).parse(input)
}

fn wrap_args(args: Vec<AttrArg>) -> AttrArg {
  if args.len() == 1 {
    args.into_iter().next().unwrap()
  } else {
    AttrArg::Group(args)
  }
}

fn attr_arg_parser<X: Clone>(input: Span<X>) -> Res<Vec<AttrArg>, X> {
  alt((
    // Named args block: {name := value, name2 := value2,}
    delimited(
      (char('{'), ws0),
      many1(terminated(
        preceded(
          ws0,
          (identifier, ws0, tag(":="), ws0, attr_arg_parser).map(|(name, _, _, _, args)| {
            AttrArg::Named {
              name,
              value: Box::new(wrap_args(args)),
            }
          }),
        ),
        opt(char(',')),
      )),
      (ws0, char('}')),
    ),
    // Group block: [item1, item2,] — each item parsed with full attr_arg_parser
    delimited(
      (char('['), ws0),
      many1(terminated(preceded(ws0, attr_arg_parser), opt(char(',')))),
      (ws0, char(']')),
    )
    .map(|vecs| vec![AttrArg::Group(vecs.into_iter().flatten().collect())]),
    // Single positional arg: "string", 42, ident
    map(
      alt((
        map(string_literal, |t| {
          if let Term::Lit {
            value: Literal::Str { value: s },
          } = t
          {
            AttrArg::Str(s)
          } else {
            AttrArg::Str(String::new())
          }
        }),
        map(i64, AttrArg::Num),
        map(identifier, AttrArg::Ident),
      )),
      |arg| vec![arg],
    ),
  ))
  .parse(input)
}

fn attribute_parser<X: Clone>(input: Span<X>) -> Res<Attribute, X> {
  delimited(
    (tag("@["), ws0),
    (name, many0(preceded(ws1, attr_arg_parser))),
    (ws0, tag("]")),
  )
  .map(|(name, args_vecs)| Attribute {
    name,
    args: args_vecs.into_iter().flatten().collect(),
  })
  .parse(input)
}

fn opt_attributes<X: Clone>(input: Span<X>) -> Res<Vec<Attribute>, X> {
  many0(attribute_parser).parse(input)
}

#[cfg(test)]
fn def_parser(input: Span) -> Res<Def> {
  def_with_attrs_parser(Vec::new(), input)
}

fn def_with_attrs_parser(attrs: Vec<Attribute>, input: Span) -> Res<Def> {
  let (input, _) = ws0(input)?;
  let (input, _) = tag("def")(input)?;
  let (input, _) = ws1(input)?;
  let (input, name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, type_cons) =
    map(opt(all_type_cons_parser), |t| t.unwrap_or_default()).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, implicit_params) = implicit_params(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = def_params(input)?;
  let (input, return_typ) = def_type_annotation(input)?;
  let (input, _) = ws0(input)?;

  let is_native = attrs.iter().any(|a| a.name.as_str() == "native");

  let (input, term) = if is_native {
    let native_name = attrs
      .iter()
      .find(|a| a.name.as_str() == "native")
      .and_then(|a| {
        a.args.iter().find_map(|arg| match arg {
          AttrArg::Ident(id) => Some(id.clone()),
          AttrArg::Named { name, value } if name.as_str() == "name" => {
            if let AttrArg::Ident(id) = value.as_ref() {
              Some(id.clone())
            } else {
              None
            }
          }
          _ => None,
        })
      })
      .ok_or_else(|| {
        nom::Err::Failure(ParseError::new(
          input.clone(),
          error::ParseErrorKind::Native("native attribute requires a name".into()),
        ))
      })?;

    let def = def_with_native(native_name, name.clone(), params.clone(), return_typ, attrs)
      .map_err(|e| {
        nom::Err::Failure(ParseError::new(
          input.clone(),
          error::ParseErrorKind::Native(e),
        ))
      })?;
    return Ok((input, def));
  } else if input.fragment().starts_with("{") {
    let (input, _) = char('{')(input)?;
    let (input, _) = ws0(input)?;
    let (input, stmts) = many0(preceded(ws0, do_statement)).parse(input)?;
    let (input, _) = ws0(input)?;
    let (input, _) = char('}')(input)?;
    let body = desugar_do_statements(stmts);
    (input, body)
  } else {
    let (input, _) = assignment_operator(input)?;
    let (input, _) = ws0(input)?;
    let (input, term) = term(input)?;
    (input, term)
  };

  if params.is_empty() {
    Ok((input, def(name, type_cons, return_typ, term, attrs)))
  } else {
    let mut full_typ = pi_typs(
      params.iter().map(|p| *p.typ.clone()).collect::<Vec<_>>(),
      return_typ,
    );
    if !implicit_params.is_empty() {
      full_typ = foralls(implicit_params, full_typ);
    }
    let body = lams(params, term);
    Ok((input, def(name, type_cons, full_typ, body, attrs)))
  }
}

fn infix_parser(input: Span) -> Res<Infix> {
  let (input, _) = tag("infix")(input)?;
  let (input, _) = ws1(input)?;
  let (input, operator) = operator_parens(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = assignment_operator(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = def_name(input)?;

  Ok((input, infix(operator, name)))
}

fn class_def_parser<X: Clone>(input: Span<X>) -> Res<ClassDef, X> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = tag("def")(input)?;
  let (input, _) = ws1(input)?;
  let (input, name) = name(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = cons_params(input)?;
  let (input, return_typ) = def_type_annotation(input)?;
  let (input, _) = ws0(input)?;
  let (input, default) = opt(preceded((assignment_operator, ws0), term)).parse(input)?;

  if params.is_empty() {
    Ok((input, class_def(name, return_typ, default, attrs)))
  } else {
    let full_typ = pi_typs(
      params.iter().map(|p| *p.typ.clone()).collect::<Vec<_>>(),
      return_typ,
    );
    let default_term = default.map(|d| lams(params, d));
    Ok((input, class_def(name, full_typ, default_term, attrs)))
  }
}

fn class_inner_parser(input: Span) -> Res<Vec<ClassDef>> {
  delimited((char('{'), ws0), many1(class_def_parser), (ws0, char('}'))).parse(input)
}

fn type_cons_parser<X: Clone>(input: Span<X>) -> Res<TypeConstraint, X> {
  map(
    separated_pair(def_name, ws1, many1(terminated(identifier, ws0))),
    |(class, args)| type_constraint(class, args),
  )
  .parse(input)
}

fn all_type_cons_parser<X: Clone>(input: Span<X>) -> Res<Vec<TypeConstraint>, X> {
  delimited(
    (char('['), ws0),
    many1(terminated(type_cons_parser, (ws0, opt(char(',')), ws0))),
    (ws0, char(']')),
  )
  .parse(input)
}

fn class_parser(input: Span) -> Res<Inductive> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = tag("class")(input)?;
  let (input, _) = ws0(input)?;
  let (input, constraints) = opt(all_type_cons_parser).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = many1(terminated(lam_param, ws0)).parse(input)?;
  let (input, defs) = class_inner_parser(input)?;

  Ok((
    input,
    class(
      name,
      constraints.unwrap_or_else(Vec::new),
      params,
      defs,
      attrs,
    ),
  ))
}

fn instance_inner_parser(input: Span) -> Res<Vec<Def>> {
  delimited(
    (char('{'), ws0),
    many1(delimited(ws0, def_with_attrs_inner_parser, ws0)),
    (ws0, char('}')),
  )
  .parse(input)
}

fn def_with_attrs_inner_parser(input: Span) -> Res<Def> {
  let (input, attrs) = opt_attributes(input)?;
  def_with_attrs_parser(attrs, input)
}

fn instance_parser(input: Span) -> Res<Instance> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = tag("instance")(input)?;
  let (input, _) = ws0(input)?;
  let (input, constraints) = opt(all_type_cons_parser).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = opt(terminated(def_name, (ws0, char(':')))).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, class_name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, args) = many0(terminated(single_term, ws0)).parse(input)?;
  let (input, defs) = instance_inner_parser(input)?;

  Ok((
    input,
    instance(
      name,
      class_name,
      constraints.unwrap_or_else(Vec::new),
      args,
      defs,
      attrs,
    ),
  ))
}

#[derive(Clone, Debug)]
struct InductiveExtra {
  induct_type: Term,
  induct_name: ModulePath,
}
fn constructor_parser<'a>(
  input: Span<'a, InductiveExtra>,
) -> Res<'a, InductConstructor, InductiveExtra> {
  let extra = input.extra().clone();
  let (input, name) = identifier(input)?;
  let (input, _) = ws0(input)?;
  let (input, implicit_params) = implicit_params(input)?;
  let (input, params) = set_res_extra(cons_params(input.map_extra(|_| ())), extra.clone())?;
  let (input, return_typ) = opt_type_annotation(input)?;
  let (input, _) = ws0(input)?;

  let return_typ = return_typ.replace_hole(|| extra.induct_type.clone());
  if params.is_empty() {
    Ok((
      input,
      induct_constructor(extra.induct_name, name, return_typ, params),
    ))
  } else {
    let mut full_typ = pi_typs(
      params.iter().map(|p| *p.typ.clone()).collect::<Vec<Term>>(),
      return_typ,
    );
    if !implicit_params.is_empty() {
      full_typ = foralls(implicit_params, full_typ);
    }
    Ok((
      input,
      induct_constructor(extra.induct_name, name, full_typ, params),
    ))
  }
}

fn inductive_inner_parser<'a>(
  input: Span<'a, InductiveExtra>,
) -> Res<'a, Vec<InductConstructor>, InductiveExtra> {
  delimited(
    (char('{'), ws0),
    many0(terminated(constructor_parser, (ws0, opt(char(',')), ws0))),
    (ws0, char('}')),
  )
  .parse(input)
}

fn inductive_parser(input: Span) -> Res<Inductive> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = tag("type")(input)?;
  let (input, _) = ws0(input)?;
  let (input, constraints) = opt(all_type_cons_parser).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = many0(terminated(lam_param, ws0)).parse(input)?;
  let (input, typ) = opt_type_annotation(input)?;
  let (input, _) = ws0(input)?;
  let induct_type = if params.is_empty() {
    mpvar(name.clone())
  } else {
    apps(
      mpvar(name.clone()),
      params.iter().map(|p| var_id(p.name.clone())).collect(),
    )
  };
  let (input, constructors) = set_res_extra(
    inductive_inner_parser(input.map_extra(|_| InductiveExtra {
      induct_type,
      induct_name: name.clone(),
    })),
    (),
  )?;

  Ok((
    input,
    inductive(
      name,
      constraints.unwrap_or_else(Vec::new),
      params,
      typ,
      constructors,
      attrs,
    ),
  ))
}

fn struct_field_parser<X: Clone>(input: Span<X>) -> Res<StructField, X> {
  let (input, name) = identifier(input)?;
  let (input, _) = ws0(input)?;
  let (input, typ) = def_type_annotation(input)?;
  let (input, _) = ws0(input)?;
  let (input, default) = opt(preceded((assignment_operator, ws0), term)).parse(input)?;

  Ok((input, stru_field(name, typ, default)))
}

fn struct_inner_parser<X: Clone>(input: Span<X>) -> Res<Vec<StructField>, X> {
  delimited(
    (char('{'), ws0),
    many1(terminated(struct_field_parser, (ws0, char(','), ws0))),
    (ws0, char('}')),
  )
  .parse(input)
}

fn struct_parser<X: Clone>(input: Span<X>) -> Res<Inductive, X> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = tag("struct")(input)?;
  let (input, _) = ws0(input)?;
  let (input, constraints) =
    map(opt(all_type_cons_parser), |t| t.unwrap_or_default()).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = cons_params(input)?;
  let (input, fields) = struct_inner_parser(input)?;

  Ok((input, stru(name, constraints, params, fields, attrs)))
}

fn struct_val_field_parser<X: Clone>(input: Span<X>) -> Res<(Identifier, Term), X> {
  let (input, name) = identifier(input)?;
  let (input, _) = ws0(input)?;
  let (input, value) = preceded((assignment_operator, ws0), term).parse(input)?;

  Ok((input, (name, value)))
}

fn struct_val_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  map(
    delimited(
      (char('{'), ws0),
      many0(terminated(
        struct_val_field_parser,
        (ws0, opt(char(',')), ws0),
      )),
      (ws0, char('}')),
    ),
    |fields| map_term(fields.into_iter().collect()),
  )
  .parse(input)
}

fn use_parser(input: Span) -> Res<Use> {
  let (input, start) = info(input)?;
  let (input, _) = tag("use")(input)?;
  let (input, _) = ws1(input)?;
  let (input, module_path) =
    alt((path_expression, map(identifier, ModulePath::single))).parse(input)?;
  let (input, end) = info(input)?;
  let source_location = SourceRange::new(start.into(), end.into());
  Ok((
    input,
    Use {
      module_path,
      source_location,
    },
  ))
}

fn open_parser(input: Span) -> Res<Open> {
  let (input, start) = info(input)?;
  let (input, _) = tag("open")(input)?;
  let (input, _) = ws1(input)?;
  let (input, module_path) =
    alt((path_expression, map(identifier, ModulePath::single))).parse(input)?;
  let (input, end) = info(input)?;
  let source_location = SourceRange::new(start.into(), end.into());

  Ok((
    input,
    Open {
      module_path,
      source_location,
    },
  ))
}
fn decl_parser(input: Span) -> Res<SourceContext<Decl>> {
  let (input, start) = info(input)?;
  let (input, attrs) = opt_attributes(input)?;
  let (input, decl) = alt((
    map(use_parser, Decl::Use),
    map(open_parser, Decl::Open),
    map(
      |input| def_with_attrs_parser(attrs.clone(), input),
      Decl::Def,
    ),
    map(class_parser, Decl::Type),
    map(instance_parser, Decl::Ins),
    map(struct_parser, Decl::Type),
    map(inductive_parser, Decl::Type),
    map(infix_parser, Decl::Infix),
  ))
  .parse(input)?;
  let (input, end) = info(input)?;
  let loc = SourceRange::new(start.into(), end.into());
  Ok((input, SourceContext::new(loc, decl)))
}

#[derive(Debug, Clone)]
pub enum ReplInput {
  Decls(Decl),
  Term(Term),
  // TODO Command,
}

impl Display for ReplInput {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ReplInput::Decls(defs) => write!(f, "{defs:#?}"),
      ReplInput::Term(term) => write!(f, "{term}"),
    }
  }
}

pub fn parse_term(input: &str) -> Result<Term, ParseTermError> {
  let span: Span = input.into();
  let (_, t) = delimited(ws0, term, ws0)
    .parse(span)
    .finish()
    .map_err(|e| {
      let err: OwnedError = e.into();
      ParseTermError {
        source: input.to_string(),
        error: err,
      }
    })?;
  Ok(t)
}

pub fn repl_parser(input: &str) -> Result<ReplInput, ReplParserError> {
  let (_, r) = delimited(
    ws0,
    alt((
      map(term, ReplInput::Term),
      map(decl_parser, |t| ReplInput::Decls(t.value)),
    )),
    ws0,
  )
  .parse(input.into())
  .finish()
  .map_err(|r| ReplParserError {
    source: input.to_string(),
    error: r.into(),
  })?;
  Ok(r)
}

fn decls_parser(input: Span) -> Res<Vec<SourceContext<Decl>>> {
  let (input, decls) = many0(delimited(ws0, decl_parser, ws0)).parse(input)?;
  let (input, _) = eof(input)?;
  Ok((input, decls))
}

pub fn parse_file(input: &str) -> Result<Vec<SourceContext<Decl>>, ParseFileError> {
  let span = Span::new(input);
  match decls_parser(span).finish() {
    Ok((_, decls)) => Ok(decls),
    Err(e) => {
      let err: OwnedError = e.into();
      Err(ParseFileError {
        source: input.to_string(),
        error: err,
      })
    }
  }
}
