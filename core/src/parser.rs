mod error;
pub mod locate;
mod string;
#[cfg(test)]
pub mod test;

use std::fmt::Display;

use crate::{
  parser::{
    error::{ParseError, ReplParserError},
    string::parse_char_literal,
  },
  term::{
    AttrArg, Attribute, ClassDef, Decl, DeclGenDef, Def, Documentation, Identifier,
    InductConstructor, Inductive, Infix, Instance, LetVar, Literal, MatchCase, ModulePath,
    Multiplicity, NameRef, NumSuffix, Open, OpenFilter, Operator, Param, SourceContext,
    SourceRange, StructField,
    Term::{self, Hole, Var},
    TypeConstraint, Use, UseFilter, UseItem, Visibility, app, apps, case, class, class_def, ctx,
    def, def_with_native, float_suffix, forall, foralls, id, if_term, induct_constructor,
    inductive, infix, instance, ivar, lam, lams, lets, match_term,
    module::ParsedModule,
    mpvar, num_suffix, opr, param, param_with_attrs, param_with_default, param_with_mult, pi_name,
    pi_typs, pi_with_mult, pvar, stru, stru_field_with_mult, type_constraint, var_id,
  },
};
use locate::{LocatedSpan, info};
use nom::{
  Finish, IResult, Input, Parser,
  branch::alt,
  bytes::complete::{tag, take_until, take_while},
  character::complete::{
    alpha1, char, digit1, hex_digit1, i64, line_ending, multispace0, multispace1, not_line_ending,
    space0,
  },
  combinator::{eof, map, not, opt, peek, recognize, success, verify},
  error::context,
  multi::{fold_many0, many0, many1},
  sequence::{delimited, pair, preceded, separated_pair, terminated},
};
use string::parse_string_literal;

pub use error::{OwnedError, ParseFileError, ParseTermError, display_source_context};
pub type Span<'a, X = ()> = LocatedSpan<&'a str, X>;
type E<'a, X = ()> = ParseError<Span<'a, X>>;
type Res<'a, O, X = ()> = IResult<Span<'a, X>, O, E<'a, X>>;

impl<'a> From<ParseError<Span<'a>>> for OwnedError {
  fn from(value: ParseError<Span>) -> Self {
    ParseError {
      input: value.input.into(),
      expected: value.expected,
      kind: value.kind,
    }
  }
}

pub fn set_res_extra<X: Clone, Y: Clone, T>(res: Res<T, X>, extra: Y) -> Res<T, Y> {
  res
    .map(|(i, o)| (i.map_extra(|_| extra.clone()), o))
    .map_err(|e| e.map(|e| e.map_input(|i| i.map_extra(|_| extra))))
}

const RESERVED_KEYWORDS: &[&str] = &[
  "def", "defmacro", "let", "in", "use", "open", "class", "struct", "instance", "type", "fn", "ꟛ",
  "match", "if", "then", "else", "infix", "return", "for", "do", "quote", "with",
];
const RESERVED_NAMES: &[&str] = &["Type", "Pred", "Sort"];

fn is_reserved_keyword(s: &str) -> bool {
  RESERVED_KEYWORDS.contains(&s)
}
fn is_reserved_name(s: &str) -> bool {
  RESERVED_NAMES.contains(&s)
}

/// Accepts letters/num/_ as identifier, rejecting reserved keywords with a nom error.
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

/// Like identifier but produces native errors for reserved keywords/names.
fn name<X: Clone>(input: Span<X>) -> Res<Identifier, X> {
  let (input, name) = recognize((
    alt((alpha1, tag("_"))),
    take_while(|c: char| c.is_alphanumeric() || c == '_'),
  ))
  .parse(input)?;
  let id_str = name.fragment();
  if is_reserved_keyword(id_str) {
    return Err(nom::Err::Error(ParseError::new(
      input,
      error::ParseErrorKind::Native(format!("'{id_str}' is a reserved keyword")),
    )));
  }
  if is_reserved_name(id_str) {
    return Err(nom::Err::Error(ParseError::new(
      input,
      error::ParseErrorKind::Native(format!("'{id_str}' is a reserved name")),
    )));
  }
  Ok((input, id(name.into_fragment())))
}

fn line_comment<X: Clone>(input: Span<X>) -> Res<Span<X>, X> {
  preceded(tag("//"), not_line_ending).parse(input)
}

/// Matches line comments but not doc comments
fn line_comment_not_doc<X: Clone>(input: Span<X>) -> Res<Span<X>, X> {
  preceded((tag("//"), not(char('/'))), not_line_ending).parse(input)
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

fn doc_comment<X: Clone>(input: Span<X>) -> Res<Documentation, X> {
  // NOTE: the whitespace skipped between `///` and a doc line's text must
  // be same-line-only (`space0`: spaces/tabs), NOT the general `ws0`
  // (which also matches `line_comment` — and `///` itself starts with the
  // `//` prefix `line_comment` looks for). Using `ws0` here used to let an
  // EMPTY `///` line's trailing `ws0` swallow the newline plus treat the
  // next `///`-prefixed line as "just another comment to skip", cascading
  // into consuming an unrelated declaration (e.g. a `use`) that happened
  // to follow as if it were that empty line's doc text.
  map(
    many1(terminated(
      preceded(tag("///"), preceded(space0, not_line_ending)),
      line_ending,
    )),
    |lines| Documentation::new(lines.join("\n").trim().to_string()),
  )
  .parse(input)
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
  delimited(
    char('('),
    infix_symbol,
    context("closing parenthesis for operator reference", char(')')),
  )
  .parse(input)
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
        preceded(
          (
            ws0,
            context("closing brace for forall type", char('}')),
            ws0,
            tag("->"),
            ws0,
          ),
          type_top_expression,
        ),
      ),
    ),
    |(name, typ, body)| forall(param(name, typ), body),
  )
  .parse(input)
}

fn type_base_expression<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((sort_parser, application, variable, type_parens)).parse(input)
}

fn sort_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = tag("Sort")(input)?;
  let (input, _) = ws1(input)?;
  let (input, level_str) = digit1(input)?;
  let level: u64 = level_str.fragment().parse().unwrap_or(0);
  Ok((input, Term::Sort { level }))
}

fn pi_type_expression<X: Clone>(input: Span<X>) -> Res<Term, X> {
  map(
    separated_pair(
      alt((
        map(
          delimited(
            (char('('), ws0),
            separated_pair(identifier, (ws0, char(':'), ws0), type_base_expression),
            (
              ws0,
              context("closing parenthesis for function type parameter", char(')')),
            ),
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
    preceded(
      ws0,
      context("closing parenthesis for type expression", tag(")")),
    ),
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
  let original = input.clone();
  let (input, value) = set_res_extra(
    parse_string_literal(input.into_fragment())
      .map_err(|e| e.map(|f: nom::error::Error<&str>| f.into()))
      .map(|(i, v)| {
        let consumed = original.input_len() - i.len();
        (original.take_from(consumed), v)
      }),
    extra,
  )?;
  Ok((
    input,
    Term::Lit {
      value: Literal::Str { value },
    },
  ))
}

fn char_literal<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let extra = input.extra().clone();
  let input = input.map_extra(|_| ());
  let original = input.clone();
  let (input, value) = set_res_extra(
    parse_char_literal(input.into_fragment())
      .map_err(|e| e.map(|f: nom::error::Error<&str>| f.into()))
      .map(|(i, v)| {
        let consumed = original.input_len() - i.len();
        (original.take_from(consumed), v)
      }),
    extra,
  )?;
  Ok((
    input,
    Term::Lit {
      value: Literal::Char { value },
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

/// `0xBADBEEF` / `0XFF` hex integer literals, with the same optional
/// leading `-` and trailing numeric suffix (`0xFFu32`) as `num_literal`.
/// Parses the digits as `u64` (not `i64`, unlike `num_literal`) and
/// bit-reinterprets — so a full-width literal like
/// `0xFFFFFFFFFFFFFFFFu64` round-trips correctly (as `u64::MAX`, stored
/// as `-1` in the shared `i64` payload) instead of being rejected for
/// having the top bit set, which `i64::from_str_radix` would do.
fn hex_literal<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, sign) = opt(char('-')).parse(input)?;
  let (input, _) = alt((tag("0x"), tag("0X"))).parse(input)?;
  let (input, digits) = hex_digit1(input)?;
  let unsigned: u64 = u64::from_str_radix(digits.fragment(), 16).map_err(|_| {
    nom::Err::Failure(ParseError::new(
      input.clone(),
      error::ParseErrorKind::Native(format!("invalid hex literal '0x{}'", digits.fragment())),
    ))
  })?;
  let magnitude = unsigned as i64;
  let value = if sign.is_some() {
    magnitude.wrapping_neg()
  } else {
    magnitude
  };
  let (input, suffix) = num_suffix_parser(input)?;
  Ok((input, num_suffix(value, suffix)))
}

fn num_literal<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, num_str) = recognize(pair(opt(char('-')), digit1)).parse(input)?;
  let value: i64 = num_str.fragment().parse().map_err(|_| {
    nom::Err::Failure(ParseError::new(
      input.clone(),
      error::ParseErrorKind::Native(format!("invalid numeric literal '{}'", num_str.fragment())),
    ))
  })?;
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

/// Parse multiplicity prefix: "%" = Erased, "!" = Linear, "?" = Affine, none = Many
fn multiplicity_prefix<X: Clone>(input: Span<X>) -> Res<Multiplicity, X> {
  map(opt(alt((char('%'), char('!'), char('?')))), |m| match m {
    Some('%') => Multiplicity::Zero,
    Some('!') => Multiplicity::Linear,
    Some('?') => Multiplicity::Affine,
    _ => Multiplicity::Many,
  })
  .parse(input)
}

fn lam_param<X: Clone>(input: Span<X>) -> Res<Param, X> {
  alt((
    map(identifier, |i| param(i, Hole)),
    delimited(
      (char('('), ws0),
      map(
        pair(
          multiplicity_prefix,
          pair(
            terminated(identifier, ws0),
            pair(
              opt_type_annotation,
              opt(preceded((ws0, tag(":="), ws0), term_inner)),
            ),
          ),
        ),
        |(mult, (name, (typ, default)))| {
          let mut p = param_with_default(name, typ, default);
          p.mult = mult;
          p
        },
      ),
      (
        ws0,
        context("closing parenthesis for function parameter", char(')')),
      ),
    ),
  ))
  .parse(input)
}

/// `#[arg]`-style attributes on a single named constructor parameter, e.g.
/// `compile (#[arg] verbose : Bool)` — consumed by `#[derive_cli]`
/// generation (`core/src/eval/derive_cli.rs`). Only meaningful ahead of the
/// named-identifiers-with-type-annotation form below; the bare-type-only
/// form (`some (A)`) has no name to attach per-field metadata to.
fn cons_param<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  alt((
    map(identifier, |t| vec![param(id(""), ivar(t))]),
    delimited(
      (char('('), ws0),
      map(
        (
          opt_attributes,
          ws0,
          alt((
            map(
              separated_pair(many1(terminated(identifier, ws0)), ws0, type_annotation),
              |(ids, typ)| {
                ids
                  .into_iter()
                  .map(|i| param(i, typ.clone()))
                  .collect::<Vec<Param>>()
              },
            ),
            map(type_expression, |t| vec![param(id(""), t)]),
          )),
        ),
        |(attrs, _, params): (Vec<Attribute>, _, Vec<Param>)| {
          if attrs.is_empty() {
            params
          } else {
            params
              .into_iter()
              .map(|p| param_with_attrs(p, attrs.clone()))
              .collect()
          }
        },
      ),
      (
        ws0,
        context("closing parenthesis for constructor parameter", char(')')),
      ),
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
      pair(
        multiplicity_prefix,
        separated_pair(many1(terminated(identifier, ws0)), ws0, type_annotation),
      ),
      |(mult, (ids, typ))| {
        ids
          .into_iter()
          .map(|i| param_with_mult(i, typ.clone(), mult.clone()))
          .collect()
      },
    ),
    (
      ws0,
      context("closing brace for implicit parameters", char('}')),
    ),
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
      pair(
        multiplicity_prefix,
        separated_pair(many1(terminated(identifier, ws0)), ws0, type_annotation),
      ),
      |(mult, (ids, typ))| {
        ids
          .into_iter()
          .map(|i| param_with_mult(i, typ.clone(), mult.clone()))
          .collect()
      },
    ),
    (
      ws0,
      context("closing parenthesis for function parameters", char(')')),
    ),
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

fn macro_call<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, name) = identifier(input)?;
  let (input, _) = char('!')(input)?;
  Ok((
    input,
    Term::Var {
      name: NameRef::Macro(name),
    },
  ))
}

/// An atomic term that does NOT include juxtaposition application, operator_var,
/// or type_expression. Guaranteed to terminate without recursive application parsing.
/// Used for application function and args.
fn term_inner<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((
    quote_parser,
    do_parser,
    let_parser,
    if_parser,
    match_parser,
    ann_parser,
    macro_call,
    variable,
    literal,
    lambda,
    tuple_or_parens,
  ))
  .parse(input)
}

/// A non-application term — `type_expression`, `term_inner`, plus standalone operator references.
/// `type_expression` is tried before `term_inner` to match the old `base_term` ordering
/// where `type_expression` was before `variable`, ensuring type expressions like `A -> B`
/// are parsed correctly inside parens.
fn non_app_term<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((type_expression, term_inner, operator_var)).parse(input)
}

fn application<X: Clone>(input: Span<X>) -> Res<Term, X> {
  // The function position must be a name/path, macro call, or parenthesized expression.
  // Literals, lambdas, etc. cannot be function heads — without this restriction,
  // `12 x` would parse as `App(12, x)` instead of just `12` followed by `x`.
  let (input, fun) = alt((macro_call, variable, parens)).parse(input)?;
  let (input, args) = many1(alt((preceded(ws1, term_inner), parens))).parse(input)?;

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
  delimited(
    terminated(tag("("), ws0),
    term,
    preceded(ws0, context("closing parenthesis for expression", tag(")"))),
  )
  .parse(input)
}

fn tuple_or_parens<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = (char('('), ws0).parse(input)?;
  let (input, first) = term(input)?;
  let (input, _) = ws0(input)?;
  let (input, has_comma) = opt(char(',')).parse(input)?;
  if has_comma.is_some() {
    let (input, _) = ws0(input)?;
    let (input, mut rest) = many0(terminated(term, (ws0, opt(char(',')), ws0))).parse(input)?;
    let mut elements = vec![first];
    elements.append(&mut rest);
    let (input, _) = (ws0, char(')')).parse(input)?;
    Ok((input, desugar_tuple_literal(elements)))
  } else {
    let (input, _) = char(')')(input)?;
    Ok((input, first))
  }
}

fn desugar_tuple_literal(elements: Vec<Term>) -> Term {
  let pair = pvar(vec!["Pair", "pair"]);
  let mut iter = elements.into_iter().rev();
  let last = iter.next().unwrap();
  let mut acc = last;
  for elem in iter {
    acc = app(app(pair.clone(), elem), acc);
  }
  acc
}

fn constructor_name<X: Clone>(input: Span<X>) -> Res<Identifier, X> {
  let (input, first) = identifier(input)?;
  let (input, rest) = many0(preceded((ws0, char('.'), ws0), identifier)).parse(input)?;
  if rest.is_empty() {
    Ok((input, first))
  } else {
    Ok((input, rest.last().unwrap().clone()))
  }
}

fn match_case_parser<X: Clone>(input: Span<X>) -> Res<MatchCase, X> {
  map(
    separated_pair(
      separated_pair(constructor_name, ws0, many0(terminated(identifier, ws0))),
      (ws0, tag("=>"), ws0),
      term,
    ),
    |((name, args), value)| case(name, args, value),
  )
  .parse(input)
}

fn match_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = tag("match")(input)?;
  let (input, _) = ws0(input)?;
  let (input, value) = term(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("{")(input)?;
  let (input, cases) =
    many1(delimited(ws0, match_case_parser, (ws0, opt(char(','))))).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = context("closing brace for match body", tag("}")).parse(input)?;

  Ok((input, match_term(value, cases)))
}

enum DoStatement {
  Let {
    name: Identifier,
    value: Term,
    typ: Term,
  },
  Bind {
    name: Identifier,
    value: Term,
    typ: Term,
  },
  Return {
    value: Term,
  },
  Expr {
    value: Term,
  },
}

fn do_statement<X: Clone>(input: Span<X>) -> Res<DoStatement, X> {
  alt((
    map(
      preceded((tag("return"), ws1), (term, opt(char(';')))),
      |(value, _)| DoStatement::Return { value },
    ),
    map(
      (
        delimited(
          (tag("let"), ws1),
          (terminated(name, ws0), opt_type_annotation),
          delimited(ws0, tag("<-"), ws0),
        ),
        terminated(term, opt(char(';'))),
      ),
      |((name, typ), value)| DoStatement::Bind { name, value, typ },
    ),
    map(
      (
        delimited(
          (tag("let"), ws1),
          (terminated(name, ws0), opt_type_annotation),
          delimited(ws0, assignment_operator, ws0),
        ),
        terminated(term, opt(char(';'))),
      ),
      |((name, typ), value)| DoStatement::Let { name, value, typ },
    ),
    map((term, opt(char(';'))), |(value, _)| DoStatement::Expr {
      value,
    }),
  ))
  .parse(input)
}

/// Custom parser for do block statements that preserves error positions.
/// Unlike many0(preceded(ws0, do_statement)), this parser doesn't reset
/// the input position when a statement fails to parse, ensuring errors
/// point to the actual problem location rather than an earlier position.
/// This parser does NOT consume the closing brace - it leaves that for the caller.
fn do_statements_parser<X: Clone>(input: Span<X>) -> Res<Vec<DoStatement>, X> {
  let mut input = input;
  let mut stmts = Vec::new();

  loop {
    // Consume leading whitespace
    let (new_input, _) = ws0(input)?;
    input = new_input;

    // Try to parse a statement
    match preceded(ws0, do_statement).parse(input.clone()) {
      Ok((new_input, stmt)) => {
        stmts.push(stmt);
        input = new_input;
      }
      Err(e) => {
        // If we failed to parse a statement, check if it's because we hit the closing brace
        // or if it's a real error that should be propagated
        if char::<_, E<X>>('}')(input.clone()).is_ok() {
          // We're at the closing brace, stop successfully
          break;
        } else {
          // Real error - propagate it with its position preserved
          return Err(e);
        }
      }
    }
  }

  Ok((input, stmts))
}

fn do_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = tag("do")(input)?;
  let (input, _) = ws1(input)?;
  let (input, _) = char('{')(input)?;
  let (input, _) = ws0(input)?;

  let (input, stmts) = do_statements_parser(input)?;

  let (input, _) = ws0(input)?;
  let (input, _) = context("closing brace for do block", char('}')).parse(input)?;

  let body = desugar_do_statements(stmts);
  Ok((input, body))
}

fn desugar_do_statements(stmts: Vec<DoStatement>) -> Term {
  let mut stmts_iter = stmts.into_iter().rev();

  let mut body = match stmts_iter.next() {
    Some(DoStatement::Return { value }) => app(pvar(vec!["Monad", "pure"]), value),
    Some(DoStatement::Expr { value }) => value,
    Some(DoStatement::Let { name, value, typ }) => {
      lets(vec![LetVar { name, typ, value }], Term::Hole)
    }
    Some(DoStatement::Bind { name, value, typ }) => {
      let body = Term::Hole;
      let lambda_body = lets(
        vec![LetVar {
          name: name.clone(),
          typ: typ.clone(),
          value: Term::Hole,
        }],
        body,
      );
      let lambda = lam(param(name, typ), lambda_body);
      app(app(pvar(vec!["Monad", "bind"]), value), lambda)
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
        body = app(app(pvar(vec!["Monad", "bind"]), value), lambda);
      }
      DoStatement::Let { name, value, typ } => {
        body = lets(vec![LetVar { name, typ, value }], body);
      }
      DoStatement::Bind { name, value, typ } => {
        let lambda = lam(param(name, typ), body);
        body = app(app(pvar(vec!["Monad", "bind"]), value), lambda);
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
    (
      ws0,
      context("closing parenthesis for type annotation", char(')')),
    ),
  )
  .parse(input)
}

fn if_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = tag("if")(input)?;
  let (input, _) = ws0(input)?;
  let (input, value) = term(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("then")(input)?;
  let (input, _) = ws0(input)?;
  let (input, then) = term(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("else")(input)?;
  let (input, _) = ws0(input)?;
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
  let (input, op) = alt([
    tag(">>="),
    tag("<*>"),
    tag("<|>"),
    tag("=="),
    tag("!="),
    tag(">="),
    tag("<="),
    tag(">>"),
    tag("<<"),
    tag("|>"),
    tag("<|"),
    tag("++"),
    tag("&&"),
    tag("||"),
    tag(">"),
    tag("<"),
    tag("="),
    tag("*"),
    tag("/"),
    tag("+"),
    tag("-"),
    tag("."),
    // No built-in meaning (unlike every other symbol above, which is
    // wired to a native or a prelude `infix` binding) — freed up from its
    // old role as the `@[...]` legacy attribute delimiter (see
    // `attribute_parser`) so library code can bind it to any function via
    // `infix (@) := someFunction`.
    tag("@"),
  ])
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
    "==" | "!=" | "=" | "<" | ">" | "<=" | ">=" => Some((40, Associativity::Left)),
    "++" | "@" => Some((50, Associativity::Right)),
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

fn quote_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  preceded(
    (tag("quote"), ws1, char('{'), ws0),
    terminated(
      term,
      (
        ws0,
        context("closing brace for quoted expression", char('}')),
      ),
    ),
  )
  .map(|t| Term::Quote { term: Box::new(t) })
  .parse(input)
}

fn base_term<X: Clone>(input: Span<X>) -> Res<Term, X> {
  alt((sort_parser, application, non_app_term)).parse(input)
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
    char_literal,
    hex_literal,
    float_literal,
    num_literal,
    struct_or_update_parser,
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
    (ws0, context("closing bracket for list literal", char(']'))),
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
  let module = (&*input.info.module_context).clone();
  let (input, start) = info(input)?;
  let (input, term) = binop(input)?;
  let (input, end) = info(input)?;
  let loc = SourceRange::new(start.into(), end.into());

  Ok((input, ctx(term, loc, module)))
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
      (
        ws0,
        context("closing brace for attribute named arguments", char('}')),
      ),
    ),
    // Group block: [item1, item2,] — each item parsed with full attr_arg_parser
    delimited(
      (char('['), ws0),
      many1(terminated(preceded(ws0, attr_arg_parser), opt(char(',')))),
      (
        ws0,
        context("closing bracket for attribute group", char(']')),
      ),
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

/// `pub`/`priv` visibility prefix on a declaration. Defaults to
/// `Visibility::PackagePrivate` when omitted. Parsed after attributes,
/// before the declaration keyword: `attributes? visibility? keyword ...`.
/// Does not apply to `use`/`open` — `use` keeps its own binary `pub use`
/// handling (see `use_parser`, which already puts `pub` after attributes);
/// `open` has no visibility at all.
fn vis_parser<X: Clone>(input: Span<X>) -> Res<Visibility, X> {
  map(
    opt(alt((
      map(terminated(tag("pub"), ws1), |_| Visibility::Pub),
      map(terminated(tag("priv"), ws1), |_| Visibility::Priv),
    ))),
    |v| v.unwrap_or_default(),
  )
  .parse(input)
}

/// `#[...]` is the (only) annotation syntax — see `attr_arg_parser` for
/// its content grammar.
fn attribute_parser<X: Clone>(input: Span<X>) -> Res<Attribute, X> {
  let (input, start) = info(input)?;
  let (input, _) = tag("#[")(input)?;
  let (input, _) = ws0(input)?;
  let (input, (name, args_vecs)) = (name, many0(preceded(ws1, attr_arg_parser))).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = context("closing bracket for attribute", tag("]")).parse(input)?;
  let (input, end) = info(input)?;
  Ok((
    input,
    Attribute {
      name,
      args: args_vecs.into_iter().flatten().collect(),
      source_location: SourceRange::new(start.into(), end.into()),
    },
  ))
}

fn opt_attributes<X: Clone>(input: Span<X>) -> Res<Vec<Attribute>, X> {
  // `ws0` before each attribute allows stacking (`#[a]\n#[b]\ndef ...` or
  // `#[a] #[b] def ...`) — the trailing `ws0` before the declaration
  // keyword (already present in each caller) handles the gap after the
  // last attribute.
  many0(preceded(ws0, attribute_parser)).parse(input)
}

fn def_parser(input: Span) -> Res<Def> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = ws0(input)?;
  let (input, vis) = vis_parser(input)?;
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
          AttrArg::Str(s) => Some(Identifier::new(s.clone())),
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

    let mut def = def_with_native(native_name, name.clone(), params.clone(), return_typ, attrs)
      .map_err(|e| {
        nom::Err::Failure(ParseError::new(
          input.clone(),
          error::ParseErrorKind::Native(e),
        ))
      })?;
    def.vis = vis;
    return Ok((input, def));
  } else if input.fragment().starts_with("{") {
    let (input, _) = char('{')(input)?;
    let (input, _) = ws0(input)?;
    let (input, stmts) = do_statements_parser(input)?;
    let (input, _) = ws0(input)?;
    let (input, _) = context("closing brace for function body", char('}')).parse(input)?;
    let body = desugar_do_statements(stmts);
    (input, body)
  } else {
    let (input, _) = assignment_operator(input)?;
    let (input, _) = ws0(input)?;
    let (input, term) = term(input)?;
    (input, term)
  };

  if params.is_empty() {
    let mut typ = return_typ;
    if !implicit_params.is_empty() {
      typ = foralls(implicit_params, typ);
    }
    let mut d = def(name, type_cons, typ, term, attrs);
    d.vis = vis;
    Ok((input, d))
  } else {
    let mut full_typ = return_typ;
    for param in params.iter().rev() {
      full_typ = pi_with_mult((*param.typ).clone(), full_typ, param.mult.clone());
    }
    if !implicit_params.is_empty() {
      full_typ = foralls(implicit_params, full_typ);
    }
    let body = lams(params, term);
    let mut d = def(name, type_cons, full_typ, body, attrs);
    d.vis = vis;
    Ok((input, d))
  }
}

fn macro_param<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  alt((
    // Untyped param: identifier
    map(identifier, |i| vec![param(i, Hole)]),
    // Typed param in parens: (x : Type) — for disambiguation
    delimited(
      (char('('), ws0),
      map(
        pair(
          multiplicity_prefix,
          separated_pair(many1(terminated(identifier, ws0)), ws0, type_annotation),
        ),
        |(mult, (ids, typ))| {
          ids
            .into_iter()
            .map(|i| param_with_mult(i, typ.clone(), mult.clone()))
            .collect()
        },
      ),
      (
        ws0,
        context("closing parenthesis for macro parameter", char(')')),
      ),
    ),
  ))
  .parse(input)
}

fn macro_params<X: Clone>(input: Span<X>) -> Res<Vec<Param>, X> {
  fold_many0(
    terminated(macro_param, ws0),
    Vec::new,
    |mut acc: Vec<_>, mut items: Vec<_>| {
      acc.append(&mut items);
      acc
    },
  )
  .parse(input)
}

fn defs_block_parser(input: Span) -> Res<Vec<Decl>> {
  let (input, _) = tag("decls")(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = char('{')(input)?;
  let (input, _) = ws0(input)?;
  let (decls, remaining) = decls_until_end(input);
  let (remaining, _) = ws0(remaining)?;
  let (remaining, _) = context("closing brace for decls block", char('}')).parse(remaining)?;
  Ok((remaining, decls))
}

/// Parse declarations until the input no longer starts with a valid declaration.
fn decls_until_end(mut input: Span) -> (Vec<Decl>, Span) {
  let mut decls = Vec::new();
  loop {
    let saved = input.clone();
    match decl_parser_no_macro(input) {
      Ok((rest, decl)) => {
        decls.push(decl);
        input = rest;
      }
      Err(_) => return (decls, saved),
    }
  }
}

fn decl_gen_parser(input: Span) -> Res<Decl> {
  let (input, _) = tag("defmacro")(input)?;
  let (input, _) = ws1(input)?;
  let (input, name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = macro_params(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = assignment_operator(input)?;
  let (input, _) = ws0(input)?;
  let (input, decls) = defs_block_parser(input)?;
  Ok((
    input,
    Decl::DeclGen(DeclGenDef {
      name,
      params,
      decls,
      attributes: vec![],
    }),
  ))
}

/// Like `term_inner`, but rejects anything shaped like the head of a
/// *new* macro-call declaration (`identifier!`, no space before `!`) —
/// both the bare-macro-name-reference alternative (`macro_call`, which
/// parses `name!` on its own — with no arguments — as an atomic `Term`)
/// and, via the leading lookahead below, an ordinary `variable`/path
/// parse of the same identifier.
///
/// Used specifically for decl-level macro-call argument parsing
/// (`macro_call_decl_parser`) below: since that parser has no terminator
/// and just keeps consuming `ws1`-separated atoms until one fails to
/// parse, a *following* top-level `other_macro! arg` declaration would
/// otherwise get silently swallowed as extra arguments to THIS call —
/// either as a `macro_call` atom directly, or (once that alternative is
/// removed) as an ordinary `variable` parse of `other_macro` that simply
/// stops right before the `!`, leaving the decl list to choke on a lone
/// `!` where it expects a new declaration. A parenthesized nested call
/// (`outer! (inner! x)`) is unaffected, since `tuple_or_parens` is still
/// in this list and the lookahead only inspects the immediate, unparenthesized
/// input.
fn macro_call_decl_arg<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = peek(not(pair(identifier, char('!')))).parse(input)?;
  alt((
    quote_parser,
    do_parser,
    let_parser,
    if_parser,
    match_parser,
    ann_parser,
    variable,
    literal,
    lambda,
    tuple_or_parens,
  ))
  .parse(input)
}

fn macro_call_decl_parser(input: Span) -> Res<Decl> {
  // Use peek to check that the identifier is followed by `!` before consuming
  let (input, _) = peek(pair(identifier, char('!'))).parse(input)?;
  let (input, name) = identifier(input)?;
  let (input, _) = char('!')(input)?;
  let (input, args) = fold_many0(
    preceded(ws1, macro_call_decl_arg),
    Vec::new,
    |mut acc: Vec<Term>, arg| {
      acc.push(arg);
      acc
    },
  )
  .parse(input)?;
  Ok((input, Decl::MacroCall { name, args }))
}

fn defmacro_parser(input: Span) -> Res<Def> {
  let (input, vis) = vis_parser(input)?;
  let (input, _) = tag("defmacro")(input)?;
  let (input, _) = ws1(input)?;
  let (input, name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = macro_params(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = assignment_operator(input)?;
  let (input, _) = ws0(input)?;
  let (input, term) = term(input)?;
  if params.is_empty() {
    let mut d = def(name, vec![], Hole, term, vec![]);
    d.vis = vis;
    Ok((input, d))
  } else {
    let body = lams(params, term);
    let mut d = def(name, vec![], Hole, body, vec![]);
    d.vis = vis;
    Ok((input, d))
  }
}

fn infix_parser(input: Span) -> Res<Infix> {
  let (input, vis) = vis_parser(input)?;
  let (input, _) = tag("infix")(input)?;
  let (input, _) = ws1(input)?;
  let (input, operator) = operator_parens(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = assignment_operator(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = def_name(input)?;

  let mut i = infix(operator, name);
  i.vis = vis;
  Ok((input, i))
}

fn class_def_parser<X: Clone>(input: Span<X>) -> Res<ClassDef, X> {
  let (input, doc) = opt(doc_comment).parse(input)?;
  let (input, _) = multispace0(input)?;
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = tag("def")(input)?;
  let (input, _) = ws1(input)?;
  let (input, name) = name(input)?;
  let (input, _) = ws0(input)?;
  let (input, constraints) = opt(all_type_cons_parser).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, implicit_params) = implicit_params(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = cons_params(input)?;
  let (input, return_typ) = def_type_annotation(input)?;
  let (input, _) = ws0(input)?;
  let (input, default) = opt(preceded((assignment_operator, ws0), term)).parse(input)?;
  let constraints = constraints.unwrap_or_else(Vec::new);

  let full_return_typ = if implicit_params.is_empty() {
    return_typ
  } else {
    foralls(implicit_params, return_typ)
  };

  if params.is_empty() {
    Ok((
      input,
      class_def(name, full_return_typ, default, constraints, attrs, doc),
    ))
  } else {
    let full_typ = pi_typs(
      params.iter().map(|p| *p.typ.clone()).collect::<Vec<_>>(),
      full_return_typ,
    );
    let default_term = default.map(|d| lams(params, d));
    Ok((
      input,
      class_def(name, full_typ, default_term, constraints, attrs, doc),
    ))
  }
}

fn class_inner_parser(input: Span) -> Res<Vec<ClassDef>> {
  delimited(
    (char('{'), ws0),
    many1(class_def_parser),
    (ws0, context("closing brace for class body", char('}'))),
  )
  .parse(input)
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
    (
      ws0,
      context("closing bracket for type constraints", char(']')),
    ),
  )
  .parse(input)
}

fn class_parser(input: Span) -> Res<Inductive> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = ws0(input)?;
  let (input, vis) = vis_parser(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("class")(input)?;
  let (input, _) = ws0(input)?;
  let (input, constraints) = opt(all_type_cons_parser).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = many1(terminated(lam_param, ws0)).parse(input)?;
  let (input, defs) = class_inner_parser(input)?;

  let mut ind = class(
    name,
    constraints.unwrap_or_else(Vec::new),
    params,
    defs,
    attrs,
  );
  ind.vis = vis;
  Ok((input, ind))
}

fn instance_inner_parser(input: Span) -> Res<Vec<Def>> {
  delimited(
    (char('{'), ws0),
    many1(delimited(ws0, def_parser, ws0)),
    (ws0, context("closing brace for instance body", char('}'))),
  )
  .parse(input)
}

fn instance_parser(input: Span) -> Res<Instance> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = ws0(input)?;
  let (input, vis) = vis_parser(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("instance")(input)?;
  let (input, _) = ws0(input)?;
  let (input, implicit_params) = implicit_params(input)?;
  let (input, _) = ws0(input)?;
  let (input, constraints) = opt(all_type_cons_parser).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = opt(terminated(def_name, (ws0, char(':')))).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, class_name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, args) = many0(terminated(term_inner, ws0)).parse(input)?;
  let (input, defs) = instance_inner_parser(input)?;

  let mut inst = instance(
    name,
    class_name,
    constraints.unwrap_or_else(Vec::new),
    implicit_params,
    args,
    defs,
    attrs,
  );
  inst.vis = vis;
  Ok((input, inst))
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
    (
      ws0,
      context("closing brace for type constructors", char('}')),
    ),
  )
  .parse(input)
}

pub(crate) fn inductive_parser(input: Span) -> Res<Inductive> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = ws0(input)?;
  let (input, vis) = vis_parser(input)?;
  let (input, _) = ws0(input)?;
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

  let mut ind = inductive(
    name,
    constraints.unwrap_or_else(Vec::new),
    params,
    typ,
    constructors,
    attrs,
  );
  ind.vis = vis;
  Ok((input, ind))
}

fn struct_field_parser<X: Clone>(input: Span<X>) -> Res<StructField, X> {
  let (input, mult) = multiplicity_prefix(input)?;
  let (input, name) = identifier(input)?;
  let (input, _) = ws0(input)?;
  let (input, typ) = def_type_annotation(input)?;
  let (input, _) = ws0(input)?;
  let (input, default) = opt(preceded((assignment_operator, ws0), term)).parse(input)?;

  Ok((input, stru_field_with_mult(name, typ, default, mult)))
}

fn struct_inner_parser<X: Clone>(input: Span<X>) -> Res<Vec<StructField>, X> {
  delimited(
    (char('{'), ws0),
    many1(terminated(struct_field_parser, (ws0, opt(char(',')), ws0))),
    (ws0, context("closing brace for struct fields", char('}'))),
  )
  .parse(input)
}

fn struct_parser<X: Clone>(input: Span<X>) -> Res<Inductive, X> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = ws0(input)?;
  let (input, vis) = vis_parser(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("struct")(input)?;
  let (input, _) = ws0(input)?;
  let (input, constraints) =
    map(opt(all_type_cons_parser), |t| t.unwrap_or_default()).parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, name) = def_name(input)?;
  let (input, _) = ws0(input)?;
  let (input, params) = cons_params(input)?;
  let (input, fields) = struct_inner_parser(input)?;

  let mut ind = stru(name, constraints, params, fields, attrs);
  ind.vis = vis;
  Ok((input, ind))
}

fn struct_val_field_parser<X: Clone>(input: Span<X>) -> Res<(Identifier, Term), X> {
  let (input, name) = identifier(input)?;
  let (input, _) = ws0(input)?;
  let (input, value) = preceded((assignment_operator, ws0), term).parse(input)?;

  Ok((input, (name, value)))
}

fn parse_struct_update<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, id) = identifier(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = tag("with")(input)?;
  let (input, _) = ws0(input)?;
  let (input, fields) = many0(terminated(
    struct_val_field_parser,
    (ws0, opt(char(',')), ws0),
  ))
  .parse(input)?;
  let (input, _) = ws0(input)?;
  let (input, _) = context("closing brace for struct update", char('}')).parse(input)?;
  Ok((
    input,
    Term::Lit {
      value: Literal::StructUpdate {
        base: id,
        fields: fields.into_iter().collect(),
      },
    },
  ))
}

fn struct_or_update_parser<X: Clone>(input: Span<X>) -> Res<Term, X> {
  let (input, _) = char('{')(input)?;
  let (input, _) = ws0(input)?;
  alt((
    parse_struct_update,
    map(
      (
        many0(terminated(
          struct_val_field_parser,
          (ws0, opt(char(',')), ws0),
        )),
        opt(terminated(preceded((char(':'), ws0), type_expression), ws0)),
        context("closing brace for struct literal", char('}')),
      ),
      |(fields, type_name, _)| Term::Lit {
        value: Literal::StructLit {
          fields: fields.into_iter().collect(),
          type_name: type_name.map(Box::new),
        },
      },
    ),
  ))
  .parse(input)
}

/// A single item inside a `use Module { ... }` brace filter, e.g. `name`,
/// `name as alias`, `*`, or a nested `name { items }` sub-module import.
/// Tried in this order: `*` first (unambiguous), then sub-module-with-rename
/// before sub-module before rename before plain name, since each is a
/// strict prefix of the previous.
fn use_brace_item(input: Span) -> Res<UseItem> {
  alt((
    map(char('*'), |_| UseItem::Glob),
    map(
      (
        identifier,
        preceded((ws1, tag("as"), ws1), identifier),
        preceded(ws0, use_brace_items),
      ),
      |(name, alias, items)| UseItem::SubModuleRename { name, alias, items },
    ),
    map(
      (identifier, preceded(ws0, use_brace_items)),
      |(name, items)| UseItem::SubModule { name, items },
    ),
    map(
      (identifier, preceded((ws1, tag("as"), ws1), identifier)),
      |(name, alias)| UseItem::Rename(name, alias),
    ),
    map(identifier, UseItem::Name),
  ))
  .parse(input)
}

fn use_brace_items(input: Span) -> Res<Vec<UseItem>> {
  delimited(
    (char('{'), ws0),
    many0(terminated(use_brace_item, (ws0, opt(char(',')), ws0))),
    context("closing brace for use filter", char('}')),
  )
  .parse(input)
}

fn use_brace_filter(input: Span) -> Res<UseFilter> {
  map(use_brace_items, UseFilter::Items).parse(input)
}

/// Optional `{ items }` filter after a `use Module`. Absent braces yield
/// `UseFilter::Bare` (deprecated bare use — see `bare_use_warnings`).
fn use_opt_filter(input: Span) -> Res<UseFilter> {
  let (after_ws, _) = ws0(input.clone())?;
  if let Ok((input, filter)) = use_brace_filter.parse(after_ws) {
    return Ok((input, filter));
  }
  // No brace filter found — return the ORIGINAL (pre-`ws0`) position, not
  // the whitespace-advanced one, so `Use.source_location.end` (computed by
  // the caller right after this) stops precisely after the module path
  // instead of swallowing trailing blank lines/comments looking for a `{`
  // that isn't there. The next declaration's own leading-whitespace-skip
  // (`decls_space_parser`) still consumes that gap, same as for every
  // other declaration kind — nothing is left unparsed.
  Ok((input, UseFilter::Bare))
}

fn use_parser(input: Span) -> Res<Use> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = ws0(input)?;
  let (input, start) = info(input)?;
  let (input, public) = opt(terminated(tag("pub"), ws1)).parse(input)?;
  let public = public.is_some();
  let (input, _) = tag("use")(input)?;
  let (input, _) = ws1(input)?;
  let (input, module_path) =
    alt((path_expression, map(identifier, ModulePath::single))).parse(input)?;
  let (input, filter) = use_opt_filter(input)?;
  let (input, end) = info(input)?;
  let source_location = SourceRange::new(start.into(), end.into());
  Ok((
    input,
    Use {
      module_path,
      source_location,
      filter,
      public,
      attributes: attrs,
    },
  ))
}

/// Shared by plain `open` and scoped `open ... in decl`: the module path
/// plus an optional `{ names }`/`{*}` filter (braces are optional for
/// `open`, unlike the now-mandatory braces on `use`; a bare `open Module`
/// still parses but is deprecated — see `bare_open_warnings` — in favor of
/// the explicit `open Module {*}`).
fn open_module_path_and_filter(input: Span) -> Res<(ModulePath, OpenFilter)> {
  let (input, module_path) =
    alt((path_expression, map(identifier, ModulePath::single))).parse(input)?;
  let (input, filter) = opt(preceded(
    ws0,
    delimited(
      (char('{'), ws0),
      alt((
        map(terminated(char('*'), ws0), |_| OpenFilter::Glob),
        map(
          many0(terminated(identifier, (ws0, opt(char(',')), ws0))),
          OpenFilter::Only,
        ),
      )),
      context("closing brace for open filter", char('}')),
    ),
  ))
  .parse(input)?;
  let filter = filter.unwrap_or(OpenFilter::All);
  Ok((input, (module_path, filter)))
}

/// The declaration kinds a scoped `open Module in <decl>` may wrap.
fn scoped_open_inner_decl(input: Span) -> Res<Decl> {
  alt((
    map(def_parser, Decl::Def),
    map(class_parser, Decl::Type),
    map(instance_parser, Decl::Ins),
    map(struct_parser, Decl::Type),
    map(inductive_parser, Decl::Type),
  ))
  .parse(input)
}

/// Parses both plain `open Module [{names}]` and scoped
/// `open Module [{names}] in <decl>`, since they share the `open` prefix
/// and module-path/filter parsing.
fn open_parser(input: Span) -> Res<Decl> {
  let (input, attrs) = opt_attributes(input)?;
  let (input, _) = ws0(input)?;
  let (input, start) = info(input)?;
  let (input, _) = tag("open")(input)?;
  let (input, _) = ws1(input)?;
  let (input, (module_path, filter)) = open_module_path_and_filter(input)?;
  let (input, scoped) =
    opt(preceded((ws1, tag("in"), ws1), scoped_open_inner_decl)).parse(input)?;
  let (input, end) = info(input)?;
  let source_location = SourceRange::new(start.into(), end.into());

  match scoped {
    Some(decl) => Ok((
      input,
      Decl::ScopedOpen {
        module_path,
        filter,
        attributes: attrs,
        decl: Box::new(decl),
      },
    )),
    None => Ok((
      input,
      Decl::Open(Open {
        module_path,
        source_location,
        filter,
        attributes: attrs,
      }),
    )),
  }
}
/// Same declaration grammar `decl_parser` uses, minus its own leading
/// doc-comment/location bookkeeping — used for `decls { ... }` decl-gen
/// macro template bodies (`defs_block_parser`). Despite the name (kept for
/// historical reasons — it originally excluded decl-level macro calls
/// entirely), it now DOES include `macro_call_decl_parser`: templates need
/// to be able to call other decl-gen macros, including the built-in
/// reflection intrinsic (`reflect_type_info!`) that drives the `derive_*!`
/// macros in `std/derive.mo` — `defmacro derive_lens (T : Type) := decls {
/// reflect_type_info! T derive_lens_meta }` needs
/// `reflect_type_info! T derive_lens_meta` to parse as an ordinary nested
/// `Decl::MacroCall` here.
fn decl_parser_no_macro(input: Span) -> Res<Decl> {
  let (input, decl) = alt((
    map(use_parser, Decl::Use),
    open_parser,
    decl_gen_parser,
    map(defmacro_parser, Decl::DefMacro),
    map(def_parser, Decl::Def),
    map(class_parser, Decl::Type),
    map(instance_parser, Decl::Ins),
    map(struct_parser, Decl::Type),
    map(inductive_parser, Decl::Type),
    map(infix_parser, Decl::Infix),
    macro_call_decl_parser,
  ))
  .parse(input)?;
  Ok((input, decl))
}

fn decl_parser(input: Span) -> Res<SourceContext<Decl>> {
  let (input, opt_doc) = decls_space_parser(input)?;
  let (input, _) = ws0(input)?;
  let (input, start) = info(input)?;
  let (input, decl) = alt((
    map(use_parser, Decl::Use),
    open_parser,
    decl_gen_parser,
    map(defmacro_parser, Decl::DefMacro),
    map(def_parser, Decl::Def),
    map(class_parser, Decl::Type),
    map(instance_parser, Decl::Ins),
    map(struct_parser, Decl::Type),
    map(inductive_parser, Decl::Type),
    map(infix_parser, Decl::Infix),
    macro_call_decl_parser,
  ))
  .parse(input)?;
  let (input, end) = info(input)?;
  let loc = SourceRange::new(start.into(), end.into());
  Ok((input, SourceContext::new(loc, decl, opt_doc)))
}

/// Consumes whitespace and doc comments (///) but NOT regular // comments
/// This is used between declarations to preserve docstrings
fn decls_space_parser<X: Clone>(input: Span<X>) -> Res<Option<Documentation>, X> {
  let (input, leading) =
    many0(alt((multispace1, line_comment_not_doc, block_comment))).parse(input)?;
  let (input, doc) = opt(doc_comment).parse(input)?;
  let (input, _) = many0(alt((multispace1, line_comment_not_doc, block_comment))).parse(input)?;
  let _ = leading;
  Ok((input, doc))
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

fn decls_parser(input: Span) -> Res<ParsedModule> {
  let (input, module_doc) = opt(doc_comment).parse(input)?;
  let (input, mut decls) = many0(decl_parser).parse(input)?;
  let (input, _) = ws0(input)?;
  // many0 discards the inner error from the last failed decl_parser.
  // If there's remaining input, re-run decl_parser to capture its error
  // (which includes context from inner delimiter parsers) for display.
  if !input.fragment().is_empty() {
    return match decl_parser(input) {
      Err(e) => Err(e),
      Ok((rest, decl)) => {
        decls.push(decl);
        let (rest, _) = ws0(rest)?;
        let (rest, _) = eof(rest)?;
        Ok((rest, ParsedModule { decls, module_doc }))
      }
    };
  }
  let (input, _) = eof(input)?;
  Ok((input, ParsedModule { decls, module_doc }))
}

pub fn parse_file(input: &str) -> Result<ParsedModule, ParseFileError> {
  parse_file_with_path(input, &Default::default())
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleContext {
  pub path: ModulePath,
  pub file: Option<std::path::PathBuf>,
}

impl ModuleContext {
  pub fn new(path: ModulePath, file: Option<std::path::PathBuf>) -> Self {
    Self { path, file }
  }
}

pub fn parse_file_with_path(
  input: &str,
  context: &ModuleContext,
) -> Result<ParsedModule, ParseFileError> {
  let span = Span::new(input, context.clone());
  match decls_parser(span).finish() {
    Ok((_, decls)) => Ok(decls),
    Err(e) => {
      let err: OwnedError = e.into();
      Err(ParseFileError {
        source: input.to_string(),
        error: err,
        context: context.clone(),
      })
    }
  }
}
