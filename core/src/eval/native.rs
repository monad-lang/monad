use std::fmt::Display;

use crate::{
  Map,
  eval::EvalOptions,
  term::{
    Constructor, F64Wrap, Identifier, Literal, Native, NumSuffix, Term, app, apps, b_false, b_true,
    id, io_term, module::Scope, num_suffix, pvar, to_list_term, unit,
  },
};

#[derive(Debug, Clone, PartialEq)]
pub enum NativeError {
  MissingArgs { expected: usize, actual: usize },
  ExpectedString { actual: Term },
  ExpectedNum { actual: Term },
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
      ExpectedString { actual } => write!(f, "expected String found {actual}"),
      ExpectedNum { actual } => write!(f, "expected number found {actual}"),
    }
  }
}

fn extract_string_at(terms: &[Term], index: usize) -> Result<String, NativeError> {
  if terms.len() > index {
    if let Term::Lit {
      value: Literal::Str { value: s },
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

fn extract_num_at(terms: &[Term], index: usize) -> Result<i64, NativeError> {
  if terms.len() > index {
    if let Term::Lit {
      value: Literal::Num { value: s, .. },
    } = &terms[index]
    {
      Ok(*s)
    } else {
      Err(ExpectedNum {
        actual: terms[index].clone(),
      })
    }
  } else {
    Err(MissingArgs {
      expected: index + 1,
      actual: terms.len(),
    })
  }
}

fn extract_float_at(terms: &[Term], index: usize) -> Result<f64, NativeError> {
  if terms.len() > index {
    if let Term::Lit {
      value: Literal::Float { value: s, .. },
    } = &terms[index]
    {
      Ok(s.0)
    } else {
      Err(ExpectedNum {
        actual: terms[index].clone(),
      })
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

fn bool_to_term(b: bool) -> Term {
  if b { b_true() } else { b_false() }
}

fn extract_num_pair(terms: &[Term]) -> Result<(i64, i64), NativeError> {
  if terms.len() >= 2 {
    if let Term::Lit {
      value: Literal::Num { value: a, .. },
    } = &terms[0]
      && let Term::Lit {
        value: Literal::Num { value: b, .. },
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

fn extract_float_pair(terms: &[Term]) -> Result<(f64, f64), NativeError> {
  if terms.len() >= 2 {
    if let Term::Lit {
      value: Literal::Float { value: a, .. },
    } = &terms[0]
      && let Term::Lit {
        value: Literal::Float { value: b, .. },
      } = &terms[1]
    {
      Ok((a.0, b.0))
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

macro_rules! int_ops {
  ($suffix:ident, $ty:ident) => {
    paste::paste! {
      pub fn [<$suffix:lower _add>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_num_pair(&terms)?;
        let v = (a as $ty).wrapping_add(b as $ty) as i64;
        Ok(num_suffix(v, NumSuffix::$suffix))
      }
      pub fn [<$suffix:lower _sub>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_num_pair(&terms)?;
        let v = (a as $ty).wrapping_sub(b as $ty) as i64;
        Ok(num_suffix(v, NumSuffix::$suffix))
      }
      pub fn [<$suffix:lower _mul>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_num_pair(&terms)?;
        let v = (a as $ty).wrapping_mul(b as $ty) as i64;
        Ok(num_suffix(v, NumSuffix::$suffix))
      }
      pub fn [<$suffix:lower _div>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_num_pair(&terms)?;
        let b = b as $ty;
        if b == 0 {
          return Err(Custom("division by zero".into()));
        }
        let v = (a as $ty).wrapping_div(b) as i64;
        Ok(num_suffix(v, NumSuffix::$suffix))
      }
      pub fn [<$suffix:lower _eq>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_num_pair(&terms)?;
        Ok(bool_to_term((a as $ty) == (b as $ty)))
      }
      pub fn [<$suffix:lower _to_string>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let n = extract_num_at(&terms, 0)?;
        Ok(Term::Lit {
          value: Literal::Str {
            value: n.to_string(),
          },
        })
      }
    }
  };
}

macro_rules! float_ops {
  ($suffix:ident) => {
    paste::paste! {
      pub fn [<$suffix:lower _add>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_float_pair(&terms)?;
        Ok(Term::Lit {
          value: Literal::Float {
            value: F64Wrap(a + b),
            suffix: NumSuffix::$suffix,
          },
        })
      }
      pub fn [<$suffix:lower _sub>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_float_pair(&terms)?;
        Ok(Term::Lit {
          value: Literal::Float {
            value: F64Wrap(a - b),
            suffix: NumSuffix::$suffix,
          },
        })
      }
      pub fn [<$suffix:lower _mul>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_float_pair(&terms)?;
        Ok(Term::Lit {
          value: Literal::Float {
            value: F64Wrap(a * b),
            suffix: NumSuffix::$suffix,
          },
        })
      }
      pub fn [<$suffix:lower _div>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_float_pair(&terms)?;
        Ok(Term::Lit {
          value: Literal::Float {
            value: F64Wrap(a / b),
            suffix: NumSuffix::$suffix,
          },
        })
      }
      pub fn [<$suffix:lower _eq>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let (a, b) = extract_float_pair(&terms)?;
        Ok(bool_to_term(a == b))
      }
      pub fn [<$suffix:lower _to_string>](terms: Vec<Term>) -> Result<Term, NativeError> {
        let n = extract_float_at(&terms, 0)?;
        Ok(Term::Lit {
          value: Literal::Str {
            value: n.to_string(),
          },
        })
      }
    }
  };
}

int_ops!(I8, i8);
int_ops!(I16, i16);
int_ops!(I32, i32);
int_ops!(I64, i64);
int_ops!(U8, u8);
int_ops!(U16, u16);
int_ops!(U32, u32);
int_ops!(U64, u64);

float_ops!(F32);
float_ops!(F64);

pub fn string_eq(terms: Vec<Term>) -> Result<Term, NativeError> {
  let a = extract_string_at(&terms, 0)?;
  let b = extract_string_at(&terms, 1)?;
  Ok(bool_to_term(a == b))
}

pub fn string_concat(terms: Vec<Term>) -> Result<Term, NativeError> {
  let a = extract_string_at(&terms, 0)?;
  let b = extract_string_at(&terms, 1)?;
  Ok(Term::Lit {
    value: Literal::Str {
      value: format!("{}{}", a, b),
    },
  })
}

pub fn string_length(terms: Vec<Term>) -> Result<Term, NativeError> {
  let s = extract_string_at(&terms, 0)?;
  Ok(num_suffix(s.len() as i64, NumSuffix::I64))
}

pub fn string_slice(terms: Vec<Term>) -> Result<Term, NativeError> {
  let s = extract_string_at(&terms, 0)?;
  let start = extract_num_at(&terms, 1)?;
  let len = extract_num_at(&terms, 2)?;
  let start = start.max(0) as usize;
  let len = len.max(0) as usize;
  let end = (start + len).min(s.len());
  if start <= s.len() {
    Ok(Term::Lit {
      value: Literal::Str {
        value: s[start..end].to_string(),
      },
    })
  } else {
    Ok(Term::Lit {
      value: Literal::Str {
        value: String::new(),
      },
    })
  }
}

pub fn string_drop(terms: Vec<Term>) -> Result<Term, NativeError> {
  let n = extract_num_at(&terms, 0)?;
  let s = extract_string_at(&terms, 1)?;
  let n = n.max(0) as usize;
  if n >= s.len() {
    Ok(Term::Lit {
      value: Literal::Str {
        value: String::new(),
      },
    })
  } else {
    Ok(Term::Lit {
      value: Literal::Str {
        value: s[n..].to_string(),
      },
    })
  }
}

pub fn string_starts_with(terms: Vec<Term>) -> Result<Term, NativeError> {
  let prefix = extract_string_at(&terms, 0)?;
  let s = extract_string_at(&terms, 1)?;
  Ok(bool_to_term(s.starts_with(&prefix)))
}

pub fn string_get(terms: Vec<Term>) -> Result<Term, NativeError> {
  let s = extract_string_at(&terms, 0)?;
  let i = extract_num_at(&terms, 1)?;
  if i >= 0 && (i as usize) < s.len() {
    let byte = s.as_bytes()[i as usize];
    let some_term = Term::Var {
      name: crate::term::NameRef::Id(id("some")),
    };
    let none_term = Term::Var {
      name: crate::term::NameRef::Id(id("none")),
    };
    Ok(app(
      app(some_term, num_suffix(byte as i64, NumSuffix::U8)),
      none_term,
    ))
  } else {
    Ok(Term::Var {
      name: crate::term::NameRef::Id(id("none")),
    })
  }
}

pub fn string_to_list(terms: Vec<Term>) -> Result<Term, NativeError> {
  let s = extract_string_at(&terms, 0)?;
  let bytes: Vec<Term> = s
    .bytes()
    .map(|b| num_suffix(b as i64, NumSuffix::U8))
    .collect();
  Ok(to_list_term(bytes))
}

fn collect_bytes_from_list(term: &Term) -> Result<Vec<u8>, NativeError> {
  match term {
    Term::Con(Constructor { name, .. }) if name == &id("empty") => Ok(vec![]),
    Term::Con(Constructor { name, args, .. }) if name == &id("cons") => {
      let mut bytes = vec![];
      if let Some(Some(head)) = args.first() {
        let b = extract_u8_from_term(head)?;
        bytes.push(b);
      } else {
        return Err(Custom("List.cons missing head argument".into()));
      }
      if let Some(Some(tail)) = args.get(1) {
        bytes.extend(collect_bytes_from_list(tail)?);
      }
      Ok(bytes)
    }
    other => Err(Custom(format!("expected List U8, got {other}"))),
  }
}

fn extract_u8_from_term(term: &Term) -> Result<u8, NativeError> {
  match term {
    Term::Lit {
      value: Literal::Num {
        value,
        suffix: NumSuffix::U8,
      },
    } => Ok(*value as u8),
    other => Err(ExpectedNum {
      actual: other.clone(),
    }),
  }
}

pub fn string_from_list(terms: Vec<Term>) -> Result<Term, NativeError> {
  let list = &terms[0];
  let bytes = collect_bytes_from_list(list)?;
  let s = String::from_utf8(bytes).map_err(|e| Custom(format!("invalid UTF-8: {e}")))?;
  Ok(Term::Lit {
    value: Literal::Str { value: s },
  })
}

pub fn bench_report(terms: Vec<Term>) -> Result<Term, NativeError> {
  let label = extract_string_at(&terms, 0)?;
  let elapsed = extract_num_at(&terms, 1)?;
  println!("  BENCH {label}: {elapsed}ms");
  Ok(b_true())
}

pub fn bench_now(_terms: Vec<Term>) -> Result<Term, NativeError> {
  let now = std::time::SystemTime::now()
    .duration_since(std::time::UNIX_EPOCH)
    .unwrap_or_default()
    .as_millis() as i64;
  Ok(num_suffix(now, NumSuffix::I64))
}

pub fn u8_lt(terms: Vec<Term>) -> Result<Term, NativeError> {
  let (a, b) = extract_num_pair(&terms)?;
  Ok(bool_to_term((a as u8) < (b as u8)))
}

pub fn u8_gt(terms: Vec<Term>) -> Result<Term, NativeError> {
  let (a, b) = extract_num_pair(&terms)?;
  Ok(bool_to_term((a as u8) > (b as u8)))
}

/// Simple native function: takes args, returns result.
pub type SimpleNativeFun = fn(Vec<Term>) -> Result<Term, NativeError>;
/// Scope-aware native function: takes args and the current scope.
pub type ScopeNativeFun = fn(Vec<Term>, &Scope) -> Result<Term, NativeError>;

#[derive(Clone)]
pub enum NativeFun {
  Simple(SimpleNativeFun),
  ScopeAware(ScopeNativeFun),
}

impl std::fmt::Debug for NativeFun {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      NativeFun::Simple(_) => write!(f, "NativeFun::Simple(...)"),
      NativeFun::ScopeAware(_) => write!(f, "NativeFun::ScopeAware(...)"),
    }
  }
}

/// J eliminator for Eq. Args: A, a, P, h, b, e
/// If e is Eq.refl a, return h (since b = a and e = refl a).
/// Otherwise, the term is stuck (can't reduce further).
pub fn eq_rec(args: Vec<Term>) -> Result<Term, NativeError> {
  if args.len() < 6 {
    return Err(NativeError::MissingArgs {
      expected: 6,
      actual: args.len(),
    });
  }
  if let Term::Con(Constructor { name, .. }) = &args[5] {
    if name.as_str() == "refl" {
      return Ok(args[3].clone());
    }
  }
  Ok(apps(pvar(vec!["Eq", "rec"]), args))
}

pub fn load_native_funs() -> Map<Identifier, NativeFun> {
  /// Helper to wrap a simple native function into NativeFun::Simple
  fn s(f: SimpleNativeFun) -> NativeFun {
    NativeFun::Simple(f)
  }
  /// Helper to wrap a scope-aware native function into NativeFun::ScopeAware
  fn sa(f: ScopeNativeFun) -> NativeFun {
    NativeFun::ScopeAware(f)
  }

  let v: Vec<(Identifier, NativeFun)> = vec![
    (id("print_str"), s(println)),
    (id("i8_add"), s(i8_add)),
    (id("i8_sub"), s(i8_sub)),
    (id("i8_mul"), s(i8_mul)),
    (id("i8_div"), s(i8_div)),
    (id("i8_eq"), s(i8_eq)),
    (id("i8_to_string"), s(i8_to_string)),
    (id("i16_add"), s(i16_add)),
    (id("i16_sub"), s(i16_sub)),
    (id("i16_mul"), s(i16_mul)),
    (id("i16_div"), s(i16_div)),
    (id("i16_eq"), s(i16_eq)),
    (id("i16_to_string"), s(i16_to_string)),
    (id("i32_add"), s(i32_add)),
    (id("i32_sub"), s(i32_sub)),
    (id("i32_mul"), s(i32_mul)),
    (id("i32_div"), s(i32_div)),
    (id("i32_eq"), s(i32_eq)),
    (id("i32_to_string"), s(i32_to_string)),
    (id("i64_add"), s(i64_add)),
    (id("i64_sub"), s(i64_sub)),
    (id("i64_mul"), s(i64_mul)),
    (id("i64_div"), s(i64_div)),
    (id("i64_eq"), s(i64_eq)),
    (id("i64_to_string"), s(i64_to_string)),
    (id("u8_add"), s(u8_add)),
    (id("u8_sub"), s(u8_sub)),
    (id("u8_mul"), s(u8_mul)),
    (id("u8_div"), s(u8_div)),
    (id("u8_eq"), s(u8_eq)),
    (id("u8_to_string"), s(u8_to_string)),
    (id("u16_add"), s(u16_add)),
    (id("u16_sub"), s(u16_sub)),
    (id("u16_mul"), s(u16_mul)),
    (id("u16_div"), s(u16_div)),
    (id("u16_eq"), s(u16_eq)),
    (id("u16_to_string"), s(u16_to_string)),
    (id("u32_add"), s(u32_add)),
    (id("u32_sub"), s(u32_sub)),
    (id("u32_mul"), s(u32_mul)),
    (id("u32_div"), s(u32_div)),
    (id("u32_eq"), s(u32_eq)),
    (id("u32_to_string"), s(u32_to_string)),
    (id("u64_add"), s(u64_add)),
    (id("u64_sub"), s(u64_sub)),
    (id("u64_mul"), s(u64_mul)),
    (id("u64_div"), s(u64_div)),
    (id("u64_eq"), s(u64_eq)),
    (id("u64_to_string"), s(u64_to_string)),
    (id("f32_add"), s(f32_add)),
    (id("f32_sub"), s(f32_sub)),
    (id("f32_mul"), s(f32_mul)),
    (id("f32_div"), s(f32_div)),
    (id("f32_eq"), s(f32_eq)),
    (id("f32_to_string"), s(f32_to_string)),
    (id("f64_add"), s(f64_add)),
    (id("f64_sub"), s(f64_sub)),
    (id("f64_mul"), s(f64_mul)),
    (id("f64_div"), s(f64_div)),
    (id("f64_eq"), s(f64_eq)),
    (id("f64_to_string"), s(f64_to_string)),
    (id("string_eq"), s(string_eq)),
    (id("string_concat"), s(string_concat)),
    (id("string_length"), s(string_length)),
    (id("string_slice"), s(string_slice)),
    (id("string_drop"), s(string_drop)),
    (id("string_starts_with"), s(string_starts_with)),
    (id("string_get"), s(string_get)),
    (id("string_to_list"), s(string_to_list)),
    (id("string_from_list"), s(string_from_list)),
    (id("bench_now"), s(bench_now)),
    (id("bench_report"), s(bench_report)),
    (id("u8_lt"), s(u8_lt)),
    (id("u8_gt"), s(u8_gt)),
    (id("eval_term"), sa(eval_term)),
    (id("eq_rec"), s(eq_rec)),
  ];
  v.into_iter().collect()
}

/// Evaluate a quoted term at runtime. Extracts the inner Term from
/// `Lit::Term` and evaluates it using the current scope.
pub fn eval_term(terms: Vec<Term>, scope: &Scope) -> Result<Term, NativeError> {
  let term = terms.into_iter().next().ok_or(NativeError::MissingArgs {
    expected: 1,
    actual: 0,
  })?;
  match term {
    Term::Lit {
      value: Literal::Term(inner),
    } => crate::eval::eval(*inner, scope, &EvalOptions::default())
      .map_err(|e| NativeError::Custom(e.to_string())),
    other => Ok(other),
  }
}

pub fn native_execute(native: Native, scope: &Scope) -> Result<Term, NativeError> {
  let native_fun = scope
    .global()
    .get_native(&native.native_name)
    .ok_or_else(|| NativeError::NotFound(native.native_name.clone()))?;
  let args: Vec<Term> = native.args.into_iter().flatten().collect();
  if args.len() == native.num_args {
    match native_fun {
      NativeFun::Simple(f) => f(args),
      NativeFun::ScopeAware(f) => f(args, scope),
    }
  } else {
    Err(NativeError::MissingArgs {
      expected: native.num_args,
      actual: args.len(),
    })
  }
}
