use std::fmt::Display;

use crate::{
  Map,
  term::{
    F64Wrap, Identifier, Literal, Native, NumSuffix, Term, app, b_false, b_true, id, io_term,
    module::Scope, num_suffix, unit,
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

pub type NativeFun = fn(Vec<Term>) -> Result<Term, NativeError>;

pub fn load_native_funs() -> Map<Identifier, NativeFun> {
  let v: Vec<(Identifier, NativeFun)> = vec![
    (id("println"), println),
    (id("i8_add"), i8_add),
    (id("i8_sub"), i8_sub),
    (id("i8_mul"), i8_mul),
    (id("i8_div"), i8_div),
    (id("i8_eq"), i8_eq),
    (id("i8_to_string"), i8_to_string),
    (id("i16_add"), i16_add),
    (id("i16_sub"), i16_sub),
    (id("i16_mul"), i16_mul),
    (id("i16_div"), i16_div),
    (id("i16_eq"), i16_eq),
    (id("i16_to_string"), i16_to_string),
    (id("i32_add"), i32_add),
    (id("i32_sub"), i32_sub),
    (id("i32_mul"), i32_mul),
    (id("i32_div"), i32_div),
    (id("i32_eq"), i32_eq),
    (id("i32_to_string"), i32_to_string),
    (id("i64_add"), i64_add),
    (id("i64_sub"), i64_sub),
    (id("i64_mul"), i64_mul),
    (id("i64_div"), i64_div),
    (id("i64_eq"), i64_eq),
    (id("i64_to_string"), i64_to_string),
    (id("u8_add"), u8_add),
    (id("u8_sub"), u8_sub),
    (id("u8_mul"), u8_mul),
    (id("u8_div"), u8_div),
    (id("u8_eq"), u8_eq),
    (id("u8_to_string"), u8_to_string),
    (id("u16_add"), u16_add),
    (id("u16_sub"), u16_sub),
    (id("u16_mul"), u16_mul),
    (id("u16_div"), u16_div),
    (id("u16_eq"), u16_eq),
    (id("u16_to_string"), u16_to_string),
    (id("u32_add"), u32_add),
    (id("u32_sub"), u32_sub),
    (id("u32_mul"), u32_mul),
    (id("u32_div"), u32_div),
    (id("u32_eq"), u32_eq),
    (id("u32_to_string"), u32_to_string),
    (id("u64_add"), u64_add),
    (id("u64_sub"), u64_sub),
    (id("u64_mul"), u64_mul),
    (id("u64_div"), u64_div),
    (id("u64_eq"), u64_eq),
    (id("u64_to_string"), u64_to_string),
    (id("f32_add"), f32_add),
    (id("f32_sub"), f32_sub),
    (id("f32_mul"), f32_mul),
    (id("f32_div"), f32_div),
    (id("f32_eq"), f32_eq),
    (id("f32_to_string"), f32_to_string),
    (id("f64_add"), f64_add),
    (id("f64_sub"), f64_sub),
    (id("f64_mul"), f64_mul),
    (id("f64_div"), f64_div),
    (id("f64_eq"), f64_eq),
    (id("f64_to_string"), f64_to_string),
    (id("string_eq"), string_eq),
    (id("string_concat"), string_concat),
    (id("string_length"), string_length),
    (id("string_get"), string_get),
  ];
  v.into_iter().collect()
}

pub fn native_execute(native: Native, scope: &Scope) -> Result<Term, NativeError> {
  let native_fun = scope
    .global()
    .get_native(&native.native_name)
    .ok_or_else(|| NativeError::NotFound(native.native_name.clone()))?;
  let args: Vec<Term> = native.args.into_iter().flatten().collect();
  if args.len() == native.num_args {
    (native_fun)(args)
  } else {
    Err(NativeError::MissingArgs {
      expected: native.num_args,
      actual: args.len(),
    })
  }
}
