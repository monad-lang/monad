use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LLVMType {
  Void,
  I1,
  I8,
  I32,
  I64,
  Pointer(Box<LLVMType>),
  Function {
    params: Vec<LLVMType>,
    return_type: Box<LLVMType>,
  },
  Struct {
    name: String,
  },
}

impl LLVMType {
  pub fn i8_ptr() -> Self {
    LLVMType::Pointer(Box::new(LLVMType::I8))
  }

  pub fn void_ptr() -> Self {
    LLVMType::Pointer(Box::new(LLVMType::Void))
  }

  pub fn is_void(&self) -> bool {
    matches!(self, LLVMType::Void)
  }
}

impl fmt::Display for LLVMType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      LLVMType::Void => write!(f, "void"),
      LLVMType::I1 => write!(f, "i1"),
      LLVMType::I8 => write!(f, "i8"),
      LLVMType::I32 => write!(f, "i32"),
      LLVMType::I64 => write!(f, "i64"),
      LLVMType::Pointer(inner) => write!(f, "{}*", inner),
      LLVMType::Function {
        params,
        return_type,
      } => {
        write!(f, "{} (", return_type)?;
        for (i, p) in params.iter().enumerate() {
          if i > 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", p)?;
        }
        write!(f, ")")
      }
      LLVMType::Struct { name } => write!(f, "%{}", name),
    }
  }
}

pub fn closure_type() -> LLVMType {
  LLVMType::Struct {
    name: "Closure".to_string(),
  }
}

pub fn constructor_type() -> LLVMType {
  LLVMType::Struct {
    name: "Constructor".to_string(),
  }
}

pub fn string_type() -> LLVMType {
  LLVMType::Struct {
    name: "StringObj".to_string(),
  }
}
