use std::fmt;

use super::types::LLVMType;

#[derive(Clone, Debug)]
pub enum LLVMValue {
  Int(i64),
  Int32(i32),
  Bool(bool),
  Unit,
  Var(String),
  Param(usize),
  Global(String),
  Call {
    function: String,
    return_type: LLVMType,
    args: Vec<LLVMValue>,
    is_tail: bool,
  },
  Add(Box<LLVMValue>, Box<LLVMValue>),
  Sub(Box<LLVMValue>, Box<LLVMValue>),
  Mul(Box<LLVMValue>, Box<LLVMValue>),
  Div(Box<LLVMValue>, Box<LLVMValue>),
  IcmpEq(Box<LLVMValue>, Box<LLVMValue>),
  Zext {
    value: Box<LLVMValue>,
    from_type: LLVMType,
    to_type: LLVMType,
  },
  Trunc {
    value: Box<LLVMValue>,
    from_type: LLVMType,
    to_type: LLVMType,
  },
  Phi(Vec<(LLVMValue, String)>),
  GetElementPtr {
    base: Box<LLVMValue>,
    indices: Vec<i64>,
  },
  Load {
    ptr: Box<LLVMValue>,
  },
  BitCast {
    value: Box<LLVMValue>,
    to_type: LLVMType,
  },
  AllocClosure {
    entry: String,
    arity: i64,
    env: Vec<LLVMValue>,
  },
  AllocConstructor {
    tag: i64,
    fields: Vec<LLVMValue>,
  },
}

impl LLVMValue {
  pub fn var(name: &str) -> Self {
    LLVMValue::Var(name.to_string())
  }

  pub fn call(function: &str, return_type: LLVMType, args: Vec<LLVMValue>) -> Self {
    LLVMValue::Call {
      function: function.to_string(),
      return_type,
      args,
      is_tail: false,
    }
  }

  pub fn tail_call(function: &str, return_type: LLVMType, args: Vec<LLVMValue>) -> Self {
    LLVMValue::Call {
      function: function.to_string(),
      return_type,
      args,
      is_tail: true,
    }
  }

  pub fn llvm_type(&self) -> LLVMType {
    match self {
      LLVMValue::Int(_) => LLVMType::I64,
      LLVMValue::Int32(_) => LLVMType::I32,
      LLVMValue::Bool(_) => LLVMType::I1,
      LLVMValue::Unit => LLVMType::Void,
      LLVMValue::Var(_) | LLVMValue::Param(_) => LLVMType::I64,
      LLVMValue::Global(_) => LLVMType::Pointer(Box::new(LLVMType::I8)),
      LLVMValue::Call { return_type, .. } => return_type.clone(),
      LLVMValue::Add(_, _)
      | LLVMValue::Sub(_, _)
      | LLVMValue::Mul(_, _)
      | LLVMValue::Div(_, _)
      | LLVMValue::IcmpEq(_, _) => LLVMType::I1,
      LLVMValue::Zext { to_type, .. } => to_type.clone(),
      LLVMValue::Trunc { to_type, .. } => to_type.clone(),
      LLVMValue::Phi(_) => LLVMType::I64,
      LLVMValue::GetElementPtr { .. } => LLVMType::Pointer(Box::new(LLVMType::I8)),
      LLVMValue::Load { .. } => LLVMType::I64,
      LLVMValue::BitCast { to_type, .. } => to_type.clone(),
      LLVMValue::AllocClosure { .. } => LLVMType::Pointer(Box::new(LLVMType::I8)),
      LLVMValue::AllocConstructor { .. } => LLVMType::Pointer(Box::new(LLVMType::I8)),
    }
  }

  pub fn display_typed(&self) -> String {
    format!("{} {}", self.llvm_type(), self)
  }
}

impl fmt::Display for LLVMValue {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      LLVMValue::Int(n) => write!(f, "{}", n),
      LLVMValue::Int32(n) => write!(f, "{}", n),
      LLVMValue::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
      LLVMValue::Unit => write!(f, "void"),
      LLVMValue::Var(name) => write!(f, "%{}", name),
      LLVMValue::Param(i) => write!(f, "%p{}", i),
      LLVMValue::Global(name) => write!(f, "@{}", name),
      LLVMValue::Call {
        function,
        return_type,
        args,
        is_tail,
      } => {
        if *is_tail {
          write!(f, "tail call {} @{}(", return_type, function)?;
        } else {
          write!(f, "call {} @{}(", return_type, function)?;
        }
        for (i, arg) in args.iter().enumerate() {
          if i > 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", arg.display_typed())?;
        }
        write!(f, ")")
      }
      LLVMValue::Add(a, b) => write!(f, "add i64 {}, {}", a, b),
      LLVMValue::Sub(a, b) => write!(f, "sub i64 {}, {}", a, b),
      LLVMValue::Mul(a, b) => write!(f, "mul i64 {}, {}", a, b),
      LLVMValue::Div(a, b) => write!(f, "sdiv i64 {}, {}", a, b),
      LLVMValue::IcmpEq(a, b) => write!(f, "icmp eq i64 {}, {}", a, b),
      LLVMValue::Zext {
        value,
        from_type,
        to_type,
      } => {
        write!(f, "zext {} {} to {}", from_type, value, to_type)
      }
      LLVMValue::Trunc {
        value,
        from_type,
        to_type,
      } => {
        write!(f, "trunc {} {} to {}", from_type, value, to_type)
      }
      LLVMValue::Phi(pairs) => {
        write!(f, "phi i64 [")?;
        for (i, (val, label)) in pairs.iter().enumerate() {
          if i > 0 {
            write!(f, ", ")?;
          }
          write!(f, "[{}, %{}]", val, label)?;
        }
        write!(f, "]")
      }
      LLVMValue::GetElementPtr { base, indices } => {
        write!(f, "getelementptr {}, {}", base, indices.len())?;
        for idx in indices {
          write!(f, ", i64 {}", idx)?;
        }
        Ok(())
      }
      LLVMValue::Load { ptr } => write!(f, "load {}", ptr),
      LLVMValue::BitCast { value, to_type } => {
        write!(f, "bitcast {} to {}", value, to_type)
      }
      LLVMValue::AllocClosure { entry, arity, env } => {
        write!(f, "alloc_closure({}, {}, {})", entry, arity, env.len())
      }
      LLVMValue::AllocConstructor { tag, fields } => {
        write!(f, "alloc_constructor({}, {})", tag, fields.len())
      }
    }
  }
}
