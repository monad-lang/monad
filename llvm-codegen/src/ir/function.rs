use super::types::LLVMType;
use super::value::LLVMValue;

#[derive(Clone, Debug)]
pub struct LLVMFunction {
    pub name: String,
    pub params: Vec<(String, LLVMType)>,
    pub return_type: LLVMType,
    pub blocks: Vec<LLVMBasicBlock>,
    pub is_ghc_cc: bool,
}

impl LLVMFunction {
    pub fn new(name: &str, params: Vec<(String, LLVMType)>, return_type: LLVMType) -> Self {
        LLVMFunction {
            name: name.to_string(),
            params,
            return_type,
            blocks: vec![],
            is_ghc_cc: true,
        }
    }

    pub fn add_block(&mut self, block: LLVMBasicBlock) {
        self.blocks.push(block);
    }

    pub fn emit_to(&self, f: &mut dyn std::fmt::Write) -> std::fmt::Result {
        let cc_prefix = if self.is_ghc_cc {
            "define cc 9 "
        } else {
            "define "
        };

        writeln!(f)?;
        writeln!(f, "; Function: {}", self.name)?;
        writeln!(f, "{}{} @{}({}) {{", cc_prefix, self.return_type, self.name, {
            let params: Vec<String> = self
                .params
                .iter()
                .map(|(name, typ)| format!("{} %{}", typ, name))
                .collect();
            params.join(", ")
        })?;

        for block in &self.blocks {
            writeln!(f)?;
            writeln!(f, "{}:", block.label)?;
            for instr in &block.instructions {
                match instr {
                    LLVMInstruction::Assign { target, value } => {
                        writeln!(f, "  %{} = {}", target, value)?;
                    }
                    LLVMInstruction::Branch {
                        condition,
                        then_label,
                        else_label,
                    } => {
                        writeln!(
                            f,
                            "  br {} %{}, %{}",
                            condition, then_label, else_label
                        )?;
                    }
                    LLVMInstruction::Jump { label } => {
                        writeln!(f, "  br label %{}", label)?;
                    }
                    LLVMInstruction::Return(value) => {
                        if value.is_unit() {
                            writeln!(f, "  ret void")?;
                        } else if value.is_i32() {
                            writeln!(f, "  ret i32 {}", value)?;
                        } else {
                            writeln!(f, "  ret i64 {}", value)?;
                        }
                    }
                    LLVMInstruction::Comment(c) => {
                        writeln!(f, "  ; {}", c)?;
                    }
                }
            }
        }

        writeln!(f, "}}")
    }
}

#[derive(Clone, Debug)]
pub struct LLVMBasicBlock {
    pub label: String,
    pub instructions: Vec<LLVMInstruction>,
}

impl LLVMBasicBlock {
    pub fn new(label: &str) -> Self {
        LLVMBasicBlock {
            label: label.to_string(),
            instructions: vec![],
        }
    }

    pub fn add(&mut self, instr: LLVMInstruction) {
        self.instructions.push(instr);
    }
}

#[derive(Clone, Debug)]
pub enum LLVMInstruction {
    Assign {
        target: String,
        value: LLVMValue,
    },
    Branch {
        condition: LLVMValue,
        then_label: String,
        else_label: String,
    },
    Jump {
        label: String,
    },
    Return(LLVMValue),
    Comment(String),
}

impl LLVMValue {
    pub fn is_unit(&self) -> bool {
        matches!(self, LLVMValue::Unit)
    }

    pub fn is_i32(&self) -> bool {
        matches!(self, LLVMValue::Int32(_))
    }
}
