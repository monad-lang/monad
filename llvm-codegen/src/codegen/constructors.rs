use monad_core::term::Constructor;

use crate::ir::{LLVMBasicBlock, LLVMFunction, LLVMInstruction, LLVMType, LLVMValue};

use super::context::CodegenCtx;
use super::term::compile_term;

pub fn compile_constructor_term(
  ctx: &mut CodegenCtx,
  constructor: &Constructor,
) -> Result<LLVMValue, String> {
  let compiled_fields: Result<Vec<LLVMValue>, String> = constructor
    .args()
    .iter()
    .filter_map(|arg| arg.as_ref().map(|a| compile_term(ctx, a)))
    .collect();

  let fields = compiled_fields?;

  let tag = 0;
  let alloc = LLVMValue::AllocConstructor { tag, fields };

  let temp = ctx.fresh_temp();
  ctx
    .current_function_mut()?
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Assign {
      target: temp.clone(),
      value: alloc,
    });

  Ok(LLVMValue::Var(temp))
}

#[allow(dead_code)]
pub fn compile_constructor_decl(
  ctx: &mut CodegenCtx,
  name: &str,
  field_count: usize,
) -> Result<(), String> {
  let params: Vec<(String, LLVMType)> = (0..field_count)
    .map(|i| (format!("p{}", i), LLVMType::I64))
    .collect();

  let return_type = LLVMType::I64;

  let mut func = LLVMFunction::new(name, params, return_type);

  let entry_block = LLVMBasicBlock::new("entry");
  func.add_block(entry_block);

  ctx.push_function(func);

  let fields: Vec<LLVMValue> = (0..field_count).map(|i| LLVMValue::Param(i)).collect();

  let tag = 0;
  let alloc = LLVMValue::AllocConstructor { tag, fields };

  let temp = ctx.fresh_temp();
  ctx
    .current_function_mut()?
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Assign {
      target: temp.clone(),
      value: alloc,
    });

  ctx.pop_function();

  let func = ctx.module.functions.last_mut().unwrap();
  func
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Return(LLVMValue::Var(temp)));

  Ok(())
}
