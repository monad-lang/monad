use monad_core::term::Par;

use crate::ir::{LLVMBasicBlock, LLVMFunction, LLVMInstruction, LLVMType, LLVMValue};

use super::context::CodegenCtx;
use super::term::compile_term;

pub fn compile_lambda(
  ctx: &mut CodegenCtx,
  param: &Par,
  body: &monad_core::term::Term,
) -> Result<LLVMValue, String> {
  let entry_name = ctx.fresh_label("lambda");

  let param_type = LLVMType::I64;
  let return_type = LLVMType::I64;

  let mut func = LLVMFunction::new(
    &entry_name,
    vec![("p0".to_string(), param_type)],
    return_type,
  );

  let entry_block = LLVMBasicBlock::new("entry");
  func.add_block(entry_block);

  ctx.push_function(func);

  if let Par::P(p) = param {
    ctx.bind_local(p.name.clone(), LLVMValue::Param(0));
  }

  let body_value = compile_term(ctx, body)?;

  let func = ctx.pop_function().unwrap();
  ctx.module.add_function(func.clone());

  let func = ctx.module.functions.last_mut().unwrap();
  func
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Return(body_value));

  Ok(LLVMValue::Var(entry_name))
}
