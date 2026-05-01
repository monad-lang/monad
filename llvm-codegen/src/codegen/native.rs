use monad_core::term::Native;

use crate::ir::{LLVMType, LLVMValue};

use super::context::CodegenCtx;
use super::term::compile_term;

pub fn compile_native(ctx: &mut CodegenCtx, native: &Native) -> Result<LLVMValue, String> {
  let args: Result<Vec<LLVMValue>, String> = native
    .args()
    .iter()
    .filter_map(|arg| arg.as_ref().map(|a| compile_term(ctx, a)))
    .collect();

  let compiled_args = args?;

  let func_name = format!("monad_{}", native.native_name);

  let temp = ctx.fresh_temp();
  let call = LLVMValue::Call {
    function: func_name,
    return_type: LLVMType::I64,
    args: compiled_args,
    is_tail: false,
  };

  ctx
    .current_function_mut()?
    .blocks
    .last_mut()
    .unwrap()
    .add(crate::ir::LLVMInstruction::Assign {
      target: temp.clone(),
      value: call,
    });

  Ok(LLVMValue::Var(temp))
}
