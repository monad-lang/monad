use monad_core::term::{Literal, Term};

use crate::ir::LLVMValue;

use super::context::CodegenCtx;

pub fn compile_literal(ctx: &mut CodegenCtx, term: &Term) -> Result<LLVMValue, String> {
  match term {
    Term::Lit {
      value: Literal::Num { value, .. },
    } => Ok(LLVMValue::Int(*value)),
    Term::Lit {
      value: Literal::Str { value },
    } => {
      let global_name = ctx.fresh_label("str");
      ctx
        .module
        .add_global(crate::ir::LLVMGlobal::string(&global_name, value));
      Ok(LLVMValue::Global(global_name))
    }
    _ => Err(format!("Expected literal, got: {:?}", term)),
  }
}
