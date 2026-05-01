use monad_core::term::{
  Literal,
  Term::{self, Ann, App, Con, Ctx, Forall, Lam, Lit, Ntv, Pi, Type, Var},
};

use crate::ir::{LLVMType, LLVMValue};

use super::constructors::compile_constructor_term;
use super::context::CodegenCtx;
use super::control::compile_if;
use super::lambda::compile_lambda;
use super::literals::compile_literal;
use super::native::compile_native;

pub fn compile_term(ctx: &mut CodegenCtx, term: &Term) -> Result<LLVMValue, String> {
  match term {
    Lit {
      value: Literal::Num { .. },
    }
    | Lit {
      value: Literal::Str { .. },
    } => compile_literal(ctx, term),

    Lit {
      value: Literal::If { value, then, els },
    } => compile_if(ctx, value, then, els),

    Lit {
      value: Literal::Match { .. } | Literal::Map { .. },
    } => Err(format!("Literal not yet supported: {:?}", term)),

    Var { name } => {
      if let Some(id) = name.as_id() {
        if let Some(val) = ctx.lookup_local(id) {
          Ok(val)
        } else {
          Ok(LLVMValue::Var(name.to_string().replace('.', "_")))
        }
      } else {
        Ok(LLVMValue::Var(name.to_string().replace('.', "_")))
      }
    }

    Lam { param, body } => compile_lambda(ctx, param, body),

    App { fun, arg } => compile_application(ctx, fun, arg),

    Con(constructor) => compile_constructor_term(ctx, constructor),

    Ntv { native } => compile_native(ctx, native),

    Ann { term, .. } => compile_term(ctx, term),

    Forall { .. } | Pi { .. } | Type { .. } => Ok(LLVMValue::Unit),

    Ctx { term, .. } => compile_term(ctx, term),

    _ => Err(format!("Unsupported term: {:?}", term)),
  }
}

fn compile_application(ctx: &mut CodegenCtx, fun: &Term, arg: &Term) -> Result<LLVMValue, String> {
  let f_val = compile_term(ctx, fun)?;
  let a_val = compile_term(ctx, arg)?;

  match f_val {
    LLVMValue::Var(name) => {
      let temp = ctx.fresh_temp();
      let call = LLVMValue::Call {
        function: name,
        return_type: LLVMType::I64,
        args: vec![a_val],
        is_tail: false,
      };
      ctx.current_function_mut()?.blocks.last_mut().unwrap().add(
        crate::ir::LLVMInstruction::Assign {
          target: temp.clone(),
          value: call,
        },
      );
      Ok(LLVMValue::Var(temp))
    }
    LLVMValue::Global(name) => {
      let temp = ctx.fresh_temp();
      let call = LLVMValue::Call {
        function: name,
        return_type: LLVMType::I64,
        args: vec![a_val],
        is_tail: false,
      };
      ctx.current_function_mut()?.blocks.last_mut().unwrap().add(
        crate::ir::LLVMInstruction::Assign {
          target: temp.clone(),
          value: call,
        },
      );
      Ok(LLVMValue::Var(temp))
    }
    _ => Err(format!("Expected function, got: {:?}", f_val)),
  }
}
