use monad_core::term::Term;

use crate::ir::{LLVMBasicBlock, LLVMInstruction, LLVMValue};

use super::context::CodegenCtx;
use super::term::compile_term;

pub fn compile_if(
    ctx: &mut CodegenCtx,
    condition: &Term,
    then_branch: &Term,
    else_branch: &Term,
) -> Result<LLVMValue, String> {
    let cond_val = compile_term(ctx, condition)?;

    let then_label = ctx.fresh_label("then");
    let else_label = ctx.fresh_label("else");
    let merge_label = ctx.fresh_label("merge");

    let func = ctx.current_function_mut()?;
    func.blocks.last_mut().unwrap().add(LLVMInstruction::Branch {
        condition: cond_val,
        then_label: then_label.clone(),
        else_label: else_label.clone(),
    });

    let mut then_block = LLVMBasicBlock::new(&then_label);
    let then_val = compile_term(ctx, then_branch)?;
    then_block.add(LLVMInstruction::Jump {
        label: merge_label.clone(),
    });

    let mut else_block = LLVMBasicBlock::new(&else_label);
    let else_val = compile_term(ctx, else_branch)?;
    else_block.add(LLVMInstruction::Jump {
        label: merge_label.clone(),
    });

    let mut merge_block = LLVMBasicBlock::new(&merge_label);
    let result_temp = ctx.fresh_temp();
    merge_block.add(LLVMInstruction::Assign {
        target: result_temp.clone(),
        value: LLVMValue::Phi(vec![
            (then_val, then_label.clone()),
            (else_val, else_label.clone()),
        ]),
    });

    let func = ctx.current_function_mut()?;
    func.blocks.push(then_block);
    func.blocks.push(else_block);
    func.blocks.push(merge_block);

    Ok(LLVMValue::Var(result_temp))
}
