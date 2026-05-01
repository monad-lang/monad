mod constructors;
mod context;
mod control;
mod lambda;
mod literals;
mod native;
mod term;

pub use context::CodegenCtx;
pub use term::compile_term;

use monad_core::term::{Decl, Def, Named};

use crate::ir::{LLVMBasicBlock, LLVMFunction, LLVMInstruction, LLVMModule, LLVMType, LLVMValue};

pub fn compile_decls(decls: &[Decl]) -> Result<LLVMModule, String> {
  use monad_core::term::Term;

  let mut ctx = CodegenCtx::new();

  for decl in decls {
    match decl {
      Decl::Def(def) => {
        let mut body = &def.term;
        while let Some((_, inner)) = body.as_lam() {
          body = inner;
        }
        let is_native = matches!(body, Term::Ntv { .. });
        if is_native {
          if let Term::Ntv { native } = body {
            ctx.register_native(def.name().clone(), native.native_name.to_string());
          }
        }
        compile_def(&mut ctx, def)?;
      }
      Decl::Type(inductive) => {
        for cons in inductive.constructors() {
          compile_constructor_decl(&mut ctx, cons)?;
        }
      }
      _ => {}
    }
  }

  if ctx.module.functions.iter().any(|f| f.name == "main") {
    rename_main_to_monad(&mut ctx)?;
    compile_main_wrapper(&mut ctx)?;
  }

  Ok(ctx.module)
}

fn is_i64_native(native_name: &str) -> bool {
  matches!(
    native_name,
    "i64_add" | "i64_sub" | "i64_mul" | "i64_div" | "i64_eq"
  )
}

fn rename_main_to_monad(ctx: &mut CodegenCtx) -> Result<(), String> {
  for func in &mut ctx.module.functions {
    if func.name == "main" {
      func.name = "main_monad".to_string();
      break;
    }
  }
  Ok(())
}

fn compile_def(ctx: &mut CodegenCtx, def: &Def) -> Result<(), String> {
  use monad_core::term::Term;

  let mut body = &def.term;
  let params = def.term.collect_params();
  while let Some((_, inner)) = body.as_lam() {
    body = inner;
  }

  if let Term::Ntv { native } = body {
    if is_i64_native(&native.native_name.to_string()) {
      compile_i64_native(ctx, def, &native.native_name.to_string(), &params)?;
      return Ok(());
    }
    return Ok(());
  }

  let name = def.name().to_string().replace('.', "_");
  let param_count = params.len();

  let llvm_params: Vec<(String, LLVMType)> = (0..param_count)
    .map(|i| (format!("p{}", i), LLVMType::I64))
    .collect();

  let return_type = LLVMType::I64;

  let mut func = LLVMFunction::new(&name, llvm_params, return_type);

  let entry_block = crate::ir::LLVMBasicBlock::new("entry");
  func.add_block(entry_block);

  ctx.push_function(func);
  ctx.push_scope();

  for (i, param) in params.iter().enumerate() {
    if let monad_core::term::Par::P(p) = *param {
      ctx.bind_local(p.name.clone(), LLVMValue::Param(i));
    }
  }

  let body_term = &def.term;
  let mut current = body_term;
  for _ in 0..param_count {
    if let Some((_, body)) = current.as_lam() {
      current = body;
    }
  }

  let body_value = compile_term(ctx, current)?;

  ctx.pop_scope();

  let func = ctx.current_function_mut()?;
  func
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Return(body_value));

  ctx.pop_function();

  Ok(())
}

fn compile_i64_native(
  ctx: &mut CodegenCtx,
  def: &Def,
  native_name: &str,
  params: &[&monad_core::term::Par],
) -> Result<(), String> {
  let name = def.name().to_string().replace('.', "_");
  let llvm_params: Vec<(String, LLVMType)> = (0..params.len())
    .map(|i| (format!("p{}", i), LLVMType::I64))
    .collect();

  let mut func = LLVMFunction::new(&name, llvm_params, LLVMType::I64);
  let entry_block = LLVMBasicBlock::new("entry");
  func.add_block(entry_block);

  ctx.push_function(func);
  ctx.push_scope();

  for i in 0..params.len() {
    ctx.bind_local(
      monad_core::term::Identifier::new(format!("p{i}")),
      LLVMValue::Param(i),
    );
  }

  let temp = ctx.fresh_temp();

  match native_name {
    "i64_add" => {
      ctx
        .current_function_mut()?
        .blocks
        .last_mut()
        .unwrap()
        .add(LLVMInstruction::Assign {
          target: temp.clone(),
          value: LLVMValue::Add(Box::new(LLVMValue::Param(0)), Box::new(LLVMValue::Param(1))),
        });
    }
    "i64_sub" => {
      ctx
        .current_function_mut()?
        .blocks
        .last_mut()
        .unwrap()
        .add(LLVMInstruction::Assign {
          target: temp.clone(),
          value: LLVMValue::Sub(Box::new(LLVMValue::Param(0)), Box::new(LLVMValue::Param(1))),
        });
    }
    "i64_mul" => {
      ctx
        .current_function_mut()?
        .blocks
        .last_mut()
        .unwrap()
        .add(LLVMInstruction::Assign {
          target: temp.clone(),
          value: LLVMValue::Mul(Box::new(LLVMValue::Param(0)), Box::new(LLVMValue::Param(1))),
        });
    }
    "i64_div" => {
      ctx
        .current_function_mut()?
        .blocks
        .last_mut()
        .unwrap()
        .add(LLVMInstruction::Assign {
          target: temp.clone(),
          value: LLVMValue::Div(Box::new(LLVMValue::Param(0)), Box::new(LLVMValue::Param(1))),
        });
    }
    "i64_eq" => {
      let icmp_temp = ctx.fresh_temp();
      ctx
        .current_function_mut()?
        .blocks
        .last_mut()
        .unwrap()
        .add(LLVMInstruction::Assign {
          target: icmp_temp.clone(),
          value: LLVMValue::IcmpEq(Box::new(LLVMValue::Param(0)), Box::new(LLVMValue::Param(1))),
        });
      ctx
        .current_function_mut()?
        .blocks
        .last_mut()
        .unwrap()
        .add(LLVMInstruction::Assign {
          target: temp.clone(),
          value: LLVMValue::Zext {
            value: Box::new(LLVMValue::Var(icmp_temp)),
            from_type: LLVMType::I1,
            to_type: LLVMType::I64,
          },
        });
    }
    _ => return Err(format!("Unknown i64 native: {native_name}")),
  }

  ctx.pop_scope();

  let func = ctx.current_function_mut()?;
  func
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Return(LLVMValue::Var(temp)));

  ctx.pop_function();

  Ok(())
}

fn compile_constructor_decl(
  ctx: &mut CodegenCtx,
  cons: &monad_core::term::InductConstructor,
) -> Result<(), String> {
  let name = cons.name().to_string().replace('.', "_");

  let param_count = cons.params().len();
  let llvm_params: Vec<(String, LLVMType)> = (0..param_count)
    .map(|i| (format!("p{}", i), LLVMType::I64))
    .collect();

  let return_type = LLVMType::I64;

  let mut func = LLVMFunction::new(&name, llvm_params, return_type);

  let entry_block = LLVMBasicBlock::new("entry");
  func.add_block(entry_block);

  ctx.push_function(func);
  ctx.push_scope();

  for (i, param) in cons.params().iter().enumerate() {
    ctx.bind_local(param.name.clone(), LLVMValue::Param(i));
  }

  let fields: Vec<LLVMValue> = (0..param_count).map(|i| LLVMValue::Param(i)).collect();

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

  ctx
    .current_function_mut()?
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Return(LLVMValue::Var(temp)));

  ctx.pop_scope();
  ctx.pop_function();

  Ok(())
}

fn compile_main_wrapper(ctx: &mut CodegenCtx) -> Result<(), String> {
  let mut main_func = LLVMFunction::new(
    "main",
    vec![
      ("argc".to_string(), LLVMType::I32),
      ("argv".to_string(), LLVMType::I64),
    ],
    LLVMType::I32,
  );
  main_func.is_ghc_cc = false;

  let entry_block = LLVMBasicBlock::new("entry");
  main_func.add_block(entry_block);

  ctx.push_function(main_func);

  let main_call = LLVMValue::Call {
    function: "main_monad".to_string(),
    return_type: LLVMType::I64,
    args: vec![],
    is_tail: false,
  };

  let temp = ctx.fresh_temp();
  ctx
    .current_function_mut()?
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Assign {
      target: temp.clone(),
      value: main_call,
    });

  let trunc_temp = ctx.fresh_temp();
  ctx
    .current_function_mut()?
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Assign {
      target: trunc_temp.clone(),
      value: LLVMValue::Trunc {
        value: Box::new(LLVMValue::Var(temp)),
        from_type: LLVMType::I64,
        to_type: LLVMType::I32,
      },
    });

  ctx
    .current_function_mut()?
    .blocks
    .last_mut()
    .unwrap()
    .add(LLVMInstruction::Return(LLVMValue::Var(trunc_temp)));

  ctx.pop_function();

  Ok(())
}
