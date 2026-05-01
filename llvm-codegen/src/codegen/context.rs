use std::collections::HashMap;

use monad_core::term::{Identifier, ModulePath};

use crate::ir::{LLVMFunction, LLVMModule, LLVMValue};

#[derive(Clone)]
pub struct CodegenCtx {
  pub module: LLVMModule,
  pub locals: HashMap<Identifier, LLVMValue>,
  pub next_temp: u64,
  pub next_label: u64,
  pub function_stack: Vec<LLVMFunction>,
  pub native_funs: HashMap<ModulePath, String>,
}

impl CodegenCtx {
  pub fn new() -> Self {
    let mut module = LLVMModule::new();
    Self::add_runtime_declarations(&mut module);
    CodegenCtx {
      module,
      locals: HashMap::new(),
      next_temp: 0,
      next_label: 0,
      function_stack: vec![],
      native_funs: HashMap::new(),
    }
  }

  fn add_runtime_declarations(module: &mut LLVMModule) {
    let runtime_funs = [
      ("monad_alloc", vec!["i64".to_string()], "i8*".to_string()),
      ("monad_retain", vec!["i8*".to_string()], "void".to_string()),
      ("monad_release", vec!["i8*".to_string()], "void".to_string()),
      (
        "monad_print_str",
        vec!["i8*".to_string()],
        "void".to_string(),
      ),
      (
        "alloc_closure",
        vec!["i8*".to_string(), "i64".to_string(), "i64".to_string()],
        "%Closure*".to_string(),
      ),
      (
        "alloc_constructor",
        vec!["i64".to_string(), "i64".to_string()],
        "%Constructor*".to_string(),
      ),
      (
        "alloc_string",
        vec!["i8*".to_string(), "i64".to_string()],
        "%StringObj*".to_string(),
      ),
    ];
    for (name, params, ret) in runtime_funs {
      module.add_declaration(crate::ir::LLVMDeclaration {
        name: name.to_string(),
        params,
        return_type: ret,
      });
    }
  }

  pub fn register_native(&mut self, name: ModulePath, native_name: String) {
    self.native_funs.insert(name, native_name);
  }

  pub fn lookup_native(&self, name: &ModulePath) -> Option<&String> {
    self.native_funs.get(name)
  }

  pub fn fresh_temp(&mut self) -> String {
    let name = format!("t{}", self.next_temp);
    self.next_temp += 1;
    name
  }

  pub fn fresh_label(&mut self, prefix: &str) -> String {
    let name = format!("{}_{}", prefix, self.next_label);
    self.next_label += 1;
    name
  }

  pub fn bind_local(&mut self, name: Identifier, value: LLVMValue) {
    self.locals.insert(name, value);
  }

  pub fn lookup_local(&self, name: &Identifier) -> Option<LLVMValue> {
    self.locals.get(name).cloned()
  }

  pub fn push_scope(&mut self) {
    self.locals = HashMap::new();
  }

  pub fn pop_scope(&mut self) {}

  pub fn push_function(&mut self, func: LLVMFunction) {
    self.function_stack.push(func);
  }

  pub fn pop_function(&mut self) -> Option<LLVMFunction> {
    let func = self.function_stack.pop();
    if let Some(f) = &func {
      self.module.add_function(f.clone());
    }
    func
  }

  pub fn current_function_mut(&mut self) -> Result<&mut LLVMFunction, String> {
    self
      .function_stack
      .last_mut()
      .ok_or_else(|| "No current function".to_string())
  }

  pub fn current_function(&self) -> Result<&LLVMFunction, String> {
    self
      .function_stack
      .last()
      .ok_or_else(|| "No current function".to_string())
  }
}
