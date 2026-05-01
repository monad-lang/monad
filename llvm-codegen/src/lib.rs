pub mod codegen;
pub mod compiler;
pub mod ir;
pub mod runtime;

pub use codegen::compile_decls;
pub use compiler::{
  CompileOptions, CompileResult, OutputKind, compile, compile_ir_to_object, compile_runtime,
  compile_to_ir, link, write_ir_file,
};
pub use ir::LLVMModule;
pub use runtime::RuntimeBuilder;
