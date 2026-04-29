pub mod codegen;
pub mod ir;
pub mod runtime;

pub use codegen::compile_decls;
pub use ir::LLVMModule;
pub use runtime::RuntimeBuilder;
