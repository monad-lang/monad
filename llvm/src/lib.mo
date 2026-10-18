// The llvm mote's library root -- bare `use llvm` resolves here.
//
// Everything here is compiler-agnostic: the LLVM IR data model and its
// text rendering (`llvm.ir`), the string map that model is built on
// (`llvm.strmap`), and the external-tool glue that turns IR text into a
// linked binary (`llvm.link`). Nothing in this mote knows what a Monad
// term is -- that is `lang`'s side of the seam.

pub use lib::ir {LLVMModule, emit_module}
pub use lib::link {compile_ir_to_obj, compile_ir_to_obj_with, compile_runtime_obj, compile_runtime_obj_for, link_ir, link_objects, link_objects_for, map_dash_l}
pub use lib::target {TargetSpec, TargetKind, TargetPlan}
