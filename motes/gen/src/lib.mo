// The gen mote's index. This file names the surface; the MODULES are what a
// generator imports, because a `pub use` re-export is not visible to another
// mote in either compiler:
//
//   use gen::env {Env, Gen.lam, Gen.ref}        binder stack, de Bruijn indices
//   use gen::tree {Gen.emit, Leaf, Spec, ...}  balanced dispatch trees
//   use gen::io {Gen.arg, Gen.banner, Gen.write_or_check}
//
// The term and declaration builders live in `lang::construct` (the compiler
// owns the AST and the printer); a generator imports those from there.
