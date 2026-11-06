// Term -> LLVM IR *text*, for callers that have a bare `List Def` and want
// a module's worth of .ll out of it. The toolchain half of "linking" -- llc,
// clang, the runtime object -- is `llvm/src/link.mo`, in the llvm mote; this
// file stays in lang because it speaks Term.

use lang::types {
    Def, NamePath, app, binder_named, concrete, i64, id, lam, lit, named, num,
    package_private,
    sort, var,
}
use llvm::ir {emit_module}
use lib::emit {compile_db_decls_ir}

open Term {app, lam, lit, var}
open Literal {num}
open Identifier {id}
open NumSuffix {i64}
open Param {mk}
open Def {mk}

/// Generate LLVM IR text from a list of Defs.
#[partial]
def compile_defs_to_ir (defs : List Def) : String :=
    let module_ := compile_db_decls_ir defs in
    emit_module module_
