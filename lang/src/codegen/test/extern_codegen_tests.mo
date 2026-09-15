use lib::types {mk}
use lib::module {mk}
use llvm::ir {mk, emit_module}
use lib::codegen::emit {compile_db_decls_ir}

open Def {mk}
open Attribute {mk}
open AttrArg {str, named, group}
open Identifier {id}
open DebugName {named}

def empty_attrs : List Attribute := List.empty

/// Each fixture's body is a `Term.lam` PER PARAM, because Monad encodes a
/// def's parameters as the lambdas of its body (`collect_db_params`
/// strips them) — a `Term.hole` body means ZERO parameters, and a
/// wrapper with no parameters never exercises the ABI-cast machinery at
/// all. That is how the original version of this suite passed green
/// while the narrow-int casts it should have caught were invalid LLVM:
/// every fixture declared a `Param` nobody read. The lam's own type
/// annotation is what `term_to_llvm_type` maps (`String` -> `i8*`,
/// `I32` -> `i32`, `F64` -> `double`).
#[partial]
def string_term : Term := Term.var 0 (named (id "String"))

/// Render a `(String) -> I32` extern def named `puts_ffi` with the param
/// genuinely attached.
#[partial]
def mk_puts_def : Def :=
    let s_id := id "s" in
    let attrs := List.cons (Attribute.mk (id "extern") (List.cons (AttrArg.str "c") List.empty)) List.empty in
    Def.mk (NamePath.npath (List.cons (id "puts_ffi") List.empty))
        (Term.var 0 (named (id "I32")))
        (Term.lam (DebugName.named s_id) string_term Term.hole)
        ([] : List TypeConstraint) attrs Visibility.package_private

/// `puts_ffi` (String → I32) compiles to:
///   declare i32 @puts(i8*)
///   define i64 @<wrapper>(i64 %p0) { %t = inttoptr i64 %p0 to i8* ...
///      call i32 @puts(i8* %t) ... %r = sext i32 %c to i64 ... ret i64 %r }
#[test]
def test_extern_puts_declare : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_puts_def List.empty)) in
    String.contains ir "declare i32 @puts"

/// `puts_ffi` wrapper body must call `puts` with the inttoptr-cast param.
#[test]
def test_extern_puts_wrapper_call : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_puts_def List.empty)) in
    String.contains ir "call i32 @puts"

/// `puts_ffi`'s `String` param must cross the boundary as
/// `inttoptr i64 %p0 to i8*` — the wrapper's param is the uniform boxed
/// `i64`, and `bitcast` disallows ptr<->int.
#[test]
def test_extern_puts_param_inttoptr : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_puts_def List.empty)) in
    String.contains ir "inttoptr i64 %p0 to i8*"

/// `puts_ffi`'s `i32` result must come back SIGN-extended: C integers
/// are signed (`puts` returns EOF = -1 on error), and the `zext` this
/// replaces turned every negative value into a huge positive one.
#[test]
def test_extern_puts_return_sext : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_puts_def List.empty)) in
    String.contains ir "sext i32"

/// `strlen : String -> I64` (link_name override via `#[extern "c" { link_name := "strlen" }]`).
#[partial]
def mk_strlen_def : Def :=
    let s_id := id "s" in
    let link_arg := AttrArg.named (id "link_name") (AttrArg.str "strlen") in
    let c_arg := AttrArg.str "c" in
    let ext_args := List.cons c_arg (List.cons link_arg List.empty) in
    let attrs := List.cons (Attribute.mk (id "extern") ext_args) List.empty in
    Def.mk (NamePath.npath (List.cons (id "strlen") List.empty))
        (Term.var 0 (named (id "I64")))
        (Term.lam (DebugName.named s_id) string_term Term.hole)
        ([] : List TypeConstraint) attrs Visibility.package_private

/// `#[extern "c" { link_name := "strlen" }]` must emit `declare i64 @strlen(i8*)`
/// (NOT `@mystrlen` — the override picks the symbol).
#[test]
def test_extern_strlen_link_name_override : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_strlen_def List.empty)) in
    String.contains ir "declare i64 @strlen"

/// The override must not disturb the param cast — `strlen`'s `String`
/// param still enters the call as `i8*` via `inttoptr`.
#[test]
def test_extern_strlen_param_inttoptr : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_strlen_def List.empty)) in
    String.contains ir "inttoptr i64 %p0 to i8*"

/// `sin : F64 -> F64` must emit `declare double @sin(double)` — the
/// `double` is what proves `return_llvm_type` peeled the `Term.ctx`
/// wrapper and then the pi chain; an `i64` here means it stopped early.
///
/// No `lib := "m"` on the attribute: which library `sin` lives in is
/// declared once by the mote (`[link] libs` in `mote.toml`), not by every
/// def that binds a symbol from it.
#[partial]
def mk_sin_def : Def :=
    let x_id := id "x" in
    let c_arg := AttrArg.str "c" in
    let ext_args := List.cons c_arg List.empty in
    let attrs := List.cons (Attribute.mk (id "extern") ext_args) List.empty in
    Def.mk (NamePath.npath (List.cons (id "sin") List.empty))
        (Term.var 0 (named (id "F64")))
        (Term.lam (DebugName.named x_id) (Term.var 0 (named (id "F64"))) Term.hole)
        ([] : List TypeConstraint) attrs Visibility.package_private

#[test]
def test_extern_sin_declare_double : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_sin_def List.empty)) in
    String.contains ir "declare double @sin"

/// `sin`'s `F64` param enters the call as `bitcast i64 %p0 to double`
/// — same 64 bits, the boxed-double convention.
#[test]
def test_extern_sin_param_bitcast_double : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_sin_def List.empty)) in
    String.contains ir "bitcast i64 %p0 to double"

/// `abs : I32 -> I32` — the narrow-integer shape. The param must be
/// TRUNCATED (a `bitcast` between unequal widths is invalid LLVM:
/// `llc: invalid cast opcode for cast from 'i64' to 'i32'`) and the
/// signed return sign-extended.
#[partial]
def mk_abs_def : Def :=
    let x_id := id "x" in
    let c_arg := AttrArg.str "c" in
    let ext_args := List.cons c_arg List.empty in
    let attrs := List.cons (Attribute.mk (id "extern") ext_args) List.empty in
    Def.mk (NamePath.npath (List.cons (id "abs") List.empty))
        (Term.var 0 (named (id "I32")))
        (Term.lam (DebugName.named x_id) (Term.var 0 (named (id "I32"))) Term.hole)
        ([] : List TypeConstraint) attrs Visibility.package_private

#[test]
def test_extern_abs_declare : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_abs_def List.empty)) in
    String.contains ir "declare i32 @abs"

#[test]
def test_extern_abs_param_trunc : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_abs_def List.empty)) in
    String.contains ir "trunc i64 %p0 to i32"

#[test]
def test_extern_abs_return_sext : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_abs_def List.empty)) in
    String.contains ir "sext i32"

/// `link_name` written in the PARSED attribute shape —
/// `lang/parser.mo`'s `attr_arg_named_close` wraps `{link_name := "..."}`
/// in a single `AttrArg.group` (deliberately NOT flattened onto the
/// attribute's own arg list), so `find_named_arg` must recurse into the
/// group or the override reads as absent and the def links against its
/// own name instead. Regression test for the parsed-vs-constructed-attr
/// mismatch the flat-attr fixtures above can't catch.
#[partial]
def mk_sin_def_grouped : Def :=
    let x_id := id "x" in
    let link_arg := AttrArg.named (id "link_name") (AttrArg.str "sinf") in
    let link_group := AttrArg.group (List.cons link_arg List.empty) in
    let c_arg := AttrArg.str "c" in
    let ext_args := List.cons c_arg (List.cons link_group List.empty) in
    let attrs := List.cons (Attribute.mk (id "extern") ext_args) List.empty in
    Def.mk (NamePath.npath (List.cons (id "sin") List.empty))
        (Term.var 0 (named (id "F64")))
        (Term.lam (DebugName.named x_id) (Term.var 0 (named (id "F64"))) Term.hole)
        ([] : List TypeConstraint) attrs Visibility.package_private

#[test]
def test_extern_link_name_grouped_attr : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_sin_def_grouped List.empty)) in
    String.contains ir "declare double @sinf"

/// A non-extern def must produce NO `declare` for any C symbol — only
/// the wrapper function (and existing runtime declarations).
#[partial]
def mk_plain_def : Def :=
    let x_id := id "x" in
    let body := Term.var 0 (named x_id) in
    Def.mk (NamePath.npath (List.cons (id "plain") List.empty))
        (Term.type_ 1) body
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private

#[test]
def test_no_extern_attr_no_c_declare : Bool :=
    let ir := emit_module (compile_db_decls_ir (List.cons mk_plain_def List.empty)) in
    not (String.contains ir "declare i64 @plain")
