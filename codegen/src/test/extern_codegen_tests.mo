use lang::types {
    Term, TypeConstraint, binder_named, group, hole, lam, named,
    package_private, sort_n,
    str, var,
}
use lang::module {}
use llvm::ir {emit_module}
use lib::emit {compile_db_decls_ir}

open Def {mk}
open Attribute {mk}
open AttrArg {str, named, group}
open Identifier {id}
open DebugName {named}

def empty_attrs : List Attribute := List.empty

/// `Term.var` for a type name, the shape these fixtures use.
#[partial]
def tv (name : String) : Term := Term.var 0 (named (id name))

/// `RawIO A`.
#[partial]
def raw_io (t : Term) : Term := Term.app (Term.var 0 (named (id "RawIO"))) t

/// One `#[extern "c" ...]` def with a single param, in the shape every
/// fixture below needs: a lambda per param (see the comment above), the
/// declared result type, and the extern attribute's own args.
#[partial]
def extern_fixture (name : String) (param_ty : Term) (ret_ty : Term) (ext_args : List AttrArg) : Def :=
    let attrs := List.cons (Attribute.mk (id "extern") ext_args) List.empty in
    Def.mk (NamePath.mk (List.cons (id name) List.empty)) ret_ty
        (Term.lam (binder_named (id "a")) param_ty Term.hole)
        ([] : List TypeConstraint) attrs Visibility.package_private List.empty

/// Compile one def's module and test the rendered IR for `needle`.
#[partial]
def contains_def_ir (d : Def) (needle : String) : Bool :=
    String.contains (emit_module (compile_db_decls_ir (List.cons d List.empty))) needle

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
def mk_puts_def : Def := extern_fixture "puts_ffi" string_term (tv "I32") [AttrArg.str "c"]

/// `puts_ffi` (String → I32) compiles to:
///   declare i32 @puts(i8*)
///   define i64 @<wrapper>(i64 %p0) { %t = inttoptr i64 %p0 to i8* ...
///      call i32 @puts(i8* %t) ... %r = sext i32 %c to i64 ... ret i64 %r }
#[test]
def test_extern_puts_declare : Bool :=
    contains_def_ir mk_puts_def "declare i32 @puts"

/// `puts_ffi` wrapper body must call `puts` with the inttoptr-cast param.
#[test]
def test_extern_puts_wrapper_call : Bool :=
    contains_def_ir mk_puts_def "call i32 @puts"

/// `puts_ffi`'s `String` param must cross the boundary as
/// `inttoptr i64 %p0 to i8*` — the wrapper's param is the uniform boxed
/// `i64`, and `bitcast` disallows ptr<->int.
#[test]
def test_extern_puts_param_inttoptr : Bool :=
    contains_def_ir mk_puts_def "inttoptr i64 %p0 to i8*"

/// `puts_ffi`'s `i32` result must come back SIGN-extended: C integers
/// are signed (`puts` returns EOF = -1 on error), and the `zext` this
/// replaces turned every negative value into a huge positive one.
#[test]
def test_extern_puts_return_sext : Bool :=
    contains_def_ir mk_puts_def "sext i32"

/// `strlen : String -> I64` (link_name override via `#[extern "c" { link_name := "strlen" }]`).
#[partial]
def mk_strlen_def : Def := extern_fixture "strlen" string_term (tv "I64") [AttrArg.str "c", AttrArg.named (id "link_name") (AttrArg.str "strlen")]

/// `#[extern "c" { link_name := "strlen" }]` must emit `declare i64 @strlen(i8*)`
/// (NOT `@mystrlen` — the override picks the symbol).
#[test]
def test_extern_strlen_link_name_override : Bool :=
    contains_def_ir mk_strlen_def "declare i64 @strlen"

/// The override must not disturb the param cast — `strlen`'s `String`
/// param still enters the call as `i8*` via `inttoptr`.
#[test]
def test_extern_strlen_param_inttoptr : Bool :=
    contains_def_ir mk_strlen_def "inttoptr i64 %p0 to i8*"

/// `sin : F64 -> F64` must emit `declare double @sin(double)` — the
/// `double` is what proves `return_llvm_type` peeled the `Term.ctx`
/// wrapper and then the pi chain; an `i64` here means it stopped early.
///
/// No `lib := "m"` on the attribute: which library `sin` lives in is
/// declared once by the mote (`[link] libs` in `mote.toml`), not by every
/// def that binds a symbol from it.
#[partial]
def mk_sin_def : Def := extern_fixture "sin" (tv "F64") (tv "F64") [AttrArg.str "c"]

#[test]
def test_extern_sin_declare_double : Bool :=
    contains_def_ir mk_sin_def "declare double @sin"

/// `sin`'s `F64` param enters the call as `bitcast i64 %p0 to double`
/// — same 64 bits, the boxed-double convention.
#[test]
def test_extern_sin_param_bitcast_double : Bool :=
    contains_def_ir mk_sin_def "bitcast i64 %p0 to double"

/// `abs : I32 -> I32` — the narrow-integer shape. The param must be
/// TRUNCATED (a `bitcast` between unequal widths is invalid LLVM:
/// `llc: invalid cast opcode for cast from 'i64' to 'i32'`) and the
/// signed return sign-extended.
#[partial]
def mk_abs_def : Def := extern_fixture "abs" (tv "I32") (tv "I32") [AttrArg.str "c"]

#[test]
def test_extern_abs_declare : Bool :=
    contains_def_ir mk_abs_def "declare i32 @abs"

#[test]
def test_extern_abs_param_trunc : Bool :=
    contains_def_ir mk_abs_def "trunc i64 %p0 to i32"

#[test]
def test_extern_abs_return_sext : Bool :=
    contains_def_ir mk_abs_def "sext i32"

/// `link_name` written in the PARSED attribute shape —
/// `lang/parser.mo`'s `attr_arg_named_close` wraps `{link_name := "..."}`
/// in a single `AttrArg.group` (deliberately NOT flattened onto the
/// attribute's own arg list), so `find_named_arg` must recurse into the
/// group or the override reads as absent and the def links against its
/// own name instead. Regression test for the parsed-vs-constructed-attr
/// mismatch the flat-attr fixtures above can't catch.
#[partial]
def mk_sin_def_grouped : Def := extern_fixture "sin" (tv "F64") (tv "F64") [AttrArg.str "c", AttrArg.group [AttrArg.named (id "link_name") (AttrArg.str "sinf")]]

#[test]
def test_extern_link_name_grouped_attr : Bool :=
    contains_def_ir mk_sin_def_grouped "declare double @sinf"

/// A non-extern def must produce NO `declare` for any C symbol — only
/// the wrapper function (and existing runtime declarations).
#[partial]
def mk_plain_def : Def :=
    let x_id := id "x" in
    let body := Term.var 0 (named x_id) in
    Def.mk (NamePath.mk (List.cons (id "plain") List.empty))
        (sort_n 1) body
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private List.empty

#[test]
def test_no_extern_attr_no_c_declare : Bool :=
    Bool.not (contains_def_ir mk_plain_def "declare i64 @plain")

/// `ctx_new_ffi : Ptr -> Ptr` — the opaque-pointer shape every OpenSSL
/// handle crosses the FFI in (`SSL_CTX_new : SSL_CTX* -> SSL_CTX*`, and
/// `SSL_CTX_new : Ptr -> Ptr` in motes/tls). `term_to_llvm_type`'s `Ptr`
/// arm maps the name to `ptr i8`, which is what makes the declared
/// return `i8*` here — an `i64` means the arm did not fire and the
/// fallback swallowed the pointer.
#[partial]
def mk_ctx_new_def : Def := extern_fixture "ctx_new_ffi" (tv "Ptr") (tv "Ptr") [AttrArg.str "c"]

#[test]
def test_extern_ptr_return_declares_i8ptr : Bool :=
    contains_def_ir mk_ctx_new_def "declare i8* @ctx_new_ffi"

/// The `Ptr` result must come back as `ptrtoint` — the raw pointer word
/// reboxed into the uniform `i64` the wrapper returns.
#[test]
def test_extern_ptr_return_ptrtoint : Bool :=
    contains_def_ir mk_ctx_new_def "ptrtoint i8*"

/// A SIDE-EFFECTING extern is declared `RawIO I32`. The wrapper must box
/// the raw `i32` result exactly once (`monad_io_pure`), so the value
/// composes with `IO.mk` like a `raw_io_passthrough` native, while the
/// inner `declare` keeps the true ABI type (`i32`, not `i64`) and the
/// result is still sign-extended before boxing.
#[partial]
def mk_puts_raw_io_def : Def := extern_fixture "puts_raw_io" string_term (raw_io (tv "I32")) [AttrArg.str "c"]

#[test]
def test_extern_raw_io_declares_payload_type : Bool :=
    contains_def_ir mk_puts_raw_io_def "declare i32 @puts_raw_io"

#[test]
def test_extern_raw_io_return_sext : Bool :=
    contains_def_ir mk_puts_raw_io_def "sext i32"

#[test]
def test_extern_raw_io_return_boxes_once : Bool :=
    contains_def_ir mk_puts_raw_io_def "call i64 @monad_io_pure"

/// `RawIO Ptr` — the payload type must still drive the inner ABI
/// declaration (`i8*`), not the `i64` fallback.
#[partial]
def mk_ctx_new_raw_io_def : Def := extern_fixture "ctx_new_raw_io" (tv "Ptr") (raw_io (tv "Ptr")) [AttrArg.str "c"]

#[test]
def test_extern_raw_io_ptr_declares_i8ptr : Bool :=
    contains_def_ir mk_ctx_new_raw_io_def "declare i8* @ctx_new_raw_io"

/// A pure extern (no `RawIO`) must NOT call `monad_io_pure` — the box is
/// only for a declared `RawIO A`.
#[test]
def test_extern_pure_return_not_boxed : Bool :=
    Bool.not (contains_def_ir mk_strlen_def "call i64 @monad_io_pure")
