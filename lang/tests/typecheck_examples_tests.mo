use lang.types {
  Decl, Def, InductConstructor, Inductive, LocalScope, ModulePath, Scope,
  ScopeData, Term, def_d, hole, id, inductive_d, mk, mp,
}
use lang.module {elaborate_module_decls, locals_with_def_typevars, mk, parse_all_decls}
use lang.parser.core {fail, mk, success}
use lang.scope {build_scope_from_decls}
use lang.typecheck.infer {empty_local_types, empty_locals, mk, type_check}

def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

def make_scope (path : ModulePath) (sd : ScopeData) : Scope := {
    module_id := path,
    scope := sd,
    parent := Option.none,
}

def is_hole (t : Term) : Bool := 
    match t {
        Term.hole => true,
        _ => false
    }

def typecheck_module (path : ModulePath) (scope : Scope) (decl_list : List Decl) : Bool := 
    match decl_list {
        List.empty => true,
        List.cons d rest =>
            let result : Bool := typecheck_decl d path scope in
            if result then
                typecheck_module path scope rest
            else
                false
    }

def typecheck_decl (d : Decl) (path : ModulePath) (scope : Scope) : Bool := 
    match d {
        Decl.def_d df => typecheck_def df scope,
        Decl.inductive_d ind => typecheck_inductive ind scope,
        _ => true  // Skip use, open, infix, class, instance for now
    }

def typecheck_def (df : Def) (scope : Scope) : Bool :=
    match df {
        mk _name typ body _constraints _attrs _vis =>
            // Skip native/abstract definitions (body is Term.hole)
            if is_hole body then
                true
            else
                // `typ`, not `Term.hole` -- mirrors `check_def_with_
                // scope` (lang/module.mo): checking the body against its
                // full declared Pi-chain lets expected-type information
                // flow into the body (a match arm whose result is an
                // unannotated constructor call, a polymorphic call whose
                // typevar must come from the declared return type, ...),
                // which pure infer mode can't recover. Needs the
                // `elaborate_module_decls` step `typecheck_source` below
                // now does (the declared `typ` of a def with an implicit
                // binder is only Pi-chain-shaped AFTER that pass
                // forall-wraps it -- before, the typevar is a free var
                // the body check can't resolve).
                match type_check body typ scope empty_local_types (locals_with_def_typevars typ body scope empty_locals) {
                    ok _ => true,
                    err _ => false,
                }
    }

def typecheck_inductive (ind : Inductive) (scope : Scope) : Bool :=
    match ind {
        mk _name _params _typ constructors _attrs _vis =>
            typecheck_constructors constructors scope
    }

def typecheck_constructors (cons : List InductConstructor) (scope : Scope) : Bool := 
    match cons {
        List.empty => true,
        List.cons c rest =>
            let result : Bool := typecheck_constructor c scope in
            if result then
                typecheck_constructors rest scope
            else
                false
    }

def typecheck_constructor (c : InductConstructor) (scope : Scope) : Bool := 
    match c {
        mk _name params typ =>
            match type_check typ Term.hole scope empty_local_types empty_locals {
                ok _ => true,
                err _ => false
            }
    }

/// A dependency-free, self-contained source snippet -- unlike every
/// real examples/*.mo file below (each needs `io`/`init` module
/// loading this harness doesn't have, see the disabled tests' own
/// doc comments), this actually exercises `typecheck_module`/
/// `build_scope_from_decls` end-to-end via a real (if trivial) def.
/// Keeps this file's own test coverage non-empty now that every
/// examples/*.mo-backed test above is disabled for the same
/// documented reason. Deliberately uses `Type`/`Prop` (not `I64`/
/// `Bool`/...): `add_builtins` (lang/scope.mo) only ever registers
/// those two -- everything else (`I64`, `Bool`, ...) comes from
/// `init/prelude.mo`, which is exactly the real module loading this
/// bare, single-file harness doesn't do.
def typecheck_source (source : String) : Bool :=
    match parse_all_decls source {
        success _ decl_list =>
            let path := ModulePath.mp (List.cons (Identifier.id "synthetic") List.empty) in
            // Scope FIRST, from the raw (pre-elaboration) decls -- same
            // order as `elaborate_loaded_modules` (lang/module.mo), and
            // load-bearing for the signature-driven call path: the def
            // signatures `ScopeData.def_sigs` registers here are the
            // PRE-`elaborate_def_typs` ones, where an implicit binder's
            // type variable is still a free `sentinel` var (that's what
            // `solve_typevars` matches against).
            let sd := build_scope_from_decls path decl_list in
            let scope := make_scope path sd in
            // Then elaborate (forall-wrap implicit binders, resolve class
            // calls, ...): all-or-nothing `elaborate_module_decls`, same
            // as `check`'s own gate -- a source whose defs can't
            // elaborate fails the test, no silent partial elaboration.
            match elaborate_module_decls scope decl_list empty_locals {
                Result.err _ => false,
                Result.ok elaborated => typecheck_module path scope elaborated,
            },
        fail _ => false
    }

#[test]
def test_typecheck_module_self_contained_def : Bool :=
    typecheck_source "def id (x : Type) : Type := x"

#[test]
def test_typecheck_module_rejects_unbound_variable : Bool :=
    not (typecheck_source "def bad (x : Type) : Type := totally_undefined_name")

// --- signature-driven application typing (`ScopeData.def_sigs`,
// `try_type_check_def_call`, lang/typecheck/infer.mo) -- regression
// tests for the self-hosted checker's call-typing gaps, each pinned to
// a bug that cost real corpus defs (`ScopeDef.sig` being
// unconditionally `Term.hole` left ~70 defs in the compiler's own
// closure unable to type a plain call to a known def). ---

// A polymorphic def called with a CONCRETE argument: the signature's
// type variable must be solved from the argument's own inferred type
// (`V := Type` here) and substituted into the return type. Before the
// signature-driven path this failed with "expected V, found Type".
#[test]
def test_typecheck_sig_driven_poly_call : Bool :=
    typecheck_source "def ident {V : Type} (x : V) : V := x\ndef use_ident : Type := ident Type"

// A hole-typed argument must NOT poison the signature's concrete type
// names. `P.mk`'s call infers `Term.hole` (constructor sigs are hole,
// so the con-fallback path has nothing to trust yet in this
// expected-type-bottoms-out-at-hole position); `solve_typevars`
// used to record `P := Term.hole` from it anyway -- and since EVERY
// free var in a pre-elaboration `Def.typ` is a `sentinel` var (concrete
// type names included), that rewrote the monomorphic `Box P` return
// into `(Box _)`, failing the whole match with "type mismatch:
// expected (Box _), found (Box P)" (live in `lang/codegen/emit.mo`'s
// `ensure_main_params`; only the match-arm shape exposed it, the
// annotated top-level form masked it).
#[test]
def test_typecheck_hole_arg_does_not_poison_sig : Bool :=
    typecheck_source "type Box (A : Type) { be, bc (h : A) (t : Box A) }\ntype P { mk (n : Prop) (t : Prop) }\ndef cp (p : P) (ps : Box P) : Box P := Box.bc p ps\ndef eps : Box P := Box.be\ndef m5 (params : Box P) : Box P := match params { Box.be => cp (P.mk Prop Prop) eps, _ => params }"

// --- examples/ non-test files ---

// These examples depend on external modules (io, init, math, etc.) and require module loading.
//
// do_block.mo/indexed_monads.mo moved here (previously listed as live
// #[test]s, both actually passing): `typecheck_file`'s single-file
// `build_scope_from_decls` has no dependency loading at all (same gap
// already documented for factorial/hello/iteration/pattern_matching
// below) — do_block.mo needs `io`'s `IO`/`println`/`Monad.bind`,
// indexed_monads.mo needs `init/prelude.mo`'s `Bool`. Both files'
// LAST declarations (the ones needing these) simply weren't reached
// before `lang/parser/combinators.mo`'s UTF-8 byte-stepping fix
// (`utf8_char_width`): both files have an em dash in a comment ahead of
// their real content, which used to truncate `decls_try` to a handful
// of self-contained leading decl_list — so these two tests were previously
// "passing" only by accident of the very bug this fix corrects, never
// because `typecheck_file`'s dependency-free harness could actually
// resolve `IO`/`Bool`. Confirmed by bisection (parsed decl count went
// from a truncated few to the full 6/6 for both, with the newly-reached
// defs the ones that genuinely fail to typecheck for lack of `io`/
// `init/prelude.mo` in scope, not from any new parser regression).
// #[test]
// def test_typecheck_examples_do_block : Bool := typecheck_file "examples/do_block.mo" "do_block"
//
// #[test]
// def test_typecheck_examples_factorial : Bool := typecheck_file "examples/factorial.mo" "factorial"
//
// #[test]
// def test_typecheck_examples_hello : Bool := typecheck_file "examples/hello.mo" "hello"
//
// #[test]
// def test_typecheck_examples_indexed_monads : Bool := typecheck_file "examples/indexed_monads.mo" "indexed_monads"

// #[test]
// def test_typecheck_examples_iteration : Bool := typecheck_file "examples/iteration.mo" "iteration"
//
// #[test]
// def test_typecheck_examples_iteration_advanced : Bool := typecheck_file "examples/iteration_advanced.mo" "iteration_advanced"

// optics.mo moved here for the SAME reason as do_block.mo/indexed_monads.mo
// above (`use init.optics {...}` — needs real module loading this harness
// doesn't have) — reached only after a later parser fix (`match_case_arrow`
// now extends `ctx` with a match arm's own bound names before parsing its
// body, so `mk x y => x` no longer resolves `x` as an unbound free
// variable; previously this file's later declarations, including its own
// struct-pattern match, weren't reached at all). Bisection also surfaced a
// SECOND, independent gap while chasing this at the time: `lang/scope.mo`'s
// `build_scope_one_decl` had `Decl.struct_d _ => acc` — struct
// declarations were never added to scope at all, so matching on a struct's
// implicit `mk` constructor (`examples/structs.mo`'s own pattern, and
// `optics.mo`'s `get_name (p : Person) : String := match p { mk name _ _
// => name }`) couldn't validate against a registered constructor regardless
// of module loading. **That second gap has since been fixed**
// (`lang/scope.mo`'s `build_scope_struct`, registers a struct's name and a
// synthetic single-constructor `Inductive` the same way `build_scope_inductive`
// does) — struct matching genuinely self-hosted-typechecks now. This test
// stays disabled purely for the ORIGINAL, still-real reason: no module
// loading in this dependency-free harness.
// #[test]
// def test_typecheck_examples_optics : Bool := typecheck_file "examples/optics.mo" "optics"

// #[test]
// def test_typecheck_examples_pattern_matching : Bool := typecheck_file "examples/pattern_matching.mo" "pattern_matching"

// This test passed by the exact accident the comment above already
// anticipated: examples/structs.mo's `main`/`print_point` (needing
// `IO`/`println` from real module loading this dependency-free harness
// doesn't have) were never actually REACHED by the lenient parser,
// because the file's own struct-literal/struct-update syntax
// (`{ x := 1, y := 2 }`, `{ p1 with x := 10 }`) was unparseable by this
// self-hosted parser until struct-literal support landed. Now that both
// parse, the whole file is reached and this test fails honestly on the
// pre-existing "no module loading" gap, not a struct-literal bug --
// same category of gap `test_typecheck_examples_optics` above already
// documents. Disabled rather than "fixed" for the same reason: adding
// real dependency loading to this harness is a separate, larger piece
// of work, not a struct-literal one.
// #[test]
// def test_typecheck_examples_structs : Bool := typecheck_file "examples/structs.mo" "structs"

// TODO this can not be tested without full mote support
// #[test]
// def test_typecheck_examples_test_mote : Bool := typecheck_file "examples/test_mote.mo" "test_mote"

// Note: Some examples require module loading (io, init, math, etc.) and are skipped for now.
