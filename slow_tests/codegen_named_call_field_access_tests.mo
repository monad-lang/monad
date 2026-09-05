/// Regression tests for a field access used as a NAMED-call argument
/// compiling to field index 0, whatever field was actually named.
///
/// `type_check_named_call_def_target` (`lang/typecheck/infer.mo`)
/// type-checked each argument and then threw the result away, folding
/// the RAW argument terms back into the application. Checking an
/// argument is also what RESOLVES it -- a field access `f.d` only
/// becomes a projection at its real field index during that check -- so
/// codegen received an unresolved access and compiled every one of them
/// to `monad_get_field(obj, 0)`. The constructor-target path in the
/// same function had always used its own elaborated args; only the
/// ordinary-def target discarded them.
///
/// This was live in `lang/main.mo`'s own
/// `compile_file_codegen { ..., preloaded := Option.some em.loaded }`:
/// `em.loaded` is `ElaboratedModules`' FOURTH field compiled as its
/// first, so codegen was handed a `Scope` where a `LoadedModules`
/// belonged and dereferenced its way into a `HashMap` -- a SIGSEGV
/// before `compile` printed a single line. It reproduced identically in
/// v30e, so it predates module-qualified symbols; it had simply never
/// been reachable, because no self-compiled binary had ever got as far
/// as running `compile`.
///
/// These compile through the self-hosted backend and RUN the binary, so
/// a regression shows up as a wrong exit code, not just an IR-shape
/// mismatch -- and the two calls are deliberately compared against each
/// other, since a value read from the wrong field is still a perfectly
/// well-formed integer.
use io {IO}
open IO {println}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// The minimal shape: the SAME field access, once as an ordinary
/// positional argument and once as a named one. Both must read field
/// `d`. Before the fix the named call read field `a`, giving 41.
#[test]
def test_named_call_arg_reads_the_named_field : IO Bool :=
    let source := r#"use io {IO}
struct Four {
    a : I64,
    b : I64,
    c : I64,
    d : I64,
}
def take_two (x : I64) (y : I64) : I64 := I64.add x y
def plain_call (f : Four) : I64 := take_two f.d 0
def named_call (f : Four) : I64 := take_two { x := f.d, y := 0 }
def main (args : List String) : IO I64 := do {
    let f : Four := { a := 1, b := 2, c := 3, d := 40 };
    return (I64.add (plain_call f) (named_call f))
}
"# in
    compile_source_run_expect source "test_named_call_arg_reads_the_named_field" 80

/// Every field, in one named call, with weights that make any swapped
/// or duplicated read produce a different total: all-field-0 gives 15,
/// reading them reversed gives 26, and the correct answer is 49. Kept
/// under 256 deliberately -- the harness compares a process EXIT CODE,
/// which the OS truncates to 8 bits, so a larger total would wrap and
/// could collide with a wrong answer.
#[test]
def test_named_call_args_keep_their_own_fields : IO Bool :=
    let source := r#"use io {IO}
struct Four {
    a : I64,
    b : I64,
    c : I64,
    d : I64,
}
def weigh (p : I64) (q : I64) (r : I64) (s : I64) : I64 :=
    I64.add (I64.add p (I64.mul q 2)) (I64.add (I64.mul r 4) (I64.mul s 8))
def main (args : List String) : IO I64 := do {
    let f : Four := { a := 1, b := 2, c := 3, d := 4 };
    return (weigh { p := f.a, q := f.b, r := f.c, s := f.d })
}
"# in
    compile_source_run_expect source "test_named_call_args_keep_their_own_fields" 49

/// Named arguments given OUT of declared order still bind by name --
/// the elaborated terms are folded in the callee's parameter order, so
/// a fold over the literal's own order would silently transpose them.
#[test]
def test_named_call_out_of_order_fields_bind_by_name : IO Bool :=
    let source := r#"use io {IO}
struct Two {
    lo : I64,
    hi : I64,
}
def sub_them (x : I64) (y : I64) : I64 := I64.sub x y
def main (args : List String) : IO I64 := do {
    let t : Two := { lo := 5, hi := 105 };
    return (sub_them { y := t.lo, x := t.hi })
}
"# in
    compile_source_run_expect source "test_named_call_out_of_order_fields_bind_by_name" 100
