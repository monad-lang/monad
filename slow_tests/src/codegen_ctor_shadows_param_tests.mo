/// Regression tests for a constructor stealing a call whose head is a LOCAL
/// of the same bare name (`try_compile_constructor_app_db`,
/// `lang/src/codegen/emit.mo`).
///
/// That function already bails out when the bare name is ALSO a real
/// top-level def -- a function/constructor collision -- but it never looked
/// at `c`'s locals, so a parameter or match-arm binder lost to any
/// constructor of the same name anywhere in the whole-program namespace.
/// `compile_call_head`, the fallback it bails out to, checks locals first;
/// this is that check, one level up.
///
/// The blast radius is why these are e2e and not unit tests. `init/src/io.mo`
/// spells `Monad IO`.bind as `match a { io a => f a }`, so a single arity-1
/// constructor named `f` in ANY loaded module compiled `f a` to
/// `alloc_constructor` + `set_field`: bind returned its payload re-wrapped
/// and never invoked the continuation. Every `do` block in the program then
/// silently did nothing -- no output, no crash, and an exit code that varied
/// run to run because `main` unwrapped a field of a constructor that was
/// never the right one. Found on `motes/tui`'s `Key.f (n : I64)`, where it
/// took down all four of that mote's test files while leaving the Rust host
/// completely silent.
open IO {println}
use lang::codegen::test::e2e_harness {compile_source_run_expect}

/// A parameter named `f` applied as a function, alongside an arity-1
/// constructor `f`. The direct unit: with the bug `f x` allocates a
/// `Probe.f` object and `apply1` returns it, so the exit code is a pointer
/// rather than 42.
#[test]
def test_local_param_shadows_same_named_ctor : IO Bool :=
    let source := r#"type Probe {
    f (n : I64),
    zero_key
}
def apply1 (f : I64 -> I64) (x : I64) : I64 := f x
def bump (y : I64) : I64 := y + 1
def main (args : List String) : IO I64 := do {
    let r := apply1 bump 41;
    return r
}
"# in
    compile_source_run_expect source "test_local_param_shadows_same_named_ctor" 42

/// The real-world shape: the program never names `f` itself, it only
/// declares the constructor. A `do` block's own desugaring reaches
/// `init/src/io.mo`'s bind, whose continuation parameter IS named `f`, so
/// with the bug the `return 7` after the first statement never runs.
#[test]
def test_ctor_named_f_does_not_break_do_blocks : IO Bool :=
    let source := r#"open IO {println}
type Probe {
    f (n : I64),
    zero_key
}
def main (args : List String) : IO I64 := do {
    println "probe";
    return 7
}
"# in
    compile_source_run_expect source "test_ctor_named_f_does_not_break_do_blocks" 7

/// A match-arm binder, not a parameter -- the other kind of local, and the
/// one `Monad IO`.bind's own `io a => f a` arm actually binds through.
#[test]
def test_match_arm_binder_shadows_same_named_ctor : IO Bool :=
    let source := r#"type Probe {
    f (n : I64),
    zero_key
}
type Boxed {
    wrap (g : I64 -> I64)
}
def bump (y : I64) : I64 := y + 1
def run_boxed (b : Boxed) (x : I64) : I64 :=
    match b {
        wrap f => f x
    }
def main (args : List String) : IO I64 := do {
    let r := run_boxed (Boxed.wrap bump) 41;
    return r
}
"# in
    compile_source_run_expect source "test_match_arm_binder_shadows_same_named_ctor" 42
