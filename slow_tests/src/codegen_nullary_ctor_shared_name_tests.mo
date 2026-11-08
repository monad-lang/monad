/// A nullary constructor whose bare name another type claims WITH fields
/// (`Tick.exited` beside `Status.exited (code)`) must match its own arm.
///
/// The whole-program pass names a type with its module (`repro::Tick`), but
/// a value-position reference keeps the source spelling `Tick.exited`. The
/// constructor maps were keyed only by the module-qualified owner, so the
/// lookup fell to the bare name: `Status.exited`'s arity 1 and an ambiguous
/// tag. `Tick.exited` compiled as a one-field constructor CLOSURE and every
/// `match` on it took `_`. Found twice in weaver: `ShellTick.exited`
/// against `ProcStatus.exited`, then `ShellTick.done` against tui's
/// `ModalNext.done`, which reported finished shell commands as killed.
use codegen::test::e2e_harness {compile_source_run_expect}

#[test]
def test_nullary_ctor_beside_same_named_field_ctor_matches_its_arm : IO Bool :=
    let source := r#"type Status { running, exited (code : I64), killed }
type Tick { waiting, exited, interrupted, flooded }
def code (t : Tick) : I64 :=
    match t {
        Tick.exited => 40,
        Tick.interrupted => 1,
        _ => 0,
    }
def main (args : List String) : IO I64 := do {
    let a := code Tick.exited;
    let b := code Tick.flooded;
    let s := match Status.exited 2 { Status.exited n => n, _ => 0 };
    return (a + b + s)
}
"# in
    compile_source_run_expect source "test_nullary_ctor_beside_same_named_field_ctor_matches_its_arm" 42
