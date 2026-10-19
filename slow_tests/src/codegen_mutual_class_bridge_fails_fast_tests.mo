/// Regression test for `constraints_resolve_without_cycle`
/// (`lang/src/scope.mo`): two classes that bridge to each other
/// (`instance [Bar A A A] Foo A` / `instance [Foo A] Bar A A A`, mirroring
/// `init/src/prelude.mo`'s real `Add`/`HAdd`) and NO concrete instance of
/// either anywhere must fail the compile with a clean error naming the
/// missing instance, not silently resolve to the mutual bridge and
/// compile two functions that call each other unconditionally.
///
/// Before `constraints_resolve_without_cycle` landed, this compiled --
/// confirmed on the real `Add`/`HAdd` shape via `gdb bt` on the generated
/// driver: `Add_A_add -> ... -> HAdd_A_A_A_add -> Add_A_add -> ...`,
/// repeating until the stack overflowed. The checker-level self-match
/// guard (`resolve_class_method_d4`'s "Refuse the self-match") only ever
/// caught a constraint resolving directly back to the SAME instance; it
/// never saw a cycle through a DIFFERENT class's instance.
///
/// The unresolved carrier has to come from a HOF argument whose type is
/// only known from a LATER sibling argument (the same inference-order gap
/// `app_arg_expected_type_from_callee`'s own doc comment records for
/// `Foldable.foldr`) -- an annotated lambda parameter would pin the
/// carrier before `Foo.foo`/`Bar.bar` are ever asked to resolve anything,
/// and the bug would never be reached.
use std::test {Test.write_fixture}
use std::process {exec_cmd, process_id}
use lang::module {LoadedModules, load_file_modules}
use lang::codegen::emit {compile_loaded_modules_to_ir}

#[test]
def test_mutual_class_bridge_with_no_concrete_instance_fails_fast : IO Bool := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/mutual_class_bridge.mo";
    let source := r#"class Foo A { def foo : A -> A -> A }
class Bar A B C { def bar : A -> B -> C }
instance [Bar A A A] Foo A { def foo (a b : A) : A := Bar.bar a b }
instance [Foo A] Bar A A A { def bar (a b : A) : A := Foo.foo a b }
class Pump (W : Type -> Type) {
    def unwrap (w : W A) : A
    def pump (f : W A -> B) (w : W A) : W B
}
type Box A { box (a : A) }
instance Pump Box {
    def unwrap (b : Box A) : A := match b { box a => a }
    def pump (f : Box A -> B) (b : Box A) : Box B := match b { box a => Box.box (f b) }
}
def never_concrete : Box I64 :=
    Pump.pump (fn a => Foo.foo (Pump.unwrap a) (Pump.unwrap a)) (Box.box 1)
def main (args : List String) : IO I64 := do {
    let _ := never_concrete;
    return 0
}
"#;
    exec_cmd "mkdir" ["-p", output_dir];
    let _w <- Test.write_fixture (Path.path src_path) source;

    let loaded_result <- load_file_modules src_path false;
    match loaded_result {
        Result.err e => do {
            IO.println ("test_mutual_class_bridge_with_no_concrete_instance_fails_fast: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err msg => do {
                    let names_bar := String.contains msg "Bar";
                    if names_bar then return true
                    else do {
                        IO.println ("test_mutual_class_bridge_with_no_concrete_instance_fails_fast: error message missing the Bar instance name: " ++ msg);
                        return false
                    }
                },
                Result.ok _ => do {
                    IO.println "test_mutual_class_bridge_with_no_concrete_instance_fails_fast: expected Result.err (no concrete Foo/Bar instance exists anywhere), got Result.ok";
                    return false
                },
            }
        },
    }
}
