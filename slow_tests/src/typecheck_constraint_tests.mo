/// Call-site enforcement of a def's declared class constraints
/// (`lang/src/typecheck/infer.mo`'s `missing_constraint_error`), end to end
/// through the real load + check path.
///
/// `lang/src/module.mo`'s in-process tests cover the APPLIED shape
/// (`use_foo p`). The BARE shape cannot be covered there: that harness builds
/// its scope from the RAW parsed decls, where a bare global reference is
/// `unknown variable` instead of being reified from its signature, so the
/// check never runs. A bare reference is a partial application, and it used to
/// compile and run with the dictionary left out, so it needs a fixture that
/// goes through `elaborate_loaded_modules` exactly as `monad check` does.
use lang::module {check_module_with_scope, elaborate_loaded_modules}
use lib::typecheck_harness {empty_local_scope}
use std::list {List.length}
use std::test {Test.write_fixture}

#[partial]
def diags_contain (needle : String) (diags : List String) : Bool :=
    match diags {
        List.empty => false,
        List.cons d rest => if String.contains d needle then true else diags_contain needle rest,
    }

/// Write `source` to a scratch fixture and return the diagnostics the real
/// check path reports for it.
#[partial]
def check_source_diags (source : String) (fixture_name : String) : IO (List String) := do {
    let path : String := String.concat "/tmp/monad_constraint_" (String.concat fixture_name ".mo");
    let _written <- Test.write_fixture (Path.path path) source;
    let loaded <- elaborate_loaded_modules path false false;
    match loaded {
        Result.err e => do {
            return (List.cons (String.concat "LOAD FAILED: " e) List.empty)
        },
        // Destructured, not projected twice: two `em.field` reads of an
        // affine record would be an over-use.
        Result.ok em => match em {
            { scope, target_decls, .. } =>
                check_module_with_scope scope target_decls empty_local_scope (Option.some path) false,
        },
    }
}

/// `use_foo` referenced BARE with no `Foo Pt` in scope: a partial
/// application whose dictionary is decided and absent.
#[test]
def test_a_bare_reference_without_an_instance_is_rejected : IO Bool := do {
    let src : String :=
        "class Foo A { def foo (x : A) : A := x }\n"
        ++ "struct Pt { x : I64 }\n"
        ++ "def use_foo [Foo S] (s : S) : S := Foo.foo s\n"
        ++ "def caller (p : Pt) : Pt := let f : Pt -> Pt := use_foo in f p\n";
    let diags <- check_source_diags src "bare_missing";
    return (diags_contain "no instance of `Foo` for `Pt`" diags)
}

/// The same shape with the instance present: accepted, and no diagnostic at
/// all -- the guard for the check firing on bare references in general.
#[test]
def test_a_bare_reference_with_the_instance_is_accepted : IO Bool := do {
    let src : String :=
        "class Foo A { def foo (x : A) : A := x }\n"
        ++ "struct Pt { x : I64 }\n"
        ++ "instance Foo Pt { def foo (p : Pt) : Pt := p }\n"
        ++ "def use_foo [Foo S] (s : S) : S := Foo.foo s\n"
        ++ "def caller (p : Pt) : Pt := let f : Pt -> Pt := use_foo in f p\n";
    let diags <- check_source_diags src "bare_present";
    return (I64.beq (List.length diags) 0)
}

/// A class-METHOD call is the same obligation at the same stage. The carrier
/// comes from the call's own first argument (`type_check_app` checks the
/// argument before the callee), so a miss is a decision, not "cannot tell" --
/// it used to fall back to the method's abstract signature and fail only in
/// codegen, as `no instance found for ...`.
#[test]
def test_a_class_method_call_without_an_instance_is_rejected : IO Bool := do {
    let src : String :=
        "class Foo A { def foo (x : A) : A := x }\n"
        ++ "def caller (x : I64) : I64 := Foo.foo x\n";
    let diags <- check_source_diags src "method_missing";
    return (diags_contain "no instance of `Foo` for `I64`" diags)
}

/// ...and accepted once the instance exists.
#[test]
def test_a_class_method_call_with_the_instance_is_accepted : IO Bool := do {
    let src : String :=
        "class Foo A { def foo (x : A) : A := x }\n"
        ++ "instance Foo I64 { def foo (x : I64) : I64 := x + 1 }\n"
        ++ "def caller (x : I64) : I64 := Foo.foo x\n";
    let diags <- check_source_diags src "method_present";
    return (I64.beq (List.length diags) 0)
}
