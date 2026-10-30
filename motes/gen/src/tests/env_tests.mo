// `Env` resolves a name to a de Bruijn index; the printed term shows the
// name either way, so these tests pin the index itself.

use gen::env {Env, Gen.lam, Gen.ref}
use lang::construct {apps, global, u32}
use lang::pretty {show_term}

#[test]
def test_free_name_is_a_global_reference : Bool :=
    String.beq (show_term (Gen.ref Env.empty "U32.lt")) "U32.lt"

#[test]
def test_innermost_binder_is_index_zero : Bool :=
    let env := Env.bind (Env.bind Env.empty "outer") "inner" in
    match Env.index env "inner" {
        Option.some idx => I64.beq idx 0,
        Option.none => false,
    }

#[test]
def test_outer_binder_is_one_further_out : Bool :=
    let env := Env.bind (Env.bind Env.empty "outer") "inner" in
    match Env.index env "outer" {
        Option.some idx => I64.beq idx 1,
        Option.none => false,
    }

#[test]
def test_unbound_name_has_no_index : Bool :=
    match Env.index Env.empty "cp" {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_shadowing_prefers_the_innermost : Bool :=
    let env := Env.bind (Env.bind Env.empty "cp") "cp" in
    match Env.index env "cp" {
        Option.some idx => I64.beq idx 0,
        Option.none => false,
    }

#[test]
def test_lam_body_sees_its_own_binder : Bool :=
    let t := Gen.lam Env.empty "x" (global "U32") (fn (body_env : Env) => Gen.ref body_env "x") in
    String.beq (show_term t) "(fn (x : U32) => x)"

#[test]
def test_lam_body_still_sees_outer_globals : Bool :=
    let t := Gen.lam Env.empty "x" (global "U32")
        (fn (body_env : Env) => apps (global "U32.lt") [Gen.ref body_env "x", u32 10]) in
    String.beq (show_term t) "(fn (x : U32) => (U32.lt x 10u32))"
