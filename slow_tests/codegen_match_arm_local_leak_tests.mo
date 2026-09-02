/// Regression test for match-arm pattern bindings leaking into the
/// SIBLING arms compiled after them.
///
/// `build_match_case_block` (lang/codegen/emit.mo) calls
/// `bind_match_fields` to push one codegen local per pattern variable,
/// then handed the resulting ctx -- bindings still on it -- straight to
/// the next arm. So a later arm referencing a name an earlier arm
/// happened to bind resolved to the EARLIER arm's SSA temp instead of
/// its own binding. Field access is what makes the collision ordinary
/// rather than exotic: `result.label` desugars to a match that binds a
/// local named `label`, which is a perfectly normal name for the
/// enclosing def's own parameter.
///
/// The wrong temp is defined in a basic block the later arm is not
/// dominated by, so the module does not even verify: `llc` rejects it
/// with "Instruction does not dominate all uses!". That is what the
/// `lang/main.mo` self-compile hit in `resolve_branch_merge_info`,
/// whose `Option.none` arm built its result out of the `Option.some`
/// arm's `result.label`/`result.blocks` temps instead of its own
/// `label`/`blocks` parameters.
///
/// The reference interpreter is unaffected (it has no shared ctx to
/// leak), and `check` says nothing -- only compiling and running finds
/// it, hence the full compile/link/execute round trip here.
use io {IO}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// `resolve_branch_merge_info`'s own shape, reduced: the `some` arm
/// reads two fields off its bound value (binding locals `label` and
/// `blocks`), and the `none` arm builds its result from the enclosing
/// def's OWN same-named parameters. Taking the `none` arm must use the
/// parameters.
///
/// Exit code 7 means the `none` arm saw its own `blocks` parameter; a
/// failure to even build the binary is the original bug (llc rejects
/// the module), and any other exit code means it read the wrong value.
#[test]
def test_match_arm_bindings_do_not_leak_into_sibling_arm : IO Bool :=
    let source := r#"use io {IO}
struct Info { reaches : Bool, label : String, blocks : I64 }
def find (b : Bool) : Option Info :=
    if b then
        let i : Info := { reaches := true, label := "found", blocks := 99 } in
        Option.some i
    else
        Option.none
def resolve (b : Bool) (label : String) (blocks : I64) : Info :=
    match find b {
        Option.some result => { reaches := true, label := result.label, blocks := result.blocks },
        Option.none => { reaches := false, label := label, blocks := blocks },
    }
def main (args : List String) : IO I64 := do {
    let r : Info := resolve false "param_label" 7;
    return (if String.beq r.label "param_label" then r.blocks else 1)
}
"# in
    compile_source_run_expect source "match_arm_local_leak" 7

/// The same leak with plain positional patterns rather than field
/// access, and with the collision running the other way (the LATER arm
/// binds a name the EARLIER arm used from an outer scope) -- confirms
/// the fix restores the enclosing scope rather than just happening to
/// order these two arms favorably.
#[test]
def test_match_arm_bindings_restore_outer_scope : IO Bool :=
    let source := r#"use io {IO}
type Two { one (v : I64), two (v : I64) }
def pick (t : Two) (v : I64) : I64 :=
    match t {
        Two.one v => v + 100,
        Two.two _ => v,
    }
def main (args : List String) : IO I64 := do {
    return (pick (Two.two 5) 7)
}
"# in
    compile_source_run_expect source "match_arm_outer_scope" 7
