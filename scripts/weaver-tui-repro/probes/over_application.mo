// A TWO-arg def called with THREE arguments: checks clean on both
// hosts and miscompiles/crashes at runtime. Found during the weaver
// UI-repair pass (a test helper handed `Model.append_block m [line]
// recurse` as three args; the compiled binary segfaulted). Both hosts'
// checkers should reject over-application.
def two (a : I64) (b : I64) : I64 := a + b

#[test]
def test_overapplied : Bool :=
    let r := two 1 2 3 in
    r == 6