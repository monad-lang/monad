/// The mote's root re-exports are enough to use it.
use regex {Regex, Regex.new, Regex.is_match}

#[test]
def test_lib_reexports : Bool :=
    match Regex.new "a+b" {
        Result.ok r => Regex.is_match r "xaab",
        Result.err _ => false,
    }
