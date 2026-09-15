// `lib` names this file's own mote, from a subdirectory: root-relative
// within the mote, never relative to this file's directory.
use lib::helper {helper_answer}

#[test]
def test_lib_alias_reaches_the_mote_root : Bool := I64.beq helper_answer 42
