/// Full case folding of strings (the generated fold tree).
use unicode::casefold {Unicode.case_fold}

#[test]
def test_case_fold : Bool :=
    String.beq (Unicode.case_fold "Straße") "strasse"
        && String.beq (Unicode.case_fold "ΑΒΓ") "αβγ"
        && String.beq (Unicode.case_fold "abc") "abc"
        && String.beq (Unicode.case_fold "ẞ") "ss"
