/// Range tables by name, the range algebra and the simple fold orbits.
use unicode::lookup {
    Unicode.decode_ranges, Unicode.union_ranges, Unicode.normalize_name, Unicode.gc_ranges,
    Unicode.script_ranges, Unicode.white_space_ranges, Unicode.digit_ranges,
    Unicode.simple_fold_entries, Unicode.simple_fold_orbit,
}
use std::list {List.any}

def contains (rs : List (Pair I64 I64)) (cp : I64) : Bool :=
    List.any (fn (r : Pair I64 I64) => Bool.not (I64.lt cp r.first) && Bool.not (I64.lt r.second cp)) rs

def has (o : Option (List (Pair I64 I64))) (cp : I64) : Bool :=
    match o {
        Option.some rs => contains rs cp,
        Option.none => false,
    }

def ints_eq (a : List I64) (b : List I64) : Bool :=
    match a {
        List.empty => List.is_empty b,
        List.cons x xs =>
            match b {
                List.empty => false,
                List.cons y ys => I64.beq x y && ints_eq xs ys,
            },
    }

def is_none {A : Type} (o : Option A) : Bool :=
    match o {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_decode : Bool :=
    match Unicode.decode_ranges "00004100005A000061000061" {
        List.cons a rest =>
            I64.beq a.first 65 && I64.beq a.second 90 && I64.beq (List.length rest) 1,
        List.empty => false,
    }

#[test]
def test_union_coalesces : Bool :=
    I64.beq (List.length (Unicode.union_ranges [Pair.pair 1 3, Pair.pair 10 12] [Pair.pair 4 5, Pair.pair 11 20])) 2

#[test]
def test_normalize_name : Bool :=
    String.beq (Unicode.normalize_name "Uppercase_Letter") "uppercaseletter"
        && String.beq (Unicode.normalize_name "old italic") "olditalic"

#[test]
def test_gc_names : Bool :=
    has (Unicode.gc_ranges "Lu") 65 && Bool.not (has (Unicode.gc_ranges "Lu") 97)
        && has (Unicode.gc_ranges "Uppercase_Letter") 192
        && has (Unicode.gc_ranges "L") 26085 && has (Unicode.gc_ranges "letter") 97
        && has (Unicode.gc_ranges "N") 178 && has (Unicode.gc_ranges "punct") 33
        && has (Unicode.gc_ranges "Cn") 888 && Bool.not (has (Unicode.gc_ranges "Cn") 65)
        && has (Unicode.gc_ranges "C") 0
        && is_none (Unicode.gc_ranges "Bogus")

#[test]
def test_scripts : Bool :=
    has (Unicode.script_ranges "Greek") 945 && Bool.not (has (Unicode.script_ranges "Greek") 65)
        && has (Unicode.script_ranges "latin") 65
        && has (Unicode.script_ranges "Han") 26085
        && has (Unicode.script_ranges "Cyrillic") 1078
        && has (Unicode.script_ranges "Old_Italic") 66304
        && is_none (Unicode.script_ranges "Klingon")

#[test]
def test_perl_sets : Bool :=
    contains Unicode.white_space_ranges 32 && contains Unicode.white_space_ranges 12288
        && contains Unicode.digit_ranges 1632 && Bool.not (contains Unicode.digit_ranges 65)

#[test]
def test_simple_fold_orbits : Bool :=
    ints_eq (Unicode.simple_fold_orbit 107) [75, 8490]
        && ints_eq (Unicode.simple_fold_orbit 75) [107, 8490]
        && ints_eq (Unicode.simple_fold_orbit 963) [931, 962]
        && List.is_empty (Unicode.simple_fold_orbit 49)

#[test]
def test_simple_fold_entries_ascend : Bool :=
    match Unicode.simple_fold_entries {
        List.cons e _ => I64.beq e.first 65,
        List.empty => false,
    }
