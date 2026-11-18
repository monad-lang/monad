/// Stack-safe walks: same answers as the ordinary helpers, on lists far
/// longer than one chunk.

use lib::seq {Seq.fold, Seq.reverse, Seq.map, Seq.filter, Seq.length, Seq.any, Seq.find, Seq.append, Seq.lines}

#[terminating]
def upto (n : I64) (acc : List I64) : List I64 := if n <= 0 then acc else upto (n - 1) (List.cons n acc)

def big : List I64 := upto 5000 List.empty

#[test]
def test_fold_sums_across_chunks : Bool := Seq.fold (fn (a : I64) (x : I64) => a + x) 0 big == 12502500

#[test]
def test_map_filter_keep_order : Bool :=
    match Seq.filter (fn (x : I64) => x > 4998) (Seq.map (fn (x : I64) => x) big) {
        List.cons a rest => a == 4999 && Seq.length rest == 1,
        List.empty => false,
    }

#[test]
def test_reverse_and_length : Bool :=
    Seq.length big == 5000 && (match Seq.reverse big { List.cons a _ => a == 5000, List.empty => false })

#[test]
def test_any_find_append : Bool :=
    Seq.any (fn (x : I64) => x == 4321) big
        && (match Seq.find (fn (x : I64) => x > 4000) big { Option.some v => v == 4001, Option.none => false })
        && Seq.length (Seq.append big big) == 10000

#[test]
def test_lines : Bool :=
    let ls : List String := Seq.lines "a\nbb\n\nc" in
    Seq.length ls == 4 && (match ls { List.cons a _ => String.beq a "a", List.empty => false })
        && Seq.length (Seq.lines "") == 1
