/// A record update in ARGUMENT position (`f { s with field := v }`), the
/// shape `plans/implementations/record-update-argument-checker-crash.md`
/// records as a self-hosted SIGSEGV. The minimal form no longer crashes on
/// current HEAD; this row keeps it compiled and run so a regression is
/// caught. A reduced repro of the original deep mutually-recursive shape is
/// still wanted in that plan.

struct St { seen : List String, n : I64 }

def use_st (s : St) : I64 := s.n

#[partial]
def f (s : St) (x : String) : I64 :=
    use_st { s with seen := List.cons x s.seen }

#[test]
def test_record_update_in_argument_position : Bool :=
    let a : St := { seen := List.empty, n := 7 } in
    let b : St := { seen := List.empty, n := 0 } in
    I64.beq (f a "x") 7 && I64.beq (f b "x") 0
