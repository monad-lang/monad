/// `IO.iterate` tests: it stops on `none`, runs each step's effect once
/// and in order, and a long loop needs no stack per iteration (run these
/// under a small `MONAD_STACK_BYTES` to see the difference from a
/// recursive do-loop).

use std::ref {Ref, Ref.new, Ref.get, Ref.add_i64, Ref.modify}

def count_to (limit : I64) (r : Ref I64) (i : I64) : IO (Option I64) := do {
    let _ <- Ref.add_i64 r 1;
    return (if i + 1 < limit then Option.some (i + 1) else Option.none)
}

#[test]
def test_iterate_stops_on_none : IO Bool := do {
    let r <- Ref.new 0;
    IO.iterate 0 (count_to 5 r);
    let n <- Ref.get r;
    return (n == 5)
}

#[test]
def test_iterate_runs_the_first_step_even_when_it_stops : IO Bool := do {
    let r <- Ref.new 0;
    IO.iterate 0 (count_to 0 r);
    let n <- Ref.get r;
    return (n == 1)
}

/// Each step appends its index as a decimal digit: in-order, exactly-once
/// effects read back as 1234.
def record (r : Ref I64) (i : I64) : IO (Option I64) := do {
    let _ <- Ref.modify r (fn (acc : I64) => acc * 10 + i);
    return (if i < 4 then Option.some (i + 1) else Option.none)
}

#[test]
def test_iterate_runs_steps_in_order : IO Bool := do {
    let r <- Ref.new 0;
    IO.iterate 1 (record r);
    let n <- Ref.get r;
    return (n == 1234)
}

/// 200k iterations: a recursive do-loop nests a native frame per
/// iteration and overflows a 2 MiB stack long before this.
#[test]
def test_iterate_long_loop : IO Bool := do {
    let r <- Ref.new 0;
    IO.iterate 0 (count_to 200000 r);
    let n <- Ref.get r;
    return (n == 200000)
}
