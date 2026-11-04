/// Plain recursive IO loops. The IO do-bind fusion
/// (`lang/src/codegen/emit.mo`'s `try_compile_io_bind_db`) compiles
/// `let x <- step ...` to straight-line code, which leaves the recursive
/// call in tail position where `tco.mo` turns it into a loop -- so an
/// ordinary `drive` helper is the supported way to write an IO loop, and
/// `IO.iterate` no longer exists.
///
/// These are the behavioural cases; the constant-stack proof (1,000,000
/// iterations under a 2 MiB stack) is
/// `slow_tests/src/heapless_io_loop_tests.mo`.

use std::ref {Ref, Ref.new, Ref.get, Ref.add_i64, Ref.modify}

def count_to (limit : I64) (r : Ref I64) (i : I64) : IO (Option I64) := do {
    let _ <- Ref.add_i64 r 1;
    return (if i + 1 < limit then Option.some (i + 1) else Option.none)
}

/// Run `step` from `s` until it answers `none`.
#[terminating]
def drive (step : I64 -> IO (Option I64)) (s : I64) : IO Unit := do {
    let next <- step s;
    match next {
        Option.none => IO.pure unit,
        Option.some s2 => drive step s2,
    }
}

#[test]
def test_loop_stops_on_none : IO Bool := do {
    let r <- Ref.new 0;
    drive (count_to 5 r) 0;
    let n <- Ref.get r;
    return (n == 5)
}

#[test]
def test_loop_runs_the_first_step_even_when_it_stops : IO Bool := do {
    let r <- Ref.new 0;
    drive (count_to 0 r) 0;
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
def test_loop_runs_steps_in_order : IO Bool := do {
    let r <- Ref.new 0;
    drive (record r) 1;
    let n <- Ref.get r;
    return (n == 1234)
}

/// 200k iterations. Without the fusion this nests a native frame per
/// iteration; it still finishes here because the loop is a back-edge.
#[test]
def test_long_loop : IO Bool := do {
    let r <- Ref.new 0;
    drive (count_to 200000 r) 0;
    let n <- Ref.get r;
    return (n == 200000)
}
