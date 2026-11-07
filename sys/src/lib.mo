/// The re-export hub for the OS floor (bare `sys` resolves here).
///
/// `std` re-exports these names, so ordinary code keeps spelling
/// `IO.read_file`, `Proc.spawn` and friends; only the declarations live
/// here. The modules arrive with the floor itself: `raw` (the
/// flag-multiplexed natives), `errno`, `signal`, then `fd`, `fs`, `env`,
/// `proc`, `net`, `time`, `watch` and `term`.
