/// The re-export hub for the OS floor (bare `sys` resolves here).
///
/// `std` re-exports these names, so ordinary code keeps spelling
/// `IO.read_file`, `Proc.spawn` and friends; only the declarations live
/// here. Without these lines `use sys {Sys.pid}` does not resolve at all --
/// the hub has to name every module whose names a caller may spell, the way
/// `init/lib.mo` and `std/lib.mo` do.
///
/// `raw` is deliberately NOT re-exported: its functions are package-private
/// and `Dir` is the opaque stream handle `Sys.list_dir` owns internally, so
/// nothing outside this mote may reach one.
///
/// The floor is still small. `fd`, `fs`, `env`, `proc`, `net`, `time`,
/// `watch` and `term` are the remaining milestone items in
/// `plans/library-ideas/system.md` (M1's native move); until they land, the
/// corresponding natives still live in `std`.
pub use lib::errno {*}
pub use lib::signal {*}
pub use lib::text {*}
pub use lib::sys {*}
