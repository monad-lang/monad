// pty / spike -- a throwaway `monad build` target for the Phase 0 IR audit.
//
// Build it with `monad build motes/pty/src/spike/main.mo --no-cache`, then
// inspect the emitted `.ll`: `fork_exec`, `exec_die` and the
// `monad_extern_{forkpty,execl8,exit_now}` wrappers must contain no
// `monad_alloc`/`alloc_constructor`/`apply_closure`/`monad_io_pure`/
// `monad_io_bind` (the child path may not allocate after `forkpty`).
//
// Not imported by the mote; `monad test` reports it as SKIP (no #[test]).
use lib::spawn {SpawnConfig, Pty}
use std::io {IO.println}

def run (m : Pty) : IO Unit := do {
    let out <- Pty.read_all m 3000;
    IO.println out;
    Pty.finish m
}

def main (args : List String) : IO Unit := do {
    let cfg : SpawnConfig := {
        bin := "/bin/sh",
        args := List.cons "-c" (List.cons "printf hi" List.empty),
        rows := 24,
        cols := 80,
        env := List.empty,
        cwd := Option.none
    };
    let r <- Pty.spawn cfg;
    match r {
        Result.err e => IO.println e,
        Result.ok m => run m
    }
}
