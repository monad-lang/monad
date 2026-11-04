/// Where a session runs: the working directory and the repository it is in.
/// `--continue` and the `/resume` picker key on `repo`, so a session started
/// in one checkout (or git worktree) is not resumed from another.
use std::io {IO.get_env}
use std::path {Path, Path.of, Path.to_string, Path.beq}
use std::process {Proc.capture}

pub struct SessionPlace {
    cwd : Path,
    /// `git rev-parse --show-toplevel` of `cwd`, or `cwd` outside a repo.
    repo : Path,
}

/// The startup place: `PWD` (there is no cwd/realpath native) and its repo.
/// None when `PWD` is unset or empty.
pub def Place.probe : IO (Option SessionPlace) := do {
    let pwd <- IO.get_env "PWD";
    match pwd {
        Option.none => IO.pure Option.none,
        Option.some p => match Path.of p {
            Result.err _ => IO.pure Option.none,
            Result.ok cwd => Place.at cwd,
        },
    }
}

pub def Place.at (cwd : Path) : IO (Option SessionPlace) := do {
    let repo <- Place.repo_of cwd;
    let place : SessionPlace := { cwd := cwd, repo := repo };
    IO.pure (Option.some place)
}

/// The git toplevel containing `cwd`; `cwd` itself when git fails.
pub def Place.repo_of (cwd : Path) : IO Path := do {
    let r <- Proc.capture "git" ["-C", Path.to_string cwd, "rev-parse", "--show-toplevel"];
    IO.pure (Place.repo_answer cwd r)
}

pub def Place.repo_answer (cwd : Path) (r : Pair I64 String) : Path :=
    match r {
        Pair.pair code out =>
            if code == 0
            then match Path.of (String.trim out) {
                Result.ok p => p,
                Result.err _ => cwd,
            }
            else cwd,
    }

/// The session's recorded repo is this one. A session saved before places
/// were recorded has none and matches nowhere.
pub def Place.same_repo (here : SessionPlace) (there : Option SessionPlace) : Bool :=
    match there {
        Option.none => false,
        Option.some t => Path.beq here.repo t.repo,
    }

pub def Place.cwd_of (place : Option SessionPlace) : Option Path :=
    match place {
        Option.none => Option.none,
        Option.some p => Option.some p.cwd,
    }

/// `session started in <cwd>` when a resumed session was started somewhere
/// other than here; none when it was started here or nothing is known.
pub def Place.moved_note (here : Option SessionPlace) (there : Option SessionPlace) : Option String :=
    match here {
        Option.none => Option.none,
        Option.some h => match there {
            Option.none => Option.none,
            Option.some t =>
                if Path.beq h.cwd t.cwd then Option.none
                else Option.some (String.concat "session started in " (Path.to_string t.cwd)),
        },
    }
