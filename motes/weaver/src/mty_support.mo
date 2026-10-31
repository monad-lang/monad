// weaver / mty_support -- spawn, isolation, gating and assertion helpers
// shared by the pty drivers under `motes/weaver/test/`.
//
// The generic harness lives in `motes/mty`; this module is the weaver-specific
// glue (weaver's argv, mock fixtures, per-test roots). Keeping it in weaver's
// `src/` is what lets `use weaver::mty_support` resolve: `use` paths address a
// mote's `src/`, not the `test/` directory.
//
// `WEAVER_MTY=1` enables the suite; unset skips it green, so the ordinary
// `monad test` sweeps stay clean.
use mty::spawn {SpawnConfig, Mty, Output}
use mty::check {Check.enabled, Check.skip, Check.bin_path, Check.value_set}
use mty::grid {Grid}
use std::io {IO.println, IO.get_env, IO.current_time_nano}
use std::process {process_id, exec_cmd}

def env_or (name : String) (fallback : String) : IO String := do {
    let v <- IO.get_env name;
    match v {
        Option.some s => IO.pure s,
        Option.none => IO.pure fallback
    }
}

pub def repo_root : IO String := do {
    let v <- IO.get_env "MTY_ROOT";
    match v {
        Option.some s => IO.pure s,
        Option.none => env_or "PWD" "."
    }
}

pub def fixture_path (name : String) : IO String := do {
    let root <- repo_root;
    return (String.concat root (String.concat "/scripts/weaver-tui-repro/" name))
}

/// A fresh `/tmp/mty_<label>_<pid>_<nano>` with `sessions/` and `procs/`.
pub def temp_root (label : String) : IO String := do {
    let t <- IO.current_time_nano;
    let root := String.concat "/tmp/mty_" (String.concat label
        (String.concat "_" (String.concat (I64.to_string process_id)
        (String.concat "_" (I64.to_string t)))));
    let sessions := String.concat root "/sessions";
    let procs := String.concat root "/procs";
    let _ <- exec_cmd "mkdir"
        (List.cons "-p" (List.cons root (List.cons sessions (List.cons procs List.empty))));
    return root
}

def base_env (root : String) : List (Pair String (Option String)) :=
    List.cons (Pair.pair "HOME" (Option.some root))
        (List.cons (Pair.pair "WEAVER_SESSION_ROOT" (Option.some (String.concat root "/sessions")))
        (List.cons (Pair.pair "WEAVER_PROC_ROOT" (Option.some (String.concat root "/procs")))
        (List.cons (Pair.pair "NO_COLOR" Option.none) List.empty)))

def turns_env (fixture : Option String) : List (Pair String (Option String)) :=
    match fixture {
        Option.some p => List.cons (Pair.pair "SHUTTLE_MOCK_TURNS" (Option.some p)) List.empty,
        Option.none => List.empty
    }

pub def env_of (root : String) (fixture : Option String) (extra : List (Pair String (Option String))) : List (Pair String (Option String)) :=
    List.append (List.append (base_env root) (turns_env fixture)) extra

pub def weaver_args (model : String) : List String :=
    List.cons "--provider" (List.cons "mock" (List.cons "--model" (List.cons model List.empty)))

pub def spawn (bin : String) (model : String) (rows : I64) (cols : I64) (root : String)
              (fixture : Option String) (extra : List (Pair String (Option String))) : IO (Result String Mty) := do {
    let cfg : SpawnConfig := {
        bin := bin,
        args := weaver_args model,
        rows := rows,
        cols := cols,
        env := env_of root fixture extra
    };
    Mty.spawn cfg
}

/// `WEAVER_MTY` unset -> print SKIP and return none (green); set -> return
/// the binary path. A missing binary then fails the test through `spawn`.
pub def gate (label : String) : IO (Option String) := do {
    let on <- Check.enabled "WEAVER_MTY";
    if Bool.not on then do {
        let _ <- Check.skip label;
        return Option.none
    } else do {
        let bin <- Check.bin_path "target-monad/release/weaver";
        return (Option.some bin)
    }
}

/// Run `body` with the resolved binary, or skip green when `WEAVER_MTY` is
/// unset. The body owns its temp root (see `with_root`).
pub def run_gated (label : String) (body : String -> IO Bool) : IO Bool := do {
    let g <- gate label;
    match g {
        Option.none => IO.pure true,
        Option.some bin => body bin
    }
}

/// Create a labelled temp root, run `body`, then remove it on success and
/// keep it (named on stdout) on failure.
pub def with_root (label : String) (body : String -> IO Bool) : IO Bool := do {
    let root <- temp_root label;
    let ok <- body root;
    cleanup_if ok root;
    return ok
}

pub def cleanup (root : String) : IO Unit := do {
    let keep <- Check.value_set "WV_SESSION_KEEP";
    if keep then IO.pure unit
    else do {
        let _ <- exec_cmd "rm" (List.cons "-rf" (List.cons root List.empty));
        return unit
    }
}

/// Remove the root on success; keep it (and name it) on failure for logs.
pub def cleanup_if (ok : Bool) (root : String) : IO Unit :=
    if ok then cleanup root
    else do {
        IO.println (String.concat "mty: kept failed test root " root);
        return unit
    }

/// Send Ctrl+C twice and wait for the alt-screen restore.
pub def quit_cleanly (m : Mty) (deadline_ms : I64) : IO Bool := do {
    Mty.send_text m "\u{3}";
    Mty.send_text m "\u{3}";
    Mty.wait_until m (fn (o : Output) => String.contains o.raw "\u{1b}[?1049l") deadline_ms
}

pub def pos_row (p : Pair I64 I64) : I64 :=
    match p { Pair.pair r _ => r }

pub def pos_col (p : Pair I64 I64) : I64 :=
    match p { Pair.pair _ c => c }

pub def found_at_row (o : Output) (needle : String) (row : I64) : Bool :=
    match Output.find o needle {
        Option.some p => I64.beq (pos_row p) row,
        Option.none => false
    }

pub def not_found (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.none => true,
        Option.some _ => false
    }

/// Count non-overlapping occurrences of an ASCII needle.
#[partial]
def count_at (hay : String) (needle : String) (i : I64) (acc : I64) : I64 :=
    if I64.gt (i + String.length needle) (String.length hay) then acc
    else if String.slice hay i (String.length needle) == needle then count_at hay needle (i + 1) (acc + 1)
    else count_at hay needle (i + 1) acc

pub def count_occurrences (hay : String) (needle : String) : I64 :=
    if String.is_empty needle then 0 else count_at hay needle 0 0

#[partial]
def rows_with_go (g : Grid) (needle : String) (r : I64) (to : I64) (acc : I64) : I64 :=
    if Bool.not (I64.lt r to) then acc
    else
        let hit := if String.contains (Grid.row_text g r) needle then acc + 1 else acc in
        rows_with_go g needle (r + 1) to hit

pub def rows_with (g : Grid) (needle : String) (from : I64) (to : I64) : I64 :=
    rows_with_go g needle from to 0

pub def any_row (g : Grid) (needle : String) (from : I64) (to : I64) : Bool :=
    I64.gt (rows_with g needle from to) 0

/// A 1-based SGR mouse report; `x`/`y` are 0-based cell coordinates.
pub def sgr (button : I64) (x : I64) (y : I64) (final : String) : String :=
    String.concat "\u{1b}[<" (I64.to_string button
        ++ ";" ++ I64.to_string (x + 1)
        ++ ";" ++ I64.to_string (y + 1)
        ++ final)
