/// The compiler's own identity, as a cache key ingredient.
///
/// This is the input that is easiest to get wrong and worst to get wrong.
/// A cache key that does not pin WHICH COMPILER produced a result will
/// hand back a stale answer the first time the compiler changes, and
/// "the compiler changed" is the normal state of this repository.

use std::process {process_id}
use std::sha256 {Sha256.hash}
use build::hash {Build.file_digest_with, Build.probe_digest_tool, DigestTool}

/// `/proc/<our pid>/exe` -- the path of the binary currently executing.
///
/// The pid must be OURS, which is why `process_id` is threaded in rather
/// than using `/proc/self/exe`: that is resolved by whichever process
/// reads it, and `Proc.capture` runs `sh`, so `readlink /proc/self/exe`
/// would faithfully report the shell's own path instead of the
/// compiler's.
def Build.proc_exe_path : String :=
    String.concat "/proc/" (String.concat (I64.to_string process_id) "/exe")

/// The absolute path of the running binary, or `none` where the
/// procfs entry does not exist -- Darwin has no `/proc` at all.
///
/// `none` is a real answer and not a failure: the caller's job is to turn
/// it into "the cache is off", never into a weaker key.
#[partial]
pub def Build.compiler_exe_path : IO (Option String) := do {
    let r <- Proc.capture "readlink" ["-f", Build.proc_exe_path];
    match r {
        Pair.pair code out =>
            if code == 0
            then (if String.is_empty (String.trim out)
                  then return Option.none
                  else return (Option.some (String.trim out)))
            else return Option.none
    }
}

/// The digest of the compiler binary that is running right now.
///
/// `Result.err` means the cache MUST be disabled. There is deliberately
/// no fallback -- not to a timestamp, and not to `build_commit`, which is
/// the obvious wrong choice sitting right there: it is a git revision
/// baked in at LINK time (`-DMONAD_BUILD_COMMIT`, runtime/src/runtime.c;
/// `option_env!` for the Rust host), so editing `lang/` and rebuilding
/// produces a binary reporting the SAME revision, because the commit has
/// not moved -- only the working tree has. That is precisely the
/// development loop, so a key built on it would serve stale results
/// exactly when it matters most. `build_commit` keeps its real job,
/// stamping a revision into linked output (`llvm/src/link.mo`'s
/// `build_commit_define`), and stays out of the cache key.
///
/// "Only cache safe and expensive work" applied to its own prerequisite:
/// where safety is unavailable, the answer is no cache.
#[partial]
pub def Build.compiler_digest_with (tool : DigestTool) : IO (Result String String) := do {
    let p <- Build.compiler_exe_path;
    match p {
        Option.none => return (err Build.no_exe_path_error),
        Option.some path => Build.file_digest_with tool path
    }
}

def Build.no_exe_path_error : String :=
    "cannot identify the running compiler: /proc/<pid>/exe is unreadable (no procfs -- Darwin, or a sandbox). The build cache is DISABLED rather than keyed on build_commit, which is a link-time git revision and would not change when an uncommitted compiler edit is rebuilt."

/// Probe a digest tool, then digest the running binary.
#[partial]
pub def Build.compiler_digest : IO (Result String String) := do {
    let t <- Build.probe_digest_tool;
    match t {
        err m => return (err m),
        ok tool => Build.compiler_digest_with tool
    }
}

// ─── The link stamp, as a cache-key ingredient ───
//
// `monad build` links with `-DMONAD_BUILD_COMMIT`, and `llvm/src/link.mo`'s
// `build_commit_define` takes that value from `$MONAD_BUILD_COMMIT` when it
// is set, falling back to the compiler's own baked revision. The ENV
// override is the half the compiler digest cannot see: the same binary,
// same sources, same flags, linked with two different values, produces two
// different binaries -- so an artifact cached under one stamp must not be
// served under the other.
//
// When the variable is unset the ingredient is unchanged, because the fall
// back is the running compiler, whose digest is already in the key. That
// keeps every existing store entry valid.

/// `$MONAD_BUILD_COMMIT`, trimmed, or `""`.
#[partial]
def Build.build_commit_override : IO String := do {
    let v <- IO.get_env "MONAD_BUILD_COMMIT";
    match v {
        Option.none => return "",
        Option.some s => return (String.trim s)
    }
}

/// The compiler identity a CACHE KEY is built from: the running binary's
/// digest, folded with `$MONAD_BUILD_COMMIT` when that is set.
///
/// `compiler_digest_with` stays what its own comment says it is -- the
/// binary's bytes -- and this is the key-facing composition, so nothing
/// that merely wants to identify the compiler gets the stamp folded in by
/// accident.
#[partial]
pub def Build.compiler_key_with (tool : DigestTool) : IO (Result String String) := do {
    let stamp <- Build.build_commit_override;
    let d <- Build.compiler_digest_with tool;
    match d {
        err e => return (err e),
        ok h =>
            if String.is_empty stamp
            then return (ok h)
            else return (ok (Sha256.hash (String.concat h (String.concat "\n" stamp))))
    }
}
