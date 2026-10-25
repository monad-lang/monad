// build / test_cache -- the `test` driver cache.
//
// Phase 2c. What is cached is the compiled DRIVER BINARY, never a result:
// a hit runs the same binary a miss would, so the PASS/FAIL lines are
// printed by the test binary itself and anything a test observes outside
// its source -- a temp file, the clock, the environment -- is still
// observed. That is the whole difference from the `check` cache, which
// stores a pure function's output and replays it verbatim.
//
// The entry is one directory per key holding the binary and the IR it was
// linked from. The driver writes its `<failed>/<total>` report to a path
// COMPILED INTO it, so that path lives in the entry and is derived from
// the key: a pid-derived path would make every cached driver write its
// report where nothing is listening for it.
//
// Key: `sha256(file bytes ++ mote closure ++ compiler identity ++ triple)`.
// The compiler identity is `Build.compiler_key_with`, not the bare digest,
// because the driver is a LINKED binary and the link stamp changes its
// bytes. The triple is in it because a cross build's driver only runs
// under an emulator. There is no profile: the driver is built the same way
// every run.

use std::list {List.intercalate, List.length}
use std::sha256 {Sha256.hash}
use build::hash {Build.file_digest_with, Build.probe_digest_tool, DigestTool}
use build::identity {Build.compiler_key_with}
use build::closure {Build.closure_digest_with}
use build::store {Build.ensure_dir, Build.entry_root_named, Build.read_leaf, Build.write_leaf}
use parsec::number {parse_i64}
use build::check {
  Build.cache_plan_key, Build.check_worth_caching, CachePlan, Build.plan_keys,
  Build.plan_roots,
}

/// `sha256(file bytes ++ mote closure ++ compiler identity ++ triple)`.
pub def Build.test_key (file_digest : String) (closure : String) (compiler : String) (triple : String) : String :=
    Sha256.hash (List.intercalate "\n" [file_digest, closure, compiler, triple])

/// `test_key` with the triple bound, for `Build.plan_keys`' key function.
pub def Build.test_key_of (triple : String) (file_digest : String) (closure : String) (compiler : String) : String :=
    Build.test_key file_digest closure compiler triple

/// The plan for one `test` invocation: the same decision shape as
/// `check`'s, with the TEST entry root and the triple in the key.
///
/// `requested` is the caller's half (`--no-cache`, `MONAD_NO_CACHE`,
/// `--verbose`), and the file-count floor is `Build.check_worth_caching`
/// -- its doc's reasoning is about the cost of the KEY, which is the same
/// digest-and-walk here, so one gate serves both caches.
#[partial]
pub def Build.test_plan (files : List String) (target_dir : String) (triple : String) (requested : Bool) : IO CachePlan :=
    if Bool.not requested
    then return (CachePlan.inactive "")
    else if Bool.not (Build.check_worth_caching (List.length files))
    then return (CachePlan.inactive "")
    else Build.test_plan_all files target_dir triple

/// The plan with neither caller half consulted -- `gc`'s way in, for the
/// reason `Build.check_plan_all` gives: `gc` caches nothing, so the gates
/// that protect the cache's economics buy it nothing, and a one-file `gc`
/// is the precise invocation rather than a degenerate one.
#[partial]
pub def Build.test_plan_all (files : List String) (target_dir : String) (triple : String) : IO CachePlan := do {
    let t <- Build.probe_digest_tool;
    match t {
        err m => return (CachePlan.inactive m),
        ok tool => do {
            let c <- Build.compiler_key_with tool;
            match c {
                err m => return (CachePlan.inactive m),
                ok compiler => do {
                    let roots <- Build.plan_roots tool files List.empty List.empty;
                    let key_of : String -> String -> String -> String := Build.test_key_of triple;
                    let keys <- Build.plan_keys key_of tool compiler files roots List.empty;
                    return (CachePlan.active (Build.entry_root_named target_dir "test") keys)
                }
            }
        }
    }
}

// ─── The entry ───
//
// `bin` is the driver, `bin.ll` the IR it was linked from (kept so `store
// verify` can check the pair the way it checks an artifact's, and so a
// miscompile can be read without a rebuild), and `monad_test_result.txt`
// the report path compiled into the binary.

pub def Build.test_entry_dir (root : String) (key : String) : String :=
    String.concat root (String.concat "/" key)

/// One leaf of a test entry: `<root>/<key>/<leaf>`. Public for the same
/// reason `Build.check_entry_leaf` is: `store verify` spells it too.
pub def Build.test_entry_leaf (root : String) (key : String) (leaf : String) : String :=
    String.concat (Build.test_entry_dir root key) (String.concat "/" leaf)

pub def Build.test_entry_bin (root : String) (key : String) : String :=
    Build.test_entry_leaf root key "bin"

pub def Build.test_entry_ir (root : String) (key : String) : String :=
    Build.test_entry_leaf root key "bin.ll"

/// The report path compiled into the driver. Derived from the key, so a
/// cached binary still writes somewhere the next run reads.
pub def Build.test_entry_report (root : String) (key : String) : String :=
    Build.test_entry_leaf root key "monad_test_result.txt"

/// The file's own test count, recorded beside the driver: the driver's
/// report carries only the FAILED count, and the total came from the IR,
/// which a hit never re-reads. Without this leaf a hit could report how
/// many failed but not out of how many.
pub def Build.test_entry_count (root : String) (key : String) : String :=
    Build.test_entry_leaf root key "count"

/// Whether the entry holds a driver to run AND the count a replay needs.
/// `bin` is written last by `link_ir` and `count` before the run, so an
/// entry interrupted at any point reads as not ready and is rebuilt.
pub def Build.test_entry_ready (root : String) (key : String) : IO Bool := do {
    let there <- IO.file_exists (Path.path (Build.test_entry_bin root key));
    if Bool.not there then return false
    else do {
        let n <- Build.test_entry_count_read root key;
        match n {
            Option.none => return false,
            Option.some _ => return true
        }
    }
}

/// Record the file's test count. Best-effort, like every other leaf write:
/// a store that cannot be written turns the next run into a miss.
pub def Build.test_entry_count_write (root : String) (key : String) (n : I64) : IO I64 := do {
    let _w <- Build.write_leaf (Path.path (Build.test_entry_count root key)) (I64.to_string n);
    return 0
}

/// The stored count, or `none` when it is absent or not a number -- a
/// miss, exactly as a damaged `check` entry is.
#[partial]
pub def Build.test_entry_count_read (root : String) (key : String) : IO (Option I64) := do {
    let raw <- Build.read_leaf (Path.path (Build.test_entry_count root key));
    return (Build.test_count_of raw)
}

/// Whether a HIT is available: the plan gave the file a key, and the entry
/// under it holds a driver.
pub def Build.test_cached_ready (root : String) (key : Option String) : IO Bool :=
    match key {
        Option.none => IO.pure false,
        Option.some k => Build.test_entry_ready root k
    }

/// Make an entry directory, for the miss path's link step.
pub def Build.test_entry_prepare (root : String) (key : String) : IO I64 :=
    Build.ensure_dir (Build.test_entry_dir root key)

def Build.test_count_of (raw : Option String) : Option I64 :=
    match raw {
        Option.none => Option.none,
        Option.some text => parse_i64 text
    }
