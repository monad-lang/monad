/// The `check` cache: what a run already knows, and where it says so.
///
/// Phase 2b of plans/packaging/mote-build-deps-artifacts-targets.md. The
/// governing rule is "only cache safe and expensive work", and both
/// halves of it are decided here rather than assumed:
///
///   * SAFE. The key covers the file's own bytes, the digest of its
///     mote's whole declared closure, and the identity of the running
///     compiler. Where any of those cannot be determined the cache turns
///     itself OFF -- it never answers from a weaker key. The specific
///     trap is documented at `Build.compiler_digest_with`: `build_commit`
///     does NOT change when an uncommitted `lang/` edit is rebuilt, and
///     that is the normal state of this repository.
///
///   * EXPENSIVE. A corpus `check` is 789 seconds over 195 files and the
///     pre-commit hook runs one on every commit. A single-file check is
///     not that (`Build.check_worth_caching`).
///
/// Two shapes here are deliberately NOT what a naive cache would do, and
/// both are load-bearing:
///
///   * **Record per file, never split the run.** `run_check_loop` threads
///     ONE `ModuleInfoCache`, which is what makes a file's dependency
///     closure free once an earlier file has loaded it -- measured at 75%
///     of dependency loads on a 5-file run. Per-file INVOCATIONS of the
///     checker throw that away, and are why one big file alone never
///     finishes while all 195 together are 789 seconds. So a hit is
///     replayed in place, inside the one loop, and the misses among it run
///     in the same single invocation they always did.
///
///   * **A hit cannot be less informative than a miss.** Entries store the
///     rendered output verbatim, so a replay is byte-exact -- see
///     `Build.check_block`.

use std::list {List.contains_by, List.intercalate, List.length}
use std::sha256 {Sha256.hash}
use lang::mote {Mote.discover}
use lang::module {extract_directory}
use parsec::number {parse_i64}
use build::hash {Build.file_digest_with, Build.probe_digest_tool, DigestTool}
use build::identity {Build.compiler_digest_with}
use build::closure {Build.closure_digest_with}
use build::store {Build.ensure_dir, Build.entry_root_dir, Build.read_leaf, Build.write_leaf, check}

/// The working directory under ONE name.
///
/// `""` and `"."` both name it -- `Mote.discover` reports the manifest's
/// directory relative to where the walk started, so `src/a.mo` gives `""`
/// while the same tree spelled `./src/a.mo` gives `"."` -- and a root is a
/// directory, so the two must not be distinguishable downstream. `""` is
/// also what `extract_directory` returns for a bare filename, which is the
/// same reading: the working directory.
def Build.root_or_cwd (d : String) : String :=
    if String.is_empty d then "." else d

/// `mote_root_of src`: the directory of the mote containing `src`.
///
/// What a closure digest must be taken over is the MOTE ROOT, not the
/// source directory. The difference is load-bearing: a mote's `mote.toml`
/// sits at the root while its sources sit in `src/`, so digesting only
/// `extract_directory src` would leave the manifest out of the key -- and
/// `gate_declared_deps` (lang/src/module.mo) runs BEFORE elaboration and
/// can fail a load on a manifest edit alone. Falls back to the source
/// directory for a file outside any mote, which has no manifest to miss.
///
/// **The empty answer is normalized, and that is a correctness fix rather
/// than tidiness.** A manifest in the working directory -- `cd mymote &&
/// monad check src/a.mo src/b.mo`, the most ordinary single-mote layout
/// there is -- comes back as `manifest.dir = ""`, while the same tree
/// spelled `./src/a.mo` comes back as `"."`. One directory, two names, and
/// a consumer that tells them apart caches one spelling and not the other:
/// `Build.plan_roots` skipped the empty one as "outside any mote", so
/// `monad check src/a.mo src/b.mo` wrote **no** check entries while
/// `monad check ./src/a.mo ./src/b.mo` wrote two. Measured, a fresh store
/// per spelling, two files in a mote rooted at the working directory:
/// `src/...` 0 entries; `./src/...` and absolute paths 2 entries on the
/// same hashes. Silently, and with the plain spelling being the one a user
/// types -- the same shape as the build cache's empty-root shutdown, one
/// layer up, where normalizing at the single producer is what fixes both
/// consumers at once rather than each remembering the convention.
///
/// For a moteless file the root becomes `"."` too, so its closure digest is
/// of the working directory. Sound (the file's own bytes are in the key
/// separately) and strictly better than declining to cache.
#[partial]
pub def Build.mote_root_of (src : String) : IO String := do {
    let m <- Mote.discover (extract_directory src);
    match m {
        Option.some manifest => return (Build.root_or_cwd manifest.dir),
        Option.none => return (Build.root_or_cwd (extract_directory src))
    }
}

/// Whether a run over `count` files is worth keying at all.
///
/// One file is not. The key costs a digest of the compiler binary (tens
/// of megabytes) plus a digest of the mote's tree, and it is computed
/// against a single file's closure load -- while `monad check <one file>`
/// is the editor loop, run hundreds of times as a fixed per-invocation
/// cost. Multi-file runs are the pre-commit hook, CI, and the corpus
/// sweep, which is where the 789 seconds live.
///
/// The threshold is on the EXPANDED list, so `monad check lang/` (one
/// argument, sixty files) is cached while `monad check lang/src/parser.mo`
/// is not.
pub def Build.check_worth_caching (count : I64) : Bool :=
    I64.gt count 1

/// Everything one `check` invocation needs to decide, per file, whether to
/// consult the store -- computed once up front, then read-only.
pub type CheckPlan {
    /// On: the store may be both consulted and written.
    active (entry_root : String) (keys : List (Pair String String)),
    /// Off. `reason` is `""` when the cache was simply not asked for --
    /// `--no-cache`, `MONAD_NO_CACHE`, `--verbose`, or a single-file run
    /// -- and those say nothing, because the user who asked for them
    /// knows why. A non-empty `reason` means the cache wanted to run and
    /// could not, which is the one case worth a line: a silently disabled
    /// cache on the machine that needed it is invisible otherwise.
    inactive (reason : String),
}

/// The store root for `check` entries, or `""` when the plan is inactive.
pub def Build.check_plan_root (p : CheckPlan) : String :=
    match p {
        CheckPlan.active root _keys => root,
        CheckPlan.inactive _reason => "",
    }

pub def Build.check_plan_active (p : CheckPlan) : Bool :=
    match p {
        CheckPlan.active _root _keys => true,
        CheckPlan.inactive _reason => false,
    }

/// The reason to report, or `""` when there is nothing to report.
pub def Build.check_plan_reason (p : CheckPlan) : String :=
    match p {
        CheckPlan.active _root _keys => "",
        CheckPlan.inactive reason => reason,
    }

/// The key for `file`, or `none` when no key could be computed for it --
/// its digest failed, or its mote's did. A file with no key is checked
/// normally and not recorded, which is the safe direction.
pub def Build.check_plan_key (p : CheckPlan) (file : String) : Option String :=
    match p {
        CheckPlan.active _root keys => Build.key_lookup file keys,
        CheckPlan.inactive _reason => Option.none,
    }

#[partial]
def Build.key_lookup (file : String) (keys : List (Pair String String)) : Option String :=
    match keys {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                Pair.pair f k => if String.beq f file then Option.some k else Build.key_lookup file rest,
            }
    }

/// Decide the whole plan for one run.
///
/// `requested` is the caller's half -- `--no-cache`, `MONAD_NO_CACHE` and
/// `--verbose` all arrive here as `false`, and all three are silent. The
/// file-count half is `Build.check_worth_caching`, also silent. When both
/// say yes, the plan is built by probing the digest tool and identifying
/// the compiler FIRST: either of those failing is an `inactive` plan
/// carrying the reason, because a key that cannot include the compiler is
/// a key that would serve stale answers the first time the compiler
/// changed.
#[partial]
pub def Build.check_plan (files : List String) (target_dir : String) (requested : Bool) : IO CheckPlan :=
    if Bool.not requested
    then return (CheckPlan.inactive "")
    else if Bool.not (Build.check_worth_caching (List.length files))
    then return (CheckPlan.inactive "")
    else Build.check_plan_all files target_dir

/// The plan with **neither caller half** consulted: no `requested` and no
/// worth-caching floor.
///
/// Both of the gates `check_plan` applies above are about the CHECK verb's
/// economics, and neither is a statement about whether a key can be
/// derived. `requested` is the escape hatch and the worth floor is "a
/// one-file check in an editor loop costs less than the fork its key
/// needs" -- both reasons not to DO the work, not reasons it would be
/// wrong to.
///
/// So `gc` needs this one. It caches nothing, so the floor buys it nothing,
/// and `monad gc src/one.mo` is not a degenerate invocation -- it is the
/// precise one, because it asks for everything a single file cannot reach.
/// Routed through `check_plan`, that invocation planned nothing, saw an
/// inactive plan, and (correctly, given what it had been told) refused. The
/// safe failure and a useless verb at the same time: `gc` could only ever
/// reclaim from a run that named two or more files. `Build.gc_run` calls
/// this directly.
#[partial]
pub def Build.check_plan_all (files : List String) (target_dir : String) : IO CheckPlan := do {
    let t <- Build.probe_digest_tool;
    match t {
        err m => return (CheckPlan.inactive m),
        ok tool => do {
            let c <- Build.compiler_digest_with tool;
            match c {
                err m => return (CheckPlan.inactive m),
                ok compiler => do {
                    let roots <- Build.plan_roots tool files List.empty List.empty;
                    let keys <- Build.plan_keys tool compiler files roots List.empty;
                    return (CheckPlan.active (Build.entry_root_dir target_dir Entry.check) keys)
                }
            }
        }
    }
}

/// One closure digest per MOTE, not one per file, and the WHOLE DECLARED
/// CLOSURE rather than the mote's own tree.
///
/// Both halves of that are load-bearing, and the second is the one that
/// is easy to get wrong.
///
/// *The closure, not the tree.* `check_deps = false` (lang/src/module.mo)
/// means only the target file's OWN decls are typechecked -- but against
/// its closure's *signatures*. So a one-line change inside `std` can flip
/// whether a file in `lang` checks, with every byte of that file and of
/// its own mote unchanged. Keying on the mote's own tree alone would
/// serve a stale answer for exactly that edit. `Build.closure_digest_with`
/// already walks the transitive declared closure and already handles the
/// real `init <-> std` dev-dependency cycle, so the key composes the same
/// walk rather than a second, weaker one.
///
/// *Per mote, not per file.* A `check` run names files in clumps -- the
/// corpus sweep is 195 files over eleven motes -- so a per-file closure
/// digest would repeat sixty identical walks for `lang/` alone.
///
/// The cost is real but bounded by the number of distinct motes named,
/// not by the file count: eleven walks, each re-digesting a handful of
/// trees, against a run whose whole point is that it is 789 seconds.
///
/// `seen` is updated even when the digest FAILS, so a mote whose closure
/// cannot be read is not retried once per file. A file whose root gives
/// no digest gets no key: it is checked normally and never recorded,
/// which is the safe direction -- a missing key costs a check, which is
/// what was going to happen anyway.
///
/// **A root that names the working directory is digested, not skipped.**
/// There used to be an `String.is_empty root` branch here that read `""` as
/// "a file outside any mote", and it was wrong for the commonest layout
/// there is -- a mote whose manifest sits in the working directory, which
/// `Mote.discover` reports as `""`. It silently declined to key one
/// spelling of one build and keyed the other. `Build.mote_root_of` now
/// normalizes that to `"."` at the single producer, so this walk sees one
/// name for one root and needs no special case; declining is left to a real
/// digest failure, which is what the paragraph above is about.
///
/// Order is visit order, i.e. first appearance in the file list, and the
/// list is a lookup table rather than a key ingredient -- nothing hashes
/// it, so its order does not matter.
#[partial]
def Build.plan_roots (tool : DigestTool) (files : List String) (seen : List String) (acc : List (Pair String String)) : IO (List (Pair String String)) :=
    match files {
        List.empty => return acc,
        List.cons f rest => do {
            let root <- Build.mote_root_of f;
            if List.contains_by String.beq root seen
            then Build.plan_roots tool rest seen acc
            else do {
                let d <- Build.closure_digest_with tool root;
                match d {
                    err _m => Build.plan_roots tool rest (List.cons root seen) acc,
                    ok h => Build.plan_roots tool rest (List.cons root seen) (List.append acc [Pair.pair root h])
                }
            }
        }
    }

/// One key per file.
///
/// The file's OWN bytes are in the key even though its mote's closure
/// digest already covers them -- that digest is a digest OF A DIRECTORY,
/// and the file is reached through it only while `Build.mote_root_of`
/// resolves the way it is expected to. One extra digest per file costs a
/// fork against a walk that already forked once per mote, and it makes
/// the key's coverage readable off the key itself rather than off an
/// argument about a directory walk.
#[partial]
def Build.plan_keys (tool : DigestTool) (compiler : String) (files : List String) (roots : List (Pair String String)) (acc : List (Pair String String)) : IO (List (Pair String String)) :=
    match files {
        List.empty => return acc,
        List.cons f rest => do {
            let root <- Build.mote_root_of f;
            match Build.root_find root roots {
                Option.none => Build.plan_keys tool compiler rest roots acc,
                Option.some c => do {
                    let fd <- Build.file_digest_with tool f;
                    match fd {
                        err _m => Build.plan_keys tool compiler rest roots acc,
                        ok fh => Build.plan_keys tool compiler rest roots
                            (List.append acc [Pair.pair f (Build.check_key fh c compiler)])
                    }
                }
            }
        }
    }

/// `sha256(file bytes ++ mote closure ++ compiler identity)`.
///
/// No profile and no triple, unlike `Build.input_hash`: `check` does not
/// compile and is target-independent today. `cfg` is the input that will
/// change that when it lands self-hosted
/// (`implementations/attributes-deprecated-and-cfg.md` already names
/// folding the resolved feature set into the build input hash as the
/// coordination point) -- and until then there is nothing to add.
def Build.check_key (file_digest : String) (closure : String) (compiler : String) : String :=
    Sha256.hash (List.intercalate "\n" [file_digest, closure, compiler])

/// The digest of `root`'s tree, from a memo of root -> closure digest.
/// Absent means the digest failed (or the root was never walked), and a
/// file with no closure digest gets no key -- checked normally, never
/// served from the store.
///
/// Shared with `gc`, which needs the same lookup over its own memo
/// (`Build.collect_root_digests`, `build/src/manage.mo`); the two memos
/// are built by different walks but have this shape.
pub def Build.root_find (root : String) (roots : List (Pair String String)) : Option String :=
    match roots {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                Pair.pair r h => if String.beq r root then Option.some h else Build.root_find root rest,
            }
    }

// --- the entry: two files, no delimiter to parse ---
//
// `out` is the rendered output, byte for byte what `check` prints.
// `errors` is the count the summary line needs. They are separate FILES
// rather than one file with a count prefix because every alternative
// needs the first newline's index, and this stdlib has `String.find_last`
// but no `String.find` -- so a delimiter would mean either a bounded
// byte-scan in Monad or a dependency on a stdlib function that is not
// public. Two small files have neither problem, and `errors` is written
// FIRST so that `out` existing implies `errors` does.
//
// The cost is one extra `read_file` on a hit, against a check that is
// seconds to minutes. That is the right trade for a format with no
// parsing in it at all.

/// The entry directory for one key: `<target-dir>/check/<key>`.
pub def Build.check_entry_dir (root : String) (key : String) : String :=
    String.concat root (String.concat "/" key)

/// One leaf of a check entry: `<root>/<key>/<leaf>`.
///
/// Public because `store verify` (`build/src/manage.mo`) has to look at
/// the two leaves a readable entry is made of, and it must spell them the
/// same way the reader and the writer do. A second copy of this path rule
/// is a second thing to forget when the format changes.
pub def Build.check_entry_leaf (root : String) (key : String) (leaf : String) : String :=
    String.concat (Build.check_entry_dir root key) (String.concat "/" leaf)

/// What `check` prints for one file -- and, because this exact string is
/// what gets stored, exactly what a hit replays.
///
/// Rendering lives here rather than in `cli/src/main.mo` so that the
/// printed text and the stored text cannot drift: the entry IS this
/// string. The loop prints it with one `println` where it used to print
/// the header and then each diagnostic on its own line, which is the same
/// bytes -- `println (intercalate "\n" xs)` is `mapM_ println xs`.
pub def Build.check_block (path : String) (diags : List String) (warnings : List String) : String :=
    if List.is_empty diags
    then
        if List.is_empty warnings
        then String.concat "ok    " path
        else List.intercalate "\n" (List.cons (Build.warn_header path (List.length warnings)) warnings)
    else List.intercalate "\n" (List.cons (Build.fail_header path (List.length diags)) (List.append diags warnings))

/// The warning counterpart of `fail_header`, for a file that checked
/// clean but still has something to say -- the same column shape, so
/// the three verdicts read as one column of statuses.
def Build.warn_header (path : String) (n : I64) : String :=
    String.concat "WARN  " (String.concat path (String.concat " (" (String.concat (I64.to_string n) " warning(s))")))

/// The two counts a replay needs to re-derive the summary line:
/// errors, which the entry has always stored, and warnings, which ride
/// the stored block but also get a leaf of their own so the summary's
/// warning total survives a cache hit.
pub struct Build.CheckTally {
    errors : I64,
    warnings : I64,
}

/// The `FAIL` header, character for character what the loop printed before
/// this module existed. `check_block` is the only producer, so a change
/// here is a change to `check`'s output and not to a cache format.
def Build.fail_header (path : String) (n : I64) : String :=
    String.concat "FAIL  " (String.concat path (String.concat " (" (String.concat (I64.to_string n) " error(s))")))

/// Replay a stored result, or `none` when there is nothing readable --
/// absent, half-written, or not a number where a number belongs.
///
/// Every one of those is a MISS and not an error. A miss costs a check,
/// which is what was going to happen anyway; a hit is only ever a saving.
/// That is also what makes a damaged entry harmless rather than
/// poisonous, which is the property a cache most needs.
#[partial]
pub def Build.check_entry_read (root : String) (key : String) : IO (Option (Pair Build.CheckTally String)) := do {
    let raw <- Build.read_leaf (Build.check_entry_leaf root key "errors");
    match Build.parsed_count raw {
        Option.none => return Option.none,
        Option.some n => Build.check_entry_read_out root key n
    }
}

/// A leaf's text as a count; `none` when it is absent or not a number.
def Build.parsed_count (raw : Option String) : Option I64 :=
    match raw {
        Option.none => Option.none,
        Option.some text => parse_i64 text
    }

/// The rest of a hit once the error count parsed: the `out` block is
/// required (absent is a miss), the warning count is not.
#[partial]
def Build.check_entry_read_out (root : String) (key : String) (n : I64) : IO (Option (Pair Build.CheckTally String)) := do {
    let block <- Build.read_leaf (Build.check_entry_leaf root key "out");
    let warns <- Build.check_entry_warn_count root key;
    return (match block {
        Option.none => Option.none,
        Option.some b => Option.some (Pair.pair (Build.CheckTally.mk n warns) b)
    })
}

/// The warnings half of a stored tally: `0` when the leaf is absent or
/// not a number, and NOT a miss. An entry written before warnings
/// existed is still a valid hit -- it was written by a checker that
/// could not produce warning text, so a zero count is the honest
/// replay of what it recorded.
#[partial]
def Build.check_entry_warn_count (root : String) (key : String) : IO I64 := do {
    let raw <- Build.read_leaf (Build.check_entry_leaf root key "warnings");
    return (match Build.parsed_count raw {
        Option.none => 0,
        Option.some n => n,
    })
}

/// Record a result. Best-effort by design: a store that cannot be written
/// turns the next run into a miss, which is the same answer as never
/// having tried -- so a failed write is reported on stderr
/// (`Build.write_leaf`) and the check carries on.
#[partial]
pub def Build.check_entry_write (root : String) (key : String) (errors : I64) (warnings : I64) (block : String) : IO I64 := do {
    let d : String := Build.check_entry_dir root key;
    let _mk <- Build.ensure_dir d;
    let _c <- Build.write_leaf (Build.check_entry_leaf root key "errors") (I64.to_string errors);
    let _w <- Build.write_leaf (Build.check_entry_leaf root key "warnings") (I64.to_string warnings);
    let _o <- Build.write_leaf (Build.check_entry_leaf root key "out") block;
    return 0
}

/// Record a result when the plan gives the file a key, and do nothing when
/// it does not -- the one place the loop has to know about either.
#[partial]
pub def Build.check_maybe_write (p : CheckPlan) (key : Option String) (errors : I64) (warnings : I64) (block : String) : IO I64 :=
    match key {
        Option.none => return 0,
        Option.some k => Build.check_entry_write (Build.check_plan_root p) k errors warnings block
    }
