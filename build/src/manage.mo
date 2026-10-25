/// The store's management verbs: `clean`, `clean --all`, `gc`,
/// `store ls` and `store verify`.
///
/// Phase 2a's second half of
/// plans/packaging/mote-build-deps-artifacts-targets.md. One module rather
/// than four because three of these verbs have to agree on ONE rule --
/// what the current source state can still reach -- and a rule written
/// twice is a rule that drifts. `store ls`/`verify` are here for the other
/// half of that agreement: what an entry IS.
///
/// **The layout respected here is what exists, not what the plan
/// sketched.** The fuller layout (`db/<hash>.json`, `.gc-roots/`,
/// symlinked profiles) has no writer yet. Two entry kinds are populated
/// today:
///
///   * `<target-dir>/store/<hash>` and `<hash>.ll` -- an artifact as a
///     SIBLING PAIR. The IR is not decoration: it is the file `llc` is
///     actually pointed at, so dropping one of the two is a bug and both
///     verbs below treat the pair as one entry.
///   * `<target-dir>/check/<hash>/{out,errors}` -- a check result.
///
/// `<target-dir>/test/` and `db/` are empty (2c is unimplemented, and
/// `db/` has no writer), which is why `store ls` cannot source a
/// human-readable name from `db/<hash>.json` and `verify` checks two kinds
/// rather than three. Saying that out loud is part of the job: a column
/// that is always empty is worse than a sentence that says why.
///
/// **A management verb may fall back to doing LESS; it must never fall
/// back to a weaker decision.** A cache may respond to an uncomputable key
/// by doing the work. A `gc` has no such fallback -- its decision is what
/// to DELETE -- so the same failure has to stop it instead. That asymmetry
/// is the whole of `Build.reach_of` below.

use std::list {List.contains_by, List.filter, List.intercalate, List.length}
use std::process {exec_cmd}
use parsec::number {parse_i64}
use build::hash {Build.file_digest_with, Build.probe_digest_tool, DigestTool}
use build::identity {Build.compiler_key_with}
use build::closure {Build.artifact_key, Build.closure_digest_with}
use build::check {
  Build.check_entry_leaf, Build.check_plan_active, Build.check_plan_all,
  Build.check_plan_key, Build.check_plan_reason, Build.mote_root_of,
  Build.root_find, CheckPlan,
}
use build::store {
  Build.artifact_ir_path, Build.entry_root_dir, Build.read_leaf, Build.store_path, Entry,
}

open Entry {artifact, check, test}

// --- what an entry is called ---

/// The four kinds `<target-dir>` owns. Spelled out because `clean` needs
/// the complement of this set, and a set defined by what the store IS is
/// one a future kind cannot fall out of.
pub def Build.kind_dir_names : List String := ["store", "check", "test", "db"]

pub def Build.is_kind_dir (name : String) : Bool :=
    List.contains_by String.beq name Build.kind_dir_names

/// Anything under `<target-dir>` that is not a kind directory is an output
/// PRODUCT -- a profile directory today (`debug`, `release`), and whatever
/// a later profile is called. Defined by exclusion so that `clean` cannot
/// reach an entry: no profile name has to be known here, and no value of
/// this predicate can be `store`, `check`, `test` or `db`.
pub def Build.is_output_dir (name : String) : Bool :=
    Bool.not (String.is_empty name) && Bool.not (Build.is_kind_dir name)

def Build.hex_digits : List String :=
    ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f"]

def Build.is_hex_char (c : String) : Bool :=
    List.contains_by String.beq c Build.hex_digits

/// Whether all 64 characters from `i` on are lowercase hex. Bounded by 64
/// rather than by the string's length because the caller has already
/// established the length.
#[partial]
def Build.all_hex (name : String) (i : I64) : Bool :=
    if I64.gt i 63 then true
    else if Build.is_hex_char (String.slice name i 1) then Build.all_hex name (i + 1)
    else false

/// A sha256 key: 64 lowercase hex characters. The only shape an entry's
/// name may have, and therefore the test that separates an entry from
/// something that merely sits in the store.
///
/// This is what lets `gc` see that a legacy slug entry (`<hash>-monad`,
/// `<hash>-r3`) is UNREACHABLE rather than merely unrecognized. Those were
/// written when the artifact entry was `<hash>-<basename of -o>`; the
/// lookup has been bare `<hash>` since the IR filename became key-derived
/// (`Build.artifact_ir_path`), so nothing can hit one again. They are
/// invisible to `store ls` -- which lists entries, and they are not
/// entries -- and they are the first thing a `gc` reclaims.
pub def Build.is_key (name : String) : Bool :=
    if Bool.not (I64.beq (String.length name) 64) then false
    else Build.all_hex name 0

pub def Build.key_of (name : String) : Option String :=
    if Build.is_key name then Option.some name else Option.none

/// The first 12 characters of a key, for a human to compare against another
/// key's first 12. Enough to tell two compilers apart, short enough to read
/// in a line of `gc` output.
pub def Build.short_key (k : String) : String :=
    if I64.gt (String.length k) 12 then String.slice k 0 12 else k

/// The artifact's IR companion suffix, spelled once.
///
/// It is stripped in two places -- `Build.artifact_name_key` asks "is this an
/// entry?" and `Build.droppable_name` asks "what would removing this
/// remove?" -- and the first cut wrote the length out as a literal in both.
/// `String.slice` takes a LENGTH, not an end index, so the literal was the
/// suffix's length and `.ll` is three characters, not two: both call sites
/// silently kept the dot and every `.ll` name read as a 65-character
/// non-key. One spelling and a derived length, so there is no number left to
/// get wrong in one place and not the other.
def Build.ir_suffix : String := ".ll"

/// `name` without its IR companion suffix, unchanged when it has none.
pub def Build.strip_ir_suffix (name : String) : String :=
    if String.ends_with name Build.ir_suffix
    then String.slice name 0 (String.length name - String.length Build.ir_suffix)
    else name

/// The key a NAME in `store/` carries, or `none` when the name is not an
/// artifact entry's name at all.
///
/// `<hash>` and `<hash>.ll` are two spellings of ONE entry, so the `.ll`
/// is stripped before the shape test and a directory listing of the store
/// yields one key per artifact rather than two.
pub def Build.artifact_name_key (name : String) : Option String :=
    Build.key_of (Build.strip_ir_suffix name)

// --- what the current tree can reach ---

/// The two profiles a `build` can produce -- `profile_name`
/// (cli/src/main.mo) is `debug` or `release`, and nothing else. A third
/// value there must be added here too, which is exactly why `gc` prints
/// the keys it derived: a profile missing from this list would make every
/// entry that build wrote look unreachable.
pub def Build.profile_names : List String := ["debug", "release"]

/// The result of deriving what a tree can reach, which is either the set
/// or a refusal to have one.
///
/// `known` carries the COMPILER digest the set was derived under, which is
/// not a detail: every key in the store has the compiler folded into it, so
/// a set derived by one compiler cannot reach an entry written by another.
/// Printed by `Build.gc_run` because the alternative is a number that reads
/// as "your store is all orphans" when the truth is "these entries were
/// made by a different compiler, and this one can never hit them". Both are
/// reclaimable and the second is not a problem, but a user told only the
/// first will go looking for a bug.
pub type Reach {
    known (artifacts : List String) (checks : List String) (compiler : String),
    refused (reason : String),
}

/// The reason an inactive plan carries, or a sentence when it carries
/// none.
///
/// `Build.check_plan` answers `inactive ""` for a cache the user simply did not
/// ask for (`--no-cache`, a single file), and a `gc` that stopped there
/// would refuse with a blank space after the colon. `gc` passes
/// `requested := true` and a whole file list, so this should never be
/// reached -- but "should never" is not a reason to print nothing.
pub def Build.inactive_reason (p : CheckPlan) : String :=
    if String.is_empty (Build.check_plan_reason p)
    then "the check plan came back inactive with no reason"
    else Build.check_plan_reason p

#[partial]
def Build.refuse (m : String) : IO Reach :=
    return (Reach.refused m)

/// Every key the CURRENT source state would produce, or a refusal.
///
/// **This is where `gc` gets its safety from.** A key is a pure function
/// of content, so anything outside this set is unreachable from this tree
/// by construction -- and that argument holds only if the set is COMPLETE.
/// Every way of failing to be complete is therefore a refusal rather than
/// a smaller set, because the failure mode is not "gc keeps something it
/// could have dropped" but "gc deletes the store". Three routes:
///
///   * an unprobeable digest tool or an uncomputable compiler digest
///     collapses `Build.check_plan` to `inactive` with no error channel at all,
///     and `Build.check_plan_key` then answers `none` for EVERY file;
///   * a per-file digest failure is absorbed by the plan -- the file
///     simply gets no key, which is the safe direction for a cache -- so
///     it is caught here structurally, by requiring one key per file
///     named, rather than by reading an error that is not reported;
///   * an empty file list derives an empty set. The same catastrophe with
///     a more innocent cause, so it refuses too.
///
/// `requested` is `true` unconditionally, and that is deliberate. `gc` is
/// not a check run. `--verbose` exists to disable a check run's cache
/// (because a replayed entry has no trace to show), and it reaches
/// `Build.check_plan` through the call site's own expression
/// (`requested && Bool.not verbose`, cli/src/main.mo) rather than through
/// `cache_enabled`. A `gc` that reused that expression would derive no
/// keys and delete the whole store -- worst of all when the user passed
/// `--verbose` to watch it happen.
#[partial]
pub def Build.reach_of (files : List String) (target_dir : String) (triples : List String) : IO Reach :=
    match files {
        List.empty => Build.refuse "no files were named, so no key could be derived",
        List.cons _ _ => Build.reach_planned files target_dir triples
    }

#[partial]
def Build.reach_planned (files : List String) (target_dir : String) (triples : List String) : IO Reach := do {
    let plan <- Build.check_plan_all files target_dir;
    if Bool.not (Build.check_plan_active plan)
    then Build.refuse (Build.inactive_reason plan)
    else do {
        let ks <- Build.collect_check_keys plan files List.empty;
        match ks {
            err f => Build.refuse ("no key could be derived for " ++ f),
            ok checks => Build.reach_keyed files triples checks
        }
    }
}

#[partial]
def Build.reach_keyed (files : List String) (triples : List String) (checks : List String) : IO Reach := do {
    let t <- Build.probe_digest_tool;
    match t {
        err m => Build.refuse m,
        ok tool => Build.reach_digested tool files triples checks
    }
}

#[partial]
def Build.reach_digested (tool : DigestTool) (files : List String) (triples : List String) (checks : List String) : IO Reach := do {
    let c <- Build.compiler_key_with tool;
    match c {
        err m => Build.refuse m,
        ok compiler => do {
            let roots <- Build.collect_root_digests tool files List.empty List.empty;
            match roots {
                err m => Build.refuse m,
                ok memo => do {
                    let arts <- Build.collect_artifacts { tool := tool, compiler := compiler,
                        files := files, roots := memo, triples := triples, acc := List.empty };
                    match arts {
                        err m => Build.refuse m,
                        ok artifacts => return (Reach.known artifacts checks compiler)
                    }
                }
            }
        }
    }
}

/// One key per file, or the name of the first file that got none.
///
/// The completeness check is structural on purpose: `Build.check_plan` reports a
/// per-file digest failure by giving that file no key, not by carrying an
/// error, so "every file named came back with a key" is the only reading
/// of success available from outside it.
#[partial]
def Build.collect_check_keys (plan : CheckPlan) (files : List String) (acc : List String) : IO (Result String (List String)) :=
    match files {
        List.empty => return (ok acc),
        List.cons f rest => do {
            let k := Build.check_plan_key plan f;
            match k {
                Option.none => return (err f),
                Option.some key => Build.collect_check_keys plan rest (List.append acc [key])
            }
        }
    }

/// The closure digest of every distinct mote root the named files resolve
/// to, as a root -> digest memo.
///
/// `Build.mote_root_of` is the same function `build_cached` calls, which
/// is what makes the artifact keys derived from these roots the keys a
/// build of these files would write -- including the normalization that
/// gives a mote whose manifest sits in the working directory the root
/// `"."`, rather than the `""` a consumer could not tell apart from
/// "outside any mote".
///
/// One walk per root, not one per file: the roots are deduped by `seen`.
/// A digest that cannot be taken is an error rather than a missing memo
/// entry, because a file whose root has no digest would get no key and
/// then look like an orphan to the `unreachable` filter -- which deletes.
#[partial]
def Build.collect_root_digests (tool : DigestTool) (files : List String) (seen : List String) (acc : List (Pair String String)) : IO (Result String (List (Pair String String))) :=
    match files {
        List.empty => return (ok acc),
        List.cons f rest => do {
            let r <- Build.mote_root_of f;
            if List.contains_by String.beq r seen
            then Build.collect_root_digests tool rest seen acc
            else do {
                let d <- Build.closure_digest_with tool r;
                match d {
                    err m => return (err m),
                    ok c => Build.collect_root_digests tool rest (List.append seen [r])
                        (List.append acc [Pair.pair r c])
                }
            }
        }
    }

/// The artifact keys for every named file, under every profile, for every
/// triple in `triples`.
///
/// One key per FILE, not per root: the key carries the file's own bytes
/// (`Build.artifact_key`), so two manifest-less files in one directory --
/// same root, same closure digest -- are two artifacts. Taking the file
/// digest here is what keeps this set complete, and completeness is the
/// only thing standing between a `gc` and the store.
///
/// The closure digest is looked up in the memo rather than taken here, and
/// the compiler digest is taken once by the caller; both are expensive (a
/// fork per tree, and a digest of the running binary). The file digest is
/// likewise taken once per file, so widening `triples` costs only the cheap
/// hash per extra triple.
#[partial]
def Build.collect_artifacts (tool : DigestTool) (compiler : String) (files : List String) (roots : List (Pair String String)) (triples : List String) (acc : List String) : IO (Result String (List String)) :=
    match files {
        List.empty => return (ok acc),
        List.cons f rest => do {
            let r <- Build.mote_root_of f;
            match Build.root_find r roots {
                // Unreachable while `collect_root_digests` walked the same
                // file list -- which is why it is a refusal and not a skip.
                Option.none => return (err ("no closure digest was derived for the root of " ++ f)),
                Option.some c => do {
                    let fd <- Build.file_digest_with tool f;
                    match fd {
                        err m => return (err m),
                        ok fh => Build.collect_artifacts { tool := tool, compiler := compiler,
                            files := rest, roots := roots, triples := triples,
                            acc := List.append acc (Build.artifact_keys fh c compiler triples) }
                    }
                }
            }
        }
    }

/// One file's artifact keys, one per (triple, profile). `profile_names` is the
/// only place that list is read.
pub def Build.artifact_keys (file_digest : String) (closure : String) (compiler : String) (triples : List String) : List String :=
    Build.artifact_keys_for { file_digest := file_digest, closure := closure,
        compiler := compiler, triples := triples, profiles := Build.profile_names }

#[partial]
def Build.artifact_keys_for (file_digest : String) (closure : String) (compiler : String) (triples : List String) (profiles : List String) : List String :=
    match triples {
        List.empty => List.empty,
        List.cons t rest =>
            List.append (Build.artifact_keys_for_one { file_digest := file_digest,
                    closure := closure, compiler := compiler, triple := t,
                    profiles := profiles })
                (Build.artifact_keys_for { file_digest := file_digest, closure := closure,
                    compiler := compiler, triples := rest, profiles := profiles })
    }

/// One file's keys for ONE triple, one per profile.
#[partial]
def Build.artifact_keys_for_one (file_digest : String) (closure : String) (compiler : String) (triple : String) (profiles : List String) : List String :=
    match profiles {
        List.empty => List.empty,
        List.cons p rest =>
            List.append [Build.artifact_key { file_digest := file_digest, closure := closure,
                    compiler := compiler, profile := p, triple := triple }]
                (Build.artifact_keys_for_one { file_digest := file_digest,
                    closure := closure, compiler := compiler, triple := triple,
                    profiles := rest })
    }

// --- the file system, a little ---

/// The names in `d`, or none when `d` is not a directory. A store that was
/// never written is not an error for any of these verbs, so the absent
/// case is `[]` rather than a failure.
#[partial]
def Build.dir_names (d : String) : IO (List String) := do {
    let there <- IO.is_dir (Path.path d);
    if there then do {
        let entries <- IO.list_dir (Path.path d);
        return (List.map Path.file_name entries)
    }
    else return List.empty
}

/// The paths that exist, in the order given.
#[partial]
def Build.present_paths (paths : List String) (acc : List String) : IO (List String) :=
    match paths {
        List.empty => return acc,
        List.cons p rest => do {
            let there <- IO.file_exists (Path.path p);
            if there then Build.present_paths rest (List.append acc [p])
            else Build.present_paths rest acc
        }
    }

/// Each path single-quoted, for the one shell this module runs.
/// `Proc.shell_quote` is what keeps a path with a space in it intact.
#[partial]
def Build.quote_each (paths : List String) (acc : List String) : List String :=
    match paths {
        List.empty => acc,
        List.cons p rest => Build.quote_each rest (List.append acc [Proc.shell_quote p])
    }

/// The total size of the paths that exist, in bytes, via one
/// `cat … | wc -c`.
///
/// `wc -c` fed by a pipe prints a bare number and a newline, so the whole
/// of the parsing is a `String.trim` and a `parse_i64` -- no column
/// splitting, no `stat`, no platform-specific flag. That matters because
/// `std` has no size or mtime primitive at all and adding one is out of
/// scope by decision, and because the alternatives (`stat -c` vs `stat -f`
/// vs `find -printf`) are GNU-or-BSD specific.
///
/// A size is REPORTED here, never a verdict: the only size rule anywhere
/// is `> 0`, and it exists because an artifact of zero bytes is a damaged
/// entry rather than a small one. So a failed parse answers `0`, which
/// that rule reads as not-ok -- the direction that flags rather than waves
/// through, which is the same rule a missing `wc` deserves.
#[partial]
def Build.present_size (paths : List String) : IO I64 := do {
    let present <- Build.present_paths paths List.empty;
    match present {
        List.empty => return 0,
        List.cons _ _ => do {
            let cmd : String :=
                "cat " ++ List.intercalate " " (Build.quote_each present List.empty) ++ " | wc -c";
            let r <- Proc.capture "sh" ["-c", cmd];
            match r {
                Pair.pair _code out => return (Build.size_of out)
            }
        }
    }
}

#[partial]
def Build.size_of (out : String) : I64 :=
    match parse_i64 (String.trim out) {
        Option.none => 0,
        Option.some n => n
    }

/// Remove one entry: BOTH files of an artifact, or a check entry's whole
/// directory.
///
/// All three kinds are matched even though `gc` only ever asks for two.
/// There is no exhaustiveness checking in this language, so a missing arm
/// would be compiled into nothing rather than reported -- and the arm that
/// would go missing is `test`, exactly the kind whose removal rules are
/// not decided yet.
#[partial]
pub def Build.remove_entry (target_dir : String) (e : Entry) (key : String) : IO I64 := do {
    match e {
        artifact => do {
            let _a <- exec_cmd "rm" ["-f", Build.store_path target_dir artifact key ""];
            exec_cmd "rm" ["-f", Build.artifact_ir_path target_dir key]
        },
        check => exec_cmd "rm" ["-rf", Build.entry_root_dir target_dir check ++ "/" ++ key],
        test => return 0
    }
}

#[partial]
def Build.remove_entries (target_dir : String) (e : Entry) (keys : List String) (n : I64) : IO I64 :=
    match keys {
        List.empty => return n,
        List.cons k rest => do {
            let _rc <- Build.remove_entry target_dir e k;
            Build.remove_entries target_dir e rest (n + 1)
        }
    }

// --- clean ---

/// `monad clean` and `monad clean --all`.
///
/// The profile directories to remove are spelled as "every directory under
/// `<target-dir>` that is not one of the four kinds" rather than as the
/// two profile names. The set of things that count as output is then
/// defined by exclusion from what counts as the store, which is the
/// direction that cannot delete an entry: a profile added later is cleaned
/// without a change here, and `store`/`check`/`test`/`db` are unreachable
/// to the remover by construction.
///
/// `--all` is the other verb -- `<target-dir>` itself goes, store
/// included. With no global store yet that is the only honest meaning the
/// flag can have: there is nothing to keep across it.
#[partial]
pub def Build.clean_run (target_dir : String) (all : Bool) : IO I64 := do {
    let there <- IO.is_dir (Path.path target_dir);
    if Bool.not there then do {
        IO.println ("clean: nothing to remove -- " ++ target_dir ++ " does not exist");
        return 0
    }
    else if all then do {
        IO.println ("clean --all: removing " ++ target_dir ++ " (the store included)");
        let rc <- exec_cmd "rm" ["-rf", target_dir];
        if rc == 0 then return 0
        else do {
            IO.println ("clean --all: rm failed with status " ++ I64.to_string rc);
            return 1
        }
    }
    else do {
        let names <- Build.dir_names target_dir;
        let outputs : List String := List.filter Build.is_output_dir names;
        let gone <- Build.remove_each target_dir outputs 0;
        if gone == 0 then do {
            IO.println ("clean: nothing to remove under " ++ target_dir ++ " (no output directories)");
            return 0
        }
        else do {
            IO.println ("clean: removed " ++ I64.to_string gone ++ " output director(ies): "
                ++ List.intercalate " " outputs);
            IO.println ("clean: the store is untouched (" ++ target_dir ++ "/{store,check,test})");
            return 0
        }
    }
}

#[partial]
def Build.remove_each (target_dir : String) (names : List String) (n : I64) : IO I64 :=
    match names {
        List.empty => return n,
        List.cons name rest => do {
            let rc <- exec_cmd "rm" ["-rf", target_dir ++ "/" ++ name];
            if rc == 0 then Build.remove_each target_dir rest (n + 1)
            else Build.remove_each target_dir rest n
        }
    }

// --- what an entry IS: the walk `ls` and `verify` share ---

/// One entry as the two listing verbs see it.
///
/// `ok` and `detail` are decided where the entry is looked at, once, so
/// that `ls` and `verify` cannot disagree about what complete means.
pub type EntryView {
    entry_view (kind : String) (key : String) (size : I64) (ok : Bool) (detail : String),
}

/// The artifact pair's verdict, from the facts about it.
///
/// One decision in one place: `ok` is never computed separately from the
/// sentence that explains it, so a `verify` can never call an entry good
/// while printing something that reads as damaged.
pub def Build.artifact_state (has_bin : Bool) (has_ir : Bool) (size : I64) : Pair Bool String :=
    if Bool.not has_bin then Pair.pair false "missing the artifact itself"
    else if Bool.not has_ir then Pair.pair false "missing its IR (an artifact is a pair)"
    else if I64.gt size 0 then Pair.pair true "bin+ir"
    else Pair.pair false "empty"

/// A check entry's verdict, with the extra rule its READER applies:
/// `errors` must parse as a number, because that is exactly what
/// `Build.check_entry_read` requires before it will serve an entry. So an
/// entry this calls good is one a hit can actually replay -- which is the
/// property a `verify` exists to assert.
pub def Build.check_state (has_out : Bool) (has_errors : Bool) (errors_ok : Bool) : Pair Bool String :=
    if Bool.not has_out then Pair.pair false "missing out"
    else if Bool.not has_errors then Pair.pair false "missing errors"
    else if Bool.not errors_ok then Pair.pair false "errors is not a number"
    else Pair.pair true "out+errors"

/// Whether `<path>` exists and holds a number. Written as its own
/// question rather than folded into `check_state` so the caller states the
/// three facts about an entry the same way for both kinds.
#[partial]
def Build.errors_parse (path : String) : IO Bool := do {
    let raw <- Build.read_leaf (Path.path path);
    return (match raw {
        Option.none => false,
        Option.some text => match parse_i64 (String.trim text) {
            Option.none => false,
            Option.some _n => true
        }
    })
}

/// Every entry under both populated kind directories, artifacts first.
///
/// `<target-dir>/test/` and `db/` are deliberately NOT walked: they have
/// no writer, so nothing in them is an entry this build system can
/// describe, and the summary below says so rather than printing an empty
/// column for them.
#[partial]
pub def Build.entry_views (target_dir : String) : IO (List EntryView) := do {
    let names_a <- Build.dir_names (Build.entry_root_dir target_dir artifact);
    let names_c <- Build.dir_names (Build.entry_root_dir target_dir check);
    let arts <- Build.artifact_views target_dir names_a List.empty List.empty;
    let chks <- Build.check_views (Build.entry_root_dir target_dir check) names_c List.empty;
    return (List.append arts chks)
}

#[partial]
def Build.artifact_views (target_dir : String) (names : List String) (seen : List String) (acc : List EntryView) : IO (List EntryView) :=
    match names {
        List.empty => return acc,
        List.cons name rest => do {
            let k := Build.artifact_name_key name;
            match k {
                Option.none => Build.artifact_views target_dir rest seen acc,
                Option.some key => Build.artifact_seen target_dir rest seen acc key
            }
        }
    }

#[partial]
def Build.artifact_seen (target_dir : String) (names : List String) (seen : List String) (acc : List EntryView) (key : String) : IO (List EntryView) := do {
    if List.contains_by String.beq key seen
    then Build.artifact_views target_dir names seen acc
    else do {
        let v <- Build.artifact_view target_dir key;
        Build.artifact_views target_dir names (List.append seen [key]) (List.append acc [v])
    }
}

#[partial]
def Build.artifact_view (target_dir : String) (key : String) : IO EntryView := do {
    let bin : String := Build.store_path target_dir artifact key "";
    let ir : String := Build.artifact_ir_path target_dir key;
    let has_bin <- IO.file_exists (Path.path bin);
    let has_ir <- IO.file_exists (Path.path ir);
    let size <- Build.present_size [bin, ir];
    match Build.artifact_state has_bin has_ir size {
        Pair.pair ok detail => return (EntryView.entry_view "artifact" key size ok detail)
    }
}

#[partial]
def Build.check_views (root : String) (names : List String) (seen : List String) : IO (List EntryView) :=
    match names {
        List.empty => return List.empty,
        List.cons name rest => do {
            let k := Build.key_of name;
            match k {
                Option.none => Build.check_views root rest seen,
                Option.some key => Build.check_seen root rest seen key
            }
        }
    }

#[partial]
def Build.check_seen (root : String) (names : List String) (seen : List String) (key : String) : IO (List EntryView) := do {
    if List.contains_by String.beq key seen
    then Build.check_views root names seen
    else do {
        let v <- Build.check_view root key;
        let rest <- Build.check_views root names (List.append seen [key]);
        return (List.append [v] rest)
    }
}

#[partial]
def Build.check_view (root : String) (key : String) : IO EntryView := do {
    let out_path : String := Build.check_entry_leaf root key "out";
    let errors_path : String := Build.check_entry_leaf root key "errors";
    let has_out <- IO.file_exists (Path.path out_path);
    let has_errors <- IO.file_exists (Path.path errors_path);
    let errors_ok <- Build.errors_parse errors_path;
    let size <- Build.present_size [out_path, errors_path];
    match Build.check_state has_out has_errors errors_ok {
        Pair.pair ok detail => return (EntryView.entry_view "check" key size ok detail)
    }
}

// --- the views, read ---

/// The kind of one view, for counting. A selector rather than a field
/// access at the call site: a `#[test]` def that reads a field of a
/// single-constructor type compiles to a def whose return type is the
/// FIELD's type when the runner is the compiled one, which is a
/// self-hosted-only miscompile -- so the access stays in here, where it
/// has a declared return type.
pub def Build.view_kind (v : EntryView) : String :=
    match v {
        EntryView.entry_view kind _key _size _ok _detail => kind
    }

/// Whether one view is an artifact rather than a check result.
pub def Build.view_is_artifact (v : EntryView) : Bool :=
    String.beq (Build.view_kind v) "artifact"

/// Whether one view is a check result.
pub def Build.view_is_check (v : EntryView) : Bool :=
    String.beq (Build.view_kind v) "check"

/// Whether one view failed its own completeness rule.
pub def Build.view_not_ok (v : EntryView) : Bool :=
    match v {
        EntryView.entry_view _kind _key _size ok _detail => Bool.not ok
    }

/// The sentence that explains one view -- the same reason `view_kind` and
/// `view_not_ok` are selectors and not field accesses.
pub def Build.view_detail (v : EntryView) : String :=
    match v {
        EntryView.entry_view _kind _key _size _ok detail => detail
    }

/// The key of one view, whole.
pub def Build.view_key (v : EntryView) : String :=
    match v {
        EntryView.entry_view _kind key _size _ok _detail => key
    }

/// One listing line: kind, short key, bytes, and the verdict's own
/// sentence.
///
/// No column alignment is attempted -- `std` has no padding helper, and
/// inventing one for a listing would be the tail wagging the dog. The
/// fields are separated by two spaces, which is enough for `grep` and for
/// a human reading a screen. The key is truncated to 8 characters because
/// a whole sha256 is unreadable and the first 8 are enough to find the
/// file; `verify`'s failure lines print the whole one.
pub def Build.view_line (v : EntryView) : String :=
    match v {
        EntryView.entry_view kind key size _ok detail =>
            kind ++ "  " ++ String.slice key 0 8 ++ "  " ++ I64.to_string size ++ " B  " ++ detail
    }

/// The same line with the whole key and no size -- what `verify` prints
/// for an entry that failed, where the point is that a reader can go and
/// look at the file without a second command.
pub def Build.view_fail_line (v : EntryView) : String :=
    match v {
        EntryView.entry_view kind key _size _ok detail =>
            kind ++ "  " ++ key ++ "  " ++ detail
    }

#[partial]
def Build.print_views (views : List EntryView) : IO I64 :=
    match views {
        List.empty => return 0,
        List.cons v rest => do {
            IO.println (Build.view_line v);
            Build.print_views rest
        }
    }

#[partial]
def Build.print_failures (views : List EntryView) : IO I64 :=
    match views {
        List.empty => return 0,
        List.cons v rest => do {
            let _x <- Build.print_if_bad v;
            Build.print_failures rest
        }
    }

#[partial]
def Build.print_if_bad (v : EntryView) : IO I64 := do {
    if Build.view_not_ok v then IO.println ("FAIL  " ++ Build.view_fail_line v)
    else return unit;
    return 0
}

/// The sentence both listing verbs end with: what is here, and what is not
/// here yet.
#[partial]
def Build.print_kind_note (target_dir : String) : IO I64 := do {
    IO.println ("  (" ++ target_dir ++ "/test and db have no writer yet, so nothing in them is listed)");
    return 0
}

/// One summary line, shared by both verbs so the counts cannot differ.
#[partial]
def Build.print_tally (verb : String) (views : List EntryView) : IO I64 := do {
    let arts : I64 := List.length (List.filter Build.view_is_artifact views);
    let chks : I64 := List.length (List.filter Build.view_is_check views);
    let bad : I64 := List.length (List.filter Build.view_not_ok views);
    IO.println (verb ++ ": " ++ I64.to_string arts ++ " artifact(s), " ++ I64.to_string chks
        ++ " check entry(ies), " ++ I64.to_string bad ++ " incomplete");
    return bad
}

/// `monad store ls`: one line per entry, then a summary.
#[partial]
pub def Build.store_ls (target_dir : String) : IO I64 := do {
    let views <- Build.entry_views target_dir;
    let _p <- Build.print_views views;
    let _n <- Build.print_kind_note target_dir;
    let _bad <- Build.print_tally "ls" views;
    IO.println "ls: a human-readable name per entry belongs in db/<hash>.json, which has no writer yet";
    return 0
}

/// `monad store verify`: re-derive what each entry claims, and exit
/// non-zero on any failure.
///
/// **What it can check is bounded by what an entry records, and an entry
/// records nothing about its own provenance.** `store/<hash>` holds no
/// note of which mote, profile or triple produced it; `check/<hash>` holds
/// no note of which FILE it is a result for. So this is a STRUCTURAL
/// check -- the pair is complete, the leaves are readable, an artifact is
/// not empty -- and it says so rather than implying the key was
/// re-derived. (The plan's layout had `db/<hash>.json` for exactly this,
/// and it has no writer yet.)
///
/// Reachability -- "does this key still follow from the current tree" --
/// is what `gc` derives, and it does it from the other end: the sources
/// rather than the store.
///
/// A `verify` that only printed would not be the tool the plan's risk
/// section promises for settling a suspected false hit, so any failed
/// entry makes this exit 1.
#[partial]
pub def Build.store_verify (target_dir : String) : IO I64 := do {
    let views <- Build.entry_views target_dir;
    let _p <- Build.print_failures views;
    let _n <- Build.print_kind_note target_dir;
    let bad <- Build.print_tally "verify" views;
    IO.println "verify: structural only -- an entry records neither the file nor the sources that produced it, so this checks that an entry is complete and readable, not that its key is the right key";
    if I64.gt bad 0 then return 1
    else return 0
}

// --- gc ---

/// The name whose removal takes one directory entry of `store/` with it.
///
/// The `.ll` is stripped unconditionally, and that is NOT the question
/// `Build.artifact_name_key` asks. That one asks "is this an entry?", and
/// must reject a legacy slug so that `store ls` lists entries rather than
/// junk. This one asks "what would removing this name remove?", and must
/// answer for EVERY name -- because a name `gc` cannot describe is a name
/// `gc` leaves behind forever, and the legacy slugs are precisely the
/// entries that most need reclaiming. A `gc` that used the key test here
/// would have been a `gc` that never reclaims them: it would report a
/// store of orphans and then spare them all.
///
/// A LONE `<hash>.ll` -- the IR of an artifact whose binary is already
/// gone -- normalizes to `<hash>` so that `remove_entry` takes the `.ll`
/// with it, rather than trying to remove a `<hash>.ll.ll` that never
/// existed and leaving the real file in place.
pub def Build.droppable_name (name : String) : String :=
    Build.strip_ir_suffix name

/// Every name under one kind directory, normalized, deduplicated, in the
/// order given.
///
/// **Unfiltered on purpose, and that is the whole of `gc`'s reach.** A
/// name that is not a key is not thereby safe: the store is this tool's
/// own directory, and anything in it that the current tree cannot reach
/// has no reader and never will. The one thing that must not happen is
/// the opposite -- a name kept because it was unrecognized -- so the
/// filter is "would `gc` remove this", not "is this well-formed".
///
/// One def for both kinds because both answer the same way: `check/`'s
/// entries are directories named by their key, so the normalizer is the
/// identity there and `rm -rf <check>/<name>` is the removal.
#[partial]
pub def Build.droppable_names (names : List String) (seen : List String) : IO (List String) :=
    match names {
        List.empty => return seen,
        List.cons n rest => Build.droppable_names rest (Build.add_key (Build.droppable_name n) seen)
    }

/// `seen` with `k` in it, once.
pub def Build.add_key (k : String) (seen : List String) : List String :=
    if List.contains_by String.beq k seen then seen else List.append seen [k]

/// What `keep` does not cover, in the order given. Written out rather than
/// as `List.filter` over a partially applied two-argument def, for the
/// same reason.
#[partial]
pub def Build.unreachable (keep : List String) (have : List String) : List String :=
    match have {
        List.empty => List.empty,
        List.cons k rest =>
            if List.contains_by String.beq k keep
            then Build.unreachable keep rest
            else List.append [k] (Build.unreachable keep rest)
    }

/// `monad gc [<path>...]` with `--apply` to remove.
///
/// Dry run by default, and the counts are printed either way: seeing them
/// BEFORE an `--apply` is the same information at the moment it is worth
/// something. A `gc` that removed first and reported afterwards would have
/// nothing to show but its own decision.
///
/// The reachable set comes from the FILES the caller named (the workspace
/// when none were), so entries recorded for a file outside that set are
/// dropped. That is the safe direction -- a dropped entry costs a re-check
/// and can never serve a stale answer -- and it is why the counts are
/// printed before anything is removed.
///
/// `triples` is the set of targets an artifact may have been built for, not
/// one target: a build keys with the target it was given, so a `gc` holding
/// only the host's own triple classifies every cross-built artifact as
/// garbage and removes it. `TargetSpec.keep_triples` is what the CLI supplies.
#[partial]
pub def Build.gc_run (files : List String) (target_dir : String) (triples : List String) (apply : Bool) : IO I64 := do {
    let reach <- Build.reach_of files target_dir triples;
    match reach {
        Reach.refused m => do {
            IO.println ("gc: refusing to remove anything -- " ++ m);
            IO.println "gc: a gc removes only what the current tree cannot reach, so an incomplete reachable set would delete the store itself";
            IO.println ("gc: nothing was removed, " ++ target_dir ++ " is untouched");
            return 1
        },
        Reach.known artifacts checks compiler => do {
            let names_a <- Build.dir_names (Build.entry_root_dir target_dir artifact);
            let names_c <- Build.dir_names (Build.entry_root_dir target_dir check);
            let have_a <- Build.droppable_names names_a List.empty;
            let have_c <- Build.droppable_names names_c List.empty;
            let drop_a : List String := Build.unreachable artifacts have_a;
            let drop_c : List String := Build.unreachable checks have_c;
            let _n <- Build.print_kind_note target_dir;
            IO.println ("gc: keyed with compiler " ++ Build.short_key compiler
                ++ " -- an entry is unreachable when this compiler, or the named files' closure, differs from what wrote it");
            IO.println ("gc: " ++ I64.to_string (List.length files) ++ " file(s) named -> "
                ++ I64.to_string (List.length artifacts) ++ " artifact key(s) and "
                ++ I64.to_string (List.length checks) ++ " check key(s) reachable");
            IO.println ("gc: unreachable here: " ++ I64.to_string (List.length drop_a) ++ " artifact(s) of "
                ++ I64.to_string (List.length have_a) ++ " present, " ++ I64.to_string (List.length drop_c)
                ++ " check entry(ies) of " ++ I64.to_string (List.length have_c) ++ " present");
            if Bool.not apply then do {
                IO.println "gc: dry run -- nothing was removed; re-run with --apply to remove them";
                return 0
            }
            else do {
                let na <- Build.remove_entries target_dir artifact drop_a 0;
                let nc <- Build.remove_entries target_dir check drop_c 0;
                IO.println ("gc: removed " ++ I64.to_string (na + nc) ++ " entry(ies) from " ++ target_dir);
                return 0
            }
        }
    }
}
