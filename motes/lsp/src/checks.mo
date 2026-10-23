/// What the checker knows about each open document: the last check of its text,
/// and the module cache those checks share.
///
/// THIS IS THE WHOLE REASON A LONG-LIVED SERVER IS WORTH HAVING. A cold `check`
/// reloads and re-elaborates a file's entire dependency closure, and parsing is most
/// of that cost; a server that paid it per keystroke would be slower than the command
/// line it replaces. `ModuleInfoCache` is what stands between the two: it holds every
/// module loaded so far in this session, so the second check of a file loads nothing,
/// and the hundredth check of a file in a project the server has been running against
/// all morning starts from a cache that is already complete. The cache is threaded
/// FORWARD rather than copied: `check_file_cached_from_source_ranged` answers the
/// cache it used, extended with whatever it had to load, and that value is what is
/// stored back here.
///
/// IT IS A SEPARATE MODULE FROM `documents.mo`, AND THE TWO ARE ABOUT DIFFERENT
/// THINGS. `documents.mo` holds what the CLIENT says each buffer contains -- a view
/// that moves on every keystroke, including keystrokes that change nothing a checker
/// sees. This holds what the CHECKER derived from some revision of it, which moves
/// only when a check runs. Keeping them apart is what lets the two have different
/// lifetimes: closing a document ends the client's interest in that text while the
/// module cache it warmed stays, for every other file in the project.
///
/// THE TEXT A CHECK WAS COMPUTED FROM IS STORED NEXT TO IT, for the reason
/// `toolkit::docstore` stores a version next to its text: the two are useful only
/// together. A warm recheck is worth having only if what it reuses is an answer about
/// the text NOW in the buffer, and "is this check current?" has a cheap answer when
/// the text is here (`checkstore_is_current`) and no answer at all when it is not. It
/// also makes skipping unchanged text a property of THIS store rather than a flag
/// every caller must remember to consult: a caller that skips the flag re-checks
/// identical text and is merely slower, never wrong.
///
/// A DOCUMENT WITH NO PATH IS NOT CHECKED. The checker is handed a filesystem path
/// and walks it for dependencies, so an `untitled:` buffer has nothing to check
/// against and no dependencies to load. Nothing is recorded for it, which makes every
/// reader of this module answer "no check" -- the same state a document that was never
/// opened is in, and the honest one, rather than a check of an empty string that would
/// report a nonexistent file as clean.
///
/// NOTHING HERE WRITES TO STDOUT. The check path prints eagerly -- `IO.println`, one
/// destination -- and the rule this server lives under is that stdout carries protocol
/// frames and nothing else, so a printing path reached from the server turns a log
/// line into a malformed frame the client rejects. This module adds no printing; the
/// printing already inside the dependency walk is a real hazard with a named place in
/// the plan, not something a caller here can suppress.
use lang::module {
  ModuleInfoCache, RangedFileCheck, check_file_cached_from_source_ranged, module_info_cache_empty,
  ranged_file_cache,
}
use std::map {Map, BTreeMap, BTreeMap.to_list}
use toolkit::docstore {docstore_path_of_uri}

// --- One check ---

/// A check and the text it was computed from.
///
/// One struct rather than two maps because the two are never useful separately: a
/// check without its text cannot be told from a stale one, and the text alone is
/// already in `docstore` for every reader that wants only it.
pub struct Check {
  text : String,
  result : RangedFileCheck,
}

pub def check_text (c : Check) : String := c.text

pub def check_result (c : Check) : RangedFileCheck := c.result

// --- The store ---

/// Every open document's last check, and the module cache they share.
///
/// The cache is one value for the whole session rather than one per document: it is
/// the loaded closure of the PROJECT, not of a file, and a per-document cache would
/// re-load every shared dependency once per open buffer -- the cost this design exists
/// to avoid.
pub struct CheckStore {
  cache : ModuleInfoCache,
  checks : BTreeMap String Check,
}

/// The empty map, and the three operations on it, each with the map type in a
/// declared signature.
///
/// The same trap `toolkit::docstore`'s struct doc records in full: dictionary
/// passing is syntactic, a struct FIELD's declared type is not a carrier source
/// it reads, and `Map`'s class default is `HashMap` -- so
/// `CheckStore.mk ... Map.empty` built a HashMap inside a `BTreeMap String
/// Check` field, and `checkstore_count`'s explicit `BTreeMap.to_list` read it
/// as a BTreeMap. A typed parameter IS a source, so these pin it.
///
/// `checkstore_count` is the only reader that would have crashed, and no server
/// path calls it -- which is why the compiled server worked and the compiled
/// TESTS did not. Pinned anyway: the next `BTreeMap.*` call on the store would
/// have been a SIGSEGV in `monad_get_tag` with nothing pointing here.
#[partial]
def checkstore_no_checks : BTreeMap String Check := Map.empty

#[partial]
def checkstore_put (uri : String) (c : Check) (m : BTreeMap String Check) : BTreeMap String Check :=
  Map.insert uri c m

#[partial]
def checkstore_get (uri : String) (m : BTreeMap String Check) : Option Check := Map.lookup uri m

#[partial]
def checkstore_drop (uri : String) (m : BTreeMap String Check) : BTreeMap String Check :=
  Map.delete uri m

pub def checkstore_empty : CheckStore := CheckStore.mk module_info_cache_empty checkstore_no_checks

/// The shared module cache, for a caller that wants to load or elaborate something
/// else against the same warm state.
pub def checkstore_cache (s : CheckStore) : ModuleInfoCache := s.cache

/// The last check of a document, or nothing.
///
/// `Option.some` says a check EXISTS, not that it was clean: a check of a file with a
/// syntax error is a check, and the diagnostics it carries are the answer. A caller
/// that wants "clean" wants `ranged_file_diagnostics` of this.
pub def checkstore_lookup (uri : String) (s : CheckStore) : Option Check := checkstore_get uri s.checks

/// How many documents have a check. Nothing makes a decision from it; the shutdown
/// path's log line and tests are the readers.
pub def checkstore_count (s : CheckStore) : I64 := checkstore_count_go (BTreeMap.to_list s.checks) 0

#[partial]
def checkstore_count_go (cs : List (Pair String Check)) (acc : I64) : I64 :=
  match cs {
    List.empty => acc,
    List.cons _c rest => checkstore_count_go rest (I64.add acc 1),
  }

/// Whether the stored check for a document was computed from exactly this text.
///
/// `false` for a document with no check at all, which is the same answer as for a
/// stale one and deliberately so: a caller asking this wants to know whether it can
/// trust a result, and "there is no result" is not a yes.
#[partial]
pub def checkstore_is_current (uri : String) (text : String) (s : CheckStore) : Bool :=
  match checkstore_lookup uri s {
    Option.none => false,
    Option.some c => String.beq (check_text c) text,
  }

/// Check a document's text and record the result -- unless there is nothing to do.
///
/// The two reasons to do nothing are both decided by `checkstore_path`: no path to
/// check, or a check that already covers this text. Both answer the store unchanged,
/// so a caller does not have to tell "nothing to do" from "done" -- the state it wanted
/// is the state it gets.
///
/// The VERBOSE flag is false, and that is not a default left standing: this module's
/// whole output contract is that the protocol stream stays clean, and verbose output
/// on the check path goes to stdout.
#[partial]
pub def checkstore_recheck (uri : String) (text : String) (s : CheckStore) : IO CheckStore := do {
    match checkstore_path uri text s {
        Option.none => return s,
        Option.some path => do {
            let r <- check_file_cached_from_source_ranged (checkstore_cache s) path text false;
            return (checkstore_store uri text r s)
        },
    }
}

/// The path to check, or nothing when there is nothing to do.
///
/// One def for both reasons, so that "is there work?" is asked once and answered in
/// one place rather than in an `if` at each call site -- and so a future third reason
/// is one more arm here instead of a second condition at every caller.
#[partial]
def checkstore_path (uri : String) (text : String) (s : CheckStore) : Option String :=
  match docstore_path_of_uri uri {
    Option.none => Option.none,
    Option.some path =>
      if checkstore_is_current uri text s
      then Option.none
      else Option.some path,
  }

/// Record a check, taking the cache it answered as the store's new cache.
///
/// This one line is the warm-reuse property: the cache handed IN was the store's, and
/// the cache handed BACK has everything that check had to load added to it, so it is
/// strictly more complete than what it replaces. Dropping it on the floor -- storing
/// the old cache instead -- would leave the server re-loading the same dependencies
/// forever while every test still passed, which is why the property is stated here
/// rather than left to be inferred from the field assignment.
def checkstore_store (uri : String) (text : String) (r : RangedFileCheck) (s : CheckStore)
    : CheckStore :=
  CheckStore.mk (ranged_file_cache r) (checkstore_put uri (Check.mk text r) s.checks)

/// `didClose`: forget the document's check and keep the cache it warmed.
///
/// The asymmetry is the decision, and it is about what each thing is FOR. A check
/// answers questions about a text the client is showing -- hover, definition, a
/// squiggle -- and a closed document is in none of those positions, so holding one
/// check per file ever opened would grow without bound for a document nobody can ask
/// about. The cache is not about the document at all: it is the loaded closure of the
/// project, still true, still expensive to rebuild, and the next file the user opens
/// is the one that benefits from it.
///
/// So a reopened document is checked again from its new text, which is correct
/// regardless of what was dropped: `checkstore_is_current` compares text, so the skip
/// for unchanged text simply does not apply to a document whose check is gone.
pub def checkstore_close (uri : String) (s : CheckStore) : CheckStore :=
  CheckStore.mk (checkstore_cache s) (checkstore_drop uri s.checks)
