/// Resolution for the editor: an identifier under the cursor resolved to the
/// declaration it names, with a detail to show and a place to go.
///
/// THE POINT OF THIS FILE IS THE KEY AGREEMENT. `nav_at` resolves a name
/// through `scope_resolve_name` and then looks the result up in the file's
/// declaration-range table BY NAME -- and the two sides agree only because
/// both derive that name from the same `Def.name` (`ScopeDef.name` is
/// registered from it, `DeclRange.name` is rendered from it). Nothing in
/// the type system enforces that, and if it ever stopped being true the
/// failure would be silent: a hover with no range, every jump in the file
/// degrading to "found nothing" while still resolving correctly. So the
/// assertions below are deliberately about the PAIR -- a name AND a line --
/// rather than about either alone.
///
/// The two halves are pinned separately too. A def that resolves but has no
/// range (the cross-module case, built by hand below) proves the name half
/// does not depend on the range half; the `detail` assertions prove the
/// signature comes from `ScopeData.def_sigs` and not from `ScopeDef.sig`,
/// which is `Term.hole` for every def in the corpus and would render a
/// hover reading `_` (the plan's Risk #6).
///
/// VACUITY IS THE HAZARD HERE, more than in most files, because "resolved
/// nothing" and "resolved to nothing" are the same value. Every test that
/// asserts an absence asserts a PRESENCE in the same test -- the same name
/// on a scope that works resolves, and the empty answer is compared against
/// that -- so a scope that failed to build cannot pass for an editor that
/// correctly found no target.
///
/// THE `IO Bool` TESTS USE THE STATEMENT FORM of `let` (`let x : T := e;`),
/// never `let … in`: inside a `do` block the latter aborts the parse at the
/// NEXT top-level declaration rather than where it was written, which is a
/// recorded trap in this repository and an expensive one to diagnose. The
/// pure helpers above them have no `do` block, so they use `in` freely.
///
/// Field reads go through typed accessor defs (`nt_*`), never inline, per
/// this repository's recorded `#[test]` plus struct-field codegen hazard.
/// The `nt_` prefix keeps whole-program scope clean.
use std::test {Test.write_fixture}
use lib::module {
  DeclRange, ModuleInfo, ModuleInfoCache, RangedFileCheck,
  check_file_cached_from_source_ranged, module_info_cache_empty, module_info_cache_insert,
  parse_all_decls, ranged_file_ranges, ranged_file_scope,
}
use lib::navigation {
  NavTarget, nav_at, nav_at_checked, nav_target_detail, nav_target_file, nav_target_kind,
  nav_target_name, nav_target_range,
}
use parsec::core {fail, success}
use lib::pretty {show_term}
use lib::scope {build_scope_from_decls}
use lib::types {
  Identifier, Location, ModulePath, Scope, ScopeData, SourceRange, Term,
}
open IO {println}
use std::process {exec_cmd, process_id}

// --- Accessors: one field read each, one explicit return type each ---

def nt_start (r : SourceRange) : Location := r.start

def nt_end (r : SourceRange) : Location := r.end

def nt_off (l : Location) : I64 := l.offset

def nt_line (l : Location) : I64 := l.line

def nt_kind (t : NavTarget) : String := nav_target_kind t

def nt_name (t : NavTarget) : String := nav_target_name t

def nt_detail (t : NavTarget) : String := nav_target_detail t

/// The start line of a target's range, or -1 when it has none -- a line no
/// real source has, so an absent range fails an equality assertion instead
/// of quietly satisfying one.
def nt_line_of (t : NavTarget) : I64 :=
    match nav_target_range t {
        Option.none => 0 - 1,
        Option.some r => nt_line (nt_start r),
    }

def nt_end_line_of (t : NavTarget) : I64 :=
    match nav_target_range t {
        Option.none => 0 - 1,
        Option.some r => nt_line (nt_end r),
    }

def nt_start_off_of (t : NavTarget) : I64 :=
    match nav_target_range t {
        Option.none => 0 - 1,
        Option.some r => nt_off (nt_start r),
    }

def nt_end_off_of (t : NavTarget) : I64 :=
    match nav_target_range t {
        Option.none => 0 - 1,
        Option.some r => nt_off (nt_end r),
    }

def nt_file_text (t : NavTarget) : String :=
    match nav_target_file t {
        Option.none => "<none>",
        Option.some f => f,
    }

/// Whether a resolution found nothing, as a `Bool` a test can `&&` into one
/// assertion -- an `Option` inside a `do` block would have to be matched,
/// and a match cannot be spelled inside a `let` there.
def nt_absent (o : Option NavTarget) : Bool :=
    match o {
        Option.none => true,
        Option.some _t => false,
    }

def nt_scope_text (f : RangedFileCheck) : String :=
    match ranged_file_scope f {
        Option.none => "<no scope>",
        Option.some _s => "<scope>",
    }

/// `yes`/`no`, for one control flag in a failure message: the `Show`
/// instance would drag an import in for the word "yes".
def nt_yes_no (b : Bool) : String := if b then "yes" else "no"

/// The names in a range table, comma separated, for an assertion about an
/// OUTLINE rather than one entry of it.
def nt_names_text (rs : List DeclRange) : String :=
    nt_names_go rs ""

def nt_names_go (rs : List DeclRange) (acc : String) : String :=
    match rs {
        List.empty => acc,
        List.cons dr rest =>
            let name : String := dr.name in
            if String.beq acc ""
            then nt_names_go rest name
            else nt_names_go rest (acc ++ "," ++ name),
    }

/// A resolution rendered for a failure message: the whole target, so a
/// failing assertion prints what was found instead of only that it was
/// wrong.
def nt_text (t : NavTarget) : String :=
    nt_name t ++ " (" ++ nt_kind t ++ ") detail=[" ++ nt_detail t ++ "] line="
        ++ I64.to_string (nt_line_of t) ++ " file=" ++ nt_file_text t

// --- Fixtures ---

/// One of each kind a name can reach: a def, an inductive, and a class --
/// one per line, so a line assertion names a line a reader can count.
/// Line 1 is `alpha` (bytes 0-29, newline at 30), so line 2 starts at 31,
/// line 3 (`type Color`) at 57 and line 4 (`class Show`) at 83.
///
/// `beta` calls `alpha` and is asserted on by nothing: it keeps the fixture
/// a plausible file, and a fixture that only ever declared and never used
/// would not notice a resolver reaching for the wrong map.
def nav_source : String :=
    "def alpha (x : I64) : I64 := x\ndef beta : I64 := alpha 1\ntype Color { red, green }\nclass Show A { def show (a : A) : String }\n"

/// A good declaration followed by a malformed one, which is the shape the
/// lenient top-level walk truncates: it keeps `ok_first` and stops. Written
/// this way round deliberately -- a file whose FIRST declaration is broken
/// truncates to nothing, and an assertion about the outline would then pass
/// for the wrong reason.
def nav_truncated_source : String := "def ok_first : I64 := 1\ndef bad ((( :=\n"

/// `Identifier` in a TYPE position, not only as the prefix of
/// `Identifier.id`: a qualified use does not count as using an import, so a
/// file whose only mention of the type is `Identifier.id` is reported as
/// importing it unused, the trap `toolkit`'s `Json` import records.
def nt_id (s : String) : Identifier := Identifier.id s

/// The same for `Term`, whose only other use here is the `Term.hole`
/// constructor in one assertion.
def nt_show_term (t : Term) : String := show_term t

/// The module and the file a def in another module is declared in, for the
/// hand-built cache below.
def nt_other_module : ModulePath := ModulePath.mk (List.cons (nt_id "other") List.empty)

def nt_here_module : ModulePath := ModulePath.mk (List.cons (nt_id "here") List.empty)

def nt_other_file : String := "/w/other.mo"

/// `process_id` in the path, not a fixed name: the sweep runs sharded and a
/// shared /tmp path collides across parallel runs.
def nav_dir : String := "/tmp/monad_navigation_" ++ I64.to_string process_id

/// The buffer on disk and its check, in one def each -- the ranged check
/// takes the text in memory, and the file on disk is what a dependency walk
/// would read, so both are needed.
#[partial]
def nt_probe_path (name : String) : String := nav_dir ++ "/" ++ name

#[partial]
def nt_check (name : String) (src : String) : IO RangedFileCheck := do {
    exec_cmd "mkdir" ["-p", nav_dir];
    let path : String := nt_probe_path name;
    let _w <- Test.write_fixture (Path.path path) src;
    let checked <- check_file_cached_from_source_ranged module_info_cache_empty path src false;
    return checked
}

// --- The elaborated in-file case, end to end ---

/// The whole chain: a check of a buffer, the scope and range table it
/// carries out, and a resolution against both. This is the test that would
/// fail if `RangedFileCheck` stopped carrying the scope (the field exists
/// only for this) or if the two name spellings drifted apart.
#[test]
def test_a_def_resolves_to_its_own_declaration : IO Bool := do {
    let checked <- nt_check "nav_probe.mo" nav_source;
    println ("outline: " ++ nt_names_text (ranged_file_ranges checked));
    match nav_at_checked checked "alpha" {
        Option.none => do { println "NO TARGET for a def declared in this file"; return false },
        Option.some t => do {
            println ("alpha -> " ++ nt_text t);
            return (String.beq (nt_name t) "alpha"
                && String.beq (nt_kind t) "def"
                && I64.beq (nt_line_of t) 1
                && I64.beq (nt_start_off_of t) 0
                && I64.lt (nt_start_off_of t) (nt_end_off_of t)
                && String.beq (nt_file_text t) "<none>")
        },
    }
}

/// The detail is a real signature, not the hole sentinel. `ScopeDef.sig` is
/// `Term.hole` for every def in the corpus, so a hover built on it renders
/// `def alpha : _` -- plausible-looking, silent, and wrong for every def in
/// every file. Comparing against the hole's own rendering is what makes
/// that failure visible rather than merely absent.
#[test]
def test_a_defs_detail_is_a_real_signature : IO Bool := do {
    let checked <- nt_check "nav_probe_sig.mo" nav_source;
    match nav_at_checked checked "alpha" {
        Option.none => do { println "VACUOUS: alpha did not resolve"; return false },
        Option.some t => do {
            println ("alpha detail: " ++ nt_detail t);
            let hole_text : String := nt_show_term Term.hole;
            return (String.starts_with "def alpha : " (nt_detail t)
                && Bool.not (String.beq (nt_detail t) ("def alpha : " ++ hole_text)))
        },
    }
}

/// A type resolves, and its target's range is the TYPE's declaration rather
/// than the position of the name -- which is what an outline jump needs,
/// since a `type` declaration's range covers its constructors too.
#[test]
def test_a_type_resolves_to_its_declaration : IO Bool := do {
    let checked <- nt_check "nav_probe_type.mo" nav_source;
    match nav_at_checked checked "Color" {
        Option.none => do { println "NO TARGET for a type declared in this file"; return false },
        Option.some t => do {
            println ("Color -> " ++ nt_text t);
            return (String.beq (nt_name t) "Color"
                && String.beq (nt_kind t) "type"
                && I64.beq (nt_line_of t) 3
                && I64.beq (nt_end_line_of t) 3
                && String.starts_with "type Color" (nt_detail t))
        },
    }
}

/// A CONSTRUCTOR resolves to the type that declares it, and this is the
/// assertion that pins the mapping rather than the resolution: `red` is not
/// a declaration in the file at all, so a target for it can only have come
/// from finding the inductive whose constructor list holds it, and the
/// range must be that inductive's -- the same line the `Color` test
/// asserts.
#[test]
def test_a_constructor_resolves_to_its_type : IO Bool := do {
    let checked <- nt_check "nav_probe_ctor.mo" nav_source;
    match nav_at_checked checked "red" {
        Option.none => do { println "NO TARGET for a constructor"; return false },
        Option.some t => do {
            println ("red -> " ++ nt_text t);
            return (String.beq (nt_kind t) "constructor"
                && String.beq (nt_name t) "Color"
                && I64.beq (nt_line_of t) 3)
        },
    }
}

/// A class resolves, and its detail is `show_class`'s rendering rather than
/// a def's `def <name> : <type>` shape -- the two vocabularies meeting in
/// one field.
#[test]
def test_a_class_resolves_to_its_declaration : IO Bool := do {
    let checked <- nt_check "nav_probe_class.mo" nav_source;
    match nav_at_checked checked "Show" {
        Option.none => do { println "NO TARGET for a class"; return false },
        Option.some t => do {
            println ("Show -> " ++ nt_text t);
            return (String.beq (nt_name t) "Show"
                && String.beq (nt_kind t) "class"
                && I64.beq (nt_line_of t) 4
                && String.starts_with "class Show" (nt_detail t))
        },
    }
}

/// An identifier that names nothing has no target -- and the same file's
/// `alpha` DOES, in the same test, so a scope that failed to build cannot
/// masquerade as a correct "found nothing". This is the answer an editor
/// gets for every partially typed word, so it is the state the server is in
/// most of the time.
#[test]
def test_an_unknown_identifier_has_no_target : IO Bool := do {
    let checked <- nt_check "nav_probe_missing.mo" nav_source;
    let control : Option NavTarget := nav_at_checked checked "alpha";
    let missing : Option NavTarget := nav_at_checked checked "no_such_name_anywhere";
    println ("control resolved: " ++ nt_yes_no (Bool.not (nt_absent control)));
    return (Bool.not (nt_absent control) && nt_absent missing)
}

// --- The cross-module file answer, built by hand ---

/// A def declared in ANOTHER module, resolved against a cache that knows
/// which file that module is.
///
/// The scope and the cache are both built by hand because the in-memory
/// check cannot produce this shape: a probe buffer has no `use`, so nothing
/// is ever loaded and the cache stays empty. That makes this test the only
/// cover for the file half of a target -- and the scope it builds resolves
/// just as a real one does, so a name reaching the wrong map would fail
/// here too.
#[test]
def test_a_def_in_another_module_answers_its_file : IO Bool := do {
    match parse_all_decls "def far : I64 := 1\n" {
        ParseResult.fail _e => do { println "VACUOUS: the fixture did not parse"; return false },
        ParseResult.success _rem decls => do {
            let sd : ScopeData := build_scope_from_decls nt_other_module decls;
            let no_parent : Option Scope := Option.none;
            let scope : Scope := { module_id := nt_here_module, scope := sd, parent := no_parent, incomplete_match_ok := false };
            let no_ranges : List DeclRange := List.empty;
            let info : ModuleInfo := ModuleInfo.mk nt_other_module nt_other_file decls;
            let cache : ModuleInfoCache := module_info_cache_insert nt_other_module info module_info_cache_empty;
            match nav_at scope no_ranges cache "far" {
                Option.none => do { println "NO TARGET for a def in another module"; return false },
                Option.some t => do {
                    println ("far -> " ++ nt_text t);
                    return (String.beq (nt_name t) "far"
                        && String.beq (nt_kind t) "def"
                        && String.beq (nt_file_text t) nt_other_file
                        && I64.beq (nt_line_of t) (0 - 1)
                        && String.starts_with "def far : " (nt_detail t))
                },
            }
        },
    }
}

// --- A buffer that does not compile ---

/// A truncated buffer keeps its outline and loses its scope, and both
/// halves of that are deliberate.
///
/// The outline survives because the declarations the lenient walk did read
/// are real declarations at real positions -- and a file with a syntax
/// error is exactly when a user wants the symbol picker to keep working.
/// The scope does not, because elaboration is what builds one and it never
/// ran, so a hover or a jump in a file that does not compile answers
/// nothing rather than resolving against a half-built scope.
///
/// Both are asserted, so neither can quietly become the other, and the
/// outline is asserted by NAME rather than by count: one declaration is
/// what this fixture truncates to, and a count of one would also be
/// satisfied by the wrong declaration.
#[test]
def test_a_truncated_buffer_keeps_its_outline : IO Bool := do {
    let checked <- nt_check "nav_probe_truncated.mo" nav_truncated_source;
    let names : String := nt_names_text (ranged_file_ranges checked);
    println ("truncated outline: " ++ names ++ ", " ++ nt_scope_text checked);
    return (String.beq names "ok_first"
        && nt_absent (nav_at_checked checked "ok_first")
        && String.beq (nt_scope_text checked) "<no scope>")
}
