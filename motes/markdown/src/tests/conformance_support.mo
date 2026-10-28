// The CommonMark conformance harness: load the spec fixture, render every
// example with the conformance options, and report by section.
//
// Tests only report pass/fail, so the printed report IS the iteration loop:
// the first failures carry the example number, section, source, expected and
// actual HTML.
use init::string {}
use parsec::core {is_empty}
use std::list {List.length}
use std::map {BTreeMap}
use std::path {Path}
use std::io {IO.read_file}
use std::stream {StreamError}
use json::json {
    Json, Json.parse, Json.ParseError, Json.get_array, Json.get_object,
    Json.get_str, Json.get_num, Json.get_num_i64, Json.object_get,
}
use lib::scan {Markdown.char_width}
use lib::tests::render {Markdown.render}

pub def Markdown.spec_path : String :=
    "motes/markdown/testdata/commonmark-0.31.2.spec.json"

pub struct Markdown.SpecExample {
    number : I64,
    section : String,
    markdown : String,
    expected : String
}

pub struct Markdown.SpecFailure {
    number : I64,
    section : String,
    markdown : String,
    expected : String,
    actual : String
}

pub struct Markdown.SpecReport {
    passed : I64,
    failed : I64,
    total : I64,
    failures : List Markdown.SpecFailure,
    sections : List (Pair String (Pair I64 I64))
}

def Markdown.mk_example (number : I64) (section : String) (markdown : String) (expected : String) : Markdown.SpecExample :=
    let e : Markdown.SpecExample :=
        { number := number, section := section, markdown := markdown, expected := expected } in e

def Markdown.mk_failure
    (number : I64) (section : String) (markdown : String) (expected : String) (actual : String)
    : Markdown.SpecFailure :=
    let f : Markdown.SpecFailure :=
        { number := number, section := section, markdown := markdown,
          expected := expected, actual := actual } in f

def Markdown.mk_report
    (passed : I64) (failed : I64) (total : I64)
    (failures : List Markdown.SpecFailure)
    (sections : List (Pair String (Pair I64 I64))) : Markdown.SpecReport :=
    let r : Markdown.SpecReport :=
        { passed := passed, failed := failed, total := total,
          failures := failures, sections := sections } in r

// ─── JSON access ───

def Markdown.str_field (name : String) (obj : BTreeMap String Json) : Option String :=
    match Json.object_get name obj {
        Option.some v =>
            match Json.get_str v {
                Result.ok s => Option.some s,
                Result.err _ => Option.none
            },
        Option.none => Option.none
    }

def Markdown.int_field (name : String) (obj : BTreeMap String Json) : Option I64 :=
    match Json.object_get name obj {
        Option.some v =>
            match Json.get_num_i64 (Json.get_num v) {
                Result.ok n => Option.some n,
                Result.err _ => Option.none
            },
        Option.none => Option.none
    }

/// One example, or `none` when a field is missing or mistyped.
pub def Markdown.example_of (j : Json) : Option Markdown.SpecExample :=
    match Json.get_object j {
        Result.err _ => Option.none,
        Result.ok obj =>
            match Markdown.int_field "example" obj {
                Option.none => Option.none,
                Option.some number =>
                    match Markdown.str_field "section" obj {
                        Option.none => Option.none,
                        Option.some section =>
                            match Markdown.str_field "markdown" obj {
                                Option.none => Option.none,
                                Option.some md =>
                                    match Markdown.str_field "html" obj {
                                        Option.none => Option.none,
                                        Option.some html =>
                                            Option.some (Markdown.mk_example number section md html)
                                    }
                            }
                    }
            }
    }

#[partial]
def Markdown.examples_of (items : List Json) (acc : List Markdown.SpecExample) : List Markdown.SpecExample :=
    match items {
        List.empty => List.reverse acc,
        List.cons j rest =>
            match Markdown.example_of j {
                Option.some e => Markdown.examples_of rest (List.cons e acc),
                Option.none => Markdown.examples_of rest acc
            }
    }

pub def Markdown.examples_of_json (j : Json) : Result String (List Markdown.SpecExample) :=
    match Json.get_array j {
        Result.err e => Result.err e,
        Result.ok items => Result.ok (Markdown.examples_of items List.empty)
    }

/// Read and decode the fixture. Every failure names the path and the reason.
/// Tests run from the repository root, which is what makes the path work.
pub def Markdown.load_spec (path : String) : IO (Result String (List Markdown.SpecExample)) := do {
    let r <- IO.read_file (Path.path path);
    Markdown.loaded_spec path r
}

def Markdown.loaded_spec
    (path : String) (r : Result StreamError String) : IO (Result String (List Markdown.SpecExample)) :=
    match r {
        Result.err e =>
            IO.pure (Result.err
                (String.concat "cannot read spec fixture " (String.concat path (String.concat ": " e.message)))),
        Result.ok text =>
            Markdown.parsed_spec text
    }

def Markdown.parsed_spec (text : String) : IO (Result String (List Markdown.SpecExample)) :=
    match Json.parse text {
        Result.err e =>
            IO.pure (Result.err
                (String.concat "spec fixture is not JSON ("
                    (String.concat (Json.ParseError.to_string e) ")"))),
        Result.ok j => IO.pure (Markdown.examples_of_json j)
    }

// ─── Comparing ───

/// Unescape exactly the three references our text escaper does not emit but
/// cmark does: `&quot;`, `&#x27;` and `&#39;`. Every rule here is a renderer
/// bug; when `Html.parse` lands the harness compares trees and drops this.
#[partial]
def Markdown.normalize_go (s : String) (acc : List String) : String :=
    if is_empty s
    then String.concat_list (List.reverse acc)
    else
        match String.get s 0 {
            Option.some b =>
                if U8.beq b 38u8
                then
                    if String.starts_with "&quot;" s
                    then Markdown.normalize_go (String.drop 6i64 s) (List.cons "\"" acc)
                    else if String.starts_with "&#x27;" s
                    then Markdown.normalize_go (String.drop 6i64 s) (List.cons "'" acc)
                    else if String.starts_with "&#39;" s
                    then Markdown.normalize_go (String.drop 5i64 s) (List.cons "'" acc)
                    else Markdown.normalize_go (String.drop 1i64 s) (List.cons "&" acc)
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.normalize_go (String.drop w s) (List.cons (String.slice s 0 w) acc),
            Option.none => String.concat_list (List.reverse acc)
        }

pub def Markdown.normalize_html (s : String) : String :=
    Markdown.normalize_go s List.empty

// ─── Section tallies ───

def Markdown.section_tally (ok : Bool) (passed : I64) (total : I64) : Pair I64 I64 :=
    if ok
    then Pair.pair (I64.add passed 1i64) (I64.add total 1i64)
    else Pair.pair passed (I64.add total 1i64)

#[partial]
def Markdown.bump_section_go
    (section : String) (ok : Bool)
    (rest : List (Pair String (Pair I64 I64)))
    (seen : List (Pair String (Pair I64 I64)))
    : List (Pair String (Pair I64 I64)) :=
    match rest {
        List.empty =>
            List.append (List.reverse seen)
                (List.cons (Pair.pair section (Markdown.section_tally ok 0i64 0i64)) List.empty),
        List.cons entry tail =>
            match entry {
                Pair.pair name counts =>
                    if String.beq name section
                    then
                        match counts {
                            Pair.pair passed total =>
                                List.append (List.reverse seen)
                                    (List.cons
                                        (Pair.pair name (Markdown.section_tally ok passed total))
                                        tail)
                        }
                    else Markdown.bump_section_go section ok tail (List.cons entry seen)
            }
    }

pub def Markdown.bump_section
    (section : String) (ok : Bool) (sections : List (Pair String (Pair I64 I64)))
    : List (Pair String (Pair I64 I64)) :=
    Markdown.bump_section_go section ok sections List.empty

// ─── Running ───

/// Run examples, keeping at most `max_report` failures.
#[partial]
def Markdown.run_examples_go
    (examples : List Markdown.SpecExample) (max_report : I64)
    (passed : I64) (failed : I64) (total : I64)
    (failures : List Markdown.SpecFailure)
    (sections : List (Pair String (Pair I64 I64))) : Markdown.SpecReport :=
    match examples {
        List.empty => Markdown.mk_report passed failed total (List.reverse failures) sections,
        List.cons e rest =>
            let actual : String := Markdown.normalize_html (Markdown.render e.markdown) in
            let expected : String := Markdown.normalize_html e.expected in
            let ok : Bool := String.beq actual expected in
            let kept : List Markdown.SpecFailure :=
                if Bool.and (Bool.not ok) (I64.lt (List.length failures) max_report)
                then List.cons (Markdown.mk_failure e.number e.section e.markdown expected actual) failures
                else failures in
            Markdown.run_examples_go rest max_report
                (if ok then I64.add passed 1i64 else passed)
                (if ok then failed else I64.add failed 1i64)
                (I64.add total 1i64)
                kept
                (Markdown.bump_section e.section ok sections)
    }

pub def Markdown.run_examples (examples : List Markdown.SpecExample) (max_report : I64) : Markdown.SpecReport :=
    Markdown.run_examples_go examples max_report 0i64 0i64 0i64 List.empty List.empty

// ─── Section filters (phase gates) ───

#[partial]
def Markdown.member (name : String) (wanted : List String) : Bool :=
    match wanted {
        List.empty => false,
        List.cons w rest => Bool.or (String.beq w name) (Markdown.member name rest)
    }

#[partial]
def Markdown.filter_sections
    (examples : List Markdown.SpecExample) (wanted : List String)
    (acc : List Markdown.SpecExample) : List Markdown.SpecExample :=
    match examples {
        List.empty => List.reverse acc,
        List.cons e rest =>
            if Markdown.member e.section wanted
            then Markdown.filter_sections rest wanted (List.cons e acc)
            else Markdown.filter_sections rest wanted acc
    }

pub def Markdown.run_sections
    (examples : List Markdown.SpecExample) (wanted : List String) (max_report : I64)
    : Markdown.SpecReport :=
    Markdown.run_examples (Markdown.filter_sections examples wanted List.empty) max_report

/// The leaf-block sections Phase 1 must pass outright.
pub def Markdown.phase1_sections : List String :=
    [ "Tabs", "Thematic breaks", "ATX headings", "Setext headings",
      "Indented code blocks", "Fenced code blocks", "Paragraphs", "Blank lines" ]

/// The block-structure sections Phase 2 must pass outright.
pub def Markdown.phase2_sections : List String :=
    [ "Block quotes", "List items", "Lists", "Link reference definitions", "HTML blocks" ]

/// The inline sections Phase 3 must pass outright.
pub def Markdown.phase3_sections : List String :=
    [ "Backslash escapes", "Entity and numeric character references", "Code spans",
      "Emphasis and strong emphasis", "Links", "Images", "Autolinks", "Raw HTML",
      "Hard line breaks", "Soft line breaks", "Textual content", "Inlines",
      "Precedence" ]

// ─── Reading the report ───

pub def Markdown.report_ok (r : Markdown.SpecReport) : Bool :=
    Bool.and (I64.beq r.failed 0i64) (I64.beq r.passed r.total)

pub def Markdown.report_total (r : Markdown.SpecReport) : I64 := r.total

pub def Markdown.report_passed (r : Markdown.SpecReport) : I64 := r.passed

pub def Markdown.report_failed (r : Markdown.SpecReport) : I64 := r.failed

pub def Markdown.section_counts (r : Markdown.SpecReport) : List (Pair String (Pair I64 I64)) := r.sections

pub def Markdown.failure_count (r : Markdown.SpecReport) : I64 := List.length r.failures

pub def Markdown.first_failure (r : Markdown.SpecReport) : Option Markdown.SpecFailure :=
    match r.failures {
        List.empty => Option.none,
        List.cons f _ => Option.some f
    }

// ─── Printing ───

pub def Markdown.print_failure (f : Markdown.SpecFailure) : IO Unit := do {
    let _ <- IO.println
        (String.concat "FAIL example "
            (String.concat (I64.to_string f.number) (String.concat " [" (String.concat f.section "]"))));
    let _ <- IO.println (String.concat "  markdown: " (Markdown.show_src f.markdown));
    let _ <- IO.println (String.concat "  expected: " (Markdown.show_src f.expected));
    let _ <- IO.println (String.concat "  actual:   " (Markdown.show_src f.actual));
    IO.pure unit
}

/// A quoted rendering, so a failing example's whitespace stays visible.
pub def Markdown.show_src (s : String) : String :=
    String.concat "\"" (String.concat s "\"")

#[partial]
def Markdown.print_failures (failures : List Markdown.SpecFailure) : IO Unit :=
    match failures {
        List.empty => IO.pure unit,
        List.cons f rest => do {
            let _ <- Markdown.print_failure f;
            Markdown.print_failures rest
        }
    }

#[partial]
def Markdown.print_sections (sections : List (Pair String (Pair I64 I64))) : IO Unit :=
    match sections {
        List.empty => IO.pure unit,
        List.cons entry rest =>
            match entry {
                Pair.pair name counts =>
                    match counts {
                        Pair.pair passed total => do {
                            let _ <- IO.println
                                (String.concat "  "
                                    (String.concat name
                                        (String.concat ": "
                                            (String.concat (I64.to_string passed)
                                                (String.concat "/" (I64.to_string total))))));
                            Markdown.print_sections rest
                        }
                    }
            }
    }

pub def Markdown.print_report (r : Markdown.SpecReport) : IO Unit := do {
    let _ <- Markdown.print_failures r.failures;
    let _ <- Markdown.print_sections r.sections;
    IO.println
        (String.concat "TOTAL "
            (String.concat (I64.to_string r.passed)
                (String.concat "/" (String.concat (I64.to_string r.total)
                    (String.concat " passed, " (String.concat (I64.to_string r.failed) " failed"))))))
}
