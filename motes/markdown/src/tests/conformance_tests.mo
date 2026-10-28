// The conformance gate: every CommonMark 0.31.2 example, rendered and
// compared byte for byte.
//
// The printed report is the iteration loop -- see `conformance_support.mo`.
use lib::tests::conformance_support {
    Markdown.SpecExample, Markdown.SpecReport, Markdown.load_spec,
    Markdown.print_report, Markdown.report_failed, Markdown.report_ok,
    Markdown.phase1_sections, Markdown.phase2_sections, Markdown.phase3_sections,
    Markdown.report_total, Markdown.run_examples,
    Markdown.run_sections, Markdown.section_counts, Markdown.spec_path,
}

def Markdown.run_spec (r : Result String (List Markdown.SpecExample)) : IO Bool :=
    match r {
        Result.err e => do {
            let _ <- IO.write_stderr (String.concat e "\n");
            return false
        },
        Result.ok examples => do {
            let report : Markdown.SpecReport := Markdown.run_examples examples 20i64;
            let _ <- Markdown.print_report report;
            return (Markdown.report_ok report)
        }
    }

#[test]
def test_commonmark_conformance : IO Bool := do {
    let r <- Markdown.load_spec Markdown.spec_path;
    Markdown.run_spec r
}

def Markdown.run_spec_sections
    (r : Result String (List Markdown.SpecExample)) (sections : List String) : IO Bool :=
    match r {
        Result.err e => do {
            let _ <- IO.write_stderr (String.concat e "\n");
            return false
        },
        Result.ok examples => do {
            let report : Markdown.SpecReport := Markdown.run_sections examples sections 100i64;
            let _ <- Markdown.print_report report;
            return (Markdown.report_ok report)
        }
    }

/// The Phase 1 gate: leaf blocks, exactly.
#[test]
def test_phase1_leaf_sections : IO Bool := do {
    let r <- Markdown.load_spec Markdown.spec_path;
    Markdown.run_spec_sections r Markdown.phase1_sections
}

/// The Phase 2 gate: container structure, exactly.
#[test]
def test_phase2_structure_sections : IO Bool := do {
    let r <- Markdown.load_spec Markdown.spec_path;
    Markdown.run_spec_sections r Markdown.phase2_sections
}

/// The Phase 3 gate: inline structure, exactly.
#[test]
def test_phase3_inline_sections : IO Bool := do {
    let r <- Markdown.load_spec Markdown.spec_path;
    Markdown.run_spec_sections r Markdown.phase3_sections
}
