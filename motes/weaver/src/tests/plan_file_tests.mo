/// Plan-file round-trip and tolerance tests (no IO): the frontmatter
/// render/parse pair, a malformed block that keeps the body, a legacy
/// plan with no frontmatter, and the slug.
use init::string {}
use weaver::plan_file {PlanDoc, PlanMeta, PlanParse, PlanFile.parse, PlanFile.render, PlanFile.slug}

def meta_of : PlanMeta :=
    { title := "Fix the widget", session := "s-1", created := "2026-10-31",
      updated := "2026-10-31", status := "ready", model := "openrouter/x" }

def doc_of : PlanDoc :=
    { meta := meta_of, body := "# Plan\n\n- do it\n" }

#[test]
def test_plan_file_round_trip_title : Bool :=
    let p : PlanParse := PlanFile.parse (PlanFile.render doc_of) in
    p.doc.meta.title == "Fix the widget"

#[test]
def test_plan_file_round_trip_session : Bool :=
    let p : PlanParse := PlanFile.parse (PlanFile.render doc_of) in
    p.doc.meta.session == "s-1"

#[test]
def test_plan_file_round_trip_status : Bool :=
    let p : PlanParse := PlanFile.parse (PlanFile.render doc_of) in
    p.doc.meta.status == "ready"

#[test]
def test_plan_file_round_trip_model : Bool :=
    let p : PlanParse := PlanFile.parse (PlanFile.render doc_of) in
    p.doc.meta.model == "openrouter/x"

#[test]
def test_plan_file_round_trip_body : Bool :=
    let p : PlanParse := PlanFile.parse (PlanFile.render doc_of) in
    String.trim p.doc.body == String.trim "# Plan\n\n- do it\n"

#[test]
def test_plan_file_round_trip_has_no_warning : Bool :=
    let p : PlanParse := PlanFile.parse (PlanFile.render doc_of) in
    match p.warning { Option.none => true, Option.some _ => false }

#[test]
def test_plan_file_keeps_the_body_when_yaml_is_bad : Bool :=
    let p : PlanParse := PlanFile.parse "---\ntitle: [unclosed\n---\n# Still here\n" in
    String.contains p.doc.body "# Still here"
        && match p.warning { Option.some _ => true, Option.none => false }

#[test]
def test_plan_file_without_frontmatter_uses_the_heading : Bool :=
    let p : PlanParse := PlanFile.parse "# Hello\n\nbody\n" in
    p.doc.meta.title == "Hello" && String.contains p.doc.body "body"

#[test]
def test_plan_slug : Bool :=
    PlanFile.slug "Fix: the Widget!" == "fix-the-widget"

#[test]
def test_empty_slug_falls_back : Bool :=
    PlanFile.slug "***" == "plan"
