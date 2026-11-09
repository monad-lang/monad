/// Plan files and the plan repo: the frontmatter render/parse pair, a
/// malformed block that keeps the body, a legacy plan, the slug and the
/// project key, the repo resolution, the changelog, and -- against a
/// scratch directory -- capture, revision, status changes and listing.
use init::string {}
use std::list {List.intercalate, List.length}
use std::path {Path}
use std::process {process_id, exec_cmd, Proc.capture}
use std::io {IO.read_file, IO.file_exists, IO.write_file}
use weaver::store {StoreState}
use weaver::plan_file {
    PlanDoc, PlanMeta, PlanMeta.empty, PlanParse, PlanFile.parse, PlanFile.render, PlanFile.slug, PlanFile.project_key,
    PlanFile.with_entry, PlanFile.revise_body, PlanFile.split_changelog, PlanFile.read, PlanFile.linked,
    PlanRepo, PlanRepo.resolve, PlanRepo.capture, PlanRepo.set_status, PlanRepo.list, PlanRepo.list_all, PlanRepo.add_session,
    PlanSettings, PlanSettings.empty, PlanEntry, PlanEntry.line, Stored,
}

def meta_of : PlanMeta :=
    { PlanMeta.empty with title := "Fix the widget", created := "2026-10-31", updated := "2026-10-31", status := "approved",
        model := "openrouter/x", project := "/src/app", sessions := ["s-1", "s-2"], completion := 40, next_action := "write the test" }

def doc_of : PlanDoc :=
    { meta := meta_of, body := "# Plan\n\n- do it\n" }

def round : PlanParse := PlanFile.parse (PlanFile.render doc_of)

#[test]
def test_plan_file_round_trip_title : Bool :=
    let p : PlanParse := round in
    p.doc.meta.title == "Fix the widget"

#[test]
def test_plan_file_round_trip_status : Bool :=
    let p : PlanParse := round in
    p.doc.meta.status == "approved"

#[test]
def test_plan_file_round_trip_model : Bool :=
    let p : PlanParse := round in
    p.doc.meta.model == "openrouter/x"

#[test]
def test_plan_file_round_trip_project : Bool :=
    let p : PlanParse := round in
    p.doc.meta.project == "/src/app"

#[test]
def test_plan_file_round_trip_sessions : Bool :=
    let p : PlanParse := round in
    let ss : List String := p.doc.meta.sessions in
    List.intercalate "," ss == "s-1,s-2"

#[test]
def test_plan_file_round_trip_progress : Bool :=
    let p : PlanParse := round in
    p.doc.meta.completion == 40 && p.doc.meta.next_action == "write the test"

#[test]
def test_plan_file_round_trip_body : Bool :=
    let p : PlanParse := round in
    String.trim p.doc.body == String.trim "# Plan\n\n- do it\n"

#[test]
def test_plan_file_round_trip_has_no_warning : Bool :=
    let p : PlanParse := round in
    match p.warning { Option.none => true, Option.some _ => false }

#[test]
def test_colons_and_stamps_survive_the_yaml : Bool :=
    let m : PlanMeta := { meta_of with title := "Fix: the widget's edge", updated := "2026-11-09T23:30:12Z" } in
    let d : PlanDoc := { meta := m, body := "b\n" } in
    let p : PlanParse := PlanFile.parse (PlanFile.render d) in
    p.doc.meta.title == "Fix: the widget's edge" && p.doc.meta.updated == "2026-11-09T23:30:12Z"

#[test]
def test_a_legacy_session_key_is_one_session : Bool :=
    let p : PlanParse := PlanFile.parse "---\ntitle: Old\nsession: s-9\nstatus: ready\n---\nbody\n" in
    List.intercalate "," p.doc.meta.sessions == "s-9"

#[test]
def test_a_missing_status_is_draft : Bool :=
    let p : PlanParse := PlanFile.parse "---\ntitle: Old\n---\nbody\n" in
    p.doc.meta.status == "draft"

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

// ── the project key and the repo ───────────────────────────────────────

#[test]
def test_the_project_key_is_stable_and_named : Bool :=
    let k : String := PlanFile.project_key "/src/My App" in
    k == PlanFile.project_key "/src/My App"
        && String.starts_with "my-app-" k
        && String.length k == String.length "my-app-" + 12

#[test]
def test_two_checkouts_named_alike_get_two_keys : Bool :=
    Bool.not (PlanFile.project_key "/a/app" == PlanFile.project_key "/b/app")

def settings_repo (repo : String) (dir : Option String) : PlanSettings :=
    { PlanSettings.empty with repo := Option.some repo, dir := dir }

def root_or (r : Option PlanRepo) : String :=
    match r { Option.none => "", Option.some x => x.root }

def dir_or (r : Option PlanRepo) : String :=
    match r { Option.none => "", Option.some x => x.dir }

#[test]
def test_the_default_repo_is_under_home : Bool :=
    let r : Option PlanRepo := PlanRepo.resolve Option.none (Option.some "/home/u") PlanSettings.empty (Option.some "/src/app") in
    root_or r == "/home/u/.weaver/plans"
        && dir_or r == String.concat "/home/u/.weaver/plans/" (PlanFile.project_key "/src/app")

#[test]
def test_the_env_wins_over_the_setting : Bool :=
    let r : Option PlanRepo := PlanRepo.resolve (Option.some "/plans") (Option.some "/home/u") (settings_repo "~/p" Option.none) Option.none in
    root_or r == "/plans" && dir_or r == "/plans/default"

#[test]
def test_a_setting_expands_home_and_the_project : Bool :=
    let home : Option PlanRepo := PlanRepo.resolve Option.none (Option.some "/home/u") (settings_repo "~/p" Option.none) Option.none in
    let rel : Option PlanRepo := PlanRepo.resolve Option.none (Option.some "/home/u") (settings_repo "plans" (Option.some "implementations")) (Option.some "/src/monad") in
    root_or home == "/home/u/p"
        && root_or rel == "/src/monad/plans"
        && dir_or rel == "/src/monad/plans/implementations"

#[test]
def test_nothing_names_a_repo_without_home : Bool :=
    match PlanRepo.resolve Option.none Option.none PlanSettings.empty Option.none {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_commit_defaults_on : Bool :=
    match PlanRepo.resolve (Option.some "/p") Option.none PlanSettings.empty Option.none {
        Option.none => false,
        Option.some r => r.commit,
    }

// ── the changelog ──────────────────────────────────────────────────────

#[test]
def test_an_entry_starts_the_changelog : Bool :=
    let b : String := PlanFile.with_entry "# Plan\n\nbody\n" "2026-11-09" "approved" in
    String.contains b "## Changelog\n\n- **2026-11-09**: approved" && String.starts_with "# Plan" b

#[test]
def test_entries_are_newest_first : Bool :=
    let b1 : String := PlanFile.with_entry "# Plan\n" "2026-11-08" "first" in
    let b2 : String := PlanFile.with_entry b1 "2026-11-09" "second" in
    I64.lt (String.find_last b2 "second") (String.find_last b2 "first")

#[test]
def test_a_revision_keeps_the_changelog : Bool :=
    let old : String := PlanFile.with_entry "# Old\n" "2026-11-08" "approved" in
    let b : String := PlanFile.revise_body old "# New\n\nsteps\n" in
    String.starts_with "# New" b && String.contains b "approved" && Bool.not (String.contains b "# Old")

// ── capture, revise, status, list (scratch directory) ──────────────────

def scratch (name : String) : String :=
    String.concat "/tmp/weaver_plans_" (String.concat (I64.to_string process_id) (String.concat "_" name))

def fresh_dir (d : String) : IO Unit := do {
    let _ <- exec_cmd "rm" ["-rf", d];
    let _ <- exec_cmd "mkdir" ["-p", d];
    IO.pure unit
}

def session_in (base : String) (id : String) : IO StoreState := do {
    let dir : String := String.concat base (String.concat "/sessions/" id);
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let st : StoreState := { root := Path.path (String.concat base "/sessions"), dir := Path.path dir, id := id };
    IO.pure st
}

def repo_in (base : String) (commit : Bool) : PlanRepo :=
    let r : PlanRepo := { root := String.concat base "/plans", dir := String.concat base "/plans/app", commit := commit } in
    r

def path_or (s : Stored) : String :=
    match s.path { Option.none => "", Option.some p => p }

#[test]
def test_a_capture_then_a_revision_is_one_file : IO Bool := do {
    let base : String := scratch "revise";
    fresh_dir base;
    let st <- session_in base "s-1";
    let r : PlanRepo := repo_in base false;
    let a <- PlanRepo.capture r st "m" "/src/app" "# First plan\n\nstep one\n";
    let b <- PlanRepo.capture r st "m" "/src/app" "# Second plan\n\nstep two\n";
    let es <- PlanRepo.list r;
    let d <- PlanFile.read (path_or b);
    IO.pure (path_or a == path_or b && List.length es == 1 && revised_ok d)
}

def revised_ok (d : Option PlanDoc) : Bool :=
    match d {
        Option.none => false,
        Option.some doc => doc.meta.title == "Second plan" && doc.meta.status == "draft"
            && doc.meta.project == "/src/app" && String.contains doc.body "step two",
    }

#[test]
def test_the_session_is_linked_to_its_plan : IO Bool := do {
    let base : String := scratch "link";
    fresh_dir base;
    let st <- session_in base "s-1";
    let r : PlanRepo := repo_in base false;
    let a <- PlanRepo.capture r st "m" "" "# A plan\n";
    let linked <- PlanFile.linked st;
    match linked {
        Option.none => IO.pure false,
        Option.some p => IO.pure (p == path_or a),
    }
}

#[test]
def test_a_status_change_is_logged : IO Bool := do {
    let base : String := scratch "status";
    fresh_dir base;
    let st <- session_in base "s-1";
    let r : PlanRepo := repo_in base false;
    let a <- PlanRepo.capture r st "m" "" "# A plan\n";
    let res <- PlanRepo.set_status r (path_or a) "approved" "";
    let d <- PlanFile.read (path_or a);
    match d {
        Option.none => IO.pure false,
        Option.some doc => IO.pure (doc.meta.status == "approved" && String.contains doc.body "status: approved"),
    }
}

#[test]
def test_a_second_session_is_recorded_once : IO Bool := do {
    let base : String := scratch "sessions";
    fresh_dir base;
    let st <- session_in base "s-1";
    let r : PlanRepo := repo_in base false;
    let a <- PlanRepo.capture r st "m" "" "# A plan\n";
    let _ <- PlanRepo.add_session r (path_or a) "s-2";
    let _ <- PlanRepo.add_session r (path_or a) "s-2";
    let d <- PlanFile.read (path_or a);
    match d {
        Option.none => IO.pure false,
        Option.some doc => IO.pure (List.length doc.meta.sessions == 2),
    }
}

#[test]
def test_two_sessions_make_two_plans_listed_newest_first : IO Bool := do {
    let base : String := scratch "list";
    fresh_dir base;
    let s1 <- session_in base "s-1";
    let s2 <- session_in base "s-2";
    let r : PlanRepo := repo_in base false;
    let a <- PlanRepo.capture r s1 "m" "" "# Older\n";
    let b <- PlanRepo.capture r s2 "m" "" "# Newer\n";
    let _ <- PlanRepo.set_status r (path_or b) "approved" "";
    let es <- PlanRepo.list r;
    let all <- PlanRepo.list_all r;
    IO.pure (List.length es == 2 && List.length all == 2 && first_title es == "Newer" && Bool.not (path_or a == path_or b))
}

def first_title (es : List PlanEntry) : String :=
    match es {
        List.cons e _ => match e.doc { Option.some d => d.meta.title, Option.none => "" },
        List.empty => "",
    }

#[test]
def test_an_unreadable_plan_is_still_listed : IO Bool := do {
    let base : String := scratch "unreadable";
    fresh_dir base;
    let r : PlanRepo := repo_in base false;
    let _ <- exec_cmd "mkdir" ["-p", r.dir];
    let _ <- exec_cmd "touch" [String.concat r.dir "/2026-11-09-empty.md"];
    let es <- PlanRepo.list r;
    IO.pure (List.length es == 1 && first_unreadable es)
}

def first_unreadable (es : List PlanEntry) : Bool :=
    match es {
        List.cons e _ => String.contains (PlanEntry.line 1 e) "(unreadable)",
        List.empty => false,
    }

#[test]
def test_a_git_plan_repo_gets_a_commit : IO Bool := do {
    let base : String := scratch "git";
    fresh_dir base;
    let st <- session_in base "s-1";
    let r : PlanRepo := repo_in base true;
    let _ <- exec_cmd "mkdir" ["-p", r.root];
    let _ <- exec_cmd "git" ["-C", r.root, "init", "-q"];
    let _ <- exec_cmd "git" ["-C", r.root, "config", "user.email", "t@example.invalid"];
    let _ <- exec_cmd "git" ["-C", r.root, "config", "user.name", "t"];
    let _ <- exec_cmd "git" ["-C", r.root, "config", "commit.gpgsign", "false"];
    let a <- PlanRepo.capture r st "m" "" "# Tracked\n";
    let log <- Proc.capture "git" ["-C", r.root, "log", "--format=%s"];
    match log {
        Pair.pair code out => IO.pure (code == 0 && String.contains out "plan: Tracked -- draft" && Bool.not (String.is_empty (path_or a))),
    }
}

#[test]
def test_a_hand_written_plan_keeps_its_other_keys : IO Bool := do {
    let base : String := scratch "extra";
    fresh_dir base;
    let r : PlanRepo := repo_in base false;
    let _ <- exec_cmd "mkdir" ["-p", r.dir];
    let path : String := String.concat r.dir "/2026-11-01-by-hand.md";
    let _ <- IO.write_file (Path.path path) "---\ntitle: By hand\nstatus: planning\npriority: high\ndepends_on: [weaver]\n---\n\n# By hand\n";
    let _ <- PlanRepo.set_status r path "done" "";
    let text <- IO.read_file (Path.path path);
    match text {
        Result.err _ => IO.pure false,
        Result.ok t => IO.pure (String.contains t "priority: high" && String.contains t "weaver" && String.contains t "status: done"),
    }
}

#[test]
def test_the_repo_root_markdown_is_not_a_plan : IO Bool := do {
    let base : String := scratch "rootmd";
    fresh_dir base;
    let st <- session_in base "s-1";
    let r : PlanRepo := repo_in base false;
    let _ <- PlanRepo.capture r st "m" "" "# Real plan\n";
    let _ <- IO.write_file (Path.path (String.concat r.root "/PLANS.md")) "# Index\n";
    let all <- PlanRepo.list_all r;
    IO.pure (List.length all == 1 && first_title all == "Real plan")
}
