use lib::release {*}

def opt_string_is (o : Option String) (v : String) : Bool :=
    match o {
        Option.some x => String.beq x v,
        Option.none => false,
    }

def first_release (rs : List Release.Info) : Option Release.Info :=
    match rs {
        List.empty => Option.none,
        List.cons r _ => Option.some r,
    }

def err_contains (r : Result String Release.Selection) (needle : String) : Bool :=
    match r {
        Result.err m => String.contains m needle,
        Result.ok _ => false,
    }

def sel_is (r : Result String Release.Selection) (platform : String) (asset : String) : Bool :=
    match r {
        Result.err _ => false,
        Result.ok s => String.beq s.platform platform && String.beq s.asset asset,
    }

def array_json : String := r#"[{"tag_name":"nightly-2026-10-19-abc1234","assets":[{"name":"monad-nightly-aarch64-linux","browser_download_url":"file:///r/monad-nightly-aarch64-linux"},{"name":"monad-src-aarch64-linux.tar.gz","browser_download_url":"file:///r/monad-src-aarch64-linux.tar.gz"},{"name":"monadup-aarch64-linux","browser_download_url":"file:///r/monadup-aarch64-linux"}]}]"#

def x86_json : String := r#"{"tag_name":"nightly-x","assets":[{"name":"monad-nightly-x86_64-linux","browser_download_url":"file:///r/monad-nightly-x86_64-linux"}]}"#

def neutral_src_json : String := r#"{"tag_name":"nightly-x","assets":[{"name":"monad-src.tar.gz","browser_download_url":"file:///r/monad-src.tar.gz"}]}"#

def no_sources_json : String := r#"{"tag_name":"nightly-x","assets":[{"name":"monadup-x86_64-linux","browser_download_url":"file:///r/monadup-x86_64-linux"}]}"#

#[test]
def test_parse_releases_latest : Bool :=
    match Release.parse_releases array_json {
        Result.err _ => false,
        Result.ok rs =>
            match Release.latest_nightly rs {
                Option.some r => String.beq r.tag "nightly-2026-10-19-abc1234",
                Option.none => false,
            },
    }

#[test]
def test_latest_nightly_skips_non_nightly : Bool :=
    let txt : String := r#"[{"tag_name":"v1.0.0","assets":[]},{"tag_name":"nightly-2","assets":[]}]"# in
    match Release.parse_releases txt {
        Result.err _ => false,
        Result.ok rs =>
            match Release.latest_nightly rs {
                Option.some r => String.beq r.tag "nightly-2",
                Option.none => false,
            },
    }

#[test]
def test_parse_single_release : Bool :=
    match Release.parse_release x86_json {
        Result.err _ => false,
        Result.ok r => String.beq r.tag "nightly-x",
    }

#[test]
def test_resolve_binary_exact_platform : Bool :=
    match Release.parse_releases array_json {
        Result.err _ => false,
        Result.ok rs =>
            match first_release rs {
                Option.none => false,
                Option.some r =>
                    sel_is (Release.resolve_binary "aarch64-linux" r)
                        "aarch64-linux" "monad-nightly-aarch64-linux",
            },
    }

#[test]
def test_resolve_binary_error_names_both : Bool :=
    match Release.parse_releases array_json {
        Result.err _ => false,
        Result.ok rs =>
            match first_release rs {
                Option.none => false,
                Option.some r =>
                    err_contains (Release.resolve_binary "riscv64-linux" r) "monad-nightly-riscv64-linux"
                        && err_contains (Release.resolve_binary "riscv64-linux" r) "monad-nightly-x86_64-linux",
            },
    }

#[test]
def test_resolve_binary_fallback : Bool :=
    match Release.parse_release x86_json {
        Result.err _ => false,
        Result.ok r =>
            match Release.resolve_binary "aarch64-linux" r {
                Result.err _ => false,
                Result.ok s =>
                    s.fallback
                        && String.beq s.platform "x86_64-linux"
                        && String.contains s.note "ships no monad-nightly-aarch64-linux",
            },
    }

#[test]
def test_resolve_monadup : Bool :=
    match Release.parse_releases array_json {
        Result.err _ => false,
        Result.ok rs =>
            match first_release rs {
                Option.none => false,
                Option.some r =>
                    sel_is (Release.resolve_monadup "aarch64-linux" r)
                        "aarch64-linux" "monadup-aarch64-linux",
            },
    }

#[test]
def test_resolve_sources_per_platform : Bool :=
    match Release.parse_releases array_json {
        Result.err _ => false,
        Result.ok rs =>
            match first_release rs {
                Option.none => false,
                Option.some r =>
                    match Release.resolve_binary "aarch64-linux" r {
                        Result.err _ => false,
                        Result.ok s =>
                            match Release.resolve_sources s r {
                                Result.err _ => false,
                                Result.ok url => opt_string_is url "file:///r/monad-src-aarch64-linux.tar.gz",
                            },
                    },
            },
    }

#[test]
def test_resolve_sources_neutral_fallback : Bool :=
    match Release.parse_release neutral_src_json {
        Result.err _ => false,
        Result.ok r =>
            let s : Release.Selection :=
                Release.selection "nightly-x" "x86_64-linux" "monad-nightly-x86_64-linux" "file:///r/monad-nightly-x86_64-linux" false "" in
            match Release.resolve_sources s r {
                Result.err _ => false,
                Result.ok url => opt_string_is url "file:///r/monad-src.tar.gz",
            },
    }

#[test]
def test_resolve_sources_absent_is_none : Bool :=
    match Release.parse_release no_sources_json {
        Result.err _ => false,
        Result.ok r =>
            let s : Release.Selection :=
                Release.selection "nightly-x" "x86_64-linux" "monad-nightly-x86_64-linux" "file:///r/monad-nightly-x86_64-linux" false "" in
            match Release.resolve_sources s r {
                Result.err _ => false,
                Result.ok url => match url { Option.none => true, Option.some _ => false },
            },
    }

#[test]
def test_commit_url : Bool :=
    let s : Release.Selection :=
        Release.selection "nightly-x" "x86_64-linux" "monad-nightly-x86_64-linux" "file:///r/monad-nightly-x86_64-linux" false "" in
    String.beq (Release.commit_url s) "file:///r/commit.txt"
