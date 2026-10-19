use lib::layout {*}

#[test]
def test_home_env_override : Bool :=
    let h : Layout.Home := Layout.resolve_home (Option.some "/tmp/mh") (Option.some "/home/u") in
    String.beq (Path.to_string h.path) "/tmp/mh" && String.beq h.source "MONAD_HOME"

#[test]
def test_home_default : Bool :=
    let h : Layout.Home := Layout.resolve_home Option.none (Option.some "/home/u") in
    String.beq (Path.to_string h.path) "/home/u/.monad" && String.beq h.source "default"

#[test]
def test_home_paths : Bool :=
    let h : Layout.Home := Layout.resolve_home (Option.some "/x") Option.none in
    String.beq (Path.to_string (Layout.downloads h)) "/x/downloads"
        && String.beq (Path.to_string (Layout.version_dir h (Path.path "nightly-1"))) "/x/downloads/nightly-1"
        && String.beq (Path.to_string (Layout.active_file h)) "/x/active"
        && String.beq (Path.to_string (Layout.monad_link h)) "/x/bin/monad"
        && String.beq (Path.to_string (Layout.up_binary h)) "/x/bin/monadup"

#[test]
def test_tag_path_rejects_unsafe_tags : Bool :=
    match Layout.tag_path "/etc" { Result.err _ => true, Result.ok _ => false }
        && match Layout.tag_path "nightly-../x" { Result.err _ => true, Result.ok _ => false }
        && match Layout.tag_path "nightly-1" {
            Result.ok p => String.beq (Path.to_string p) "nightly-1",
            Result.err _ => false,
        }

#[test]
def test_valid_tag : Bool :=
    Layout.valid_tag "nightly-2026-10-19-abc1234"
        && Bool.not (Layout.valid_tag "stable-1")
        && Bool.not (Layout.valid_tag "nightly-../x")
        && Bool.not (Layout.valid_tag "nightly-a/b")

#[test]
def test_find_nightly_binary : Bool :=
    match Layout.find_nightly_binary ["commit.txt", "monad-nightly-x86_64-linux"] {
        Option.some n => String.beq n "monad-nightly-x86_64-linux",
        Option.none => false,
    }

#[test]
def test_find_monadup_binary : Bool :=
    match Layout.find_monadup_binary ["monad-src-x.tar.gz", "monadup-x86_64-linux"] {
        Option.some n => String.beq n "monadup-x86_64-linux",
        Option.none => false,
    }

#[test]
def test_drop_trailing_slash : Bool :=
    String.beq (Layout.drop_trailing_slash "/a/b/") "/a/b"
        && String.beq (Layout.drop_trailing_slash "/a/b") "/a/b"
