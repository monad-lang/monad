/// The pure doctor checks, exercised against synthetic environments. No
/// test touches the real `MONAD_HOME`.
use lib::doctor {*}
use lib::layout {*}
use lib::platform {*}

def base_platform : Platform.Resolution :=
    let p : Platform.Resolution := {
        platform := "x86_64-linux",
        uname_sm := "Linux x86_64",
        used_fallback := false,
        note := "",
    } in p

def base_home : Layout.Home :=
    let h : Layout.Home := { path := "/tmp/monadup-doctor", source := "default" } in h

def base_tools : Doctor.Tools :=
    let t : Doctor.Tools := {
        curl := true, tar := true, llc := true, clang := true,
        pkg_config := true, bdw_gc := true,
    } in t

def base_env : Doctor.Env :=
    let e : Doctor.Env := {
        platform := base_platform,
        home := base_home,
        home_exists := true,
        home_writable := true,
        active := Option.some "nightly-x",
        active_dir_exists := true,
        binary := Option.some "monad-nightly-x86_64-linux",
        binary_exec := true,
        commit := Option.some "abc",
        binary_version := Option.some "abc",
        sources := ["init", "std", "llvm", "runtime"],
        root_manifest := true,
        monad_link := Option.some "../downloads/nightly-x/monad-nightly-x86_64-linux",
        monad_link_ok := true,
        link_is_symlink := true,
        path_has_bin := true,
        overrides := List.empty,
        monad_root_bad := false,
        api_ok := true,
        downloads := ["nightly-x"],
        tools := base_tools,
        no_network := true,
    } in e

def status_text (c : Doctor.Check) : String := Doctor.status_text c.status

#[test]
def test_platform_unknown_is_fail : Bool :=
    let p : Platform.Resolution := { base_platform with uname_sm := "", used_fallback := true, note := "unknown" } in
    let e : Doctor.Env := { base_env with platform := p } in
    String.beq (status_text (Doctor.platform_check e)) "fail"

#[test]
def test_platform_fallback_is_warn : Bool :=
    let p : Platform.Resolution := { base_platform with platform := "x86_64-linux", uname_sm := "SunOS sun4u", used_fallback := true, note := "fallback" } in
    let e : Doctor.Env := { base_env with platform := p } in
    String.beq (status_text (Doctor.platform_check e)) "warn"

#[test]
def test_home_unwritable_is_fail : Bool :=
    let e : Doctor.Env := { base_env with home_writable := false } in
    String.beq (status_text (Doctor.home_check e)) "fail"

#[test]
def test_home_missing_is_ok : Bool :=
    let e : Doctor.Env := { base_env with home_exists := false } in
    String.beq (status_text (Doctor.home_check e)) "ok"

#[test]
def test_regular_file_link_is_ok : Bool :=
    let e : Doctor.Env := { base_env with link_is_symlink := false } in
    String.beq (status_text (Doctor.link_check e)) "ok"

#[test]
def test_dangling_symlink_is_fail : Bool :=
    let e : Doctor.Env := { base_env with monad_link_ok := false } in
    String.beq (status_text (Doctor.link_check e)) "fail"

#[test]
def test_missing_symlink_is_fail : Bool :=
    let e : Doctor.Env := { base_env with link_is_symlink := false, monad_link_ok := false } in
    String.beq (status_text (Doctor.link_check e)) "fail"

#[test]
def test_missing_sources_warns : Bool :=
    let e : Doctor.Env := { base_env with sources := ["init"] } in
    String.beq (status_text (Doctor.sources_check e)) "warn"

#[test]
def test_complete_sources_is_ok : Bool :=
    String.beq (status_text (Doctor.sources_check base_env)) "ok"
