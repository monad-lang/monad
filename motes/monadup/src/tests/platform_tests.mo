use std::list {List.length}
use lib::platform {*}

#[test]
def test_platform_linux_x86_64 : Bool :=
    let r : Platform.Resolution := Platform.of_uname "Linux x86_64" in
    String.beq r.platform "x86_64-linux" && Bool.not r.used_fallback

#[test]
def test_platform_linux_arm64 : Bool :=
    let r : Platform.Resolution := Platform.of_uname "Linux arm64" in
    String.beq r.platform "aarch64-linux"

#[test]
def test_platform_linux_riscv64 : Bool :=
    let r : Platform.Resolution := Platform.of_uname "Linux riscv64" in
    String.beq r.platform "riscv64-linux"

#[test]
def test_platform_darwin_arm64 : Bool :=
    let r : Platform.Resolution := Platform.of_uname "Darwin arm64" in
    String.beq r.platform "aarch64-darwin"

#[test]
def test_platform_fallback_names_the_machine : Bool :=
    let r : Platform.Resolution := Platform.of_uname "SunOS sun4u" in
    r.used_fallback
        && String.beq r.platform "x86_64-linux"
        && String.contains r.note "SunOS sun4u"

#[test]
def test_platform_chain_has_fallback : Bool :=
    I64.beq (List.length (Platform.chain "aarch64-linux")) 2
        && I64.beq (List.length (Platform.chain "x86_64-linux")) 1

#[test]
def test_asset_names : Bool :=
    String.beq (Platform.bin_asset "x86_64-linux") "monad-nightly-x86_64-linux"
        && String.beq (Platform.src_asset "x86_64-linux") "monad-src-x86_64-linux.tar.gz"
        && String.beq (Platform.up_asset "x86_64-linux") "monadup-x86_64-linux"
