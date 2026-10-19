/// Platform resolution: `uname -sm` -> the `<arch>-<os>` label the nightly
/// release names its assets with.
///
/// The table is the same one `scripts/lib/platform-label.sh` uses on the
/// release side, with one deliberate difference carried over from the bash
/// script: an unrecognised machine FALLS BACK to `x86_64-linux` rather than
/// erroring. A release's assets are resolved separately (release.mo's
/// platform chain), so a machine with no nightly of its own still gets a
/// working install.
pub struct Platform.Resolution {
    platform : String,
    uname_sm : String,
    used_fallback : Bool,
    note : String,
}

pub def Platform.fallback : String := "x86_64-linux"

pub def Platform.platforms : List String := [
    "x86_64-linux",
    "aarch64-linux",
    "riscv64-linux",
    "aarch64-darwin",
]

def Platform.resolved (platform : String) (uname_sm : String) : Platform.Resolution :=
    let r : Platform.Resolution := {
        platform := platform,
        uname_sm := uname_sm,
        used_fallback := false,
        note := "",
    } in r

def Platform.fell_back (uname_sm : String) : Platform.Resolution :=
    let r : Platform.Resolution := {
        platform := Platform.fallback,
        uname_sm := uname_sm,
        used_fallback := true,
        note := String.concat "no nightly is published for '" (String.concat uname_sm "'; installing the x86_64-linux artifacts"),
    } in r

pub def Platform.of_uname (uname_sm : String) : Platform.Resolution :=
    if String.beq uname_sm "Darwin arm64" then Platform.resolved "aarch64-darwin" uname_sm
    else if String.beq uname_sm "Darwin aarch64" then Platform.resolved "aarch64-darwin" uname_sm
    else if String.beq uname_sm "Linux aarch64" then Platform.resolved "aarch64-linux" uname_sm
    else if String.beq uname_sm "Linux arm64" then Platform.resolved "aarch64-linux" uname_sm
    else if String.beq uname_sm "Linux riscv64" then Platform.resolved "riscv64-linux" uname_sm
    else if String.beq uname_sm "Linux x86_64" then Platform.resolved "x86_64-linux" uname_sm
    else if String.beq uname_sm "Linux amd64" then Platform.resolved "x86_64-linux" uname_sm
    else Platform.fell_back uname_sm

pub def Platform.bin_asset (platform : String) : String :=
    String.concat "monad-nightly-" platform

pub def Platform.src_asset (platform : String) : String :=
    String.concat "monad-src-" (String.concat platform ".tar.gz")

pub def Platform.up_asset (platform : String) : String :=
    String.concat "monadup-" platform

/// The platform, then the historical fallback, in lookup order.
pub def Platform.chain (platform : String) : List String :=
    if String.beq platform Platform.fallback
    then [platform]
    else [platform, Platform.fallback]
