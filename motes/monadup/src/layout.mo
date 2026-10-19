use lib::text {*}

/// Pure path math for the `$MONAD_HOME` layout:
///
///   <home>/downloads/<tag>/monad-nightly-<platform>
///   <home>/downloads/<tag>/commit.txt
///   <home>/downloads/<tag>/{init,std,llvm,runtime,mote.toml}
///   <home>/active
///   <home>/bin/monad -> ../downloads/<tag>/monad-nightly-<platform>
///   <home>/bin/monadup
///
/// The same layout the bash `monadup` wrote, so an existing install keeps
/// working.
pub struct Layout.Home {
    path : String,
    source : String,
}

pub def Layout.resolve_home (env_home : Option String) (user_home : Option String) : Layout.Home :=
    match env_home {
        Option.some raw =>
            let p : String := Text.trim raw in
            if String.is_empty p
            then Layout.default_home user_home
            else let h : Layout.Home := { path := p, source := "MONAD_HOME" } in h,
        Option.none => Layout.default_home user_home,
    }

def Layout.default_home (user_home : Option String) : Layout.Home :=
    let base : String := Option.get_or_default "" user_home in
    let p : String :=
        if String.is_empty base
        then ".monad"
        else String.concat base "/.monad" in
    let h : Layout.Home := { path := p, source := "default" } in h

pub def Layout.downloads (h : Layout.Home) : String :=
    String.concat (Layout.drop_trailing_slash h.path) "/downloads"

pub def Layout.version_dir (h : Layout.Home) (tag : String) : String :=
    String.concat (Layout.downloads h) (String.concat "/" tag)

pub def Layout.active_file (h : Layout.Home) : String :=
    String.concat (Layout.drop_trailing_slash h.path) "/active"

pub def Layout.bin_dir (h : Layout.Home) : String :=
    String.concat (Layout.drop_trailing_slash h.path) "/bin"

/// The directories a nightly's sources asset unpacks into, plus the root
/// `mote.toml` the compiler's toolchain discovery requires.
pub def Layout.source_names : List String := ["init", "std", "llvm", "runtime"]

pub def Layout.monad_link (h : Layout.Home) : String :=
    String.concat (Layout.bin_dir h) "/monad"

pub def Layout.up_binary (h : Layout.Home) : String :=
    String.concat (Layout.bin_dir h) "/monadup"

pub def Layout.commit_file (h : Layout.Home) (tag : String) : String :=
    String.concat (Layout.version_dir h tag) "/commit.txt"

/// `downloads/<tag>` names only tags the release API can have produced:
/// the `nightly-` prefix and no path separators / parent segments.
pub def Layout.valid_tag (tag : String) : Bool :=
    String.starts_with "nightly-" tag
        && Bool.not (String.contains tag "/")
        && Bool.not (String.contains tag "\\")
        && Bool.not (String.contains tag "..")

#[partial]
pub def Layout.find_nightly_binary (entries : List String) : Option String :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            if String.starts_with "monad-nightly-" e
            then Option.some e
            else Layout.find_nightly_binary rest,
    }

#[partial]
pub def Layout.find_monadup_binary (entries : List String) : Option String :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            if String.starts_with "monadup-" e
            then Option.some e
            else Layout.find_monadup_binary rest,
    }

/// `/a/b/` -> `/a/b` (a trailing slash is not part of a path for the
/// comparisons monadup makes).
#[partial]
pub def Layout.drop_trailing_slash (s : String) : String :=
    let n : I64 := String.length s in
    if I64.lt 1 n && String.beq (String.slice s (I64.sub n 1) 1) "/"
    then Layout.drop_trailing_slash (String.slice s 0 (I64.sub n 1))
    else s
