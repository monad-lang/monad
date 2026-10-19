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
    path : Path,
    source : String,
}

pub def Layout.resolve_home (env_home : Option String) (user_home : Option String) : Layout.Home :=
    match env_home {
        Option.some raw =>
            let p : String := Text.trim raw in
            if String.is_empty p
            then Layout.default_home user_home
            else let h : Layout.Home := { path := Path.path p, source := "MONAD_HOME" } in h,
        Option.none => Layout.default_home user_home,
    }

def Layout.default_home (user_home : Option String) : Layout.Home :=
    let base : String := Option.get_or_default "" user_home in
    let p : Path :=
        if String.is_empty base
        then Path.path ".monad"
        else Path.join (Path.path base) (Path.path ".monad") in
    let h : Layout.Home := { path := p, source := "default" } in h

pub def Layout.downloads (h : Layout.Home) : Path :=
    Path.join h.path (Path.path "downloads")

/// A tag's path component. `valid_tag` rejects the empty string, absolute
/// paths, separators and `..`; `Path.join` would otherwise replace the
/// whole base with an absolute component.
pub def Layout.tag_path (tag : String) : Result String Path :=
    if Bool.not (Layout.valid_tag tag)
    then Result.err ("invalid nightly tag: " ++ tag)
    else Path.of tag

pub def Layout.version_dir (h : Layout.Home) (tag : Path) : Path :=
    Path.join (Layout.downloads h) tag

pub def Layout.active_file (h : Layout.Home) : Path :=
    Path.join h.path (Path.path "active")

pub def Layout.bin_dir (h : Layout.Home) : Path :=
    Path.join h.path (Path.path "bin")

/// The directories a nightly's sources asset unpacks into, plus the root
/// `mote.toml` the compiler's toolchain discovery requires.
pub def Layout.source_names : List String := ["init", "std", "llvm", "runtime"]

pub def Layout.monad_link (h : Layout.Home) : Path :=
    Path.join (Layout.bin_dir h) (Path.path "monad")

pub def Layout.up_binary (h : Layout.Home) : Path :=
    Path.join (Layout.bin_dir h) (Path.path "monadup")

pub def Layout.commit_file (h : Layout.Home) (tag : Path) : Path :=
    Path.join (Layout.version_dir h tag) (Path.path "commit.txt")

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
/// comparisons monadup makes). Keeps `/` itself.
#[partial]
pub def Layout.drop_trailing_slash (s : String) : String :=
    let n : I64 := String.length s in
    if I64.lt 1 n && String.beq (String.slice s (I64.sub n 1) 1) "/"
    then Layout.drop_trailing_slash (String.slice s 0 (I64.sub n 1))
    else s
