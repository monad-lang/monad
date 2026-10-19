/// Install/list/use/default/uninstall/update/self-install/upgrade.
///
/// Behavior is parity with the bash implementation: the same version
/// directory layout, the same "already installed" and missing-sources
/// notes, the repair path (sources are installed outside the
/// already-installed branch), and the same platform fallback.
use std::process {process_id}
use lib::platform {*}
use lib::text {*}
use lib::layout {*}
use lib::release {*}
use lib::shell {*}

pub struct Install.Context {
    home : Layout.Home,
    platform : Platform.Resolution,
    api_url : String,
}

pub def Install.context : IO Install.Context := do {
    let home_env <- Shell.monad_home_env;
    let user_home <- Shell.home_env;
    let uname <- Shell.uname_sm;
    let api <- Shell.api_url;
    let ctx : Install.Context := {
        home := Layout.resolve_home home_env user_home,
        platform := Platform.of_uname (Option.get_or_default "" uname),
        api_url := api,
    };
    return ctx
}

def Install.fail (msg : String) : IO I64 := do {
    IO.write_stderr (String.concat "monadup: error: " (String.concat msg "\n"));
    return 1
}

def Install.note (msg : String) : IO Unit :=
    IO.println (String.concat "monadup: note: " msg)

#[partial]
def Install.active_tag_from (raw : String) : Option String :=
    let t : String := Text.trim raw in
    if String.is_empty t then Option.none else Option.some t

pub def Install.active_tag (h : Layout.Home) : IO (Option String) := do {
    let path : String := Layout.active_file h;
    let exists <- Shell.file_exists path;
    if Bool.not exists then return Option.none
    else do {
        let raw <- Shell.read_file path;
        return (Install.active_tag_from raw)
    }
}

pub def Install.fetch_releases (ctx : Install.Context) : IO (Result String (List Release.Info)) := do {
    let r <- Shell.curl_fetch ctx.api_url;
    match r {
        Pair.pair code out =>
            if I64.beq code 0
            then return (Release.parse_releases out)
            else return (Result.err "failed to query the releases API (network or rate limit)"),
    }
}

pub def Install.fetch_release (ctx : Install.Context) (tag : String) : IO (Result String Release.Info) := do {
    let url : String := String.concat ctx.api_url (String.concat "/tags/" tag);
    let r <- Shell.curl_fetch url;
    match r {
        Pair.pair code out =>
            if I64.beq code 0
            then return (Release.parse_release out)
            else return (Result.err (String.concat "failed to fetch release '" (String.concat tag "'"))),
    }
}

pub def Install.latest (ctx : Install.Context) : IO (Result String Release.Info) := do {
    let rs <- Install.fetch_releases ctx;
    match rs {
        Result.err e => return (Result.err e),
        Result.ok releases =>
            match Release.latest_nightly releases {
                Option.some r => return (Result.ok r),
                Option.none => return (Result.err "no nightly release found"),
            },
    }
}

/// The hash a `<url>.sha256` sibling publishes, if it publishes one.
/// Releases before checksums existed have no sibling, so `none` means
/// "cannot verify", not "bad".
def Install.fetch_checksum (url : String) : IO (Option String) := do {
    let r <- Shell.curl_fetch (String.concat url ".sha256");
    match r {
        Pair.pair code out =>
            if I64.beq code 0
            then
                let token : String := Text.first_word (Text.trim out) in
                if I64.beq (String.length token) 64 then return (Option.some token) else return Option.none
            else return Option.none,
    }
}

/// Download, then verify when the release publishes a `.sha256` beside
/// the asset. A mismatch removes the file. An asset with no checksum is
/// accepted (older releases), but a published checksum that cannot be
/// checked is an error rather than a silent pass.
pub def Install.download_to (url : String) (dest : String) : IO (Result String Unit) := do {
    let code <- Shell.curl_download url dest;
    if Bool.not (I64.beq code 0) then return (Result.err (String.concat "failed to download " url))
    else do {
        let expected <- Install.fetch_checksum url;
        match expected {
            Option.none => return (Result.ok unit),
            Option.some want => do {
                let got <- Shell.sha256 dest;
                match got {
                    Option.none => do {
                        let _ <- Shell.rm_rf dest;
                        return (Result.err (String.concat "cannot verify " (String.concat url ": neither sha256sum nor shasum is available")))
                    },
                    Option.some have =>
                        if String.beq have want
                        then return (Result.ok unit)
                        else do {
                            let _ <- Shell.rm_rf dest;
                            return (Result.err (String.concat "checksum mismatch for " url))
                        },
                }
            },
        }
    }
}

pub def Install.do_use (ctx : Install.Context) (tag : String) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let dir : String := Layout.version_dir h tag;
    let isdir <- Shell.is_dir dir;
    if Bool.not isdir then Install.fail (String.concat "nightly '" (String.concat tag "' is not installed"))
    else do {
        let entries <- Shell.list_dir dir;
        match Layout.find_nightly_binary entries {
            Option.none => Install.fail (String.concat "binary missing in '" (String.concat tag "'")),
            Option.some binary => do {
                let path : String := String.concat dir (String.concat "/" binary);
                let exe <- Shell.is_executable path;
                if Bool.not exe then Install.fail (String.concat "binary in '" (String.concat tag "' is not executable"))
                else do {
                    let bin : String := Layout.bin_dir h;
                    let mk <- Shell.mkdir_p bin;
                    if Bool.not (I64.beq mk 0)
                    then Install.fail (String.concat "failed to create " bin)
                    else do {
                        let target : String := String.concat "../downloads/" (String.concat tag (String.concat "/" binary));
                        let ln <- Shell.ln_sfn target (Layout.monad_link h);
                        if Bool.not (I64.beq ln 0)
                        then Install.fail (String.concat "failed to point " (String.concat (Layout.monad_link h) " at the new nightly"))
                        else do {
                            Shell.write_file (Layout.active_file h) tag;
                            let written <- Shell.read_file (Layout.active_file h);
                            if String.beq (Text.trim written) tag
                            then return 0
                            else Install.fail (String.concat "failed to write " (Layout.active_file h))
                        }
                    }
                }
            },
        }
    }
}

pub def Install.use_tag (ctx : Install.Context) (tag : String) : IO I64 := do {
    if Bool.not (Layout.valid_tag tag)
    then Install.fail (String.concat "invalid nightly tag: " tag)
    else do {
        let code <- Install.do_use ctx tag;
        if I64.beq code 0 then IO.println (String.concat "monadup: switched to " tag) else return unit;
        return code
    }
}

def Install.sources_complete (dir : String) : IO Bool := do {
    let dirs <- Install.source_dirs_present dir Layout.source_names;
    let manifest <- Shell.file_exists (String.concat dir "/mote.toml");
    return (dirs && manifest)
}

def Install.source_dirs_present (dir : String) (names : List String) : IO Bool :=
    match names {
        List.empty => return true,
        List.cons name rest => do {
            let present <- Shell.is_dir (String.concat dir (String.concat "/" name));
            if Bool.not present then return false else Install.source_dirs_present dir rest
        },
    }

pub def Install.install_sources (ctx : Install.Context) (sel : Release.Selection) (r : Release.Info) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let dir : String := Layout.version_dir h r.tag;
    let have <- Install.sources_complete dir;
    if have then return 0
    else do {
        let src := Release.resolve_sources sel r;
        match src {
            Result.err e => Install.fail e,
            Result.ok maybe_url =>
                match maybe_url {
                    Option.none => do {
                        Install.note (String.concat r.tag (String.concat " ships no " (String.concat (Platform.src_asset sel.platform) " and no monad-src.tar.gz")));
                        IO.println "monadup:       the binary is installed and usable inside a compiler checkout,";
                        IO.println "monadup:       but 'monad build'/'run'/'test' elsewhere will not find init,";
                        IO.println "monadup:       std, llvm or the C runtime: declare [dependencies.runtime] and run";
                        IO.println "monadup:       from a checkout, or install a tag that ships the sources.";
                        return 0
                    },
                    Option.some url => do {
                        let has_tar <- Shell.tool_exists "tar";
                        if Bool.not has_tar
                        then Install.fail (String.concat "tar is not available (needed to unpack " (String.concat (Platform.src_asset sel.platform) "); install tar, or fetch the binary by hand from the release"))
                        else do {
                            let asset : String := Text.basename url;
                            let tarball : String := String.concat dir (String.concat "/" asset);
                            let dl <- Install.download_to url tarball;
                            match dl {
                                Result.err e => Install.fail e,
                                Result.ok _ => do {
                                    let code <- Shell.untar tarball dir;
                                    let _ <- Shell.rm_rf tarball;
                                    if I64.beq code 0
                                    then do {
                                        IO.println "monadup: installed mote sources (init, std, llvm, runtime)";
                                        return 0
                                    }
                                    else Install.fail (String.concat "failed to unpack " asset)
                                },
                            }
                        }
                    },
                },
        }
    }
}

pub def Install.do_install (ctx : Install.Context) (r : Release.Info) : IO I64 := do {
    if Bool.not (Layout.valid_tag r.tag)
    then Install.fail (String.concat "release has an invalid tag: " r.tag)
    else if String.is_empty ctx.platform.uname_sm
    then Install.fail "could not determine the platform (`uname -sm` failed); refusing to install a release for the wrong machine"
    else do {
        let sel_res := Release.resolve_binary ctx.platform.platform r;
        match sel_res {
            Result.err e => Install.fail e,
            Result.ok sel => do {
                if sel.fallback then Install.note sel.note else return unit;
                Install.download_version ctx sel r
            },
        }
    }
}

def Install.download_version (ctx : Install.Context) (sel : Release.Selection) (r : Release.Info) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let dir : String := Layout.version_dir h r.tag;
    let binary : String := String.concat dir (String.concat "/" sel.asset);
    let already <- Shell.is_executable binary;
    if already
    then do {
        IO.println (String.concat "monadup: " (String.concat r.tag " already installed"));
        return 0
    }
    else do {
        let _ <- Shell.mkdir_p dir;
        IO.println (String.concat "monadup: downloading " (String.concat r.tag "..."));
        let dl <- Install.download_to sel.url binary;
        match dl {
            Result.err e => Install.fail e,
            Result.ok _ => Install.download_commit ctx sel r binary,
        }
    }
}

def Install.download_commit (ctx : Install.Context) (sel : Release.Selection) (r : Release.Info) (binary : String) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let commit <- Install.download_to (Release.commit_url sel) (Layout.commit_file h r.tag);
    match commit {
        Result.err e => Install.fail e,
        Result.ok _ => do {
            let _ <- Shell.chmod_x binary;
            IO.println (String.concat "monadup: installed " r.tag);
            let v <- Shell.capture_line binary ["version"];
            match v {
                Option.some s => IO.println s,
                Option.none => Install.note "installed binary did not run (`monad version` failed)",
            };
            return 0
        },
    }
}

pub def Install.after_install (ctx : Install.Context) (r : Release.Info) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let sel_res := Release.resolve_binary ctx.platform.platform r;
    match sel_res {
        Result.err e => Install.fail e,
        Result.ok sel => do {
            let src <- Install.install_sources ctx sel r;
            if Bool.not (I64.beq src 0) then return src
            else do {
                let active <- Install.active_tag h;
                match active {
                    Option.none => Install.do_use ctx r.tag,
                    Option.some _ => return 0,
                }
            }
        },
    }
}

pub def Install.install_latest (ctx : Install.Context) : IO I64 := do {
    let latest <- Install.latest ctx;
    match latest {
        Result.err e => Install.fail e,
        Result.ok r => do {
            let code <- Install.do_install ctx r;
            if Bool.not (I64.beq code 0) then return code
            else Install.after_install ctx r
        },
    }
}

pub def Install.install_tag (ctx : Install.Context) (tag : String) : IO I64 := do {
    if Bool.not (Layout.valid_tag tag)
    then Install.fail (String.concat "invalid nightly tag: " tag)
    else do {
        let r <- Install.fetch_release ctx tag;
        match r {
            Result.err e => Install.fail e,
            Result.ok release => do {
                let code <- Install.do_install ctx release;
                if Bool.not (I64.beq code 0) then return code
                else Install.after_install ctx release
            },
        }
    }
}

pub def Install.default (ctx : Install.Context) : IO I64 := do {
    let latest <- Install.latest ctx;
    match latest {
        Result.err e => Install.fail e,
        Result.ok r => do {
            let code <- Install.do_install ctx r;
            if Bool.not (I64.beq code 0) then return code
            else do {
                let src <- Install.after_install ctx r;
                if Bool.not (I64.beq src 0) then return src
                else do {
                    let code2 <- Install.do_use ctx r.tag;
                    if I64.beq code2 0
                    then IO.println (String.concat "monadup: default set to " r.tag)
                    else return unit;
                    return code2
                }
            }
        },
    }
}

#[partial]
def Install.nightly_entries (entries : List String) : List String :=
    match entries {
        List.empty => List.empty,
        List.cons e rest =>
            if String.starts_with "nightly-" e
            then List.cons e (Install.nightly_entries rest)
            else Install.nightly_entries rest,
    }

pub def Install.list (ctx : Install.Context) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let dl : String := Layout.downloads h;
    let isdir <- Shell.is_dir dl;
    if Bool.not isdir then do {
        IO.println "monadup: no nightlies installed";
        return 0
    } else do {
        let entries <- Shell.list_dir dl;
        let tags : List String := Text.sort (Install.nightly_entries entries);
        let active <- Install.active_tag h;
        match tags {
            List.empty => do {
                IO.println "monadup: no nightlies installed";
                return 0
            },
            List.cons _ _ => do {
                Install.print_list h tags active;
                return 0
            },
        }
    }
}

#[partial]
def Install.print_list (h : Layout.Home) (tags : List String) (active : Option String) : IO Unit :=
    match tags {
        List.empty => return unit,
        List.cons tag rest => do {
            let marker : String :=
                match active {
                    Option.some a => if String.beq a tag then "*" else " ",
                    Option.none => " ",
                };
            let commit_path : String := Layout.commit_file h tag;
            let exists <- Shell.file_exists commit_path;
            let commit : String <-
                if exists then Shell.read_file commit_path else return "";
            IO.println (String.concat marker (String.concat " " (String.concat tag (String.concat "  " (Text.trim commit)))));
            Install.print_list h rest active
        },
    }

pub def Install.uninstall (ctx : Install.Context) (tag : String) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    if Bool.not (Layout.valid_tag tag) then Install.fail (String.concat "invalid nightly tag: " tag)
    else do {
        let dir : String := Layout.version_dir h tag;
        let isdir <- Shell.is_dir dir;
        if Bool.not isdir then Install.fail (String.concat "nightly '" (String.concat tag "' is not installed"))
        else do {
            let active <- Install.active_tag h;
            match active {
                Option.some a =>
                    if String.beq a tag
                    then Install.fail "cannot uninstall active nightly, switch first"
                    else do {
                        let _ <- Shell.rm_rf dir;
                        IO.println (String.concat "monadup: removed " tag);
                        return 0
                    },
                Option.none => do {
                    let _ <- Shell.rm_rf dir;
                    IO.println (String.concat "monadup: removed " tag);
                    return 0
                },
            }
        }
    }
}

#[partial]
def Install.prune (h : Layout.Home) (keep : String) (active : Option String) (tags : List String) : IO Unit :=
    match tags {
        List.empty => return unit,
        List.cons tag rest => do {
            let keep_it : Bool := String.beq tag keep || match active { Option.some a => String.beq a tag, Option.none => false };
            if keep_it then Install.prune h keep active rest
            else do {
                let _ <- Shell.rm_rf (Layout.version_dir h tag);
                IO.println (String.concat "monadup: pruned " tag);
                Install.prune h keep active rest
            }
        },
    }

pub def Install.update (ctx : Install.Context) : IO I64 := do {
    let latest <- Install.latest ctx;
    match latest {
        Result.err e => Install.fail e,
        Result.ok r => do {
            let code <- Install.do_install ctx r;
            if Bool.not (I64.beq code 0) then return code
            else do {
                let src <- Install.after_install ctx r;
                if Bool.not (I64.beq src 0) then return src
                else do {
                    // The release resolved above is the one to keep; a second
                    // list call here could see a newer tag and prune the one
                    // just installed.
                    let h : Layout.Home := ctx.home;
                    let dl : String := Layout.downloads h;
                    let isdir <- Shell.is_dir dl;
                    let entries <- if isdir then Shell.list_dir dl else return List.empty;
                    let active <- Install.active_tag h;
                    let switch <- Install.do_use ctx r.tag;
                    if Bool.not (I64.beq switch 0) then return switch
                    else do {
                        Install.prune h r.tag active (Install.nightly_entries entries);
                        IO.println (String.concat "monadup: updated to " r.tag);
                        return 0
                    }
                }
            }
        },
    }
}

pub def Install.self_install (ctx : Install.Context) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let target : String := Layout.up_binary h;
    let bin : String := Layout.bin_dir h;
    let mk <- Shell.mkdir_p bin;
    if Bool.not (I64.beq mk 0) then Install.fail (String.concat "failed to create " bin)
    else do {
        let me <- Shell.self_exe_path;
        match me {
            Option.some path => do {
                let tmp : String := String.concat target (String.concat ".tmp." (I64.to_string process_id));
                let c <- Shell.cp path tmp;
                if Bool.not (I64.beq c 0) then Install.fail "failed to copy the running monadup"
                else do {
                    let x <- Shell.chmod_x tmp;
                    if Bool.not (I64.beq x 0) then Install.fail "failed to make the copied monadup executable"
                    else do {
                        let m <- Shell.mv tmp target;
                        if Bool.not (I64.beq m 0) then Install.fail "failed to install monadup"
                        else do {
                            IO.println (String.concat "monadup: installed to " target);
                            Install.print_path_hint bin;
                            return 0
                        }
                    }
                }
            },
            Option.none => Install.seed_from_release ctx target,
        }
    }
}

def Install.print_path_hint (bin : String) : IO Unit := do {
    IO.println (String.concat "Add " (String.concat bin " to your PATH:"));
    IO.println (String.concat "  export PATH=\"" (String.concat bin ":$PATH\""));
    IO.println "Add that line to your ~/.bashrc or ~/.zshrc to make it permanent."
}

def Install.seed_from_release (ctx : Install.Context) (target : String) : IO I64 := do {
    if String.is_empty ctx.platform.uname_sm
    then Install.fail "could not determine the platform (`uname -sm` failed); refusing to download a monadup built for the wrong machine"
    else do {
        let latest <- Install.latest ctx;
        match latest {
            Result.err e => Install.fail e,
            Result.ok r =>
                match Release.resolve_monadup ctx.platform.platform r {
                    Result.err e => Install.fail e,
                    Result.ok sel => do {
                        let tmp : String := String.concat target (String.concat ".tmp." (I64.to_string process_id));
                        let dl <- Install.download_to sel.url tmp;
                        match dl {
                            Result.err e => Install.fail e,
                            Result.ok _ => do {
                                let x <- Shell.chmod_x tmp;
                                if Bool.not (I64.beq x 0) then Install.fail "failed to make the downloaded monadup executable"
                                else do {
                                    let m <- Shell.mv tmp target;
                                    if Bool.not (I64.beq m 0) then Install.fail "failed to install monadup"
                                    else do {
                                        IO.println (String.concat "monadup: installed to " target);
                                        Install.print_path_hint (Layout.bin_dir ctx.home);
                                        return 0
                                    }
                                }
                            },
                        }
                    },
                },
        }
    }
}

pub def Install.upgrade (ctx : Install.Context) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let target : String := Layout.up_binary h;
    let exists <- Shell.file_exists target;
    if Bool.not exists
    then Install.fail "not self-installed yet; run 'monadup self-install' first"
    else Install.seed_from_release ctx target
}
