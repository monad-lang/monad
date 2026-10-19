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
        platform := Platform.of_uname uname,
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

pub def Install.download_to (url : String) (dest : String) : IO (Result String Unit) := do {
    let code <- Shell.curl_download url dest;
    if I64.beq code 0
    then return (Result.ok unit)
    else return (Result.err (String.concat "failed to download " url))
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
                    let _ <- Shell.mkdir_p (Layout.bin_dir h);
                    let target : String := String.concat "../downloads/" (String.concat tag (String.concat "/" binary));
                    let _ <- Shell.ln_sfn target (Layout.monad_link h);
                    Shell.write_file (Layout.active_file h) tag;
                    return 0
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

pub def Install.install_sources (ctx : Install.Context) (sel : Release.Selection) (r : Release.Info) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let dir : String := Layout.version_dir h r.tag;
    let init_dir : String := String.concat dir "/init";
    let have <- Shell.is_dir init_dir;
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
                    },
                },
        }
    }
}

pub def Install.do_install (ctx : Install.Context) (r : Release.Info) : IO I64 := do {
    let sel_res := Release.resolve_binary ctx.platform.platform r;
    match sel_res {
        Result.err e => Install.fail e,
        Result.ok sel => do {
            if sel.fallback then Install.note sel.note else return unit;
            let has_tar <- Shell.tool_exists "tar";
            if Bool.not has_tar
            then Install.fail (String.concat "tar is not available (needed to unpack " (String.concat (Platform.src_asset sel.platform) "); install tar, or fetch the binary by hand from the release"))
            else Install.download_version ctx sel r
        },
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
                    Option.none => do {
                        let _ <- Install.do_use ctx r.tag;
                        return 0
                    },
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
    let code <- Install.install_latest ctx;
    if Bool.not (I64.beq code 0) then return code
    else do {
        let h : Layout.Home := ctx.home;
        let dl : String := Layout.downloads h;
        let isdir <- Shell.is_dir dl;
        if Bool.not isdir then return 0
        else do {
            let entries <- Shell.list_dir dl;
            let tags : List String := Install.nightly_entries entries;
            let active <- Install.active_tag h;
            let latest <- Install.latest ctx;
            match latest {
                Result.err _ => return 0,
                Result.ok r => do {
                    Install.prune h r.tag active tags;
                    return 0
                },
            }
        }
    }
}

pub def Install.self_install (ctx : Install.Context) : IO I64 := do {
    let h : Layout.Home := ctx.home;
    let target : String := Layout.up_binary h;
    let _ <- Shell.mkdir_p (Layout.bin_dir h);
    let me <- Shell.self_exe_path;
    match me {
        Option.some path => do {
            let tmp : String := String.concat target (String.concat ".tmp." (I64.to_string process_id));
            let c <- Shell.cp path tmp;
            if Bool.not (I64.beq c 0) then Install.fail "failed to copy the running monadup"
            else do {
                let _ <- Shell.chmod_x tmp;
                let m <- Shell.mv tmp target;
                if Bool.not (I64.beq m 0) then Install.fail "failed to install monadup"
                else do {
                    IO.println (String.concat "monadup: installed to " target);
                    Install.print_path_hint;
                    return 0
                }
            }
        },
        Option.none => Install.seed_from_release ctx target,
    }
}

def Install.print_path_hint : IO Unit := do {
    IO.println "Add ~/.monad/bin to your PATH:";
    IO.println "  export PATH=\"$HOME/.monad/bin:$PATH\"";
    IO.println "Add that line to your ~/.bashrc or ~/.zshrc to make it permanent."
}

def Install.seed_from_release (ctx : Install.Context) (target : String) : IO I64 := do {
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
                            let _ <- Shell.chmod_x tmp;
                            let m <- Shell.mv tmp target;
                            if Bool.not (I64.beq m 0) then Install.fail "failed to install monadup"
                            else do {
                                IO.println (String.concat "monadup: installed to " target);
                                Install.print_path_hint;
                                return 0
                            }
                        },
                    }
                },
            },
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
