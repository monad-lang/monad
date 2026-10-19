/// Release-JSON parsing and asset selection.
///
/// The network hop stays `curl` (there is no TLS in the language yet), but
/// JSON is parsed in-language through `motes/json`, so the bash version's
/// "neither jq nor python3 is available" failure class is gone from the
/// binary.
use std::map {BTreeMap}
use lib::platform {*}
use lib::text {*}
use json::json {
    Json, Json.ParseError, Json.parse, Json.get_array, Json.get_object,
    Json.get_str, Json.object_get,
}

pub struct Release.Asset {
    name : String,
    url : String,
}

pub struct Release.Info {
    tag : String,
    assets : List Release.Asset,
}

/// The resolved artifact for one platform.
pub struct Release.Selection {
    tag : String,
    platform : String,
    asset : String,
    url : String,
    fallback : Bool,
    note : String,
}

pub def Release.asset (name : String) (url : String) : Release.Asset :=
    let a : Release.Asset := { name := name, url := url } in a

pub def Release.release (tag : String) (assets : List Release.Asset) : Release.Info :=
    let r : Release.Info := { tag := tag, assets := assets } in r

pub def Release.selection
        (tag : String) (platform : String) (asset : String) (url : String)
        (fallback : Bool) (note : String) : Release.Selection :=
    let s : Release.Selection := {
        tag := tag,
        platform := platform,
        asset := asset,
        url := url,
        fallback := fallback,
        note := note,
    } in s

def Release.required_str (name : String) (o : BTreeMap String Json) : Result String String :=
    match Json.object_get name o {
        Option.none => Result.err (String.concat "release JSON is missing '" (String.concat name "'")),
        Option.some j => Json.get_str j,
    }

def Release.asset_of (j : Json) : Result String Release.Asset :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok o =>
            match Release.required_str "name" o {
                Result.err e => Result.err e,
                Result.ok name =>
                    match Release.required_str "browser_download_url" o {
                        Result.err e => Result.err e,
                        Result.ok url => Result.ok (Release.asset name url),
                    },
            },
    }

#[partial]
def Release.assets_of_list (js : List Json) : Result String (List Release.Asset) :=
    match js {
        List.empty => Result.ok List.empty,
        List.cons j rest =>
            match Release.asset_of j {
                Result.err e => Result.err e,
                Result.ok a =>
                    match Release.assets_of_list rest {
                        Result.err e => Result.err e,
                        Result.ok as => Result.ok (List.cons a as),
                    },
            },
    }

pub def Release.of_json (j : Json) : Result String Release.Info :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok o =>
            match Release.required_str "tag_name" o {
                Result.err e => Result.err e,
                Result.ok tag =>
                    match Json.object_get "assets" o {
                        Option.none => Result.err "release has no assets",
                        Option.some aj =>
                            match Json.get_array aj {
                                Result.err e => Result.err e,
                                Result.ok js =>
                                    match Release.assets_of_list js {
                                        Result.err e => Result.err e,
                                        Result.ok assets => Result.ok (Release.release tag assets),
                                    },
                            },
                    },
            },
    }

#[partial]
def Release.of_list (js : List Json) : Result String (List Release.Info) :=
    match js {
        List.empty => Result.ok List.empty,
        List.cons j rest =>
            match Release.of_json j {
                Result.err e => Result.err e,
                Result.ok r =>
                    match Release.of_list rest {
                        Result.err e => Result.err e,
                        Result.ok rs => Result.ok (List.cons r rs),
                    },
            },
    }

pub def Release.parse_releases (text : String) : Result String (List Release.Info) :=
    match Json.parse text {
        Result.err e => Result.err (Json.ParseError.to_string e),
        Result.ok j =>
            match Json.get_array j {
                Result.err e => Result.err e,
                Result.ok js => Release.of_list js,
            },
    }

pub def Release.parse_release (text : String) : Result String Release.Info :=
    match Json.parse text {
        Result.err e => Result.err (Json.ParseError.to_string e),
        Result.ok j => Release.of_json j,
    }

#[partial]
pub def Release.latest_nightly (rs : List Release.Info) : Option Release.Info :=
    match rs {
        List.empty => Option.none,
        List.cons r rest =>
            if String.starts_with "nightly-" r.tag
            then Option.some r
            else Release.latest_nightly rest,
    }

#[partial]
pub def Release.asset_url (name : String) (assets : List Release.Asset) : Option String :=
    match assets {
        List.empty => Option.none,
        List.cons a rest =>
            if String.beq a.name name then Option.some a.url else Release.asset_url name rest,
    }

def Release.no_asset_error (tag : String) (platform : String) : String :=
    String.concat "release '" (String.concat tag
        (String.concat "' has no " (String.concat (Platform.bin_asset platform)
            (String.concat " asset, and no " (String.concat (Platform.bin_asset Platform.fallback)
                (String.concat " one either, so it ships no binary for this machine ("
                    (String.concat platform ")")))))))

#[partial]
def Release.resolve_binary_chain
        (tag : String) (original : String) (platforms : List String)
        (assets : List Release.Asset) : Result String Release.Selection :=
    match platforms {
        List.empty => Result.err (Release.no_asset_error tag original),
        List.cons p rest =>
            match Release.asset_url (Platform.bin_asset p) assets {
                Option.none => Release.resolve_binary_chain tag original rest assets,
                Option.some url =>
                    let fallback : Bool := Bool.not (String.beq p original) in
                    let note : String :=
                        if fallback
                        then String.concat "release '" (String.concat tag
                            (String.concat "' ships no " (String.concat (Platform.bin_asset original)
                                (String.concat " binary; installing the " (String.concat (Platform.bin_asset p) " one")))))
                        else "" in
                    Result.ok (Release.selection tag p (Platform.bin_asset p) url fallback note),
            },
    }

pub def Release.resolve_binary (platform : String) (r : Release.Info) : Result String Release.Selection :=
    Release.resolve_binary_chain r.tag platform (Platform.chain platform) r.assets

#[partial]
def Release.resolve_up_chain
        (tag : String) (original : String) (platforms : List String)
        (assets : List Release.Asset) : Result String Release.Selection :=
    match platforms {
        List.empty =>
            Result.err (String.concat "release '" (String.concat tag
                (String.concat "' has no " (String.concat (Platform.up_asset original)
                    (String.concat " asset, and no " (String.concat (Platform.up_asset Platform.fallback)
                        " one either")))))),
        List.cons p rest =>
            match Release.asset_url (Platform.up_asset p) assets {
                Option.none => Release.resolve_up_chain tag original rest assets,
                Option.some url =>
                    Result.ok (Release.selection tag p (Platform.up_asset p) url
                        (Bool.not (String.beq p original)) ""),
            },
    }

/// The `monadup-<platform>` asset, used by `self-install`/`upgrade`.
pub def Release.resolve_monadup (platform : String) (r : Release.Info) : Result String Release.Selection :=
    Release.resolve_up_chain r.tag platform (Platform.chain platform) r.assets

/// The sources asset: the per-platform name first, then the neutral one.
/// `Option.none` is a release that ships no sources at all — a note, not
/// an error (the binary alone still installs).
pub def Release.resolve_sources (sel : Release.Selection) (r : Release.Info) : Result String (Option String) :=
    match Release.asset_url (Platform.src_asset sel.platform) r.assets {
        Option.some url => Result.ok (Option.some url),
        Option.none =>
            match Release.asset_url "monad-src.tar.gz" r.assets {
                Option.some url => Result.ok (Option.some url),
                Option.none => Result.ok Option.none,
            },
    }

/// The release base URL, derived by stripping the asset's own name from
/// its `browser_download_url`; sibling assets (`commit.txt`) live there.
pub def Release.base_url (url : String) (asset : String) : String :=
    if String.ends_with url asset
    then String.slice url 0 (I64.sub (String.length url) (String.length asset))
    else url

pub def Release.commit_url (sel : Release.Selection) : String :=
    String.concat (Release.base_url sel.url sel.asset) "commit.txt"
