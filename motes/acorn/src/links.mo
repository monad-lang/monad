/// The broken-link gate: every internal link in a rendered page must name a
/// page the build emits and, with a `#fragment`, an id on that page.
///
/// Pages are named by their path under the output root (`docs/types.html`).
/// A link is internal when it is relative and names an `.html` page or is a
/// bare `#fragment`; directories (`../try/`), images and absolute URLs are
/// outside the gate (static dirs join it when the cut-over copies them).
use xml_html::html {Html.Node, Html.Attr}
use std::list {List.any, List.filter_map, List.intercalate}

/// The ids a page defines and the hrefs it links to.
pub struct PageLinks {
    /// The path the page is reported at.
    path : String,
    /// The other paths the same document is written to (`index.html` repeats
    /// the first chapter; the 404 page is served from two).
    aliases : List String,
    ids : List String,
    hrefs : List String,
}

/// Ids and hrefs found in one attribute list.
struct Found {
    ids : List String,
    hrefs : List String,
}

def found_attr (a : Html.Attr) (acc : Found) : Found :=
    match a {
        Html.Attr.attr name value => found_value name value acc,
        Html.Attr.bool_attr _ => acc,
    }

def found_value (name : String) (value : String) (acc : Found) : Found :=
    match acc {
        { ids, hrefs } =>
            if String.beq name "id" then { ids := List.cons value ids, hrefs := hrefs }
            else if String.beq name "href" then { ids := ids, hrefs := List.cons value hrefs }
            else { ids := ids, hrefs := hrefs },
    }

def found_attrs (attrs : List Html.Attr) (acc : Found) : Found :=
    match attrs {
        List.empty => acc,
        List.cons a rest => found_attrs rest (found_attr a acc),
    }

def found_nodes (nodes : List Html.Node) (acc : Found) : Found :=
    match nodes {
        List.empty => acc,
        List.cons n rest => found_nodes rest (found_node n acc),
    }

// Recursion over the node tree: `children` are subterms of `n`, but the
// walk threads them through `found_nodes`.
#[terminating]
def found_node (n : Html.Node) (acc : Found) : Found :=
    match n {
        Html.Node.node_element _ attrs children => found_nodes children (found_attrs attrs acc),
        Html.Node.node_void _ attrs => found_attrs attrs acc,
        Html.Node.node_fragment children => found_nodes children acc,
        _ => acc,
    }

/// The links of a page at `path` whose markup is `nodes`.
pub def Links.of_page (path : String) (nodes : List Html.Node) : PageLinks :=
    match found_nodes nodes { ids := List.empty, hrefs := List.empty } {
        { ids, hrefs } => { path := path, aliases := List.empty, ids := ids, hrefs := hrefs },
    }

/// The same page, reachable at `aliases` too.
pub def Links.with_aliases (aliases : List String) (p : PageLinks) : PageLinks :=
    { p with aliases := aliases }

/// The index of the last `/` in `s`, or -1.
def last_slash (s : String) : I64 :=
    String.find_last s "/"

/// The directory part of a page path, with its trailing `/` (`""` at root).
def dir_of (path : String) : String :=
    let i : I64 := last_slash path in
    if i < 0 then "" else String.slice path 0 (i + 1)

#[terminating]
def split_slashes (s : String) : List String :=
    let i : I64 := String.find_last s "/" in
    if i < 0
    then [s]
    else List.append (split_slashes (String.slice s 0 i)) [String.drop (i + 1) s]

/// Fold path segments onto a reversed stack, applying `.` and `..`.
def normalize (segments : List String) (stack : List String) : List String :=
    match segments {
        List.empty => List.reverse stack,
        List.cons seg rest =>
            if String.beq seg "." || String.is_empty seg then normalize rest stack
            else if String.beq seg ".." then normalize rest (pop stack)
            else normalize rest (List.cons seg stack),
    }

def pop (stack : List String) : List String :=
    match stack {
        List.empty => List.empty,
        List.cons _ rest => rest,
    }

/// A link's target page and fragment (`""` for none), when the gate checks
/// it: relative, and naming an `.html` page or only a fragment.
pub def Links.target (page : String) (href : String) : Option (Pair String String) :=
    if String.contains href "://" || String.starts_with "/" href || String.starts_with "mailto:" href
    then Option.none
    else split_target page href (String.find_last href "#")

def split_target (page : String) (href : String) (hash : I64) : Option (Pair String String) :=
    let file : String := if hash < 0 then href else String.slice href 0 hash in
    let frag : String := if hash < 0 then "" else String.drop (hash + 1) href in
    if String.is_empty file
    then Option.some (Pair.pair page frag)
    else if String.ends_with file ".html"
    then Option.some (Pair.pair (List.intercalate "/" (normalize (split_slashes (String.concat (dir_of page) file)) List.empty)) frag)
    else Option.none

def has_page (pages : List PageLinks) (path : String) : Option PageLinks :=
    match pages {
        List.empty => Option.none,
        List.cons p rest =>
            if String.beq p.path path || List.any (fn (a : String) => String.beq a path) p.aliases
            then Option.some p
            else has_page rest path,
    }

def has_id (page : PageLinks) (frag : String) : Bool :=
    String.is_empty frag || List.any (fn (i : String) => String.beq i frag) page.ids

/// Why one link is broken, or none when it resolves (or is not checked).
def check_href (pages : Shared (List PageLinks)) (from_page : String) (href : String) : Option String :=
    match Links.target from_page href {
        Option.none => Option.none,
        Option.some t => check_target pages from_page href t,
    }

def check_target (pages : Shared (List PageLinks)) (from_page : String) (href : String) (t : Pair String String) : Option String :=
    match t {
        Pair.pair path frag =>
            match has_page (Shared.get pages) path {
                Option.none => Option.some (broken from_page href "no such page"),
                Option.some p =>
                    if has_id p frag then Option.none else Option.some (broken from_page href "no such anchor"),
            },
    }

def broken (from_page : String) (href : String) (why : String) : String :=
    String.concat from_page (String.concat ": " (String.concat href (String.concat " (" (String.concat why ")"))))

def page_problems (pages : Shared (List PageLinks)) (p : PageLinks) : List String :=
    match p {
        { path, hrefs, .. } => List.filter_map (check_href pages path) (List.reverse hrefs),
    }

/// Every broken internal link across `pages`, as `page: href (why)`.
pub def Links.broken (pages : List PageLinks) : List String :=
    let all : Shared (List PageLinks) := Shared.of pages in
    problems_of all (Shared.get all)

def problems_of (all : Shared (List PageLinks)) (pages : List PageLinks) : List String :=
    match pages {
        List.empty => List.empty,
        List.cons p rest => List.append (page_problems all p) (problems_of all rest),
    }
