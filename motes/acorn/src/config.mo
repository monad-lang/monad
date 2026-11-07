/// The site configuration, read from `docs/site.toml`.
///
/// It replaced `docs/book.toml` (mdBook) and `docs/site/config.toml` (Zola).
/// Paths are relative to the directory `acorn` runs in (the repo root).
use toml::toml {Toml.Value, Toml.ParseError, Toml.parse, Toml.table_get}

pub struct SiteConfig {
    /// The site title, shown in `<title>` and the header.
    title : String,
    /// The public origin, e.g. `https://monad-lang.org`.
    base_url : String,
    /// The book's markdown sources (`docs/src`).
    book_src : String,
    /// The book's location under the output root (`docs` → `/docs/`).
    book_dir : String,
    /// The output root (`docs/public`).
    out_dir : String,
    /// A tree copied as-is into the output root (a stylesheet, icons,
    /// images); `""` when the site has none.
    assets_dir : String := "",
    /// A second tree copied as-is into the output root, for content the
    /// site owns rather than the generator (a landing page's assets, static
    /// sub-sites); `""` when the site has none.
    static_dir : String := "",
}

/// Every field is a `String`, so duplicating the record shares only pointers.
pub instance Copy SiteConfig {
    def copy (c : SiteConfig) : Pair SiteConfig SiteConfig := Pair.pair c c
}

/// Look a key up in a TOML table value; anything else has no keys.
def field (key : String) (v : Toml.Value) : Option Toml.Value :=
    match v {
        Toml.Value.table t => Toml.table_get key t,
        _ => Option.none,
    }

/// A string at `key`, or `fallback` when the key is absent. A present key of
/// another type is an error, not a silent default.
def string_or (key : String) (fallback : String) (v : Toml.Value) : Result String String :=
    match field key v {
        Option.none => Result.ok fallback,
        Option.some found => as_string key found,
    }

def as_string (key : String) (v : Toml.Value) : Result String String :=
    match v {
        Toml.Value.string s => Result.ok s,
        _ => Result.err (String.concat key ": expected a string"),
    }

/// The table at `key`, or a value with no keys when absent (an empty array:
/// `field` finds nothing in it).
def table_or_empty (key : String) (v : Toml.Value) : Toml.Value :=
    match field key v {
        Option.some t => t,
        Option.none => Toml.Value.array List.empty,
    }

def parse_error_text (e : Toml.ParseError) : String :=
    match e {
        Toml.ParseError.expected want found =>
            String.concat "expected " (String.concat want (String.concat ", found " found)),
        Toml.ParseError.generic msg => msg,
    }

def book_of (book : Shared Toml.Value) (title : String) (base_url : String) (out_dir : String) (assets_dir : String) (static_dir : String) : Result String SiteConfig := do {
    let book_src <- string_or "src" "docs/src" (Shared.get book);
    let book_dir <- string_or "dir" "docs" (Shared.get book);
    let cfg : SiteConfig :=
        { title := title, base_url := base_url, book_src := book_src,
            book_dir := book_dir, out_dir := out_dir, assets_dir := assets_dir, static_dir := static_dir };
    return cfg
}

def of_value (root_value : Toml.Value) : Result String SiteConfig :=
    let root : Shared Toml.Value := Shared.of root_value in
    do {
        let title <- string_or "title" "Monad language" (Shared.get root);
        let base_url <- string_or "base_url" "/" (Shared.get root);
        let out_dir <- string_or "out" "docs/public" (Shared.get root);
        let assets_dir <- string_or "assets" "" (Shared.get root);
        let static_dir <- string_or "static" "" (Shared.get root);
        book_of (Shared.of (table_or_empty "book" (Shared.get root))) title base_url out_dir assets_dir static_dir
    }

/// Parse `site.toml` text. Absent keys take the monad-lang.org defaults.
pub def SiteConfig.parse (src : String) : Result String SiteConfig :=
    match Toml.parse src {
        Result.err e => Result.err (String.concat "site.toml: " (parse_error_text e)),
        Result.ok t => of_value (Toml.Value.table t),
    }

/// The output directory with `--out` applied.
pub def SiteConfig.with_out (out : Option String) (cfg : SiteConfig) : SiteConfig :=
    match out {
        Option.some dir => { cfg with out_dir := dir },
        Option.none => cfg,
    }
