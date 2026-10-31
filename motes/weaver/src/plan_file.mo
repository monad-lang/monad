/// A plan file: YAML frontmatter plus a Markdown body.
///
/// Plan mode writes `<session>/plan.md`; `/plan save` copies it to the
/// workspace's `plans/implementations/` under a dated slug. The frontmatter
/// is parsed with the yaml mote and the body is rendered by the normal
/// Markdown path, so a plan survives a restart and leaves the session as a
/// reviewable document.
///
/// Frontmatter is advisory: a malformed block yields a warning and the
/// body is still shown, because losing the plan is worse than losing its
/// metadata.
use init::string {}
use std::list {List.length}
use std::map {Map, BTreeMap}
use std::io {IO.write_file, IO.file_exists}
use std::path {Path}
use std::process {Proc.capture, exec_cmd}
use markdown::parse {Markdown.split_frontmatter}
use markdown::scan {Markdown.split_lines}
use markdown::types {Markdown.FrontSplit, Markdown.FrontFormat, Markdown.Frontmatter}
use yaml::yaml {Yaml, Yaml.ParseError, Yaml.parse, Yaml.to_string, Yaml.get_mapping, Yaml.get_str, Yaml.make_mapping_pairs, Yaml.make_str}
use weaver::store {StoreState, Store.child}

pub struct PlanMeta {
    title : String,
    session : String,
    created : String,
    updated : String,
    status : String,
    model : String,
}

pub struct PlanDoc {
    meta : PlanMeta,
    body : String,
}

/// A parsed plan plus a non-fatal frontmatter warning.
pub struct PlanParse {
    doc : PlanDoc,
    warning : Option String,
}

pub def PlanMeta.empty : PlanMeta :=
    { title := "", session := "", created := "", updated := "", status := "draft", model := "" }

// ─── Rendering ─────────────────────────────────────────────────────────

pub def PlanFile.render (d : PlanDoc) : String :=
    let pairs : List (Pair String Yaml) := [
        Pair.pair "title" (Yaml.make_str d.meta.title),
        Pair.pair "session" (Yaml.make_str d.meta.session),
        Pair.pair "created" (Yaml.make_str d.meta.created),
        Pair.pair "updated" (Yaml.make_str d.meta.updated),
        Pair.pair "status" (Yaml.make_str d.meta.status),
        Pair.pair "model" (Yaml.make_str d.meta.model),
    ] in
    let front : Yaml := Yaml.make_mapping_pairs pairs in
    String.concat "---\n" (String.concat (Yaml.to_string front) (String.concat "\n---\n\n" d.body))

// ─── Parsing ───────────────────────────────────────────────────────────

def yaml_str (key : String) (m : BTreeMap String Yaml) : String :=
    match Map.lookup key m {
        Option.none => "",
        Option.some y => match Yaml.get_str y {
            Result.ok s => s,
            Result.err _ => "",
        },
    }

/// A UTF-8-safe prefix: `String.slice` answers "" at a continuation
/// byte, so back off up to three bytes.
#[partial]
def cap_title (s : String) (max : I64) (back : I64) : String :=
    if I64.gt back 3 then ""
    else if I64.lt (max - back) 1 then ""
    else
        let x : String := String.slice s 0 (max - back) in
        if String.is_empty x then cap_title s max (back + 1) else x

/// The first heading or non-empty line, for a plan with no frontmatter.
#[partial]
def title_of (lines : List String) : String :=
    match lines {
        List.empty => "Untitled plan",
        List.cons l rest =>
            let t : String := String.trim l in
            if String.is_empty t then title_of rest
            else if String.starts_with "# " t then String.trim (String.drop 2 t)
            else if I64.gt (String.length t) 80 then cap_title t 80 0 else t,
    }

def title_of_text (text : String) : String :=
    title_of (Markdown.split_lines text)

pub def PlanFile.parse (text : String) : PlanParse :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter text in
    match split.front {
        Option.none =>
            let meta : PlanMeta := { PlanMeta.empty with title := title_of_text text } in
            { doc := { meta := meta, body := text }, warning := Option.none },
        Option.some f => match f.format {
            Markdown.FrontFormat.front_toml =>
                let meta : PlanMeta := { PlanMeta.empty with title := title_of_text split.body } in
                { doc := { meta := meta, body := split.body }, warning := Option.some "frontmatter is TOML, not YAML" },
            Markdown.FrontFormat.front_yaml => match Yaml.parse f.literal {
                Result.err e =>
                    let meta : PlanMeta := { PlanMeta.empty with title := title_of_text split.body } in
                    { doc := { meta := meta, body := split.body },
                      warning := Option.some (String.concat "frontmatter: " (Yaml.ParseError.to_string e)) },
                Result.ok y => match Yaml.get_mapping y {
                    Result.err e =>
                        let meta : PlanMeta := { PlanMeta.empty with title := title_of_text split.body } in
                        { doc := { meta := meta, body := split.body },
                          warning := Option.some (String.concat "frontmatter: " e) },
                    Result.ok m =>
                        let meta : PlanMeta := {
                            title := yaml_str "title" m,
                            session := yaml_str "session" m,
                            created := yaml_str "created" m,
                            updated := yaml_str "updated" m,
                            status := yaml_str "status" m,
                            model := yaml_str "model" m,
                        } in
                        let meta2 : PlanMeta := if String.is_empty meta.title then { meta with title := title_of_text split.body } else meta in
                        { doc := { meta := meta2, body := split.body }, warning := Option.none },
                },
            },
        },
    }

// ─── Session storage ───────────────────────────────────────────────────

pub def PlanFile.load_session (st : StoreState) : IO (Option PlanDoc) := do {
    let r <- Store.read_named st "plan.md";
    match r {
        Option.none => IO.pure Option.none,
        Option.some text => IO.pure (Option.some (PlanFile.parse text).doc),
    }
}

pub def PlanFile.save_session (st : StoreState) (d : PlanDoc) : IO (Result String Unit) := do {
    let r <- IO.write_file (Store.child st.dir "plan.md") (PlanFile.render d);
    match r {
        Result.ok _ => IO.pure (Result.ok unit),
        Result.err _ => IO.pure (Result.err "could not write plan.md"),
    }
}

// ─── Date and slug ─────────────────────────────────────────────────────

/// The UTC calendar day, from the same `date` fork the log filenames use
/// (the compiled clock is monotonic, so the time mote cannot supply a
/// wall-clock date).
pub def PlanFile.today : IO String := do {
    let r <- Proc.capture "date" ["+%Y-%m-%d"];
    match r {
        Pair.pair code out => if I64.beq code 0 then IO.pure (String.trim out) else IO.pure "unknown",
    }
}

def lower_u8 (b : U8) : U8 :=
    let n : U32 := U8.to_u32 b in
    if Bool.and (U32.lt 64u32 n) (U32.lt n 91u32)
    then U32.to_u8 (U32.add n 32u32)
    else b

def alnum_u8 (b : U8) : Bool :=
    let n : U32 := U8.to_u32 b in
    Bool.or (Bool.and (U32.lt 47u32 n) (U32.lt n 58u32))
        (Bool.and (U32.lt 96u32 n) (U32.lt n 123u32))

/// Lowercase ASCII, punctuation to `-`, runs collapsed, capped at 40
/// bytes. A title with no ASCII letters/numbers yields "plan".
#[partial]
def slug_go (bs : List U8) (last_dash : Bool) (n : I64) (acc : List U8) : List U8 :=
    if I64.lt n 1 then acc
    else match bs {
        List.empty => acc,
        List.cons b rest =>
            let lower : U8 := lower_u8 b in
            if alnum_u8 lower
            then slug_go rest false (n - 1) (List.append acc (List.cons lower List.empty))
            else if Bool.not last_dash
            then slug_go rest true (n - 1) (List.append acc (List.cons 45u8 List.empty))
            else slug_go rest true (n - 1) acc,
    }

#[partial]
def drop_leading_dashes (bs : List U8) : List U8 :=
    match bs {
        List.empty => List.empty,
        List.cons b rest => if U8.beq b 45u8 then drop_leading_dashes rest else bs,
    }

#[partial]
def drop_trailing_dashes (bs : List U8) : List U8 :=
    List.reverse (drop_leading_dashes (List.reverse bs))

pub def PlanFile.slug (title : String) : String :=
    // The byte cap lives in slug_go, so a multibyte title is never cut
    // mid-character (the old pre-slice could).
    let chars : List U8 := drop_trailing_dashes (drop_leading_dashes (slug_go (String.to_list title) true 40 List.empty)) in
    let s : String := String.from_list chars in
    if String.is_empty s then "plan" else s

// ─── The workspace copy ────────────────────────────────────────────────

def candidate (dir : String) (base : String) (n : I64) : String :=
    if I64.lt n 2
    then String.concat dir (String.concat "/" (String.concat base ".md"))
    else String.concat dir (String.concat "/" (String.concat base (String.concat "-" (String.concat (I64.to_string n) ".md"))))

#[partial]
def unique_path (dir : String) (base : String) (n : I64) : IO String := do {
    let p : String := candidate dir base n;
    let exists <- IO.file_exists (Path.path p);
    if exists then unique_path dir base (n + 1) else IO.pure p
}

/// Write `plans/implementations/<date>-<slug>.md` under `root`, never
/// overwriting an existing plan (a second save gets `-2`, `-3`, ...).
pub def PlanFile.save_repo (root : String) (d : PlanDoc) : IO (Result String String) := do {
    let day <- PlanFile.today;
    let base : String := String.concat day (String.concat "-" (PlanFile.slug d.meta.title));
    let dir : String := String.concat root "/plans/implementations";
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let path <- unique_path dir base 1;
    let r <- IO.write_file (Path.path path) (PlanFile.render d);
    match r {
        Result.ok _ => IO.pure (Result.ok path),
        Result.err _ => IO.pure (Result.err "could not write the plan file"),
    }
}
