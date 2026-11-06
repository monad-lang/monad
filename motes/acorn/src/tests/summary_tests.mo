/// `SUMMARY.md` parsing and reading order.
use std::list {List.intercalate}
use lib::summary {NavEntry, NavChapter, Summary.parse, Summary.chapters, Summary.stem_of_link}
use lib::site {ChapterPage, Site.with_neighbours}

def sample : String :=
    "# Summary\n\n- [Intro](./intro.md)\n\n# Tutorial\n\n- [Types](./types.md)\n    - [Structs](./structs.md)\n- [IO](io.md)\n"

def entry_text (e : NavEntry) : String :=
    match e {
        NavEntry.part title => String.concat "part:" title,
        NavEntry.chapter title stem depth =>
            String.concat title (String.concat "@" (String.concat stem (String.concat "/" (I64.to_string depth)))),
    }

#[test]
def test_parse_parts_chapters_and_depth : Bool :=
    let got : List String := List.map entry_text (Summary.parse sample) in
    String.beq (List.intercalate "," got) "Intro@intro/0,part:Tutorial,Types@types/0,Structs@structs/1,IO@io/0"

#[test]
def test_stem_of_link_rejects_non_markdown : Bool :=
    match Summary.stem_of_link "https://example.com" {
        Option.some _ => false,
        Option.none => true,
    }

def neighbours_text (p : ChapterPage) : String :=
    match p {
        { chapter, prev, next } =>
            String.concat (stem_or "-" prev) (String.concat "<" (String.concat chapter.stem (String.concat ">" (stem_or "-" next)))),
    }

def stem_or (fallback : String) (c : Option NavChapter) : String :=
    match c {
        Option.some ch => ch.stem,
        Option.none => fallback,
    }

#[test]
def test_reading_order_neighbours : Bool :=
    let pages : List ChapterPage := Site.with_neighbours Option.none (Summary.chapters (Summary.parse sample)) in
    String.beq (List.intercalate " " (List.map neighbours_text pages))
        "-<intro>types intro<types>structs types<structs>io structs<io>-"
