// Regenerate the unicode mote's tables from the Unicode character database.
//
//   monad run motes/unicode/src/tools/gen_tables.mo -- \
//       --ucd <dir> --out motes/unicode/src
//
// Add `--check` to verify the committed files are current instead of
// writing. <dir> holds these UCD 15.1.0 files (not vendored), from
// https://www.unicode.org/Public/15.1.0/ucd/ :
//
//   UnicodeData.txt  CaseFolding.txt  Scripts.txt  PropList.txt
//   DerivedCoreProperties.txt
//
// Writes three files under --out:
//
//   classify.mo  balanced-tree predicates over U32 (hot paths: a
//                classifier called per character)
//   fold.mo      full case folding (statuses C+F) as a tree
//   ranges.mo    range tables as fixed-width hex strings (lookup.mo
//                decodes them), and the simple case-fold orbits
//
// Every text input is walked as one `List U8`: `String.get` at a non-zero
// index pays a `strlen` compiled, and UnicodeData is 2 MB.

use gen::io {Gen.arg, Gen.banner, Gen.flag, Gen.write_or_check}
use gen::tree {Gen.emit, Leaf, Spec, leaf, spec}
use lang::construct {apps, con, con_app, global, if_, str, u32, var}
use lang::types {Term}
use lib::utf8 {Unicode.utf8_of_codepoint}
use std::io {IO.println, IO.read_file}
use std::list {List.filter, List.intercalate, List.sort_by}
use std::path {Path}
use std::stream {StreamError}

def base_url : String := "https://www.unicode.org/Public/15.1.0/ucd/"

def tool : String := "motes/unicode/src/tools/gen_tables.mo"

def max_cp : I64 := 1114111

// ─── Arguments and IO ───

def main (args : List String) : IO I64 :=
    match Gen.arg args "--ucd" {
        Option.some dir =>
            match Gen.arg args "--out" {
                Option.some out => run dir out (Gen.flag args "--check"),
                Option.none => usage,
            },
        Option.none => usage,
    }

def usage : IO I64 := do {
    let _printed <- IO.println "usage: gen_tables --ucd <dir> --out <motes/unicode/src> [--check]";
    return 2
}

def read_text (dir : String) (name : String) : IO String := do {
    let r <- IO.read_file (Path.path (String.concat_list [dir, "/", name]));
    return (text_or_empty r)
}

def text_or_empty (r : Result StreamError String) : String :=
    match r {
        Result.ok s => s,
        Result.err _ => "",
    }

def run (dir : String) (out : String) (check : Bool) : IO I64 := do {
    let ud <- read_text dir "UnicodeData.txt";
    let cf <- read_text dir "CaseFolding.txt";
    let sc <- read_text dir "Scripts.txt";
    let pl <- read_text dir "PropList.txt";
    let dc <- read_text dir "DerivedCoreProperties.txt";
    if String.is_empty ud || String.is_empty cf || String.is_empty sc || String.is_empty pl || String.is_empty dc
    then do {
        let _p <- IO.println "cannot read one of the UCD files under --ucd";
        return 3
    }
    else emit_all (build ud cf sc pl dc) out check
}

def emit_all (t : Tables) (out : String) (check : Bool) : IO I64 := do {
    let a <- Gen.write_or_check check (String.concat out "/classify.mo") (render_classify t);
    let b <- Gen.write_or_check check (String.concat out "/fold.mo") (render_fold t);
    let c <- Gen.write_or_check check (String.concat out "/ranges.mo") (render_ranges t);
    return (a + b + c)
}

// ─── Lines and fields over bytes ───

#[terminating]
def fold_left {A : Type} {B : Type} (f : B -> A -> B) (z : B) (xs : List A) : B :=
    match xs {
        List.empty => z,
        List.cons x rest => fold_left f (f z x) rest,
    }

/// Lines of a byte list (`\n`-terminated; `\r` is dropped), each as bytes.
def lines_of (text : String) : List (List U8) :=
    List.reverse (lines_go (String.to_list text) List.empty List.empty)

#[terminating]
def lines_go (xs : List U8) (cur : List U8) (acc : List (List U8)) : List (List U8) :=
    match xs {
        List.empty => if List.is_empty cur then acc else List.cons (List.reverse cur) acc,
        List.cons b rest =>
            if U8.beq b 10u8 then lines_go rest List.empty (List.cons (List.reverse cur) acc)
            else if U8.beq b 13u8 then lines_go rest cur acc
            else lines_go rest (List.cons b cur) acc,
    }

/// Everything before the first `#`.
#[terminating]
def strip_comment (xs : List U8) : List U8 :=
    match xs {
        List.empty => List.empty,
        List.cons b rest => if U8.beq b 35u8 then List.empty else List.cons b (strip_comment rest),
    }

/// Fields split on `;`, each with surrounding spaces trimmed, as strings.
def fields_of (xs : List U8) : List String :=
    List.map field_text (List.reverse (fields_go xs List.empty List.empty))

#[terminating]
def fields_go (xs : List U8) (cur : List U8) (acc : List (List U8)) : List (List U8) :=
    match xs {
        List.empty => List.cons (List.reverse cur) acc,
        List.cons b rest =>
            if U8.beq b 59u8 then fields_go rest List.empty (List.cons (List.reverse cur) acc)
            else fields_go rest (List.cons b cur) acc,
    }

def field_text (xs : List U8) : String := String.trim (String.from_list xs)

def field (fields : List String) (n : I64) : String :=
    match List.get n fields {
        Option.some s => s,
        Option.none => "",
    }

def hex_digit (b : U8) : I64 :=
    let c : I64 := U8.to_i64 b in
    if I64.lt c 58 then c - 48
    else if I64.lt c 71 then c - 55
    else c - 87

#[terminating]
def hex_go (xs : List U8) (acc : I64) : I64 :=
    match xs {
        List.empty => acc,
        List.cons b rest => hex_go rest (acc * 16 + hex_digit b),
    }

def hex_value (s : String) : I64 := hex_go (String.to_list s) 0

/// `0041` or `0041..005A`.
def parse_range (s : String) : Pair I64 I64 :=
    match String.index_of s ".." {
        Option.some i =>
            Pair.pair (hex_value (String.slice s 0 i))
                (hex_value (String.slice s (i + 2) (String.length s - i - 2))),
        Option.none => Pair.pair (hex_value s) (hex_value s),
    }

// ─── Range lists ───

def by_lo (a : Pair I64 I64) (b : Pair I64 I64) : Bool := I64.lt a.first b.first

/// Sort by `lo` and merge overlapping or adjacent ranges.
def normalize (rs : List (Pair I64 I64)) : List (Pair I64 I64) :=
    List.reverse (coalesce (List.sort_by by_lo rs) List.empty)

#[terminating]
def coalesce (xs : List (Pair I64 I64)) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match xs {
        List.empty => acc,
        List.cons r rest =>
            match acc {
                List.empty => coalesce rest (List.cons r List.empty),
                List.cons top below =>
                    if I64.lt (top.second + 1) r.first then coalesce rest (List.cons r (List.cons top below))
                    else coalesce rest
                        (List.cons (Pair.pair top.first (if I64.lt top.second r.second then r.second else top.second)) below),
            },
    }

/// The complement of a normalized list within [0, max_cp].
#[terminating]
def complement (rs : List (Pair I64 I64)) (next : I64) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match rs {
        List.empty => List.reverse (if I64.lt max_cp next then acc else List.cons (Pair.pair next max_cp) acc),
        List.cons r rest =>
            complement rest (r.second + 1)
                (if I64.lt next r.first then List.cons (Pair.pair next (r.first - 1)) acc else acc),
    }

/// Add `r` to `key`'s list in an association list (newest-first values).
#[terminating]
def add_to (key : String) (r : Pair I64 I64) (xs : List (Pair String (List (Pair I64 I64)))) : List (Pair String (List (Pair I64 I64))) :=
    match xs {
        List.empty => List.cons (Pair.pair key (List.cons r List.empty)) List.empty,
        List.cons entry rest =>
            match entry {
                Pair.pair k v =>
                    if String.beq k key then List.cons (Pair.pair k (List.cons r v)) rest
                    else List.cons (Pair.pair k v) (add_to key r rest),
            },
    }

#[terminating]
def lookup (key : String) (xs : List (Pair String (List (Pair I64 I64)))) : List (Pair I64 I64) :=
    match xs {
        List.empty => List.empty,
        List.cons entry rest =>
            match entry {
                Pair.pair k v => if String.beq k key then v else lookup key rest,
            },
    }

def normalize_all (xs : List (Pair String (List (Pair I64 I64)))) : List (Pair String (List (Pair I64 I64))) :=
    List.map normalize_entry xs

def normalize_entry (e : Pair String (List (Pair I64 I64))) : Pair String (List (Pair I64 I64)) :=
    match e {
        Pair.pair k v => Pair.pair k (normalize v),
    }

def union_all (lists : List (List (Pair I64 I64))) : List (Pair I64 I64) :=
    normalize (List.flatten lists)

// ─── UnicodeData: General_Category ───

struct GcState {
    cats : List (Pair String (List (Pair I64 I64))),
    /// The `First>` line of a block being read: its start.
    block_lo : I64,
}

def scan_gc (text : String) : List (Pair String (List (Pair I64 I64))) :=
    let st0 : GcState := { cats := List.empty, block_lo := 0 - 1 } in
    let st : GcState := fold_left gc_line st0 (lines_of text) in
    List.reverse st.cats

def gc_line (st : GcState) (line : List U8) : GcState :=
    let fs : List String := fields_of line in
    let code : String := field fs 0 in
    if String.is_empty code then st
    else gc_apply st (hex_value code) (field fs 1) (field fs 2)

def gc_apply (st : GcState) (cp : I64) (name : String) (cat : String) : GcState :=
    if String.ends_with name ", First>" then { st with block_lo := cp }
    else if String.ends_with name ", Last>" then
        { cats := add_to cat (Pair.pair st.block_lo cp) st.cats, block_lo := 0 - 1 }
    else { st with cats := add_to cat (Pair.pair cp cp) st.cats }

// ─── Property files: `range ; Name # comment` ───

def scan_props (text : String) : List (Pair String (List (Pair I64 I64))) :=
    List.reverse (fold_left prop_line List.empty (lines_of text))

def prop_line (acc : List (Pair String (List (Pair I64 I64)))) (line : List U8) : List (Pair String (List (Pair I64 I64))) :=
    let fs : List String := fields_of (strip_comment line) in
    let code : String := field fs 0 in
    if String.is_empty code then acc
    else add_to (field fs 1) (parse_range code) acc

// ─── CaseFolding ───

struct Folding {
    /// `cp -> UTF-8 text`, statuses C and F, ascending.
    full : List (Pair I64 String),
    /// `cp -> target`, statuses C and S.
    simple : List (Pair I64 I64),
}

def scan_folding (text : String) : Folding :=
    let st0 : Folding := { full := List.empty, simple := List.empty } in
    let st : Folding := fold_left fold_line st0 (lines_of text) in
    { full := List.reverse st.full, simple := List.reverse st.simple }

def fold_line (st : Folding) (line : List U8) : Folding :=
    let fs : List String := fields_of (strip_comment line) in
    let code : String := field fs 0 in
    if String.is_empty code then st
    else fold_apply st (hex_value code) (field fs 1) (field fs 2)

def fold_apply (st : Folding) (cp : I64) (status : String) (mapping : String) : Folding :=
    let full : List (Pair I64 String) :=
        if String.beq status "C" || String.beq status "F" then List.cons (Pair.pair cp (mapping_text mapping)) st.full
        else st.full in
    let simple : List (Pair I64 I64) :=
        if String.beq status "C" || String.beq status "S" then List.cons (Pair.pair cp (hex_value mapping)) st.simple
        else st.simple in
    { full := full, simple := simple }

/// `0069 0307` -> "i̇": each space-separated codepoint, UTF-8 encoded.
def mapping_text (field : String) : String :=
    String.concat_list (List.map mapping_word (List.filter non_empty (String.split field " ")))

def non_empty (s : String) : Bool := Bool.not (String.is_empty s)

def mapping_word (word : String) : String := Unicode.utf8_of_codepoint (hex_value word)

/// Orbit entries: each scalar with a simple fold, mapped to the other
/// members of its orbit (all scalars sharing its fold target, and the
/// target itself), ascending by scalar.
def orbit_entries (simple : List (Pair I64 I64)) : List (Pair I64 (List I64)) :=
    let groups : List (Pair I64 (List I64)) := fold_left group_by_target List.empty simple in
    List.sort_by entry_lt (List.flatten (List.map orbit_of_group groups))

def entry_lt (a : Pair I64 (List I64)) (b : Pair I64 (List I64)) : Bool := I64.lt a.first b.first

#[terminating]
def group_by_target (acc : List (Pair I64 (List I64))) (m : Pair I64 I64) : List (Pair I64 (List I64)) :=
    match acc {
        List.empty => List.cons (Pair.pair m.second (List.cons m.first List.empty)) List.empty,
        List.cons g rest =>
            match g {
                Pair.pair target members =>
                    if I64.beq target m.second then List.cons (Pair.pair target (List.cons m.first members)) rest
                    else List.cons (Pair.pair target members) (group_by_target rest m),
            },
    }

def orbit_of_group (g : Pair I64 (List I64)) : List (Pair I64 (List I64)) :=
    match g {
        Pair.pair target members =>
            let orbit : List I64 := List.sort_by I64.lt (List.cons target members) in
            List.map (fn (x : I64) => Pair.pair x (List.filter (fn (y : I64) => Bool.not (I64.beq x y)) orbit)) orbit,
    }

// ─── Everything ───

struct Tables {
    gc : List (Pair String (List (Pair I64 I64))),
    scripts : List (Pair String (List (Pair I64 I64))),
    white_space : List (Pair I64 I64),
    word : List (Pair I64 I64),
    digit : List (Pair I64 I64),
    punct_or_symbol : List (Pair I64 I64),
    folding : Folding,
    orbits : List (Pair I64 (List I64)),
}

def gc_codes : List String :=
    ["Lu", "Ll", "Lt", "Lm", "Lo", "Mn", "Mc", "Me", "Nd", "Nl", "No",
        "Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po", "Sm", "Sc", "Sk", "So",
        "Zs", "Zl", "Zp", "Cc", "Cf", "Cs", "Co"]

def build (ud : String) (cf : String) (sc : String) (pl : String) (dc : String) : Tables :=
    let gc0 : List (Pair String (List (Pair I64 I64))) := normalize_all (scan_gc ud) in
    let assigned : List (Pair I64 I64) := union_all (List.map (fn (c : String) => lookup c gc0) gc_codes) in
    let gc : List (Pair String (List (Pair I64 I64))) :=
        List.append (List.map (fn (c : String) => Pair.pair c (lookup c gc0)) gc_codes)
            [Pair.pair "Cn" (complement assigned 0 List.empty)] in
    let props : List (Pair String (List (Pair I64 I64))) := normalize_all (scan_props pl) in
    let derived : List (Pair String (List (Pair I64 I64))) := normalize_all (scan_props dc) in
    let folding : Folding := scan_folding cf in
    {
        gc := gc,
        scripts := normalize_all (scan_props sc),
        white_space := lookup "White_Space" props,
        word := union_all [lookup "Alphabetic" derived, lookup "Mn" gc, lookup "Mc" gc, lookup "Me" gc,
            lookup "Nd" gc, lookup "Pc" gc, lookup "Join_Control" props],
        digit := lookup "Nd" gc,
        punct_or_symbol := union_all (List.map (fn (c : String) => lookup c gc)
            ["Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po", "Sm", "Sc", "Sk", "So"]),
        folding := folding,
        orbits := orbit_entries folding.simple,
    }

// ─── classify.mo ───

def range_leaves (rs : List (Pair I64 I64)) : List Leaf := List.map range_leaf rs

/// `lo` alone takes `U32.beq`; anything wider needs both ends tested,
/// with the bounds stepped in by one because there is no `<=`.
def range_leaf (r : Pair I64 I64) : Leaf :=
    leaf (u32 r.first) (range_body r.first r.second)

def range_body (lo : I64) (hi : I64) : Term :=
    if I64.beq lo hi
    then apps (global "U32.beq") [var 0 "cp", u32 lo]
    else range_span lo hi

def range_span (lo : I64) (hi : I64) : Term :=
    if_ (apps (global "U32.lt") [u32 (lo - 1), var 0 "cp"])
        (apps (global "U32.lt") [var 0 "cp", u32 (hi + 1)])
        (global "false")

def pred_spec (name : String) : Spec :=
    spec name "cp" (global "U32") (global "Bool") "U32.lt" (global "false")

def render_classify (t : Tables) : String :=
    String.concat_list
        [Gen.banner tool
            [String.concat "Inputs: " base_url,
                "",
                "Predicates over a codepoint, each a balanced tree of one small",
                "function per node: a lookup is log2(ranges) comparisons, and no",
                "`else if` chain nests on the elaborator's stack."],
            "\n",
            Gen.emit (pred_spec "Unicode.is_space_separator") (range_leaves (lookup "Zs" t.gc)),
            Gen.emit (pred_spec "Unicode.is_punctuation_or_symbol") (range_leaves t.punct_or_symbol),
            Gen.emit (pred_spec "Unicode.is_white_space") (range_leaves t.white_space),
            Gen.emit (pred_spec "Unicode.is_word") (range_leaves t.word),
            Gen.emit (pred_spec "Unicode.is_digit") (range_leaves t.digit)]

// ─── fold.mo ───

def fold_spec : Spec :=
    spec "Unicode.case_fold_cp" "cp" (global "U32")
        (apps (global "Option") [global "String"])
        "U32.lt" (con "Option" "none")

def fold_leaf (f : Pair I64 String) : Leaf :=
    leaf (u32 f.first)
        (if_ (apps (global "U32.beq") [var 0 "cp", u32 f.first])
            (con_app "Option" "some" [str f.second])
            (con "Option" "none"))

def render_fold (t : Tables) : String :=
    String.concat_list
        [Gen.banner tool
            [String.concat "Input: " (String.concat base_url "CaseFolding.txt"),
                "",
                String.concat (I64.to_string (List.length t.folding.full))
                    " full case folding entries (statuses C and F), as a tree over",
                "codepoints. `Unicode.case_fold` (casefold.mo) walks a string with it."],
            "\n",
            Gen.emit fold_spec (List.map fold_leaf t.folding.full)]

// ─── ranges.mo ───

def hex_chars : String := "0123456789ABCDEF"

#[terminating]
def hex_fixed (v : I64) (n : I64) (acc : List String) : String :=
    if I64.lt 0 n then hex_fixed (I64.shr v 4) (n - 1) (List.cons (String.slice hex_chars (I64.and v 15) 1) acc)
    else String.concat_list acc

def hex6 (v : I64) : String := hex_fixed v 6 List.empty

def range_hex (r : Pair I64 I64) : String := String.concat (hex6 r.first) (hex6 r.second)

/// Pieces of at most `n` strings each, in order.
#[terminating]
def chunks (n : I64) (xs : List String) (cur : List String) (k : I64) (acc : List (List String)) : List (List String) :=
    match xs {
        List.empty => List.reverse (flush cur acc),
        List.cons x more =>
            if I64.beq k n then chunks n more (List.cons x List.empty) 1 (flush cur acc)
            else chunks n more (List.cons x cur) (k + 1) acc,
    }

def flush (cur : List String) (acc : List (List String)) : List (List String) :=
    if List.is_empty cur then acc else List.cons (List.reverse cur) acc

/// A string def whose body is `String.concat_list` over lines of hex.
def string_def (name : String) (doc : String) (pieces : List String) : String :=
    let lines : List String := List.map (fn (c : List String) => String.concat_list ["        \"", String.concat_list c, "\""])
        (chunks 6 pieces List.empty 0 List.empty) in
    String.concat_list
        [doc, "pub def ", name, " : String :=\n",
            if List.is_empty lines then "    \"\"\n"
            else String.concat_list ["    String.concat_list [\n", List.intercalate ",\n" lines, "]\n"],
            "\n"]

def ranges_def (name : String) (doc : String) (rs : List (Pair I64 I64)) : String :=
    string_def name doc (List.map range_hex rs)

/// A def name per table entry: `Unicode.gc_Lu`, `Unicode.sc_Old_Italic`.
def table_defs (prefix : String) (xs : List (Pair String (List (Pair I64 I64)))) : String :=
    String.concat_list (List.map (fn (e : Pair String (List (Pair I64 I64))) =>
        ranges_def (String.concat prefix e.first) "" e.second) xs)

def table_index (name : String) (doc : String) (prefix : String) (xs : List (Pair String (List (Pair I64 I64)))) : String :=
    String.concat_list
        [doc, "pub def ", name, " : List (Pair String String) :=\n    [",
            List.intercalate ",\n        "
                (List.map (fn (e : Pair String (List (Pair I64 I64))) =>
                    String.concat_list ["Pair.pair \"", e.first, "\" ", prefix, e.first]) xs),
            "]\n\n"]

def orbit_hex (e : Pair I64 (List I64)) : String :=
    String.concat_list (List.cons (hex6 e.first)
        (List.cons (String.slice hex_chars (List.length e.second) 1) (List.map hex6 e.second)))

/// The parts each end with a blank line; the file ends with one newline.
def render_ranges (t : Tables) : String :=
    let text : String := ranges_text t in
    if String.ends_with text "\n\n" then String.slice text 0 (String.length text - 1) else text

def ranges_text (t : Tables) : String :=
    String.concat_list
        [Gen.banner tool
            [String.concat "Inputs: " base_url,
                "",
                "Each range table is a string of fixed-width hex, 12 characters per",
                "inclusive range (LLLLLLHHHHHH), decoded by `Unicode.decode_ranges`",
                "(lookup.mo). A string literal costs the elaborator nothing, where a",
                "list literal of thousands of pairs nests that deep.",
                "",
                String.concat_list [I64.to_string (List.length t.gc), " General_Category values, ",
                    I64.to_string (List.length t.scripts), " scripts, ",
                    I64.to_string (List.length t.orbits), " simple case-fold orbit entries."]],
            "\n",
            table_defs "Unicode.gc_" t.gc,
            table_index "Unicode.gc_data" "/// Every General_Category value by its two-letter code.\n" "Unicode.gc_" t.gc,
            table_defs "Unicode.sc_" t.scripts,
            table_index "Unicode.script_data" "/// Every Script by its long name.\n" "Unicode.sc_" t.scripts,
            ranges_def "Unicode.white_space_data" "/// White_Space (PropList).\n" t.white_space,
            ranges_def "Unicode.word_data"
                "/// Alphabetic, Mark, Decimal_Number, Connector_Punctuation and Join_Control.\n" t.word,
            ranges_def "Unicode.digit_data" "/// Decimal_Number.\n" t.digit,
            string_def "Unicode.simple_fold_data"
                "/// Simple case-fold orbits (statuses C and S): per scalar, 6 hex digits,\n/// a 1-digit count, then the other orbit members at 6 digits each.\n"
                (List.map orbit_hex t.orbits)]
