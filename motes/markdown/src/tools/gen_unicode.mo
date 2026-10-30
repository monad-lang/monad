// Regenerate src/unicode.mo from the Unicode character database.
//
//   monad run motes/markdown/src/tools/gen_unicode.mo -- \
//       --unicode-data UnicodeData.txt --case-folding CaseFolding.txt \
//       --out motes/markdown/src/unicode.mo
//
// Add `--check` to verify the committed file is current instead of writing.
// Inputs (not vendored):
//   https://www.unicode.org/Public/15.1.0/ucd/UnicodeData.txt
//   https://www.unicode.org/Public/15.1.0/ucd/CaseFolding.txt
//
// Emits the whitespace and punctuation classifiers as balanced trees over
// codepoint ranges and the full case folding (statuses C and F) as a tree
// over codepoints, then appends the two recursive defs that walk a string:
// they are not table-shaped, so they stay verbatim source.

use gen::io {Gen.arg, Gen.banner, Gen.write_or_check}
use gen::tree {Gen.emit, Leaf, Spec, leaf, spec}
use lang::construct {apps, con, con_app, global, if_, str, u32, var}
use lang::types {Term}
use lib::scan {Markdown.split_lines, Markdown.utf8_of_codepoint}
use parsec::number {char_to_hex_digit}
use std::io {IO.println, IO.read_file}
use std::list {List.length}
use std::path {Path}
use std::stream {StreamError}

def ud_url : String := "https://www.unicode.org/Public/15.1.0/ucd/UnicodeData.txt"

def cf_url : String := "https://www.unicode.org/Public/15.1.0/ucd/CaseFolding.txt"

def tool : String := "motes/markdown/src/tools/gen_unicode.mo"

// --- Arguments and IO ---

def main (args : List String) : IO I64 :=
    match Gen.arg args "--unicode-data" {
        Option.some ud => with_folding args ud,
        Option.none => usage,
    }

def with_folding (args : List String) (ud : String) : IO I64 :=
    match Gen.arg args "--case-folding" {
        Option.some cf => with_out args ud cf,
        Option.none => usage,
    }

def with_out (args : List String) (ud : String) (cf : String) : IO I64 :=
    match Gen.arg args "--out" {
        Option.some out => do {
            let ud_raw <- IO.read_file (Path.path ud);
            let cf_raw <- IO.read_file (Path.path cf);
            let code <- generate ud_raw cf_raw out (Gen.arg args "--check");
            return code
        },
        Option.none => usage,
    }

def usage : IO I64 := do {
    let _printed <- IO.println
        "usage: gen_unicode --unicode-data <UnicodeData.txt> --case-folding <CaseFolding.txt> --out <unicode.mo> [--check]";
    return 2
}

def generate (ud : Result StreamError String) (cf : Result StreamError String)
    (out : String) (check : Option String) : IO I64 :=
    match ud {
        Result.err e => fail_with (String.concat "cannot read UnicodeData: " e.message),
        Result.ok ud_text => after_ud ud_text cf out check,
    }

def after_ud (ud_text : String) (cf : Result StreamError String)
    (out : String) (check : Option String) : IO I64 :=
    match cf {
        Result.err e => fail_with (String.concat "cannot read CaseFolding: " e.message),
        Result.ok cf_text => Gen.write_or_check (check_wanted check) out (render ud_text cf_text),
    }

def fail_with (message : String) : IO I64 := do {
    let _printed <- IO.println message;
    return 3
}

def check_wanted (check : Option String) : Bool :=
    match check {
        Option.some _ => true,
        Option.none => false,
    }

// --- Scanning ---

/// The two classifier sets. Held newest-first while scanning -- the input
/// ascends, so only the head can ever merge -- and reversed at the end.
struct Ranges {
    ws : List (Pair I64 I64),
    punct : List (Pair I64 I64),
}

/// The `First>`/`Last>` block being scanned. UnicodeData writes a whole
/// block as two lines and only the block's category decides membership,
/// so nothing is emitted until its `Last>` line arrives.
struct Block {
    lo : I64,
    ws : Bool,
    punct : Bool,
}

struct ScanState {
    ranges : Ranges,
    block : Option Block,
}

/// Tab, LF, FF and CR are whitespace by CommonMark's own list rather than
/// by category (they are `Cc`), so they seed the set; the rest is `Zs`.
def empty_state : ScanState :=
    { ranges := { ws := List.cons (Pair.pair 9 10) (List.cons (Pair.pair 12 13) List.empty),
                  punct := List.empty },
      block := Option.none }

#[partial]
def scan_lines (lines : List String) (st : ScanState) : ScanState :=
    match lines {
        List.empty => st,
        List.cons line tl => scan_lines tl (scan_line line st),
    }

def scan_line (line : String) (st : ScanState) : ScanState :=
    scan_fields (split_on line ";") st

def scan_fields (fields : List String) (st : ScanState) : ScanState :=
    if String.is_empty (field_or fields 0)
    then st
    else apply_fields (hex_value (field_or fields 0)) (field_or fields 1) (field_or fields 2) st

def apply_fields (cp : I64) (name : String) (category : String) (st : ScanState) : ScanState :=
    if String.ends_with name ", First>"
    then open_block cp (is_ws_category category) (is_punct_category category) st
    else if String.ends_with name ", Last>"
    then close_block cp st
    else scan_member cp (is_ws_category category) (is_punct_category category) st

def open_block (cp : I64) (ws : Bool) (punct : Bool) (st : ScanState) : ScanState :=
    { ranges := st.ranges, block := Option.some (block_of cp ws punct) }

def block_of (cp : I64) (ws : Bool) (punct : Bool) : Block :=
    { lo := cp, ws := ws, punct := punct }

def close_block (hi : I64) (st : ScanState) : ScanState :=
    match st.block {
        Option.none => st,
        Option.some b => { ranges := include_block b hi st.ranges, block := Option.none },
    }

def include_block (b : Block) (hi : I64) (ranges : Ranges) : Ranges :=
    { ws := include_if b.ws ranges.ws b.lo hi,
      punct := include_if b.punct ranges.punct b.lo hi }

def scan_member (cp : I64) (ws : Bool) (punct : Bool) (st : ScanState) : ScanState :=
    { ranges := { ws := include_if ws st.ranges.ws cp cp,
                  punct := include_if punct st.ranges.punct cp cp },
      block := st.block }

def include_if (wanted : Bool) (rs : List (Pair I64 I64)) (lo : I64) (hi : I64)
    : List (Pair I64 I64) :=
    if wanted then include_range rs lo hi else rs

/// Merge `[lo, hi]` into a DESCENDING range list. The input ascends, so a
/// merge can only ever touch the head: every older range ends below it.
def include_range (rs : List (Pair I64 I64)) (lo : I64) (hi : I64) : List (Pair I64 I64) :=
    match rs {
        List.empty => List.cons (Pair.pair lo hi) List.empty,
        List.cons hd tl =>
            if I64.lt (I64.add hd.second 1) lo
            then List.cons (Pair.pair lo hi) rs
            else List.cons (Pair.pair hd.first hi) tl,
    }

def is_ws_category (category : String) : Bool :=
    String.beq "Zs" category

def is_punct_category (category : String) : Bool :=
    Bool.or (String.starts_with "P" category) (String.starts_with "S" category)

#[partial]
def scan_folding (text : String) : List (Pair I64 String) :=
    List.reverse (folding_lines (Markdown.split_lines text) List.empty)

#[partial]
def folding_lines (lines : List String) (acc : List (Pair I64 String))
    : List (Pair I64 String) :=
    match lines {
        List.empty => acc,
        List.cons line tl => folding_lines tl (fold_entry line acc),
    }

def fold_entry (line : String) (acc : List (Pair I64 String)) : List (Pair I64 String) :=
    if Bool.or (String.is_empty line) (String.starts_with "#" line)
    then acc
    else fold_fields (split_on (comment_stripped line) ";") acc

def comment_stripped (line : String) : String :=
    match List.first (split_on line "#") {
        Option.some s => s,
        Option.none => "",
    }

def fold_fields (fields : List String) (acc : List (Pair I64 String))
    : List (Pair I64 String) :=
    if fold_status_kept (fold_status_of fields)
    then fold_insert (hex_value (field_or fields 0)) (mapping_text (field_or fields 2)) acc
    else acc

/// The two statuses that make up the full case folding; `T` (Turkic) and
/// `S` (simple, superseded by `F`) are skipped, as the spec says.
def fold_status_kept (status : String) : Bool :=
    Bool.or (String.beq "C" status) (String.beq "F" status)

/// A later line for the same codepoint wins: the input groups them
/// adjacently and ascending, so the head is the previous entry.
def fold_insert (cp : I64) (value : String) (acc : List (Pair I64 String))
    : List (Pair I64 String) :=
    match acc {
        List.empty => List.cons (Pair.pair cp value) List.empty,
        List.cons hd tl =>
            if I64.beq hd.first cp
            then List.cons (Pair.pair cp value) tl
            else List.cons (Pair.pair cp value) acc,
    }

/// `0069 0307` -> "i̇": every space-separated codepoint, UTF-8 encoded.
def mapping_text (field : String) : String :=
    String.concat_list (List.map mapping_word (split_on field " "))

def mapping_word (word : String) : String :=
    Markdown.utf8_of_codepoint (hex_value word)

// --- Text helpers ---

/// Split `s` on every `sep`, dropping empty pieces.
#[partial]
def split_on (s : String) (sep : String) : List String :=
    split_on_go s sep 0 0 List.empty

#[partial]
def split_on_go (s : String) (sep : String) (start : I64) (i : I64) (acc : List String)
    : List String :=
    if I64.lt (String.length s) (I64.add i 1)
    then List.reverse (push_piece s start (String.length s) acc)
    else split_on_step s sep start i acc (String.beq sep (String.slice s i 1))

#[partial]
def split_on_step (s : String) (sep : String) (start : I64) (i : I64)
    (acc : List String) (at_sep : Bool) : List String :=
    if at_sep
    then split_on_go s sep (I64.add i 1) (I64.add i 1) (push_piece s start i acc)
    else split_on_go s sep start (I64.add i 1) acc

def push_piece (s : String) (start : I64) (stop : I64) (acc : List String) : List String :=
    if I64.beq start stop
    then acc
    else List.cons (String.slice s start (I64.sub stop start)) acc

def field_or (fields : List String) (n : I64) : String :=
    match List.get n fields {
        Option.some s => s,
        Option.none => "",
    }

/// CaseFolding pads its status field with spaces ("0041; C; 0061").
def fold_status_of (fields : List String) : String :=
    String.trim (field_or fields 1)

/// A hexadecimal codepoint field (`0041`, `1D504`).
#[partial]
def hex_value (digits : String) : I64 :=
    hex_value_go digits 0 0

#[partial]
def hex_value_go (digits : String) (i : I64) (acc : I64) : I64 :=
    if I64.lt (String.length digits) (I64.add i 1)
    then acc
    else hex_value_go digits (I64.add i 1)
            (I64.add (I64.mul acc 16) (char_to_hex_digit (String.slice digits i 1)))

// --- Leaves and source ---

def ws_spec : Spec :=
    spec "Markdown.is_unicode_whitespace" "cp" (global "U32") (global "Bool")
        "U32.lt" (global "false")

def punct_spec : Spec :=
    spec "Markdown.is_unicode_punctuation" "cp" (global "U32") (global "Bool")
        "U32.lt" (global "false")

def fold_spec : Spec :=
    spec "Markdown.case_fold_cp" "cp" (global "U32")
        (apps (global "Option") [global "String"])
        "U32.lt" (con "Option" "none")

#[partial]
def range_leaves (rs : List (Pair I64 I64)) : List Leaf :=
    match rs {
        List.empty => List.empty,
        List.cons hd tl => List.cons (range_leaf hd) (range_leaves tl),
    }

/// `lo` alone takes `U32.beq`; anything wider needs both ends tested,
/// with the bounds stepped in by one because there is no `<=`.
def range_leaf (r : Pair I64 I64) : Leaf :=
    leaf (u32 r.first) (range_body r.first r.second)

def range_body (lo : I64) (hi : I64) : Term :=
    if I64.beq lo hi
    then apps (global "U32.beq") [var 0 "cp", u32 lo]
    else range_span lo hi

def range_span (lo : I64) (hi : I64) : Term :=
    if_ (apps (global "U32.lt") [u32 (I64.sub lo 1), var 0 "cp"])
        (apps (global "U32.lt") [var 0 "cp", u32 (I64.add hi 1)])
        (global "false")

#[partial]
def fold_leaves (fs : List (Pair I64 String)) : List Leaf :=
    match fs {
        List.empty => List.empty,
        List.cons hd tl => List.cons (fold_leaf hd) (fold_leaves tl),
    }

def fold_leaf (f : Pair I64 String) : Leaf :=
    leaf (u32 f.first)
        (if_ (apps (global "U32.beq") [var 0 "cp", u32 f.first])
            (con_app "Option" "some" [str f.second])
            (con "Option" "none"))

def use_lines : String :=
    "use init::string {}\nuse parsec::core {is_empty}\nuse lib::scan {Markdown.char_width, Markdown.codepoint_at}\n\n"

/// The string-walking pair is hand-written source, not a table.
def tail_block : String :=
    String.concat_list (List.map line_of tail_lines)

def line_of (s : String) : String := String.concat s "\n"

def tail_lines : List String :=
    [ "/// Case-fold a string for reference-label comparison.",
      "#[partial]",
      "pub def Markdown.case_fold (s : String) : String :=",
      "    String.concat_list (List.reverse (Markdown.case_fold_go s List.empty))",
      "",
      "#[partial]",
      "def Markdown.case_fold_go (s : String) (acc : List String) : List String :=",
      "    if is_empty s",
      "    then acc",
      "    else",
      "        match Markdown.codepoint_at s {",
      "            Option.none => acc,",
      "            Option.some cp =>",
      "                match Markdown.case_fold_cp cp {",
      "                    Option.some folded =>",
      "                        Markdown.case_fold_go (String.drop (Markdown.char_width s) s)",
      "                            (List.cons folded acc),",
      "                    Option.none =>",
      "                        Markdown.case_fold_go (String.drop (Markdown.char_width s) s)",
      "                            (List.cons (String.slice s 0 (Markdown.char_width s)) acc)",
      "                }",
      "        }" ]

def render (ud_text : String) (cf_text : String) : String :=
    let state : ScanState := scan_lines (Markdown.split_lines ud_text) empty_state in
    let folds : List (Pair I64 String) := scan_folding cf_text in
    let ws : List (Pair I64 I64) := List.reverse state.ranges.ws in
    let punct : List (Pair I64 I64) := List.reverse state.ranges.punct in
    let parts : List String :=
        [ Gen.banner tool (banner_notes (List.length ws) (List.length punct) (List.length folds)),
          use_lines,
          Gen.emit ws_spec (range_leaves ws),
          Gen.emit punct_spec (range_leaves punct),
          Gen.emit fold_spec (fold_leaves folds),
          tail_block ] in
    String.concat_list parts

def banner_notes (ws : I64) (punct : I64) (folds : I64) : List String :=
    [ String.concat "UnicodeData: " ud_url,
      String.concat "CaseFolding: " cf_url,
      "",
      String.concat (String.concat (I64.to_string ws) " whitespace ranges, ")
          (String.concat (String.concat (I64.to_string punct) " punctuation ranges, ")
              (String.concat (I64.to_string folds) " case folding entries.")),
      "",
      "Each classifier is a balanced tree of one small function per node, so a",
      "lookup costs log2(ranges) comparisons and checking the whole corpus",
      "cannot nest an `else if` chain on the elaborator's stack. The range and",
      "folding tables are grouped under their `Markdown.` entry points." ]
