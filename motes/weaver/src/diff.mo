/// Weaver's approval diff -- weaver.md Phase 5: when the gate asks about
/// a `write` or `edit` pick, the human sees WHAT WOULD CHANGE, not just
/// a JSON blob. `Diff.render` is the pure line-based old -> new render
/// (common prefix/suffix trimmed, the middle marked `- `/`+ `); the
/// `edit` tool's own input already carries both sides
/// (`expected_content`/`new_content`), and `write`'s old side is the
/// file on disk (empty when the file is new).
///
/// Line splitting is byte-walked and splits ONLY on `'\n'` (0x0A), so it
/// is UTF-8-safe: a multi-byte sequence never contains that byte, so no
/// line boundary can land mid-character. `Diff.render` itself stays
/// pure -- the gate (`gate.mo`) owns the I/O and the display cap.
use json::json {Json, Json.get_object, Json.object_get, Json.get_str}
use std::io {IO.file_exists, IO.read_file}
use std::path {Path.of}

/// Split a string into lines at `'\n'` (no phantom empty line after a
/// trailing newline; an empty string is no lines).
pub def Diff.lines (s : String) : List String :=
    lines_walk s 0 0 []

#[partial]
def lines_walk (s : String) (i : I64) (start : I64) (acc : List String) : List String :=
    if String.length s < i + 1
    then lines_done s start acc
    else if String.slice s i 1 == "\n"
    then lines_walk s (i + 1) (i + 1) (List.cons (String.slice s start (i - start)) acc)
    else lines_walk s (i + 1) start acc

def lines_done (s : String) (start : I64) (acc : List String) : List String :=
    if start < String.length s
    then List.reverse (List.cons (String.slice s start (String.length s - start)) acc)
    else List.reverse acc

/// The line-based old -> new render: the common prefix and suffix are
/// trimmed, the changed middle shows old lines as `- ` and new lines as
/// `+ `. Identical inputs render as the empty string.
pub def Diff.render (old : String) (new : String) : String :=
    render_lines (Diff.lines old) (Diff.lines new)

def render_lines (a : List String) (b : List String) : String :=
    let p : I64 := common_prefix a b in
    let total_a : I64 := line_count a in
    let total_b : I64 := line_count b in
    let s : I64 := capped (common_prefix (List.reverse a) (List.reverse b)) (min_of (total_a - p) (total_b - p)) in
    mid_block
        (drop_lines p (take_lines (total_a - s) a))
        (drop_lines p (take_lines (total_b - s) b))

/// `- ` lines then `+ ` lines, one per changed line -- empty when
/// nothing changed (the prompt then shows no block at all).
def mid_block (mid_old : List String) (mid_new : List String) : String :=
    if list_empty mid_old && list_empty mid_new
    then ""
    else List.intercalate "\n" (List.append (tag_lines "- " mid_old) (tag_lines "+ " mid_new))

def common_prefix (a : List String) (b : List String) : I64 :=
    prefix_walk a b 0

#[partial]
def prefix_walk (xs : List String) (ys : List String) (n : I64) : I64 :=
    match xs {
        List.empty => n,
        List.cons x xr => match ys {
            List.empty => n,
            List.cons y yr => if x == y then prefix_walk xr yr (n + 1) else n,
        },
    }

#[partial]
def line_count (xs : List String) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + line_count rest,
    }

#[partial]
def take_lines (n : I64) (xs : List String) : List String :=
    if n < 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take_lines (n - 1) rest),
    }

#[partial]
def drop_lines (n : I64) (xs : List String) : List String :=
    if n < 1 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => drop_lines (n - 1) rest,
    }

#[partial]
def tag_lines (tag : String) (xs : List String) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (String.concat tag x) (tag_lines tag rest),
    }

def list_empty (xs : List String) : Bool :=
    match xs { List.empty => true, _ => false }

def min_of (a : I64) (b : I64) : I64 := if a < b then a else b

def capped (v : I64) (m : I64) : I64 := if v > m then m else v

// ── From a pick's input JSON to the diff's two sides ────────────────────

/// The `(old, new)` pair a `write`/`edit` pick is about to produce, or
/// none when the pick is not a file mutation (nothing to show). `edit`
/// carries both sides in its own input; `write`'s old side is the file
/// on disk, empty when the file does not exist yet -- a new file's diff
/// is all `+ ` lines.
pub def Diff.for_input (name : String) (input : Json) : IO (Option (Pair String String)) :=
    if name == "edit"
    then edit_pair input
    else if name == "write"
    then write_pair input
    else IO.pure Option.none

def edit_pair (input : Json) : IO (Option (Pair String String)) :=
    match str_field "expected_content" input {
        Option.none => IO.pure Option.none,
        Option.some old => match str_field "new_content" input {
            Option.none => IO.pure Option.none,
            Option.some new => IO.pure (Option.some (Pair.pair old new)),
        },
    }

def write_pair (input : Json) : IO (Option (Pair String String)) :=
    match str_field "path" input {
        Option.none => IO.pure Option.none,
        Option.some path => match str_field "content" input {
            Option.none => IO.pure Option.none,
            Option.some new => read_old path new,
        },
    }

def read_old (path : String) (new : String) : IO (Option (Pair String String)) :=
    match Path.of path {
        Result.err _ => IO.pure Option.none,
        Result.ok p => read_old_at p new,
    }

def read_old_at (p : Path) (new : String) : IO (Option (Pair String String)) := do {
    let exists <- IO.file_exists p;
    old_of exists p new
}

def old_of (exists : Bool) (p : Path) (new : String) : IO (Option (Pair String String)) :=
    if Bool.not exists then IO.pure (Option.some (Pair.pair "" new)) else old_read p new

def old_read (p : Path) (new : String) : IO (Option (Pair String String)) := do {
    let text <- IO.read_file p;
    return (Option.some (Pair.pair text new))
}

def str_field (key : String) (j : Json) : Option String :=
    match Json.get_object j {
        Result.err _ => Option.none,
        Result.ok o => field_of (Json.object_get key o),
    }

def field_of (v : Option Json) : Option String :=
    match v {
        Option.none => Option.none,
        Option.some j => match Json.get_str j {
            Result.ok s => Option.some s,
            Result.err _ => Option.none,
        },
    }
