/// A declaration as tooling shows it: its span trimmed to the text the
/// user wrote, and its name's own range, both read back from the source.
///
/// The parser stamps a declaration from the input it started at to the
/// remainder it left (`pd_at`). A def's parse consumes the whitespace and
/// comment lines after it, so its span runs to the next declaration's first
/// byte; a `struct`/`type`/`class` stops at its `}`. The name gets no
/// position at all. Both are recovered here from the text, which leaves the
/// compiler untouched: the end drops trailing whitespace and whole comment
/// lines, and the name is the first whole-word occurrence on the header
/// line, after the leading comments and `#[...]` attributes.
///
/// Every scan below makes ONE self-call, so the compiled backend's
/// tail-call rewrite turns it into a loop.
use lang::types {Location, SourceRange}
use lang::module {DeclRange, decl_range_kind, decl_range_name, decl_range_span, decl_ranges_of_source}
use std::list {List.length}

/// One declaration of a file's outline. `range` is the declaration as
/// written, from its first token to its last; `name_range` is the name's
/// extent inside it, or `range` itself when the header has no whole-word
/// name (an unnamed instance's `_`).
pub struct DeclText {
    name : String,
    kind : String,
    range : SourceRange,
    name_range : SourceRange,
}

pub def decl_text_name (d : DeclText) : String := d.name

pub def decl_text_kind (d : DeclText) : String := d.kind

pub def decl_text_span (d : DeclText) : SourceRange := d.range

pub def decl_text_name_span (d : DeclText) : SourceRange := d.name_range

/// The compiler's declaration ranges for `src`, trimmed and named. The
/// ranges come in source order, so `src` is turned into bytes once and
/// walked forward.
#[partial]
pub def decl_texts (src : String) (ranges : List DeclRange) : List DeclText :=
    decl_texts_go (String.to_list src) 0 ranges List.empty

/// `decl_texts` over the declarations `src` parses to.
#[partial]
pub def decl_texts_of_source (src : String) : List DeclText :=
    decl_texts src (decl_ranges_of_source src)

/// `bytes` is the file from byte `pos` on.
#[partial]
def decl_texts_go (bytes : List U8) (pos : I64) (ranges : List DeclRange) (acc : List DeclText)
    : List DeclText :=
    match ranges {
        List.empty => List.reverse acc,
        List.cons dr rest =>
            let sp : SourceRange := decl_range_span dr in
            let off : I64 := sp.start.offset in
            let here : List U8 := dt_drop bytes (off - pos) in
            decl_texts_go here off rest (List.cons (decl_text_of dr sp here) acc),
    }

#[partial]
def decl_text_of (dr : DeclRange) (sp : SourceRange) (bytes : List U8) : DeclText :=
    let name : String := decl_range_name dr in
    match decl_text_ranges bytes sp.start (sp.end.offset - sp.start.offset) name {
        Pair.pair trimmed named =>
            let d : DeclText := {
                name := name,
                kind := decl_range_kind dr,
                range := { trimmed with path := sp.path },
                name_range := { named with path := sp.path },
            } in
            d,
    }

def dt_nl : U8 := 10u8

def dt_slash : U8 := 47u8

def dt_hash : U8 := 35u8

def dt_lbracket : U8 := 91u8

def dt_rbracket : U8 := 93u8

def dt_quote : U8 := 34u8

def dt_backslash : U8 := 92u8

def dt_is_ws (b : U8) : Bool :=
  U8.beq b 32u8 || U8.beq b 9u8 || U8.beq b dt_nl || U8.beq b 13u8

/// A byte that continues a name: alphanumeric, `_`, `'` or `.` (a dotted
/// def name is one name).
def dt_is_name_byte (b : U8) : Bool :=
  let n : I64 := U8.to_i64 b in
  dt_between n 48 57 || dt_between n 65 90 || dt_between n 97 122
    || I64.beq n 95 || I64.beq n 39 || I64.beq n 46

def dt_between (n : I64) (lo : I64) (hi : I64) : Bool :=
  Bool.not (I64.lt n lo) && Bool.not (I64.gt n hi)

/// `bs` with its first `n` bytes dropped.
#[partial]
def dt_drop (bs : List U8) (n : I64) : List U8 :=
  if I64.lt n 1 then bs
  else match bs {
    List.empty => bs,
    List.cons _ rest => dt_drop rest (n - 1),
  }

#[partial]
def dt_take (bs : List U8) (n : I64) (acc : List U8) : List U8 :=
  if I64.lt n 1 then List.reverse acc
  else match bs {
    List.empty => List.reverse acc,
    List.cons b rest => dt_take rest (n - 1) (List.cons b acc),
  }

/// The span and the name range of one declaration: `bytes` starts at the
/// declaration (it may run past it), `start` is its parsed start and `len`
/// its parsed length. With no whole-word `name` in the header -- an unnamed
/// instance's `_`, a `use` -- the name range is the span itself, which an
/// editor's `selectionRange` still accepts.
#[partial]
def decl_text_ranges (bytes : List U8) (start : Location) (len : I64) (name : String)
    : Pair SourceRange SourceRange :=
  let body : List U8 := dt_take bytes len List.empty in
  let kept : I64 := dt_trim_end (List.reverse body) len in
  let span : SourceRange := { start := start, end := dt_advance body kept start, path := Option.none } in
  match dt_name_offset body name kept {
    Option.none => Pair.pair span span,
    Option.some off =>
      let named : SourceRange := {
        start := dt_advance body off start,
        end := dt_advance body (off + String.length name) start,
        path := Option.none,
      } in
      Pair.pair span named,
  }

// --- The end: trailing whitespace and comment lines ---

/// The length left once trailing whitespace and whole `//` lines are gone.
/// `rev` is the body reversed, `n` its length.
#[partial]
def dt_trim_end (rev : List U8) (n : I64) : I64 :=
  match dt_drop_ws_counting rev n {
    Pair.pair bare left =>
      let line : List U8 := dt_take_line bare List.empty in
      let line_len : I64 := List.length line in
      if I64.gt left 0 && dt_is_comment_line line
      then dt_trim_end (dt_drop bare line_len) (left - line_len)
      else left,
  }

#[partial]
def dt_drop_ws_counting (bs : List U8) (n : I64) : Pair (List U8) I64 :=
  match bs {
    List.empty => Pair.pair bs n,
    List.cons b rest => if dt_is_ws b then dt_drop_ws_counting rest (n - 1) else Pair.pair bs n,
  }

#[partial]
def dt_drop_ws (bs : List U8) : List U8 :=
  match bs {
    List.empty => bs,
    List.cons b rest => if dt_is_ws b then dt_drop_ws rest else bs,
  }

/// The reversed bytes up to the first newline, read back into forward order.
#[partial]
def dt_take_line (rev : List U8) (acc : List U8) : List U8 :=
  match rev {
    List.empty => acc,
    List.cons b rest => if U8.beq b dt_nl then acc else dt_take_line rest (List.cons b acc),
  }

#[partial]
def dt_is_comment_line (line : List U8) : Bool :=
  match dt_drop_ws line {
    List.cons a rest => U8.beq a dt_slash && dt_starts_with_slash rest,
    List.empty => false,
  }

def dt_starts_with_slash (bs : List U8) : Bool :=
  match bs {
    List.cons b _ => U8.beq b dt_slash,
    List.empty => false,
  }

// --- The name: past comments and attributes, the first whole word ---

#[partial]
def dt_name_offset (body : List U8) (name : String) (limit : I64) : Option I64 :=
  if String.beq name "_" || String.beq name ""
  then Option.none
  else match dt_header_end body 0 {
    Pair.pair rest i =>
      dt_find_word rest i (String.to_list name) (String.length name) (dt_line_limit rest i limit) false,
  }

/// The header line's end, so a name the header does not spell (a `with`
/// block's prefixed def) is not found at a use in the body.
#[partial]
def dt_line_limit (bs : List U8) (i : I64) (limit : I64) : I64 :=
  match dt_skip_line bs i {
    Pair.pair _ eol => if I64.lt eol limit then eol else limit,
  }

/// Skip leading whitespace, `//` comments and `#[...]` attributes.
#[partial]
def dt_header_end (bs : List U8) (i : I64) : Pair (List U8) I64 :=
  match dt_header_step bs i {
    Option.none => Pair.pair bs i,
    Option.some p => match p { Pair.pair rest j => dt_header_end rest j },
  }

#[partial]
def dt_header_step (bs : List U8) (i : I64) : Option (Pair (List U8) I64) :=
  match bs {
    List.empty => Option.none,
    List.cons b rest =>
      if dt_is_ws b then Option.some (Pair.pair rest (i + 1))
      else if U8.beq b dt_slash && dt_starts_with_slash rest then Option.some (dt_skip_line rest (i + 1))
      else if U8.beq b dt_hash && dt_starts_with rest dt_lbracket then Option.some (dt_skip_attr rest (i + 1) 0 false false)
      else Option.none,
  }

def dt_starts_with (bs : List U8) (c : U8) : Bool :=
  match bs {
    List.cons b _ => U8.beq b c,
    List.empty => false,
  }

/// Up to, not past, the newline: the whitespace step eats it.
#[partial]
def dt_skip_line (bs : List U8) (i : I64) : Pair (List U8) I64 :=
  match bs {
    List.empty => Pair.pair bs i,
    List.cons b rest => if U8.beq b dt_nl then Pair.pair bs i else dt_skip_line rest (i + 1),
  }

/// From the `[` after `#` to just past its matching `]`; brackets inside a
/// string literal (`#[native "x[0]"]`) do not count.
#[partial]
def dt_skip_attr (bs : List U8) (i : I64) (depth : I64) (in_str : Bool) (esc : Bool)
    : Pair (List U8) I64 :=
  match bs {
    List.empty => Pair.pair bs i,
    List.cons b rest =>
      let code : Bool := Bool.not in_str in
      let opens : Bool := code && U8.beq b dt_lbracket in
      let shuts : Bool := code && U8.beq b dt_rbracket in
      if shuts && I64.lt depth 2
      then Pair.pair rest (i + 1)
      else dt_skip_attr rest (i + 1)
        (if opens then depth + 1 else if shuts then depth - 1 else depth)
        (if esc then in_str else if U8.beq b dt_quote then code else in_str)
        (in_str && Bool.not esc && U8.beq b dt_backslash),
  }

/// The offset of the first whole-word `name` at or after `i`, ending within
/// `limit`.
#[partial]
def dt_find_word (bs : List U8) (i : I64) (name : List U8) (nlen : I64) (limit : I64) (prev_name : Bool)
    : Option I64 :=
  if I64.gt (i + nlen) limit then Option.none
  else match bs {
    List.empty => Option.none,
    List.cons b rest =>
      if Bool.not prev_name && dt_word_at bs name
      then Option.some i
      else dt_find_word rest (i + 1) name nlen limit (dt_is_name_byte b),
  }

/// `name` starts `bs` and is not followed by another name byte.
#[partial]
def dt_word_at (bs : List U8) (name : List U8) : Bool :=
  match name {
    List.empty => match bs {
      List.empty => true,
      List.cons b _ => Bool.not (dt_is_name_byte b),
    },
    List.cons n nrest => match bs {
      List.empty => false,
      List.cons b brest => U8.beq b n && dt_word_at brest nrest,
    },
  }

// --- Offsets to positions ---

/// The position `r` bytes into `bs`, which starts at `origin`: a byte
/// offset, a 1-based line and a 1-based CHARACTER column, the parser's own
/// convention (`lang/src/parser/position.mo`), so a UTF-8 continuation byte
/// does not advance the column.
#[partial]
def dt_advance (bs : List U8) (r : I64) (origin : Location) : Location :=
  dt_advance_go bs r origin.offset origin.line origin.column

#[partial]
def dt_advance_go (bs : List U8) (r : I64) (off : I64) (line : I64) (col : I64) : Location :=
  let here : Location := { offset := off, line := line, column := col } in
  if I64.lt r 1 then here
  else match bs {
    List.empty => here,
    List.cons b rest =>
      let nl : Bool := U8.beq b dt_nl in
      let cont : Bool := dt_between (U8.to_i64 b) 128 191 in
      dt_advance_go rest (r - 1) (off + 1) (if nl then line + 1 else line)
        (if nl then 1 else if cont then col else col + 1),
  }
