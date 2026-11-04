// pty / ansi -- byte-level ANSI stripping for assertions.
//
// The Python drivers strip `ESC [ ... final` before matching because a
// rendered phrase is never contiguous in the raw stream (cell deltas
// interleave cursor/SGR codes). This module does the same over BYTES, so a
// multi-byte glyph is never split: only escape sequences are dropped.
//
// OSC is dropped too (the app emits OSC 52 clipboard sequences). A caller
// that wants to assert on an OSC payload searches the RAW output instead
// (`String.contains`), so stripping it here is safe.

def is_csi_final (b : U8) : Bool :=
    Bool.and (Bool.not (U8.lt b 64u8)) (Bool.not (U8.gt b 126u8))

#[partial]
def strip_go (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => List.reverse acc,
        List.cons b rest =>
            if U8.beq b 27u8 then strip_esc rest acc
            else strip_go rest (List.cons b acc)
    }

#[partial]
def strip_esc (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => List.reverse acc,
        List.cons b rest =>
            if U8.beq b 91u8 then strip_csi rest acc
            else if U8.beq b 93u8 then strip_osc rest acc
            else strip_go rest acc
    }

#[partial]
def strip_csi (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => List.reverse acc,
        List.cons b rest =>
            if is_csi_final b then strip_go rest acc else strip_csi rest acc
    }

#[partial]
def strip_osc (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => List.reverse acc,
        List.cons b rest =>
            if U8.beq b 7u8 then strip_go rest acc
            else if U8.beq b 27u8 then strip_st rest acc
            else strip_osc rest acc
    }

#[partial]
def strip_st (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => List.reverse acc,
        List.cons b rest =>
            if U8.beq b 92u8 then strip_go rest acc
            else strip_osc (List.cons b rest) acc
    }

/// Drop CSI and OSC sequences; everything else (including UTF-8 bytes) passes
/// through unchanged.
pub def Ansi.strip (s : String) : String :=
    String.from_list (strip_go (String.to_list s) List.empty)

def is_space (b : U8) : Bool :=
    U8.beq b 32u8 || U8.beq b 9u8 || U8.beq b 10u8 || U8.beq b 13u8

#[partial]
def tight_go (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => List.reverse acc,
        List.cons b rest =>
            if is_space b then tight_go rest acc else tight_go rest (List.cons b acc)
    }

/// `Ansi.strip` with ASCII whitespace removed -- the Python drivers'
/// `striptight`, used for phrase matching that ignores the interleaved cell
/// deltas.
pub def Ansi.tight (s : String) : String :=
    String.from_list (tight_go (String.to_list (Ansi.strip s)) List.empty)

// ── Colours ──────────────────────────────────────────────────────────────
//
// The Python `--no-color` driver searched SGR codes for a foreground or
// background palette index. Same domain here: 30-37, 40-47, 90-97, 100-107.
// One deliberate limitation: extended colours (`38;5;n`, `38;2;r;g;b`) are
// NOT palette parameters, so a stream carrying only those reports false. The
// app's theme emits basic codes only, and the Python regex's substring match
// on those forms was accidental.

def is_digit_b (b : U8) : Bool :=
    Bool.and (Bool.not (U8.lt b 48u8)) (Bool.not (U8.gt b 57u8))

def in_range (lo : I64) (hi : I64) (v : I64) : Bool :=
    Bool.and (Bool.not (I64.lt v lo)) (Bool.not (I64.gt v hi))

def color_param (v : I64) : Bool :=
    in_range 30 37 v || in_range 40 47 v || in_range 90 97 v || in_range 100 107 v

#[partial]
def sgr_scan (bs : List U8) (param : I64) (in_num : Bool) : Bool :=
    match bs {
        List.empty => false,
        List.cons b rest =>
            if U8.beq b 59u8 then
                (if in_num then color_param param else false) || sgr_scan rest 0 false
            else if U8.beq b 109u8 then
                (if in_num then color_param param else color_param 0)
            else if is_digit_b b then
                sgr_scan rest (param * 10 + (U8.to_i64 b - 48)) true
            else
                false
    }

#[partial]
def has_color_esc (bs : List U8) : Bool :=
    match bs {
        List.empty => false,
        List.cons b rest =>
            if U8.beq b 91u8 then
                (if sgr_scan rest 0 false then true else has_color_go rest)
            else has_color_go rest
    }

#[partial]
def has_color_go (bs : List U8) : Bool :=
    match bs {
        List.empty => false,
        List.cons b rest =>
            if U8.beq b 27u8 then has_color_esc rest else has_color_go rest
    }

/// Whether a CSI SGR sequence carries a basic foreground/background colour.
pub def Ansi.has_color (s : String) : Bool :=
    has_color_go (String.to_list s)
