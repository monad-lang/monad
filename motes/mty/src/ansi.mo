// mty / ansi -- byte-level ANSI stripping for assertions.
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
