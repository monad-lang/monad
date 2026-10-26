/// Text helpers for one-line displays (session names/descriptions and
/// dialog labels): `String.slice` is BYTE-based, so a naive cut can split
/// a multibyte UTF-8 sequence and write invalid bytes to the terminal.
/// Every cut here backs off to a character boundary.
def is_continuation (b : U8) : Bool :=
    Bool.and (U8.lt 0x7Fu8 b) (U8.lt b 0xC0u8)

/// How many bytes the UTF-8 sequence starting with `b` occupies
/// (`b` is a leader byte; a continuation byte never reaches here).
def seq_len (b : U8) : I64 :=
    if U8.lt b 0x80u8 then 1
    else if U8.lt b 0xE0u8 then 2
    else if U8.lt b 0xF0u8 then 3
    else 4

#[partial]
def take_bytes (n : I64) (bs : List U8) (acc : List U8) : List U8 :=
    if n < 1 then acc
    else match bs {
        List.empty => acc,
        List.cons b rest => take_bytes (n - 1) rest (List.cons b acc),
    }

/// The byte index of the last non-continuation byte before `n`, and that
/// byte (`-1`/0 when there is none).
#[partial]
def last_leader_go (bs : List U8) (i : I64) (li : I64) (lb : U8) : Pair I64 U8 :=
    match bs {
        List.empty => Pair.pair li lb,
        List.cons b rest =>
            if is_continuation b
            then last_leader_go rest (i + 1) li lb
            else last_leader_go rest (i + 1) i b,
    }

/// The largest boundary <= `n` of the UTF-8 byte list: `n` itself when
/// the last character is complete, else that character's leader index.
/// A leading byte without its continuations is an incomplete character
/// too, which is why the leader's own length is consulted.
def cut_end (bs : List U8) (n : I64) : I64 :=
    let taken : List U8 := List.reverse (take_bytes n bs List.empty) in
    match last_leader_go taken 0 (0i64 - 1i64) 0u8 {
        Pair.pair li lb =>
            if li < 0 then 0
            else
                let end : I64 := li + seq_len lb in
                if I64.lt n end then li else n,
    }

/// `s` capped to at most `max_bytes` bytes (never splitting a codepoint),
/// with `…` appended when it was cut. Shorter strings are returned as-is.
/// The bytes come from `String.to_list`, not `String.slice`: a slice
/// whose length lands mid-codepoint returns "" (measured), which would
/// leave only the ellipsis.
pub def Text.cut (max_bytes : I64) (s : String) : String :=
    let n : I64 := String.length s in
    if max_bytes < 1 then ""
    else if Bool.not (I64.lt max_bytes n) then s
    else
        let bs : List U8 := String.to_list s in
        let end : I64 := cut_end bs max_bytes in
        let kept : List U8 := List.reverse (take_bytes (if end < 0 then 0 else end) bs List.empty) in
        String.concat (String.from_list kept) "…"

#[partial]
def first_line_go (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => acc,
        List.cons b rest =>
            if Bool.or (U8.beq b 10u8) (U8.beq b 13u8)
            then acc
            else first_line_go rest (List.cons b acc),
    }

/// The text up to the first newline (`\n` or `\r`), byte-exact.
pub def Text.first_line (s : String) : String :=
    String.from_list (List.reverse (first_line_go (String.to_list s) List.empty))
