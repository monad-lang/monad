/// URL percent-encoding for `href` and `src`, following cmark's
/// `escape_href`.
///
/// The safe set is ASCII alphanumerics plus the URL punctuation below; every
/// other ASCII character and EVERY byte of a multi-byte character becomes
/// uppercase `%XX`. `%` itself is preserved so an already-encoded URL is not
/// double-encoded, and `&` is preserved because the attribute serializer
/// turns it into `&amp;`.
use init::string {}
use parsec::core {is_empty}
use lib::scan {Markdown.char_width}

pub def Markdown.href_safe (b : U8) : Bool :=
    if Bool.and (U8.lt 47u8 b) (U8.lt b 58u8) then true
    else if Bool.and (U8.lt 64u8 b) (U8.lt b 91u8) then true
    else if Bool.and (U8.lt 96u8 b) (U8.lt b 123u8) then true
    else if U8.beq b 33u8 then true
    else if U8.beq b 35u8 then true
    else if U8.beq b 36u8 then true
    else if U8.beq b 37u8 then true
    else if U8.beq b 38u8 then true
    else if U8.beq b 40u8 then true
    else if U8.beq b 41u8 then true
    else if U8.beq b 42u8 then true
    else if U8.beq b 43u8 then true
    else if U8.beq b 44u8 then true
    else if U8.beq b 45u8 then true
    else if U8.beq b 46u8 then true
    else if U8.beq b 47u8 then true
    else if U8.beq b 58u8 then true
    else if U8.beq b 59u8 then true
    else if U8.beq b 61u8 then true
    else if U8.beq b 63u8 then true
    else if U8.beq b 64u8 then true
    else if U8.beq b 95u8 then true
    else if U8.beq b 126u8 then true
    else false

/// A nibble (0-15) as its uppercase hex digit, in U32 arithmetic because
/// `init` exposes no U8-to-I64 conversion.
def Markdown.hex_digit (n : U32) : String :=
    if U32.lt n 10u32
    then String.from_list [U32.to_u8 (U32.add 48u32 n)]
    else String.from_list [U32.to_u8 (U32.add 65u32 (U32.sub n 10u32))]

def Markdown.byte_hex (b : U8) : String :=
    let n : U32 := U8.to_u32 b in
    String.concat "%" (String.concat (Markdown.hex_digit (U32.shr n 4u32)) (Markdown.hex_digit (U32.and n 15u32)))

#[partial]
def Markdown.escape_href_go (s : String) (acc : List String) : String :=
    if is_empty s
    then String.concat_list (List.reverse acc)
    else
        match String.get s 0 {
            Option.none => String.concat_list (List.reverse acc),
            Option.some b =>
                let w : I64 := Markdown.char_width s in
                let piece : String := String.slice s 0 w in
                if Bool.and (Markdown.href_safe b) (I64.beq w 1i64)
                then Markdown.escape_href_go (String.drop 1i64 s) (List.cons piece acc)
                else
                    // A multi-byte character is encoded byte by byte, and the
                    // whole character is consumed: dropping one BYTE into a
                    // continuation byte would truncate the string.
                    Markdown.escape_href_go (String.drop w s)
                        (List.cons (Markdown.encode_bytes (String.to_list piece) List.empty) acc)
        }

#[partial]
def Markdown.encode_bytes (bytes : List U8) (acc : List String) : String :=
    match bytes {
        List.empty => String.concat_list (List.reverse acc),
        List.cons b rest => Markdown.encode_bytes rest (List.cons (Markdown.byte_hex b) acc)
    }

pub def Markdown.escape_href (s : String) : String :=
    Markdown.escape_href_go s List.empty
