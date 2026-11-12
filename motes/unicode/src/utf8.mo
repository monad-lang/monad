/// UTF-8 encoding and decoding over `String` suffixes.
///
/// `String.get s 0` is the only read: compiled, any other index pays a
/// `strlen` for its bounds check, so these work on the head of a suffix.

/// The width in bytes of the character at the head of `s`, at least 1, so a
/// malformed byte can never stall a scan. An empty string has width 1.
pub def Unicode.char_width (s : String) : I64 :=
    match String.get s 0 {
        Option.some b =>
            if U8.lt b 192u8 then 1
            else if U8.lt b 224u8 then 2
            else if U8.lt b 240u8 then 3
            else 4,
        Option.none => 1,
    }

/// A continuation byte's six payload bits, or 0 when the byte is not one.
def Unicode.cont_bits (head : String) (i : I64) : U32 :=
    match String.get head i {
        Option.some b =>
            if U8.lt b 128u8 then 0u32
            else if U8.lt b 192u8 then U32.sub (U8.to_u32 b) 128u32
            else 0u32,
        Option.none => 0u32
    }

/// Decode the codepoint at the head of `s`. Malformed input yields a
/// best-effort value rather than an error, for consumers that only
/// classify.
pub def Unicode.codepoint_at (s : String) : Option U32 :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b0 =>
            if U8.lt b0 128u8
            then Option.some (U8.to_u32 b0)
            else
                let w : I64 := Unicode.char_width s in
                let head : String := String.slice s 0 w in
                let b : U32 := U8.to_u32 b0 in
                let c1 : U32 := Unicode.cont_bits head 1i64 in
                if I64.beq w 1i64
                then Option.some b
                else if I64.beq w 2i64
                then Option.some (U32.or (U32.shl (U32.and b 31u32) 6u32) c1)
                else if I64.beq w 3i64
                then Option.some
                    (U32.or (U32.or (U32.shl (U32.and b 15u32) 12u32) (U32.shl c1 6u32))
                        (Unicode.cont_bits head 2i64))
                else Option.some
                    (U32.or
                        (U32.or (U32.shl (U32.and b 7u32) 18u32)
                            (U32.or (U32.shl c1 12u32) (U32.shl (Unicode.cont_bits head 2i64) 6u32)))
                        (Unicode.cont_bits head 3i64))
    }

/// The UTF-8 bytes of a codepoint. Surrogate halves, values past U+10FFFF
/// and negatives become U+FFFD (as does 0, which a C string cannot hold).
pub def Unicode.utf8_of_codepoint (cp : I64) : String :=
    let too_high : Bool := I64.gt cp 1114111i64 in
    let surrogate : Bool := Bool.and (Bool.not (I64.lt cp 55296i64)) (Bool.not (I64.gt cp 57343i64)) in
    let c : U32 :=
        if Bool.or (Bool.or (I64.lt cp 1i64) too_high) surrogate
        then 65533u32
        else I64.to_u32 cp in
    let c1 : U32 := U32.or 128u32 (U32.and c 63u32) in
    let c2 : U32 := U32.or 128u32 (U32.and (U32.shr c 6u32) 63u32) in
    let c3 : U32 := U32.or 128u32 (U32.and (U32.shr c 12u32) 63u32) in
    if U32.lt c 128u32
    then String.from_list [U32.to_u8 c]
    else if U32.lt c 2048u32
    then String.from_list [U32.to_u8 (U32.or 192u32 (U32.shr c 6u32)), U32.to_u8 c1]
    else if U32.lt c 65536u32
    then String.from_list
        [U32.to_u8 (U32.or 224u32 (U32.shr c 12u32)),
            U32.to_u8 c2,
            U32.to_u8 c1]
    else String.from_list
        [U32.to_u8 (U32.or 240u32 (U32.shr c 18u32)),
            U32.to_u8 c3,
            U32.to_u8 c2,
            U32.to_u8 c1]
