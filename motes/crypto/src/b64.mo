/// Base64 (RFC 4648 §4) and base64url (§5) codecs, pure Monad.
///
/// `B64` is the standard alphabet (`+`/`/`, `=`-padded); `B64Url` is the
/// URL alphabet (`-`/`_`) and emits no padding. Both decoders accept
/// their own alphabet with or without padding and reject non-canonical
/// trailing bits, so a re-encode of what they return is byte-identical.
///
/// This duplicates `motes/http`'s standard-base64 decoder on purpose:
/// `motes/crypto` is a leaf so every other mote can depend on it without
/// pulling in HTTP.
///
/// `U8` has no shift or bitwise operations, so encoding works in `U32`
/// (`U8.to_u32`/`U32.to_u8`) and decoding uses multiplication/division,
/// the shape `std`'s SHA-256 and `http`'s decoder already use.

// ── byte predicates ─────────────────────────────────────────────────────

def B64.is_upper (b : U8) : Bool :=
  if U8.lt b 65u8 then false
  else U8.lt b 91u8

def B64.is_lower (b : U8) : Bool :=
  if U8.lt b 97u8 then false
  else U8.lt b 123u8

def B64.is_digit (b : U8) : Bool :=
  if U8.lt b 48u8 then false
  else U8.lt b 58u8

// ── alphabet ────────────────────────────────────────────────────────────

/// A 6-bit value as its alphabet character.
def B64.alpha (standard : Bool) (v : U8) : U8 :=
  if U8.lt v 26u8 then U8.add v 65u8
  else if U8.lt v 52u8 then U8.add (U8.sub v 26u8) 97u8
  else if U8.lt v 62u8 then U8.add (U8.sub v 52u8) 48u8
  else if U8.beq v 62u8 then (if standard then 43u8 else 45u8)
  else (if standard then 47u8 else 95u8)

/// The shared `A-Z a-z 0-9` range, the same in both alphabets.
def B64.value_alnum (c : U8) : Option U8 :=
  if B64.is_upper c then Option.some (U8.sub c 65u8)
  else if B64.is_lower c then Option.some (U8.add (U8.sub c 97u8) 26u8)
  else if B64.is_digit c then Option.some (U8.add (U8.sub c 48u8) 52u8)
  else Option.none

/// An alphabet character's 6-bit value; `Option.none` for anything else,
/// `=` included (the decoders treat padding separately).
def B64.value_opt (standard : Bool) (c : U8) : Option U8 :=
  if standard
  then
    if U8.beq c 43u8 then Option.some 62u8
    else if U8.beq c 47u8 then Option.some 63u8
    else B64.value_alnum c
  else
    if U8.beq c 45u8 then Option.some 62u8
    else if U8.beq c 95u8 then Option.some 63u8
    else B64.value_alnum c

// ── encoding ────────────────────────────────────────────────────────────

/// Cons four finished characters onto the REVERSED accumulator, so a run
/// of groups stays linear (`List.append` per group would be quadratic).
def B64.push4 (c1 : U8) (c2 : U8) (c3 : U8) (c4 : U8) (out : List U8) : List U8 :=
  List.cons c4 (List.cons c3 (List.cons c2 (List.cons c1 out)))

/// Six-bit slice `by` bits down from a packed word.
def B64.slice6 (w : U32) (by : U32) : U8 :=
  U32.to_u8 (U32.and (U32.shr w by) 63u32)

def B64.encode_triple (standard : Bool) (b0 : U8) (b1 : U8) (b2 : U8) (out : List U8) : List U8 :=
  let w : U32 :=
    U32.or (U32.or (U32.shl (U8.to_u32 b0) 16u32) (U32.shl (U8.to_u32 b1) 8u32))
      (U8.to_u32 b2)
  in
  B64.push4
    (B64.alpha standard (B64.slice6 w 18u32))
    (B64.alpha standard (B64.slice6 w 12u32))
    (B64.alpha standard (B64.slice6 w 6u32))
    (B64.alpha standard (B64.slice6 w 0u32))
    out

/// One leftover byte: two characters, plus `==` when padded.
def B64.encode_tail1 (standard : Bool) (b0 : U8) (out : List U8) : List U8 :=
  let v1 := B64.alpha standard (U32.to_u8 (U32.shr (U8.to_u32 b0) 2u32)) in
  let v2 := B64.alpha standard (U32.to_u8 (U32.shl (U32.and (U8.to_u32 b0) 3u32) 4u32)) in
  if standard
  then List.cons 61u8 (List.cons 61u8 (List.cons v2 (List.cons v1 out)))
  else List.cons v2 (List.cons v1 out)

/// Two leftover bytes: three characters, plus `=` when padded.
def B64.encode_tail2 (standard : Bool) (b0 : U8) (b1 : U8) (out : List U8) : List U8 :=
  let w : U32 := U32.or (U32.shl (U8.to_u32 b0) 8u32) (U8.to_u32 b1) in
  let v1 := B64.alpha standard (B64.slice6 w 10u32) in
  let v2 := B64.alpha standard (B64.slice6 w 4u32) in
  let v3 := B64.alpha standard (U32.to_u8 (U32.shl (U32.and (U8.to_u32 b1) 15u32) 2u32)) in
  if standard
  then List.cons 61u8 (List.cons v3 (List.cons v2 (List.cons v1 out)))
  else List.cons v3 (List.cons v2 (List.cons v1 out))

def B64.encode_go (standard : Bool) (xs : List U8) (out : List U8) : List U8 :=
  match xs {
    List.empty => List.reverse out,
    List.cons b0 r0 => match r0 {
      List.empty => List.reverse (B64.encode_tail1 standard b0 out),
      List.cons b1 r1 => match r1 {
        List.empty => List.reverse (B64.encode_tail2 standard b0 b1 out),
        List.cons b2 r2 => B64.encode_go standard r2 (B64.encode_triple standard b0 b1 b2 out)
      }
    }
  }

// ── decoding ────────────────────────────────────────────────────────────

def B64.u8_mod (x : U8) (m : U8) : U8 := U8.sub x (U8.mul (U8.div x m) m)

def B64.byte1 (v1 : U8) (v2 : U8) : U8 := U8.add (U8.mul v1 4u8) (U8.div v2 16u8)

def B64.byte2 (v2 : U8) (v3 : U8) : U8 :=
  U8.add (U8.mul (B64.u8_mod v2 16u8) 16u8) (U8.div v3 4u8)

def B64.byte3 (v3 : U8) (v4 : U8) : U8 :=
  U8.add (U8.mul (B64.u8_mod v3 4u8) 64u8) v4

def B64.char_err : Result String (List U8) := Result.err "base64: invalid character"

def B64.pad_err : Result String (List U8) := Result.err "base64: invalid padding"

def B64.after_pad_err : Result String (List U8) :=
  Result.err "base64: data after the padding"

def B64.canonical_err : Result String (List U8) :=
  Result.err "base64: non-canonical padding bits"

def B64.length_err : Result String (List U8) :=
  Result.err "base64: length is not a multiple of 4"

/// A final group of two characters, one byte: the last character's low
/// four bits are unused and must be zero.
def B64.final2 (standard : Bool) (c1 : U8) (c2 : U8) (out : List U8) : Result String (List U8) :=
  if U8.beq c1 61u8 then B64.pad_err
  else if U8.beq c2 61u8 then B64.pad_err
  else match B64.value_opt standard c1 {
    Option.none => B64.char_err,
    Option.some v1 => match B64.value_opt standard c2 {
      Option.none => B64.char_err,
      Option.some v2raw =>
        let v2 : U8 := v2raw in
        if U8.beq (B64.u8_mod v2 16u8) 0u8
        then Result.ok (List.reverse (List.cons (B64.byte1 v1 v2) out))
        else B64.canonical_err
    }
  }

/// A final group of three characters, two bytes: the last character's low
/// two bits are unused and must be zero.
def B64.final3 (standard : Bool) (c1 : U8) (c2 : U8) (c3 : U8) (out : List U8) : Result String (List U8) :=
  if U8.beq c1 61u8 then B64.pad_err
  else if U8.beq c2 61u8 then B64.pad_err
  else if U8.beq c3 61u8 then B64.pad_err
  else match B64.value_opt standard c1 {
    Option.none => B64.char_err,
    Option.some v1 => match B64.value_opt standard c2 {
      Option.none => B64.char_err,
      Option.some v2raw =>
        let v2 : U8 := v2raw in
        match B64.value_opt standard c3 {
          Option.none => B64.char_err,
          Option.some v3raw =>
            let v3 : U8 := v3raw in
            if U8.beq (B64.u8_mod v3 4u8) 0u8
            then Result.ok (List.reverse
              (List.cons (B64.byte2 v2 v3) (List.cons (B64.byte1 v1 v2) out)))
            else B64.canonical_err
        }
    }
  }

/// A group whose fourth character is `=`: one byte (`xx==`) or two
/// (`xxx=`), with the same canonical-bits rule as the unpadded tails.
def B64.padded_one (standard : Bool) (c1 : U8) (c2 : U8) (out : List U8) : Result String (List U8) :=
  B64.final2 standard c1 c2 out

def B64.padded_two (standard : Bool) (c1 : U8) (c2 : U8) (c3 : U8) (out : List U8) : Result String (List U8) :=
  B64.final3 standard c1 c2 c3 out

/// One whole group. `=` may appear only as the third or fourth character
/// of the LAST group; anything after it is an error.
///
/// `#[terminating]`: the walk alternates with `decode_go`, so neither is
/// structurally recursive on its own (the same shape `http`'s decoder
/// carries).
#[terminating]
def B64.group4
  (standard : Bool) (c1 : U8) (c2 : U8) (c3 : U8) (c4 : U8)
  (rest : List U8) (out : List U8) : Result String (List U8) :=
  if U8.beq c4 61u8 then
    match rest {
      List.cons _ _ => B64.after_pad_err,
      List.empty =>
        if U8.beq c3 61u8
        then B64.padded_one standard c1 c2 out
        else B64.padded_two standard c1 c2 c3 out
    }
  else if U8.beq c1 61u8 then B64.pad_err
  else if U8.beq c2 61u8 then B64.pad_err
  else if U8.beq c3 61u8 then B64.pad_err
  else
    match B64.value_opt standard c1 {
      Option.none => B64.char_err,
      Option.some v1 => match B64.value_opt standard c2 {
        Option.none => B64.char_err,
        Option.some v2raw =>
          let v2 : U8 := v2raw in
          match B64.value_opt standard c3 {
            Option.none => B64.char_err,
            Option.some v3raw =>
              let v3 : U8 := v3raw in
              match B64.value_opt standard c4 {
                Option.none => B64.char_err,
                Option.some v4 =>
                  B64.decode_go standard rest
                    (List.cons (B64.byte3 v3 v4)
                      (List.cons (B64.byte2 v2 v3)
                        (List.cons (B64.byte1 v1 v2) out)))
              }
          }
      }
    }

/// `#[terminating]`: a tail shorter than two characters ends the walk, and
/// this and `group4` call each other, so neither is structurally recursive
/// on its own (the same reason `http`'s decoder carries the attribute).
#[terminating]
def B64.decode_go (standard : Bool) (xs : List U8) (out : List U8) : Result String (List U8) :=
  match xs {
    List.empty => Result.ok (List.reverse out),
    List.cons c1 r1 => match r1 {
      List.empty => B64.length_err,
      List.cons c2 r2 => match r2 {
        List.empty => B64.final2 standard c1 c2 out,
        List.cons c3 r3 => match r3 {
          List.empty => B64.final3 standard c1 c2 c3 out,
          List.cons c4 r4 => B64.group4 standard c1 c2 c3 c4 r4 out
        }
      }
    }
  }

def B64.decode_with (standard : Bool) (s : String) : Result String (List U8) :=
  B64.decode_go standard (String.to_list s) List.empty

// ── public surface ──────────────────────────────────────────────────────

/// Standard alphabet, `=`-padded (RFC 4648 §4).
pub def B64.encode_std (bs : List U8) : String :=
  String.from_list (B64.encode_go true bs List.empty)

/// Standard alphabet; accepts padded or unpadded input.
pub def B64.decode_std (s : String) : Result String (List U8) :=
  B64.decode_with true s

/// URL alphabet, unpadded (RFC 4648 §5).
pub def B64Url.encode (bs : List U8) : String :=
  String.from_list (B64.encode_go false bs List.empty)

/// URL alphabet; accepts padded or unpadded input.
pub def B64Url.decode (s : String) : Result String (List U8) :=
  B64.decode_with false s
