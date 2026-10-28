/// Hex codecs: lowercase output, case-insensitive input.
///
/// `std`'s SHA-256 keeps its byte→hex helper private, so the general form
/// lives here.

def Hex.char_of_nibble (n : U8) : U8 :=
  if U8.lt n 10u8 then U8.add n 48u8 else U8.add n 87u8

def Hex.nibble_of_char (c : U8) : Option U8 :=
  if U8.lt c 48u8 then Option.none
  else if U8.lt c 58u8 then Option.some (U8.sub c 48u8)
  else if U8.lt c 65u8 then Option.none
  else if U8.lt c 71u8 then Option.some (U8.sub c 55u8)
  else if U8.lt c 97u8 then Option.none
  else if U8.lt c 103u8 then Option.some (U8.sub c 87u8)
  else Option.none

#[terminating]
def Hex.encode_go (bs : List U8) (out : List U8) : List U8 :=
  match bs {
    List.empty => List.reverse out,
    List.cons b rest =>
      let hi := U8.div b 16u8 in
      let lo := U8.sub b (U8.mul hi 16u8) in
      Hex.encode_go rest
        (List.cons (Hex.char_of_nibble lo) (List.cons (Hex.char_of_nibble hi) out))
  }

pub def Hex.encode (bs : List U8) : String :=
  String.from_list (Hex.encode_go bs List.empty)

#[terminating]
def Hex.decode_go (xs : List U8) (out : List U8) : Result String (List U8) :=
  match xs {
    List.empty => Result.ok (List.reverse out),
    List.cons c1 r1 => match r1 {
      List.empty => Result.err "hex: odd length",
      List.cons c2 r2 => match Hex.nibble_of_char c1 {
        Option.none => Result.err "hex: invalid character",
        Option.some h1 => match Hex.nibble_of_char c2 {
          Option.none => Result.err "hex: invalid character",
          Option.some h2 =>
            Hex.decode_go r2 (List.cons (U8.add (U8.mul h1 16u8) h2) out)
        }
      }
    }
  }

pub def Hex.decode (s : String) : Result String (List U8) :=
  Hex.decode_go (String.to_list s) List.empty
