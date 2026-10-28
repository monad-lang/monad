/// `application/x-www-form-urlencoded` encoding.
///
/// `http`'s `Uri.format_query` uses `%20` for a space; RFC 6749's token
/// requests are traditionally `+`. This module is the `+` form, with
/// strict RFC 3986 percent-encoding for everything outside the unreserved
/// set — the client-side counterpart to `Body.parse_urlencoded`, which
/// already treats `+` as a space and percent-decodes strictly.
///
/// It lives in `moose` because encoding a request body is an HTTP-client
/// concern; any client that has to build a form body uses it, not only
/// OAuth.

use std::list {List.intercalate}

/// RFC 3986 §2.3: the characters `encode_component` leaves alone.
pub def Form.is_unreserved (b : U8) : Bool :=
  if U8.beq b 45u8 then true
  else if U8.beq b 46u8 then true
  else if U8.beq b 95u8 then true
  else if U8.beq b 126u8 then true
  else if U8.lt b 48u8 then false
  else if U8.lt b 58u8 then true
  else if U8.lt b 65u8 then false
  else if U8.lt b 91u8 then true
  else if U8.lt b 97u8 then false
  else U8.lt b 123u8

def Form.hex_digit (n : U8) : U8 :=
  if U8.lt n 10u8 then U8.add n 48u8 else U8.add n 55u8

#[terminating]
def Form.encode_bytes (bs : List U8) (out : List U8) : List U8 :=
  match bs {
    List.empty => List.reverse out,
    List.cons b rest =>
      if U8.beq b 32u8
      then Form.encode_bytes rest (List.cons 43u8 out)
      else if Form.is_unreserved b
      then Form.encode_bytes rest (List.cons b out)
      else
        let hi := U8.div b 16u8 in
        let lo := U8.sub b (U8.mul hi 16u8) in
        Form.encode_bytes rest
          (List.cons (Form.hex_digit lo)
            (List.cons (Form.hex_digit hi) (List.cons 37u8 out)))
  }

/// One component: space becomes `+`, unreserved bytes pass through, and
/// every other byte becomes uppercase `%XX`.
pub def Form.encode_component (s : String) : String :=
  String.from_list (Form.encode_bytes (String.to_list s) List.empty)

def Form.field (f : Pair String String) : String :=
  match f {
    Pair.pair k v =>
      String.concat (Form.encode_component k)
        (String.concat "=" (Form.encode_component v))
  }

/// `k=v` pairs joined by `&`, in the list's order. An empty list encodes
/// to the empty string.
pub def Form.encode (fields : List (Pair String String)) : String :=
  List.intercalate "&" (List.map Form.field fields)
