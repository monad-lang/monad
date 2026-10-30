/// Byte splitting, local to this mote.
///
/// `std` has no `String.split`, and `http::strings.Strings.split_on` would
/// pull `http` into a parser that must stay usable in a CLI or a test with
/// no transport at all. Segment sizes here are tiny, so the two reverses
/// per field are irrelevant.

/// Split on every occurrence of `sep`. Empty segments are preserved;
/// callers that want them gone use `List.filter`.
pub def Split.on_byte (sep : U8) (s : String) : List String :=
  Split.on_byte_go sep (String.to_list s) List.empty List.empty

#[terminating]
def Split.on_byte_go
  (sep : U8) (rest : List U8) (cur : List U8) (out : List String)
  : List String :=
  match rest {
    List.empty =>
      List.reverse (List.cons (String.from_list (List.reverse cur)) out),
    List.cons b more =>
      if U8.beq b sep
      then Split.on_byte_go sep more List.empty
             (List.cons (String.from_list (List.reverse cur)) out)
      else Split.on_byte_go sep more (List.cons b cur) out
  }
