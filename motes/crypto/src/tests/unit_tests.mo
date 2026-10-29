/// Constant-time equality tests for `motes/crypto` (`Ct.eq`).
///
/// The RFC 4648 and hex vectors moved to `std/src/base64_tests.mo` and
/// `std/src/hex_tests.mo` when the codecs moved to `std`.
///
/// Pure (`Bool`), so both hosts run it.

use crypto::ct {Ct.eq}

def one_zero_byte : List U8 := [0u8]

#[test]
def test_ct_eq : Bool :=
  Ct.eq (String.to_list "abc") (String.to_list "abc")
  && Bool.not (Ct.eq (String.to_list "abc") (String.to_list "abd"))
  && Bool.not (Ct.eq (String.to_list "abc") (String.to_list "zbc"))
  && Bool.not (Ct.eq (String.to_list "abc") (String.to_list "ab"))
  && Bool.not (Ct.eq (String.to_list "abc") (String.to_list "abcd"))
  && Ct.eq List.empty List.empty
  && Bool.not (Ct.eq List.empty one_zero_byte)
