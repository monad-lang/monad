use super::*;
use crate::term::float_suffix;

#[test]
fn test_hex_literal() {
  let p = |i: Span<'static, ()>| hex_literal::<()>(i);
  let (_, r) = p("0xBADBEEF".into()).unwrap();
  similar!(r, num_suffix(0xBADBEEF, NumSuffix::I64));
  let (_, r) = p("0XCAFE".into()).unwrap(); // uppercase 0X prefix
  similar!(r, num_suffix(0xCAFE, NumSuffix::I64));
  let (_, r) = p("0xFFu32".into()).unwrap();
  similar!(r, num_suffix(0xFF, NumSuffix::U32));
  let (_, r) = p("-0x10".into()).unwrap();
  similar!(r, num_suffix(-0x10, NumSuffix::I64));
  assert!(p("0xZZ".into()).is_err()); // no valid hex digits after prefix
}

#[test]
fn test_hex_literal_in_literal_dispatch() {
  // Proves hex_literal is actually reachable through `literal`, not just
  // callable in isolation (the ordering-before-num_literal requirement).
  let p = |i: Span<'static, ()>| literal::<()>(i);
  let (_, r) = p("0xFF".into()).unwrap();
  similar!(r, num_suffix(0xFF, NumSuffix::I64));
}

#[test]
fn test_hex_literal_range_validation() {
  let p = |i: Span<'static, ()>| hex_literal::<()>(i);
  // Boundary values of each width parse.
  let (_, r) = p("0xFFu8".into()).unwrap();
  similar!(r, num_suffix(255, NumSuffix::U8));
  let (_, r) = p("0x7Fi8".into()).unwrap();
  similar!(r, num_suffix(127, NumSuffix::I8));
  let (_, r) = p("-0x80i8".into()).unwrap();
  similar!(r, num_suffix(-128, NumSuffix::I8));
  // One past each boundary is a parse error, not a silently wrapped
  // payload.
  assert!(p("0x100u8".into()).is_err());
  assert!(p("0x80i8".into()).is_err()); // 128 > i8::MAX
  assert!(p("0x10000u16".into()).is_err());
  // Bare i64: 2^63 rejected, -2^63 accepted.
  assert!(p("0x8000000000000000".into()).is_err());
  let (_, r) = p("-0x8000000000000000".into()).unwrap();
  similar!(r, num_suffix(i64::MIN, NumSuffix::I64));
  // Negative + unsigned suffix.
  assert!(p("-0x1u8".into()).is_err());
  assert!(p("-0xFFu32".into()).is_err());
  // Full-width u64 still bit-reinterprets into the shared i64 payload.
  let (_, r) = p("0xFFFFFFFFFFFFFFFFu64".into()).unwrap();
  similar!(r, num_suffix(-1, NumSuffix::U64));
}

#[test]
fn test_num_literal_range_validation() {
  let p = |i: Span<'static, ()>| num_literal::<()>(i);
  // Boundary values of each width parse.
  let (_, r) = p("100u8".into()).unwrap();
  similar!(r, num_suffix(100, NumSuffix::U8));
  let (_, r) = p("127i8".into()).unwrap();
  similar!(r, num_suffix(127, NumSuffix::I8));
  let (_, r) = p("-128i8".into()).unwrap();
  similar!(r, num_suffix(-128, NumSuffix::I8));
  let (_, r) = p("4294967295u32".into()).unwrap();
  similar!(r, num_suffix(4294967295, NumSuffix::U32));
  // Out-of-range is a parse error, not a masked payload.
  assert!(p("300u8".into()).is_err());
  assert!(p("128i8".into()).is_err());
  assert!(p("-129i8".into()).is_err());
  assert!(p("65536u16".into()).is_err());
  assert!(p("2147483648i32".into()).is_err());
  // Bare overflow past i64::MAX is still an error.
  assert!(p("9223372036854775808".into()).is_err());
  // Decimal u64 above i64::MAX bit-reinterprets into the payload —
  // agreeing with 0xFFFFFFFFFFFFFFFFu64 at last.
  let (_, r) = p("9223372036854775808u64".into()).unwrap();
  similar!(r, num_suffix(i64::MIN, NumSuffix::U64));
  let (_, r) = p("18446744073709551615u64".into()).unwrap();
  similar!(r, num_suffix(-1, NumSuffix::U64));
  assert!(p("18446744073709551616u64".into()).is_err());
}

#[test]
fn test_literal_leading_zeros_are_not_significant() {
  // Pins the parity the self-hosted gate (`numeric_literal.mo`'s
  // significant-digit count) has to match: zero padding never changes
  // the value or trips the range gate.
  let n = |i: Span<'static, ()>| num_literal::<()>(i);
  let (_, r) = n("00000000000000000042".into()).unwrap();
  similar!(r, num_suffix(42, NumSuffix::I64));
  let (_, r) = n("0000000000000000000255u8".into()).unwrap();
  similar!(r, num_suffix(255, NumSuffix::U8));
  assert!(n("0009223372036854775808".into()).is_err());
  let h = |i: Span<'static, ()>| hex_literal::<()>(i);
  let (_, r) = h("0x00000000000000001".into()).unwrap();
  similar!(r, num_suffix(1, NumSuffix::I64));
  let (_, r) = h("0x0000FFFFFFFFFFFFFFFFu64".into()).unwrap();
  similar!(r, num_suffix(-1, NumSuffix::U64));
  assert!(h("0x00001FFFFFFFFFFFFFFFFu64".into()).is_err());
}

#[test]
fn test_num_literal_negative_unsigned_rejected() {
  let p = |i: Span<'static, ()>| num_literal::<()>(i);
  assert!(p("-1u8".into()).is_err());
  assert!(p("-1u64".into()).is_err());
  assert!(p("-0u8".into()).is_err());
  // Signed negatives are unaffected.
  let (_, r) = p("-5i32".into()).unwrap();
  similar!(r, num_suffix(-5, NumSuffix::I32));
}

#[test]
fn test_num_literal_float_suffix_routes_to_float() {
  // Integer digits with a float suffix are a Float literal, not a Num
  // tagged with a float suffix.
  let p = |i: Span<'static, ()>| num_literal::<()>(i);
  let (_, r) = p("33f64".into()).unwrap();
  similar!(r, float_suffix(33.0, NumSuffix::F64));
  let (_, r) = p("33f32".into()).unwrap();
  similar!(r, float_suffix(33.0f64 as f32 as f64, NumSuffix::F32));
  let (_, r) = p("-5f64".into()).unwrap();
  similar!(r, float_suffix(-5.0, NumSuffix::F64));
  // Reachable through `literal` dispatch too.
  let pl = |i: Span<'static, ()>| literal::<()>(i);
  let (_, r) = pl("33f64".into()).unwrap();
  similar!(r, float_suffix(33.0, NumSuffix::F64));
}

#[test]
fn test_float_literal_f32_rounds_payload() {
  let p = |i: Span<'static, ()>| float_literal::<()>(i);
  let (_, r) = p("0.5f32".into()).unwrap();
  similar!(r, float_suffix(0.5f64 as f32 as f64, NumSuffix::F32));
  // 0.1f32 carries the f32-rounded payload, not the f64 one.
  let (_, r) = p("0.1f32".into()).unwrap();
  similar!(r, float_suffix(0.1f64 as f32 as f64, NumSuffix::F32));
  let (_, r) = p("0.1f64".into()).unwrap();
  similar!(r, float_suffix(0.1, NumSuffix::F64));
}
