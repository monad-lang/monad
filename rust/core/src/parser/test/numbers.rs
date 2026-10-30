use super::*;

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
