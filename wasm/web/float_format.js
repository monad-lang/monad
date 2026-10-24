// The float spelling `F64.to_string` promises, shared by every
// hand-written loader of the web profile.
//
// The native and wasi runtimes format with `runtime_libc.c`'s
// snprintf/strtod search: the SHORTEST decimal that round-trips, always in
// positional notation (never `1e+21`), with Rust's `f64::to_string`
// spellings for the non-finite values. The freestanding web profile has no
// libc, so the host supplies the digits. `String(d)` is ECMAScript's
// shortest round-trip representation -- the same contract -- and this
// module only rewrites its exponent form into the positional one.

const EXPONENT = /[eE]/;

// Digits and decimal point of an exponent-form number, spelled the way
// Rust spells it: positional, with leading `0.` or trailing zeros as
// needed. `s` has no sign.
function positional(s) {
  let exp = 0;
  const e = s.search(EXPONENT);
  if (e >= 0) {
    exp = parseInt(s.slice(e + 1), 10);
    s = s.slice(0, e);
  }
  const dot = s.indexOf('.');
  const intPart = dot >= 0 ? s.slice(0, dot) : s;
  const fracPart = dot >= 0 ? s.slice(dot + 1) : '';
  const digits = intPart + fracPart;
  const point = intPart.length + exp;
  if (point <= 0) return '0.' + '0'.repeat(-point) + digits;
  if (point >= digits.length) return digits + '0'.repeat(point - digits.length);
  return digits.slice(0, point) + '.' + digits.slice(point);
}

export function f64ToRustString(d) {
  if (Number.isNaN(d)) return 'NaN';
  if (d === Infinity) return 'inf';
  if (d === -Infinity) return '-inf';
  if (Object.is(d, -0)) return '-0';
  const s = String(d);
  if (s[0] === '-') return '-' + positional(s.slice(1));
  return positional(s);
}
