/// HTTP-date formatting and parsing (RFC 9110 §5.6.7, IMF-fixdate).
///
/// Pure: a `Date` / `Last-Modified` header is bytes, not a clock read. The
/// clock lives in `std::io`; callers pass epoch seconds. Dates before the
/// epoch clamp to 1970-01-01 for formatting (an HTTP date is not signed);
/// parsing rejects them.
///
/// The format is fixed width: `Sun, 06 Nov 1994 08:49:37 GMT`.

use std::list {List.length}

def Http.Date.month_names : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun",
   "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

def Http.Date.weekday_names : List String :=
  ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]

#[terminating]
def Http.Date.nth (n : I64) (xs : List String) (fallback : String) : String :=
  match xs {
    List.empty => fallback,
    List.cons x rest =>
      if I64.lt n 1i64 then x else Http.Date.nth (I64.sub n 1i64) rest fallback
  }

def Http.Date.pad2 (n : I64) : String :=
  if I64.lt n 10i64
  then String.concat "0" (I64.to_string n)
  else I64.to_string n

def Http.Date.pad4 (n : I64) : String :=
  if I64.lt n 10i64
  then String.concat "000" (I64.to_string n)
  else if I64.lt n 100i64
  then String.concat "00" (I64.to_string n)
  else if I64.lt n 1000i64
  then String.concat "0" (I64.to_string n)
  else I64.to_string n

/// `n - (n / d) * d`; `n` is non-negative everywhere this is used.
def Http.Date.mod_n (n : I64) (d : I64) : I64 :=
  I64.sub n (I64.mul (I64.div n d) d)

/// Days-since-epoch to (year, (month, day)), Hinnant's civil-from-days.
/// `z0 >= 0` for every HTTP date this module formats.
def Http.Date.civil_from_days (z0 : I64) : Pair I64 (Pair I64 I64) :=
  let z : I64 := I64.add z0 719468i64 in
  let era : I64 := I64.div z 146097i64 in
  let doe : I64 := I64.sub z (I64.mul era 146097i64) in
  let yoe : I64 := I64.div
    (I64.add (I64.sub doe (I64.div doe 1460i64))
      (I64.sub (I64.div doe 36524i64) (I64.div doe 146096i64)))
    365i64 in
  let y0 : I64 := I64.add yoe (I64.mul era 400i64) in
  let doy : I64 := I64.sub doe
    (I64.sub (I64.add (I64.mul 365i64 yoe) (I64.div yoe 4i64)) (I64.div yoe 100i64)) in
  let mp : I64 := I64.div (I64.add (I64.mul 5i64 doy) 2i64) 153i64 in
  let d : I64 := I64.add (I64.sub doy (I64.div (I64.add (I64.mul 153i64 mp) 2i64) 5i64)) 1i64 in
  let m : I64 := if I64.lt mp 10i64 then I64.add mp 3i64 else I64.sub mp 9i64 in
  let y : I64 := if I64.lt m 3i64 then I64.add y0 1i64 else y0 in
  Pair.pair y (Pair.pair m d)

/// (year, month, day) to days-since-epoch, Hinnant's days-from-civil.
def Http.Date.days_from_civil (y0 : I64) (m : I64) (d : I64) : I64 :=
  let y : I64 := if I64.lt m 3i64 then I64.sub y0 1i64 else y0 in
  let era : I64 := I64.div y 400i64 in
  let yoe : I64 := I64.sub y (I64.mul era 400i64) in
  let mp : I64 := if I64.gt m 2i64 then I64.sub m 3i64 else I64.add m 9i64 in
  let doy : I64 := I64.add (I64.div (I64.add (I64.mul 153i64 mp) 2i64) 5i64) (I64.sub d 1i64) in
  let doe : I64 := I64.add (I64.add (I64.mul yoe 365i64) (I64.div yoe 4i64))
    (I64.sub doy (I64.div yoe 100i64)) in
  I64.sub (I64.add (I64.mul era 146097i64) doe) 719468i64

/// Format epoch seconds as an IMF-fixdate.
pub def Http.Date.imf_fixdate (epoch_seconds : I64) : String :=
  let e : I64 := if I64.lt epoch_seconds 0i64 then 0i64 else epoch_seconds in
  let days : I64 := I64.div e 86400i64 in
  let secs : I64 := Http.Date.mod_n e 86400i64 in
  let hh : I64 := I64.div secs 3600i64 in
  let rest : I64 := I64.sub secs (I64.mul hh 3600i64) in
  let mi : I64 := I64.div rest 60i64 in
  let ss : I64 := I64.sub rest (I64.mul mi 60i64) in
  let wd : I64 := Http.Date.mod_n (I64.add days 4i64) 7i64 in
  match Http.Date.civil_from_days days {
    Pair.pair y md =>
      match md {
        Pair.pair mo d =>
          String.concat_all [
            Http.Date.nth wd Http.Date.weekday_names "Thu", ", ",
            Http.Date.pad2 d, " ",
            Http.Date.nth (I64.sub mo 1i64) Http.Date.month_names "Jan", " ",
            Http.Date.pad4 y, " ",
            Http.Date.pad2 hh, ":", Http.Date.pad2 mi, ":", Http.Date.pad2 ss,
            " GMT"
          ]
      }
  }

// ── parsing ─────────────────────────────────────────────────────────────

#[terminating]
def Http.Date.byte_at (i : I64) (bytes : List U8) : Option U8 :=
  match bytes {
    List.empty => Option.none,
    List.cons b rest =>
      if I64.lt i 1i64 then Option.some b else Http.Date.byte_at (I64.sub i 1i64) rest
  }

def Http.Date.digit (b : U8) : Option I64 :=
  if U8.lt b 48u8
  then Option.none
  else if U8.lt 57u8 b
  then Option.none
  else Option.some (I64.sub (U8.to_i64 b) 48i64)

def Http.Date.at_is (i : I64) (want : U8) (bytes : List U8) : Bool :=
  match Http.Date.byte_at i bytes {
    Option.none => false,
    Option.some b => U8.beq b want
  }

def Http.Date.layout_ok (bytes : List U8) : Bool :=
  I64.beq (List.length bytes) 29i64
    && Http.Date.at_is 3i64 44u8 bytes
    && Http.Date.at_is 4i64 32u8 bytes
    && Http.Date.at_is 7i64 32u8 bytes
    && Http.Date.at_is 11i64 32u8 bytes
    && Http.Date.at_is 16i64 32u8 bytes
    && Http.Date.at_is 19i64 58u8 bytes
    && Http.Date.at_is 22i64 58u8 bytes
    && Http.Date.at_is 25i64 32u8 bytes
    && Http.Date.at_is 26i64 71u8 bytes
    && Http.Date.at_is 27i64 77u8 bytes
    && Http.Date.at_is 28i64 84u8 bytes

def Http.Date.two_digits (i : I64) (bytes : List U8) : Option I64 :=
  match Http.Date.byte_at i bytes {
    Option.none => Option.none,
    Option.some a =>
      match Http.Date.byte_at (I64.add i 1i64) bytes {
        Option.none => Option.none,
        Option.some b =>
          match Http.Date.digit a {
            Option.none => Option.none,
            Option.some da =>
              match Http.Date.digit b {
                Option.none => Option.none,
                Option.some db => Option.some (I64.add (I64.mul da 10i64) db)
              }
          }
      }
  }

def Http.Date.four_digits (i : I64) (bytes : List U8) : Option I64 :=
  match Http.Date.two_digits i bytes {
    Option.none => Option.none,
    Option.some hi =>
      match Http.Date.two_digits (I64.add i 2i64) bytes {
        Option.none => Option.none,
        Option.some lo => Option.some (I64.add (I64.mul hi 100i64) lo)
      }
  }

def Http.Date.month_triple (a b c : U8) : Option I64 :=
  if U8.beq a 74u8 && U8.beq b 97u8 && U8.beq c 110u8 then Option.some 1i64
  else if U8.beq a 70u8 && U8.beq b 101u8 && U8.beq c 98u8 then Option.some 2i64
  else if U8.beq a 77u8 && U8.beq b 97u8 && U8.beq c 114u8 then Option.some 3i64
  else if U8.beq a 65u8 && U8.beq b 112u8 && U8.beq c 114u8 then Option.some 4i64
  else if U8.beq a 77u8 && U8.beq b 97u8 && U8.beq c 121u8 then Option.some 5i64
  else if U8.beq a 74u8 && U8.beq b 117u8 && U8.beq c 110u8 then Option.some 6i64
  else if U8.beq a 74u8 && U8.beq b 117u8 && U8.beq c 108u8 then Option.some 7i64
  else if U8.beq a 65u8 && U8.beq b 117u8 && U8.beq c 103u8 then Option.some 8i64
  else if U8.beq a 83u8 && U8.beq b 101u8 && U8.beq c 112u8 then Option.some 9i64
  else if U8.beq a 79u8 && U8.beq b 99u8 && U8.beq c 116u8 then Option.some 10i64
  else if U8.beq a 78u8 && U8.beq b 111u8 && U8.beq c 118u8 then Option.some 11i64
  else if U8.beq a 68u8 && U8.beq b 101u8 && U8.beq c 99u8 then Option.some 12i64
  else Option.none

def Http.Date.month_at (i : I64) (bytes : List U8) : Option I64 :=
  match Http.Date.byte_at i bytes {
    Option.none => Option.none,
    Option.some a =>
      match Http.Date.byte_at (I64.add i 1i64) bytes {
        Option.none => Option.none,
        Option.some b =>
          match Http.Date.byte_at (I64.add i 2i64) bytes {
            Option.none => Option.none,
            Option.some c => Http.Date.month_triple a b c
          }
      }
  }

def Http.Date.valid_civil (y : I64) (mo : I64) (d : I64) (hh : I64) (mi : I64) (ss : I64) : Bool :=
  I64.gt y 1969i64
    && I64.lt y 10000i64
    && I64.gt mo 0i64
    && I64.lt mo 13i64
    && I64.gt d 0i64
    && I64.lt d 32i64
    && Bool.not (I64.lt hh 0i64)
    && I64.lt hh 24i64
    && Bool.not (I64.lt mi 0i64)
    && I64.lt mi 60i64
    && Bool.not (I64.lt ss 0i64)
    && I64.lt ss 61i64

def Http.Date.epoch_of (y : I64) (mo : I64) (d : I64) (hh : I64) (mi : I64) (ss : I64) : Option I64 :=
  if Bool.not (Http.Date.valid_civil y mo d hh mi ss)
  then Option.none
  else
    let days : I64 := Http.Date.days_from_civil y mo d in
    Option.some (I64.add (I64.mul days 86400i64)
      (I64.add (I64.mul hh 3600i64) (I64.add (I64.mul mi 60i64) ss)))

/// Parse an IMF-fixdate. `none` for any other shape, an invalid month, or
/// an out-of-range field.
pub def Http.Date.parse_imf_fixdate (s : String) : Option I64 :=
  let bytes := String.to_list s in
  if Bool.not (Http.Date.layout_ok bytes)
  then Option.none
  else
    match Http.Date.two_digits 5i64 bytes {
      Option.none => Option.none,
      Option.some d =>
        match Http.Date.month_at 8i64 bytes {
          Option.none => Option.none,
          Option.some mo =>
            match Http.Date.four_digits 12i64 bytes {
              Option.none => Option.none,
              Option.some y =>
                match Http.Date.two_digits 17i64 bytes {
                  Option.none => Option.none,
                  Option.some hh =>
                    match Http.Date.two_digits 20i64 bytes {
                      Option.none => Option.none,
                      Option.some mi =>
                        match Http.Date.two_digits 23i64 bytes {
                          Option.none => Option.none,
                          Option.some ss => Http.Date.epoch_of y mo d hh mi ss
                        }
                    }
                }
            }
        }
    }
