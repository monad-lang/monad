/// Text -> numbers, in pure Monad: strict, whole-string, no trimming.
///
/// `Option`, not `Result`, because these classify a TOKEN rather than parse
/// a document -- a YAML plain scalar that is not a number stays a string,
/// which is exactly the `none` branch.
///
/// PORTABLE BY CONSTRUCTION: no native is used, and in particular this does
/// NOT call `F64.bits_of_string` (its `f64_of_string` native is web-gated,
/// `lang/src/codegen/natives.mo`'s `web_only_natives`), so it works on every
/// target including wasm. The value is built from F64 literals, a digit
/// table and repeated multiplication/division.
///
/// WHY THE ODD SPELLING OF ADDITION: `infix (+)` resolves to `I64.add`
/// (`init/src/lib.mo`), and `F64.add` is package-private to `init`, so
/// `a + b` on two F64 values does not check. Addition is spelled
/// `a - (0.0f64 - b)`; `*`, `-` and `/` dispatch through the pub
/// `HMul`/`Sub`/`Div` instances and are what this module uses.
///
/// PRECISION: correctly rounded while the mantissa has at most 19
/// significant digits and the decimal exponent is within +/-22 (each power
/// of ten is then exact and the single final scale is one IEEE operation).
/// Beyond that the result carries a bounded relative error (~1e-15), which
/// is what config data needs. Exact `strtod` parity is deliberately not
/// claimed.
use init::string {}
use init::number {}

// ─── Byte helpers ───

/// The decimal value of an ASCII digit byte, or `none`.
def Parse.digit_value (b : U8) : Option I64 :=
    if U8.beq b 48u8 then Option.some 0i64
    else if U8.beq b 49u8 then Option.some 1i64
    else if U8.beq b 50u8 then Option.some 2i64
    else if U8.beq b 51u8 then Option.some 3i64
    else if U8.beq b 52u8 then Option.some 4i64
    else if U8.beq b 53u8 then Option.some 5i64
    else if U8.beq b 54u8 then Option.some 6i64
    else if U8.beq b 55u8 then Option.some 7i64
    else if U8.beq b 56u8 then Option.some 8i64
    else if U8.beq b 57u8 then Option.some 9i64
    else Option.none

/// One digit as an F64. There is no `Int -> F64` conversion in the
/// language, so this table is the bridge the mantissa accumulator uses.
def Parse.digit_float (n : I64) : F64 :=
    if I64.beq n 0i64 then 0.0f64
    else if I64.beq n 1i64 then 1.0f64
    else if I64.beq n 2i64 then 2.0f64
    else if I64.beq n 3i64 then 3.0f64
    else if I64.beq n 4i64 then 4.0f64
    else if I64.beq n 5i64 then 5.0f64
    else if I64.beq n 6i64 then 6.0f64
    else if I64.beq n 7i64 then 7.0f64
    else if I64.beq n 8i64 then 8.0f64
    else 9.0f64

/// `a + b` for F64, spelled through subtraction -- see the module doc.
def Parse.f64_plus (a : F64) (b : F64) : F64 :=
    a - (0.0f64 - b)

// ─── Integers ───

/// Would `acc * 10 + d` overflow I64? Checked before the multiply, because
/// I64 arithmetic wraps silently.
def Parse.i64_overflows (acc : I64) (d : I64) : Bool :=
    I64.gt acc (I64.div (I64.sub 9223372036854775807i64 d) 10i64)

/// Magnitude accumulator. `seen` is what rejects an empty digit run (a bare
/// `+`, `-` or empty string); a non-digit ends the run with `none`, because
/// these parsers require the WHOLE string to be a number.
#[partial]
def Parse.i64_go (bs : List U8) (acc : I64) (seen : Bool) : Option I64 :=
    match bs {
        List.empty => if seen then Option.some acc else Option.none,
        List.cons b rest =>
            match Parse.digit_value b {
                Option.none => Option.none,
                Option.some d =>
                    if Parse.i64_overflows acc d
                    then Option.none
                    else Parse.i64_go rest (I64.add (I64.mul acc 10i64) d) true,
            },
    }

/// Parse a strict decimal integer: optional `+`/`-`, one or more digits,
/// nothing else. Overflow is `none`. `0x`/`0o`/`0b` are not accepted (they
/// are not in the YAML 1.2 core schema, and a caller that wants them can
/// add a case).
#[partial]
pub def Parse.i64 (s : String) : Option I64 :=
    match String.to_list s {
        List.empty => Option.none,
        List.cons b rest =>
            if U8.beq b 45u8
            then Parse.i64_magnitude rest true
            else if U8.beq b 43u8
            then Parse.i64_magnitude rest false
            else Parse.i64_magnitude (List.cons b rest) false,
    }

#[partial]
def Parse.i64_magnitude (bs : List U8) (neg : Bool) : Option I64 :=
    match Parse.i64_go bs 0i64 false {
        Option.none => Option.none,
        Option.some n => Option.some (if neg then I64.neg n else n),
    }

// ─── Floats ───

/// The scanner's whole state. `phase` is 0 for the integer part, 1 for the
/// fraction and 2 for the exponent.
struct Parse.Decimal {
    mant : F64,
    sig : I64,
    frac : I64,
    phase : I64,
    exp_neg : Bool,
    exp_signed : Bool,
    exp_digits : Bool,
    expv : I64,
}

def Parse.decimal_init : Parse.Decimal :=
    let d : Parse.Decimal := {
        mant := 0.0f64,
        sig := 0i64,
        frac := 0i64,
        phase := 0i64,
        exp_neg := false,
        exp_signed := false,
        exp_digits := false,
        expv := 0i64,
    } in d

/// Accumulate one byte. Returns `none` for any byte the grammar forbids.
def Parse.decimal_step (d : Parse.Decimal) (b : U8) : Option Parse.Decimal :=
    match Parse.digit_value b {
        Option.some n =>
            if I64.beq d.phase 2i64
            then
                let raw : I64 := I64.add (I64.mul d.expv 10i64) n in
                let capped : I64 := if I64.gt raw 1000i64 then 1000i64 else raw in
                let d2 : Parse.Decimal := { d with expv := capped, exp_digits := true } in
                Option.some d2
            else
                let mant2 : F64 := Parse.f64_plus (d.mant * 10.0f64) (Parse.digit_float n) in
                let d2 : Parse.Decimal :=
                    if I64.beq d.phase 1i64
                    then { d with mant := mant2, sig := I64.add d.sig 1i64, frac := I64.add d.frac 1i64 }
                    else { d with mant := mant2, sig := I64.add d.sig 1i64 } in
                Option.some d2,
        Option.none =>
            if U8.beq b 46u8
            then
                if I64.beq d.phase 0i64
                then let d2 : Parse.Decimal := { d with phase := 1i64 } in Option.some d2
                else Option.none
            else if Bool.or (U8.beq b 101u8) (U8.beq b 69u8)
            then
                if Bool.and (I64.gt d.sig 0i64) (Bool.or (I64.beq d.phase 0i64) (I64.beq d.phase 1i64))
                then let d2 : Parse.Decimal := { d with phase := 2i64 } in Option.some d2
                else Option.none
            else if Bool.or (U8.beq b 43u8) (U8.beq b 45u8)
            then
                if Bool.and (I64.beq d.phase 2i64) (Bool.not (Bool.or d.exp_signed d.exp_digits))
                then
                    let d2 : Parse.Decimal :=
                        { d with exp_neg := U8.beq b 45u8, exp_signed := true } in
                    Option.some d2
                else Option.none
            else Option.none,
    }

#[partial]
def Parse.decimal_fold (bs : List U8) (d : Parse.Decimal) : Option Parse.Decimal :=
    match bs {
        List.empty => Option.some d,
        List.cons b rest =>
            match Parse.decimal_step d b {
                Option.none => Option.none,
                Option.some d2 => Parse.decimal_fold rest d2,
            },
    }

/// `10^n` for `0 <= n <= 22`, where every such power is EXACTLY
/// representable as a double (5^22 < 2^53). Multiplying or dividing by one
/// of these is a single correctly-rounded operation -- which is what keeps
/// `3.14` from becoming `3.1400000000000001` through two roundings. (Dividing
/// 314 by 10 and then by 10 is NOT the same as dividing once by 100.)
#[partial]
def Parse.pow10_go (n : I64) (acc : F64) : F64 :=
    if I64.gt n 0i64
    then Parse.pow10_go (I64.sub n 1i64) (acc * 10.0f64)
    else acc

def Parse.pow10_exact (n : I64) : F64 :=
    Parse.pow10_go n 1.0f64

/// Multiply/divide `v` by ten `n` times. Within |n| <= 22 this is one exact
/// power and one IEEE operation (correctly rounded); beyond it, exact 1e22
/// chunks keep the error to a handful of roundings rather than `n` of them.
#[partial]
def Parse.scale10 (v : F64) (n : I64) : F64 :=
    if I64.gt n 22i64
    then Parse.scale10 (v * Parse.pow10_exact 22i64) (I64.sub n 22i64)
    else if I64.lt n (I64.neg 22i64)
    then Parse.scale10 (v / Parse.pow10_exact 22i64) (I64.add n 22i64)
    else if I64.gt n 0i64
    then v * Parse.pow10_exact n
    else if I64.lt n 0i64
    then v / Parse.pow10_exact (I64.neg n)
    else v

def Parse.decimal_finish (d : Parse.Decimal) (neg : Bool) : Option F64 :=
    if I64.gt d.sig 0i64
    then
        if Bool.and (I64.beq d.phase 2i64) (Bool.not d.exp_digits)
        then Option.none
        else
            let e : I64 := if d.exp_neg then I64.neg d.expv else d.expv in
            let n : I64 := I64.sub e d.frac in
            let v : F64 := Parse.scale10 d.mant n in
            Option.some (if neg then 0.0f64 - v else v)
    else Option.none

#[partial]
def Parse.f64_scan (bs : List U8) (neg : Bool) : Option F64 :=
    match Parse.decimal_fold bs Parse.decimal_init {
        Option.none => Option.none,
        Option.some d => Parse.decimal_finish d neg,
    }

/// Parse a strict decimal float: optional sign, an integer part, an
/// optional `.` + fraction (either part may be empty, but not both), and an
/// optional `[eE]` + optional sign + digits. The whole string must be
/// consumed. Non-finite spellings (`.inf`, `.nan`) are NOT accepted here;
/// they are a YAML scalar-resolution concern, not a number grammar one.
#[partial]
pub def Parse.f64 (s : String) : Option F64 :=
    match String.to_list s {
        List.empty => Option.none,
        List.cons b rest =>
            if U8.beq b 45u8
            then Parse.f64_scan rest true
            else if U8.beq b 43u8
            then Parse.f64_scan rest false
            else Parse.f64_scan (List.cons b rest) false,
    }
