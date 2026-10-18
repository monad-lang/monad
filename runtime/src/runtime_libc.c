/* Runtime formatting that needs a C library (snprintf/strtod). Included for
   native and wasi only; platform_web.c supplies its own integer itoa. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* `I64.to_string` (init/number.mo) had no backing implementation at
   all -- neither a Monad-level `:=` body nor a runtime primitive.
   Returns a plain malloc'd NUL-terminated buffer, matching this
   runtime's uniform raw-`char*` String convention (see
   monad_build_args's own doc comment: strings are never
   alloc_string's boxed StringObj in practice, every native that
   consumes/produces a String uses a bare char*). */
rt_str monad_i64_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%lld", (long long)n);
    char* out = (char*)RT_PTR(monad_alloc_atomic((rt_size)((size_t)len + 1)));
    if (out) memcpy(out, buf, (size_t)len + 1);
    return RT_STR_WORD(out);
}

/* `#[native string_concat]` (init/string.mo's `String.concat`, also the
   `++`/`Append.append` infix's own real backing for two Strings) --
   previously entirely unwired in codegen: `compile_native_app_db`/
   `compile_native_ir` have no NativeOp entry for it, so every call fell
   through to the generic "native def with no known implementation"
   fallback, which compiles to a meaningless `alloc_constructor(0, 0)` --
   confirmed as a real gap via direct repro (a do-block printing a
   `String.concat` result printed nothing meaningful). Same bare-`char*`
   convention as `monad_i64_to_string` just above (this backend's Strings
   are never `alloc_string`'s boxed `StringObj` in practice). NULL-safe:
   a NULL operand is treated as empty, matching the NULL tolerance of
   the other String natives in this file, since a still-missing/upstream
   String native could plausibly hand this a NULL rather than a real
   empty string. */
/* `#[native i32_to_string]` (init/number.mo). Same shape as
   monad_i64_to_string above -- this backend holds every integer width
   in an i64, so the only real difference is truncating to 32 bits
   first, matching the reference's own I32 formatting. */
rt_str monad_i32_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%d", (int)(int32_t)n);
    char* out = (char*)RT_PTR(monad_alloc_atomic((rt_size)((size_t)len + 1)));
    if (out) memcpy(out, buf, (size_t)len + 1);
    return RT_STR_WORD(out);
}

/* `#[native u8_to_string]`/`#[native u16_to_string]`/`#[native
   u64_to_string]` (init/number.mo). Same shape as
   monad_i64_to_string/monad_i32_to_string above; all three print
   UNSIGNED, which is the whole difference from the signed variants (a
   U64 near the top of its range is a negative i64 in this backend's
   uniform i64 representation, and must still print as the large
   positive number the reference prints). */
rt_str monad_u8_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%u", (unsigned)(uint8_t)n);
    char* out = (char*)RT_PTR(monad_alloc_atomic((rt_size)((size_t)len + 1)));
    if (out) memcpy(out, buf, (size_t)len + 1);
    return RT_STR_WORD(out);
}

rt_str monad_u16_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%u", (unsigned)(uint16_t)n);
    char* out = (char*)RT_PTR(monad_alloc_atomic((rt_size)((size_t)len + 1)));
    if (out) memcpy(out, buf, (size_t)len + 1);
    return RT_STR_WORD(out);
}

rt_str monad_u64_to_string(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%llu", (unsigned long long)n);
    char* out = (char*)RT_PTR(monad_alloc_atomic((rt_size)((size_t)len + 1)));
    if (out) memcpy(out, buf, (size_t)len + 1);
    return RT_STR_WORD(out);
}

/* The decimal -> double conversion. `Literal.flt` carries the literal's
   SOURCE TEXT, not a value (`lang/types.mo`: self-hosted Monad has no
   native bridge to parse a decimal into a float bit pattern), so the
   compiler needs exactly this to lower a float literal -- and it reaches
   it the ordinary way, as a `#[native f64_of_string]` call from
   `lang/codegen/emit.mo`'s `compile_lit_ir`, rather than by growing an
   IEEE-754 decimal parser inside the compiler. `strtod` is the same
   parse the Rust host does with `f64::from_str` for the forms a Monad
   float literal can take (digits with an optional fraction and exponent;
   the lexer produces nothing else). A NULL or unparsable string gives
   0.0 rather than a crash -- a wrong value is a test failure, not a
   segfault in the compiler. */
int64_t monad_f64_of_string(rt_str s) {
    return monad_f64_bits(RT_STR(s) ? strtod(RT_STR(s), NULL) : 0.0);
}

/* Rust's `f64::to_string` -- what `F64.to_string` means on the host --
   prints the SHORTEST decimal that round-trips, in plain positional
   notation, and never in exponent form: "100" for 100.0, "0.1" for 0.1,
   "100000000000000000000" for 1e20, "0.0000001" for 1e-7. `%g` cannot
   do that on its own: at its default precision it prints 3.14's
   neighbours badly, and it switches to exponent form whenever the
   exponent is outside [1, precision) -- "1e+20" where Rust spells the
   number out in full.

   So this finds the digit count the same way the Rust formatter's own
   shortest-round-trip search does -- the first `%.*e` precision that
   `strtod`s back to the identical bits -- and then renders those digits
   positionally around the decimal point `%e` reports. 17 significant
   digits always suffice for a double, so the search is bounded and
   short. Rust's spellings for the non-finite values ("NaN", "inf",
   "-inf") come out of the no-digits exit below. */
rt_str monad_f64_to_string(int64_t v) {
    double d = monad_f64_unbits(v);
    char mant[64];
    int prec = 0;
    for (; prec <= 16; prec++) {
        snprintf(mant, sizeof(mant), "%.*e", prec, d);
        if (strtod(mant, NULL) == d) break;
    }
    if (prec > 16) snprintf(mant, sizeof(mant), "%.16e", d);

    char digits[24];
    int ndig = 0;
    int exp10 = 0;
    int neg = 0;
    const char* p = mant;
    if (*p == '-') { neg = 1; p++; }
    for (; *p && *p != 'e' && *p != 'E'; p++) {
        if (*p >= '0' && *p <= '9') { if (ndig < 23) digits[ndig++] = *p; }
    }
    if (*p == 'e' || *p == 'E') exp10 = (int)strtol(p + 1, NULL, 10);

    char out[400];
    int n = 0;
    /* The sign goes first, for every finite value and for an infinity --
       `-0` and `-inf` are both real Rust spellings. A NaN is the one
       value that prints without one (`d == d` is false exactly there),
       which is why this is a guard rather than a plain `if (neg)`. */
    if (neg && d == d) out[n++] = '-';
    if (ndig == 0) {
        /* No digits at all from `%e`: a NaN or an infinity, the only
           values that produce none. Same spelling as the Rust host's
           Display, which is what the two runners have to agree on. */
        const char* word = (d != d) ? "NaN" : "inf";
        while (*word && n < 399) out[n++] = *word++;
    } else if (exp10 >= 0) {
        int before = exp10 + 1;
        for (int i = 0; i < ndig && n < 399; i++) {
            if (i == before) out[n++] = '.';
            out[n++] = digits[i];
        }
        for (int i = ndig; i < before && n < 399; i++) out[n++] = '0';
    } else {
        out[n++] = '0';
        out[n++] = '.';
        for (int i = 0; i < -exp10 - 1 && n < 399; i++) out[n++] = '0';
        for (int i = 0; i < ndig && n < 399; i++) out[n++] = digits[i];
    }
    out[n] = '\0';

    char* res = (char*)RT_PTR(monad_alloc_atomic((rt_size)((size_t)n + 1)));
    if (res) memcpy(res, out, (size_t)n + 1);
    return RT_STR_WORD(res);
}
