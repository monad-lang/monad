/// The compiled-path mirror of `init/src/number_width_tests.mo`: the
/// width arithmetic every backend must get right, run from a NATIVE
/// binary instead of an interpreter.
///
/// `monad test` evaluates a file through the interpreter
/// (`lang/src/core_eval.mo`'s native table), so it can never catch a
/// backend regression. Build this file and run the binary:
///
///     monad build examples/number_widths.mo -o /tmp/number_widths && /tmp/number_widths
///
/// Every check here is chosen to DISCRIMINATE the width-correct backend
/// from the raw one the tree used to carry: `U8.sub 0u8 1u8` is 255
/// masked and -1 raw, `U16.add 65535u16 1u16` is 0 masked and 65536
/// raw, and so on. The `*_div_zero` checks pin the uniform zero-divisor
/// convention, and the `*_div_min` checks pin the wrapping `MIN / -1`
/// (raw sdiv traps; the runtime's wider-int division folds it back to
/// MIN). The unsigned arithmetic and the i8/i32 comparisons are
/// emitters (`runtime/src/natives.mo`); the signed arithmetic, the
/// i16 comparisons and the whole f32 family are `runtime_core.c`
/// functions (`LLVMType` has no `i16_` and `LLVMValue` no `ashr`), so
/// this binary exercises both mechanisms.
#![mote { name := "number_widths", deps := [init] }]

open IO {println}

def check (name : String) (ok : Bool) : IO Unit :=
    if ok then println ("PASS " ++ name)
    else println ("FAIL " ++ name)

def main : IO Unit := do {
    check "u8_sub_masks" (U8.sub 0u8 1u8 == 255u8);
    check "u8_mul_masks" (U8.mul 16u8 16u8 == 0u8);
    check "u8_add_wraps" (U8.add 255u8 1u8 == 0u8);
    check "u8_div_zero" (U8.div 5u8 0u8 == 0u8);
    check "u16_add_masks" (U16.add 65535u16 1u16 == 0u16);
    check "u16_sub_masks" (U16.sub 0u16 1u16 == 65535u16);
    check "u16_mul_masks" (U16.mul 300u16 300u16 == 24464u16);
    check "u16_div_zero" (U16.div 7u16 0u16 == 0u16);
    check "u32_div_zero" (U32.div 7u32 0u32 == 0u32);
    check "u8_cmp" (U8.lt 255u8 0u8 == false);
    check "u16_cmp" (U16.lt 65535u16 0u16 == false);
    check "i8_add_wraps" (I8.add 100i8 100i8 == -56i8);
    check "i8_sub_wraps" (I8.sub -128i8 1i8 == 127i8);
    check "i8_mul_wraps" (I8.mul 16i8 16i8 == 0i8);
    check "i8_div_zero" (I8.div 5i8 0i8 == 0i8);
    check "i8_div_min" (I8.div -128i8 -1i8 == -128i8);
    check "i8_cmp" (I8.lt 100i8 101i8 && I8.gt 101i8 100i8);
    check "i8_to_string" (I8.to_string -128i8 == "-128");
    check "i16_add_wraps" (I16.add 32767i16 1i16 == -32768i16);
    check "i16_sub_wraps" (I16.sub -32768i16 1i16 == 32767i16);
    check "i16_mul_wraps" (I16.mul 200i16 200i16 == -25536i16);
    check "i16_div_zero" (I16.div 7i16 0i16 == 0i16);
    check "i16_div_min" (I16.div -32768i16 -1i16 == -32768i16);
    check "i16_cmp" (I16.lt -1i16 0i16 && I16.gt 0i16 -1i16);
    check "i16_to_string" (I16.to_string -25536i16 == "-25536");
    check "i32_add_wraps" (I32.add 2147483647i32 1i32 == -2147483648i32);
    check "i32_sub_wraps" (I32.sub -2147483648i32 1i32 == 2147483647i32);
    check "i32_div_zero" (I32.div 7i32 0i32 == 0i32);
    check "i32_div_min" (I32.div -2147483648i32 -1i32 == -2147483648i32);
    check "i32_cmp" (I32.lt 2147483647i32 1i32 == false);
    check "f32_add_rounds" (F32.add 0.1f32 0.2f32 == 0.3f32);
    check "f32_sub_exact" (F32.sub 0.5f32 0.25f32 == 0.25f32);
    check "f32_mul_exact" (F32.mul 0.5f32 0.5f32 == 0.25f32);
    check "f32_div_exact" (F32.div 1.0f32 4.0f32 == 0.25f32);
    check "f32_cmp" (F32.lt 0.5f32 0.75f32 && F32.gt 0.75f32 0.5f32);
    check "f32_to_string" (F32.to_string 0.1f32 == "0.1");
    check "f64_not_f32_rounded" (Bool.not (F64.add 0.1 0.2 == 0.3))
}
