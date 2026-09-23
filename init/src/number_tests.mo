/// `U64` end to end: every member of the class, on both backends.
///
/// This file exists because five of the ten `U64` members were declared
/// with a `#[native]` attribute and never wired into the LLVM backend, and
/// nothing in the corpus could see it. `U64.add` and `U64.mul` are used by
/// `init/src/string.mo`'s `hash_bytes_selfhosted`, so the gap was not
/// confined to an exotic corner -- it was reachable from string hashing.
/// The reason it stayed invisible is worth recording: `monad check` cannot
/// detect an unwired native, because the natives are resolved at *codegen*.
/// A file whose call to one is never reached by a test therefore reports
/// `0 error(s)` while being unable to compile. That is exactly the state
/// `bench/src/hashmap_bucket_dispatch.mo` was in, and the only file that
/// did reach one was the single file the sweep's test list excluded.
///
/// Every assertion is a cross-check rather than a restatement: this file
/// runs under the self-hosted runner (compiled code, the generated-IR
/// natives in `runtime/src/natives.mo`) and under `monad-rs test` (the
/// Rust evaluator, `core/src/core_native.rs`), so a passing test is two
/// independent implementations agreeing -- the same hazard `f64_tests.mo`
/// guards for floats.
///
/// The values are chosen to discriminate, not merely to pass:
///
///   * `mul 1000000 1000000 = 10^12` does not fit in 32 bits, so a native
///     that had been wired through the `U32` path (which masks both
///     operands and the result, `emit_masked_binop`) would fail it. This
///     is the case that separates "wired to the right emitter" from
///     "wired".
///   * `add`/`sub` use values correct under either signed or unsigned i64
///     arithmetic, since the reference routes both through `int_binop`
///     and wrapping i64 add/sub are bit-identical either way -- so they
///     pin the WIRING, not the sign rule.
///   * `lt`/`gt` are asserted in both directions, so a swapped `slt`/`sgt`
///     operand order fails instead of passing by symmetry.
///
/// One thing this file deliberately does NOT claim: true unsigned ordering.
/// `u64_lt`/`u64_gt` are in the same generic `int_cmp` group as every
/// other width's comparisons (`core_native.rs:217-222`, `|a, b| a < b` on
/// the i64 payload), so the reference applies no mask and no unsigned
/// reinterpretation, and a value at or above 2^63 therefore compares
/// signed. That is a property of the reference being mirrored, not an
/// oversight in the port -- and it cannot be asserted from here, because
/// no such value is expressible as an i64-carried `U64` literal.
///
/// `beq`, not `eq`: the class member follows the `BEq` naming convention
/// while the native it is wired to is `u64_eq`. The distinction is real
/// enough that the first version of this file guessed `U64.eq` and got a
/// correct `unknown variable 'U64.eq'` back.

#[test]
def test_u64_add : Bool := U64.add 2u64 3u64 == 5u64

#[test]
def test_u64_sub : Bool := U64.sub 5u64 3u64 == 2u64

#[test]
def test_u64_mul_overflows_32_bits : Bool := U64.mul 1000000u64 1000000u64 == 1000000000000u64

#[test]
def test_u64_xor : Bool := U64.xor 12u64 10u64 == 6u64

#[test]
def test_u64_lt : Bool := U64.lt 1u64 2u64

#[test]
def test_u64_lt_is_false_the_other_way : Bool := Bool.not (U64.lt 2u64 1u64)

#[test]
def test_u64_gt : Bool := U64.gt 3u64 2u64

#[test]
def test_u64_gt_is_false_the_other_way : Bool := Bool.not (U64.gt 2u64 3u64)

#[test]
def test_u64_div_and_mod : Bool :=
    U64.div 17u64 5u64 == 3u64 && U64.mod 17u64 5u64 == 2u64

#[test]
def test_u64_beq : Bool := U64.beq 4u64 4u64 && Bool.not (U64.beq 4u64 5u64)

#[test]
def test_u64_to_string : Bool := U64.to_string 42u64 == "42"

/// The shape `bench/src/hashmap_bucket_dispatch.mo` was blocked on: the
/// `U64.mod (U64.add idx 1u64) 256u64` ring step, asserted at the wrap
/// boundary and one past it -- the two places an off-by-one or a
/// truncation would show.
#[test]
def test_u64_ring_step : Bool :=
    U64.mod (U64.add 255u64 1u64) 256u64 == 0u64
    && U64.mod (U64.add 256u64 1u64) 256u64 == 1u64
