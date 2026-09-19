/// Monad-generated runtime natives -- the Phase-1 proof of concept for
/// plans/bootstrapping/self-hosted-runtime.md: instead of adding every
/// new native to `runtime/src/runtime.c` as C, the SIMPLE ones (pure
/// byte-loop String ops, single-`icmp` U8/U64 comparisons, zero-arg
/// stubs) are built here as `LLVMFunction` values straight from the
/// `llvm.ir` ADTs and merged into every compiled module by
/// `compile_db_module_with_debug` (`lang.codegen.emit`).
///
/// Integration is uniform with the C runtime: a native's
/// `native_runtime_fn_name` entry (`lang.codegen.emit`) just names a
/// symbol, and `compile_native_def_wrapper_ir` emits a wrapper def
/// calling `@<symbol>` -- whether that symbol is a C function in
/// runtime.c or one of THESE generated functions makes no difference
/// to the wrapper. Generated functions must NOT also appear in
/// `runtime_declarations` (a `declare` + `define` of the same name is
/// an invalid redefinition), and they must not be `ghc_cc` -- they are
/// ordinary ccc functions called from cc-9 wrapper bodies with plain
/// `call` instructions.
///
/// Representation facts (audit, confirmed against runtime.c):
/// - String values are raw `char*` held in an i64 (literals are plain
///   LLVM global constants, NOT boxed `StringObj`; runtime.c:539-543
///   documents this) -- so byte access is `add` for the address,
///   `inttoptr` to `i8*`, then the new typed `load i8`.
/// - Builtin constructor tags are the fixed convention below (must
///   match `builtin_ctor_tags` in `lang.codegen.emit` -- the single
///   source of truth; duplicated here rather than imported because
///   emit.mo imports THIS module, so the dependency can't be cyclic).
///   `alloc_constructor`/`monad_set_field` are callable symbols, so
///   generated IR marshals `List`/`Option` exactly like user code.
/// - All monad numbers are unboxed i64s, and the reference U8/U64 ops
///   apply NO width mask (core_native.rs's own doc comment notes this
///   known gap), so plain i64 arithmetic IS the matching semantics.
/// - `monad_string_length` (C, already declared in
///   `runtime_declarations`) is the NUL-terminated strlen.
use llvm::ir {LLVMFunction, LLVMInstruction, LLVMValue, ParamPair}
use std::list {List}

open LLVMType {i1_, i8_, i64_, ptr}
open LLVMValue {
  add, alloc_constructor, and_, call, icmp_eq, icmp_ne, icmp_sgt, icmp_slt,
  int_, inttoptr, load, lshr_, mul, or_, parm_, phi, sdiv, shl_, sub, udiv,
  urem, var_, xor_, zext,
}
open LLVMInstruction {assign, branch, jump, ret}

// ─── Fixed builtin constructor tags ─────────────────────────────────
// Mirror of `builtin_ctor_tags` (lang.codegen/emit.mo) + runtime.c's
// own doc comments -- the fixed prelude-constructor tag convention
// every compiled binary and the C runtime agree on. Named constants,
// not magic numbers, per self-hosted-runtime.md's Phase-8 note; keep in
// sync with emit.mo (imported there, so this copy cannot share the
// source of truth directly without a dependency cycle).

def rt_tag_none : I64 := 3
def rt_tag_some : I64 := 4
def rt_tag_list_empty : I64 := 5
def rt_tag_list_cons : I64 := 6

// ─── Emitted-function registry ──────────────────────────────────────

/// Every generated runtime native, merged into each compiled module's
/// function list by `compile_db_module_with_debug`. Currently always
/// emitted (an unreferenced internal define is dead code `llc` drops
/// happily); trimming to the referenced set is a later
/// self-hosted-runtime phase, not a PoC concern.
/// `IO.current_time` and `IO.current_time_nano` are real C functions
/// (`monad_current_time`/`monad_current_time_nano`, runtime.c) and
/// `Bench.report` is ordinary Monad (`std/bench.mo`), so neither needs a
/// generated stub any more -- the pair used to return 0/1 and print
/// nothing, which silently disabled every `--verbose` timing in a
/// compiled binary.
pub def runtime_native_functions : List LLVMFunction :=
  List.append string_runtime_functions numeric_runtime_functions

def string_runtime_functions : List LLVMFunction :=
  [emit_string_starts_with, emit_string_to_list, emit_string_get,
   emit_string_get_char]

def numeric_runtime_functions : List LLVMFunction :=
  [emit_u8_eq, emit_u8_lt, emit_u8_gt, emit_u64_eq,
   emit_u8_sub, emit_u8_mul, emit_u8_div, emit_u64_mod, emit_u64_div,
   emit_u8_add, emit_u8_to_u32, emit_i64_to_u32, emit_u32_to_u8,
   emit_u32_add, emit_u32_sub, emit_u32_and, emit_u32_or, emit_u32_xor,
   emit_u32_shl, emit_u32_shr, emit_u32_eq,
   emit_i64_to_u64, emit_u8_to_u64,
   emit_u16_eq, emit_u16_lt, emit_u16_gt,
   emit_i8_eq, emit_i8_lt, emit_i8_gt,
   emit_i64_add, emit_i64_sub, emit_i64_mul, emit_i64_div,
   emit_i64_eq, emit_i64_lt, emit_i64_gt]

// ─── Shared emitter helpers ─────────────────────────────────────────

/// The param list `(i64 %p0, i64 %p1, ...)`, matching how
/// `compile_native_def_wrapper_ir` passes `parm_ 0 .. N` -- the
/// generated function's own `%pN` names must line up with the
/// `parm_ N` values the wrapper's call arguments render as.
#[partial]
def i64_params (n : I64) : List ParamPair :=
  if n < 1 then []
  else List.cons (ParamPair.mk "p0" i64_) (i64_params_rest 1 n)

#[partial]
def i64_params_rest (i : I64) (n : I64) : List ParamPair :=
  if i < n then List.cons (ParamPair.mk ("p" ++ I64.to_string i) i64_) (i64_params_rest (i + 1) n)
  else []

/// Instructions to load the byte at `base + idx` as an i64 (0-255):
/// `%addr = add`, `%q = inttoptr ... to i8*`, `%b8 = load i8, i8* %q`,
/// `%b = zext i8 ... to i64` -- raw `char*` String representation, no
/// header offsets. The four SSA names must be fresh within the
/// enclosing function; zext exists because `icmp`'s `show_arith`
/// renders i64-typed operands only.
#[partial]
def load_byte_instrs (base : LLVMValue) (idx : LLVMValue) (addr_n : String) (q_n : String) (b8_n : String) (b_n : String) : List LLVMInstruction :=
  [assign addr_n (add base idx),
   assign q_n (inttoptr (var_ addr_n) i64_ (ptr i8_)),
   assign b8_n (load i8_ (ptr i8_) (var_ q_n)),
   assign b_n (zext (var_ b8_n) i8_ i64_)]

/// `@monad_set_field(obj, idx, val)` as an assign -- assigned to a
/// throwaway temp because every instruction in this IR assigns, and
/// the C function's real void return is masked by calling it as an
/// i64, the same `build_set_field_instrs` convention (llc tolerates
/// the ret-type mismatch).
#[partial]
def set_field_call (obj : LLVMValue) (idx : I64) (val : LLVMValue) (temp_n : String) : LLVMInstruction :=
  assign temp_n
    (call "monad_set_field" i64_
      [obj, int_ idx, val] false)

// ─── String natives ─────────────────────────────────────────────────

/// `monad_string_starts_with(prefix, s) -> raw 0/1` (wired
/// `bool_result`): `s.starts_with(prefix)` byte loop. Reading `s[i]`
/// for `i == length(s)` yields the NUL terminator, which no prefix
/// byte can equal (prefix bytes below its own length are all
/// non-NUL), so a too-long prefix falls out through the byte
/// comparison, not a bounds check -- matching Rust's
/// `s.starts_with(prefix)` exactly.
def emit_string_starts_with : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "plen" (call "monad_string_length" i64_ [parm_ 0] false),
       jump "loop"] in
  let loop :=
    LLVMBasicBlock.mk "loop"
      [assign "i" (phi [PhiPair.mk (int_ 0) "entry", PhiPair.mk (var_ "i_next") "next"]),
       assign "cont" (icmp_slt (var_ "i") (var_ "plen")),
       branch (var_ "cont") "body" "done"] in
  let body :=
    LLVMBasicBlock.mk "body"
      (List.append (load_byte_instrs (parm_ 1) (var_ "i") "addr_s" "qs" "s_b8" "sb")
        (List.append (load_byte_instrs (parm_ 0) (var_ "i") "addr_p" "qp" "p_b8" "pb")
          [assign "neq" (icmp_ne (var_ "pb") (var_ "sb")),
           branch (var_ "neq") "fail" "next"])) in
  let next :=
    LLVMBasicBlock.mk "next"
      [assign "i_next" (add (var_ "i") (int_ 1)), jump "loop"] in
  let done := LLVMBasicBlock.mk "done" [ret (int_ 1)] in
  let fail := LLVMBasicBlock.mk "fail" [ret (int_ 0)] in
  { name := "monad_string_starts_with",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry, loop, body, next, done, fail],
    ghc_cc := false,
    dbg_loc := Option.none }

/// `monad_string_to_list(s) -> List U8` (wired `passthrough`): walk the
/// bytes right-to-left PREPENDING each `cons` -- the same shape as the
/// reference's own `for byte in s.as_bytes().iter().rev()` loop
/// (core_native.rs), which leaves the list in original left-to-right
/// order. Two loop-carried phis (index, accumulator); the empty
/// string takes `icmp sgt i, -1` false on the very first iteration
/// (`start = -1`) and returns the `List.empty` (tag 5) seed directly.
/// `i >= 0` is spelled `i > -1` because the IR has `icmp_sgt`/`slt`
/// but no `sge`/`sle` variants.
def emit_string_to_list : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "len" (call "monad_string_length" i64_ [parm_ 0] false),
       assign "start" (sub (var_ "len") (int_ 1)),
       assign "empty_con" (alloc_constructor rt_tag_list_empty []),
       jump "loop"] in
  let loop :=
    LLVMBasicBlock.mk "loop"
      [assign "i" (phi [PhiPair.mk (var_ "start") "entry", PhiPair.mk (var_ "i_next") "body"]),
       assign "acc" (phi [PhiPair.mk (var_ "empty_con") "entry", PhiPair.mk (var_ "con") "body"]),
       assign "cont" (icmp_sgt (var_ "i") (int_ (0 - 1))),
       branch (var_ "cont") "body" "done"] in
  let body :=
    LLVMBasicBlock.mk "body"
      (List.append (load_byte_instrs (parm_ 0) (var_ "i") "addr_b" "qb" "byte8" "byte")
        [assign "con" (alloc_constructor rt_tag_list_cons [var_ "byte", var_ "acc"]),
         set_field_call (var_ "con") 0 (var_ "byte") "sf0",
         set_field_call (var_ "con") 1 (var_ "acc") "sf1",
         assign "i_next" (sub (var_ "i") (int_ 1)),
         jump "loop"]) in
  let done := LLVMBasicBlock.mk "done" [ret (var_ "acc")] in
  { name := "monad_string_to_list",
    params := (i64_params 1),
    ret_ty := i64_,
    blocks := [entry, loop, body, done],
    ghc_cc := false,
    dbg_loc := Option.none }

/// `monad_string_get(s, i) -> Option U8` (wired `passthrough`):
/// `none` (tag 3) for `i < 0 || i >= length(s)`, else `some` (tag 4)
/// wrapping the byte. The general path calls `monad_string_length` (a
/// full `strlen`) for the bounds check -- but `i == 0`, overwhelmingly
/// the parser's case (`is_empty`, `utf8_char_width`, every scanner's
/// first-byte peek), is in range exactly when `s[0]` isn't the NUL
/// terminator, so a fast path skips the `strlen` and reads one byte.
/// Without it a per-char scan loop paid a whole-remaining-input
/// `strlen` per step -- an O(n^2) pure-CPU cost on top of any scan.
/// The fast path still checks `s == NULL` itself (the general path's
/// `monad_string_length` was what made NULL safe; the byte load must
/// not dereference it). The `i < len` test is spelled with SWAPPED
/// branch targets, since the IR has no `icmp_sge`.
def emit_string_get : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "neg" (icmp_slt (parm_ 1) (int_ 0)),
       branch (var_ "neg") "none_block" "zero_check"] in
  let zero_check :=
    LLVMBasicBlock.mk "zero_check"
      [assign "is_zero" (icmp_eq (parm_ 1) (int_ 0)),
       branch (var_ "is_zero") "null_check" "len_check"] in
  let null_check :=
    LLVMBasicBlock.mk "null_check"
      [assign "is_null" (icmp_eq (parm_ 0) (int_ 0)),
       branch (var_ "is_null") "none_block" "first_byte_check"] in
  let first_byte_check :=
    LLVMBasicBlock.mk "first_byte_check"
      (List.append (load_byte_instrs (parm_ 0) (int_ 0) "addr_f" "qf" "fbyte8" "fbyte")
        [assign "is_nul" (icmp_eq (var_ "fbyte") (int_ 0)),
         branch (var_ "is_nul") "none_block" "some_block"]) in
  let len_check :=
    LLVMBasicBlock.mk "len_check"
      [assign "len" (call "monad_string_length" i64_ [parm_ 0] false),
       assign "in_range" (icmp_slt (parm_ 1) (var_ "len")),
       branch (var_ "in_range") "some_block" "none_block"] in
  let none_block :=
    LLVMBasicBlock.mk "none_block"
      [assign "none_con" (alloc_constructor rt_tag_none []),
       ret (var_ "none_con")] in
  let some_block :=
    LLVMBasicBlock.mk "some_block"
      (List.append (load_byte_instrs (parm_ 0) (parm_ 1) "addr_g" "qg" "gbyte8" "gbyte")
        [assign "some_con" (alloc_constructor rt_tag_some [var_ "gbyte"]),
         set_field_call (var_ "some_con") 0 (var_ "gbyte") "gsf",
         ret (var_ "some_con")]) in
  { name := "monad_string_get",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry, zero_check, null_check, first_byte_check, len_check, none_block, some_block],
    ghc_cc := false,
    dbg_loc := Option.none }

// ─── U8/U64 arithmetic + comparison natives ─────────────────────────

/// `monad_u8_eq(a, b) -> raw 0/1` (wired `bool_result`): plain `icmp
/// eq` -- U8 values are unboxed i64s and the reference compares them
/// with NO width mask (core_native.rs's own doc comment), so i64
/// equality IS the semantics. `zext` widens the i1 for the wrapper's
/// `2 - raw` Bool boxing.
def emit_u8_eq : LLVMFunction := emit_icmp_native "monad_u8_eq" (icmp_eq (parm_ 0) (parm_ 1))

/// `monad_u8_lt(a, b) -> raw 0/1` (wired `bool_result`). Signed `slt`
/// matches the reference's Rust `a < b` on i64; byte values (0-255)
/// make unsigned comparison equivalent anyway.
def emit_u8_lt : LLVMFunction := emit_icmp_native "monad_u8_lt" (icmp_slt (parm_ 0) (parm_ 1))

def emit_u8_gt : LLVMFunction := emit_icmp_native "monad_u8_gt" (icmp_sgt (parm_ 0) (parm_ 1))

def emit_u64_eq : LLVMFunction := emit_icmp_native "monad_u64_eq" (icmp_eq (parm_ 0) (parm_ 1))

#[partial]
def emit_icmp_native (name : String) (cmp : LLVMValue) : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "raw" cmp,
       assign "wide" (zext (var_ "raw") i1_ i64_),
       ret (var_ "wide")] in
  { name := name,
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

/// `monad_u8_sub(a, b)` (wired `passthrough`): plain wrapping i64 sub
/// -- the reference's `wrapping_sub`, with no width mask.
def emit_u8_sub : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "r" (sub (parm_ 0) (parm_ 1)), ret (var_ "r")] in
  { name := "monad_u8_sub",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

def emit_u8_mul : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "r" (mul (parm_ 0) (parm_ 1)), ret (var_ "r")] in
  { name := "monad_u8_mul",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

/// `monad_u8_div(a, b)`: 0 when `b == 0`, else `a / b` -- matching the
/// reference's `if b == 0 { 0 } else { a.wrapping_div(b) }` guard.
/// `sdiv`, not `udiv`: the reference's `wrapping_div` is SIGNED
/// (core_native.rs:174-175), and these values are i64-carried u8s --
/// identical to `udiv` for in-range operands, but the mirror-the-
/// reference rule that `emit_u8_lt`/`emit_u8_gt`'s signed `slt`/`sgt`
/// already follow says match it exactly.
def emit_u8_div : LLVMFunction := emit_guarded_native "monad_u8_div" (sdiv (parm_ 0) (parm_ 1))

/// `monad_u64_mod(a, b)`: 0 when `b == 0`, else `a % b`. `urem`, which is
/// what an unsigned mod should be, and since 2026-09-12 the reference
/// interpreter agrees (`core/src/core_native.rs`'s `u64_mod` used the
/// signed `wrapping_rem`; it now uses `uint_binop`).
///
/// This comment used to record the divergence and dismiss it: bucketing is
/// internal to `HashMap`, only self-consistency matters, and "`std/map.mo`'s
/// own 0-15 bucket chain is simply never entered with a negative index."
/// The last clause is true and was the trap. The chain is not ENTERED with a
/// negative index -- it FALLS THROUGH it, into the final `else` slot. So on
/// the interpreter, every key whose `String.hash` had bit 63 set (djb2
/// wraps, so about half of them) shared one bucket: 1612 of the compiler's
/// own 3068 symbol names, against a worst bucket of 23 once the mod is
/// unsigned. It cost 45443ms of a 266178ms self-compile in one validator.
/// The compiled binary was always fine; only the interpreter paid, which is
/// the runtime CI's self-compile actually uses.
def emit_u64_mod : LLVMFunction := emit_guarded_native "monad_u64_mod" (urem (parm_ 0) (parm_ 1))

/// `#[native u64_div]` (init/number.mo's `U64.div`). Guarded like
/// `u64_mod`: a zero divisor yields 0 rather than trapping.
///
/// Newly REACHABLE as of `std/map.mo`'s 256-bucket table, whose
/// `get_bucket` splits a flat index with `U64.div idx 16u64`. Before
/// that nothing in the compiled closure divided a `U64`, so this was
/// missing -- and `validate_no_unwired_natives` caught it as a build
/// failure rather than letting it compile to a "return Unit" stub that
/// would have silently produced garbage bucket indices.
def emit_u64_div : LLVMFunction := emit_guarded_native "monad_u64_div" (udiv (parm_ 0) (parm_ 1))

#[partial]
def emit_guarded_native (name : String) (op : LLVMValue) : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "zero_b" (icmp_eq (parm_ 1) (int_ 0)),
       branch (var_ "zero_b") "zero" "calc"] in
  let zero := LLVMBasicBlock.mk "zero" [ret (int_ 0)] in
  let calc := LLVMBasicBlock.mk "calc" [assign "r" op, ret (var_ "r")] in
  { name := name,
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry, zero, calc],
    ghc_cc := false,
    dbg_loc := Option.none }

// ─── Fixed-width unsigned integer natives (u8 / u32) ────────────────
//
// SHA-256 (std/src/sha256.mo) is written against `U32`, so every one of
// these has to exist before it can be compiled at all -- that single
// dependency is why they land together.
//
// **Every operation masks to its width, on the inputs AND the result.**
// That is what `mask_to_suffix` (core/src/core_native.rs) does for the
// Rust host -- `v as u32 as i64` -- and the two runtimes must agree
// bit-for-bit or sha256 produces a plausible-looking wrong digest
// rather than failing loudly. `emit_u8_sub` above predates this rule
// and is deliberately unmasked (its own comment says so); do not copy
// that shape here.
//
// Values are boxed as i64 throughout, so a "u32" is an i64 whose top 32
// bits are zero. `lshr`, never `ashr`: these are unsigned.

/// `0xFFFFFFFF` -- the u32 width mask.
def u32_mask : LLVMValue := int_ 4294967295

/// `0xFF` -- the u8 width mask.
def u8_mask : LLVMValue := int_ 255

/// A two-argument native that masks both operands to `mask`, applies
/// `op` to the masked temporaries `%a`/`%b`, then masks the result.
/// `op` is built from `var_ "a"`/`var_ "b"` by the caller.
def emit_masked_binop (name : String) (mask : LLVMValue) (op : LLVMValue) : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "a" (and_ (parm_ 0) mask),
       assign "b" (and_ (parm_ 1) mask),
       assign "r" op,
       assign "m" (and_ (var_ "r") mask),
       ret (var_ "m")] in
  { name := name,
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

/// A one-argument width conversion: mask the operand and return it.
/// Covers every `uN_to_uM`/`i64_to_uN` in the set, since the boxed
/// representation is i64 either way and the conversion IS the mask.
def emit_mask_convert (name : String) (mask : LLVMValue) : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "m" (and_ (parm_ 0) mask), ret (var_ "m")] in
  { name := name,
    params := (i64_params 1),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

def emit_u8_add : LLVMFunction :=
  emit_masked_binop "monad_u8_add" u8_mask (add (var_ "a") (var_ "b"))

def emit_u32_add : LLVMFunction :=
  emit_masked_binop "monad_u32_add" u32_mask (add (var_ "a") (var_ "b"))

def emit_u32_sub : LLVMFunction :=
  emit_masked_binop "monad_u32_sub" u32_mask (sub (var_ "a") (var_ "b"))

def emit_u32_and : LLVMFunction :=
  emit_masked_binop "monad_u32_and" u32_mask (and_ (var_ "a") (var_ "b"))

def emit_u32_or : LLVMFunction :=
  emit_masked_binop "monad_u32_or" u32_mask (or_ (var_ "a") (var_ "b"))

def emit_u32_xor : LLVMFunction :=
  emit_masked_binop "monad_u32_xor" u32_mask (xor_ (var_ "a") (var_ "b"))

/// Shifts mask the RESULT, which is what makes an overshift wrap the way
/// the reference does rather than leaving high bits set.
def emit_u32_shl : LLVMFunction :=
  emit_masked_binop "monad_u32_shl" u32_mask (shl_ (var_ "a") (var_ "b"))

def emit_u32_shr : LLVMFunction :=
  emit_masked_binop "monad_u32_shr" u32_mask (lshr_ (var_ "a") (var_ "b"))

/// `monad_u32_eq(a, b) -> raw 0/1` (wired `bool_result`), comparing the
/// MASKED operands -- `icmp eq` on unmasked i64s would call `0x1_0000_0000`
/// and `0` different when both are zero as u32.
def emit_u32_eq : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "a" (and_ (parm_ 0) u32_mask),
       assign "b" (and_ (parm_ 1) u32_mask),
       assign "c" (icmp_eq (var_ "a") (var_ "b")),
       assign "r" (zext (var_ "c") i1_ i64_),
       ret (var_ "r")] in
  { name := "monad_u32_eq",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

/// `monad_string_get_char(s, i) -> Option Char` (wired `passthrough`):
/// `none` for `i < 0` or an out-of-range index, else `some` wrapping the
/// character's LEAD BYTE.
///
/// Indexed by CHARACTER, not byte -- that is the whole difference from
/// `monad_string_get` above, and why it needs a scan rather than a
/// pointer offset. A UTF-8 continuation byte matches `b & 0xC0 == 0x80`,
/// so the character at index `i` starts at the `i`-th byte that is NOT a
/// continuation byte.
///
/// The payload is the lead byte rather than a decoded code point,
/// deliberately: `Char` has no operations and no `BEq` instance anywhere
/// in the language (`init/src/string.mo` says so at the declaration), so
/// nothing can observe the difference -- every caller only asks whether
/// the index was in range. Decoding the full scalar value would be dead
/// work today. Revisit if `Char` ever grows operations.
def emit_string_get_char : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "neg" (icmp_slt (parm_ 1) (int_ 0)),
       branch (var_ "neg") "none_block" "null_check"] in
  let null_check :=
    LLVMBasicBlock.mk "null_check"
      [assign "is_null" (icmp_eq (parm_ 0) (int_ 0)),
       branch (var_ "is_null") "none_block" "loop"] in
  // `bi` = byte cursor, `ci` = how many character starts seen so far.
  let loop_ :=
    LLVMBasicBlock.mk "loop"
      [assign "bi" (phi [PhiPair.mk (int_ 0) "null_check", PhiPair.mk (var_ "bi_next") "advance"]),
       assign "ci" (phi [PhiPair.mk (int_ 0) "null_check", PhiPair.mk (var_ "ci_next") "advance"]),
       jump "read"] in
  let read :=
    LLVMBasicBlock.mk "read"
      (List.append (load_byte_instrs (parm_ 0) (var_ "bi") "addr_c" "qc" "cbyte8" "cbyte")
        [assign "at_end" (icmp_eq (var_ "cbyte") (int_ 0)),
         branch (var_ "at_end") "none_block" "classify"]) in
  // A continuation byte is `0b10xxxxxx`: (b & 0xC0) == 0x80.
  let classify :=
    LLVMBasicBlock.mk "classify"
      [assign "masked" (and_ (var_ "cbyte") (int_ 192)),
       assign "is_cont" (icmp_eq (var_ "masked") (int_ 128)),
       branch (var_ "is_cont") "advance" "at_char_start"] in
  let at_char_start :=
    LLVMBasicBlock.mk "at_char_start"
      [assign "found" (icmp_eq (var_ "ci") (parm_ 1)),
       branch (var_ "found") "some_block" "advance"] in
  let advance :=
    LLVMBasicBlock.mk "advance"
      [assign "bi_next" (add (var_ "bi") (int_ 1)),
       // `masked` (set in `classify`, which dominates every path here)
       // is `0x80` exactly on continuation bytes; a non-continuation
       // byte starts a character, so bump the character counter.
       assign "starts" (icmp_ne (var_ "masked") (int_ 128)),
       assign "starts_i" (zext (var_ "starts") i1_ i64_),
       assign "ci_next" (add (var_ "ci") (var_ "starts_i")),
       jump "loop"] in
  let none_block :=
    LLVMBasicBlock.mk "none_block"
      [assign "none_con" (alloc_constructor rt_tag_none []),
       ret (var_ "none_con")] in
  let some_block :=
    LLVMBasicBlock.mk "some_block"
      [assign "some_con" (alloc_constructor rt_tag_some [var_ "cbyte"]),
       set_field_call (var_ "some_con") 0 (var_ "cbyte") "csf",
       ret (var_ "some_con")] in
  { name := "monad_string_get_char",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry, null_check, loop_, read, classify, at_char_start, advance, none_block, some_block],
    ghc_cc := false,
    dbg_loc := Option.none }

def emit_u8_to_u32 : LLVMFunction := emit_mask_convert "monad_u8_to_u32" u8_mask
def emit_i64_to_u32 : LLVMFunction := emit_mask_convert "monad_i64_to_u32" u32_mask
def emit_u32_to_u8 : LLVMFunction := emit_mask_convert "monad_u32_to_u8" u8_mask

/// A one-argument conversion that changes nothing: return the operand.
/// The reference sends BOTH `i64_to_u64` and `u8_to_u64` through
/// `int_to_int(args, NumSuffix::U64)`, and that helper's mask is
/// `v as u64 as i64` -- a no-op on the uniform i64 payload this backend
/// carries end to end. So unlike `emit_mask_convert`, there is no mask
/// to apply, and `u8_to_u64` must NOT narrow first either: `U8` values
/// are unmasked i64s here too (the reference's own documented known
/// gap, `core_native.rs`'s `int_cmp` group).
def emit_identity_native (name : String) : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry" [ret (parm_ 0)] in
  { name := name,
    params := (i64_params 1),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

def emit_i64_to_u64 : LLVMFunction := emit_identity_native "monad_i64_to_u64"
def emit_u8_to_u64 : LLVMFunction := emit_identity_native "monad_u8_to_u64"

/// The `I64` arithmetic/comparison family -- the LAST set of natives with
/// no runtime backing, and the only one whose absence was a live
/// miscompile rather than a latent one.
///
/// `I64.add/sub/mul/div/beq/lt/gt` are all in `native_op_table`, so their
/// DIRECT call sites inline and never touch a global -- which is how they
/// survived every prior wiring pass (`init/number.mo`'s
/// `instance Add I64 { def add (a b : I64) : I64 := I64.add a b }` is
/// always a direct call, so all ordinary arithmetic worked). A
/// VALUE-position reference (`apply2 I64.beq a b`, `native_i64_bool_binop
/// I64.beq args`) reads the def's own compiled body instead, which was the
/// generic hole-bodied "return Unit" stub.
///
/// What that produced was not a clean crash: the stub returns a 0-arity
/// constructor, and `apply_closure2` on it yields that constructor back,
/// so a caller that only ever consumed the result as a `Bool`
/// (`if f x y then ... else ...`) saw a tag that never equals
/// `Bool.true`'s -- every such comparison answered FALSE, for equal
/// operands and unequal ones alike. That is exactly how it surfaced:
/// `lang/src/core_eval.mo`'s `basic_native_table` passes `I64.beq`/`I64.lt`
/// as first-class arguments, so the self-hosted meta-evaluator judged
/// `0 == 0` false, and every `#[derive]`d `BEq`/`BOrd` instance body took
/// its "different constructor" arm. Same shape in the Rust host, which
/// interprets this very file.
///
/// `sdiv` for div, 0 on a zero divisor, wrapping add/sub/mul, and
/// `icmp`+`zext` (raw 0/1, `bool_result`-wrapped at the def) for the
/// comparisons -- each matching the reference's `core_native.rs` group
/// for `i64_*` exactly, which is the same rule the u8/u16/i8 groups here
/// already follow.
def emit_i64_add : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "r" (add (parm_ 0) (parm_ 1)), ret (var_ "r")] in
  { name := "monad_i64_add",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

def emit_i64_sub : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "r" (sub (parm_ 0) (parm_ 1)), ret (var_ "r")] in
  { name := "monad_i64_sub",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

def emit_i64_mul : LLVMFunction :=
  let entry :=
    LLVMBasicBlock.mk "entry"
      [assign "r" (mul (parm_ 0) (parm_ 1)), ret (var_ "r")] in
  { name := "monad_i64_mul",
    params := (i64_params 2),
    ret_ty := i64_,
    blocks := [entry],
    ghc_cc := false,
    dbg_loc := Option.none }

def emit_i64_div : LLVMFunction := emit_guarded_native "monad_i64_div" (sdiv (parm_ 0) (parm_ 1))

def emit_i64_eq : LLVMFunction := emit_icmp_native "monad_i64_eq" (icmp_eq (parm_ 0) (parm_ 1))
def emit_i64_lt : LLVMFunction := emit_icmp_native "monad_i64_lt" (icmp_slt (parm_ 0) (parm_ 1))
def emit_i64_gt : LLVMFunction := emit_icmp_native "monad_i64_gt" (icmp_sgt (parm_ 0) (parm_ 1))

/// The `U16`/`I8` comparison families, wired as plain unmasked i64
/// comparisons for the same reason `emit_u8_eq`/`_lt`/`_gt` are: the
/// reference routes all three widths through the SAME generic
/// `int_cmp` group (`a == b` / `a < b` / `a > b` on the raw payload),
/// with no width mask. `U32` is the only width that masks, and it has
/// its own masked emitters.
def emit_u16_eq : LLVMFunction := emit_icmp_native "monad_u16_eq" (icmp_eq (parm_ 0) (parm_ 1))
def emit_u16_lt : LLVMFunction := emit_icmp_native "monad_u16_lt" (icmp_slt (parm_ 0) (parm_ 1))
def emit_u16_gt : LLVMFunction := emit_icmp_native "monad_u16_gt" (icmp_sgt (parm_ 0) (parm_ 1))
def emit_i8_eq : LLVMFunction := emit_icmp_native "monad_i8_eq" (icmp_eq (parm_ 0) (parm_ 1))
def emit_i8_lt : LLVMFunction := emit_icmp_native "monad_i8_lt" (icmp_slt (parm_ 0) (parm_ 1))
def emit_i8_gt : LLVMFunction := emit_icmp_native "monad_i8_gt" (icmp_sgt (parm_ 0) (parm_ 1))


// ─── Bench stubs ────────────────────────────────────────────────────

/// `Bench.now`/`Bench.report`'s natives, reachable from every
/// `--verbose` compile. The compiled binary has no measurement clock
/// wired yet, so these are documented zero/true stubs -- the
/// measurement API is never load-bearing for correctness, and a
/// wrong-but-typed `0`/`1` is exactly what keeps the verbose paths
/// from crashing on a Unit stub. Real timing is a later
/// self-hosted-runtime phase.
