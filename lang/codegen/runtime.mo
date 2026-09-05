/// Monad-generated runtime natives -- the Phase-1 proof of concept for
/// plans/bootstrapping/self-hosted-runtime.md: instead of adding every
/// new native to `lang/codegen/runtime.c` as C, the SIMPLE ones (pure
/// byte-loop String ops, single-`icmp` U8/U64 comparisons, zero-arg
/// stubs) are built here as `LLVMFunction` values straight from the
/// `lang.codegen.ir` ADTs and merged into every compiled module by
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
use lang.codegen.ir {LLVMFunction, LLVMInstruction, LLVMValue, ParamPair}
use std.list {List}

open LLVMType {i1_, i8_, i64_, ptr}
open LLVMValue {
  add, alloc_constructor, call, icmp_eq, icmp_ne, icmp_sgt, icmp_slt,
  int_, inttoptr, load, mul, parm_, phi, sdiv, sub, udiv, urem, var_, zext,
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
/// `Bench.now` is a real C function (`monad_bench_now`, runtime.c) and
/// `Bench.report` is ordinary Monad (`std/bench.mo`), so neither needs a
/// generated stub any more -- the pair used to return 0/1 and print
/// nothing, which silently disabled every `--verbose` timing in a
/// compiled binary.
def runtime_native_functions : List LLVMFunction :=
  List.append string_runtime_functions numeric_runtime_functions

def string_runtime_functions : List LLVMFunction :=
  [emit_string_starts_with, emit_string_to_list, emit_string_get]

def numeric_runtime_functions : List LLVMFunction :=
  [emit_u8_eq, emit_u8_lt, emit_u8_gt, emit_u64_eq,
   emit_u8_sub, emit_u8_mul, emit_u8_div, emit_u64_mod, emit_u64_div]

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

/// `monad_u64_mod(a, b)`: 0 when `b == 0`, else `a % b`. `urem`, not
/// the reference's signed `wrapping_rem` -- for `String.hash`'s
/// full-range u64-as-i64 values this buckets differently than the
/// interpreter would, but bucketing is internal to `HashMap` and only
/// self-consistency matters (`std/map.mo`'s own 0-15 bucket chain is
/// simply never entered with a negative index).
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

// ─── Bench stubs ────────────────────────────────────────────────────

/// `Bench.now`/`Bench.report`'s natives, reachable from every
/// `--verbose` compile. The compiled binary has no measurement clock
/// wired yet, so these are documented zero/true stubs -- the
/// measurement API is never load-bearing for correctness, and a
/// wrong-but-typed `0`/`1` is exactly what keeps the verbose paths
/// from crashing on a Unit stub. Real timing is a later
/// self-hosted-runtime phase.
