/// Native operations: the table of what compiles to an inline LLVM
/// instruction, and the wiring for the ones backed by a C runtime
/// function.
///
/// `native_op_table` is keyed on what the SOURCE wrote (`I64.add`), but
/// every name reaching codegen now carries its module
/// (`init.number::I64.add`), so `lookup_native_any` strips the
/// qualifier first -- exact, not a guess, because `::` cannot appear in
/// either half of a qualified name.
///
/// `runtime_declarations` lives here too: it is the `declare` list for
/// exactly the C functions these tables dispatch to.
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use lang::types {AttrArg, Attribute, id, id_eq}
use llvm::ir {LLVMDeclaration, NativeOp}
use llvm::target {TargetKind}
use lang::codegen::symbols {
  extract_base_name, replace_dots_with_underscores, symbol_identifier,
  unqualify_def_name,
}
use lib::codegen::util {}
use std::map {HashMap}

#[partial]
def lookup_native (name : String) : Option NativeOp := str_map_lookup name native_op_table

/// `"I64_eq"` (no such identifier exists -- `I64.eq` doesn't typecheck,
/// "unknown variable") is deliberately NOT one of this table's keys: the
/// real, only I64 equality function throughout the whole corpus is
/// `I64.beq` (`init/number.mo`, the `BEq I64` instance's own method),
/// which mangles to `I64_beq`, never matching a hypothetical `"I64_eq"`
/// entry at all. Confirmed as a real, previously undiscovered gap via a
/// direct repro: `I64.beq` compiled to the generic "return Unit" stub
/// both as a bare call AND as an `if`'s own condition
/// (`is_native_bool_op_name`/`ensure_i1_cond` never recognized it as
/// already-i1 either, same root cause) -- every I64 equality check in
/// real code silently miscompiled. THIS key fixed the direct-call half;
/// the stub's other half (a value-position reference, which reads the
/// def rather than inlining) stayed open for the whole family until
/// `native_runtime_fn_name` gained its own `i64_*` group -- see that
/// chain's own comment.
/// `I64.ne`/`"I64_ne"` has the same "no such identifier" shape
/// (`Bool.not (I64.beq a b)` is how real code expresses it, per this
/// session's own `materialize_native_bool_arg` fix) -- its `"I64_ne"` key
/// below is left as dead code, not touched here (nothing reaches it, out
/// of scope for this fix).
///
/// Deliberately NO bare "file_exists"/"is_dir" keys: `std/io.mo`'s Path refactor
/// split each into a bodyless `#[native "X"]` primitive
/// (`IO.X_native`) plus a real-bodied `IO.X` wrapper (unwraps `Path` to
/// `String` first). `try_compile_inline_native_db` matches purely on
/// the CALLEE'S TEXTUAL NAME (`lookup_native_any`'s `extract_base_name`
/// strips the module qualifier, so `IO.X` and `IO.X_native` are
/// indistinguishable from a bare key "X") -- it does not check whether
/// that name actually resolves to the native-tagged def or to an
/// unrelated same-named wrapper. A bare "X" key here would silently
/// hijack every call to the WRAPPER `IO.X` too, skipping its `Path.to_
/// string` unwrap and passing the raw boxed `Path` constructor straight
/// to `monad_X`'s C implementation. Confirmed live: `IO.is_dir (Path.
/// path "/tmp")` read garbage past the `Path` object's header instead
/// of the real string, always false when compiled and run (correct
/// under the tree-walking interpreter, which doesn't go through this
/// codegen path at all -- invisible to `test`/`check`). `IO.file_exists`
/// had the identical wrapper/native name collision (as did `read_file`/
/// `write_file` while they were natives) -- this was silently corrupting
/// the self-compile's own compiled-and-run behavior. `IO.list_dir` was never
/// given a bare key at all and was never affected -- confirms the fix:
/// with no bare key, `IO.X_native`'s own call still dispatches
/// correctly (through a separate, properly-scoped attribute-based
/// mechanism unaffected by this table), while `IO.X`'s wrapper call
/// goes through ordinary compilation instead of being hijacked.
#[partial]
def native_op_table : HashMap String NativeOp :=
    let m := str_map_empty in
    let m := str_map_insert "I64_add" NativeOp.op_add m in
    let m := str_map_insert "I64_sub" NativeOp.op_sub m in
    let m := str_map_insert "I64_mul" NativeOp.op_mul m in
    let m := str_map_insert "I64_div" NativeOp.op_sdiv m in
    let m := str_map_insert "I64_beq" NativeOp.op_eq m in
    let m := str_map_insert "I64_lt" NativeOp.op_lt m in
    let m := str_map_insert "I64_gt" NativeOp.op_gt m in
    let m := str_map_insert "I64_ne" NativeOp.op_ne m in
    let m := str_map_insert "monad_file_exists" NativeOp.op_file_exists m in
    let m := str_map_insert "monad_is_dir" NativeOp.op_is_dir m in
    let m := str_map_insert "monad_string_hash" NativeOp.op_string_hash m in
    let m := str_map_insert "I64_to_string" NativeOp.op_i64_to_string m in
    m

/// `lookup_native` needs its match arms in two different forms depending
/// on caller: dotted arithmetic ops (`I64.add`) are only registered
/// under their fully-qualified, underscore-mangled form ("I64_add", to
/// agree with `compile_db_def_ir`'s own `def_symbol_name`
/// naming for the real global -- not that this global is ever actually
/// called when this fast path fires, but the table's naming convention
/// still has to agree with it), while the IO natives are registered
/// under their bare unqualified form ("println", not "IO_println") since
/// they're called both qualified (`IO.println`) and via an `open`ed bare
/// name. `try_compile_inline_native_db` used to look up ONLY the
/// bare-extracted form (`extract_base_name "I64.add"` => "add"), which
/// can never match "I64_add" -- so this fast path silently never fired
/// for any dotted arithmetic call, falling through to a real call to the
/// named global. That's normally invisible (the global just does the
/// same arithmetic) EXCEPT `I64.add`/`I64.sub`/etc. are native-signature
/// defs with no `:=` body at all (`init/number.mo`) -- their "body" is
/// `Term.hole`. At the time that repro was found,
/// `compile_db_def_ir` compiled that hole as a bogus `Unit` constructor
/// stub, so every dotted arithmetic call silently returned a garbage
/// heap pointer instead of computing anything; the family now has real
/// `native_runtime_fn_name` wrappers, so the named global is correct in
/// both call shapes. Try the underscore-mangled form first (covers
/// arithmetic), then the bare-extracted form (covers IO), so both naming
/// conventions work.
///
/// `native_op_table` is keyed on what the SOURCE wrote (`I64.add`,
/// mangled to `I64_add`), but every name reaching codegen now carries
/// its module (`init.number::I64.add`), so strip the qualifier first --
/// `unqualify_def_name` is exact, not a guess, because `::` cannot
/// appear in either half of a qualified name.
#[partial]
def lookup_native_any (name : String) : Option NativeOp :=
    let src := unqualify_def_name name in
    match lookup_native (replace_dots_with_underscores src) {
        Option.some op => Option.some op,
        Option.none => lookup_native (extract_base_name src),
    }

/// Which shape a native runtime function's raw `i64` result needs
/// wrapped into before it's a legitimate Monad-level value.
/// `passthrough` covers a native whose result IS ALREADY this
/// backend's uniform value representation for its type (a `String` is
/// always a bare `char*`/i64, per `monad_i64_to_string`'s own doc
/// comment -- `monad_string_concat` needs nothing further).
/// `bool_result` covers a native that's semantically `Bool`-returning
/// but implemented as a plain C `int64_t` 0/1 (`monad_string_eq`,
/// matching `NativeOp.op_eq`'s own raw-i1 comparison convention) -- a
/// raw 0/1 is NOT a valid `Bool` value on its own here: this backend's
/// `Bool` is always a tagged `Constructor` (`monad_ctor_Bool_true`/
/// `_false`, tags 1/2 -- see `constructor_tag`), and anything that
/// receives this result as an ordinary `Bool` VALUE rather than an
/// immediate `if`-condition (`ensure_i1_cond`'s own special-cased
/// native-comparison recognition only applies to a `Term` it can see
/// is a direct native-op call, not a value already reduced to a bare
/// local/parameter) will call `monad_get_tag` on it, segfaulting on a
/// small integer address -- confirmed as a real gap via direct repro
/// (`String.beq` passed into an ordinary `Bool`-parameter function).
type NativeWrapKind {
    passthrough (rt_fn_name : String),
    bool_result (rt_fn_name : String),
    // `IO A`-returning natives (`monad_current_time`): call, then wrap
    // the raw result directly as `IO.mk (RawIO.io raw)` -- mirrors
    // `wrap_io_value_native_result_go` at the term-level fast-path call
    // site: this backend already treats a native-sourced C string as a
    // valid `String` value with no extra boxing.
    io_passthrough (rt_fn_name : String),
    // `RawIO A`-returning natives (the piped-subprocess family): call,
    // then wrap the raw result ONCE as `RawIO.io raw` -- no outer
    // `IO.mk`. The `.mo` wrappers in std/src/process.mo build the
    // user-facing `IO` type themselves (`IO.mk (proc_read c 0)`), the
    // same split `IO.pure`/`RawIO.pure` use, so the C side stays a raw
    // payload producer and the naming/defaults live in Monad source.
    raw_io_passthrough (rt_fn_name : String),
    // `IO Bool`-returning natives using the "truthy pointer" C
    // convention (`monad_file_exists`/`monad_is_dir` -- non-null
    // pointer for true, `NULL` for false, NOT already 0/1 like
    // `bool_result`'s `monad_string_eq` assumes): `icmp_ne` against 0
    // first (`materialize_truthy_ptr_as_bool`), then IO-wrap the result.
    io_truthy_ptr_bool_result (rt_fn_name : String),
}

/// A `#[native <name>]`-attributed def has no real body (`Term.hole`,
/// per `is_term_hole`) -- absent a special case, `compile_db_def_ir`
/// falls all the way through to its own `LLVMValue.void_val` arm below,
/// silently compiling EVERY native def to the exact same "return Unit"
/// stub regardless of what it's actually supposed to do (confirmed as a
/// real gap: `String.concat`'s own compiled body was this stub,
/// producing a do-block that printed nothing meaningful). Whitelisted
/// to the natives this backend actually has a real C implementation
/// for (`runtime/src/runtime.c`) -- anything else still falls through
/// to the unchanged stub behavior below, so this can never newly break
/// a native this backend doesn't implement yet.
#[partial]
def native_runtime_fn_name (attrs : List Attribute) : Option NativeWrapKind :=
    match native_attr_target_name attrs {
        Option.none => Option.none,
        Option.some target =>
            if String.beq target "string_concat" then Option.some (NativeWrapKind.passthrough "monad_string_concat")
            else if String.beq target "string_concat_list" then Option.some (NativeWrapKind.passthrough "monad_string_concat_list")
            else if String.beq target "string_eq" then Option.some (NativeWrapKind.bool_result "monad_string_eq")
            // `String.length` (std/string.mo) had no entry here either --
            // same "confirmed as a real gap" shape as `string_concat`'s
            // own doc comment above: a `#[native string_length]` def with
            // no real body silently compiled to the generic "return Unit"
            // stub, discarding its argument entirely. Found via a direct
            // repro (`println (I64.to_string (String.length "abc"))`
            // printed a garbage heap address instead of `3`).
            else if String.beq target "string_length" then Option.some (NativeWrapKind.passthrough "monad_string_length")
            // `String.count_newlines`/`String.trailing_chars`
            // (init/string.mo) -- plain `(char*, i64) -> i64` scans, the
            // same passthrough shape as `string_length` just above. Both
            // halves of this file matter for them: without the entry
            // here the call compiles to the generic "return Unit" stub
            // that silently discards its arguments, and without the
            // `mk_decl` in `runtime_declarations` below it fails as
            // `call to undefined symbol(s): monad_...` out of the
            // call-target gate (`gate_result`, `lang/codegen/emit.mo`).
            else if String.beq target "string_count_newlines" then Option.some (NativeWrapKind.passthrough "monad_string_count_newlines")
            else if String.beq target "string_trailing_chars" then Option.some (NativeWrapKind.passthrough "monad_string_trailing_chars")
            // `std/array.mo`. Plain passthroughs: every value in this
            // backend is one machine word (a `Constructor*`, a `char*`,
            // or an unboxed i64), so an array's elements need no
            // per-type treatment and these return exactly the
            // representation their Monad-level type expects.
            // `array_get` returns a real `Option` Constructor built in
            // `runtime.c`, so it needs no `bool_result`-style
            // materialisation either.
            else if String.beq target "array_new" then Option.some (NativeWrapKind.passthrough "monad_array_new")
            else if String.beq target "array_len" then Option.some (NativeWrapKind.passthrough "monad_array_len")
            else if String.beq target "array_get" then Option.some (NativeWrapKind.passthrough "monad_array_get")
            else if String.beq target "array_with" then Option.some (NativeWrapKind.passthrough "monad_array_with")
            // The two `IO`-typed ones: `io_passthrough` wraps the raw
            // result as `IO.mk (RawIO.io raw)`, which is what `Monad.bind`'s `IO`
            // instance destructures.
            else if String.beq target "array_set_in_place" then Option.some (NativeWrapKind.io_passthrough "monad_array_set_in_place")
            else if String.beq target "array_freeze" then Option.some (NativeWrapKind.io_passthrough "monad_array_freeze")
            // `String.hash`'s `#[native string_hash]` -- pure `U64`
            // result, same shape as `string_length`. `IO.file_exists`/
            // `is_dir` (`std/io.mo`, `#[native "X_native"]` on the
            // WRAPPED, `_native`-suffixed defs) were
            // the same "confirmed as a real gap" stub for any reference
            // to them that doesn't go through the term-level fast path
            // (`try_compile_inline_native_db`/`lookup_native_any`) --
            // which is every reference now that each has a real-bodied
            // `IO.X` wrapper calling `IO.X_native` as an ORDINARY call
            // (`Term.app (Term.var ...)` referencing the global by name,
            // never inlined). Confirmed live: `IO.is_dir (Path.path
            // "/tmp")`, compiled and run, always "false" -- its own
            // compiled `IO_is_dir_native` global was the bogus Unit
            // stub, called for real from `IO_is_dir`'s own compiled body.
            else if String.beq target "string_hash" then Option.some (NativeWrapKind.passthrough "monad_string_hash")
            else if String.beq target "current_time" then Option.some (NativeWrapKind.io_passthrough "monad_current_time")
            // Raw nanoseconds, same CLOCK_MONOTONIC origin as
            // `current_time` (std/io.mo). The test runner's synthesized
            // driver times each test with this and does every unit
            // conversion itself, in Monad -- see
            // `lang/codegen/test_driver.mo`.
            else if String.beq target "current_time_nano" then Option.some (NativeWrapKind.io_passthrough "monad_current_time_nano")
            // `String.lt`/`String.gt` (`init/string.mo`, `instance BOrd
            // String`'s own backing natives) -- same previously-unwired
            // gap as `string_length`/`string_hash` above (a `#[native]`
            // def with no real body silently compiled to the generic
            // "return Unit" stub). Confirmed live via a real compiled
            // binary: `std/map.mo`'s `instance [BOrd K] Map BTreeMap`'s
            // own `BOrd.lt`/`BOrd.gt` calls always took the SAME branch
            // regardless of input, corrupting every `BTreeMap String _`
            // built through this backend -- see `monad_string_lt`/`_gt`'s
            // own doc comment (`runtime/src/runtime.c`) for the full
            // story. `bool_result`, not `passthrough` -- same wrap kind
            // `string_eq` uses, for the same reason (a real `i1`-shaped
            // comparison result needs boxing into a tagged `Bool`, not a
            // raw `i64` passthrough).
            else if String.beq target "string_lt" then Option.some (NativeWrapKind.bool_result "monad_string_lt")
            else if String.beq target "string_gt" then Option.some (NativeWrapKind.bool_result "monad_string_gt")
            // `String.slice`/`String.drop` (init/string.mo) -- same
            // previously-unwired-wrapper gap as `string_length`/`string_
            // hash` above, but with a DEEPER root cause underneath it:
            // `monad_string_slice`/`monad_string_drop` didn't exist in
            // `runtime/src/runtime.c` AT ALL (confirmed live via a real
            // self-compiled binary calling itself: `remove_quotes_loop`'s
            // own `String.slice s 1 (String.length s - 1)` recursion
            // never actually shrank `s`, looping until the native stack
            // overflowed instead of terminating), so both the wrapper
            // AND the runtime primitive needed adding together -- see
            // `monad_string_slice`'s own doc comment, `runtime.c`, for
            // the exact (Rust-host-matching) clamping semantics.
            else if String.beq target "string_slice" then Option.some (NativeWrapKind.passthrough "monad_string_slice")
            else if String.beq target "string_drop" then Option.some (NativeWrapKind.passthrough "monad_string_drop")
            // RawIO.pure / RawIO.bind -- the opaque IO layer's native
            // constructors. `io_pure` wraps in `RawIO.io` (tag 7);
            // `io_bind` unwraps and calls the continuation. Both return
            // `RawIO` values (not `IO`), so `passthrough` is correct.
            else if String.beq target "io_pure" then Option.some (NativeWrapKind.passthrough "monad_io_pure")
            else if String.beq target "io_bind" then Option.some (NativeWrapKind.passthrough "monad_io_bind")
            else if String.beq target "file_exists" then Option.some (NativeWrapKind.io_truthy_ptr_bool_result "monad_file_exists")
            else if String.beq target "is_dir" then Option.some (NativeWrapKind.io_truthy_ptr_bool_result "monad_is_dir")
            // `std/io.mo`'s two remaining raw-stdio natives -- the
            // byte-level half of stdio the stream primitives cannot
            // express (`read_stdin_exact`'s fill-to-n read and a real
            // stdout flush). `RawIO` natives behind `.mo` wrappers, so
            // `raw_io_passthrough`. `IO.println`/`write_stdout`/
            // `write_stderr`/`read_line` are ordinary Monad over
            // `std/stream.mo` and have no native at all.
            //
            // Deliberately NO `native_op_table` entries for these: a
            // BARE key in that table hijacks every call whose callee's
            // *textual* name matches, including the same-named `pub`
            // wrapper (`IO.is_dir`'s own bug -- see the long comment
            // above the table).
            else if String.beq target "read_stdin_exact" then Option.some (NativeWrapKind.raw_io_passthrough "monad_read_stdin_exact")
            else if String.beq target "flush_stdout" then Option.some (NativeWrapKind.raw_io_passthrough "monad_flush_stdout")
            // ─── The compiler's own remaining closure ───────────────
            // Exactly the set `validate_no_unwired_natives` reported for
            // a self-compile of `cli/src/main.mo` -- wired together so the
            // bootstrap ladder advances in ONE step (each self-compile
            // costs ~14 minutes, so a partial wiring just relocates the
            // fail-fast error rather than making progress).
            //
            // Most are backed by GENERATED IR (`runtime/src/natives.mo`,
            // built in Monad itself from the `llvm.ir` ADTs);
            // the rest are C in `runtime.c`. Which one a symbol is makes
            // no difference here -- an entry just names a symbol, and
            // `compile_native_def_wrapper_ir` emits the same wrapper
            // either way.

            // Generated IR: pure byte loops over the raw-`char*` String
            // representation.
            else if String.beq target "string_starts_with" then Option.some (NativeWrapKind.bool_result "monad_string_starts_with")
            else if String.beq target "string_to_list" then Option.some (NativeWrapKind.passthrough "monad_string_to_list")
            else if String.beq target "string_get" then Option.some (NativeWrapKind.passthrough "monad_string_get")
            // Generated IR: UTF-8 character-indexed variant of
            // `string_get` above -- `string_get_char(s, i)` counts
            // non-continuation bytes (`(b & 0xC0) != 0x80`), so `i`
            // is a character index, not the byte index
            // `string_get` takes.
            else if String.beq target "string_get_char" then Option.some (NativeWrapKind.passthrough "monad_string_get_char")
            // Generated IR: single-instruction integer bodies. `U8`/`U64`
            // values are unboxed i64s here and the reference applies NO
            // width mask (`core_native.rs`'s own doc comment records this
            // known gap), so plain i64 ops ARE the matching semantics.
            else if String.beq target "u8_eq" then Option.some (NativeWrapKind.bool_result "monad_u8_eq")
            else if String.beq target "u8_lt" then Option.some (NativeWrapKind.bool_result "monad_u8_lt")
            else if String.beq target "u8_gt" then Option.some (NativeWrapKind.bool_result "monad_u8_gt")
            else if String.beq target "u64_eq" then Option.some (NativeWrapKind.bool_result "monad_u64_eq")
            else if String.beq target "u8_sub" then Option.some (NativeWrapKind.passthrough "monad_u8_sub")
            else if String.beq target "u8_mul" then Option.some (NativeWrapKind.passthrough "monad_u8_mul")
            else if String.beq target "u8_div" then Option.some (NativeWrapKind.passthrough "monad_u8_div")
            else if String.beq target "u64_mod" then Option.some (NativeWrapKind.passthrough "monad_u64_mod")
            else if String.beq target "u64_div" then Option.some (NativeWrapKind.passthrough "monad_u64_div")
            // The `U64` arithmetic half, wired 2026-09-23. Same no-mask rule
            // as `u64_eq`/`u64_mod`/`u64_div` above -- `core_native.rs` sends
            // add/sub/mul/xor through `int_binop`, and `U64` is already the
            // full i64 width, so there is no mask to apply. These were the
            // only `number::U64` members left unwired, which is what kept
            // `bench/src/hashmap_bucket_dispatch.mo` out of the sweep.
            else if String.beq target "u64_add" then Option.some (NativeWrapKind.passthrough "monad_u64_add")
            else if String.beq target "u64_sub" then Option.some (NativeWrapKind.passthrough "monad_u64_sub")
            else if String.beq target "u64_mul" then Option.some (NativeWrapKind.passthrough "monad_u64_mul")
            else if String.beq target "u64_xor" then Option.some (NativeWrapKind.passthrough "monad_u64_xor")
            // `u64_lt`/`u64_gt` are in the same `int_cmp` group as `u64_eq`
            // (`core_native.rs:217-222`), so they are i64-payload signed
            // comparisons with no mask -- `bool_result`, like `u64_eq`.
            else if String.beq target "u64_lt" then Option.some (NativeWrapKind.bool_result "monad_u64_lt")
            else if String.beq target "u64_gt" then Option.some (NativeWrapKind.bool_result "monad_u64_gt")
            // The fixed-width unsigned family, unlike the u8 ops above:
            // these DO mask to width, on both operands and the result,
            // matching `mask_to_suffix` (core/src/core_native.rs). They
            // exist because std/src/sha256.mo is written against `U32`
            // and could not be compiled at all without them.
            else if String.beq target "u8_add" then Option.some (NativeWrapKind.passthrough "monad_u8_add")
            else if String.beq target "u32_add" then Option.some (NativeWrapKind.passthrough "monad_u32_add")
            else if String.beq target "u32_sub" then Option.some (NativeWrapKind.passthrough "monad_u32_sub")
            else if String.beq target "u32_mul" then Option.some (NativeWrapKind.passthrough "monad_u32_mul")
            else if String.beq target "u32_lt" then Option.some (NativeWrapKind.bool_result "monad_u32_lt")
            else if String.beq target "u32_gt" then Option.some (NativeWrapKind.bool_result "monad_u32_gt")
            else if String.beq target "u32_and" then Option.some (NativeWrapKind.passthrough "monad_u32_and")
            else if String.beq target "u32_or" then Option.some (NativeWrapKind.passthrough "monad_u32_or")
            else if String.beq target "u32_xor" then Option.some (NativeWrapKind.passthrough "monad_u32_xor")
            else if String.beq target "u32_shl" then Option.some (NativeWrapKind.passthrough "monad_u32_shl")
            else if String.beq target "u32_shr" then Option.some (NativeWrapKind.passthrough "monad_u32_shr")
            else if String.beq target "u32_eq" then Option.some (NativeWrapKind.bool_result "monad_u32_eq")
            else if String.beq target "u8_to_u32" then Option.some (NativeWrapKind.passthrough "monad_u8_to_u32")
            else if String.beq target "i64_to_u32" then Option.some (NativeWrapKind.passthrough "monad_i64_to_u32")
            else if String.beq target "u32_to_u8" then Option.some (NativeWrapKind.passthrough "monad_u32_to_u8")
            // `U64` widening (`I64.to_u64`, `std/src/number.mo`) is the
            // IDENTITY: the reference's `int_to_int(args, U64)` masks to
            // `v as u64 as i64`, which changes nothing about an i64
            // payload. It is here rather than in `native_op_table`
            // because the table's entries are all `NativeOp`s and a
            // conversion has nothing to fold -- `I64_to_u32` is wired the
            // same way, by this chain alone.
            else if String.beq target "i64_to_u64" then Option.some (NativeWrapKind.passthrough "monad_i64_to_u64")
            else if String.beq target "u8_to_u64" then Option.some (NativeWrapKind.passthrough "monad_u8_to_u64")
            // The `U16`/`I8` comparisons, same unmasked-i64 family as the
            // `U8` entries above (the reference sends every width except
            // `U32` through one generic `int_cmp`).
            else if String.beq target "u16_eq" then Option.some (NativeWrapKind.bool_result "monad_u16_eq")
            else if String.beq target "u16_lt" then Option.some (NativeWrapKind.bool_result "monad_u16_lt")
            else if String.beq target "u16_gt" then Option.some (NativeWrapKind.bool_result "monad_u16_gt")
            // The `U16` arithmetic, newly reachable from the HTTP motes
            // (`motes/http/src/wire.mo`/`uri.mo`). `passthrough`, the
            // same kind the `u8`/`u32`/`i64` arithmetic uses, and
            // `runtime/src/natives.mo`'s own comment records why the
            // emitters are unmasked: the reference masks `U32` alone.
            else if String.beq target "u16_add" then Option.some (NativeWrapKind.passthrough "monad_u16_add")
            else if String.beq target "u16_sub" then Option.some (NativeWrapKind.passthrough "monad_u16_sub")
            else if String.beq target "u16_mul" then Option.some (NativeWrapKind.passthrough "monad_u16_mul")
            else if String.beq target "u16_div" then Option.some (NativeWrapKind.passthrough "monad_u16_div")
            else if String.beq target "i8_eq" then Option.some (NativeWrapKind.bool_result "monad_i8_eq")
            else if String.beq target "i8_lt" then Option.some (NativeWrapKind.bool_result "monad_i8_lt")
            else if String.beq target "i8_gt" then Option.some (NativeWrapKind.bool_result "monad_i8_gt")
            // The `I32` comparisons and `I32`↔`I64` conversions, newly
            // reachable from `motes/tls`: OpenSSL entry points return
            // `int`, and the handshake compares it. No mk_decl -- these
            // are `define`s in the runtime module (runtime/src/natives.mo),
            // and a `declare` beside a `define` is the invalid
            // redefinition the d64 comment warns about.
            else if String.beq target "i32_eq" then Option.some (NativeWrapKind.bool_result "monad_i32_eq")
            else if String.beq target "i32_lt" then Option.some (NativeWrapKind.bool_result "monad_i32_lt")
            else if String.beq target "i32_gt" then Option.some (NativeWrapKind.bool_result "monad_i32_gt")
            else if String.beq target "i32_to_i64" then Option.some (NativeWrapKind.passthrough "monad_i32_to_i64")
            else if String.beq target "i64_to_i32" then Option.some (NativeWrapKind.passthrough "monad_i64_to_i32")
            // The `I64` arithmetic/comparison family -- the last group in
            // `native_op_table` (see that table's own doc comment, and
            // `runtime/src/natives.mo`'s emitters for the semantics).
            // Every one of these has a DIRECT call site all over the
            // corpus, and direct call sites inline through
            // `try_compile_inline_native_db`, so their defs' own compiled
            // bodies were never reached in ordinary code -- which is why
            // this group is the one that outlived every earlier wiring
            // pass. A VALUE-position reference reads the def, and the def
            // was the generic hole-bodied "return Unit" stub; a stub
            // result consumed as a `Bool` (`if f x y then ...`) then
            // answered FALSE for every operand pair, equal or not. Live
            // consequence: `lang/src/core_eval.mo` passes `I64.beq` into
            // `native_i64_bool_binop` as a first-class argument, so the
            // self-hosted meta-evaluator computed `0 == 0` as false and
            // every `#[derive]`d `BEq`/`BOrd` body silently took its
            // "different constructor" arm.
            else if String.beq target "i64_add" then Option.some (NativeWrapKind.passthrough "monad_i64_add")
            else if String.beq target "i64_sub" then Option.some (NativeWrapKind.passthrough "monad_i64_sub")
            else if String.beq target "i64_mul" then Option.some (NativeWrapKind.passthrough "monad_i64_mul")
            else if String.beq target "i64_div" then Option.some (NativeWrapKind.passthrough "monad_i64_div")
            else if String.beq target "i64_eq" then Option.some (NativeWrapKind.bool_result "monad_i64_eq")
            else if String.beq target "i64_lt" then Option.some (NativeWrapKind.bool_result "monad_i64_lt")
            else if String.beq target "i64_gt" then Option.some (NativeWrapKind.bool_result "monad_i64_gt")
            // `F64` (`init/number.mo`): the family that used to be named
            // here only as the reason this backend had no floating point
            // at all. An F64 value is its IEEE-754 BIT PATTERN in an
            // ordinary i64 payload, so every one of these is an ordinary
            // i64-in/i64-out C call and the `NativeWrapKind`s are the
            // same ones the integer families use -- `passthrough` for the
            // arithmetic and the two conversions, `bool_result` for the
            // comparisons (`F64.beq`/`blt`/`bgt` really are `Bool`).
            // runtime.c's F64 section is where the bit patterns are
            // unpacked; its own comment records why the semantics there
            // are C arithmetic rather than something hand-rolled.
            else if String.beq target "f64_add" then Option.some (NativeWrapKind.passthrough "monad_f64_add")
            else if String.beq target "f64_sub" then Option.some (NativeWrapKind.passthrough "monad_f64_sub")
            else if String.beq target "f64_mul" then Option.some (NativeWrapKind.passthrough "monad_f64_mul")
            else if String.beq target "f64_div" then Option.some (NativeWrapKind.passthrough "monad_f64_div")
            else if String.beq target "f64_eq" then Option.some (NativeWrapKind.bool_result "monad_f64_eq")
            else if String.beq target "f64_lt" then Option.some (NativeWrapKind.bool_result "monad_f64_lt")
            else if String.beq target "f64_gt" then Option.some (NativeWrapKind.bool_result "monad_f64_gt")
            else if String.beq target "f64_to_string" then Option.some (NativeWrapKind.passthrough "monad_f64_to_string")
            // `f64_of_string` is the one member of this family with no
            // `#[native]` def behind it in `init/number.mo`: the COMPILER
            // calls it, to lower a float literal (`lang/codegen/emit.mo`'s
            // `compile_lit_ir`), so its call site is a compiler-internal
            // def rather than a number.mo one. Same convention, same
            // table -- a native reached from a def the compiler compiles
            // is an ordinary native.
            else if String.beq target "f64_of_string" then Option.some (NativeWrapKind.passthrough "monad_f64_of_string")
            // Generated IR: documented stubs (0 / true). `Bench` is a
            // measurement API, never load-bearing for correctness, and
            // the compiled runtime has no clock wired yet -- a typed
            // zero keeps `--verbose` compiles from crashing on a Unit
            // stub. Real timing is a later self-hosted-runtime phase.
            else if String.beq target "current_time" then Option.some (NativeWrapKind.io_passthrough "monad_current_time")
            else if String.beq target "bench_report" then Option.some (NativeWrapKind.bool_result "monad_bench_report")
            else if String.beq target "process_id" then Option.some (NativeWrapKind.passthrough "monad_process_id")
            else if String.beq target "build_commit" then Option.some (NativeWrapKind.passthrough "monad_build_commit")
            // C: libc-shaped or growable-buffer-shaped.
            else if String.beq target "string_to_lowercase" then Option.some (NativeWrapKind.passthrough "monad_string_to_lowercase")
            else if String.beq target "string_from_list" then Option.some (NativeWrapKind.passthrough "monad_string_from_list")
            // `#[native i64_to_string]` (`I64.to_string`, init/number.mo)
            // was the ONE member of this formatting family missing an
            // entry -- i32/u8/u64 just below all have one. `I64_to_string`
            // is in `native_op_table`, so every DIRECT call inlines and
            // works; only a VALUE-position reference fell through to the
            // "return Unit" stub and silently yielded an empty string.
            // Measured 2026-09-19: `list_show I64.to_string [42]` printed
            // `[]` instead of `[42]`, the emitted def's whole body being
            // `%t4 = call i64 @alloc_constructor(i64 0, i64 0)`; the
            // corpus repro is `std/src/list_tests1.mo`'s two
            // `list_show I64.to_string` tests, which is also why it went
            // unnoticed -- the direct-call path hides it.
            else if String.beq target "i64_to_string" then Option.some (NativeWrapKind.passthrough "monad_i64_to_string")
            else if String.beq target "i32_to_string" then Option.some (NativeWrapKind.passthrough "monad_i32_to_string")
            // Unsigned formatting: a U64 near the top of its range is a
            // NEGATIVE i64 in this backend's uniform representation, so
            // these can't share `monad_i64_to_string`. `U16.to_string`
            // joins them -- same reason (a 16-bit-truncated unsigned
            // decimal), newly reached by the HTTP motes' URL rendering
            // and `Wire.format_request`.
            else if String.beq target "u8_to_string" then Option.some (NativeWrapKind.passthrough "monad_u8_to_string")
            else if String.beq target "u16_to_string" then Option.some (NativeWrapKind.passthrough "monad_u16_to_string")
            else if String.beq target "u64_to_string" then Option.some (NativeWrapKind.passthrough "monad_u64_to_string")
            // `exec_cmd` is THE load-bearing one for the ladder:
            // `llvm/src/link.mo` shells out to `llc`/`clang` through
            // it, so without it a self-compiled compiler can never run
            // its own `compile` command at all.
            else if String.beq target "exec_cmd" then Option.some (NativeWrapKind.io_passthrough "monad_exec_cmd")
            // The piped-subprocess family (std/process.mo,
            // agent-skills.md Phase 4) -- `proc_spawn`/`write`/`read`/
            // `wait`. All four are `RawIO`-returning C functions in
            // `runtime.c` that build their own `Result`/`Option`/`I64`
            // payloads from the fixed prelude tags, so all four take
            // `raw_io_passthrough`: one `RawIO.io` wrap, with the
            // user-facing `IO` built by the `Proc.*` wrappers in
            // process.mo. `proc_read`'s second arg picks the stream
            // (0 = stdout, 1 = stderr) and `proc_wait`'s picks the
            // disposition (0 = reap, 1 = SIGKILL-then-reap) -- twin
            // natives merged behind an I64 flag rather than duplicated.
            // Deliberately no `native_op_table` entries, for the same
            // reason the raw-stdio group above has none: a bare key in
            // that table hijacks every same-named textual callee.
            else if String.beq target "proc_spawn" then Option.some (NativeWrapKind.raw_io_passthrough "monad_proc_spawn")
            else if String.beq target "proc_write" then Option.some (NativeWrapKind.raw_io_passthrough "monad_proc_write")
            else if String.beq target "proc_read" then Option.some (NativeWrapKind.raw_io_passthrough "monad_proc_read")
            else if String.beq target "proc_wait" then Option.some (NativeWrapKind.raw_io_passthrough "monad_proc_wait")
            // `term_ctl : I64 -> I64 -> RawIO I64` (motes/tui/src/
            // terminal.mo) -- the tui mote's ONE terminal-control
            // native: cbreak enter/leave, TIOCGWINSZ and stdin-poll
            // merged behind an I64 op flag (the second i64 is the
            // poll timeout; the mode/size ops ignore it),
            // the same one-entry-point-one-flag shape the proc family
            // just above set. `raw_io_passthrough` (one `RawIO.io` wrap;
            // the `Terminal.*` wrappers add the `IO.mk`), and
            // deliberately no `native_op_table` key, for the same
            // hijack reason as the proc family.
            else if String.beq target "term_ctl" then Option.some (NativeWrapKind.raw_io_passthrough "monad_term_ctl")
            else if String.beq target "list_dir" then Option.some (NativeWrapKind.io_passthrough "monad_list_dir")
            // `IO.get_env` (std/io.mo) -- `IO (Option String)`: the raw
            // result is a real `Option` Constructor built in runtime.c
            // (some=4/none=3, the same fixed tags `monad_array_get` and
            // runtime.mo's `rt_tag_some`/`rt_tag_none` use), so plain
            // `io_passthrough` (IO.mk/RawIO.io-wrap only) like `list_dir`. Wired
            // because `std/ansi.mo`'s `colors_enabled` reads
            // NO_COLOR/FORCE_COLOR/TERM through it, and the compiler's
            // own `--verbose` stage trace (std/src/log.mo) colorizes through
            // that.
            else if String.beq target "get_env" then Option.some (NativeWrapKind.io_passthrough "monad_get_env")
            // The async runtime (`std/concurrent/{fiber,combine}.mo`).
            // Seven of the eight are `IO`-returning the same way: call the
            // runtime, wrap the raw result in `IO.mk (RawIO.io _)`.
            // `await_fiber` is the exception -- what it hands back IS the
            // action's own result, already a complete `IO A`, so it is a
            // plain `passthrough` (the kind `io_pure`/`io_bind` use) and
            // the backend adds no second layer. See `monad_await_fiber`'s
            // own comment in runtime.c.
            //
            // The handles themselves are opaque: `Fiber`/`Scope` values
            // are raw runtime pointers, never constructors, which is why
            // nothing here needs a `constructor_tag` lookup for them.
            // `Fiber`'s own module says so ("Fiber handles are opaque
            // runtime objects; do not pattern match on them").
            else if String.beq target "fork_io" then Option.some (NativeWrapKind.io_passthrough "monad_fork_io")
            else if String.beq target "await_fiber" then Option.some (NativeWrapKind.passthrough "monad_await_fiber")
            else if String.beq target "cancel_fiber" then Option.some (NativeWrapKind.io_passthrough "monad_cancel_fiber")
            // `pollFiber` (std/concurrent/fiber.mo) -- `Fiber A ->
            // IO (Option A)`: await's non-blocking sibling. The raw
            // result is a real `Option` Constructor built in runtime.c
            // (some=4/none=3), so `io_passthrough` like `get_env` --
            // not `await_fiber`'s plain `passthrough`. The async
            // event-loop primitive tui's `Cmd.perform_async` and
            // weaver's turn loop poll every tick (weaver.md Phase 12).
            else if String.beq target "poll_fiber" then Option.some (NativeWrapKind.io_passthrough "monad_poll_fiber")
            else if String.beq target "sleep_io" then Option.some (NativeWrapKind.io_passthrough "monad_sleep_io")
            else if String.beq target "scope_new" then Option.some (NativeWrapKind.io_passthrough "monad_scope_new")
            else if String.beq target "scope_fork" then Option.some (NativeWrapKind.io_passthrough "monad_scope_fork")
            else if String.beq target "scope_drop" then Option.some (NativeWrapKind.io_passthrough "monad_scope_drop")
            // The TCP family (`std/io.mo`'s four `#[native "tcp_*"]`
            // defs, reached by `motes/moon`'s server and `motes/moose`'s
            // client). All four are `RawIO` natives behind `.mo` wrappers,
            // so `raw_io_passthrough`, like the `stream_*` family below
            // that reads, writes and closes what they open. A connection
            // or listener is an `FdStream`, whose runtime value is the
            // file descriptor itself.
            //
            // There is no Rust-host half to mirror: the reference
            // deliberately does not implement TCP (its maintenance cost
            // was not worth a second implementation), so this backend is
            // TCP's only implementation and `runtime/src/runtime.c`'s
            // comments are its specification.
            else if String.beq target "tcp_connect" then Option.some (NativeWrapKind.raw_io_passthrough "monad_tcp_connect")
            else if String.beq target "tcp_listen" then Option.some (NativeWrapKind.raw_io_passthrough "monad_tcp_listen")
            else if String.beq target "tcp_accept" then Option.some (NativeWrapKind.raw_io_passthrough "monad_tcp_accept")
            else if String.beq target "tcp_local_port" then Option.some (NativeWrapKind.raw_io_passthrough "monad_tcp_local_port")
            // `Ptr.null` (init/prelude.mo) -- the NULL pointer for the C
            // FFI's callback arguments. `passthrough` with zero params:
            // the call's result IS the def's value, the raw word 0.
            else if String.beq target "ptr_null" then Option.some (NativeWrapKind.passthrough "monad_ptr_null")
            // `std/bytebuf.mo`'s eight `#[native "bytebuf_*"]` defs -- a
            // flat byte buffer the FFI can address (motes/tls's
            // `SSL_read`/`SSL_write`). Compiled, a `ByteBuf` is a pointer
            // to a `BufObj` (runtime.c: element kind, recorded length,
            // 64-byte-aligned payload); the four `IO`-typed ones are
            // `io_passthrough` like the TCP family, `ptr` and `length`
            // are pure and stay bare `passthrough`es, and the two
            // `RawIO` text-bridge ones below are `raw_io_passthrough`.
            else if String.beq target "bytebuf_alloc" then Option.some (NativeWrapKind.io_passthrough "monad_bytebuf_alloc")
            else if String.beq target "bytebuf_of_list" then Option.some (NativeWrapKind.io_passthrough "monad_bytebuf_of_list")
            else if String.beq target "bytebuf_to_list" then Option.some (NativeWrapKind.io_passthrough "monad_bytebuf_to_list")
            else if String.beq target "bytebuf_free" then Option.some (NativeWrapKind.io_passthrough "monad_bytebuf_free")
            else if String.beq target "bytebuf_ptr" then Option.some (NativeWrapKind.passthrough "monad_bytebuf_ptr")
            else if String.beq target "bytebuf_len" then Option.some (NativeWrapKind.passthrough "monad_bytebuf_len")
            // The text bridge (`ByteBuf.to_string`/`of_string`): `RawIO`
            // natives behind `.mo` wrappers, so `raw_io_passthrough` --
            // the C side hands back a bare string / `BufObj` pointer.
            else if String.beq target "bytebuf_to_string" then Option.some (NativeWrapKind.raw_io_passthrough "monad_bytebuf_to_string")
            else if String.beq target "bytebuf_of_string" then Option.some (NativeWrapKind.raw_io_passthrough "monad_bytebuf_of_string")
            // `ByteBuf.truncate`'s raw half: a `RawIO Unit`, same kind.
            else if String.beq target "bytebuf_truncate" then Option.some (NativeWrapKind.raw_io_passthrough "monad_bytebuf_truncate")
            else if String.beq target "bytebuf_copy_into" then Option.some (NativeWrapKind.raw_io_passthrough "monad_bytebuf_copy_into")
            // `std/stream.mo`'s byte streams: the five effectful ones are
            // `RawIO` natives behind `.mo` wrappers (`raw_io_passthrough`;
            // the `Result`/`Unit`/fd words come back raw), and `std_fd` is
            // pure, so a bare `passthrough` -- the fd IS the value.
            else if String.beq target "stream_open" then Option.some (NativeWrapKind.raw_io_passthrough "monad_stream_open")
            else if String.beq target "stream_read" then Option.some (NativeWrapKind.raw_io_passthrough "monad_stream_read")
            else if String.beq target "stream_write" then Option.some (NativeWrapKind.raw_io_passthrough "monad_stream_write")
            else if String.beq target "stream_close" then Option.some (NativeWrapKind.raw_io_passthrough "monad_stream_close")
            else if String.beq target "stream_fd" then Option.some (NativeWrapKind.raw_io_passthrough "monad_stream_fd")
            else if String.beq target "std_fd" then Option.some (NativeWrapKind.passthrough "monad_std_fd")
            else Option.none,
    }

#[partial]
def native_attr_target_name (attrs : List Attribute) : Option String :=
    match attrs {
        List.empty => Option.none,
        List.cons a rest =>
            match a {
                Attribute.mk aname args =>
                    if id_eq aname (Identifier.id "native")
                    then attr_arg_as_string_first args
                    else native_attr_target_name rest,
            },
    }

#[partial]
def attr_arg_as_string_first (args : List AttrArg) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a _ =>
            match a {
                AttrArg.ident aid => Option.some (symbol_identifier aid),
                AttrArg.str s => Option.some s,
                _ => Option.none,
            },
    }

#[partial]
def mk_decl (name : String) (params : List String) (ret_ty : String) : LLVMDeclaration :=
    LLVMDeclaration.mk name params ret_ty

/// The `declare` list for `kind`: the same C symbols everywhere, except
/// that the natives whose IR calls are typed `i64` are declared `i64` on
/// wasm (wasm-ld checks signatures; native llc tolerates the historical
/// `void` mismatch).
#[partial]
pub def runtime_declarations_for (kind : TargetKind) : List LLVMDeclaration :=
    // CONVENTION: every parameter and return type below is i64. The
    // backend holds Strings (and pointers generally) as raw i64 values
    // ("a String is always a bare char*/i64", `NativeWrapKind`'s own doc
    // comment), so EVERY emitter -- `compile_native_def_wrapper_ir` (all
    // `NativeWrapKind`s), the `native_op` paths, the generated natives
    // -- types its calls with `LLVMType.i64_`, and a declare typed any
    // other way (`i8*` used to appear here, copied from the C header
    // shapes) silently mismatches every call site of that native in the
    // emitted module. The current `llc` (21.1.8) happens to accept a
    // mismatched direct call (verified: the call survives into real
    // assembly; the v28 binary built and ran with dozens of them), but
    // it is malformed IR per the spec and a stricter parser could
    // reject it. `test_runtime_decls_i64_convention` pins this.
    let void_ret : String := if TargetKind.is_wasm kind then "i64" else "void" in
    let d1 := mk_decl "monad_alloc" (List.cons "i64" List.empty) "i64" in
    let d2 := mk_decl "monad_retain" (List.cons "i64" List.empty) "void" in
    let d3 := mk_decl "monad_release" (List.cons "i64" List.empty) "void" in
    let d7 := mk_decl "monad_file_exists" (List.cons "i64" List.empty) "i64" in
    let d7b := mk_decl "monad_is_dir" (List.cons "i64" List.empty) "i64" in
    let d7c := mk_decl "monad_string_hash" (List.cons "i64" List.empty) "i64" in
    let d7d := mk_decl "monad_current_time" List.empty "i64" in
    let d7e := mk_decl "monad_current_time_nano" List.empty "i64" in
    let d8 := mk_decl "alloc_closure" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "i64" in
    let d9 := mk_decl "alloc_constructor" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d10 := mk_decl "alloc_string" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // Tag/field accessors for match dispatch (compile_match_ir) --
    // there's no other way to read back what an already-allocated value
    // was tagged/constructed with.
    let d11 := mk_decl "monad_get_tag" (List.cons "i64" List.empty) "i64" in
    let d12 := mk_decl "monad_get_field" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // Writes a constructor's field at allocation time (compile_con_ir) --
    // alloc_constructor only ever allocates space, it has no way to
    // accept field values itself.
    let d13 := mk_decl "monad_set_field" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) void_ret in
    // Fixed-arity indirect-call trampolines for a boxed, zero-capture
    // closure value (runtime.c's apply_closureN family) -- see that
    // file's own doc comment on the family. Used by
    // compile_general_db_call's callee dispatch whenever the callee is a
    // computed value rather than a statically-known global name.
    let d14 := mk_decl "apply_closure1" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d15 := mk_decl "apply_closure2" (apply_closure_arg_types 2) "i64" in
    let d16 := mk_decl "apply_closure3" (apply_closure_arg_types 3) "i64" in
    let d17 := mk_decl "apply_closure4" (apply_closure_arg_types 4) "i64" in
    let d18 := mk_decl "apply_closure5" (apply_closure_arg_types 5) "i64" in
    let d19 := mk_decl "apply_closure6" (apply_closure_arg_types 6) "i64" in
    let d20 := mk_decl "apply_closure7" (apply_closure_arg_types 7) "i64" in
    let d21 := mk_decl "apply_closure8" (apply_closure_arg_types 8) "i64" in
    // `I64.to_string` (init/number.mo) is, like `I64.add`, a
    // native-signature-only def with no `:=` body at all -- unlike
    // `I64.add`, it had no runtime backing whatsoever (no C function,
    // no NativeOp variant), so every call to it -- reached only once
    // `lookup_native_any`'s I64_add-style fast path was fixed to
    // actually fire, see that fix's own doc comment -- fell through to
    // the same "Term.hole compiles as a bogus Unit stub" bug: `println
    // (I64.to_string n)` printed nothing at all (a real, hand-compiled
    // repro). `monad_i64_to_string` (runtime.c) is the actual
    // implementation; `test_compile_i64_to_string_native`
    // (lang/codegen/test/compile_tests.mo) is its regression test.
    // i64, not the C header's `char*` -- see the CONVENTION comment at
    // the head of this list (the returned char* IS the String value,
    // held as i64, and every call site types it i64).
    let d22 := mk_decl "monad_i64_to_string" (List.cons "i64" List.empty) "i64" in
    // `Term.ntv`/`compile_ntv_ir`'s generic native-call mechanism (used
    // for every `#[native ...]`-attributed def, e.g. `String.length`)
    // emits a bare `call i64 @monad_<name>(...)` with no accompanying
    // `declare` of its own -- unlike a genuinely first-referenced-by-call
    // symbol in ordinary C, LLVM's textual IR does NOT implicitly
    // synthesize a declaration for it (confirmed via a direct repro: omitting
    // this line reproduced the exact same "use of undefined value
    // '@monad_string_length'" `llc` failure `monad_i64_to_string` (just
    // above) needed its own explicit declare entry to avoid) -- every
    // native this module ever calls needs its own entry here regardless
    // of which of the two parallel native-dispatch mechanisms
    // (`lookup_native_any` vs. `Term.ntv`) it goes through.
    let d23 := mk_decl "monad_string_length" (List.cons "i64" List.empty) "i64" in
    // `monad_string_count_newlines`/`monad_string_trailing_chars`
    // (runtime.c) -- two args, same i64-not-`char*` convention as d23.
    let d23a := mk_decl "monad_string_count_newlines" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d23b := mk_decl "monad_string_trailing_chars" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // Same requirement as `monad_string_length` just above --
    // `compile_native_def_wrapper_ir`'s own `call` (the "native def
    // compiles to a real wrapper" fix) hits the identical "no implicit
    // declare" gap.
    let d24 := mk_decl "monad_string_concat" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d24b := mk_decl "monad_string_concat_list" (List.cons "i64" List.empty) "i64" in
    let d25 := mk_decl "monad_string_eq" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // Closure free-variable capture (see `monad_closure_get_env`/
    // `monad_closure_set_env`, `runtime.c`, and `compile_db_lam_ir`'s
    // own doc comment above).
    let d26 := mk_decl "monad_closure_get_env" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d27 := mk_decl "monad_closure_set_env" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) void_ret in
    // Same "no implicit declare" requirement as every other native above
    // -- `monad_string_slice`/`monad_string_drop` (runtime.c) were added
    // together with their own `native_runtime_fn_name` wiring, see that
    // wiring's own doc comment.
    let d28 := mk_decl "monad_string_slice" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "i64" in
    let d29 := mk_decl "monad_string_drop" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // Same "no implicit declare" requirement as every other native above
    // -- `monad_string_lt`/`monad_string_gt` (runtime.c) were added
    // together with their own `native_runtime_fn_name` wiring, see that
    // wiring's own doc comment. Same signature shape as `monad_string_eq`
    // just above (two boxed-string i64s in, a raw 0/1 i64 out).
    let d30 := mk_decl "monad_string_lt" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d31 := mk_decl "monad_string_gt" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // The remaining genuinely-C-shaped natives (`runtime.c`): they need
    // libc (fork/exec, opendir, qsort) or growable buffers, which the
    // GENERATED natives (`runtime/src/natives.mo`) have no way to
    // express yet. Note the asymmetry: only these get a `declare` --
    // a generated native is `define`d in this same module, and a
    // `declare` alongside a `define` of one name is an invalid
    // redefinition `llc` rejects outright.
    let d32 := mk_decl "monad_string_to_lowercase" (List.cons "i64" List.empty) "i64" in
    let d33 := mk_decl "monad_string_from_list" (List.cons "i64" List.empty) "i64" in
    // Same i64-not-`char*` convention as `monad_i64_to_string` (d22) --
    // the CONVENTION comment at the head of this list.
    let d34 := mk_decl "monad_i32_to_string" (List.cons "i64" List.empty) "i64" in
    let d35 := mk_decl "monad_exec_cmd" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d36 := mk_decl "monad_list_dir" (List.cons "i64" List.empty) "i64" in
    let d37 := mk_decl "monad_u8_to_string" (List.cons "i64" List.empty) "i64" in
    let d38 := mk_decl "monad_u64_to_string" (List.cons "i64" List.empty) "i64" in
    let d39 := mk_decl "monad_process_id" List.empty "i64" in
    let d40 := mk_decl "monad_build_commit" List.empty "i64" in
    // `std/array.mo`'s six (runtime.c). Same "no implicit declare"
    // requirement as every native above -- without these, the
    // call-target gate (`gate_result`, `lang/codegen/emit.mo`) rejects
    // the module with "call to undefined symbol(s): monad_array_new".
    let d41 := mk_decl "monad_array_new" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d42 := mk_decl "monad_array_len" (List.cons "i64" List.empty) "i64" in
    let d43 := mk_decl "monad_array_get" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d44 := mk_decl "monad_array_with" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "i64" in
    let d45 := mk_decl "monad_array_set_in_place" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "i64" in
    let d46 := mk_decl "monad_array_freeze" (List.cons "i64" List.empty) "i64" in
    // `IO.get_env` (runtime.c) -- same "no implicit declare" requirement
    // as every native above; see its `native_runtime_fn_name` entry.
    let d47 := mk_decl "monad_get_env" (List.cons "i64" List.empty) "i64" in
    // `init/number.mo`'s F64 family (runtime.c). Same "no implicit
    // declare" requirement as every native above; `monad_f64_to_string`
    // and `monad_f64_of_string` are the binary<->text pair, both i64->i64
    // like `monad_i64_to_string` (d22) -- a `char*` and a bit pattern are
    // both just i64 here.
    let d48 := mk_decl "monad_f64_add" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d49 := mk_decl "monad_f64_sub" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d50 := mk_decl "monad_f64_mul" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d51 := mk_decl "monad_f64_div" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d52 := mk_decl "monad_f64_eq" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d53 := mk_decl "monad_f64_lt" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d54 := mk_decl "monad_f64_gt" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d55 := mk_decl "monad_f64_to_string" (List.cons "i64" List.empty) "i64" in
    let d56 := mk_decl "monad_f64_of_string" (List.cons "i64" List.empty) "i64" in
    // The async runtime (`runtime.c`). Same "no implicit declare"
    // requirement as every native above: without these the call-target
    // gate (`gate_result`, `lang/codegen/emit.mo`) rejects the module
    // with "call to undefined symbol(s): monad_fork_io". Every one
    // returns i64 under the CONVENTION at the head of this list -- a
    // fiber/scope handle and a `char*`/bit-pattern are all just i64 here.
    // `monad_scope_new` genuinely takes no arguments
    // (`def scope_new : IO Scope`), so its parameter list is empty and
    // the emitted `call` has no operands to type.
    let d57 := mk_decl "monad_fork_io" (List.cons "i64" List.empty) "i64" in
    let d58 := mk_decl "monad_await_fiber" (List.cons "i64" List.empty) "i64" in
    let d59 := mk_decl "monad_cancel_fiber" (List.cons "i64" List.empty) "i64" in
    let d60 := mk_decl "monad_sleep_io" (List.cons "i64" List.empty) "i64" in
    let d61 := mk_decl "monad_scope_new" List.empty "i64" in
    let d62 := mk_decl "monad_scope_fork" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d63 := mk_decl "monad_scope_drop" (List.cons "i64" List.empty) "i64" in
    // `U16.to_string` (`runtime.c`), the u8/u64 siblings' shape
    // (d37/d38). Same "no implicit declare" requirement as every native
    // above; the `u16` ARITHMETIC next to it in the wiring needs no
    // entry here because it is GENERATED (`runtime/src/natives.mo`),
    // and a declare beside a define of one name is the invalid
    // redefinition the comment above d32 warns about.
    let d64 := mk_decl "monad_u16_to_string" (List.cons "i64" List.empty) "i64" in
    // The TCP family (`runtime.c`). Same "no implicit declare"
    // requirement as every native above -- without these the call-target
    // gate (`gate_result`, `lang/codegen/emit.mo`) rejects the module
    // with "call to undefined symbol(s): monad_tcp_connect". Every
    // parameter and return is i64 under the CONVENTION at the head of
    // this list: a String, an `FdStream` (the file descriptor) and a
    // port are all i64 here.
    let d65 := mk_decl "monad_tcp_connect" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d66 := mk_decl "monad_tcp_listen" (List.cons "i64" List.empty) "i64" in
    let d67 := mk_decl "monad_tcp_accept" (List.cons "i64" List.empty) "i64" in
    let d72 := mk_decl "monad_tcp_local_port" (List.cons "i64" List.empty) "i64" in
    // `std/io.mo`'s two raw-stdio natives (`runtime.c`). Same "no
    // implicit declare" requirement as every native above. All i64
    // under the CONVENTION at the head of this list;
    // `monad_flush_stdout` genuinely takes no arguments, and returns the
    // Unit constructor pointer like `monad_stream_close` (d98).
    let d74 := mk_decl "monad_read_stdin_exact" (List.cons "i64" List.empty) "i64" in
    let d76 := mk_decl "monad_flush_stdout" List.empty "i64" in
    // `monad_io_pure`/`monad_io_bind` (runtime.c) -- the opaque IO layer's
    // native constructors. `io_pure` takes one i64 (the value) and returns
    // `RawIO.io` wrapping it; `io_bind` takes two i64s (the `RawIO` value and
    // the continuation closure) and returns the result of applying the
    // continuation. Same "no implicit declare" requirement as every native
    // above.
    let d78 := mk_decl "monad_io_pure" (List.cons "i64" List.empty) "i64" in
    let d79 := mk_decl "monad_io_bind" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // `monad_ptr_null` (runtime.c) -- `Ptr.null`'s backing function. No
    // parameters; the i64 result is the NULL word itself.
    let d80 := mk_decl "monad_ptr_null" List.empty "i64" in
    // `std/bytebuf.mo`'s first six (runtime.c) -- every arg and result i64
    // under the head-of-list convention: a `ByteBuf` is a pointer to its
    // `BufObj`, and `of_list`/`to_list`'s `List U8` is one i64 pointer to
    // the list's head, not a (pointer, length) pair.
    let d81 := mk_decl "monad_bytebuf_alloc" (List.cons "i64" List.empty) "i64" in
    let d82 := mk_decl "monad_bytebuf_of_list" (List.cons "i64" List.empty) "i64" in
    let d83 := mk_decl "monad_bytebuf_to_list" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d84 := mk_decl "monad_bytebuf_free" (List.cons "i64" List.empty) "i64" in
    let d85 := mk_decl "monad_bytebuf_ptr" (List.cons "i64" List.empty) "i64" in
    // `monad_bytebuf_len` (runtime.c) -- `ByteBuf.length`'s backing
    // function: the element count recorded in the `BufObj`.
    let d87 := mk_decl "monad_bytebuf_len" (List.cons "i64" List.empty) "i64" in
    // The piped-subprocess family (runtime.c) -- every handle, string
    // and `List String` is one i64 word under the uniform boxed
    // convention (`Child` is an opaque registry index, `FdStream`'s own
    // trick), and every result is i64: the `Result`/`Option`/`I64`
    // values these return are constructor POINTERS, and
    // `raw_io_passthrough` types the call's result as i64 and wraps
    // that word ONCE as `RawIO.io` (the `.mo` wrappers add the
    // `IO.mk`) -- the same "declare i64, not the struct you'd expect"
    // note the three `IO Unit` natives above carry. `monad_proc_read`'s
    // and `monad_proc_wait`'s second i64 are the stream/kill flags.
    let d88 := mk_decl "monad_proc_spawn" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d89 := mk_decl "monad_proc_write" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d90 := mk_decl "monad_proc_read" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d91 := mk_decl "monad_proc_wait" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // `monad_term_ctl` (runtime.c) -- `term_ctl : I64 -> I64 ->
    // RawIO I64`'s backing function: the i64 op flag plus one i64
    // argument (the poll timeout; the mode/size ops ignore it) in,
    // i64 result out (the mode ops' 1/0, the size packed as
    // rows*65536+cols, or the poll's readable/timeout/error).
    let d92 := mk_decl "monad_term_ctl" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // `std/bytebuf.mo`'s text bridge (runtime.c): buffer + length in,
    // string pointer out; string pointer in, `BufObj` pointer out.
    let d93 := mk_decl "monad_bytebuf_to_string" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d94 := mk_decl "monad_bytebuf_of_string" (List.cons "i64" List.empty) "i64" in
    // `std/stream.mo`'s byte streams (runtime.c): an `FdStream` is its
    // descriptor and a `ByteBuf` its `BufObj` pointer, so every arg and
    // result is one i64 word.
    let d95 := mk_decl "monad_stream_open" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d96 := mk_decl "monad_stream_read" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d97 := mk_decl "monad_stream_write" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d98 := mk_decl "monad_stream_close" (List.cons "i64" List.empty) "i64" in
    let d99 := mk_decl "monad_stream_fd" (List.cons "i64" List.empty) "i64" in
    let d100 := mk_decl "monad_std_fd" (List.cons "i64" List.empty) "i64" in
    // `ByteBuf.truncate` (runtime.c): buffer + new length in, Unit out.
    let d101 := mk_decl "monad_bytebuf_truncate" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    // `pollFiber` (runtime.c): an opaque fiber handle in, a real
    // `Option` Constructor out (some=4/none=3) -- the async event
    // loop's poll primitive.
    let d102 := mk_decl "monad_poll_fiber" (List.cons "i64" List.empty) "i64" in
    // `ByteBuf.copy_into` (runtime_core.c): dst, offset, src in; Unit out.
    let d103 := mk_decl "monad_bytebuf_copy_into" ["i64", "i64", "i64"] "i64" in
    [d1, d2, d3, d7, d7b, d7c, d7d, d7e, d8, d9, d10, d11, d12, d13,
     d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d23a, d23b, d24, d24b, d25, d26, d27, d28, d29, d30, d31,
     d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47,
     d48, d49, d50, d51, d52, d53, d54, d55, d56,
     d57, d58, d59, d60, d61, d62, d63, d64,
     d65, d66, d67, d72,
     d74, d76, d78, d79, d80, d81, d82, d83, d84, d85, d87,
     d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99, d100, d101, d102, d103]

/// The native target's declaration list -- the historical name, kept for
/// every existing caller and test.
pub def runtime_declarations : List LLVMDeclaration := runtime_declarations_for TargetKind.native

/// Whether an IR-facing native is available on `kind`.
pub type NativeAvailability {
    available,
    unavailable (reason : String),
}

/// Natives backed by OS processes, threads, sockets, files or preopens.
/// Both wasm profiles omit them; the target gate turns a reachable use into
/// a compile error naming the native and the target.
def wasm_os_only_natives : List String := [
    "fork_io", "await_fiber", "poll_fiber", "cancel_fiber", "scope_new", "scope_fork",
    "scope_drop", "sleep_io", "exec_cmd", "process_id", "proc_spawn",
    "proc_write", "proc_read", "proc_wait", "tcp_connect", "tcp_listen",
    "tcp_accept", "tcp_local_port", "file_exists", "is_dir", "list_dir",
    "get_env", "stream_open", "term_ctl",
]

/// Natives whose C implementation needs `snprintf`/`strtod`; the web
/// profile is freestanding, wasi-libc has them.
def web_only_natives : List String := ["f64_to_string", "f64_of_string"]

#[terminating]
def name_in (name : String) (names : List String) : Bool := match names {
    List.empty => false,
    List.cons hd tl => if String.beq name hd then true else name_in name tl,
}

/// Whether the native named `target` (its `#[native "..."]` spelling) can
/// be served on `kind`. Unknown names default to available, so a new native
/// is gated only when it is explicitly listed here.
pub def native_target_availability (kind : TargetKind) (target : String) : NativeAvailability :=
    match kind {
        TargetKind.native => NativeAvailability.available,
        TargetKind.wasi =>
            if name_in target wasm_os_only_natives
            then NativeAvailability.unavailable "the wasi profile has no OS threads, processes, sockets or filesystem preopens"
            else NativeAvailability.available,
        TargetKind.web =>
            if name_in target wasm_os_only_natives
            then NativeAvailability.unavailable "the web profile has no OS threads, processes, sockets or filesystems"
            else if name_in target web_only_natives
            then NativeAvailability.unavailable "the web profile is freestanding: no C library float formatting"
            else NativeAvailability.available,
    }

#[test]
def test_wasm_gates_posix_only_natives : Bool :=
    match native_target_availability TargetKind.wasi "term_ctl" {
        NativeAvailability.unavailable _ => true,
        NativeAvailability.available => false,
    }
        && match native_target_availability TargetKind.web "fork_io" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.wasi "tcp_connect" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.web "poll_fiber" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }

#[test]
def test_wasm_keeps_console_and_arithmetic : Bool :=
    match native_target_availability TargetKind.wasi "stream_write" {
        NativeAvailability.available => true,
        NativeAvailability.unavailable _ => false,
    }
        && match native_target_availability TargetKind.web "print_str" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }
        && match native_target_availability TargetKind.native "term_ctl" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }

#[test]
def test_web_gates_float_formatting : Bool :=
    match native_target_availability TargetKind.web "f64_to_string" {
        NativeAvailability.unavailable _ => true,
        NativeAvailability.available => false,
    }
        && match native_target_availability TargetKind.wasi "f64_to_string" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }

/// `apply_closureN`'s own declared param list: the closure value itself
/// plus `n` ordinary args, all i64 (matches every def's own uniform
/// boxed-i64 calling convention). `n` is the applied arity, so this
/// always produces `n + 1` total "i64" strings.
#[partial]
def apply_closure_arg_types (n : I64) : List String :=
    List.cons "i64" (repeat_str "i64" n)

#[partial]
def repeat_str (s : String) (n : I64) : List String :=
    if I64.beq n 0 then List.empty else List.cons s (repeat_str s (n - 1))
