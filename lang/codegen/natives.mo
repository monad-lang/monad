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
use lang.types {AttrArg, Attribute}
use lang.codegen.ir {LLVMDeclaration, NativeOp, mk}
use lang.codegen.symbols {extract_base_name, replace_dots_with_underscores, unqualify_def_name}
use lang.codegen.util {str_map_empty, str_map_insert, str_map_lookup}
use std.map {}

#[partial]
def lookup_native (name : String) : Option NativeOp := str_map_lookup name native_op_table

/// `"I64_eq"` (no such identifier exists -- `I64.eq` doesn't typecheck,
/// "unknown variable") is deliberately NOT one of this table's keys: the
/// real, only I64 equality function throughout the whole corpus is
/// `I64.beq` (`init/number.mo`, the `BEq I64` instance's own method),
/// which mangles to `I64_beq`, never matching a hypothetical `"I64_eq"`
/// entry at all. Confirmed as a real, previously undiscovered gap via a
/// direct repro: `I64.beq` compiled to the generic "return Unit" stub
/// (`native_runtime_fn_name` has no entry for it either) both as a bare
/// call AND as an `if`'s own condition (`is_native_bool_op_name`/
/// `ensure_i1_cond` never recognized it as already-i1 either, same root
/// cause) -- every I64 equality check in real code silently miscompiled.
/// `I64.ne`/`"I64_ne"` has the same "no such identifier" shape
/// (`Bool.not (I64.beq a b)` is how real code expresses it, per this
/// session's own `materialize_native_bool_arg` fix) -- its `"I64_ne"` key
/// below is left as dead code, not touched here (nothing reaches it, out
/// of scope for this fix).
///
/// Deliberately NO bare "read_file"/"write_file"/"file_exists"/"is_dir"
/// keys (unlike "println", which keeps one): `std/io.mo`'s Path refactor
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
/// codegen path at all -- invisible to `test`/`check`). `IO.write_file`/
/// `read_file`/`file_exists` have the identical wrapper/native name
/// collision and are called throughout `lang/main.mo`/`lang/module.mo`/
/// `lang/codegen/link.mo` -- this was silently corrupting the self-
/// compile's own compiled-and-run behavior. `IO.list_dir` was never
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
    let m := str_map_insert "monad_print_str" NativeOp.op_print_str m in
    let m := str_map_insert "println" NativeOp.op_print_str m in
    let m := str_map_insert "monad_read_file" NativeOp.op_read_file m in
    let m := str_map_insert "monad_write_file" NativeOp.op_write_file m in
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
/// `Term.hole`, which `compile_db_def_ir` compiles as a bogus `Unit`
/// constructor stub. Confirmed via a direct repro
/// (`let a := 2 in let b := 3 in I64.add a b`, non-literal so constant
/// folding doesn't hide it): every dotted arithmetic call silently
/// returned a garbage heap pointer instead of computing anything. Try
/// the underscore-mangled form first (covers arithmetic), then the
/// bare-extracted form (covers IO), so both naming conventions work.
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
    // `IO String`-returning natives (`monad_read_file`): call, then wrap
    // the raw result directly as `IO.io raw` -- mirrors
    // `wrap_io_value_native_result_go`'s own treatment of read_file at
    // its (other, term-level fast-path) call site: this backend already
    // treats a native-sourced C string as a valid `String` value with no
    // extra boxing.
    io_passthrough (rt_fn_name : String),
    // `IO Bool`-returning natives using the "truthy pointer" C
    // convention (`monad_file_exists`/`monad_is_dir` -- non-null
    // pointer for true, `NULL` for false, NOT already 0/1 like
    // `bool_result`'s `monad_string_eq` assumes): `icmp_ne` against 0
    // first (`materialize_truthy_ptr_as_bool`), then IO-wrap the result.
    io_truthy_ptr_bool_result (rt_fn_name : String),
    // `IO Unit`-returning `monad_write_file`: needs a 3rd `len` arg
    // (`monad_string_length` on the content param) the mo-level call
    // site never supplies -- mirrors `emit_native_call2_instr`'s own
    // `op_write_file` special case.
    io_write_file (rt_fn_name : String),
}

/// A `#[native <name>]`-attributed def has no real body (`Term.hole`,
/// per `is_term_hole`) -- absent a special case, `compile_db_def_ir`
/// falls all the way through to its own `LLVMValue.void_val` arm below,
/// silently compiling EVERY native def to the exact same "return Unit"
/// stub regardless of what it's actually supposed to do (confirmed as a
/// real gap: `String.concat`'s own compiled body was this stub,
/// producing a do-block that printed nothing meaningful). Whitelisted
/// to the natives this backend actually has a real C implementation
/// for (`lang/codegen/runtime.c`) -- anything else still falls through
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
            // result as `IO.io raw`, which is what `Monad.bind`'s `IO`
            // instance destructures.
            else if String.beq target "array_set_in_place" then Option.some (NativeWrapKind.io_passthrough "monad_array_set_in_place")
            else if String.beq target "array_freeze" then Option.some (NativeWrapKind.io_passthrough "monad_array_freeze")
            // `String.hash`'s `#[native string_hash]` -- pure `U64`
            // result, same shape as `string_length`. `IO.write_file`/
            // `read_file`/`file_exists`/`is_dir` (`std/io.mo`, `#[native
            // "X_native"]` on the WRAPPED, `_native`-suffixed defs) were
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
            // `String.lt`/`String.gt` (`init/string.mo`, `instance BOrd
            // String`'s own backing natives) -- same previously-unwired
            // gap as `string_length`/`string_hash` above (a `#[native]`
            // def with no real body silently compiled to the generic
            // "return Unit" stub). Confirmed live via a real compiled
            // binary: `std/map.mo`'s `instance [BOrd K] Map BTreeMap`'s
            // own `BOrd.lt`/`BOrd.gt` calls always took the SAME branch
            // regardless of input, corrupting every `BTreeMap String _`
            // built through this backend -- see `monad_string_lt`/`_gt`'s
            // own doc comment (`lang/codegen/runtime.c`) for the full
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
            // `lang/codegen/runtime.c` AT ALL (confirmed live via a real
            // self-compiled binary calling itself: `remove_quotes_loop`'s
            // own `String.slice s 1 (String.length s - 1)` recursion
            // never actually shrank `s`, looping until the native stack
            // overflowed instead of terminating), so both the wrapper
            // AND the runtime primitive needed adding together -- see
            // `monad_string_slice`'s own doc comment, `runtime.c`, for
            // the exact (Rust-host-matching) clamping semantics.
            else if String.beq target "string_slice" then Option.some (NativeWrapKind.passthrough "monad_string_slice")
            else if String.beq target "string_drop" then Option.some (NativeWrapKind.passthrough "monad_string_drop")
            else if String.beq target "read_file" then Option.some (NativeWrapKind.io_passthrough "monad_read_file")
            else if String.beq target "file_exists" then Option.some (NativeWrapKind.io_truthy_ptr_bool_result "monad_file_exists")
            else if String.beq target "is_dir" then Option.some (NativeWrapKind.io_truthy_ptr_bool_result "monad_is_dir")
            else if String.beq target "write_file" then Option.some (NativeWrapKind.io_write_file "monad_write_file")
            // ─── The compiler's own remaining closure ───────────────
            // Exactly the set `validate_no_unwired_natives` reported for
            // a self-compile of `lang/main.mo` -- wired together so the
            // bootstrap ladder advances in ONE step (each self-compile
            // costs ~14 minutes, so a partial wiring just relocates the
            // fail-fast error rather than making progress).
            //
            // Most are backed by GENERATED IR (`lang/codegen/runtime.mo`,
            // built in Monad itself from the `lang.codegen.ir` ADTs);
            // the rest are C in `runtime.c`. Which one a symbol is makes
            // no difference here -- an entry just names a symbol, and
            // `compile_native_def_wrapper_ir` emits the same wrapper
            // either way.

            // Generated IR: pure byte loops over the raw-`char*` String
            // representation.
            else if String.beq target "string_starts_with" then Option.some (NativeWrapKind.bool_result "monad_string_starts_with")
            else if String.beq target "string_to_list" then Option.some (NativeWrapKind.passthrough "monad_string_to_list")
            else if String.beq target "string_get" then Option.some (NativeWrapKind.passthrough "monad_string_get")
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
            // Generated IR: documented stubs (0 / true). `Bench` is a
            // measurement API, never load-bearing for correctness, and
            // the compiled runtime has no clock wired yet -- a typed
            // zero keeps `--verbose` compiles from crashing on a Unit
            // stub. Real timing is a later self-hosted-runtime phase.
            else if String.beq target "current_time" then Option.some (NativeWrapKind.io_passthrough "monad_current_time")
            else if String.beq target "bench_report" then Option.some (NativeWrapKind.bool_result "monad_bench_report")
            else if String.beq target "process_id" then Option.some (NativeWrapKind.passthrough "monad_process_id")
            // C: libc-shaped or growable-buffer-shaped.
            else if String.beq target "string_to_lowercase" then Option.some (NativeWrapKind.passthrough "monad_string_to_lowercase")
            else if String.beq target "string_from_list" then Option.some (NativeWrapKind.passthrough "monad_string_from_list")
            else if String.beq target "i32_to_string" then Option.some (NativeWrapKind.passthrough "monad_i32_to_string")
            // Unsigned formatting: a U64 near the top of its range is a
            // NEGATIVE i64 in this backend's uniform representation, so
            // these can't share `monad_i64_to_string`.
            else if String.beq target "u8_to_string" then Option.some (NativeWrapKind.passthrough "monad_u8_to_string")
            else if String.beq target "u64_to_string" then Option.some (NativeWrapKind.passthrough "monad_u64_to_string")
            // `exec_cmd` is THE load-bearing one for the ladder:
            // `lang/codegen/link.mo` shells out to `llc`/`clang` through
            // it, so without it a self-compiled compiler can never run
            // its own `compile` command at all.
            else if String.beq target "exec_cmd" then Option.some (NativeWrapKind.io_passthrough "monad_exec_cmd")
            else if String.beq target "list_dir" then Option.some (NativeWrapKind.io_passthrough "monad_list_dir")
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

#[partial]
def runtime_declarations : List LLVMDeclaration :=
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
    let d1 := mk_decl "monad_alloc" (List.cons "i64" List.empty) "i64" in
    let d2 := mk_decl "monad_retain" (List.cons "i64" List.empty) "void" in
    let d3 := mk_decl "monad_release" (List.cons "i64" List.empty) "void" in
    let d4 := mk_decl "monad_print_str" (List.cons "i64" List.empty) "void" in
    let d5 := mk_decl "monad_read_file" (List.cons "i64" List.empty) "i64" in
    let d6 := mk_decl "monad_write_file" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "void" in
    let d7 := mk_decl "monad_file_exists" (List.cons "i64" List.empty) "i64" in
    let d7b := mk_decl "monad_is_dir" (List.cons "i64" List.empty) "i64" in
    let d7c := mk_decl "monad_string_hash" (List.cons "i64" List.empty) "i64" in
    let d7d := mk_decl "monad_current_time" List.empty "i64" in
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
    let d13 := mk_decl "monad_set_field" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "void" in
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
    let d27 := mk_decl "monad_closure_set_env" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "void" in
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
    // GENERATED natives (`lang/codegen/runtime.mo`) have no way to
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
    // `std/array.mo`'s six (runtime.c). Same "no implicit declare"
    // requirement as every native above -- without these,
    // `validate_all_call_targets_defined` rejects the module with
    // "call to undefined symbol(s): monad_array_new".
    let d41 := mk_decl "monad_array_new" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d42 := mk_decl "monad_array_len" (List.cons "i64" List.empty) "i64" in
    let d43 := mk_decl "monad_array_get" (List.cons "i64" (List.cons "i64" List.empty)) "i64" in
    let d44 := mk_decl "monad_array_with" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "i64" in
    let d45 := mk_decl "monad_array_set_in_place" (List.cons "i64" (List.cons "i64" (List.cons "i64" List.empty))) "i64" in
    let d46 := mk_decl "monad_array_freeze" (List.cons "i64" List.empty) "i64" in
    [d1, d2, d3, d4, d5, d6, d7, d7b, d7c, d7d, d8, d9, d10, d11, d12, d13,
     d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d24b, d25, d26, d27, d28, d29, d30, d31,
     d32, d33, d34, d35, d36, d37, d38, d39, d41, d42, d43, d44, d45, d46]

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
