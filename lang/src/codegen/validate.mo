/// The fail-fast gates.
///
/// Codegen has several ways to produce a silently WRONG program rather
/// than an error, and each of these exists because one of them actually
/// shipped:
///
/// * an unwired `#[native]` compiles to a "return Unit" stub -- a
///   runtime SIGSEGV, discovered only in the built binary;
/// * a struct literal that best-effort elaboration never desugared
///   compiles to a void placeholder;
/// * two defs sharing an LLVM symbol means one is silently dropped and
///   its callers re-pointed at the other -- the collision that crashed
///   the self-compiled compiler inside `strcmp`;
/// * a call to a symbol nothing defines surfaces only as `llc:
///   undefined value` at the END of a 15-25 minute self-compile, naming
///   one symbol and no call site.
///
/// All four run on the REACHABLE decls, so a bug in dead code cannot
/// block a build that never touches it.
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use lang::types {
  AttrArg, Attribute, Con, Decl, Def, Identifier, Literal, MatchCase, NamePath, Native,
  Term, binder_is_explicit, id_eq, show_identifier, term_peel,
}
use lib::scope {collect_classes, find_unresolved_class_calls_decls}
use lib::codegen::ctors {CtorClaim, collect_ctor_claims_inds}
use std::list {List.intercalate, List.length}
open IO {get_env, println}
use llvm::ir {
  LLVMBasicBlock, LLVMDeclaration, LLVMFunction, LLVMInstruction, LLVMModule,
  LLVMValue, PhiPair,
}
use lib::codegen::decls {def_name_str, extract_defs, extract_inductives, has_export_attr}
use runtime::natives {runtime_native_functions}
use lib::codegen::natives {
  lookup_native_any, native_attr_target_name, native_runtime_fn_name,
  runtime_declarations, NativeAvailability, native_target_availability,
}
use llvm::target {TargetKind}
use lang::codegen::symbols {def_symbol_name, ends_with_main, name_path_to_str, unqualify_def_name}
use lib::codegen::util {
  dedup_strs, join_semicolon_msgs, list_contains_str
}
use std::map {HashMap}

/// An `#[extern "c"]` declaration names a symbol in a FOREIGN library. It
/// must not bind a Monad runtime symbol (the `monad_*` functions in
/// runtime/src/): those have the uniform i64 native ABI and a safe
/// `#[native]` wrapper, which an extern call bypasses. If a mote needs
/// runtime functionality, add a `#[native]` in init/std with the full
/// wiring instead. This is checked over the reachable decls, like the
/// other gates.
#[partial]
pub def validate_no_monad_externs (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := find_monad_externs (extract_defs decl_list) List.empty in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (List.intercalate "; " msgs),
    }

#[partial]
def find_monad_externs (defs : List Def) (acc : List String) : List String :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            match monad_extern_message d {
                Option.none => find_monad_externs rest acc,
                Option.some m => find_monad_externs rest (List.cons m acc),
            }
    }

def monad_extern_message (d : Def) : Option String :=
    match d {
        Def.mk {name, attrs, ..} =>
            match has_extern_attr attrs {
                false => Option.none,
                true =>
                    match extern_link_name attrs {
                        Option.some link => monad_extern_check name link,
                        Option.none =>
                            // No explicit link_name: the C symbol defaults
                            // to the def's last name segment. After
                            // qualification that segment may carry a
                            // `modpath::` or `modpath.` prefix, so check
                            // all three spellings.
                            match name_path_last name {
                                Option.none => Option.none,
                                Option.some segment =>
                                    if String.starts_with "monad_" segment
                                       || String.contains segment "::monad_"
                                       || String.contains segment ".monad_"
                                    then Option.some (extern_message name segment)
                                    else Option.none,
                            },
                    },
            }
    }

/// Whether the def carries any `#[extern ...]` attribute. Without this,
/// an ordinary def whose name happens to start with `monad_` would be
/// treated as an extern and rejected.
def has_extern_attr (attrs : List Attribute) : Bool :=
    match attrs {
        List.empty => false,
        List.cons a rest =>
            match a {
                Attribute.mk aname _ =>
                    if id_eq aname (Identifier.id "extern") then true else has_extern_attr rest,
            }
    }

def extern_message (name : NamePath) (link : String) : String :=
    String.concat_list
        ["extern `", link, "` on `", name_path_to_str name,
         "` binds a Monad runtime symbol; declare it as a #[native] in init/std instead"]

def monad_extern_check (name : NamePath) (link : String) : Option String :=
    if String.starts_with "monad_" link
    then Option.some (extern_message name link)
    else Option.none

/// The last identifier of a name path, as written. Qualification may pack
/// `modpath::name` into a single segment, which is why the caller also
/// checks for a `::monad_` substring.
def last_identifier_name (ids : List Identifier) : Option String :=
    match ids {
        List.empty => Option.none,
        List.cons id rest =>
            match rest {
                List.empty => Option.some (show_identifier id),
                List.cons _ _ => last_identifier_name rest,
            }
    }

def name_path_last (name : NamePath) : Option String :=
    match name {
        NamePath.mk ids => last_identifier_name ids
    }

/// The explicit `link_name := "..."` of an `#[extern ...]` attribute, if
/// any. The fallback symbol (the def's own last name segment) is checked
/// in `monad_extern_message`.
def extern_link_name (attrs : List Attribute) : Option String :=
    match attrs {
        List.empty => Option.none,
        List.cons a rest =>
            match a {
                Attribute.mk aname aargs =>
                    if id_eq aname (Identifier.id "extern")
                    then find_link_name_arg aargs
                    else extern_link_name rest,
            }
    }

def link_name_value (v : AttrArg) : Option String :=
    match v {
        AttrArg.str s => Option.some s,
        _ => Option.none,
    }

def find_link_name_arg (args : List AttrArg) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            match a {
                AttrArg.named n v =>
                    if id_eq n (Identifier.id "link_name")
                    then link_name_value v
                    else find_link_name_arg rest,
                AttrArg.group group_args => find_link_name_arg group_args,
                _ => find_link_name_arg rest,
            }
    }

/// A bodyless `#[native X]` def compiles to a "return Unit" stub unless
/// X is wired into the native backend somewhere -- a
/// `native_runtime_fn_name` entry (the def compiles to a real wrapper
/// calling a runtime `monad_*` function) or an inline `native_op_table`
/// key (`lookup_native_any` on the def's own name, the same lookup every
/// direct call site's own fast path uses). This exact gap has now cost
/// two multi-hour runtime-debugging sessions: `String.length`'s "printed
/// a garbage heap address instead of `3`" repro (see its own doc comment
/// above) and the self-compiled v25 binary's SIGSEGV deep inside
/// `List_reverse_append` -- `String_to_list` stubbed to Unit,
/// `String.ends_with`/`String.reverse` then pattern-matching that Unit
/// object and walking a wild pointer out of `monad_get_field`. In both
/// cases the miscompile was silent and structural: `llc`'s IR verifier
/// passes it, only running the binary finds it. Fail fast instead, over
/// the REACHABLE decls (same reasoning as
/// `validate_no_unresolved_class_calls`'s own doc comment: a bug in dead
/// code the program never uses must not block a compile that works),
/// with the native target and enclosing def named directly.
///
/// Deliberately NOT covered: a native that IS in `native_op_table` but has
/// no `native_runtime_fn_name` entry still has its stub def emitted (direct
/// calls inline, but a VALUE-position reference -- `List.map I64.to_string
/// ids`, a class-instance method binding -- calls the stub global). That
/// narrower gap needs the def itself to compile a wrapper, not a validator;
/// left alone here rather than false-positive-ing every program that only
/// ever calls it directly.
///
/// That carve-out is now nearly empty, and the exception that ate it is
/// worth recording: the `I64_*` keys were the one group in
/// `native_op_table` with no runtime backing at all, and the missing half
/// was NOT benign. The stub's `alloc_constructor(0, 0)` result, applied
/// through `apply_closure*`, comes back as a constructor whose tag is
/// never `Bool.true`'s -- so a value-position `I64.beq`/`I64.lt` consumed
/// as a `Bool` answered FALSE for every operand pair, and it did so
/// silently (no crash, no link error). It stayed invisible until
/// `lang/src/core_eval.mo`'s `basic_native_table` passed `I64.beq` into
/// `native_i64_bool_binop`, which made the self-hosted meta-evaluator
/// compute `0 == 0` as false and quietly broke every `#[derive]`d
/// `BEq`/`BOrd` body. The family is wired now
/// (`native_runtime_fn_name`'s own `i64_*` group); `I64_ne` remains the
/// sole unwired key and is unreachable dead code.
#[partial]
pub def validate_no_unwired_natives (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := find_unwired_native_defs (extract_defs decl_list) in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
    }

/// One error message per reachable bodyless `#[native X]` def whose X is
/// wired nowhere -- see `validate_no_unwired_natives`'s own doc comment
/// for the fail-fast contract. Only BODYLESS natives are checked: a
/// real-bodied def compiles a real function whatever its attributes.
#[partial]
def find_unwired_native_defs (defs : List Def) : List String :=
    List.reverse (find_unwired_native_defs_go defs List.empty)

#[partial]
def find_unwired_native_defs_go (defs : List Def) (acc : List String) : List String :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Def.mk {name, typ := _typ, term := term_, constraints := _constraints, attrs, vis := _vis, ..} =>
                    match strip_db_lams term_ {
                        Term.hole =>
                            match native_attr_target_name attrs {
                                Option.some target =>
                                    match native_runtime_fn_name attrs {
                                        Option.some _ => find_unwired_native_defs_go rest acc,
                                        Option.none =>
                                            match lookup_native_any (def_symbol_name name) {
                                                Option.some _ => find_unwired_native_defs_go rest acc,
                                                Option.none =>
                                                    let def_name := name_path_to_str name in
                                                    let head := String.concat "native `" (String.concat target "`") in
                                                    let mid := String.concat " (needed by def `" (String.concat def_name "`)") in
                                                    let msg := String.concat head (String.concat mid " is not wired into the native backend -- it would silently compile to a 'return Unit' stub; add a monad_* runtime function + native_runtime_fn_name entry, or an inline native_op_table key") in
                                                    find_unwired_native_defs_go rest (List.cons msg acc),
                                            },
                                    },
                                Option.none => find_unwired_native_defs_go rest acc,
                            },
                        _ => find_unwired_native_defs_go rest acc,
                    },
            },
    }

/// A reachable bodyless native the selected target cannot serve is a
/// compile error naming the native and the target, not a link failure or a
/// run-time trap. Runs on the REACHABLE decls, like the unwired check.
#[partial]
pub def validate_native_target_availability (kind : TargetKind) (triple : String) (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := find_unavailable_native_defs kind triple (extract_defs decl_list) in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
    }

#[partial]
def find_unavailable_native_defs (kind : TargetKind) (triple : String) (defs : List Def) : List String :=
    List.reverse (find_unavailable_native_defs_go kind triple defs List.empty)

#[partial]
def find_unavailable_native_defs_go (kind : TargetKind) (triple : String) (defs : List Def) (acc : List String) : List String :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Def.mk {name, typ := _typ, term := term_, constraints := _constraints, attrs, vis := _vis, ..} =>
                    match strip_db_lams term_ {
                        Term.hole =>
                            match native_attr_target_name attrs {
                                Option.none =>
                                    match extern_target_problem kind triple name attrs {
                                        Option.none => find_unavailable_native_defs_go kind triple rest acc,
                                        Option.some msg => find_unavailable_native_defs_go kind triple rest (List.cons msg acc),
                                    },
                                Option.some target =>
                                    match native_target_availability kind target {
                                        NativeAvailability.available =>
                                            find_unavailable_native_defs_go kind triple rest acc,
                                        NativeAvailability.unavailable reason =>
                                            let def_name := name_path_to_str name in
                                            let msg := "native `" ++ target ++ "` (needed by def `" ++ def_name ++ "`) is not available on target `" ++ triple ++ "` (" ++ TargetKind.name kind ++ "): " ++ reason in
                                            find_unavailable_native_defs_go kind triple rest (List.cons msg acc),
                                    },
                            },
                        _ => find_unavailable_native_defs_go kind triple rest acc,
                    },
            },
    }

/// A `#[extern "c"]` binding that only exists on the web profile.
///
/// `motes/web_wasm` owns every browser extern and names each one `web_*`
/// (the prefix is also what keeps `validate_no_monad_externs` from treating
/// a browser import as a runtime symbol). On native/wasi the symbol has no
/// implementation at all, so a REACHABLE one is a compile error naming the
/// extern and the target instead of an `undefined symbol` at link -- the
/// same shape `native_target_availability` gives an unsupported native.
///
/// The check is reachability-based, not mote-based: `web_wasm`'s PURE parts
/// (`WebAbi`, `Glue.loader`) must keep running on every target, including
/// the golden and drift tests, so a whole-mote "web only" gate would be
/// wrong.
#[partial]
def extern_target_problem (kind : TargetKind) (triple : String) (name : NamePath) (attrs : List Attribute) : Option String :=
    match kind {
        TargetKind.web => Option.none,
        _ =>
            match extern_link_name attrs {
                Option.none => Option.none,
                Option.some link =>
                    if String.starts_with "web_" link
                    then
                        let def_name := name_path_to_str name in
                        Option.some (String.concat
                            ("extern `" ++ link ++ "` (needed by def `" ++ def_name ++ "`) is not available on target `" ++ triple ++ "` (" ++ TargetKind.name kind ++ "): ")
                            "it is part of the browser boundary (motes/web_wasm), which only the web profile implements")
                    else Option.none,
            },
    }

/// `#[export "c"]` shape checks. Run only on the web profile: every other
/// target ignores the attribute (a library that declares exports must stay
/// testable natively), so there is nothing to enforce there.
///
/// What a web export must be, and why:
/// * a real def with a body -- the compiler exports the def's own code, it
///   does not synthesize a foreign binding;
/// * a single identifier segment -- the name becomes a JS property
///   (`instance.exports.oak_mount`), so a dotted `with`-block name or a
///   path is not addressable;
/// * not `main` -- `ren_main_and_wrap` renames that symbol, so the export
///   would point at nothing;
/// * monomorphic and constraint-free -- the exported symbol has the
///   uniform i64 ABI with no dictionary arguments, so a caller in JS could
///   not supply them;
/// * unique -- two exports on one name would collide at link.
#[partial]
pub def validate_export_defs (kind : TargetKind) (triple : String) (decl_list : List Decl) : Result String (List Decl) :=
    match kind {
        TargetKind.native => Result.ok decl_list,
        TargetKind.wasi => Result.ok decl_list,
        TargetKind.web => export_check triple decl_list,
    }

#[partial]
def export_check (triple : String) (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := find_export_msgs (extract_defs decl_list) List.empty List.empty in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
    }

#[partial]
def find_export_msgs (defs : List Def) (seen : List String) (acc : List String) : List String := match defs {
    List.empty => List.reverse acc,
    List.cons d rest => find_export_msgs_one d rest seen acc,
}

/// One def's contribution, split out of the list walk: a `let` bound to an
/// `if` inside a `match` arm is a shape the Rust host's checker rejects
/// ("expected a function type, found `String`"), while the self-hosted
/// checker accepts it -- so the shared code keeps the conservative shape.
#[partial]
def find_export_msgs_one (d : Def) (rest : List Def) (seen : List String) (acc : List String) : List String :=
    match export_def_name d {
        Option.none => find_export_msgs rest seen acc,
        Option.some plain =>
            find_export_msgs rest (List.cons plain seen) (export_msgs_for plain d seen acc),
    }

#[partial]
def export_msgs_for (plain : String) (d : Def) (seen : List String) (acc : List String) : List String :=
    let dup := export_dup_msg plain seen in
    let problems := List.append dup (export_def_problems plain d) in
    List.append (List.reverse problems) acc

#[partial]
def export_dup_msg (plain : String) (seen : List String) : List String :=
    if list_contains_str seen plain
    then List.cons (String.concat "duplicate `#[export \"c\"]` name `" (String.concat plain "`")) List.empty
    else List.empty

/// The JS-visible name of an `#[export "c"]` def, or `none` for every other
/// def.
#[partial]
def export_def_name (d : Def) : Option String :=
    match d {
        Def.mk {name, typ := _typ, term := _term, constraints := _constraints, attrs, vis := _vis, ..} =>
            if has_export_attr attrs then Option.some (unqualify_def_name (def_symbol_name name)) else Option.none,
    }

#[partial]
def export_def_problems (plain : String) (d : Def) : List String :=
    match d {
        Def.mk {name, typ, term := term_, constraints, attrs, vis := _vis, ..} =>
            let label := String.concat "`#[export \"c\"]` def `" (String.concat plain "`") in
            // `rename_main` renames the entry symbol (`ends_with_main`,
            // i.e. source name exactly `main`), so that export would leave
            // its thunk with no target.
            let main_problem := if ends_with_main (def_symbol_name name)
                then List.cons (String.concat label " cannot be `main`: the runtime entry renames that symbol") List.empty
                else List.empty in
            let shape_problem := if String.contains plain "."
                then List.cons (String.concat label " must be a single identifier segment; a dotted name is not a JS property") List.empty
                else List.empty in
            let abi_problem := if export_abi_is_c attrs
                then List.empty
                else List.cons (String.concat label " must name the C ABI as `#[export \"c\"]`") List.empty in
            let body_problem := match strip_db_lams term_ {
                Term.hole => List.cons (String.concat label " needs a body: an export is the def's own code, not a foreign binding") List.empty,
                _ => List.empty,
            } in
            let implicit_problem := if export_has_implicit_param typ
                then List.cons (String.concat label " cannot have implicit parameters: the export ABI passes only explicit i64 words") List.empty
                else List.empty in
            let constraint_problem := if List.is_empty constraints
                then List.empty
                else List.cons (String.concat label " cannot have type-class constraints: no dictionary can cross the export ABI") List.empty in
            List.append main_problem (List.append shape_problem (List.append abi_problem (List.append body_problem (List.append implicit_problem constraint_problem)))),
    }

/// Whether the def's `#[export ...]` attribute names the C ABI. Mirrors the
/// `#[extern]` check (`build_extern_info`), which requires a positional
/// `"c"`: an unknown ABI string is a diagnostic, never silently treated as
/// C.
#[partial]
def export_abi_is_c (attrs : List Attribute) : Bool := match attrs {
    List.empty => false,
    List.cons a rest =>
        match a {
            Attribute.mk aname aargs =>
                if id_eq aname (Identifier.id "export")
                then export_args_have_c aargs
                else export_abi_is_c rest,
        },
}

#[partial]
def export_args_have_c (args : List AttrArg) : Bool := match args {
    List.empty => false,
    List.cons a rest =>
        match a {
            AttrArg.str s => if String.beq s "c" then true else export_args_have_c rest,
            _ => export_args_have_c rest,
        },
}

#[partial]
def export_has_implicit_param (typ : Term) : Bool := match term_peel typ {
    Term.pi b _ body => if binder_is_explicit b then export_has_implicit_param body else true,
    _ => false,
}

/// Fail fast on a struct literal that reached codegen still spelled as
/// `Literal.struct_lit`/`Literal.struct_update` instead of a real
/// `Term.con`.
///
/// `compile_lit_ir` compiles both of those to `void_val` -- a silent
/// placeholder written on the assumption that
/// `lang/typecheck/infer.mo`'s `type_check_struct_lit` ALWAYS desugars
/// them first (see its own doc comment there). That assumption holds
/// only for a def that elaboration actually SUCCEEDED on:
/// `elaborate_module_decls_best_effort` is best-effort by design, and
/// when `type_check` fails for a def it keeps the ORIGINAL, un-desugared
/// decl and codegen proceeds anyway. A bare struct literal with no
/// `: StructName` annotation and no expected type from context (the
/// literal `type_check_struct_lit` rejects with "cannot infer struct
/// type for struct literal") is exactly such a def, and `compile`/
/// `check` typecheck only the TARGET file -- so one written in a
/// DEPENDENCY module is never diagnosed anywhere and goes straight to
/// `void_val`.
///
/// That cost a full ladder rung. `check_file_cached` (lang/module.mo)
/// returned `{ result := { path := ..., diagnostics := ... }, cache :=
/// ... }` under a `return`; the self-compiled binary printed
/// `FAIL   (0 error(s))` -- empty path, and a `diagnostics` value that
/// answered "cons" to `run_check_loop`'s match while `List.length` read
/// it as empty -- then `print_diagnostics` recursed on its garbage tail
/// until the 16MB stack was gone (SIGSEGV, no output, frame-pointer
/// chain destroyed). Same silent-structural-miscompile shape as the
/// unwired-native stubs above: `llc` verifies it, only running the
/// binary finds it.
///
/// Reachable decls only, same reasoning as
/// `validate_no_unwired_natives`. The fix at any reported site is to
/// bind the literal to a local with an explicit type annotation first
/// (AGENTS.md's rule-1 pitfall).
#[partial]
def validate_no_undesugared_struct_lits (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := find_undesugared_struct_lit_defs (extract_defs decl_list) in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
    }

/// One message per reachable def whose body still contains an
/// un-desugared struct literal -- see
/// `validate_no_undesugared_struct_lits`'s own doc comment.
#[partial]
def find_undesugared_struct_lit_defs (defs : List Def) : List String :=
    List.reverse (find_undesugared_struct_lit_defs_go defs List.empty)

#[partial]
def find_undesugared_struct_lit_defs_go (defs : List Def) (acc : List String) : List String :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Def.mk {name, typ := _typ, term := term_, constraints := _constraints, attrs := _attrs, vis := _vis, ..} =>
                    if term_has_struct_lit term_
                    then
                        let def_name := name_path_to_str name in
                        let head := String.concat "def `" (String.concat def_name "`") in
                        let msg := String.concat head " contains a struct literal that never desugared to a constructor -- it would silently compile to a void placeholder; give the literal an explicit `: StructName` annotation, or bind it to an annotated local before passing it" in
                        find_undesugared_struct_lit_defs_go rest (List.cons msg acc)
                    else find_undesugared_struct_lit_defs_go rest acc,
            },
    }

/// Structural walk for a surviving `Literal.struct_lit`/
/// `Literal.struct_update` anywhere inside `t`. This gate's whole reason
/// for existing is that its caller runs on BEST-EFFORT decls -- a def
/// `type_check` rejected is left un-elaborated and codegen proceeds on it
/// anyway (see this file's own doc comment above on the SIGSEGV that
/// shape caused) -- so, unlike a gate that only ever sees type-checked
/// terms, this one is exactly where a leftover `Term.quote_`/`var_macro`
/// is most likely to still be sitting; it must cover them for real.
def term_has_struct_lit (t : Term) : Bool := match t {
    Term.var _idx _dbg => false,
    Term.lam _dbg typ body => term_has_struct_lit typ || term_has_struct_lit body,
    // Merged; inert on the folded flavour -- a quantifier's domain is a
    // sort, and a sort carries no struct literal.
    Term.pi _b arg ret => term_has_struct_lit arg || term_has_struct_lit ret,
    Term.app fun_ arg_ => term_has_struct_lit fun_ || term_has_struct_lit arg_,
    Term.ntv native => native_has_struct_lit native,
    Term.con con_ => con_has_struct_lit con_,
    Term.lit lit_ => lit_has_struct_lit lit_,
    // A sort carries no struct literal.
    Term.sort _level => false,
    Term.hole => false,
    // A bare macro-template var carries no struct literal, same as `var`.
    Term.var_macro _idx _dbg => false,
    // Must recurse, mirroring the `ctx` arm below: a struct literal can sit
    // under an unexpanded quote.
    Term.quote_ inner => term_has_struct_lit inner,
    // Must recurse, or a struct literal under a located term passes the
    // gate and later compiles to a `void_val` placeholder.
    Term.ctx _loc inner => term_has_struct_lit inner,
    // Must recurse: once `PathP` takes type arguments a struct literal can
    // sit under one, and this gate is what keeps it from reaching the
    // `void_val` placeholder.
    Term.cubical c => match c { { prim := _, args := args } => terms_have_struct_lit args },
}

def terms_have_struct_lit (ts : List Term) : Bool := match ts {
    List.empty => false,
    List.cons x rest => term_has_struct_lit x || terms_have_struct_lit rest,
}

def lit_has_struct_lit (l : Literal) : Bool := match l {
    Literal.num _n _suffix => false,
    Literal.flt _text _suffix => false,
    Literal.str _s => false,
    Literal.char _c => false,
    Literal.if_ cond then_ else_ =>
        term_has_struct_lit cond || term_has_struct_lit then_ || term_has_struct_lit else_,
    Literal.match_ scrutinee cases =>
        term_has_struct_lit scrutinee || cases_have_struct_lit cases,
    Literal.struct_lit _fields _type_name => true,
    Literal.struct_update _base _fields => true,
}

#[partial]
def native_has_struct_lit (n : Native) : Bool := match n {
    Native.mk _name _num_args args => opt_terms_have_struct_lit args,
}

#[partial]
def con_has_struct_lit (c : Con) : Bool := match c {
    Con.mk _name _typ_name _num_args args => opt_terms_have_struct_lit args,
}

#[partial]
def opt_terms_have_struct_lit (args : List (Option Term)) : Bool := match args {
    List.empty => false,
    List.cons opt_ rest =>
        match opt_ {
            Option.some t => term_has_struct_lit t || opt_terms_have_struct_lit rest,
            Option.none => opt_terms_have_struct_lit rest,
        },
}

#[partial]
def cases_have_struct_lit (cases : List MatchCase) : Bool := match cases {
    List.empty => false,
    List.cons c rest =>
        match c {
            MatchCase.mk _name _args body _fp _typ_name =>
                term_has_struct_lit body || cases_have_struct_lit rest,
        },
}

/// One message per LLVM symbol claimed by two or more reachable defs.
#[partial]
def validate_no_colliding_def_symbols (decl_list : List Decl) : Result String (List Decl) :=
    let msgs := colliding_def_symbol_msgs (extract_defs decl_list) str_map_empty in
    match msgs {
        List.empty => Result.ok decl_list,
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
    }

#[partial]
def colliding_def_symbol_msgs (defs : List Def) (seen : HashMap String Bool) : List String :=
    match defs {
        List.empty => List.empty,
        List.cons d rest =>
            let sym := def_name_str d in
            match str_map_lookup sym seen {
                Option.some _ =>
                    List.cons (String.concat "two definitions share the LLVM symbol `" (String.concat sym
                        "` -- one of them would be silently dropped; give them distinct names or distinct modules"))
                        (colliding_def_symbol_msgs rest seen),
                Option.none =>
                    if reserved_runtime_symbol sym
                    then List.cons (String.concat "def `" (String.concat sym
                            "` collides with a runtime symbol of the same name -- rename the def"))
                            (colliding_def_symbol_msgs rest (str_map_insert sym true seen))
                    else colliding_def_symbol_msgs rest (str_map_insert sym true seen),
            },
    }

/// The symbols the C runtime and the generated runtime natives already
/// own. A def landing on one of these is dropped by `dedup_funcs_by_name`
/// exactly like a def-vs-def collision -- `compile_db_module_with_debug`
/// concatenates `runtime_native_functions` ahead of the compiled defs,
/// so the runtime one wins and the real def vanishes.
#[partial]
def reserved_runtime_symbol (sym : String) : Bool :=
    if runtime_func_name_matches runtime_native_functions sym then true
    else runtime_decl_name_matches runtime_declarations sym

#[partial]
def runtime_func_name_matches (funcs : List LLVMFunction) (sym : String) : Bool := match funcs {
    List.empty => false,
    List.cons f rest => if String.beq (f.name) sym then true else runtime_func_name_matches rest sym,
}

#[partial]
def runtime_decl_name_matches (decls : List LLVMDeclaration) (sym : String) : Bool := match decls {
    List.empty => false,
    List.cons d rest =>
        match d {
            LLVMDeclaration.mk name _params _ret =>
                if String.beq name sym then true else runtime_decl_name_matches rest sym,
        },
}

/// Every function symbol reachable from `funcs` as a CALL TARGET -- the
/// `fn_name` of every `call`, plus every `fn_ref` (a callee named
/// directly by symbol rather than through a register).
#[partial]
def collect_call_targets (funcs : List LLVMFunction) : List String := match funcs {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            LLVMFunction.mk _name _params _ret _blocks _dbg =>
                List.append (call_targets_in_blocks (f.blocks)) (collect_call_targets rest),
        },
}

#[partial]
def call_targets_in_blocks (bs : List LLVMBasicBlock) : List String := match bs {
    List.empty => List.empty,
    List.cons b rest =>
        match b {
            LLVMBasicBlock.mk _label instrs =>
                List.append (call_targets_in_instrs instrs) (call_targets_in_blocks rest),
        },
}

#[partial]
def call_targets_in_instrs (is_ : List LLVMInstruction) : List String := match is_ {
    List.empty => List.empty,
    List.cons i rest => List.append (call_targets_in_instr i) (call_targets_in_instrs rest),
}

#[partial]
def call_targets_in_instr (i : LLVMInstruction) : List String := match i {
    LLVMInstruction.assign _t v => call_targets_in_value v,
    LLVMInstruction.ret v => call_targets_in_value v,
    LLVMInstruction.branch c _t _e => call_targets_in_value c,
    LLVMInstruction.store v _pty p => List.append (call_targets_in_value v) (call_targets_in_value p),
    LLVMInstruction.jump _l => List.empty,
    LLVMInstruction.comment _t => List.empty,
    // Same reachability treatment as `assign`/`ret`/`branch`/`store`
    // above -- a `call_void` calls a real function (`monad_release`,
    // currently) and must be tracked or reachability would strip a
    // declaration something in this instruction list genuinely calls.
    LLVMInstruction.call_void v => call_targets_in_value v,
    // Calls no one -- must stay empty, or reachability would keep a def alive
    // that nothing actually references.
    LLVMInstruction.loc_marker _loc => List.empty,
}

/// Total walk over `LLVMValue`. Every arm is spelled out rather than
/// falling through a wildcard: a new value constructor that can carry a
/// callee must fail to compile here rather than silently escape the
/// gate.
#[partial]
def call_targets_in_value (v : LLVMValue) : List String := match v {
    LLVMValue.call fn_name _rt args _tail => List.cons fn_name (call_targets_in_values args),
    LLVMValue.fn_ref name => List.cons name List.empty,
    LLVMValue.add a b => call_targets_in_pair a b,
    LLVMValue.sub a b => call_targets_in_pair a b,
    LLVMValue.mul a b => call_targets_in_pair a b,
    LLVMValue.sdiv a b => call_targets_in_pair a b,
    LLVMValue.udiv a b => call_targets_in_pair a b,
    LLVMValue.urem a b => call_targets_in_pair a b,
    LLVMValue.and_ a b => call_targets_in_pair a b,
    LLVMValue.or_ a b => call_targets_in_pair a b,
    LLVMValue.xor_ a b => call_targets_in_pair a b,
    LLVMValue.shl_ a b => call_targets_in_pair a b,
    LLVMValue.lshr_ a b => call_targets_in_pair a b,
    LLVMValue.icmp_eq a b => call_targets_in_pair a b,
    LLVMValue.icmp_ne a b => call_targets_in_pair a b,
    LLVMValue.icmp_slt a b => call_targets_in_pair a b,
    LLVMValue.icmp_sgt a b => call_targets_in_pair a b,
    LLVMValue.icmp_ult a b => call_targets_in_pair a b,
    LLVMValue.icmp_ugt a b => call_targets_in_pair a b,
    LLVMValue.zext v2 _f _t => call_targets_in_value v2,
    LLVMValue.trunc v2 _f _t => call_targets_in_value v2,
    LLVMValue.ptrtoint v2 _f _t => call_targets_in_value v2,
    LLVMValue.inttoptr v2 _f _t => call_targets_in_value v2,
    LLVMValue.bitcast v2 _f _t => call_targets_in_value v2,
    LLVMValue.sext v2 _f _t => call_targets_in_value v2,
    LLVMValue.typed v2 _t => call_targets_in_value v2,
    LLVMValue.gep base _idxs => call_targets_in_value base,
    LLVMValue.load _ty _pty p => call_targets_in_value p,
    // `entry` is an already-rendered text fragment (`global_fn_ptr_text`'s
    // `bitcast (... @"name" to i8*)`), not a bare symbol, so the callee
    // it names is not extractable here without re-parsing it. It is
    // always a shim emitted into this same function list by the site
    // that built it, so it cannot dangle -- the env values still get
    // walked.
    LLVMValue.alloc_closure _entry _arity env => call_targets_in_values env,
    LLVMValue.alloc_constructor _tag fields => call_targets_in_values fields,
    LLVMValue.native_op _op args => call_targets_in_values args,
    LLVMValue.phi pairs => call_targets_in_phis pairs,
    LLVMValue.int_ _n => List.empty,
    LLVMValue.int32_ _n => List.empty,
    LLVMValue.bool_ _b => List.empty,
    LLVMValue.void_val => List.empty,
    LLVMValue.var_ _n => List.empty,
    LLVMValue.parm_ _i => List.empty,
    LLVMValue.global_ _n => List.empty,
}

#[partial]
def call_targets_in_pair (a : LLVMValue) (b : LLVMValue) : List String :=
    List.append (call_targets_in_value a) (call_targets_in_value b)

#[partial]
def call_targets_in_values (vs : List LLVMValue) : List String := match vs {
    List.empty => List.empty,
    List.cons v rest => List.append (call_targets_in_value v) (call_targets_in_values rest),
}

#[partial]
def call_targets_in_phis (ps : List PhiPair) : List String := match ps {
    List.empty => List.empty,
    List.cons p rest =>
        match p {
            PhiPair.mk v _label => List.append (call_targets_in_value v) (call_targets_in_phis rest),
        },
}

#[partial]
def build_defined_symbol_set (funcs : List LLVMFunction) (decls : List LLVMDeclaration) : HashMap String Bool :=
    add_decl_symbols decls (add_func_symbols funcs str_map_empty)

#[partial]
def add_func_symbols (funcs : List LLVMFunction) (acc : HashMap String Bool) : HashMap String Bool := match funcs {
    List.empty => acc,
    List.cons f rest => add_func_symbols rest (str_map_insert (f.name) true acc),
}

#[partial]
def add_decl_symbols (decls : List LLVMDeclaration) (acc : HashMap String Bool) : HashMap String Bool := match decls {
    List.empty => acc,
    List.cons d rest =>
        match d {
            LLVMDeclaration.mk name _params _ret => add_decl_symbols rest (str_map_insert name true acc),
        },
}

#[partial]
def missing_call_targets (targets : List String) (defined : HashMap String Bool) : List String := match targets {
    List.empty => List.empty,
    List.cons t rest =>
        match str_map_lookup t defined {
            Option.some _ => missing_call_targets rest defined,
            Option.none => List.cons t (missing_call_targets rest defined),
        },
}

/// Strip lambda and quantifier prefixes from a de Bruijn Term body.
// Peels, for the same reason `collect_db_params` does: this decides
// whether a def is a BODYLESS native by stripping lams and testing for
// `Term.hole`, and a wrapper around the hole makes a real native look
// bodied -- silently skipping the unwired-native gate.
#[partial]
def strip_db_lams (term_ : Term) : Term := match term_peel term_ {
    Term.lam _dbg _typ body => strip_db_lams body,
    // One arm, two flavours. A quantifier is stripped exactly as the old
    // `Term.forall` arm stripped it; an EXPLICIT binder is not, matching the
    // old `Term.pi` catch-all -- and it must keep returning `term_` (the
    // wrapper) rather than the peeled `dom`, for the reason the note below
    // gives.
    Term.pi b _dom body =>
        if binder_is_explicit b then term_ else strip_db_lams body,
    // Returns the term WITH its wrapper, not the peeled one. Peeling is
    // only needed to see THROUGH a wrapper to a binder; the term this
    // finally lands on is the def's body, and its position is the one a
    // function most wants -- `compile_db_def_ir_body` compiles exactly
    // this, so peeling here would silently discard it.
    _ => term_,
}

// --- Elaboration-handoff measurement (codegen-from-checker, stage 11.0) ---
//
// What the checker left for codegen's syntactic fallbacks to cover. Report
// only: nothing here gates a build.

/// Per-bare-constructor-name claim counts, for the tag/arity keying that
/// resolves a constructor by spelling instead of by owner.
pub struct CtorSpread {
    counts : HashMap String I64,
    first : HashMap String I64,
    arity_multi : HashMap String Bool,
    bare_names : I64,
    multi_owner : I64,
    multi_arity : I64,
}

#[partial]
def scan_ctor_spread (claims : List CtorClaim) (st : CtorSpread) : CtorSpread := match claims {
    List.empty => st,
    List.cons cl rest =>
        match cl {
            CtorClaim.mk bare arity _qualified =>
                let st2 : CtorSpread := match str_map_lookup bare st.counts {
                    Option.none => { st with counts := str_map_insert bare 1 st.counts, first := str_map_insert bare arity st.first, bare_names := st.bare_names + 1 },
                    Option.some n =>
                        let st_n : CtorSpread := { st with counts := str_map_insert bare (n + 1) st.counts, multi_owner := if n == 1 then st.multi_owner + 1 else st.multi_owner } in
                        match str_map_lookup bare st.first {
                            Option.none => st_n,
                            Option.some a0 =>
                                if a0 == arity then st_n
                                else match str_map_lookup bare st.arity_multi {
                                    Option.some _ => st_n,
                                    Option.none => { st_n with arity_multi := str_map_insert bare true st_n.arity_multi, multi_arity := st_n.multi_arity + 1 },
                                },
                        }
                } in
                scan_ctor_spread rest st2,
        },
}

#[partial]
def reachable_def_names (defs : List Def) (acc : HashMap String Bool) : HashMap String Bool := match defs {
    List.empty => acc,
    List.cons d rest => reachable_def_names rest (str_map_insert (def_name_str d) true acc),
}

#[partial]
def restrict_decls_to_names (names : HashMap String Bool) (decls : List Decl) : List Decl := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.def_d def_ =>
                match str_map_lookup (def_name_str def_) names {
                    Option.some _ => List.cons d (restrict_decls_to_names names rest),
                    Option.none => restrict_decls_to_names names rest,
                },
            _ => restrict_decls_to_names names rest,
        },
}

#[partial]
def stats_take (xs : List String) (n : I64) : List String :=
    if I64.lt n 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (stats_take rest (n - 1)),
    }

#[partial]
def print_stats_lines (ls : List String) : IO Unit := match ls {
    List.empty => return unit,
    List.cons l rest => do { println l; print_stats_lines rest },
}

/// Print the handoff report when `verbose` or `MONAD_ELAB_STATS` is set.
/// `elaborated` is the decl list straight out of elaboration (before
/// `resolve_class_calls_decls`); `reachable` is the final filtered list.
/// Interim switch for the reachable-elaboration-failure gate
/// (`validate_reachable_elaborated`). The compiler's own self-compile still
/// has 55 decls (34 reachable) that fail to elaborate, all bare-name
/// collisions (`Param` in lang/types.mo and init/meta.mo, `MatchArm` in
/// lang/core_ir.mo and init/meta.mo, and the constructors those drag in).
/// Qualified-name resolution (plan item 10) removes them; the gate then
/// becomes unconditional and this switch is deleted.
#[partial]
pub def strict_elab_enabled : IO Bool := do {
    let env <- get_env "MONAD_STRICT_ELAB";
    return (match env { Option.some _ => true, Option.none => false })
}

#[partial]
pub def report_elab_stats (verbose : Bool) (failed : List String) (elaborated : List Decl) (reachable : List Decl) : IO Unit := do {
    let env <- get_env "MONAD_ELAB_STATS";
    let on : Bool := verbose || (match env { Option.some _ => true, Option.none => false });
    if not on then return unit else do {
        let classes := collect_classes elaborated;
        let reach_elab := restrict_decls_to_names (reachable_def_names (extract_defs reachable) str_map_empty) elaborated;
        let cc_all := find_unresolved_class_calls_decls classes elaborated;
        let cc_reach := find_unresolved_class_calls_decls classes reach_elab;
        let sl_all := find_undesugared_struct_lit_defs (extract_defs elaborated);
        let sl_reach := find_undesugared_struct_lit_defs (extract_defs reach_elab);
        let spread0 : CtorSpread := { counts := str_map_empty, first := str_map_empty, arity_multi := str_map_empty, bare_names := 0, multi_owner := 0, multi_arity := 0 };
        let spread := scan_ctor_spread (List.reverse (collect_ctor_claims_inds (extract_inductives reachable) List.empty)) spread0;
        let l_swallowed : String := "elab_stats: swallowed=" ++ I64.to_string (List.length failed);
        let swallowed_lines : List String := List.map (fn m => "elab_stats: swallowed " ++ m) (stats_take failed 100);
        let l_calls : String := "elab_stats: unresolved_class_call_sites graph=" ++ I64.to_string (List.length cc_all) ++ " reachable=" ++ I64.to_string (List.length cc_reach);
        let l_lits : String := "elab_stats: undesugared_struct_lit_defs graph=" ++ I64.to_string (List.length sl_all) ++ " reachable=" ++ I64.to_string (List.length sl_reach);
        let l_ctors : String := "elab_stats: ctor_bare_names reachable=" ++ I64.to_string spread.bare_names ++ " multi_owner=" ++ I64.to_string spread.multi_owner ++ " multi_arity=" ++ I64.to_string spread.multi_arity;
        let samples : List String := List.map (fn m => "elab_stats: sample " ++ m) (stats_take cc_reach 5);
        print_stats_lines (List.append [l_swallowed, l_calls, l_lits, l_ctors] (List.append swallowed_lines samples))
    }
}
