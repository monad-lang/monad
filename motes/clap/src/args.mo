/// Small runtime helper library for CLI argument parsing over `List String`.
///
/// Used two ways:
/// - by hand, from `cli/src/main.mo` (which stays free of any macro/attribute
///   syntax — it is the file the bootstrap is built from; see
///   `cli/src/main.mo`'s own
///   header comment and the self-hosted parse/scope/typecheck tests in
///   `lang/tests/`);
/// - by generated code, from `#[derive Cli]`-annotated types — see
///   `derive_cli_meta`/`derive_cli` below, and the demo in
///   `lib/tests/cli_derive_tests.mo`.
///
/// Each operation returns a dedicated, non-generic result type
/// (`Cli.FlagResult`/`Cli.PosResult`/`Cli.OptResult`) rather than a generic
/// `Pair`/tuple. That's deliberate, not incidental: reusing `Pair A B` here
/// tripped a real type-checker gap where nested `match`es over types that
/// share a type-parameter name with `Result A E` (as `Pair`/`Option` both
/// do — everyone names their first param `A`) lose track of which `A` is
/// which. Dedicated concrete types sidestep it entirely — see the longer
/// note on `derive_cli_meta` below.

// The newer, spec-driven surface. Re-exported through this module because
// every existing consumer imports `clap::args {*}`, and `lib.mo` also
// re-exports this module wholesale.
pub use lib::spec {*}
pub use lib::help {*}
pub use lib::parse {*}
pub use lib::attr {*}

use std::list {List.any, List.filter, List.length}
// `String.concat_all` lives in `init/string.mo` (moved there by
// c431ba0, which deleted this file's own `cli_concat_all` copy). An
// explicit import is required, not optional: this module's defs are
// meta-evaluated during `#[derive Cli]` expansion, and that closure is
// scoped to the module's own declared dependencies -- without this the
// expansion fails with `unbound variable String.concat_all`, taking
// `cli/src/main.mo` and four test files down with it. `motes/json`
// imports from `init.string` the same way.
use init::string {}
use init::meta {TypeInfo, CtorInfo, FieldInfo, Expr, Decl}
open List {length}
open TypeInfo {type_info}
open CtorInfo {ctor_info}
open FieldInfo {field_info}
open Expr {e_var, e_str, e_int, e_bool, e_app, e_if, e_match, e_ctor}
open MatchArm {match_arm}
open Param {meta_param}
open Decl {d_def, d_error}

pub type Cli.FlagResult {
    flag_result (found : Bool) (rest : List String),
}

pub type Cli.PosResult {
    pos_result (value : Option String) (rest : List String),
}

pub type Cli.OptResult {
    opt_result (value : String) (rest : List String),
}

/// Scan `args` for `--<long>` or `-<short>`, removing the first occurrence
/// if present. Pass `""` for `short` to only recognize the long form. Flags
/// are position-independent — this finds the flag wherever it is and
/// returns the remaining args with it stripped out, order preserved.
pub def Cli.take_flag (long : String) (short : String) (args : List String) : Cli.FlagResult :=
    match args {
        List.empty => Cli.FlagResult.flag_result false List.empty,
        List.cons hd tl =>
            let want_long := String.concat "--" long in
            let want_short := String.concat "-" short in
            let is_short := if String.is_empty short then false else String.beq hd want_short in
            if String.beq hd want_long || is_short then
                Cli.FlagResult.flag_result true tl
            else
                match Cli.take_flag long short tl {
                    Cli.FlagResult.flag_result found rest =>
                        Cli.FlagResult.flag_result found (List.cons hd rest),
                }
    }

/// Take the first token off `args` as a positional value, if any.
pub def Cli.take_positional (args : List String) : Cli.PosResult :=
    match args {
        List.empty => Cli.PosResult.pos_result Option.none List.empty,
        List.cons hd tl => Cli.PosResult.pos_result (Option.some hd) tl,
    }

/// Scan `args` for `--<long> <value>`/`-<short> <value>`, removing both
/// tokens if present and returning `value`; falls back to `default` if
/// absent. Pass `""` for `short` to only recognize the long form.
/// (v1 scope: space-separated `<flag> <value>` only — no `--<long>=<value>`
/// combined form, see this module's plan note on `String.split` not
/// existing yet.)
pub def Cli.take_opt (long : String) (short : String) (default : String) (args : List String) : Cli.OptResult :=
    match args {
        List.empty => Cli.OptResult.opt_result default List.empty,
        List.cons hd tl =>
            let want_long := String.concat "--" long in
            let want_short := String.concat "-" short in
            let is_short := if String.is_empty short then false else String.beq hd want_short in
            if String.beq hd want_long || is_short then
                match tl {
                    List.cons value rest => Cli.OptResult.opt_result value rest,
                    List.empty => Cli.OptResult.opt_result default List.empty,
                }
            else
                match Cli.take_opt long short default tl {
                    Cli.OptResult.opt_result value rest =>
                        Cli.OptResult.opt_result value (List.cons hd rest),
                }
    }

// --- #[derive Cli]: reflection-as-data metaprogramming ---
//
// `derive_cli_meta` is an ordinary `TypeInfo -> List Decl` function (see
// `init/meta.mo`/`plans/review-and-reduce-the-greedy-nest.md`), invoked via
// `reflect_type_info!` through the `derive_cli` decl-gen macro below —
// the same mechanism `std/derive.mo`'s four derives use (`derive_lens`/
// `derive_debug`/`derive_beq`/`derive_bord`), replacing the former
// hand-rolled Rust term-builder this file's header comment used to point
// at. Generates `parse_<lowercased type name> : List String -> Result
// String <TypeName>`, dispatching on the first argv token against each
// constructor's own name; within a constructor, every `#[arg]`-annotated
// (`Bool`-typed, v1) field is a `--<name>` flag, everything else a
// required positional consumed in declared order.
//
// Every intermediate binding in the generated code (`__cli_hd`/
// `__cli_rest`/`__cli_args`/`__cli_opt`) uses a fixed, `__cli_`-prefixed
// name rather than a gensym counter (the Rust generator's own approach):
// a flag/positional's actual VALUE is always bound under the field's own
// declared name instead (e.g. `Cli.take_flag "verbose" "" __cli_rest`
// binds its result's `found` field as `verbose` directly), so the final
// `Ctor field1 ... fieldN` application just references each field by its
// own name, in ORIGINAL declared order — regardless of the flags-then-
// positionals order fields are actually PARSED in. Real lexical scoping
// makes every `__cli_rest` rebinding, across however many flags/
// positionals a constructor has, a fresh, properly nested binding with no
// hygiene concerns; the fixed `__cli_` prefix just keeps those auxiliary
// names out of a real field's own namespace.

def cli_field_name (f : FieldInfo) : String :=
    match f { field_info name typ attrs default => name }

def cli_field_typ (f : FieldInfo) : Expr :=
    match f { field_info name typ attrs default => typ }

def cli_field_attrs (f : FieldInfo) : List String :=
    match f { field_info name typ attrs default => attrs }

def cli_field_default (f : FieldInfo) : Option Expr :=
    match f { field_info name typ attrs default => default }

// ─── Type classification ──────────────────────────────────────────────

/// The field shapes `#[derive Cli]` understands. Anything else is a
/// `Decl.d_error` naming the field, rather than generated code that fails
/// with a confusing type error.
type Cli.TypeClass {
    tc_bool,
    tc_string,
    tc_i64,
    tc_option_string,
    tc_option_i64,
    tc_list_string,
}

def cli_class_of_name (name : String) : Option Cli.TypeClass :=
    if String.beq name "Bool" then Option.some Cli.TypeClass.tc_bool
    else if String.beq name "String" then Option.some Cli.TypeClass.tc_string
    else if String.beq name "I64" then Option.some Cli.TypeClass.tc_i64
    else Option.none

def cli_option_class (a : Expr) : Option Cli.TypeClass :=
    match a {
        e_var name =>
            if String.beq name "String" then Option.some Cli.TypeClass.tc_option_string
            else if String.beq name "I64" then Option.some Cli.TypeClass.tc_option_i64
            else Option.none,
        _ => Option.none,
    }

def cli_list_class (a : Expr) : Option Cli.TypeClass :=
    match a {
        e_var name => if String.beq name "String" then Option.some Cli.TypeClass.tc_list_string else Option.none,
        _ => Option.none,
    }

def cli_class_of_app (name : String) (a : Expr) : Option Cli.TypeClass :=
    if String.beq name "Option" then cli_option_class a
    else if String.beq name "List" then cli_list_class a
    else Option.none

def cli_type_class (t : Expr) : Option Cli.TypeClass :=
    match t {
        e_var name => cli_class_of_name name,
        e_app f a =>
            match f {
                e_var name => cli_class_of_app name a,
                _ => Option.none,
            },
        _ => Option.none,
    }

def cli_class_is_option (c : Cli.TypeClass) : Bool :=
    match c {
        Cli.TypeClass.tc_option_string => true,
        Cli.TypeClass.tc_option_i64 => true,
        _ => false,
    }

def cli_class_is_list (c : Cli.TypeClass) : Bool :=
    match c { Cli.TypeClass.tc_list_string => true, _ => false }

def cli_class_is_i64 (c : Cli.TypeClass) : Bool :=
    match c {
        Cli.TypeClass.tc_i64 => true,
        Cli.TypeClass.tc_option_i64 => true,
        _ => false,
    }

def cli_class_is_bool (c : Cli.TypeClass) : Bool :=
    match c { Cli.TypeClass.tc_bool => true, _ => false }

// ─── Attribute/name mapping ───────────────────────────────────────────

def cli_kind_name (k : Cli.ArgKind) : String :=
    match k {
        Cli.ArgKind.arg_flag => "arg",
        Cli.ArgKind.arg_option => "opt",
        Cli.ArgKind.arg_positional => "pos",
    }

def cli_is_positional (k : Cli.ArgKind) : Bool :=
    match k { Cli.ArgKind.arg_positional => true, _ => false }

/// Which kind a field is:
/// - `#[arg]` / `#[opt]` / `#[pos]` when present;
/// - otherwise, for a `struct` (where field attributes cannot be carried),
///   `Bool` -> flag and everything else -> positional;
/// - otherwise positional (the historical unannotated form).
def cli_field_kind (struct_form : Bool) (f : FieldInfo) : Cli.ArgKind :=
    let attrs : List String := cli_field_attrs f in
    if Cli.attr_has "arg" attrs then Cli.ArgKind.arg_flag
    else if Cli.attr_has "opt" attrs then Cli.ArgKind.arg_option
    else if Cli.attr_has "pos" attrs then Cli.ArgKind.arg_positional
    else if struct_form then
        match cli_type_class (cli_field_typ f) {
            Option.none => Cli.ArgKind.arg_positional,
            Option.some c => if cli_class_is_bool c then Cli.ArgKind.arg_flag else Cli.ArgKind.arg_positional,
        }
    else Cli.ArgKind.arg_positional

def cli_attr_value (k : Cli.ArgKind) (key : String) (f : FieldInfo) : Option String :=
    Cli.attr_arg (cli_kind_name k) key (cli_field_attrs f)

def cli_first_char (s : String) : String :=
    if String.is_empty s then "" else String.slice s 0 1

def cli_long (k : Cli.ArgKind) (f : FieldInfo) : String :=
    match cli_attr_value k "long" f {
        Option.some s => s,
        Option.none => Cli.kebab (cli_field_name f),
    }

def cli_short (k : Cli.ArgKind) (f : FieldInfo) : String :=
    if Cli.attr_has "no_short" (cli_field_attrs f) then ""
    else match cli_attr_value k "short" f {
        Option.some s => s,
        Option.none => if cli_is_positional k then "" else cli_first_char (cli_long k f),
    }

def cli_help (k : Cli.ArgKind) (f : FieldInfo) : String :=
    Option.get_or_default "" (cli_attr_value k "help" f)

def cli_value_name (k : Cli.ArgKind) (f : FieldInfo) : String :=
    Option.get_or_default "VALUE" (cli_attr_value k "value_name" f)

def cli_has_default (f : FieldInfo) : Bool :=
    match cli_field_default f {
        Option.some _ => true,
        Option.none => false,
    }

/// Help-text rendering only; numeric/bool defaults are applied by the
/// decoder from the original `Expr` and are deliberately not stringified
/// here (the meta evaluator has no `I64.to_string`).
def cli_default_string (f : FieldInfo) : String :=
    match cli_field_default f {
        Option.some d =>
            match d {
                e_str s => s,
                _ => "",
            },
        Option.none => "",
    }

def cli_required (k : Cli.ArgKind) (f : FieldInfo) : Bool :=
    match k {
        Cli.ArgKind.arg_flag => false,
        _ =>
            if cli_has_default f then false
            else match cli_type_class (cli_field_typ f) {
                Option.none => true,
                Option.some c => if cli_class_is_option c || cli_class_is_list c then false else true,
            },
    }

def cli_multiple (f : FieldInfo) : Bool :=
    match cli_type_class (cli_field_typ f) {
        Option.none => false,
        Option.some c => cli_class_is_list c,
    }

def cli_value_type_expr (f : FieldInfo) : Expr :=
    match cli_type_class (cli_field_typ f) {
        Option.none => e_var "Cli.ArgValueType.arg_string",
        Option.some c => if cli_class_is_i64 c then e_var "Cli.ArgValueType.arg_i64" else e_var "Cli.ArgValueType.arg_string",
    }

// ─── Expr construction helpers ────────────────────────────────────────

def cli_app1 (f : String) (a : Expr) : Expr := e_app (e_var f) a
def cli_app2 (f : String) (a : Expr) (b : Expr) : Expr := e_app (cli_app1 f a) b
def cli_app3 (f : String) (a : Expr) (b : Expr) (c : Expr) : Expr := e_app (cli_app2 f a b) c
def cli_app4 (f : String) (a : Expr) (b : Expr) (c : Expr) (d : Expr) : Expr := e_app (cli_app3 f a b c) d
def cli_app5 (f : String) (a : Expr) (b : Expr) (c : Expr) (d : Expr) (e : Expr) : Expr := e_app (cli_app4 f a b c d) e
def cli_app6 (f : String) (a : Expr) (b : Expr) (c : Expr) (d : Expr) (e : Expr) (g : Expr) : Expr := e_app (cli_app5 f a b c d e) g
def cli_app7 (f : String) (a : Expr) (b : Expr) (c : Expr) (d : Expr) (e : Expr) (g : Expr) (h : Expr) : Expr := e_app (cli_app6 f a b c d e g) h
def cli_app8 (f : String) (a : Expr) (b : Expr) (c : Expr) (d : Expr) (e : Expr) (g : Expr) (h : Expr) (i : Expr) : Expr := e_app (cli_app7 f a b c d e g h) i
def cli_app9 (f : String) (a : Expr) (b : Expr) (c : Expr) (d : Expr) (e : Expr) (g : Expr) (h : Expr) (i : Expr) (j : Expr) : Expr := e_app (cli_app8 f a b c d e g h i) j

#[partial]
def cli_expr_list (xs : List Expr) (nil : Expr) : Expr :=
    match xs {
        List.empty => nil,
        List.cons x rest => e_ctor "List.cons" [x, cli_expr_list rest nil],
    }

// ─── Spec construction ────────────────────────────────────────────────

def cli_arg_spec_expr (struct_form : Bool) (f : FieldInfo) : Expr :=
    let k : Cli.ArgKind := cli_field_kind struct_form f in
    let long : String := cli_long k f in
    let short : String := cli_short k f in
    let help : String := cli_help k f in
    match k {
        Cli.ArgKind.arg_flag =>
            cli_app3 "Cli.flag" (e_str long) (e_str short) (e_str help),
        Cli.ArgKind.arg_option =>
            cli_app9 "Cli.option_spec" (cli_value_type_expr f) (e_str long) (e_str short)
                (e_str (cli_value_name k f)) (e_bool (cli_required k f))
                (e_bool (cli_has_default f)) (e_str (cli_default_string f))
                (e_bool (cli_multiple f)) (e_str help),
        Cli.ArgKind.arg_positional =>
            cli_app7 "Cli.positional_spec" (cli_value_type_expr f) (e_str long)
                (e_bool (cli_required k f)) (e_bool (cli_has_default f))
                (e_str (cli_default_string f)) (e_bool (cli_multiple f)) (e_str help),
    }

def cli_arg_specs (struct_form : Bool) (fields : List FieldInfo) : List Expr :=
    List.map (fn f => cli_arg_spec_expr struct_form f) fields

def cli_command_expr (name : String) : Expr :=
    cli_app2 "Cli.command" (e_str name) (e_str "")

def cli_ctor_spec_expr (struct_form : Bool) (command_name : String) (fields : List FieldInfo) : Expr :=
    let args : Expr := cli_expr_list (cli_arg_specs struct_form fields) (e_var "Cli.no_args") in
    e_app (cli_app1 "Cli.with_args" args) (cli_command_expr command_name)

def cli_sub_specs (ctors : List CtorInfo) : List Expr :=
    match ctors {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                ctor_info cname fields =>
                    List.cons (cli_ctor_spec_expr false (Cli.kebab cname) fields) (cli_sub_specs rest),
            },
    }

def cli_spec_expr (type_name : String) (ctors : List CtorInfo) (struct_form : Bool) (single_command : Bool) : Expr :=
    if single_command then
        match ctors {
            List.empty => cli_command_expr (Cli.kebab type_name),
            List.cons c _ =>
                match c {
                    ctor_info cname fields => cli_ctor_spec_expr struct_form (Cli.kebab type_name) fields,
                },
        }
    else
        let subs : Expr := cli_expr_list (cli_sub_specs ctors) (e_var "Cli.no_subcommands") in
        e_app (cli_app1 "Cli.with_subcommands" subs) (cli_command_expr (Cli.kebab type_name))

// ─── Decode construction ──────────────────────────────────────────────

def cli_required_option_expr (accessor : String) (long : String) (default : Option Expr) (p : Expr) : Expr :=
    let base : Expr := cli_app2 accessor (e_str long) p in
    match default {
        Option.none => base,
        Option.some d => e_if (cli_app2 "Cli.has_option" (e_str long) p) base d,
    }

def cli_optional_option_expr (accessor : String) (long : String) (default : Option Expr) (p : Expr) : Expr :=
    let base : Expr := cli_app2 accessor (e_str long) p in
    match default {
        Option.none => base,
        Option.some d => e_if (cli_app2 "Cli.has_option" (e_str long) p) base d,
    }

def cli_option_expr (cls : Option Cli.TypeClass) (long : String) (default : Option Expr) (p : Expr) : Expr :=
    match cls {
        Option.none => e_str "",
        Option.some c =>
            match c {
                Cli.TypeClass.tc_string => cli_required_option_expr "Cli.required_option" long default p,
                Cli.TypeClass.tc_i64 => cli_required_option_expr "Cli.required_option_i64" long default p,
                Cli.TypeClass.tc_option_string => cli_optional_option_expr "Cli.option_value" long default p,
                Cli.TypeClass.tc_option_i64 => cli_optional_option_expr "Cli.option_value_i64" long default p,
                Cli.TypeClass.tc_list_string => cli_optional_option_expr "Cli.option_values" long default p,
                Cli.TypeClass.tc_bool => e_str "",
            },
    }

def cli_required_positional_expr (accessor : String) (idx : I64) (default : Option Expr) (p : Expr) : Expr :=
    let base : Expr := cli_app2 accessor (e_int idx) p in
    match default {
        Option.none => base,
        Option.some d => e_if (cli_app2 "Cli.has_positional" (e_int idx) p) base d,
    }

def cli_positional_expr (cls : Option Cli.TypeClass) (idx : I64) (default : Option Expr) (p : Expr) : Expr :=
    match cls {
        Option.none => e_str "",
        Option.some c =>
            match c {
                Cli.TypeClass.tc_string => cli_required_positional_expr "Cli.required_positional" idx default p,
                Cli.TypeClass.tc_i64 => cli_required_positional_expr "Cli.required_positional_i64" idx default p,
                Cli.TypeClass.tc_option_string => cli_required_positional_expr "Cli.positional_value" idx default p,
                Cli.TypeClass.tc_option_i64 => cli_required_positional_expr "Cli.positional_value_i64" idx default p,
                Cli.TypeClass.tc_list_string => cli_required_positional_expr "Cli.positional_values" idx default p,
                Cli.TypeClass.tc_bool => e_str "",
            },
    }

def cli_field_expr (struct_form : Bool) (f : FieldInfo) (pos_index : I64) : Expr :=
    let k : Cli.ArgKind := cli_field_kind struct_form f in
    let long : String := cli_long k f in
    let p : Expr := e_var "p" in
    let cls : Option Cli.TypeClass := cli_type_class (cli_field_typ f) in
    let default : Option Expr := cli_field_default f in
    match k {
        Cli.ArgKind.arg_flag =>
            let base : Expr := cli_app2 "Cli.flag_set" (e_str long) p in
            match default {
                Option.none => base,
                Option.some d => e_if base (e_bool true) d,
            },
        Cli.ArgKind.arg_option => cli_option_expr cls long default p,
        Cli.ArgKind.arg_positional => cli_positional_expr cls pos_index default p,
    }

#[partial]
def cli_field_exprs (struct_form : Bool) (fields : List FieldInfo) (pos_index : I64) : Pair (List Expr) I64 :=
    match fields {
        List.empty => Pair.pair List.empty pos_index,
        List.cons f rest =>
            let k : Cli.ArgKind := cli_field_kind struct_form f in
            let next : I64 :=
                if cli_is_positional k && Bool.not (cli_multiple f)
                then I64.add pos_index 1
                else pos_index in
            match cli_field_exprs struct_form rest next {
                Pair.pair exprs final_index =>
                    Pair.pair (List.cons (cli_field_expr struct_form f pos_index) exprs) final_index,
            },
    }

def cli_ctor_decode_expr (type_name : String) (ctor_name : String) (struct_form : Bool) (fields : List FieldInfo) : Expr :=
    match cli_field_exprs struct_form fields 0 {
        Pair.pair exprs _ =>
            let applied : Expr := e_ctor (String.concat type_name (String.concat "." ctor_name)) exprs in
            e_app (e_var "Result.ok") applied,
    }

#[partial]
def cli_decode_chain (type_name : String) (ctors : List CtorInfo) (rest : Expr) : Expr :=
    match ctors {
        List.empty => rest,
        List.cons c tail =>
            match c {
                ctor_info cname fields =>
                    e_if (cli_app2 "String.beq" (cli_app1 "Cli.command_name" (e_var "p")) (e_str (Cli.kebab cname)))
                         (cli_ctor_decode_expr type_name cname false fields)
                         (cli_decode_chain type_name tail rest),
            },
    }

def cli_decode_expr (type_name : String) (ctors : List CtorInfo) (struct_form : Bool) (single_command : Bool) : Expr :=
    if single_command then
        match ctors {
            List.empty => e_app (e_var "Result.err") (e_str "missing subcommand"),
            List.cons c _ =>
                match c {
                    ctor_info cname fields => cli_ctor_decode_expr type_name cname struct_form fields,
                },
        }
    else
        let unknown : Expr :=
            cli_app1 "Result.err"
                (cli_app2 "String.concat" (e_str "unknown subcommand: ") (cli_app1 "Cli.command_name" (e_var "p"))) in
        cli_decode_chain type_name ctors unknown

// ─── Validation ───────────────────────────────────────────────────────

def cli_bad_field (struct_form : Bool) (ctor_display : String) (f : FieldInfo) : Option String :=
    let k : Cli.ArgKind := cli_field_kind struct_form f in
    let name : String := cli_field_name f in
    match k {
        Cli.ArgKind.arg_flag =>
            match cli_type_class (cli_field_typ f) {
                Option.some c =>
                    if cli_class_is_bool c then Option.none
                    else Option.some (String.concat_all ["#[derive Cli]: `", ctor_display, "`'s field `", name, "` is a flag but is not `Bool`"]),
                Option.none =>
                    Option.some (String.concat_all ["#[derive Cli]: `", ctor_display, "`'s field `", name, "` is a flag but its type is not supported"]),
            },
        _ =>
            match cli_type_class (cli_field_typ f) {
                Option.none =>
                    Option.some (String.concat_all ["#[derive Cli]: `", ctor_display, "`'s field `", name, "` has an unsupported type (expected String, I64, Option String/I64, or List String)"]),
                Option.some c =>
                    if cli_class_is_bool c
                    then Option.some (String.concat_all ["#[derive Cli]: `", ctor_display, "`'s Bool field `", name, "` must be annotated `#[arg]`"])
                    else if Bool.not (cli_required k f) && Bool.not (cli_has_default f) && Bool.not (cli_class_is_option c) && Bool.not (cli_class_is_list c)
                         then Option.some (String.concat_all ["#[derive Cli]: `", ctor_display, "`'s field `", name, "` is optional but has no default; use Option, List, or a `:=` default"])
                         else Option.none,
            },
    }

#[partial]
def cli_bad_fields (struct_form : Bool) (ctor_display : String) (fields : List FieldInfo) : Option String :=
    match fields {
        List.empty => Option.none,
        List.cons f rest =>
            match cli_bad_field struct_form ctor_display f {
                Option.some msg => Option.some msg,
                Option.none => cli_bad_fields struct_form ctor_display rest,
            },
    }

#[partial]
def cli_bad_ctors (struct_form : Bool) (ctors : List CtorInfo) : Option String :=
    match ctors {
        List.empty => Option.none,
        List.cons c rest =>
            match c {
                ctor_info cname fields =>
                    match cli_bad_fields struct_form cname fields {
                        Option.some msg => Option.some msg,
                        Option.none => cli_bad_ctors struct_form rest,
                    },
            },
    }

#[partial]
def cli_short_conflict (short : String) (long : String) (struct_form : Bool) (fields : List FieldInfo) : Option String :=
    match fields {
        List.empty => Option.none,
        List.cons f rest =>
            let k : Cli.ArgKind := cli_field_kind struct_form f in
            let s : String := if cli_is_positional k then "" else cli_short k f in
            if Bool.not (String.is_empty s) && String.beq s short && Bool.not (String.beq (cli_field_name f) long)
            then Option.some (String.concat_all ["#[derive Cli]: short flag `-", s, "` is used by both `", long, "` and `", cli_field_name f, "`; add `#[no_short]` to one"])
            else cli_short_conflict short long struct_form rest,
    }

#[partial]
def cli_short_conflicts (struct_form : Bool) (fields : List FieldInfo) : Option String :=
    match fields {
        List.empty => Option.none,
        List.cons f rest =>
            let k : Cli.ArgKind := cli_field_kind struct_form f in
            let s : String := if cli_is_positional k then "" else cli_short k f in
            if String.is_empty s
            then cli_short_conflicts struct_form rest
            else match cli_short_conflict s (cli_field_name f) struct_form rest {
                Option.some msg => Option.some msg,
                Option.none => cli_short_conflicts struct_form rest,
            },
    }

#[partial]
def cli_short_conflicts_all (struct_form : Bool) (ctors : List CtorInfo) : Option String :=
    match ctors {
        List.empty => Option.none,
        List.cons c rest =>
            match c {
                ctor_info _cname fields =>
                    match cli_short_conflicts struct_form fields {
                        Option.some msg => Option.some msg,
                        Option.none => cli_short_conflicts_all struct_form rest,
                    },
            },
    }

#[partial]
def cli_check_positionals
        (struct_form : Bool) (ctor_display : String) (fields : List FieldInfo)
        (seen_optional : Bool) (seen_multiple : Bool) : Option String :=
    match fields {
        List.empty => Option.none,
        List.cons f rest =>
            let k : Cli.ArgKind := cli_field_kind struct_form f in
            if Bool.not (cli_is_positional k)
            then cli_check_positionals struct_form ctor_display rest seen_optional seen_multiple
            else
                let name : String := cli_field_name f in
                if seen_multiple
                then Option.some (String.concat_all ["#[derive Cli]: `", ctor_display, "`'s `List String` positional `", name, "` must be last"])
                else if cli_multiple f
                     then cli_check_positionals struct_form ctor_display rest seen_optional true
                     else if Bool.not (cli_required k f)
                          then cli_check_positionals struct_form ctor_display rest true seen_multiple
                          else if seen_optional
                               then Option.some (String.concat_all ["#[derive Cli]: `", ctor_display, "`'s required positional `", name, "` follows an optional one"])
                               else cli_check_positionals struct_form ctor_display rest false seen_multiple,
    }

#[partial]
def cli_check_all_positionals (struct_form : Bool) (ctors : List CtorInfo) : Option String :=
    match ctors {
        List.empty => Option.none,
        List.cons c rest =>
            match c {
                ctor_info cname fields =>
                    match cli_check_positionals struct_form cname fields false false {
                        Option.some msg => Option.some msg,
                        Option.none => cli_check_all_positionals struct_form rest,
                    },
            },
    }

// ─── Entry point ──────────────────────────────────────────────────────

def cli_parse_expr (type_name : String) : Expr :=
    let lower : String := String.to_lowercase type_name in
    let call : Expr := cli_app2 "Cli.parse" (e_var (String.concat "spec_" lower)) (e_var "args") in
    e_match call [
        match_arm "parse_ok" ["p"] (cli_app1 (String.concat "decode_" lower) (e_var "p")),
        match_arm "parse_help" ["text"] (cli_app1 "Result.err" (e_var "text")),
        match_arm "parse_version" ["text"] (cli_app1 "Result.err" (e_var "text")),
        match_arm "parse_err" ["msg"] (cli_app1 "Result.err" (e_var "msg")),
    ]

/// `#[derive Cli] type Command { ... }` (or, called directly,
/// `derive_cli! Command`) generates:
///
///   - `spec_<lower> : Cli.CommandSpec`
///   - `decode_<lower> : Cli.Parsed -> Result String T`
///   - `parse_<lower> : List String -> Result String T`
///
/// Every shape the mapping cannot express is a `Decl.d_error` naming the
/// constructor/field, so a mistake is a derive-time error rather than
/// generated code that fails with an unrelated type error.
pub def derive_cli_meta (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            match ctors {
                List.empty =>
                    [d_error (String.concat_all ["#[derive Cli]: `", type_name, "` has no constructors"])],
                List.cons first rest =>
                    let is_mk : Bool :=
                        match first {
                            ctor_info cname _fields => String.beq cname "mk",
                        } in
                    let struct_form : Bool := is_mk && List.is_empty rest in
                    let single_command : Bool := List.is_empty rest in
                    let lower : String := String.to_lowercase type_name in
                    match cli_bad_ctors struct_form ctors {
                        Option.some msg => [d_error msg],
                        Option.none =>
                            match cli_check_all_positionals struct_form ctors {
                                Option.some msg => [d_error msg],
                                Option.none =>
                                    match cli_short_conflicts_all struct_form ctors {
                                        Option.some msg => [d_error msg],
                                        Option.none =>
                                            let spec_expr : Expr := cli_spec_expr type_name ctors struct_form single_command in
                                            let decode_expr : Expr := cli_decode_expr type_name ctors struct_form single_command in
                                            let parse_expr : Expr := cli_parse_expr type_name in
                                            [
                                                d_def (String.concat "spec_" lower) List.empty (e_var "Cli.CommandSpec") spec_expr,
                                                d_def (String.concat "decode_" lower)
                                                    [meta_param "p" (e_var "Cli.Parsed")]
                                                    (cli_app2 "Result" (e_var "String") (e_var type_name))
                                                    decode_expr,
                                                d_def (String.concat "parse_" lower)
                                                    [meta_param "args" (e_app (e_var "List") (e_var "String"))]
                                                    (cli_app2 "Result" (e_var "String") (e_var type_name))
                                                    parse_expr,
                                            ],
                                    },
                            },
                    },
            },
    }

// Registers the `Cli` derive target: any module that brings this macro
// into scope (`use clap.args {derive_cli}` or a superset) can write
// `#[derive Cli]` on its command types — the old `#[derive_cli]`
// attribute special case is gone. The macro itself stays
// package-private (a `defmacro` has no visibility prefix), same as
// before this annotation existed.
#[derive_handler Cli]
defmacro derive_cli T := decls {
    reflect_type_info! T derive_cli_meta
}

// --- Tests ---

// NOTE: comparisons below check `rest`/`List String` contents via
// `List.length` plus `Cli.nth` rather than `==`/generic `BEq (List A)` —
// the same runtime dispatch issue noted in `lang/toml.mo` for custom types
// turns out to affect `List String` too (`==` on a `List String` produced
// this way evaluates to the list itself instead of a `Bool` here). Concrete
// `String`/`Bool` `==` is unaffected and used freely. Match-arm patterns
// also only bind flat identifiers (no nested constructor sub-patterns like
// `List.cons hd List.empty`), which is the other reason for a helper here.

#[partial]
def Cli.nth (n : I64) (l : List String) : String :=
    match l {
        List.cons hd tl => if n == 0 then hd else Cli.nth (n - 1) tl,
        List.empty => "",
    }

#[test]
def test_take_flag_found : Bool :=
    match Cli.take_flag "verbose" "" ["--verbose", "file.mo"] {
        Cli.FlagResult.flag_result found rest =>
            found == true && List.length rest == 1 && Cli.nth 0 rest == "file.mo",
    }

#[test]
def test_take_flag_not_found : Bool :=
    match Cli.take_flag "verbose" "" ["file.mo"] {
        Cli.FlagResult.flag_result found rest =>
            found == false && List.length rest == 1 && Cli.nth 0 rest == "file.mo",
    }

#[test]
def test_take_flag_short_form : Bool :=
    match Cli.take_flag "verbose" "v" ["-v", "file.mo"] {
        Cli.FlagResult.flag_result found rest =>
            found == true && List.length rest == 1 && Cli.nth 0 rest == "file.mo",
    }

#[test]
def test_take_flag_position_independent : Bool :=
    match Cli.take_flag "v" "" ["a", "--v", "b"] {
        Cli.FlagResult.flag_result found rest =>
            found == true
                && List.length rest == 2
                && Cli.nth 0 rest == "a"
                && Cli.nth 1 rest == "b",
    }

#[test]
def test_take_flag_empty_args : Bool :=
    match Cli.take_flag "v" "" [] {
        Cli.FlagResult.flag_result found rest =>
            found == false,
    }

#[test]
def test_take_positional_some : Bool :=
    match Cli.take_positional ["a", "b"] {
        Cli.PosResult.pos_result value rest =>
            match value {
                Option.some v => v == "a" && List.length rest == 1 && Cli.nth 0 rest == "b",
                Option.none => false,
            },
    }

#[test]
def test_take_positional_none : Bool :=
    match Cli.take_positional [] {
        Cli.PosResult.pos_result value rest =>
            match value {
                Option.none => true,
                Option.some _ => false,
            },
    }

#[test]
def test_take_opt_found : Bool :=
    match Cli.take_opt "output" "" "source" ["--output", "out", "a.mo"] {
        Cli.OptResult.opt_result value rest =>
            value == "out" && List.length rest == 1 && Cli.nth 0 rest == "a.mo",
    }

#[test]
def test_take_opt_short_form : Bool :=
    match Cli.take_opt "output" "o" "source" ["-o", "out", "a.mo"] {
        Cli.OptResult.opt_result value rest =>
            value == "out" && List.length rest == 1 && Cli.nth 0 rest == "a.mo",
    }

#[test]
def test_take_opt_default_when_absent : Bool :=
    match Cli.take_opt "output" "" "source" ["a.mo"] {
        Cli.OptResult.opt_result value rest =>
            value == "source" && List.length rest == 1 && Cli.nth 0 rest == "a.mo",
    }

#[test]
def test_take_opt_default_when_missing_value : Bool :=
    match Cli.take_opt "output" "" "source" ["a.mo", "--output"] {
        Cli.OptResult.opt_result value rest =>
            value == "source",
    }
