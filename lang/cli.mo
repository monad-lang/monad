/// Small runtime helper library for CLI argument parsing over `List String`.
///
/// Used two ways:
/// - by hand, from `lang/main.mo` (which stays free of any macro/attribute
///   syntax so the self-hosted parser/typechecker — which doesn't know
///   about `#[derive_cli]` — can still parse it; see `lang/main.mo`'s own
///   header comment and the self-hosted parse/scope/typecheck tests in
///   `lang/tests/`);
/// - by generated code, from `#[derive_cli]`-annotated types — see
///   `derive_cli_meta`/`derive_cli` below, and the demo in
///   `lang/tests/cli_derive_tests.mo`.
///
/// Each operation returns a dedicated, non-generic result type
/// (`Cli.FlagResult`/`Cli.PosResult`/`Cli.OptResult`) rather than a generic
/// `Pair`/tuple. That's deliberate, not incidental: reusing `Pair A B` here
/// tripped a real type-checker gap where nested `match`es over types that
/// share a type-parameter name with `Result A E` (as `Pair`/`Option` both
/// do — everyone names their first param `A`) lose track of which `A` is
/// which. Dedicated concrete types sidestep it entirely — see the longer
/// note on `derive_cli_meta` below.

use std.list {length, filter, any}
use init.meta {TypeInfo, CtorInfo, FieldInfo, Expr, Decl}
open List {length}
open TypeInfo {type_info}
open CtorInfo {ctor_info}
open FieldInfo {field_info}
open Expr {e_var, e_str, e_app, e_if, e_match, e_ctor}
open MatchArm {match_arm}
open Param {meta_param}
open Decl {d_def, d_error}

type Cli.FlagResult {
    flag_result (found : Bool) (rest : List String),
}

type Cli.PosResult {
    pos_result (value : Option String) (rest : List String),
}

type Cli.OptResult {
    opt_result (value : String) (rest : List String),
}

/// Scan `args` for `--<long>` or `-<short>`, removing the first occurrence
/// if present. Pass `""` for `short` to only recognize the long form. Flags
/// are position-independent — this finds the flag wherever it is and
/// returns the remaining args with it stripped out, order preserved.
def Cli.take_flag (long : String) (short : String) (args : List String) : Cli.FlagResult :=
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
def Cli.take_positional (args : List String) : Cli.PosResult :=
    match args {
        List.empty => Cli.PosResult.pos_result Option.none List.empty,
        List.cons hd tl => Cli.PosResult.pos_result (Option.some hd) tl,
    }

/// Scan `args` for `--<long> <value>`/`-<short> <value>`, removing both
/// tokens if present and returning `value`; falls back to `default` if
/// absent. Pass `""` for `short` to only recognize the long form.
/// (v1 scope: space-separated `<flag> <value>` only — no `--<long>=<value>`
/// combined form, see `lang/cli.mo`'s plan note on `String.split` not
/// existing yet.)
def Cli.take_opt (long : String) (short : String) (default : String) (args : List String) : Cli.OptResult :=
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

// --- #[derive_cli]: reflection-as-data metaprogramming ---
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
    match f { field_info name typ attrs => name }

def cli_field_typ (f : FieldInfo) : Expr :=
    match f { field_info name typ attrs => typ }

def cli_field_attrs (f : FieldInfo) : List String :=
    match f { field_info name typ attrs => attrs }

def cli_has_arg_attr (f : FieldInfo) : Bool :=
    List.any (fn a => a == "arg") (cli_field_attrs f)

def cli_is_bool_typ (t : Expr) : Bool :=
    match t {
        e_var name => name == "Bool",
        _ => false,
    }

/// `#[arg]` used on a non-`Bool` field is a hard error (v1 only supports
/// boolean flags) — checked across every field of every constructor
/// before any code is generated, so the FIRST violation (in constructor/
/// field declaration order) is what gets reported, matching the former
/// Rust generator's fail-fast behaviour.
def cli_bad_arg_field_in_ctor (ctor_display : String) (fields : List FieldInfo) : Option String :=
    match fields {
        empty => Option.none,
        cons f tail =>
            if cli_has_arg_attr f && Bool.not (cli_is_bool_typ (cli_field_typ f))
                then Option.some
                    (String.concat_all
                        ["#[derive_cli]: `", ctor_display, "`'s field `", cli_field_name f,
                         "` is annotated `#[arg]` but is not `Bool` — only boolean flags are supported (v1)"])
                else cli_bad_arg_field_in_ctor ctor_display tail,
    }

def cli_bad_arg_field (ctors : List CtorInfo) : Option String :=
    match ctors {
        empty => Option.none,
        cons c tail =>
            match c {
                ctor_info cname fields =>
                    match cli_bad_arg_field_in_ctor cname fields {
                        some msg => Option.some msg,
                        none => cli_bad_arg_field tail,
                    }
            },
    }

/// `match Cli.take_flag "<field>" "" __cli_rest { flag_result <field>
/// __cli_rest => inner }` — binds the flag's own `Bool` value directly
/// under the field's own declared name.
def cli_wrap_flag (field_name : String) (inner : Expr) : Expr :=
    e_match
        (e_app (e_app (e_app (e_var "Cli.take_flag") (e_str field_name)) (e_str "")) (e_var "__cli_rest"))
        [match_arm "flag_result" [field_name, "__cli_rest"] inner]

/// `match Cli.take_positional __cli_rest { pos_result __cli_opt __cli_rest
/// => match __cli_opt { some <field> => inner, none => Result.err "..." }
/// }`
def cli_wrap_positional (ctor_display : String) (field_name : String) (inner : Expr) : Expr :=
    e_match (e_app (e_var "Cli.take_positional") (e_var "__cli_rest"))
        [match_arm "pos_result" ["__cli_opt", "__cli_rest"]
            (e_match (e_var "__cli_opt")
                [match_arm "some" [field_name] inner,
                 match_arm "none" []
                     (e_app (e_var "Result.err")
                         (e_str (String.concat_all
                             [ctor_display, ": missing required argument '", field_name, "'"])))])]

def cli_wrap_flags (fields : List FieldInfo) (inner : Expr) : Expr :=
    match fields {
        empty => inner,
        cons f tail => cli_wrap_flag (cli_field_name f) (cli_wrap_flags tail inner),
    }

def cli_wrap_positionals (ctor_display : String) (fields : List FieldInfo) (inner : Expr) : Expr :=
    match fields {
        empty => inner,
        cons f tail => cli_wrap_positional ctor_display (cli_field_name f) (cli_wrap_positionals ctor_display tail inner),
    }

/// One constructor's whole parser body: peel all `#[arg]` flags first (in
/// declared order — flags are position-independent in real argv), then
/// all positionals (in declared order, from whatever argv is left), then
/// apply the constructor to every field by its own name, in ORIGINAL
/// declared order, wrapped in `Result.ok` — built as `e_app (e_var
/// "Result.ok") applied`, ordinary function application of a QUALIFIED
/// `Var` reference (reified through `meta_reflect.rs`'s already-general
/// `e_app`/`e_var` handling), not a raw pre-resolved `Con` node. That
/// distinction is load-bearing, not stylistic: the type checker only
/// correctly instantiates `Result`'s type parameters through the former —
/// this is the "narrow gap" a zero-arg constructor wrapped in `Result.ok`
/// (`Command6.help6` in `core/src/eval/derive_cli_test.rs`'s regression
/// test) used to trip when the original Rust generator built it as a raw
/// `Con` instead.
def cli_build_ctor_parser (type_name : String) (ctor_name : String) (fields : List FieldInfo) : Expr :=
    let flags := List.filter cli_has_arg_attr fields in
    let positionals := List.filter (fn f => Bool.not (cli_has_arg_attr f)) fields in
    let ordered_names := List.map cli_field_name fields in
    let applied := e_ctor (String.concat type_name (String.concat "." ctor_name)) (List.map e_var ordered_names) in
    let inner := e_app (e_var "Result.ok") applied in
    cli_wrap_flags flags (cli_wrap_positionals ctor_name positionals inner)

/// `if String.beq __cli_hd "<ctor>" then <ctor's parser> else rest` — one
/// `if`-branch per constructor, tried in declared order.
def cli_dispatch_ctor (type_name : String) (ctor : CtorInfo) (rest : Expr) : Expr :=
    match ctor {
        ctor_info ctor_name fields =>
            e_if (e_app (e_app (e_var "String.beq") (e_var "__cli_hd")) (e_str ctor_name))
                 (cli_build_ctor_parser type_name ctor_name fields)
                 rest
    }

def cli_dispatch_chain (type_name : String) (ctors : List CtorInfo) : Expr :=
    match ctors {
        empty =>
            e_app (e_var "Result.err")
                (e_app (e_app (e_var "String.concat") (e_str "unknown subcommand: ")) (e_var "__cli_hd")),
        cons c tail => cli_dispatch_ctor type_name c (cli_dispatch_chain type_name tail),
    }

/// `#[derive_cli] type Command { ... }` (or, called directly, `derive_cli!
/// Command`) generates `parse_<lowercased name> : List String -> Result
/// String Command`. Fails at meta-expansion time (`Decl.d_error`) if the
/// type has no constructors, or if `#[arg]` annotates a non-`Bool` field.
pub def derive_cli_meta (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            match ctors {
                empty =>
                    [d_error (String.concat_all ["#[derive_cli]: `", type_name, "` has no constructors"])],
                cons _ _ =>
                    match cli_bad_arg_field ctors {
                        some msg => [d_error msg],
                        none =>
                            let body :=
                                e_match (e_var "__cli_args")
                                    [match_arm "cons" ["__cli_hd", "__cli_rest"] (cli_dispatch_chain type_name ctors),
                                     match_arm "empty" [] (e_app (e_var "Result.err") (e_str "missing subcommand"))] in
                            [d_def
                                (String.concat "parse_" (String.to_lowercase type_name))
                                [meta_param "__cli_args" (e_app (e_var "List") (e_var "String"))]
                                (e_app (e_app (e_var "Result") (e_var "String")) (e_var type_name))
                                body]
                    },
            }
    }

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
