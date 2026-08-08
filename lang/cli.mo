/// Small runtime helper library for CLI argument parsing over `List String`.
///
/// Used two ways:
/// - by hand, from `lang/main.mo` (which stays free of any macro/attribute
///   syntax so the self-hosted parser/typechecker — which doesn't know
///   about `#[derive_cli]` — can still parse it; see `lang/main.mo`'s own
///   header comment and the self-hosted parse/scope/typecheck tests in
///   `lang/tests/`);
/// - by generated code, from `#[derive_cli]`-annotated types (see
///   `core/src/eval/derive_cli.rs`, and the demo in
///   `lang/tests/cli_derive_tests.mo`).
///
/// Each operation returns a dedicated, non-generic result type
/// (`Cli.FlagResult`/`Cli.PosResult`/`Cli.OptResult`) rather than a generic
/// `Pair`/tuple. That's deliberate, not incidental: reusing `Pair A B` here
/// tripped a real type-checker gap where nested `match`es over types that
/// share a type-parameter name with `Result A E` (as `Pair`/`Option` both
/// do — everyone names their first param `A`) lose track of which `A` is
/// which. Dedicated concrete types sidestep it entirely — see the longer
/// note in `core/src/eval/derive_cli.rs`.

use std.list {length}
open List {length}

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
