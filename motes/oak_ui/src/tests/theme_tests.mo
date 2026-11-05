/// Theme tokens and the stylesheet's contract with them.

use lib::theme {Ui.Theme, Ui.Theme.light, Ui.Theme.dark, Ui.Theme.tokens, Ui.Theme.css_vars, Ui.Theme.css_auto}
use lib::css {Ui.css_all}

// ─── Scanning `var(--oak-NAME)` references out of the sheet ───

#[terminating]
def name_end (s : String) (i : I64) : I64 :=
    match String.get s i {
        Option.none => i,
        Option.some b => if U8.beq b 41u8 || U8.beq b 44u8 then i else name_end s (i + 1),
    }

#[terminating]
def var_names (s : String) (i : I64) (acc : List String) : List String :=
    if I64.lt (String.length s) (i + 10)
    then acc
    else if String.beq (String.slice s i 10) "var(--oak-"
    then
        let start : I64 := i + 10 in
        let stop : I64 := name_end s start in
        var_names s stop (List.cons (String.slice s start (stop - start)) acc)
    else var_names s (i + 1) acc

#[terminating]
def token_defined (name : String) (tokens : List (Pair String String)) : Bool :=
    match tokens {
        List.empty => false,
        List.cons p rest =>
            match p { Pair.pair k _ => if String.beq k name then true else token_defined name rest },
    }

#[terminating]
def undefined_vars (names : List String) (tokens : List (Pair String String)) : List String :=
    match names {
        List.empty => List.empty,
        List.cons n rest =>
            if token_defined n tokens
            then undefined_vars rest tokens
            else List.cons n (undefined_vars rest tokens),
    }

#[test]
def test_sheet_references_only_theme_tokens : Bool :=
    let names : List String := var_names Ui.css_all 0 List.empty in
    Bool.not (List.is_empty names)
        && List.is_empty (undefined_vars names (Ui.Theme.tokens Ui.Theme.light))

#[test]
def test_css_vars_rule_shape : Bool :=
    let css : String := Ui.Theme.css_vars ":root" Ui.Theme.light in
    String.starts_with ":root { --oak-bg: #f8fafc; --oak-surface: #ffffff;" css
        && String.ends_with css " }\n"

#[test]
def test_css_auto_has_both_schemes : Bool :=
    let css : String := Ui.Theme.css_auto Ui.Theme.light Ui.Theme.dark in
    String.contains css "@media (prefers-color-scheme: dark)"
        && String.contains css "[data-theme=\"dark\"] { --oak-bg: #0d1117;"
        && String.contains css ":root, [data-theme=\"light\"] { --oak-bg: #f8fafc;"

#[test]
def test_theme_override_is_a_record_update : Bool :=
    let brand : Ui.Theme := { Ui.Theme.light with primary := "#7c3aed" } in
    String.contains (Ui.Theme.css_vars ":root" brand) "--oak-primary: #7c3aed;"
