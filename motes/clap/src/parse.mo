/// The spec-driven argument parser and the `Cli.run` IO entry point.
///
/// Deliberately separate from `args.mo`'s legacy `take_*` helpers: those
/// keep their exact historical behavior (including missing-value fallback),
/// while this parser is the strict, typed one new CLIs use.
use std::list {List.length}
use std::io {IO.write_stderr}
use lib::spec {
    Cli.ArgKind, Cli.ArgSpec, Cli.ArgValue, Cli.ArgValueType, Cli.CommandSpec,
    Cli.ParseResult, Cli.Parsed, Cli.arg_value, Cli.digit_of, Cli.parse_i64,
    Cli.parsed, Cli.same_kind, Cli.subcommand_named,
}
use lib::help {Cli.help_text, Cli.usage}

// ─── Lookups ───────────────────────────────────────────────────────────

#[partial]
pub def Cli.find_long_loop (name : String) (args : List Cli.ArgSpec) : Option Cli.ArgSpec :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_positional a.kind
            then Cli.find_long_loop name rest
            else if String.beq a.long name
            then Option.some a
            else Cli.find_long_loop name rest,
    }

pub def Cli.find_long (name : String) (spec : Cli.CommandSpec) : Option Cli.ArgSpec :=
    Cli.find_long_loop name spec.args

#[partial]
pub def Cli.find_short_loop (s : String) (args : List Cli.ArgSpec) : Option Cli.ArgSpec :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_positional a.kind
            then Cli.find_short_loop s rest
            else if String.beq a.short s
            then Option.some a
            else Cli.find_short_loop s rest,
    }

pub def Cli.find_short (s : String) (spec : Cli.CommandSpec) : Option Cli.ArgSpec :=
    if String.is_empty s then Option.none else Cli.find_short_loop s spec.args

#[partial]
pub def Cli.find_positional_loop (i : I64) (args : List Cli.ArgSpec) : Option Cli.ArgSpec :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_positional a.kind
            then if I64.beq i 0 then Option.some a else Cli.find_positional_loop (I64.sub i 1) rest
            else Cli.find_positional_loop i rest,
    }

pub def Cli.find_positional_at (i : I64) (spec : Cli.CommandSpec) : Option Cli.ArgSpec :=
    if I64.lt i 0 then Option.none else Cli.find_positional_loop i spec.args

#[partial]
pub def Cli.has_option_in_loop (name : String) (xs : List Cli.ArgValue) : Bool :=
    match xs {
        List.empty => false,
        List.cons x rest => if String.beq x.name name then true else Cli.has_option_in_loop name rest,
    }

pub def Cli.has_option_in (name : String) (xs : List Cli.ArgValue) : Bool :=
    Cli.has_option_in_loop name xs

/// A token that the scanner must treat as a flag, not as a value.
pub def Cli.looks_like_flag (s : String) : Bool :=
    if String.beq s "-" then false
    else if String.starts_with "--" s then true
    else if String.starts_with "-" s then
        if I64.lt 1 (String.length s)
        then match Cli.digit_of (String.slice s 1 1) {
            Option.some _ => false,
            Option.none => true,
        }
        else false
    else false

pub def Cli.is_negative_number (s : String) : Bool :=
    I64.lt 1 (String.length s) && String.beq (String.slice s 0 1) "-" && match Cli.digit_of (String.slice s 1 1) {
        Option.some _ => true,
        Option.none => false,
    }

/// Split `name=value` at the first `=`, outside nothing (option names have
/// no quotes). `Option.none` means the token has no `=`.
#[partial]
pub def Cli.split_first_eq (s : String) : Option (Pair String String) :=
    Cli.split_first_eq_at s 0

#[partial]
pub def Cli.split_first_eq_at (s : String) (i : I64) : Option (Pair String String) :=
    if I64.lt i (String.length s) then
        if String.beq (String.slice s i 1) "="
        then Option.some (Pair.pair (String.slice s 0 i) (String.drop (I64.add i 1) s))
        else Cli.split_first_eq_at s (I64.add i 1)
    else Option.none

// ─── Scanner ───────────────────────────────────────────────────────────

#[partial]
pub def Cli.scan
        (spec : Cli.CommandSpec) (args : List String) (fenced : Bool)
        (flags : List String) (options : List Cli.ArgValue)
        (positionals : List Cli.ArgValue) (pos_index : I64) : Cli.ParseResult :=
    match args {
        List.empty => Cli.finish spec flags options positionals pos_index,
        List.cons hd tl =>
            if fenced
            then Cli.add_positional spec hd tl true flags options positionals pos_index
            else if String.beq hd "--"
            then Cli.scan spec tl true flags options positionals pos_index
            else if String.starts_with "--" hd
            then Cli.scan_long spec hd tl flags options positionals pos_index
            else if String.starts_with "-" hd
            then if String.beq hd "-" || Cli.is_negative_number hd
                 then Cli.add_positional spec hd tl false flags options positionals pos_index
                 else Cli.scan_short spec hd tl flags options positionals pos_index
            else Cli.add_positional spec hd tl false flags options positionals pos_index,
    }

#[partial]
pub def Cli.add_positional
        (spec : Cli.CommandSpec) (value : String) (rest : List String) (fenced : Bool)
        (flags : List String) (options : List Cli.ArgValue)
        (positionals : List Cli.ArgValue) (pos_index : I64) : Cli.ParseResult :=
    match Cli.find_positional_at pos_index spec {
        Option.none =>
            Cli.ParseResult.parse_err (String.concat "unexpected argument '" (String.concat value "'")),
        Option.some a =>
            let next_pos : List Cli.ArgValue := List.append positionals [Cli.arg_value a.long value] in
            let next_index : I64 := if a.multiple then pos_index else I64.add pos_index 1 in
            Cli.scan spec rest fenced flags options next_pos next_index,
    }

// ─── Long options ─────────────────────────────────────────────────────

#[partial]
pub def Cli.scan_long
        (spec : Cli.CommandSpec) (hd : String) (tl : List String)
        (flags : List String) (options : List Cli.ArgValue)
        (positionals : List Cli.ArgValue) (pos_index : I64) : Cli.ParseResult :=
    if String.beq hd "--help" && Bool.not (Cli.long_claimed spec "help")
    then Cli.ParseResult.parse_help (Cli.help_text spec)
    else if String.beq hd "--version" && Bool.not (Cli.long_claimed spec "version")
    then if String.is_empty spec.version
         then Cli.ParseResult.parse_err "unknown flag: --version"
         else Cli.ParseResult.parse_version (Cli.version_text spec)
    else
        let body : String := String.drop 2 hd in
        match Cli.split_first_eq body {
            Option.some pair =>
                match pair {
                    Pair.pair key value => Cli.apply_long_equals spec key value tl flags options positionals pos_index,
                },
            Option.none =>
                match Cli.find_long body spec {
                    Option.none => Cli.ParseResult.parse_err (String.concat "unknown flag: --" body),
                    Option.some a =>
                        match a.kind {
                            Cli.ArgKind.arg_flag =>
                                Cli.scan spec tl false (List.append flags [a.long]) options positionals pos_index,
                            Cli.ArgKind.arg_option =>
                                Cli.consume_option_value spec a tl flags options positionals pos_index,
                            Cli.ArgKind.arg_positional =>
                                Cli.ParseResult.parse_err (String.concat "unknown flag: --" body),
                        },
                },
        }

#[partial]
pub def Cli.apply_long_equals
        (spec : Cli.CommandSpec) (key : String) (value : String) (tl : List String)
        (flags : List String) (options : List Cli.ArgValue)
        (positionals : List Cli.ArgValue) (pos_index : I64) : Cli.ParseResult :=
    match Cli.find_long key spec {
        Option.none => Cli.ParseResult.parse_err (String.concat "unknown flag: --" key),
        Option.some a =>
            match a.kind {
                Cli.ArgKind.arg_flag =>
                    Cli.ParseResult.parse_err (String.concat "flag '--" (String.concat key "' does not take a value")),
                Cli.ArgKind.arg_option =>
                    Cli.scan spec tl false flags (List.append options [Cli.arg_value key value]) positionals pos_index,
                Cli.ArgKind.arg_positional =>
                    Cli.ParseResult.parse_err (String.concat "unknown flag: --" key),
            },
    }

#[partial]
pub def Cli.consume_option_value
        (spec : Cli.CommandSpec) (a : Cli.ArgSpec) (tl : List String)
        (flags : List String) (options : List Cli.ArgValue)
        (positionals : List Cli.ArgValue) (pos_index : I64) : Cli.ParseResult :=
    match tl {
        List.empty =>
            Cli.ParseResult.parse_err (String.concat "option '--" (String.concat a.long "' requires a value")),
        List.cons next rest =>
            if Cli.looks_like_flag next
            then Cli.ParseResult.parse_err (String.concat "option '--" (String.concat a.long "' requires a value"))
            else Cli.scan spec rest false flags (List.append options [Cli.arg_value a.long next]) positionals pos_index,
    }

// ─── Short options and clusters ───────────────────────────────────────

#[partial]
pub def Cli.scan_short
        (spec : Cli.CommandSpec) (hd : String) (tl : List String)
        (flags : List String) (options : List Cli.ArgValue)
        (positionals : List Cli.ArgValue) (pos_index : I64) : Cli.ParseResult :=
    if String.beq hd "-h" && Bool.not (Cli.short_claimed spec "h")
    then Cli.ParseResult.parse_help (Cli.help_text spec)
    else if String.beq hd "-V" && Bool.not (Cli.short_claimed spec "V")
    then if String.is_empty spec.version
         then Cli.ParseResult.parse_err "unknown flag: -V"
         else Cli.ParseResult.parse_version (Cli.version_text spec)
    else Cli.scan_short_cluster spec hd tl flags options positionals pos_index 1

#[partial]
pub def Cli.scan_short_cluster
        (spec : Cli.CommandSpec) (token : String) (rest : List String)
        (flags : List String) (options : List Cli.ArgValue)
        (positionals : List Cli.ArgValue) (pos_index : I64) (i : I64) : Cli.ParseResult :=
    if I64.lt i (String.length token) then
        let c : String := String.slice token i 1 in
        match Cli.find_short c spec {
            Option.none => Cli.ParseResult.parse_err (String.concat "unknown flag: -" c),
            Option.some a =>
                match a.kind {
                    Cli.ArgKind.arg_flag =>
                        if I64.lt (I64.add i 1) (String.length token) && String.beq (String.slice token (I64.add i 1) 1) "="
                        then Cli.ParseResult.parse_err (String.concat "flag '-" (String.concat c "' does not take a value"))
                        else Cli.scan_short_cluster spec token rest (List.append flags [a.long]) options positionals pos_index (I64.add i 1),
                    Cli.ArgKind.arg_option =>
                        let rem : String := String.drop (I64.add i 1) token in
                        if String.starts_with "=" rem
                        then Cli.scan spec rest false flags (List.append options [Cli.arg_value a.long (String.drop 1 rem)]) positionals pos_index
                        else if String.is_empty rem
                        then match rest {
                            List.empty => Cli.ParseResult.parse_err (String.concat "option '-" (String.concat c "' requires a value")),
                            List.cons next rest2 =>
                                if Cli.looks_like_flag next
                                then Cli.ParseResult.parse_err (String.concat "option '-" (String.concat c "' requires a value"))
                                else Cli.scan spec rest2 false flags (List.append options [Cli.arg_value a.long next]) positionals pos_index,
                        }
                        else Cli.scan spec rest false flags (List.append options [Cli.arg_value a.long rem]) positionals pos_index,
                    Cli.ArgKind.arg_positional =>
                        Cli.ParseResult.parse_err (String.concat "unknown flag: -" c),
                },
        }
    else Cli.scan spec rest false flags options positionals pos_index

// ─── Required/typed validation ─────────────────────────────────────────

pub def Cli.long_claimed (spec : Cli.CommandSpec) (long : String) : Bool :=
    match Cli.find_long long spec {
        Option.some _ => true,
        Option.none => false,
    }

pub def Cli.short_claimed (spec : Cli.CommandSpec) (short : String) : Bool :=
    match Cli.find_short short spec {
        Option.some _ => true,
        Option.none => false,
    }

#[partial]
pub def Cli.check_required_options (args : List Cli.ArgSpec) (options : List Cli.ArgValue) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_option a.kind && a.required && Bool.not (Cli.has_option_in a.long options)
            then Option.some (String.concat "missing required option '--" (String.concat a.long "'"))
            else Cli.check_required_options rest options,
    }

#[partial]
pub def Cli.required_positional_after
        (i : I64) (args : List Cli.ArgSpec) (positionals : List Cli.ArgValue) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_positional a.kind
            then
                if a.multiple
                then Option.none
                else if a.required && Bool.not (I64.lt i (List.length positionals))
                     then Option.some (String.concat "missing required argument '<" (String.concat a.long ">'"))
                     else Cli.required_positional_after (I64.add i 1) rest positionals
            else Cli.required_positional_after i rest positionals,
    }

#[partial]
pub def Cli.check_i64_options (args : List Cli.ArgSpec) (options : List Cli.ArgValue) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_option a.kind && Cli.same_value_type Cli.ArgValueType.arg_i64 a.value_type
            then match Cli.first_bad_i64 a.long options {
                Option.some v => Option.some (String.concat "invalid value '" (String.concat v (String.concat "' for '--" (String.concat a.long "': expected an integer")))),
                Option.none => Cli.check_i64_options rest options,
            }
            else Cli.check_i64_options rest options,
    }

#[partial]
pub def Cli.first_bad_i64 (name : String) (options : List Cli.ArgValue) : Option String :=
    match options {
        List.empty => Option.none,
        List.cons x rest =>
            if String.beq x.name name
            then match Cli.parse_i64 x.value {
                Option.some _ => Cli.first_bad_i64 name rest,
                Option.none => Option.some x.value,
            }
            else Cli.first_bad_i64 name rest,
    }

#[partial]
pub def Cli.check_i64_range
        (i : I64) (long : String) (positionals : List Cli.ArgValue) : Option String :=
    match Cli.nth_positional i positionals {
        Option.none => Option.none,
        Option.some x =>
            match Cli.parse_i64 x.value {
                Option.some _ => Cli.check_i64_range (I64.add i 1) long positionals,
                Option.none => Option.some
                    (String.concat "invalid value '" (String.concat x.value
                        (String.concat "' for '<" (String.concat long ">': expected an integer")))),
            },
    }

#[partial]
pub def Cli.check_i64_positionals_after
        (i : I64) (args : List Cli.ArgSpec) (positionals : List Cli.ArgValue) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_positional a.kind
            then
                if a.multiple
                then
                    if Cli.same_value_type Cli.ArgValueType.arg_i64 a.value_type
                    then Cli.check_i64_range i a.long positionals
                    else Option.none
                else
                    if Cli.same_value_type Cli.ArgValueType.arg_i64 a.value_type
                    then match Cli.nth_positional i positionals {
                        Option.some x =>
                            match Cli.parse_i64 x.value {
                                Option.some _ => Cli.check_i64_positionals_after (I64.add i 1) rest positionals,
                                Option.none => Option.some
                                    (String.concat "invalid value '" (String.concat x.value
                                        (String.concat "' for '<" (String.concat a.long ">': expected an integer")))),
                            },
                        Option.none => Option.none,
                    }
                    else Cli.check_i64_positionals_after (I64.add i 1) rest positionals
            else Cli.check_i64_positionals_after i rest positionals,
    }

#[partial]
pub def Cli.nth_positional (i : I64) (xs : List Cli.ArgValue) : Option Cli.ArgValue :=
    match xs {
        List.empty => Option.none,
        List.cons x rest => if I64.beq i 0 then Option.some x else Cli.nth_positional (I64.sub i 1) rest,
    }

pub def Cli.same_value_type (a : Cli.ArgValueType) (b : Cli.ArgValueType) : Bool :=
    match a {
        Cli.ArgValueType.arg_string => match b { Cli.ArgValueType.arg_string => true, _ => false },
        Cli.ArgValueType.arg_i64 => match b { Cli.ArgValueType.arg_i64 => true, _ => false },
    }

#[partial]
pub def Cli.finish
        (spec : Cli.CommandSpec) (flags : List String) (options : List Cli.ArgValue)
        (positionals : List Cli.ArgValue) (pos_index : I64) : Cli.ParseResult :=
    match Cli.check_required_options spec.args options {
        Option.some msg => Cli.ParseResult.parse_err msg,
        Option.none =>
            match Cli.required_positional_after 0 spec.args positionals {
                Option.some msg => Cli.ParseResult.parse_err msg,
                Option.none =>
                    match Cli.check_i64_options spec.args options {
                        Option.some msg => Cli.ParseResult.parse_err msg,
                        Option.none =>
                            match Cli.check_i64_positionals_after 0 spec.args positionals {
                                Option.some msg => Cli.ParseResult.parse_err msg,
                                Option.none => Cli.ParseResult.parse_ok (Cli.parsed spec.name flags options positionals),
                            },
                    },
            },
    }

// ─── Subcommands ──────────────────────────────────────────────────────

#[partial]
pub def Cli.select_subcommand
        (spec : Cli.CommandSpec) (name : String) (tl : List String) : Cli.ParseResult :=
    match Cli.find_subcommand name spec.subcommands {
        Option.none => Cli.ParseResult.parse_err (String.concat "unknown subcommand: " name),
        Option.some sub => Cli.parse sub tl,
    }

#[partial]
pub def Cli.find_subcommand (name : String) (subs : List Cli.CommandSpec) : Option Cli.CommandSpec :=
    match subs {
        List.empty => Option.none,
        List.cons s rest => if String.beq s.name name then Option.some s else Cli.find_subcommand name rest,
    }

#[terminating]
pub def Cli.parse_sub
        (spec : Cli.CommandSpec) (args : List String) (fenced : Bool) : Cli.ParseResult :=
    match args {
        List.empty => Cli.ParseResult.parse_err "missing subcommand",
        List.cons hd tl =>
            if fenced
            then Cli.select_subcommand spec hd tl
            else if String.beq hd "--"
            then Cli.parse_sub spec tl true
            else if String.starts_with "--" hd
            then Cli.parse_sub_flag_long spec hd tl
            else if String.starts_with "-" hd
            then if String.beq hd "-" || Cli.is_negative_number hd
                 then Cli.select_subcommand spec hd tl
                 else if String.beq hd "-h" && Bool.not (Cli.short_claimed spec "h")
                      then Cli.ParseResult.parse_help (Cli.help_text spec)
                      else if String.beq hd "-V" && Bool.not (Cli.short_claimed spec "V")
                           then if String.is_empty spec.version
                                then Cli.ParseResult.parse_err "unknown flag: -V"
                                else Cli.ParseResult.parse_version (Cli.version_text spec)
                           else Cli.parse_sub_flag_short spec (String.drop 1 hd) tl
            else Cli.select_subcommand spec hd tl,
    }

/// Top-level flags/options before a subcommand are accepted but discarded
/// (the selected subcommand's `Parsed` is what the decoder sees). The
/// derive never emits them; hand-written users get the common
/// `--global-flag value` forms.
#[partial]
pub def Cli.parse_sub_flag_long (spec : Cli.CommandSpec) (hd : String) (tl : List String) : Cli.ParseResult :=
    if String.beq hd "--help" && Bool.not (Cli.long_claimed spec "help")
    then Cli.ParseResult.parse_help (Cli.help_text spec)
    else if String.beq hd "--version" && Bool.not (Cli.long_claimed spec "version")
    then if String.is_empty spec.version
         then Cli.ParseResult.parse_err "unknown flag: --version"
         else Cli.ParseResult.parse_version (Cli.version_text spec)
    else
        let body : String := String.drop 2 hd in
        match Cli.split_first_eq body {
            Option.some pair =>
                match pair {
                    Pair.pair key _value =>
                        match Cli.find_long key spec {
                            Option.none =>
                                if String.beq key "help" && Bool.not (Cli.long_claimed spec "help")
                                then Cli.ParseResult.parse_err "flag '--help' does not take a value"
                                else if String.beq key "version" && Bool.not (Cli.long_claimed spec "version")
                                then Cli.ParseResult.parse_err "flag '--version' does not take a value"
                                else Cli.ParseResult.parse_err (String.concat "unknown flag: --" key),
                            Option.some a =>
                                match a.kind {
                                    Cli.ArgKind.arg_flag =>
                                        Cli.ParseResult.parse_err (String.concat "flag '--" (String.concat key "' does not take a value")),
                                    Cli.ArgKind.arg_option => Cli.parse_sub spec tl false,
                                    Cli.ArgKind.arg_positional =>
                                        Cli.ParseResult.parse_err (String.concat "unknown flag: --" key),
                                },
                        },
                },
            Option.none =>
                match Cli.find_long body spec {
                    Option.none => Cli.ParseResult.parse_err (String.concat "unknown flag: --" body),
                    Option.some a =>
                        match a.kind {
                            Cli.ArgKind.arg_option =>
                                match tl { List.empty => Cli.ParseResult.parse_err (String.concat "option '--" (String.concat a.long "' requires a value")), List.cons _ rest => Cli.parse_sub spec rest false },
                            _ => Cli.parse_sub spec tl false,
                        },
                },
        }

#[partial]
pub def Cli.parse_sub_flag_short (spec : Cli.CommandSpec) (cluster : String) (tl : List String) : Cli.ParseResult :=
    let c : String := String.slice cluster 0 1 in
    match Cli.find_short c spec {
        Option.none => Cli.ParseResult.parse_err (String.concat "unknown flag: -" c),
        Option.some a =>
            match a.kind {
                Cli.ArgKind.arg_option =>
                    if I64.lt 1 (String.length cluster)
                    then Cli.parse_sub spec tl false
                    else match tl { List.empty => Cli.ParseResult.parse_err (String.concat "option '-" (String.concat c "' requires a value")), List.cons _ rest => Cli.parse_sub spec rest false },
                _ =>
                    if I64.lt 1 (String.length cluster)
                    then Cli.parse_sub_flag_short spec (String.drop 1 cluster) tl
                    else Cli.parse_sub spec tl false,
            },
    }

// ─── Entry points ─────────────────────────────────────────────────────

pub def Cli.version_text (spec : Cli.CommandSpec) : String :=
    String.concat spec.name (String.concat " " spec.version)

#[terminating]
pub def Cli.parse (spec : Cli.CommandSpec) (args : List String) : Cli.ParseResult :=
    if List.is_empty spec.subcommands
    then Cli.scan spec args false List.empty List.empty List.empty 0
    else Cli.parse_sub spec args false

/// Parse, then decode and hand the value to `handler`. Help/version print
/// to stdout and return 0; a parse/decode error prints `error: ...` plus
/// usage to stderr and returns 2.
pub def Cli.run {A : Type}
        (spec : Cli.CommandSpec) (args : List String)
        (decode : Cli.Parsed -> Result String A)
        (handler : A -> IO I64) : IO I64 := do {
    match Cli.parse spec args {
        Cli.ParseResult.parse_ok p =>
            match decode p {
                Result.ok v => handler v,
                Result.err msg => do {
                    let shown : Cli.CommandSpec :=
                        match Cli.subcommand_named p.name spec {
                            Option.some sub => sub,
                            Option.none => spec,
                        };
                    IO.write_stderr (String.concat "error: " (String.concat msg "\n"));
                    IO.write_stderr (String.concat (Cli.usage shown) "\n");
                    return 2
                },
            },
        Cli.ParseResult.parse_help text => do {
            IO.println text;
            return 0
        },
        Cli.ParseResult.parse_version text => do {
            IO.println text;
            return 0
        },
        Cli.ParseResult.parse_err msg => do {
            IO.write_stderr (String.concat "error: " (String.concat msg "\n"));
            IO.write_stderr (String.concat (Cli.usage spec) "\n");
            return 2
        },
    }
}
