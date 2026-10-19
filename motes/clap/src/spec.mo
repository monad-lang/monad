/// The declarative surface of `motes/clap`: argument/command specs, the
/// parsed-result type, and the accessors a generated or hand-written
/// decoder reads.
///
/// This is additive. `args.mo` keeps the legacy `take_*` helpers and their
/// result types untouched so `cli/src/main.mo`, `motes/shuttle` and
/// `motes/weaver` keep their exact behavior; new code uses these types and
/// `parse.mo`'s parser instead.
use std::list {List.any, List.length}

/// What an argument is.
pub type Cli.ArgKind {
    arg_flag,
    arg_option,
    arg_positional,
}

/// The type a value is decoded as. `Cli.parse` validates `arg_i64` at parse
/// time; `arg_string` is passed through.
pub type Cli.ArgValueType {
    arg_string,
    arg_i64,
}

/// One declared argument.
///
/// `long` is the spelling without the leading `--`; `short` is a one-byte
/// spelling without the leading `-` (empty means none). Positionals use
/// `long` as their display name. `default` is help metadata only: the
/// decoder applies the field's own default expression, so a typed default
/// need not be rendered to text here.
pub struct Cli.ArgSpec {
    long : String,
    short : String,
    kind : Cli.ArgKind,
    value_type : Cli.ArgValueType,
    required : Bool,
    has_default : Bool,
    default : String,
    multiple : Bool,
    allow_hyphen_values : Bool,
    help : String,
    value_name : String,
}

/// One command (or subcommand) definition.
pub struct Cli.CommandSpec {
    name : String,
    about : String,
    version : String,
    args : List Cli.ArgSpec,
    subcommands : List Cli.CommandSpec,
}

/// One parsed option or positional value. Repeats are distinct entries.
pub struct Cli.ArgValue {
    name : String,
    value : String,
}

/// A successfully parsed command line. `name` is the selected command
/// (the top-level command for a flags-only spec, the subcommand's name for
/// an ADT).
pub struct Cli.Parsed {
    name : String,
    flags : List String,
    options : List Cli.ArgValue,
    positionals : List Cli.ArgValue,
}

/// The parser's total result: success, help, version, or a usage error.
pub type Cli.ParseResult {
    parse_ok (parsed : Cli.Parsed),
    parse_help (text : String),
    parse_version (text : String),
    parse_err (message : String),
}

// ─── Builders ──────────────────────────────────────────────────────────

pub def Cli.no_args : List Cli.ArgSpec := List.empty
pub def Cli.no_subcommands : List Cli.CommandSpec := List.empty

/// The full-shape flag builder. `kind := arg_flag`, `value_type :=
/// arg_string`; a flag never takes a value.
pub def Cli.flag (long : String) (short : String) (help : String) : Cli.ArgSpec :=
    let a : Cli.ArgSpec := {
        long := long,
        short := short,
        kind := Cli.ArgKind.arg_flag,
        value_type := Cli.ArgValueType.arg_string,
        required := false,
        has_default := false,
        default := "",
        multiple := false,
        allow_hyphen_values := false,
        help := help,
        value_name := "",
    } in a

/// The one option builder every typed/required/default variant delegates
/// to.
pub def Cli.option_spec
        (value_type : Cli.ArgValueType) (long : String) (short : String)
        (value_name : String) (required : Bool) (has_default : Bool)
        (default : String) (multiple : Bool) (help : String) : Cli.ArgSpec :=
    let a : Cli.ArgSpec := {
        long := long,
        short := short,
        kind := Cli.ArgKind.arg_option,
        value_type := value_type,
        required := required,
        has_default := has_default,
        default := default,
        multiple := multiple,
        allow_hyphen_values := false,
        help := help,
        value_name := value_name,
    } in a

pub def Cli.option (long : String) (short : String) (value_name : String) (help : String) : Cli.ArgSpec :=
    Cli.option_spec Cli.ArgValueType.arg_string long short value_name true false "" false help

pub def Cli.option_optional (long : String) (short : String) (value_name : String) (help : String) : Cli.ArgSpec :=
    Cli.option_spec Cli.ArgValueType.arg_string long short value_name false false "" false help

pub def Cli.option_default (long : String) (short : String) (value_name : String) (default : String) (help : String) : Cli.ArgSpec :=
    Cli.option_spec Cli.ArgValueType.arg_string long short value_name false true default false help

pub def Cli.option_i64 (long : String) (short : String) (value_name : String) (help : String) : Cli.ArgSpec :=
    Cli.option_spec Cli.ArgValueType.arg_i64 long short value_name true false "" false help

pub def Cli.option_i64_optional (long : String) (short : String) (value_name : String) (help : String) : Cli.ArgSpec :=
    Cli.option_spec Cli.ArgValueType.arg_i64 long short value_name false false "" false help

pub def Cli.option_i64_default (long : String) (short : String) (value_name : String) (default : String) (help : String) : Cli.ArgSpec :=
    Cli.option_spec Cli.ArgValueType.arg_i64 long short value_name false true default false help

pub def Cli.multi_option (long : String) (short : String) (value_name : String) (help : String) : Cli.ArgSpec :=
    Cli.option_spec Cli.ArgValueType.arg_string long short value_name false false "" true help

pub def Cli.positional_spec
        (value_type : Cli.ArgValueType) (name : String) (required : Bool)
        (has_default : Bool) (default : String) (multiple : Bool) (help : String) : Cli.ArgSpec :=
    let a : Cli.ArgSpec := {
        long := name,
        short := "",
        kind := Cli.ArgKind.arg_positional,
        value_type := value_type,
        required := required,
        has_default := has_default,
        default := default,
        multiple := multiple,
        allow_hyphen_values := false,
        help := help,
        value_name := name,
    } in a

pub def Cli.positional (name : String) (help : String) : Cli.ArgSpec :=
    Cli.positional_spec Cli.ArgValueType.arg_string name true false "" false help

pub def Cli.positional_optional (name : String) (help : String) : Cli.ArgSpec :=
    Cli.positional_spec Cli.ArgValueType.arg_string name false false "" false help

pub def Cli.positional_i64 (name : String) (help : String) : Cli.ArgSpec :=
    Cli.positional_spec Cli.ArgValueType.arg_i64 name true false "" false help

pub def Cli.positional_i64_optional (name : String) (help : String) : Cli.ArgSpec :=
    Cli.positional_spec Cli.ArgValueType.arg_i64 name false false "" false help

pub def Cli.positional_multi (name : String) (help : String) : Cli.ArgSpec :=
    Cli.positional_spec Cli.ArgValueType.arg_string name false false "" true help

pub def Cli.command (name : String) (about : String) : Cli.CommandSpec :=
    let s : Cli.CommandSpec := {
        name := name,
        about := about,
        version := "",
        args := Cli.no_args,
        subcommands := Cli.no_subcommands,
    } in s

pub def Cli.with_name (name : String) (s : Cli.CommandSpec) : Cli.CommandSpec :=
    { s with name := name }

pub def Cli.with_about (about : String) (s : Cli.CommandSpec) : Cli.CommandSpec :=
    { s with about := about }

pub def Cli.with_version (version : String) (s : Cli.CommandSpec) : Cli.CommandSpec :=
    { s with version := version }

pub def Cli.with_args (args : List Cli.ArgSpec) (s : Cli.CommandSpec) : Cli.CommandSpec :=
    { s with args := args }

pub def Cli.with_subcommands (subs : List Cli.CommandSpec) (s : Cli.CommandSpec) : Cli.CommandSpec :=
    { s with subcommands := subs }

pub def Cli.same_kind (a : Cli.ArgKind) (b : Cli.ArgKind) : Bool :=
    match a {
        Cli.ArgKind.arg_flag => match b { Cli.ArgKind.arg_flag => true, _ => false },
        Cli.ArgKind.arg_option => match b { Cli.ArgKind.arg_option => true, _ => false },
        Cli.ArgKind.arg_positional => match b { Cli.ArgKind.arg_positional => true, _ => false },
    }

pub def Cli.arg_value (name : String) (value : String) : Cli.ArgValue :=
    let v : Cli.ArgValue := { name := name, value := value } in v

pub def Cli.parsed (name : String) (flags : List String) (options : List Cli.ArgValue) (positionals : List Cli.ArgValue) : Cli.Parsed :=
    let p : Cli.Parsed := { name := name, flags := flags, options := options, positionals := positionals } in p

// ─── Accessors ─────────────────────────────────────────────────────────

/// The selected command's name (the single command's name for a
/// flags-only spec, the subcommand's name for an ADT).
pub def Cli.command_name (p : Cli.Parsed) : String :=
    p.name

pub def Cli.flag_set (name : String) (p : Cli.Parsed) : Bool :=
    List.any (fn n => String.beq n name) p.flags

#[partial]
def Cli.flag_count_loop (name : String) (xs : List String) (acc : I64) : I64 :=
    match xs {
        List.empty => acc,
        List.cons x rest =>
            if String.beq x name
            then Cli.flag_count_loop name rest (I64.add acc 1)
            else Cli.flag_count_loop name rest acc,
    }

pub def Cli.flag_count (name : String) (p : Cli.Parsed) : I64 :=
    Cli.flag_count_loop name p.flags 0

#[partial]
def Cli.option_value_loop (name : String) (xs : List Cli.ArgValue) (acc : Option String) : Option String :=
    match xs {
        List.empty => acc,
        List.cons x rest =>
            if String.beq x.name name
            then Cli.option_value_loop name rest (Option.some x.value)
            else Cli.option_value_loop name rest acc,
    }

/// Last occurrence wins for a non-repeatable option.
pub def Cli.option_value (name : String) (p : Cli.Parsed) : Option String :=
    Cli.option_value_loop name p.options Option.none

pub def Cli.has_option (name : String) (p : Cli.Parsed) : Bool :=
    match Cli.option_value name p {
        Option.some _ => true,
        Option.none => false,
    }

#[partial]
def Cli.option_values_loop (name : String) (xs : List Cli.ArgValue) (acc : List String) : List String :=
    match xs {
        List.empty => acc,
        List.cons x rest =>
            if String.beq x.name name
            then Cli.option_values_loop name rest (List.append acc [x.value])
            else Cli.option_values_loop name rest acc,
    }

pub def Cli.option_values (name : String) (p : Cli.Parsed) : List String :=
    Cli.option_values_loop name p.options List.empty

pub def Cli.required_option (name : String) (p : Cli.Parsed) : String :=
    Option.get_or_default "" (Cli.option_value name p)

#[partial]
def Cli.positional_at_loop (i : I64) (xs : List Cli.ArgValue) : Option Cli.ArgValue :=
    match xs {
        List.empty => Option.none,
        List.cons x rest =>
            if I64.beq i 0 then Option.some x else Cli.positional_at_loop (I64.sub i 1) rest,
    }

pub def Cli.positional_value (i : I64) (p : Cli.Parsed) : Option String :=
    match Cli.positional_at_loop i p.positionals {
        Option.some v => Option.some v.value,
        Option.none => Option.none,
    }

pub def Cli.has_positional (i : I64) (p : Cli.Parsed) : Bool :=
    I64.lt i (List.length p.positionals)

#[partial]
def Cli.positionals_from_loop (i : I64) (xs : List Cli.ArgValue) : List Cli.ArgValue :=
    match xs {
        List.empty => List.empty,
        List.cons x rest =>
            if I64.lt i 1 then xs else Cli.positionals_from_loop (I64.sub i 1) rest,
    }

#[partial]
def Cli.arg_values_to_strings (xs : List Cli.ArgValue) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x.value (Cli.arg_values_to_strings rest),
    }

pub def Cli.positional_values (i : I64) (p : Cli.Parsed) : List String :=
    Cli.arg_values_to_strings (Cli.positionals_from_loop i p.positionals)

pub def Cli.required_positional (i : I64) (p : Cli.Parsed) : String :=
    Option.get_or_default "" (Cli.positional_value i p)

/// Parse an optionally-signed decimal I64. Kept local (rather than importing
/// `motes/parsec`) because clap is a compiler input loaded by
/// `cli/src/main.mo`, and the Rust `derive_cli_test` host loads it with only
/// the ambient modules.
#[partial]
pub def Cli.parse_i64 (s : String) : Option I64 :=
    if String.is_empty s then Option.none
    else if String.beq (String.slice s 0 1) "-"
    then match Cli.parse_i64_unsigned (String.drop 1 s) 0 {
        Option.some n => Option.some (I64.sub 0 n),
        Option.none => Option.none,
    }
    else Cli.parse_i64_unsigned s 0

#[partial]
def Cli.parse_i64_unsigned (s : String) (acc : I64) : Option I64 :=
    if String.is_empty s then Option.some acc
    else
        let c : String := String.slice s 0 1 in
        match Cli.digit_of c {
            Option.some d => Cli.parse_i64_unsigned (String.drop 1 s) (I64.add (I64.mul acc 10) d),
            Option.none => Option.none,
        }

pub def Cli.digit_of (c : String) : Option I64 :=
    if String.beq c "0" then Option.some 0
    else if String.beq c "1" then Option.some 1
    else if String.beq c "2" then Option.some 2
    else if String.beq c "3" then Option.some 3
    else if String.beq c "4" then Option.some 4
    else if String.beq c "5" then Option.some 5
    else if String.beq c "6" then Option.some 6
    else if String.beq c "7" then Option.some 7
    else if String.beq c "8" then Option.some 8
    else if String.beq c "9" then Option.some 9
    else Option.none

pub def Cli.option_value_i64 (name : String) (p : Cli.Parsed) : Option I64 :=
    match Cli.option_value name p {
        Option.some v => Cli.parse_i64 v,
        Option.none => Option.none,
    }

pub def Cli.required_option_i64 (name : String) (p : Cli.Parsed) : I64 :=
    Option.get_or_default 0 (Cli.option_value_i64 name p)

pub def Cli.positional_value_i64 (i : I64) (p : Cli.Parsed) : Option I64 :=
    match Cli.positional_value i p {
        Option.some v => Cli.parse_i64 v,
        Option.none => Option.none,
    }

pub def Cli.required_positional_i64 (i : I64) (p : Cli.Parsed) : I64 :=
    Option.get_or_default 0 (Cli.positional_value_i64 i p)
