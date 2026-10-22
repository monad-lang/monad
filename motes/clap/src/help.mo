/// Deterministic usage/help text for a `Cli.CommandSpec`.
///
/// Kept in its own module so the parser (`parse.mo`) and the derive can
/// call it without a cycle, and so the text is golden-testable on its own.
use lib::spec {
    Cli.ArgKind, Cli.ArgSpec, Cli.CommandSpec, Cli.flag, Cli.same_kind,
}

#[partial]
pub def Cli.has_option_arg (args : List Cli.ArgSpec) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_flag a.kind || Cli.same_kind Cli.ArgKind.arg_option a.kind
            then true
            else Cli.has_option_arg rest,
    }

#[partial]
pub def Cli.has_positional_arg (args : List Cli.ArgSpec) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            if Cli.same_kind Cli.ArgKind.arg_positional a.kind then true else Cli.has_positional_arg rest,
    }

#[partial]
pub def Cli.has_long_arg (name : String) (args : List Cli.ArgSpec) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            if String.beq a.long name then true else Cli.has_long_arg name rest,
    }

#[partial]
pub def Cli.has_short_arg (short : String) (args : List Cli.ArgSpec) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            if String.beq a.short short then true else Cli.has_short_arg short rest,
    }

/// `-h`/`--help` is available unless the user declared either spelling.
pub def Cli.help_available (s : Cli.CommandSpec) : Bool :=
    Bool.not (Cli.has_long_arg "help" s.args) && Bool.not (Cli.has_short_arg "h" s.args)

/// `-V`/`--version` needs a version and is available unless the user
/// declared either spelling.
pub def Cli.version_available (s : Cli.CommandSpec) : Bool :=
    Bool.not (String.is_empty s.version)
        && Bool.not (Cli.has_long_arg "version" s.args)
        && Bool.not (Cli.has_short_arg "V" s.args)

pub def Cli.usage (s : Cli.CommandSpec) : String :=
    let opts : Bool :=
        Cli.help_available s || Cli.version_available s || Cli.has_option_arg s.args in
    let args : Bool := Cli.has_positional_arg s.args in
    let subs : Bool := Bool.not (List.is_empty s.subcommands) in
    let tail : String :=
        String.concat (if opts then " [OPTIONS]" else "")
            (String.concat (if subs then " <SUBCOMMAND>" else "")
                (if args then " [ARGS]" else "")) in
    String.concat "Usage: " (String.concat s.name tail)

#[partial]
pub def Cli.spaces (n : I64) : String :=
    if I64.lt n 1 then "" else String.concat " " (Cli.spaces (I64.sub n 1))

#[partial]
pub def Cli.string_len_max (xs : List String) (acc : I64) : I64 :=
    match xs {
        List.empty => acc,
        List.cons x rest =>
            let n : I64 := String.length x in
            Cli.string_len_max rest (if I64.lt acc n then n else acc),
    }

#[partial]
pub def Cli.pad_right (n : I64) (s : String) : String :=
    String.concat s (Cli.spaces (I64.sub n (String.length s)))

pub def Cli.arg_value_name (a : Cli.ArgSpec) : String :=
    if String.is_empty a.value_name then "VALUE" else a.value_name

pub def Cli.arg_label (a : Cli.ArgSpec) : String :=
    match a.kind {
        Cli.ArgKind.arg_flag =>
            if String.is_empty a.short
            then String.concat "--" a.long
            else String.concat "-" (String.concat a.short (String.concat ", --" a.long)),
        Cli.ArgKind.arg_option =>
            let head : String :=
                if String.is_empty a.short
                then String.concat "--" a.long
                else String.concat "-" (String.concat a.short (String.concat ", --" a.long)) in
            String.concat head (String.concat " <" (String.concat (Cli.arg_value_name a) ">")),
        Cli.ArgKind.arg_positional =>
            if a.multiple
            then String.concat "<" (String.concat a.long ">...")
            else String.concat "<" (String.concat a.long ">"),
    }

pub def Cli.arg_help (a : Cli.ArgSpec) : String :=
    if a.has_default
    then String.concat a.help (String.concat " (default: " (String.concat a.default ")"))
    else a.help

#[partial]
pub def Cli.arg_labels (args : List Cli.ArgSpec) : List String :=
    match args {
        List.empty => List.empty,
        List.cons a rest => List.cons (Cli.arg_label a) (Cli.arg_labels rest),
    }

#[partial]
pub def Cli.render_arg_lines (width : I64) (args : List Cli.ArgSpec) : List String :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            List.cons
                (String.concat "  " (String.concat (Cli.pad_right width (Cli.arg_label a)) (Cli.arg_help a)))
                (Cli.render_arg_lines width rest),
    }

#[partial]
pub def Cli.filter_args (kind : Cli.ArgKind) (args : List Cli.ArgSpec) : List Cli.ArgSpec :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            if Cli.same_kind kind a.kind
            then List.cons a (Cli.filter_args kind rest)
            else Cli.filter_args kind rest,
    }

#[partial]
pub def Cli.sub_labels (subs : List Cli.CommandSpec) : List String :=
    match subs {
        List.empty => List.empty,
        List.cons s rest => List.cons s.name (Cli.sub_labels rest),
    }

#[partial]
pub def Cli.render_sub_lines (width : I64) (subs : List Cli.CommandSpec) : List String :=
    match subs {
        List.empty => List.empty,
        List.cons s rest =>
            List.cons
                (String.concat "  " (String.concat (Cli.pad_right width s.name) s.about))
                (Cli.render_sub_lines width rest),
    }

#[partial]
pub def Cli.lines_with_newlines (lines : List String) : List String :=
    match lines {
        List.empty => List.empty,
        List.cons line rest => List.cons (String.concat line "\n") (Cli.lines_with_newlines rest),
    }

#[partial]
pub def Cli.section (title : String) (lines : List String) : String :=
    if List.is_empty lines
    then ""
    else String.concat "\n" (String.concat (String.concat title "\n")
        (String.concat_list (Cli.lines_with_newlines lines)))

pub def Cli.help_text (s : Cli.CommandSpec) : String :=
    let positionals : List Cli.ArgSpec := Cli.filter_args Cli.ArgKind.arg_positional s.args in
    let help_builtin : List Cli.ArgSpec :=
        if Cli.help_available s then [Cli.flag "help" "h" "print help"] else [] in
    let version_builtin : List Cli.ArgSpec :=
        if Cli.version_available s then [Cli.flag "version" "V" "print version"] else [] in
    let builtins : List Cli.ArgSpec := List.append help_builtin version_builtin in
    let options : List Cli.ArgSpec :=
        List.append (List.append builtins (Cli.filter_args Cli.ArgKind.arg_option s.args))
                    (Cli.filter_args Cli.ArgKind.arg_flag s.args) in
    let arg_width : I64 := Cli.string_len_max (Cli.arg_labels (List.append positionals options)) 0 in
    let sub_width : I64 := Cli.string_len_max (Cli.sub_labels s.subcommands) 0 in
    let about : String :=
        if String.is_empty s.about then "" else String.concat "\n" (String.concat s.about "\n") in
    String.concat (Cli.usage s)
        (String.concat about
            (String.concat
                (Cli.section "Arguments:" (Cli.render_arg_lines arg_width positionals))
                (String.concat
                    (Cli.section "Options:" (Cli.render_arg_lines arg_width options))
                    (Cli.section "Commands:" (Cli.render_sub_lines sub_width s.subcommands)))))
