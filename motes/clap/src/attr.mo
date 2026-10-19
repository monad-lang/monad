/// Read the canonical attribute string the compiler's reflection puts in
/// `FieldInfo.attrs` (see `init/src/meta.mo`):
///
///   - `arg` (bare)
///   - `arg(short:="v",help:="a, b")`
///
/// This module is evaluated by the self-hosted meta evaluator when a
/// `#[derive Cli]` expands, so it uses only that evaluator's pure-native
/// subset: `String.length/slice/drop/starts_with/beq/concat`, `I64.*`.
/// In particular it does not use `String.to_list`-backed helpers such as
/// `contains`/`trim`/`ends_with`.
///
/// The string is produced by the compiler, not typed by a user directly,
/// so the serializer's no-spaces `key:=value` form is the only one that has
/// to parse correctly; the scanner still handles quoted values, escapes and
/// commas inside quotes.

#[partial]
pub def Cli.attr_name (s : String) : String :=
    Cli.attr_name_at s 0

#[partial]
def Cli.attr_name_at (s : String) (i : I64) : String :=
    if I64.lt i (String.length s) then
        if String.beq (String.slice s i 1) "("
        then String.slice s 0 i
        else Cli.attr_name_at s (I64.add i 1)
    else s

#[partial]
pub def Cli.attr_has (name : String) (attrs : List String) : Bool :=
    match attrs {
        List.empty => false,
        List.cons a rest =>
            if String.beq (Cli.attr_name a) name then true else Cli.attr_has name rest,
    }

#[partial]
def Cli.find_char (ch : String) (s : String) (i : I64) : Option I64 :=
    if I64.lt i (String.length s) then
        if String.beq (String.slice s i 1) ch
        then Option.some i
        else Cli.find_char ch s (I64.add i 1)
    else Option.none

#[partial]
def Cli.find_sub (needle : String) (s : String) (i : I64) : Option I64 :=
    if I64.lt i (String.length s) then
        if String.starts_with needle (String.drop i s)
        then Option.some i
        else Cli.find_sub needle s (I64.add i 1)
    else Option.none

/// The text between the attribute name's `(` and the matching final `)`.
#[partial]
pub def Cli.attr_body (s : String) : String :=
    match Cli.find_char "(" s 0 {
        Option.none => "",
        Option.some open_i =>
            let rest : String := String.drop (I64.add open_i 1) s in
            if I64.lt 0 (String.length rest) && String.beq (String.slice rest (I64.sub (String.length rest) 1) 1) ")"
            then String.slice rest 0 (I64.sub (String.length rest) 1)
            else rest,
    }

#[partial]
def Cli.unescape (s : String) : String :=
    Cli.unescape_from s 0 ""

#[partial]
def Cli.unescape_from (s : String) (i : I64) (acc : String) : String :=
    if I64.lt i (String.length s) then
        let c : String := String.slice s i 1 in
        if String.beq c "\\" && I64.lt (I64.add i 1) (String.length s)
        then Cli.unescape_from s (I64.add i 2) (String.concat acc (String.slice s (I64.add i 1) 1))
        else Cli.unescape_from s (I64.add i 1) (String.concat acc c)
    else acc

#[partial]
def Cli.decode_attr_value (v : String) : String :=
    if I64.lt 1 (String.length v)
       && String.beq (String.slice v 0 1) "\""
       && String.beq (String.slice v (I64.sub (String.length v) 1) 1) "\""
    then Cli.unescape (String.slice v 1 (I64.sub (String.length v) 2))
    else v

#[partial]
def Cli.parse_kv (piece : String) : Option (Pair String String) :=
    match Cli.find_sub ":=" piece 0 {
        Option.none => Option.none,
        Option.some idx =>
            Option.some (Pair.pair
                (String.slice piece 0 idx)
                (Cli.decode_attr_value (String.drop (I64.add idx 2) piece))),
    }

/// Split at commas outside double quotes; escapes are copied through for
/// `decode_attr_value` to handle.
#[partial]
def Cli.split_kv_loop
        (body : String) (i : I64) (start : I64) (in_quote : Bool) (escaped : Bool)
        (acc : List String) : List String :=
    if I64.lt i (String.length body) then
        let c : String := String.slice body i 1 in
        if escaped
        then Cli.split_kv_loop body (I64.add i 1) start in_quote false acc
        else if String.beq c "\\"
             then Cli.split_kv_loop body (I64.add i 1) start in_quote true acc
             else if String.beq c "\""
                  then Cli.split_kv_loop body (I64.add i 1) start (Bool.not in_quote) false acc
                  else if Bool.not in_quote && String.beq c ","
                       then Cli.split_kv_loop body (I64.add i 1) (I64.add i 1) false false
                                (List.append acc [String.slice body start (I64.sub i start)])
                       else Cli.split_kv_loop body (I64.add i 1) start in_quote false acc
    else List.append acc [String.slice body start (I64.sub (String.length body) start)]

#[partial]
def Cli.parse_kv_list (pieces : List String) : List (Pair String String) :=
    match pieces {
        List.empty => List.empty,
        List.cons p rest =>
            if String.is_empty p
            then Cli.parse_kv_list rest
            else match Cli.parse_kv p {
                Option.none => Cli.parse_kv_list rest,
                Option.some pair => List.cons pair (Cli.parse_kv_list rest),
            },
    }

pub def Cli.attr_args (s : String) : List (Pair String String) :=
    Cli.parse_kv_list (Cli.split_kv_loop (Cli.attr_body s) 0 0 false false List.empty)

#[partial]
def Cli.attr_value_of (key : String) (args : List (Pair String String)) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons pair rest =>
            match pair {
                Pair.pair k v => if String.beq k key then Option.some v else Cli.attr_value_of key rest,
            },
    }

/// The value of `key` on the attribute named `name`, if both exist.
#[partial]
pub def Cli.attr_arg (name : String) (key : String) (attrs : List String) : Option String :=
    match attrs {
        List.empty => Option.none,
        List.cons a rest =>
            if String.beq (Cli.attr_name a) name
            then Cli.attr_value_of key (Cli.attr_args a)
            else Cli.attr_arg name key rest,
    }

/// `max_turns` -> `max-turns`; a trailing `_` is dropped first, so a
/// reserved word can be a constructor (`use_` -> `use`).
#[partial]
pub def Cli.kebab (s : String) : String :=
    let n : I64 := String.length s in
    let t : String :=
        if I64.lt 0 n && String.beq (String.slice s (I64.sub n 1) 1) "_"
        then String.slice s 0 (I64.sub n 1)
        else s in
    Cli.kebab_from t 0 ""

#[partial]
def Cli.kebab_from (s : String) (i : I64) (acc : String) : String :=
    if I64.lt i (String.length s) then
        let c : String := String.slice s i 1 in
        if String.beq c "_"
        then Cli.kebab_from s (I64.add i 1) (String.concat acc "-")
        else Cli.kebab_from s (I64.add i 1) (String.concat acc c)
    else acc
