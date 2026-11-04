/// The backend's one attribute-lookup vocabulary.
///
/// `#[native X]`, `#[extern "c" ...]` and `#[export "c"]` all ask the same
/// questions of a `List Attribute`: find the attribute by name, read its
/// first positional string, or read a named argument (including the
/// `{link_name := "..."}` group the parser nests one level down). Keeping
/// one implementation means a new attribute inherits the same group
/// handling instead of growing a near-copy.
use lang::types {AttrArg, Attribute, Identifier, attr_args, id_eq}
use lib::symbols {symbol_identifier}

/// The argument list of the first attribute spelled `name`, if present.
///
/// A string-keyed facade over `lang::types.attr_args` (which takes an
/// `Identifier`): reusing it keeps one implementation, and the distinct
/// name avoids a global-table collision with that definition, since names
/// are not module-scoped.
#[partial]
pub def find_attr_args (name : String) (attrs : List Attribute) : Option (List AttrArg) :=
    attr_args (Identifier.id name) attrs

/// The first positional string of the first attribute spelled `name`.
#[partial]
pub def attr_target (name : String) (attrs : List Attribute) : Option String :=
    match find_attr_args name attrs {
        Option.some args => attr_arg_as_string_first args,
        Option.none => Option.none,
    }

#[partial]
pub def attr_arg_as_string_first (args : List AttrArg) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a _ =>
            match a {
                AttrArg.ident aid => Option.some (symbol_identifier aid),
                AttrArg.str s => Option.some s,
                _ => Option.none,
            },
    }

/// The first `name := "value"` argument, recursing into a parser-produced
/// `AttrArg.group` (see `lang/parser.mo`'s `attr_arg_named_close`).
#[partial]
pub def find_named_arg (key : String) (args : List AttrArg) : Option String := match args {
    List.empty => Option.none,
    List.cons hd tl =>
        match hd {
            AttrArg.named n v =>
                if id_eq n (Identifier.id key)
                then match v { AttrArg.str s => Option.some s, _ => Option.none }
                else find_named_arg key tl,
            AttrArg.group items =>
                match find_named_arg key items {
                    Option.some s => Option.some s,
                    Option.none => find_named_arg key tl,
                },
            _ => find_named_arg key tl,
        },
}
