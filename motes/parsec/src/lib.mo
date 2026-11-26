// The parsec mote's library root -- bare `use parsec` resolves here.
//
// The parser substrate, four modules deep: `core` (the `ParseResult` every
// other module answers with, and the error it carries), `combinators` (the
// combinators a grammar is built out of), `char_preds` (the character
// classes those combinators are parameterised by) and `number`
// (`parse_i64`, which is also how `build/src/manage.mo` reads a size out
// of a tool's output).
//
// What is re-exported here is the `pub`-marked surface and nothing else,
// which is a small one on purpose (`lang/src/lib.mo`'s doctrine): a
// grammar that wants `alt`/`many1`/`map_parse` names `parsec::combinators`
// for them exactly as `lang/src/parser.mo` does, and a hub mirroring all
// ~40 of that module's defs would be a second, always-stale index of it.
// The point of this file is that `use parsec {...}` resolves at all.
//
// No `{*}` globs: at this size a glob drags a whole namespace into every
// importer's scope, which is both slow and a name-collision hazard.

pub use lib::core {ParseError, ParseResult, Text}
pub use lib::input {Bytes, Input}
pub use lib::parser {Parser}
pub use lib::combinators {take_while, take_while_byte}
pub use lib::char_preds {is_ident_char, is_ident_char_byte, is_space, is_space_byte}
pub use lib::number {parse_i64}
