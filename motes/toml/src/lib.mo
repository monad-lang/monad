// The toml mote's library root -- bare `use toml` resolves here.
//
// One module, so this hub is thin by construction: the `Toml.Value` a
// parsed document is (all seven constructors' worth, floats and
// date-times included since the grammar became the whole of TOML 1.0.0),
// the reader that produces it, and the accessors a caller walks the
// result with. The load-bearing consumer, `lang/src/mote.mo`, reaches
// past this hub to `toml::toml` for the `Toml.Value` constructors as
// well, so this hub is the starting surface rather than the whole of
// what a manifest reader needs.
//
// Small rather than a mirror, as `lang/src/lib.mo` argues: `Toml.to_string`
// and the assembler's internals are reached by naming the module, which
// is what `motes/toml/src/toml.mo`'s own tests and `examples/toml.mo`
// already do.
//
// No `{*}` globs.

pub use lib::toml {
    Toml.Value, Toml.ParseError, Toml.parse, Toml.table_get, Toml.array_at,
    Toml.to_string,
    Toml.get_string, Toml.get_integer, Toml.get_float, Toml.get_boolean,
    Toml.get_datetime, Toml.get_array, Toml.get_table,
    Toml.make_string, Toml.make_integer, Toml.make_float,
    Toml.make_boolean, Toml.make_datetime, Toml.make_array, Toml.make_table,
}
