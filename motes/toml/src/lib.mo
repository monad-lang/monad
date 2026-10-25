// The toml mote's library root -- bare `use toml` resolves here.
//
// One module, so this hub is thin by construction: the `Toml.Value` a
// parsed document is, the reader that produces it, and the two lookups a
// caller walks the result with. That is a surface for a consumer that does
// not exist yet: the load-bearing one, `lang/src/mote.mo`, reaches past this
// hub to `toml::toml` for the four `Toml.Value` constructors as well, so
// these five names are a starting point and not the whole of what a manifest
// reader needs.
//
// Small rather than a mirror, as `lang/src/lib.mo` argues: `Toml.to_string`
// and the `Toml.insert_at_steps` assembler are reached by naming the
// module, which is what `motes/toml/src/toml.mo`'s own tests and
// `examples/toml.mo` already do.
//
// No `{*}` globs.

pub use lib::toml {
    Toml.Value, Toml.ParseError, Toml.parse, Toml.table_get, Toml.array_at,
    Toml.to_string,
}
