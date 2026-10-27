// The yaml mote's library root -- bare `use yaml` resolves here.
//
// The `Yaml` value type, its parse error, and the reader/writer pair. Every
// consumer that wants codecs imports `yaml::serde_backend` for the
// `derive_yaml_serialize!`/`derive_yaml_deserialize!` macros, exactly as
// `json` consumers import `json::serde_backend`.
//
// No `{*}` globs.

pub use lib::yaml {Yaml, Yaml.ParseError, Yaml.parse, Yaml.to_string, Yaml.to_string_flow}
