/// The format-agnostic half of serde: what any wire/text format must
/// provide to be a target for the derive machinery in `derive.mo`. Every
/// method takes the format's own type (`S`/`D`) as a plain VALUE
/// argument, never only in a return position -- confirmed by probe
/// (`plans/library-ideas/serde.md`) that a class method whose own class
/// parameter appears ONLY in the return type, inside a function that is
/// itself generic over that parameter (`[Serializer S] (a : String) : S`),
/// fails to dispatch at run time (`motes/json/src/json.mo`'s own
/// `Json.Deserializer` documents the identical failure for its `D`).
/// That failure mode does not apply here: nothing in this mote defines a
/// generic-over-`S`/`D` wrapper function. `derive.mo` generates one
/// CONCRETE instance per (type, format) -- the format is baked in at
/// generation time, not resolved generically -- so every actual call site
/// of `ser_string`/`de_get_field`/etc. is ordinary concrete dispatch, the
/// same shape as any other class method call in this codebase.
pub class Serializer (S : Type) {
    def ser_null : S
    def ser_bool (b : Bool) : S
    def ser_int (i : I64) : S
    def ser_string (s : String) : S
    def ser_list (xs : List S) : S
    def ser_object (fields : List (Pair String S)) : S
}

/// A second, measured limit on top of the one above: `derive.mo`'s
/// GENERATED code must never reference a `Serializer`/`Deserializer`
/// method by its class-qualified name (`Serializer.ser_int`) directly --
/// confirmed by probe that a macro-REIFIED bare top-level `d_def` calling
/// a class method this way fails at run time with `unresolved global`,
/// even though the identical call, normally PARSED (not macro-generated),
/// dispatches fine. Calling an ordinary, hand-written, non-class WRAPPER
/// function instead (itself calling the class method, normally parsed) is
/// what works. So every format backend (`motes/json`'s `instance
/// Serializer Json`, for instance) must ALSO provide one plain wrapper
/// function per method, named `<format_tag>_ser_null`/`_ser_bool`/
/// `_ser_int`/`_ser_string`/`_ser_list`/`_ser_object` and
/// `<format_tag>_de_get_bool`/etc. (`format_tag` is the lowercase tag
/// passed to `derive_serialize_meta`/`derive_deserialize_meta`, e.g.
/// `"json"`) -- `derive.mo` generates calls to THESE, never to the class
/// methods themselves.

/// `de_get_field`'s `Option D` (not a hard error on a missing key) is what
/// lets `derive.mo` treat a defaulted/`Option`-typed field as optional:
/// the caller decides what a missing key means, the format backend only
/// reports whether the key was there.
pub class Deserializer (D : Type) {
    def de_is_null (d : D) : Bool
    def de_get_bool (d : D) : Result String Bool
    def de_get_int (d : D) : Result String I64
    def de_get_string (d : D) : Result String String
    def de_get_list (d : D) : Result String (List D)
    def de_get_field (d : D) (name : String) : Result String (Option D)
}
