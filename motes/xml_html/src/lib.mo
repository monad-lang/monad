// The xml_html mote's library root -- bare `use xml_html` resolves here.
//
// Two independent format modules: `html` owns `Html.Attr`/`Html.Node` and
// `Html.to_string`, `xml` owns `Xml.Attr`/`Xml.Node` and `Xml.to_string`.
// They deliberately share no format-generic classes (the `lang/json.mo` vs
// `lang/toml.mo` policy): own constructors, own escapers, own BEq.
//
// This hub exports types and the serializers only. Constructors stay
// reachable through their type namespace (`Html.node_text`,
// `Html.Node.node_text`); no `{*}` globs, which would drag every helper
// into an importer's scope.

pub use lib::html {
    Html.Attr, Html.Node, Html.RenderOpts, Html.default_opts,
    Html.to_string, Html.to_string_with, Html.beq,
}
pub use lib::xml {Xml.Attr, Xml.Node, Xml.to_string, Xml.beq}
