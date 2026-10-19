// Oak's library root -- bare `use oak` resolves here.
//
// The re-exports are explicit (no globs), following xml_html's lib.mo.
// The types stay in xml_html: consumers import
// `use xml_html::html {Html.Attr, Html.Node, Html.to_string}` directly.

pub use lib::elements {
    Html.id_, Html.class_, Html.href, Html.src, Html.alt, Html.type_, Html.value_,
    Html.placeholder, Html.name_, Html.for_, Html.open_, Html.data, Html.style_attr,
    Html.disabled, Html.checked, Html.required, Html.readonly, Html.selected,

    Html.div, Html.span, Html.p, Html.a, Html.ul, Html.ol, Html.li,
    Html.h1, Html.h2, Html.h3, Html.h4, Html.h5, Html.h6,
    Html.header, Html.footer, Html.nav, Html.main_, Html.section, Html.article, Html.aside,

    Html.table, Html.thead, Html.tbody, Html.tfoot, Html.tr, Html.th, Html.td,
    Html.caption, Html.colgroup,
    Html.form, Html.label, Html.fieldset, Html.legend, Html.select, Html.option,
    Html.optgroup, Html.textarea, Html.button, Html.datalist, Html.output,
    Html.input, Html.img, Html.br, Html.hr, Html.meta, Html.link, Html.col,
    Html.source, Html.area, Html.base, Html.embed, Html.track, Html.wbr,
    Html.script, Html.style, Html.title, Html.head, Html.body,

    Html.node, Html.void, Html.text, Html.raw, Html.comment, Html.doctype,
    Html.fragment, Html.document, Html.navbar, Html.card
}
