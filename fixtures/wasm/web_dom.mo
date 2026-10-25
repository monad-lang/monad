// The `web_wasm` DOM surface, end to end: mount a text node under the
// root, then exercise the read-only introspection (nodeType, lowercase
// tagName, form value, selector lookup, and the null handle).
//
// `scripts/check-wasm-target.sh` builds this for the web profile and
// `wasm/web/dom_smoke.mjs` instantiates it against the real
// `wasm/web/web_runtime.js` over a stub DOM, which is what proves the
// externs, the C wrappers and the JS host agree. The readings are written
// into the page as `span#report` so the harness asserts them from the DOM
// the program actually produced.

#![mote { name := "web_dom", deps := [web_wasm] }]

use web_wasm::dom {
  Dom.append, Dom.child, Dom.create, Dom.node_type, Dom.query, Dom.root, Dom.set_attr,
  Dom.tag_name, Dom.text_node, Dom.value,
}

/// `name=ok ` on success; a wrong reading says so in the page.
def report (label : String) (ok : Bool) : String :=
    if ok then String.concat label "=ok " else String.concat label "=FAIL "

def main : IO Unit := do {
    let root <- Dom.root;

    let block <- Dom.create "div";
    let _ <- Dom.set_attr block "id" "probe";
    let greeting <- Dom.text_node "hello from wasm";
    let _ <- Dom.append block greeting;
    let _ <- Dom.append root block;

    let field <- Dom.create "input";
    let _ <- Dom.set_attr field "id" "field";
    let _ <- Dom.set_attr field "value" "probe-value";
    let _ <- Dom.append block field;

    let tag <- Dom.tag_name block;
    let kind <- Dom.node_type block;
    let typed <- Dom.value field;
    let found <- Dom.query "#field";
    let queried <- Dom.value found;

    // Past the end: the null handle, which hydration uses as "no node".
    let missing <- Dom.child block 9i64;
    let missing_kind <- Dom.node_type missing;
    let missing_tag <- Dom.tag_name missing;

    let line : String := String.concat_list [
        report "tag" (String.beq tag "div"),
        report "type" (I64.beq kind 1i64),
        report "value" (String.beq typed "probe-value"),
        report "queried" (String.beq queried "probe-value"),
        report "nulltype" (I64.beq missing_kind 0i64),
        report "nulltag" (String.is_empty missing_tag),
    ];

    let report_node <- Dom.create "span";
    let _ <- Dom.set_attr report_node "id" "report";
    let summary <- Dom.text_node line;
    let _ <- Dom.append report_node summary;
    let _ <- Dom.append root report_node;
    return unit
}
