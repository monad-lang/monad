// HtmlOptions tests: safe URLs, heading ids and the depth cap, none of which
// the CommonMark corpus exercises (it renders with URLs unfiltered, no ids
// and shallow input).
use init::string {}
use xml_html::html {Html.RenderOpts, Html.to_string_with}
use markdown::options {
    Markdown.HtmlOptions, Markdown.Options, Markdown.commonmark_options,
    Markdown.conformance_html_options, Markdown.default_html_options,
    Markdown.default_options,
}
use markdown::parse {Markdown.parse_with}
use markdown::html {Markdown.to_html_with, Markdown.heading_ids}
use markdown::types {Markdown.Block, Markdown.Document, Markdown.ListItem}

def render_opts : Html.RenderOpts :=
    { charset := false, annotate := false, xhtml_void := false }

def ids_html_opts : Markdown.HtmlOptions :=
    { allow_raw_html := false, safe_urls := true, heading_ids := true,
      heading_id_prefix := "" }

def unsafe_html_opts : Markdown.HtmlOptions :=
    { allow_raw_html := false, safe_urls := false, heading_ids := false,
      heading_id_prefix := "" }

def render_with (html : Markdown.HtmlOptions) (parse : Markdown.Options) (src : String) : String :=
    Html.to_string_with render_opts (Markdown.to_html_with html (Markdown.parse_with parse src))

/// The default options: GFM parsing, safe URLs on, ids off.
def render_default (src : String) : String :=
    render_with Markdown.default_html_options Markdown.default_options src

def render_ids (src : String) : String :=
    render_with ids_html_opts Markdown.default_options src

// ─── safe_urls ───

#[test]
def test_safe_urls_blocks_javascript : Bool :=
    String.beq (render_default "[x](javascript:alert(1))\n") "<p>x</p>\n"

#[test]
def test_safe_urls_blocks_vbscript_and_data : Bool :=
    Bool.and
        (String.beq (render_default "[x](vbscript:msgbox)\n") "<p>x</p>\n")
        (String.beq (render_default "[x](data:text/html,hi)\n") "<p>x</p>\n")

/// `data:image/*` is the documented exception.
#[test]
def test_safe_urls_allows_data_image : Bool :=
    String.beq (render_default "[x](data:image/png;base64,AA)\n")
        "<p><a href=\"data:image/png;base64,AA\">x</a></p>\n"

#[test]
def test_safe_urls_leaves_images_as_alt : Bool :=
    String.beq (render_default "![a](javascript:alert(1))\n") "<p>a</p>\n"

/// The conformance renderer turns filtering off, which is what lets the spec
/// fixture compare URLs verbatim.
#[test]
def test_conformance_options_do_not_filter : Bool :=
    String.beq
        (render_with Markdown.conformance_html_options Markdown.commonmark_options
            "[x](javascript:alert(1))\n")
        "<p><a href=\"javascript:alert(1)\">x</a></p>\n"

#[test]
def test_unsafe_urls_option_renders_the_link : Bool :=
    String.beq (render_with unsafe_html_opts Markdown.default_options "[x](javascript:a)\n")
        "<p><a href=\"javascript:a\">x</a></p>\n"

// ─── heading_ids ───

#[test]
def test_heading_ids_are_slugs : Bool :=
    String.beq (render_ids "# Hello World\n") "<h1 id=\"hello-world\">Hello World</h1>\n"

/// The slug comes from the heading's plain text, and repeats get `-1`, `-2`.
#[test]
def test_heading_ids_deduplicate : Bool :=
    String.beq (render_ids "# A *b* c!\n\n# A *b* c!\n")
        "<h1 id=\"a-b-c\">A <em>b</em> c!</h1>\n<h1 id=\"a-b-c-1\">A <em>b</em> c!</h1>\n"

#[test]
def test_heading_ids_are_off_by_default : Bool :=
    String.beq (render_default "# Hello\n") "<h1>Hello</h1>\n"

#[test]
def test_heading_ids_prefix : Bool :=
    let opts : Markdown.HtmlOptions :=
        { allow_raw_html := false, safe_urls := true, heading_ids := true,
          heading_id_prefix := "sec-" } in
    String.beq
        (Html.to_string_with render_opts
            (Markdown.to_html_with opts (Markdown.parse_with Markdown.default_options "# Hi\n")))
        "<h1 id=\"sec-hi\">Hi</h1>\n"

// ─── max_depth ───

#[partial]
def block_depth (blocks : List Markdown.Block) : I64 :=
    match blocks {
        List.empty => 0i64,
        List.cons b rest =>
            let here : I64 := block_node_depth b in
            let there : I64 := block_depth rest in
            if I64.lt here there then there else here
    }

#[partial]
def block_node_depth (b : Markdown.Block) : I64 :=
    match b {
        Markdown.Block.block_quote inner => I64.add 1i64 (block_depth inner),
        Markdown.Block.block_list _ _ items => I64.add 1i64 (item_depth items),
        _ => 1i64
    }

#[partial]
def item_depth (items : List Markdown.ListItem) : I64 :=
    match items {
        List.empty => 0i64,
        List.cons item rest =>
            let here : I64 := block_depth item.blocks in
            let there : I64 := item_depth rest in
            if I64.lt here there then there else here
    }

def doc_depth (d : Markdown.Document) : I64 := block_depth d.blocks

def depth_of (src : String) : I64 :=
    doc_depth (Markdown.parse_with Markdown.default_options src)

/// A long run of `>` markers stops nesting at `max_depth` and the remainder
/// is text, so the input stays linear instead of growing an unbounded stack.
#[test]
def test_block_depth_is_capped : Bool :=
    let deep := String.concat (String.repeat ">" 500i64) " x\n" in
    I64.lt (depth_of deep) 65i64

#[test]
def test_shallow_documents_are_unaffected : Bool :=
    I64.beq (depth_of "> > > x\n") 4i64
