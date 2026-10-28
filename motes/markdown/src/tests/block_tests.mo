// Block-level tests: leaf blocks and their exact cmark formatting.
use lib::tests::render {Markdown.render, Markdown.render_default}
use lib::parse {Markdown.parse_with, Markdown.split_frontmatter}
use lib::types {
    Markdown.Document, Markdown.FrontFormat, Markdown.FrontSplit, Markdown.Frontmatter,
}
use lib::options {Markdown.site_options}

def is (src : String) (want : String) : Bool :=
    String.beq (Markdown.render src) want

// ─── Paragraphs ───

#[test]
def test_paragraph : Bool :=
    is "hello\n" "<p>hello</p>\n"

#[test]
def test_two_paragraphs : Bool :=
    is "a\n\nb\n" "<p>a</p>\n<p>b</p>\n"

#[test]
def test_paragraph_continuation_joins_lines : Bool :=
    is "aaa\nbbb\n" "<p>aaa\nbbb</p>\n"

#[test]
def test_paragraph_strips_leading_spaces : Bool :=
    is "aaa\n   bbb\n" "<p>aaa\nbbb</p>\n"

#[test]
def test_paragraph_hard_break : Bool :=
    is "aaa  \nbbb\n" "<p>aaa<br />\nbbb</p>\n"

#[test]
def test_paragraph_backslash_hard_break : Bool :=
    is "aaa\\\nbbb\n" "<p>aaa<br />\nbbb</p>\n"

#[test]
def test_empty_input_is_empty : Bool :=
    is "" ""

/// CommonMark ends a line at `\n`, `\r` or `\r\n`; the next line continues
/// the paragraph with a soft break, so the CR never reaches the text.
#[test]
def test_lone_cr_ends_a_line : Bool :=
    is "a\rb\n" "<p>a\nb</p>\n"

#[test]
def test_crlf_ends_a_line : Bool :=
    is "a\r\nb\r\n" "<p>a\nb</p>\n"

#[test]
def test_blank_lines_only : Bool :=
    is "\n\n\n" ""

// ─── ATX headings ───

#[test]
def test_atx_levels : Bool :=
    is "# a\n## b\n### c\n" "<h1>a</h1>\n<h2>b</h2>\n<h3>c</h3>\n"

#[test]
def test_atx_closing_sequence : Bool :=
    is "## foo ##\n" "<h2>foo</h2>\n"

#[test]
def test_atx_closing_sequence_needs_space : Bool :=
    is "## foo##\n" "<h2>foo##</h2>\n"

#[test]
def test_atx_seven_hashes_is_a_paragraph : Bool :=
    is "####### foo\n" "<p>####### foo</p>\n"

#[test]
def test_atx_needs_space_after_hashes : Bool :=
    is "#5 bolt\n" "<p>#5 bolt</p>\n"

#[test]
def test_atx_empty : Bool :=
    is "#\n" "<h1></h1>\n"

#[test]
def test_atx_four_space_indent_is_code : Bool :=
    is "    # foo\n" "<pre><code># foo\n</code></pre>\n"

// ─── Setext headings ───

#[test]
def test_setext_level_one : Bool :=
    is "foo\n===\n" "<h1>foo</h1>\n"

#[test]
def test_setext_level_two : Bool :=
    is "foo\n---\n" "<h2>foo</h2>\n"

#[test]
def test_setext_multiline : Bool :=
    is "foo\nbar\n---\n" "<h2>foo\nbar</h2>\n"

#[test]
def test_thematic_break_without_paragraph : Bool :=
    is "---\n" "<hr />\n"

// ─── Thematic breaks ───

#[test]
def test_thematic_variants : Bool :=
    is "***\n___\n" "<hr />\n<hr />\n"

#[test]
def test_thematic_spaced : Bool :=
    is " - - -\n" "<hr />\n"

#[test]
def test_thematic_two_stars_is_a_paragraph : Bool :=
    is "**\n" "<p>**</p>\n"

#[test]
def test_thematic_interrupts_paragraph : Bool :=
    is "foo\n***\nbar\n" "<p>foo</p>\n<hr />\n<p>bar</p>\n"

// ─── Indented code ───

#[test]
def test_indented_code : Bool :=
    is "    a simple\n      indented code block\n"
        "<pre><code>a simple\n  indented code block\n</code></pre>\n"

#[test]
def test_indented_code_internal_blank_line : Bool :=
    is "    chunk1\n\n    chunk2\n" "<pre><code>chunk1\n\nchunk2\n</code></pre>\n"

#[test]
def test_indented_code_cannot_interrupt_a_paragraph : Bool :=
    is "foo\n    bar\n" "<p>foo\nbar</p>\n"

#[test]
def test_indented_code_trailing_blank_lines_are_stripped : Bool :=
    is "    foo\n\n\n" "<pre><code>foo\n</code></pre>\n"

// ─── Fenced code ───

#[test]
def test_fenced_code : Bool :=
    is "```\nfoo\n```\n" "<pre><code>foo\n</code></pre>\n"

#[test]
def test_fenced_code_info_string : Bool :=
    is "```monad\ndef x := 1\n```\n"
        "<pre><code class=\"language-monad\">def x := 1\n</code></pre>\n"

#[test]
def test_fenced_code_unclosed_runs_to_eof : Bool :=
    is "```\nfoo\n" "<pre><code>foo\n</code></pre>\n"

#[test]
def test_fenced_code_tilde : Bool :=
    is "~~~\nfoo\n~~~\n" "<pre><code>foo\n</code></pre>\n"

#[test]
def test_fence_closing_must_be_long_enough : Bool :=
    is "````\nfoo\n```\n" "<pre><code>foo\n```\n</code></pre>\n"

#[test]
def test_fence_keeps_blank_lines : Bool :=
    is "```\na\n\nb\n```\n" "<pre><code>a\n\nb\n</code></pre>\n"

/// A backtick fence whose info string contains a backtick is not a fence at
/// all, so the line is an ordinary paragraph line (`a closing fence on a
/// later line would still interrupt it).
#[test]
def test_fence_backtick_info_may_not_contain_backtick : Bool :=
    is "``` a`b\nfoo\n" "<p>``` a`b\nfoo</p>\n"

// ─── Escapes and entities in text ───

#[test]
def test_backslash_escape : Bool :=
    is "\\*not emphasis\\*\n" "<p>*not emphasis*</p>\n"

#[test]
def test_backslash_before_letter_is_literal : Bool :=
    is "\\a\n" "<p>\\a</p>\n"

#[test]
def test_numeric_character_reference : Bool :=
    is "&#35;\n" "<p>#</p>\n"

#[test]
def test_hex_character_reference : Bool :=
    is "&#x41;\n" "<p>A</p>\n"

#[test]
def test_named_character_reference : Bool :=
    is "&amp;\n" "<p>&amp;</p>\n"

#[test]
def test_unknown_named_reference_is_literal : Bool :=
    is "&nope;\n" "<p>&amp;nope;</p>\n"

// ─── Frontmatter ───

def front_literal_of (split : Markdown.FrontSplit) : String :=
    match split.front {
        Option.some fm => fm.literal,
        Option.none => "<none>"
    }

def front_body_of (split : Markdown.FrontSplit) : String := split.body

def is_yaml (fm : Markdown.Frontmatter) : Bool :=
    match fm.format {
        Markdown.FrontFormat.front_yaml => true,
        Markdown.FrontFormat.front_toml => false
    }

def front_has_yaml (split : Markdown.FrontSplit) : Bool :=
    match split.front {
        Option.some fm => is_yaml fm,
        Option.none => false
    }

#[test]
def test_split_frontmatter_yaml : Bool :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter "---\ntitle: x\n---\nbody\n" in
    Bool.and (front_has_yaml split)
        (Bool.and (String.beq (front_literal_of split) "title: x")
            (String.beq (front_body_of split) "body"))

#[test]
def test_split_frontmatter_toml : Bool :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter "+++\na = 1\n+++\nbody\n" in
    Bool.and (Bool.not (front_has_yaml split))
        (Bool.and (String.beq (front_literal_of split) "a = 1")
            (String.beq (front_body_of split) "body"))

/// Without a closing delimiter the input is ordinary Markdown.
#[test]
def test_split_frontmatter_needs_a_close : Bool :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter "---\ntitle: x\n" in
    Bool.and (String.beq (front_literal_of split) "<none>")
        (String.beq (front_body_of split) "---\ntitle: x\n")

#[test]
def test_frontmatter_is_off_by_default : Bool :=
    String.beq (Markdown.render_default "---\ntitle: x\n---\n\nbody\n")
        "<hr />\n<h2>title: x</h2>\n<p>body</p>\n"

#[test]
def test_site_options_strip_frontmatter : Bool :=
    let d : Markdown.Document := Markdown.parse_with Markdown.site_options "---\ntitle: x\n---\n\nbody\n" in
    match d.front {
        Option.some _ => String.beq (Markdown.render_default "body\n") "<p>body</p>\n",
        Option.none => false
    }
