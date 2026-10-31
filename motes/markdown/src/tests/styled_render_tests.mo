/// Goldens for the semantic styled-text renderer: block structure,
/// inline styles, and the plain-text form used for persistence.
use init::string {}
use markdown::parse {Markdown.parse}
use markdown::render {
    Markdown.to_lines, Markdown.to_plain_lines, Markdown.line_text,
    Markdown.style_name, Markdown.StyledLine, Markdown.StyledSpan,
}

/// Join rendered lines with `\n` so a golden is one comparable String
/// (generic `BEq (List A)` dispatch is unreliable in this tree).
#[partial]
def join_lines (ls : List String) : String :=
    match ls {
        List.empty => "",
        List.cons x rest =>
            match rest {
                List.empty => x,
                List.cons _ _ => String.concat x (String.concat "\n" (join_lines rest)),
            },
    }

#[partial]
def join_with (sep : String) (ls : List String) : String :=
    match ls {
        List.empty => "",
        List.cons x rest =>
            match rest {
                List.empty => x,
                List.cons _ _ => String.concat x (String.concat sep (join_with sep rest)),
            },
    }

def plain (src : String) : String :=
    join_lines (Markdown.to_plain_lines (Markdown.parse src))

def style_names (l : Markdown.StyledLine) : String :=
    join_with "," (List.map (fn (s : Markdown.StyledSpan) => Markdown.style_name s.style) l.spans)

def first_styles (src : String) : String :=
    match Markdown.to_lines (Markdown.parse src) {
        List.empty => "",
        List.cons l _ => style_names l,
    }

#[test]
def test_heading_drops_the_marker : Bool :=
    plain "# Title" == "Title"

#[test]
def test_heading_carries_the_heading_style : Bool :=
    first_styles "## Sub" == "heading"

#[test]
def test_paragraph_inline_styles : Bool :=
    plain "a **b** _c_ `d`" == "a b c d"
    && first_styles "a **b** _c_ `d`" == "plain,strong,plain,emphasis,plain,code"

#[test]
def test_fenced_code_keeps_indentation : Bool :=
    plain "```\nlet x := 1\n```" == "  let x := 1"

#[test]
def test_bullet_list_markers : Bool :=
    plain "- one\n- two" == "• one\n• two"

#[test]
def test_ordered_list_numbers : Bool :=
    plain "1. one\n2. two" == "1. one\n2. two"

#[test]
def test_block_quote_prefix : Bool :=
    plain "> quoted" == "│ quoted"

#[test]
def test_link_appends_its_destination : Bool :=
    plain "[label](https://example.com)" == "label <https://example.com>"

#[test]
def test_link_with_matching_destination_is_not_repeated : Bool :=
    plain "[x](x)" == "x"

#[test]
def test_table_has_borders_and_header_style : Bool :=
    plain "| a | b |\n|---|---|\n| 1 | 2 |"
        == "│ a │ b │\n────────────────────────────────────────\n│ 1 │ 2 │"
    && first_styles "| a | b |\n|---|---|\n| 1 | 2 |" == "table_border,table_head,table_border,table_head,table_border"

#[test]
def test_hard_break_is_a_new_line : Bool :=
    plain "one  \ntwo" == "one\ntwo"

#[test]
def test_soft_break_is_a_space : Bool :=
    plain "one\ntwo" == "one two"

#[test]
def test_nested_list_is_indented : Bool :=
    plain "- one\n  - two" == "• one\n  • two"
