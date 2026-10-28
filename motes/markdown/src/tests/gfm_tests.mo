// GFM goldens: tables (and the options-off behaviour of every extension).
use lib::tests::render {Markdown.render, Markdown.render_gfm}

def gfm_is (src : String) (want : String) : Bool :=
    String.beq (Markdown.render_gfm src) want

def commonmark_is (src : String) (want : String) : Bool :=
    String.beq (Markdown.render src) want

// ─── Tables ───

#[test]
def test_table_basic : Bool :=
    gfm_is "| a | b |\n| --- | --- |\n| 1 | 2 |\n"
        "<table>\n<thead>\n<tr>\n<th>a</th>\n<th>b</th>\n</tr>\n</thead>\n<tbody>\n<tr>\n<td>1</td>\n<td>2</td>\n</tr>\n</tbody>\n</table>\n"

#[test]
def test_table_alignment : Bool :=
    gfm_is "| a | b | c |\n| :- | :-: | -: |\n"
        "<table>\n<thead>\n<tr>\n<th align=\"left\">a</th>\n<th align=\"center\">b</th>\n<th align=\"right\">c</th>\n</tr>\n</thead>\n<tbody>\n</tbody>\n</table>\n"

#[test]
def test_table_without_outer_pipes : Bool :=
    gfm_is "a | b\n--- | ---\n1 | 2\n"
        "<table>\n<thead>\n<tr>\n<th>a</th>\n<th>b</th>\n</tr>\n</thead>\n<tbody>\n<tr>\n<td>1</td>\n<td>2</td>\n</tr>\n</tbody>\n</table>\n"

#[test]
def test_table_rows_are_ragged : Bool :=
    gfm_is "| a | b |\n| --- | --- |\n| 1 |\n| 1 | 2 | 3 |\n"
        "<table>\n<thead>\n<tr>\n<th>a</th>\n<th>b</th>\n</tr>\n</thead>\n<tbody>\n<tr>\n<td>1</td>\n<td></td>\n</tr>\n<tr>\n<td>1</td>\n<td>2</td>\n</tr>\n</tbody>\n</table>\n"

#[test]
def test_table_cell_count_must_match : Bool :=
    gfm_is "| a | b |\n| --- |\n"
        "<p>| a | b |\n| --- |</p>\n"

/// An escaped pipe stays in the cell; a pipe inside a code span does not split.
#[test]
def test_table_escaped_pipe : Bool :=
    gfm_is "| a | b |\n| --- | --- |\n| x \\| y | `p | q` |\n"
        "<table>\n<thead>\n<tr>\n<th>a</th>\n<th>b</th>\n</tr>\n</thead>\n<tbody>\n<tr>\n<td>x | y</td>\n<td><code>p | q</code></td>\n</tr>\n</tbody>\n</table>\n"

/// Without a pipe, `foo` over `---` is a setext heading, not a table.
#[test]
def test_table_needs_a_pipe : Bool :=
    gfm_is "foo\n---\nbar\n" "<h2>foo</h2>\n<p>bar</p>\n"

#[test]
def test_tables_off_under_commonmark : Bool :=
    commonmark_is "| a | b |\n| --- | --- |\n| 1 | 2 |\n" "<p>| a | b |\n| --- | --- |\n| 1 | 2 |</p>\n"

// ─── Task lists ───

#[test]
def test_task_list : Bool :=
    gfm_is "- [ ] foo\n- [x] bar\n"
        "<ul>\n<li><input type=\"checkbox\" disabled=\"\" /> foo</li>\n<li><input type=\"checkbox\" checked=\"\" disabled=\"\" /> bar</li>\n</ul>\n"

#[test]
def test_task_list_capital_x : Bool :=
    gfm_is "- [X] done\n"
        "<ul>\n<li><input type=\"checkbox\" checked=\"\" disabled=\"\" /> done</li>\n</ul>\n"

#[test]
def test_task_lists_off_under_commonmark : Bool :=
    commonmark_is "- [ ] foo\n" "<ul>\n<li>[ ] foo</li>\n</ul>\n"

/// Only the first paragraph's leading marker counts.
#[test]
def test_task_marker_in_second_paragraph_is_text : Bool :=
    gfm_is "- a\n\n  [ ] b\n" "<ul>\n<li>\n<p>a</p>\n<p>[ ] b</p>\n</li>\n</ul>\n"

// ─── Strikethrough ───

#[test]
def test_strikethrough : Bool :=
    gfm_is "~~a~~\n" "<p><del>a</del></p>\n"

#[test]
def test_single_tilde_is_text : Bool :=
    gfm_is "~a~\n" "<p>~a~</p>\n"

#[test]
def test_strikethrough_inside_emphasis : Bool :=
    gfm_is "*a ~~b~~ c*\n" "<p><em>a <del>b</del> c</em></p>\n"

#[test]
def test_strikethrough_off_under_commonmark : Bool :=
    commonmark_is "~~a~~\n" "<p>~~a~~</p>\n"

// ─── Bare autolinks ───

#[test]
def test_bare_www : Bool :=
    gfm_is "visit www.example.com now\n"
        "<p>visit <a href=\"http://www.example.com\">www.example.com</a> now</p>\n"

#[test]
def test_bare_https_trims_trailing_period : Bool :=
    gfm_is "see https://example.com/a?b=c.\n"
        "<p>see <a href=\"https://example.com/a?b=c\">https://example.com/a?b=c</a>.</p>\n"

#[test]
def test_bare_email : Bool :=
    gfm_is "mail foo@example.com\n"
        "<p>mail <a href=\"mailto:foo@example.com\">foo@example.com</a></p>\n"

/// A balanced paren stays in the URL; an unbalanced one does not.
#[test]
def test_bare_url_balanced_paren : Bool :=
    gfm_is "(see https://example.com/Foo_(bar))\n"
        "<p>(see <a href=\"https://example.com/Foo_(bar)\">https://example.com/Foo_(bar)</a>)</p>\n"

#[test]
def test_bare_autolinks_off_under_commonmark : Bool :=
    commonmark_is "visit www.example.com now\n" "<p>visit www.example.com now</p>\n"
