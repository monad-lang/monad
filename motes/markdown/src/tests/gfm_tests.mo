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
