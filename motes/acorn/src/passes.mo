/// Passes over a rendered chapter's `Html.Node` tree.
///
/// The markdown mote has no render hooks, so book-specific markup is applied
/// after rendering, on typed nodes (never on HTML text):
///
/// - a relative link to `foo.md` (with or without `#anchor`) points at the
///   rendered `foo.html`;
/// - a GFM admonition (`> [!WARNING]` …) becomes
///   `<div class="admonition warning">` with a title paragraph;
/// - a fenced block's info string (`monad,ignore`) splits into the language
///   (`<code class="language-monad">`) and its flags (`<pre class="ignore">`),
///   and a `monad` block's text becomes highlighted spans.
use xml_html::html {Html.Node, Html.Attr}
use std::list {List.intercalate}
use fmt::highlight {Span, Highlight.css_class, Highlight.spans}

/// A relative `.md` link → `.html`, keeping its `#fragment`. Absolute URLs,
/// root paths, bare fragments and other files are unchanged.
pub def Passes.rewrite_href (href : String) : String :=
    if String.contains href "://" || String.starts_with "/" href || String.starts_with "#" href || String.starts_with "mailto:" href
    then href
    else rewrite_relative href (String.find_last href "#")

def rewrite_relative (href : String) (hash : I64) : String :=
    let path : String := if hash < 0 then href else String.slice href 0 hash in
    let frag : String := if hash < 0 then "" else String.drop hash href in
    let n : I64 := String.length path in
    if String.ends_with path ".md"
    then String.concat (String.slice path 0 (n - 3)) (String.concat ".html" frag)
    else href

def rewrite_attr (a : Html.Attr) : Html.Attr :=
    match a {
        Html.Attr.attr name value =>
            if String.beq name "href" then Html.Attr.attr name (Passes.rewrite_href value) else Html.Attr.attr name value,
        Html.Attr.bool_attr name => Html.Attr.bool_attr name,
    }

/// The admonition kinds GitHub renders, with their display titles.
def admonition_title (kind : String) : Option String :=
    let k : String := String.to_lowercase kind in
    if String.beq k "note" then Option.some "Note"
    else if String.beq k "tip" then Option.some "Tip"
    else if String.beq k "important" then Option.some "Important"
    else if String.beq k "warning" then Option.some "Warning"
    else if String.beq k "caution" then Option.some "Caution"
    else Option.none

/// The index of the first `byte` in `s` at or after `i`, or -1.
// Ends: `i` grows toward the string's length, where `String.get` is none.
#[terminating]
def index_of_byte (s : String) (byte : U8) (i : I64) : I64 :=
    match String.get s i {
        Option.none => -1,
        Option.some b => if b == byte then i else index_of_byte s byte (i + 1),
    }

/// The marker's kind in text starting `[!KIND]`, and the text after it.
pub def Passes.admonition_marker (text : String) : Option (Pair String String) :=
    if String.starts_with "[!" text
    then marker_at text (index_of_byte text 93u8 2)
    else Option.none

def marker_at (text : String) (close : I64) : Option (Pair String String) :=
    if close < 0
    then Option.none
    else Option.some (Pair.pair (String.slice text 2 (close - 2)) (String.trim (String.drop (close + 1) text)))

def admonition_div (kind : String) (title : String) (rest : List Html.Node) : Html.Node :=
    Html.Node.node_element "div"
        [Html.Attr.attr "class" (String.concat "admonition " (String.to_lowercase kind))]
        (List.cons (Html.Node.node_element "p" [Html.Attr.attr "class" "admonition-title"] [Html.Node.node_text title]) rest)

/// The first paragraph with its marker text removed; dropped when nothing
/// else was in it.
def strip_marker (after : String) (more : List Html.Node) : List Html.Node :=
    if String.is_empty after
    then strip_leading_break more
    else [Html.Node.node_element "p" List.empty (List.cons (Html.Node.node_text after) more)]

/// A paragraph that was only the marker line may still hold a soft break.
def strip_leading_break (nodes : List Html.Node) : List Html.Node :=
    match nodes {
        List.empty => List.empty,
        List.cons n rest => [Html.Node.node_element "p" List.empty (List.cons n rest)],
    }

/// Rendered markup is an immutable tree: sharing a node shares pointers.
instance Copy Html.Node {
    def copy (n : Html.Node) : Pair Html.Node Html.Node := Pair.pair n n
}

/// A blockquote whose first paragraph opens with `[!KIND]` → an admonition;
/// anything else stays a blockquote.
def blockquote (children : List Html.Node) : Html.Node :=
    match drop_blank children {
        List.cons first rest => blockquote_first first rest,
        List.empty => plain_quote List.empty,
    }

/// Leading whitespace-only text (the newlines between block tags) dropped.
def drop_blank (nodes : List Html.Node) : List Html.Node :=
    match nodes {
        List.empty => List.empty,
        List.cons n rest => drop_blank_at n rest,
    }

// Mutual recursion with `drop_blank` on the list's own tail.
#[terminating]
def drop_blank_at (n : Html.Node) (rest : List Html.Node) : List Html.Node :=
    match n {
        Html.Node.node_text t =>
            if String.is_empty (String.trim t) then drop_blank rest else List.cons (Html.Node.node_text t) rest,
        _ => List.cons n rest,
    }

def blockquote_first (first : Html.Node) (rest : List Html.Node) : Html.Node :=
    match first {
        Html.Node.node_element tag attrs para =>
            if String.beq tag "p"
            then paragraph_marker attrs para rest
            else plain_quote (List.cons (Html.Node.node_element tag attrs para) rest),
        _ => plain_quote (List.cons first rest),
    }

def plain_quote (children : List Html.Node) : Html.Node :=
    Html.Node.node_element "blockquote" List.empty children

def paragraph_marker (attrs : List Html.Attr) (para : List Html.Node) (rest : List Html.Node) : Html.Node :=
    match para {
        List.cons head more => head_marker attrs head more rest,
        List.empty => plain_quote (List.cons (Html.Node.node_element "p" attrs List.empty) rest),
    }

def head_marker (attrs : List Html.Attr) (head : Html.Node) (more : List Html.Node) (rest : List Html.Node) : Html.Node :=
    match head {
        Html.Node.node_text t => text_marker attrs t more rest (Passes.admonition_marker t),
        _ => plain_quote (List.cons (Html.Node.node_element "p" attrs (List.cons head more)) rest),
    }

def text_marker (attrs : List Html.Attr) (t : String) (more : List Html.Node) (rest : List Html.Node) (marker : Option (Pair String String)) : Html.Node :=
    match marker {
        Option.some m => pair_marker attrs t more rest m,
        Option.none => plain_quote (List.cons (Html.Node.node_element "p" attrs (List.cons (Html.Node.node_text t) more)) rest),
    }

def pair_marker (attrs : List Html.Attr) (t : String) (more : List Html.Node) (rest : List Html.Node) (m : Pair String String) : Html.Node :=
    match m {
        Pair.pair kind after => kind_marker attrs t more rest kind after,
    }

def kind_marker (attrs : List Html.Attr) (t : String) (more : List Html.Node) (rest : List Html.Node) (kind : String) (after : String) : Html.Node :=
    match admonition_title kind {
        Option.some title => admonition_div kind title (List.append (strip_marker after more) rest),
        Option.none => plain_quote (List.cons (Html.Node.node_element "p" attrs (List.cons (Html.Node.node_text t) more)) rest),
    }

/// Apply every pass to one node, children first.
pub def Passes.node (n : Html.Node) : Html.Node :=
    match n {
        Html.Node.node_element tag attrs children =>
            element tag (List.map rewrite_attr attrs) (List.map Passes.node children),
        Html.Node.node_void tag attrs => Html.Node.node_void tag (List.map rewrite_attr attrs),
        Html.Node.node_fragment children => Html.Node.node_fragment (List.map Passes.node children),
        _ => n,
    }

def element (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
    if String.beq tag "blockquote" then blockquote children
    else if String.beq tag "pre" then pre_block attrs children
    else Html.Node.node_element tag attrs children

/// A fence's info string, split at its first comma: the language and the
/// comma-separated flags after it.
pub struct FenceInfo {
    lang : String,
    flags : List String,
}

/// `monad,ignore` → `{ lang := "monad", flags := ["ignore"] }`.
pub def Passes.fence_info (info : String) : FenceInfo :=
    match split_commas info {
        List.empty => { lang := "", flags := List.empty },
        List.cons lang flags => { lang := lang, flags := flags },
    }

#[terminating]
def split_commas (s : String) : List String :=
    let i : I64 := index_of_byte s 44u8 0 in
    if i < 0
    then [s]
    else List.cons (String.slice s 0 i) (split_commas (String.drop (i + 1) s))

/// The fence's info string from the `<code>`'s `language-…` class.
def code_info (attrs : List Html.Attr) : String :=
    match attrs {
        List.empty => "",
        List.cons a rest => attr_info a rest,
    }

// Mutual recursion with `code_info` on the list's own tail.
#[terminating]
def attr_info (a : Html.Attr) (rest : List Html.Attr) : String :=
    match a {
        Html.Attr.attr name value =>
            if String.beq name "class" && String.starts_with "language-" value
            then String.drop 9 value
            else code_info rest,
        Html.Attr.bool_attr _ => code_info rest,
    }

/// `<pre><code class="language-INFO">text</code></pre>`, the only shape the
/// markdown renderer emits for a fence; anything else is left alone.
def pre_block (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
    match children {
        List.cons first rest => pre_first attrs first rest,
        List.empty => Html.Node.node_element "pre" attrs List.empty,
    }

def pre_first (attrs : List Html.Attr) (first : Html.Node) (rest : List Html.Node) : Html.Node :=
    match rest {
        List.empty => pre_code attrs first,
        List.cons r more => Html.Node.node_element "pre" attrs (List.cons first (List.cons r more)),
    }

def pre_code (attrs : List Html.Attr) (code : Html.Node) : Html.Node :=
    match code {
        Html.Node.node_element tag cattrs body =>
            if String.beq tag "code"
            then fenced (Passes.fence_info (code_info cattrs)) body
            else Html.Node.node_element "pre" attrs [Html.Node.node_element tag cattrs body],
        _ => Html.Node.node_element "pre" attrs [code],
    }

def fenced (info : FenceInfo) (body : List Html.Node) : Html.Node :=
    match info {
        { lang, flags } =>
            let pre_attrs : List Html.Attr :=
                if List.is_empty flags then List.empty else [Html.Attr.attr "class" (List.intercalate " " flags)] in
            let code_attrs : List Html.Attr :=
                if String.is_empty lang then List.empty else [Html.Attr.attr "class" (String.concat "language-" lang)] in
            Html.Node.node_element "pre" pre_attrs
                [Html.Node.node_element "code" code_attrs (code_body lang body)],
    }

/// A `monad` block's text as highlighted spans; other languages unchanged.
def code_body (lang : String) (body : List Html.Node) : List Html.Node :=
    if String.beq lang "monad" then highlight_body body else body

def highlight_body (body : List Html.Node) : List Html.Node :=
    match body {
        List.cons first rest => highlight_first first rest,
        List.empty => List.empty,
    }

def highlight_first (first : Html.Node) (rest : List Html.Node) : List Html.Node :=
    match rest {
        List.empty => highlight_text first,
        List.cons r more => List.cons first (List.cons r more),
    }

def highlight_text (n : Html.Node) : List Html.Node :=
    match n {
        Html.Node.node_text src => List.map span_node (Highlight.spans src),
        _ => [n],
    }

def span_node (s : Span) : Html.Node :=
    match s {
        { cls, text } =>
            let c : String := Highlight.css_class cls in
            if String.is_empty c
            then Html.Node.node_text text
            else Html.Node.node_element "span" [Html.Attr.attr "class" c] [Html.Node.node_text text],
    }

/// Apply every pass to a rendered chapter body.
pub def Passes.chapter (nodes : List Html.Node) : List Html.Node :=
    List.map Passes.node nodes
