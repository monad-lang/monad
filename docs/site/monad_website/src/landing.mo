/// The monad-lang.org landing page (`/index.html`), ported from the Zola
/// templates (`docs/site/templates/{base,index}.html`).
///
/// It is its own document, styled by `landing.css` from the static tree, not
/// the book shell: a hero, the install box, the feature grid, a highlighted
/// example and the community links. Icons are `<use>` references into the
/// static `icons.svg` sprite, so the page carries no raw markup.
use oak::typed {Oak.Node, Oak.Attr}
use oak::elements {
    Html.a, Html.alt, Html.attr, Html.charset, Html.class_, Html.div, Html.document_with,
    Html.footer, Html.h1, Html.h2, Html.h3, Html.height, Html.href, Html.id_, Html.img,
    Html.lang, Html.link, Html.meta, Html.nav, Html.node, Html.p, Html.rel, Html.section,
    Html.span, Html.src, Html.style_attr, Html.text, Html.title, Html.width,
}
use fmt::highlight {Span, Highlight.css_class, Highlight.spans}
use acorn::config {SiteConfig}

def description : String :=
    "A purely functional, dependently typed systems programming language with LLVM native compilation."

def source_url : String := "https://tangled.org/monad-lang.org/monad"

def releases_url : String := "https://github.com/monad-lang/monad"

def head_nodes (cfg : SiteConfig) : List (Oak.Node Unit) :=
    [Html.meta [Html.charset "utf-8"],
        Html.meta [Html.attr "name" "viewport", Html.attr "content" "width=device-width, initial-scale=1"],
        Html.meta [Html.attr "name" "description", Html.attr "content" description],
        Html.title List.empty [Html.text (String.concat cfg.title " — Dependently Typed Systems Programming")],
        Html.link [Html.rel "icon", Html.href "favicon.svg"],
        Html.link [Html.rel "stylesheet", Html.href "landing.css"]]

/// An icon from the static sprite; `size` 0 leaves the size to CSS.
def icon (name : String) (size : I64) : Oak.Node Unit :=
    let dims : List (Oak.Attr Unit) := if size > 0 then [Html.width size, Html.height size] else List.empty in
    Html.node "svg" dims [Html.node "use" [Html.href (String.concat "icons.svg#icon-" name)] List.empty]

def docs_href (cfg : SiteConfig) (stem : String) : String :=
    String.concat cfg.book_dir (String.concat "/" (String.concat stem ".html"))

def link_to (href : String) (label : String) : Oak.Node Unit :=
    Html.a [Html.href href] [Html.text label]

def top_nav (cfg : SiteConfig) : Oak.Node Unit :=
    Html.nav List.empty
        [Html.div [Html.class_ ["logo"]]
            [Html.img [Html.src "logo.svg", Html.alt "Monad logo", Html.width 28, Html.height 28],
                Html.span List.empty [Html.text "Monad"]],
            Html.div [Html.class_ ["nav-links"]]
                [link_to "try/" "Try",
                    link_to (docs_href cfg "introduction") "Documentation",
                    link_to source_url "Source",
                    link_to "https://blog.monad-lang.org/" "Blog",
                    link_to "https://links.monad-lang.org" "Links",
                    link_to "https://monad-lang.zulipchat.com/" "Community"]]

def badge (color : String) (label : String) : Oak.Node Unit :=
    Html.span [Html.class_ ["badge"]]
        [Html.span [Html.class_ ["dot"], Html.style_attr (String.concat "background:var(--" (String.concat color ")"))] List.empty,
            Html.text (String.concat " " label)]

def button (cls : String) (href : String) (label : String) : Oak.Node Unit :=
    Html.a [Html.class_ ["btn", cls], Html.href href] [Html.text label]

def hero (cfg : SiteConfig) : Oak.Node Unit :=
    Html.section [Html.class_ ["hero"]]
        [Html.img [Html.src "logo.svg", Html.class_ ["logo-svg"], Html.alt "Monad logo", Html.width 100, Html.height 100],
            Html.h1 List.empty [Html.text "Monad"],
            Html.p [Html.class_ ["tagline"]]
                [Html.text "A purely functional, dependently typed systems programming language that compiles to native code through LLVM."],
            Html.div [Html.class_ ["badges"]]
                [badge "orange" "Alpha", badge "green" "Self-hosting", badge "accent" "LLVM native"],
            Html.div [Html.class_ ["cta-group"]]
                [button "btn-primary" "#install" "Get Started",
                    button "btn-secondary" "try/" "Try in your browser",
                    button "btn-secondary" (docs_href cfg "introduction") "Read the Docs"]]

/// One shell line as `(class, text)` pieces; `""` is unstyled.
def shell_piece (piece : Pair String String) : Oak.Node Unit :=
    match piece {
        Pair.pair cls text => styled cls text,
    }

def styled (cls : String) (text : String) : Oak.Node Unit :=
    if String.is_empty cls then Html.text text else Html.span [Html.class_ [cls]] [Html.text text]

def install_lines : List (Pair String String) :=
    [("comment", "# Install monadup (the Monad-written toolchain manager)"), ("", "\n"),
        ("cmd", "curl"), ("", " -fsSL https://monad-lang.org/install | "), ("cmd", "bash"), ("", "\n"),
        ("cmd", "export"), ("", " PATH="), ("str", "\"$HOME/.monad/bin:$PATH\""), ("", "\n\n"),
        ("comment", "# Install the latest nightly, check the toolchain, start a project"), ("", "\n"),
        ("cmd", "monadup"), ("", " default\n"),
        ("cmd", "monadup"), ("", " doctor\n"),
        ("cmd", "monadup"), ("", " new hello\n"),
        ("cmd", "cd"), ("", " hello && "), ("cmd", "monad"), ("", " run .")]

def install : Oak.Node Unit :=
    Html.section [Html.class_ ["install"], Html.id_ "install"]
        [Html.div [Html.class_ ["install-box"]]
            [Html.h3 List.empty [Html.text "Install with monadup"],
                Html.div [Html.class_ ["install-code"]] (List.map shell_piece install_lines)]]

/// A feature card's status: its CSS modifier and label.
def status_label (status : String) : String :=
    if String.beq status "realized" then "Available now"
    else if String.beq status "future" then "Future"
    else "In progress"

struct Feature {
    /// The sprite icon's name.
    glyph : String,
    title : String,
    text : String,
    /// `goal`, `future` or `realized` (the CSS modifier).
    status : String,
}

def feature_card (f : Feature) : Oak.Node Unit :=
    match f {
        { glyph, title, text, status } =>
            Html.div [Html.class_ ["feature-card"]]
                [Html.div [Html.class_ ["icon"]] [icon glyph 24],
                    Html.h3 List.empty [Html.text title],
                    Html.p List.empty [Html.text text],
                    Html.span [Html.class_ ["feature-status", status]]
                        [Html.span [Html.class_ ["dot"]] List.empty, Html.text (String.concat " " (status_label status))]],
    }

/// One card each, as an annotated def: the Rust host cannot infer a list
/// literal's element type when the elements are bare struct literals, with
/// or without an annotation on the list.
def zap_feature : Feature :=
    { glyph := "zap", title := "Optimized for LLMs and AI",
        text := "Monad's type system, compiler, syntax and tooling are designed to work well with AI coding assistants and automated development workflows.",
        status := "goal" }

def shield_feature : Feature :=
    { glyph := "shield", title := "Verifiable systems programming",
        text := "A cubical type system that lets you prove programs are correct at compile time, not just test them.",
        status := "goal" }

def layers_feature : Feature :=
    { glyph := "layers", title := "LLVM and MLIR support",
        text := "Compile to native binaries, GPUs, TPUs, and eventually QPUs through industry-standard compiler backends.",
        status := "future" }

def brackets_feature : Feature :=
    { glyph := "brackets", title := "Powerful macros and metaprogramming",
        text := "Write code that writes code. Derive boilerplate, extend the language, and build domain-specific abstractions.",
        status := "realized" }

def recycle_feature : Feature :=
    { glyph := "recycle", title := "Quantitative types",
        text := "Memory safety without a garbage collector, enforced at compile time through linear type annotations.",
        status := "future" }

def lambda_feature : Feature :=
    { glyph := "lambda", title := "General purpose and flexible",
        text := "Compile to the web via WASM, build for any platform, from servers to embedded devices.",
        status := "goal" }

def features : List Feature :=
    [zap_feature, shield_feature, layers_feature, brackets_feature, recycle_feature, lambda_feature]

def features_section : Oak.Node Unit :=
    Html.section [Html.class_ ["features"]]
        [Html.h2 List.empty [Html.text "Why Monad?"],
            Html.div [Html.class_ ["feature-grid"]] (List.map feature_card features)]

/// The showcase program, highlighted by `fmt` like every book example.
def hello_source : String :=
    "// A program is a native binary\nuse std::io {}\nopen IO {println}\n\n#[decreasing n]\ndef factorial (n : I64) : I64 :=\n    if n == 0\n    then 1\n    else n * factorial (n - 1)\n\ndef main (args : List String) : IO Unit :=\n    println (I64.to_string (factorial 5))"

def span_node (s : Span) : Oak.Node Unit :=
    match s {
        { cls, text } =>
            let c : String := Highlight.css_class cls in
            if String.is_empty c then Html.text text else Html.span [Html.class_ [c]] [Html.text text],
    }

def showcase : Oak.Node Unit :=
    Html.section [Html.class_ ["showcase"]]
        [Html.h2 List.empty [Html.text "Hello, Monad"],
            Html.div [Html.class_ ["code-block"]] (List.map span_node (Highlight.spans hello_source))]

def community_link (link : Pair String String) : Oak.Node Unit :=
    match link {
        Pair.pair name href => community_anchor name href,
    }

def community_anchor (name : String) (href : String) : Oak.Node Unit :=
    Html.a [Html.class_ ["community-link"], Html.href href] [icon (String.to_lowercase name) 0, Html.text name]

def community : Oak.Node Unit :=
    Html.section [Html.class_ ["community"], Html.id_ "community"]
        [Html.h2 List.empty [Html.text "Join the Community"],
            Html.p List.empty [Html.text "Monad is an open project. Come ask questions, share ideas, or contribute."],
            Html.div [Html.class_ ["community-links"]]
                (List.map community_link
                    [("Zulip", "https://monad-lang.zulipchat.com/"), ("Tangled", source_url), ("GitHub", releases_url),
                        ("Reddit", "https://www.reddit.com/r/monad_lang/"), ("Discord", "https://discord.gg/b5ZJ67TE")])]

def site_footer (cfg : SiteConfig) : Oak.Node Unit :=
    Html.footer List.empty
        [Html.p List.empty
            [Html.text "Monad is an open-source project hosted on ", link_to source_url "Tangled",
                Html.text " with releases on ", link_to releases_url "GitHub",
                Html.text ". · ", link_to (docs_href cfg "introduction") "Documentation",
                Html.text " · ", link_to (docs_href cfg "maturity") "Maturity Matrix"]]

def alpha_notice : Oak.Node Unit :=
    Html.div [Html.class_ ["alpha-notice"]]
        [Html.span List.empty
            [Html.text "Monad is in active development (Alpha). Features and APIs may change. Not recommended for production use."]]

/// The landing page, at the output root.
pub def Landing.page (cfg : SiteConfig) : Oak.Node Unit :=
    Html.document_with [Html.lang "en"] List.empty List.empty (head_nodes cfg)
        [top_nav cfg, alpha_notice, hero cfg, install, features_section, showcase, community, site_footer cfg]
