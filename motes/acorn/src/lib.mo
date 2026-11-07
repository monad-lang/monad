/// acorn: a static book/site generator, built on Oak.
///
/// The configuration-only builder is `Site.build`; a site supplies its own
/// chrome and extra pages through `Site.build_with` (see
/// `docs/site/monad_website`, which renders monad-lang.org).
pub use lib::config {SiteConfig, SiteConfig.parse, SiteConfig.with_out}
pub use lib::summary {NavEntry, NavChapter, Summary.parse, Summary.chapters, Summary.stem_of_link}
pub use lib::passes {Passes.chapter, Passes.node, Passes.rewrite_href, Passes.admonition_marker}
pub use lib::layout {
    PageSpec, BookNav, Shell, Shell.default, Layout.page, Layout.page_with, Layout.document,
    Layout.document_with, Layout.render, Layout.render_with, Layout.chapter_href,
}
pub use lib::toc {TocEntry, Toc.of_nodes, Toc.text_of}
pub use lib::site {
    ChapterPage, Built, Built.page, Built.pages, SiteSpec, Site.build, Site.build_with,
    Site.render_chapter, Site.render_chapter_with, Site.with_neighbours,
}
