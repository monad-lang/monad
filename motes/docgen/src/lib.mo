/// docgen: API reference pages for the motes, generated from their sources.
///
/// The extraction half of `monad doc`; acorn's `Site.write_pages` is the
/// rendering half. `extract.mo` reads a mote's sources through the
/// compiler's own declaration ranges, `model.mo` holds the page model, and
/// `render.mo` turns the model into one small site per mote (`<mote>/`) -- in the
/// chrome and stylesheet `style.mo` supplies, so the reference is styled
/// wherever it is written (the site, or a bare `monad doc`).
pub use lib::model {DocItem, DocModule, DocMote, DocMote.public_only}
pub use lib::gen {DocGen.build}
pub use lib::extract {DocExtract.extract_mote, DocExtract.extract_source, DocExtract.extract_source_as, module_of_file}
pub use lib::render {
    DocRender.anchor_of, DocRender.css_page, DocRender.css_path, DocRender.page_path,
    DocRender.mote_pages, DocRender.module_page, DocRender.hub_page, DocRender.nav_modules,
    DocRender.mote_home_page, DocRender.mote_home_path, DocRender.mote_site,
    DocRender.mote_of_module, kind_class, module_short, root_for, NavModule,
}
pub use lib::style {Style.api_css}
