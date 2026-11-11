/// docgen: API reference pages for the motes, generated from their sources.
///
/// The extraction half of `monad doc`; acorn's `Site.write_pages` is the
/// rendering half. `extract.mo` reads a mote's sources through the
/// compiler's own declaration ranges, `model.mo` holds the page model, and
/// `render.mo` turns the model into pages under `api/<mote>/`.
pub use lib::model {DocItem, DocModule, DocMote}
pub use lib::extract {DocExtract.extract_mote, DocExtract.extract_source}
