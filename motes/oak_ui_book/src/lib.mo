// oak_ui_book's library root. Everything here is pure (no web externs), so
// the static generator and the tests run natively; `main.mo` adds the
// browser host.

pub use lib::story {
    Book.Knob, Book.Ctx, Book.Msg, Book.Story, Book.story, Book.Story.id, Book.Story.group, Book.Story.title,
    Book.Story.notes, Book.Story.knobs, Book.Story.render, Book.Knob.name, Book.Knob.default_value,
    Book.lookup, Book.lookup_or, Book.assoc, Book.ctx_for, Book.default_ctx, Book.parse_int,
    Book.text, Book.flag, Book.choice, Book.int, Book.tone_knob, Book.size_knob, Book.variant_knob,
    Book.knob_text, Book.knob_bool, Book.knob_int, Book.state, Book.state_bool, Book.state_int,
    Book.set, Book.action, Book.set_and_log, Book.setter, Book.bool_setter, Book.logger,
    Book.tone_opt, Book.size_opt, Book.variant_opt,
}

pub use lib::inspect {Book.attr_value, Book.pretty_html, Book.listeners, Book.a11y_lint}

pub use lib::app {
    Book.Model, Book.Effect, Book.init, Book.update, Book.view, Book.subscriptions, Book.program,
    Book.scoped, Book.log_limit, Book.css,
}

pub use lib::stories::all {Book.all_stories}

pub use lib::gallery {Book.stylesheet, Book.gallery_page, Book.story_page}
