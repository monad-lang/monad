// oak_ui's library root -- bare `use oak_ui` resolves here.
//
// Explicit re-exports (no globs), following oak's lib.mo.

pub use lib::vocab {
    Ui.Tone, Ui.Size, Ui.Variant, Ui.Align, Ui.Opt, Ui.Style,
    Ui.Tone.slug, Ui.Tone.all, Ui.Size.slug, Ui.Variant.slug, Ui.Align.slug,
    Ui.Style.default, Ui.resolve, Ui.resolve_from, Ui.class_names,
    Ui.neutral, Ui.primary, Ui.success, Ui.warning, Ui.danger, Ui.info,
    Ui.small, Ui.medium, Ui.large,
    Ui.solid, Ui.soft, Ui.outline, Ui.ghost, Ui.plain,
    Ui.full, Ui.busy, Ui.inactive, Ui.wrapping,
    Ui.gap, Ui.cols, Ui.align, Ui.justify, Ui.cls,
}

pub use lib::theme {
    Ui.Theme, Ui.Theme.light, Ui.Theme.dark, Ui.Theme.tokens, Ui.Theme.declarations,
    Ui.Theme.css_vars, Ui.Theme.css_auto,
}

pub use lib::css {
    Ui.css_base, Ui.css_reset, Ui.css_layout, Ui.css_typography,
    Ui.css_all, Ui.stylesheet, Ui.stylesheet_auto,
}

pub use lib::base {
    Ui.root_attrs, Ui.tone_mod, Ui.size_mod, Ui.gap_class, Ui.align_class, Ui.justify_class,
    Ui.style_tag, Ui.style_tag_auto,
}

pub use lib::layout {
    Ui.stack, Ui.row, Ui.cluster, Ui.grid, Ui.container, Ui.center, Ui.spacer, Ui.divider,
    Ui.app_shell,
}

pub use lib::typography {
    Ui.heading, Ui.text, Ui.muted, Ui.inline, Ui.code, Ui.code_block, Ui.kbd, Ui.link,
}
