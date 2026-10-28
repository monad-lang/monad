/// Parser and renderer options, with the presets the plan pins.
///
/// Every literal spells every field. An omitted field is filled positionally
/// (which shifts the fields after it), and a constructor-valued default
/// (`true`) cannot be lowered by the Rust host at all -- so the `:=` defaults
/// below document intent for outside callers while this tree always names
/// them.
pub struct Markdown.Options {
    gfm_tables : Bool := true,
    gfm_task_lists : Bool := true,
    gfm_strikethrough : Bool := true,
    gfm_autolinks : Bool := true,
    frontmatter : Bool := false,
    max_depth : I64 := 64
}

pub struct Markdown.HtmlOptions {
    allow_raw_html : Bool := false,
    safe_urls : Bool := true,
    heading_ids : Bool := false,
    heading_id_prefix : String := ""
}

/// The default: CommonMark plus GFM essentials, frontmatter off.
///
/// Frontmatter is opt-in because Weaver renders arbitrary model output, and
/// a reply that happens to start with `---` must not lose its middle.
pub def Markdown.default_options : Markdown.Options :=
    { gfm_tables := true, gfm_task_lists := true, gfm_strikethrough := true,
      gfm_autolinks := true, frontmatter := false, max_depth := 64 }

/// Strict CommonMark 0.31.2: every GFM extension off.
pub def Markdown.commonmark_options : Markdown.Options :=
    { gfm_tables := false, gfm_task_lists := false, gfm_strikethrough := false,
      gfm_autolinks := false, frontmatter := false, max_depth := 64 }

/// Site-generator shape: GFM on, frontmatter recognised.
pub def Markdown.site_options : Markdown.Options :=
    { gfm_tables := true, gfm_task_lists := true, gfm_strikethrough := true,
      gfm_autolinks := true, frontmatter := true, max_depth := 64 }

pub def Markdown.default_html_options : Markdown.HtmlOptions :=
    { allow_raw_html := false, safe_urls := true, heading_ids := false,
      heading_id_prefix := "" }

/// What the CommonMark conformance harness renders with: verbatim HTML and
/// no URL filtering, because the spec's expected output has both.
pub def Markdown.conformance_html_options : Markdown.HtmlOptions :=
    { allow_raw_html := true, safe_urls := false, heading_ids := false,
      heading_id_prefix := "" }
