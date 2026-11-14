/// The API reference's stylesheet, as a Monad string.
///
/// It lives here rather than in an assets tree because `monad doc` must be
/// self-sufficient: run in any directory, it writes `docgen.css` at the
/// docs base beside the pages it generates, so the reference it produces is
/// styled without the site's copy step. The site build writes the same file
/// under its own base (`motes/docs/docgen.css`).
///
/// The palette and type scale are the book's (`motes/acorn/assets/acorn.css`
/// and `docs/site/static/landing.css` share it), so a reader crossing from a
/// chapter to a module page sees no seam: same background, same accent, same
/// monospace stack. What it adds is what a *reference* needs and prose does
/// not -- per-declaration cards, kind badges coloured like the highlighter's
/// spans, and the module sidebar.
///
/// A raw string (`r#"…"#`) because CSS is full of `#` hex colours and
/// backslashes; the delimiter is chosen so no CSS we write can close it.
pub def Style.api_css : String := r#"/* docgen: the API reference stylesheet. The palette and type scale are the
   book's (acorn.css), so the reference and the chapters read as one site. */
:root {
  --bg: #0d1117;
  --bg-card: #161b22;
  --bg-hover: #1c2330;
  --bg-code: #010409;
  --border: #30363d;
  --text: #e6edf3;
  --text-muted: #8b949e;
  --accent: #58a6ff;
  --accent-bright: #79c0ff;
  --accent-dim: #1f6feb;
  --green: #3fb950;
  --orange: #d29922;
  --red: #f85149;
  --purple: #bc8cff;
  --radius: 8px;
  --sidebar: 260px;
  --content: 860px;
  color-scheme: dark;
  --mono: ui-monospace, SFMono-Regular, "SF Mono", Menlo, Consolas, monospace;
}

* { box-sizing: border-box; }

body {
  margin: 0;
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
  background: var(--bg);
  color: var(--text);
  line-height: 1.65;
  -webkit-font-smoothing: antialiased;
}

a { color: var(--accent); text-decoration: none; }
a:hover { color: var(--accent-bright); text-decoration: underline; }

code { font-family: var(--mono); font-size: 0.9em; }
:not(pre) > code {
  padding: 0.15em 0.35em;
  background: var(--bg-card);
  border: 1px solid var(--border);
  border-radius: 5px;
}

/* ---- Header ---- */
.site-header {
  position: sticky;
  top: 0;
  z-index: 10;
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 16px;
  padding: 12px 24px;
  background: var(--bg);
  border-bottom: 1px solid var(--border);
}
.site-header .brand { color: var(--text); font-weight: 600; font-size: 17px; }
.site-header .brand:hover { text-decoration: none; }
.site-nav { display: flex; gap: 20px; font-size: 14px; }
.site-nav a { color: var(--text-muted); }
.site-nav a:hover { color: var(--text); text-decoration: none; }

/* ---- Layout ----
   A module page is `main.content > div.api > (nav.api-sidebar, div.api-main)`,
   so the content region carries the grid and `div.api-main` is the readable
   column. The hub has no sidebar and uses `div.hub` instead. */
main.content {
  width: 100%;
  max-width: none;
  margin: 0;
  padding: 0;
  min-width: 0;
}

.api {
  display: grid;
  grid-template-columns: var(--sidebar) minmax(0, 1fr);
  align-items: start;
  min-height: calc(100vh - 50px);
}

.api-main, .hub {
  width: 100%;
  max-width: var(--content);
  min-width: 0;
  margin: 0 auto;
  padding: 32px 24px 64px;
}

.api-sidebar {
  position: sticky;
  top: 50px;
  align-self: start;
  max-height: calc(100vh - 50px);
  overflow-y: auto;
  padding: 24px 12px 40px 20px;
  border-right: 1px solid var(--border);
  font-size: 14px;
  scrollbar-width: thin;
  scrollbar-color: var(--border) transparent;
}
.api-sidebar .mote-name {
  margin: 0 0 14px;
  color: var(--text);
  font-size: 15px;
  font-weight: 600;
  font-family: var(--mono);
  overflow-wrap: anywhere;
}
.api-sidebar .mote-name a { color: var(--text); }
.api-sidebar .mote-name a:hover { color: var(--accent-bright); text-decoration: none; }
.api-sidebar .nav-label {
  margin: 0 0 6px;
  color: var(--text-muted);
  font-size: 12px;
  font-weight: 600;
  letter-spacing: 0.06em;
  text-transform: uppercase;
}
.api-sidebar ol { list-style: none; margin: 0; padding: 0; }
.api-sidebar li a {
  display: block;
  padding: 4px 10px;
  border-radius: 6px;
  color: var(--text);
  font-family: var(--mono);
  font-size: 13px;
  overflow-wrap: anywhere;
}
.api-sidebar li a:hover { background: var(--bg-hover); text-decoration: none; }
.api-sidebar li.current a {
  background: var(--bg-card);
  color: var(--accent-bright);
  font-weight: 600;
}

/* A module with no declarations of its own: said, not left blank. */
.no-items { color: var(--text-muted); font-style: italic; }

/* ---- Module header ---- */
.module-head { margin-bottom: 2em; }
.module-head h1 {
  font-size: 1.9em;
  line-height: 1.25;
  margin: 0 0 6px;
  letter-spacing: -0.02em;
  font-family: var(--mono);
  font-weight: 600;
  overflow-wrap: anywhere;
}
.module-head .module-source {
  color: var(--text-muted);
  font-size: 13px;
  font-family: var(--mono);
}
.module-doc {
  margin-bottom: 2em;
  padding-bottom: 1.5em;
  border-bottom: 1px solid var(--border);
}

/* ---- Prose (a module or declaration doc comment) ---- */
main.content h2 { font-size: 1.4em; margin: 1.8em 0 0.6em; padding-bottom: 0.3em; border-bottom: 1px solid var(--border); }
main.content h3 { font-size: 1.2em; margin: 1.5em 0 0.5em; }
main.content h4 { font-size: 1em; margin: 1.3em 0 0.4em; }
main.content p, main.content ul, main.content ol, main.content table,
main.content pre, main.content blockquote { margin: 0 0 1em; }
main.content ul, main.content ol { padding-left: 1.6em; }
main.content li + li { margin-top: 0.25em; }
main.content img { max-width: 100%; }
main.content hr { border: 0; border-top: 1px solid var(--border); margin: 2em 0; }
main.content blockquote {
  margin-left: 0;
  padding: 0.2em 1em;
  color: var(--text-muted);
  border-left: 3px solid var(--border);
}
main.content table { border-collapse: collapse; display: block; overflow-x: auto; }
main.content th, main.content td { padding: 6px 12px; border: 1px solid var(--border); text-align: left; }
main.content th { background: var(--bg-card); }

pre {
  padding: 14px 16px;
  overflow-x: auto;
  background: var(--bg-code);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  line-height: 1.5;
  font-family: var(--mono);
}
pre code { font-size: 13.5px; }

/* Highlight classes (the book's, so a signature is coloured like a chapter). */
.kw { color: var(--purple); }
.fn { color: var(--accent-bright); }
.type { color: var(--orange); }
.num { color: var(--green); }
.str { color: #a5d6ff; }
.comment { color: var(--text-muted); font-style: italic; }
.attr { color: var(--orange); }

/* ---- One declaration ---- */
.item {
  position: relative;
  margin: 0 0 12px;
  padding: 14px 18px 4px;
  background: var(--bg-card);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  scroll-margin-top: 64px;
}
.item:target { border-color: var(--accent-dim); }

.item-head {
  display: flex;
  align-items: baseline;
  gap: 10px;
  flex-wrap: wrap;
  margin-bottom: 10px;
}

/* The kind badge: `def`, `struct`, `type`, `class`, `instance`, `infix`. */
.item-kind {
  flex: none;
  padding: 1px 8px;
  border: 1px solid currentColor;
  border-radius: 20px;
  font-size: 11px;
  font-weight: 600;
  letter-spacing: 0.04em;
  text-transform: uppercase;
  font-family: var(--mono);
  opacity: 0.9;
}
.kind-def { color: var(--accent-bright); }
.kind-struct { color: var(--orange); }
.kind-type { color: var(--orange); }
.kind-class { color: var(--purple); }
.kind-instance { color: var(--green); }
.kind-infix { color: var(--text-muted); }
.kind-use { color: var(--text-muted); }
.kind-other { color: var(--text-muted); }

.item-name {
  font-family: var(--mono);
  font-size: 1.05em;
  font-weight: 600;
  color: var(--text);
  overflow-wrap: anywhere;
}

/* The per-declaration deep link: visible on hover, like a chapter heading. */
.item-anchor {
  margin-left: auto;
  color: var(--text-muted);
  font-weight: 400;
  font-size: 0.85em;
  opacity: 0;
  transition: opacity 0.1s;
}
.item:hover .item-anchor, .item-anchor:focus { opacity: 1; text-decoration: none; }

.item > pre { margin: 0 0 12px; }
.item-doc { color: var(--text); }
.item-doc > :last-child { margin-bottom: 12px; }

/* ---- The hub: one card per mote ---- */
.hub-intro { color: var(--text-muted); margin: 0 0 2em; }
.api-mote {
  margin: 0 0 16px;
  padding: 18px 20px;
  background: var(--bg-card);
  border: 1px solid var(--border);
  border-radius: var(--radius);
}
/* Scoped under `.hub` so they outrank the prose rules (`main.content h2`,
   `main.content li + li`), which otherwise push the title down under a rule
   and stagger the grid's first row. A mote's home is a `.hub` too. */
.hub .api-mote h2 {
  margin: 0 0 4px;
  padding: 0;
  border: 0;
  font-size: 1.2em;
  font-family: var(--mono);
  color: var(--text);
}
.hub .mote-meta {
  margin: 0 0 14px;
  color: var(--text-muted);
  font-size: 13px;
}
.hub .api-modules {
  list-style: none;
  margin: 0;
  padding: 0;
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(220px, 1fr));
  gap: 2px 16px;
}
.hub .api-modules li + li { margin-top: 0; }
.hub .api-modules a {
  display: block;
  padding: 3px 8px;
  border-radius: 5px;
  font-family: var(--mono);
  font-size: 13px;
  overflow-wrap: anywhere;
}
.hub .api-modules a:hover { background: var(--bg-hover); text-decoration: none; }

/* ---- Footer ---- */
.site-footer {
  padding: 24px;
  border-top: 1px solid var(--border);
  color: var(--text-muted);
  font-size: 13px;
  text-align: center;
}

/* ---- Narrow screens: the sidebar folds above the content ---- */
@media (max-width: 860px) {
  .api { display: block; }
  .api-sidebar {
    position: static;
    max-height: none;
    border-right: 0;
    border-bottom: 1px solid var(--border);
  }
  .api-main, .hub { padding: 24px 16px 48px; }
  .hub .api-modules { grid-template-columns: 1fr; }
}

/* ---- Print: the declarations alone ---- */
@media print {
  :root { color-scheme: light; }
  body { background: #fff; color: #000; }
  .site-header, .api-sidebar, .site-footer, .item-anchor { display: none; }
  .api { display: block; }
  .api-main, .hub { max-width: none; padding: 0; }
  .item { background: #fff; border-color: #d0d7de; }
  pre, :not(pre) > code { background: #f6f8fa; border-color: #d0d7de; }
}
"#
