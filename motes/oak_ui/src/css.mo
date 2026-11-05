// The stylesheet, one section per component family.
//
// Rules read ONLY `--oak-*` variables (see `lib::theme`); there is no literal
// colour here, so a theme or a single overridden variable restyles
// everything. Sections are separate defs so an application can ship a
// subset; `Ui.css_all` is the whole sheet and `Ui.stylesheet` prepends a
// theme's variables. Class names follow `oak-<block>` / `oak-<block>--<mod>`
// and are the stable styling contract.
//
// Raw strings keep the CSS readable (no escaped quotes).

use lib::theme {Ui.Theme, Ui.Theme.css_vars, Ui.Theme.css_auto}

// ═══ Base ═══

pub def Ui.css_base : String := r#"
.oak-root, [data-theme] {
  background: var(--oak-bg); color: var(--oak-text);
  font-family: var(--oak-font-sans); font-size: var(--oak-font-size);
  line-height: var(--oak-line-height);
}
.oak-root *, .oak-root *::before, .oak-root *::after,
[data-theme] *, [data-theme] *::before, [data-theme] *::after { box-sizing: border-box; }
.oak-root :focus-visible, [data-theme] :focus-visible {
  outline: 2px solid var(--oak-focus); outline-offset: 2px;
}
.oak-sr-only {
  position: absolute; width: 1px; height: 1px; padding: 0; margin: -1px;
  overflow: hidden; clip: rect(0, 0, 0, 0); white-space: nowrap; border: 0;
}
"#

/// An optional page reset: zero body margin and apply the theme to `body`.
pub def Ui.css_reset : String := r#"
html, body { margin: 0; padding: 0; }
body {
  background: var(--oak-bg); color: var(--oak-text);
  font-family: var(--oak-font-sans); font-size: var(--oak-font-size);
  line-height: var(--oak-line-height); -webkit-font-smoothing: antialiased;
}
"#

// ═══ Layout ═══

pub def Ui.css_layout : String := r#"
.oak-stack { display: flex; flex-direction: column; }
.oak-row { display: flex; flex-direction: row; align-items: center; }
.oak-row--wrap, .oak-stack--wrap { flex-wrap: wrap; }
.oak-gap-0 { gap: 0; }
.oak-gap-1 { gap: var(--oak-space); }
.oak-gap-2 { gap: calc(var(--oak-space) * 2); }
.oak-gap-3 { gap: calc(var(--oak-space) * 3); }
.oak-gap-4 { gap: calc(var(--oak-space) * 4); }
.oak-gap-5 { gap: calc(var(--oak-space) * 6); }
.oak-gap-6 { gap: calc(var(--oak-space) * 8); }
.oak-gap-7 { gap: calc(var(--oak-space) * 12); }
.oak-gap-8 { gap: calc(var(--oak-space) * 16); }
.oak-align-start { align-items: flex-start; }
.oak-align-center { align-items: center; }
.oak-align-end { align-items: flex-end; }
.oak-align-stretch { align-items: stretch; }
.oak-justify-start { justify-content: flex-start; }
.oak-justify-center { justify-content: center; }
.oak-justify-end { justify-content: flex-end; }
.oak-justify-between { justify-content: space-between; }
.oak-grid { display: grid; grid-template-columns: minmax(0, 1fr); }
.oak-grid--auto { grid-template-columns: repeat(auto-fit, minmax(16rem, 1fr)); }
.oak-grid--cols-2 { grid-template-columns: repeat(2, minmax(0, 1fr)); }
.oak-grid--cols-3 { grid-template-columns: repeat(3, minmax(0, 1fr)); }
.oak-grid--cols-4 { grid-template-columns: repeat(4, minmax(0, 1fr)); }
.oak-grid--cols-5 { grid-template-columns: repeat(5, minmax(0, 1fr)); }
.oak-grid--cols-6 { grid-template-columns: repeat(6, minmax(0, 1fr)); }
@media (max-width: 640px) {
  .oak-grid--cols-2, .oak-grid--cols-3, .oak-grid--cols-4,
  .oak-grid--cols-5, .oak-grid--cols-6 { grid-template-columns: minmax(0, 1fr); }
}
.oak-container {
  width: 100%; max-width: 72rem; margin-left: auto; margin-right: auto;
  padding-left: calc(var(--oak-space) * 4); padding-right: calc(var(--oak-space) * 4);
}
.oak-container--sm { max-width: 40rem; }
.oak-container--lg { max-width: 90rem; }
.oak-center { display: flex; align-items: center; justify-content: center; }
.oak-spacer { flex: 1 1 auto; }
.oak-divider {
  border: 0; border-top: 1px solid var(--oak-border);
  margin: calc(var(--oak-space) * 3) 0; width: 100%;
}
.oak-shell {
  display: grid; min-height: 100vh;
  grid-template-columns: 16rem minmax(0, 1fr);
  grid-template-rows: auto 1fr auto;
  grid-template-areas: "header header" "sidebar main" "footer footer";
}
.oak-shell--no-sidebar { grid-template-columns: minmax(0, 1fr); grid-template-areas: "header" "main" "footer"; }
.oak-shell__header {
  grid-area: header; background: var(--oak-surface);
  border-bottom: 1px solid var(--oak-border);
}
.oak-shell__sidebar {
  grid-area: sidebar; background: var(--oak-surface);
  border-right: 1px solid var(--oak-border); overflow-y: auto;
}
.oak-shell__main { grid-area: main; min-width: 0; padding: calc(var(--oak-space) * 6); }
.oak-shell__footer {
  grid-area: footer; color: var(--oak-muted);
  border-top: 1px solid var(--oak-border); padding: calc(var(--oak-space) * 4);
}
@media (max-width: 768px) {
  .oak-shell { grid-template-columns: minmax(0, 1fr); grid-template-areas: "header" "main" "footer"; }
  .oak-shell__sidebar { display: none; }
  .oak-shell--nav-open .oak-shell__sidebar {
    display: block; position: fixed; top: 0; bottom: 0; left: 0; width: 80%;
    max-width: 20rem; z-index: 40; box-shadow: var(--oak-shadow-lg);
  }
}
"#

// ═══ Typography ═══

pub def Ui.css_typography : String := r#"
.oak-heading { margin: 0; font-weight: 650; line-height: 1.25; color: var(--oak-text); }
.oak-heading--1 { font-size: 2.25em; }
.oak-heading--2 { font-size: 1.75em; }
.oak-heading--3 { font-size: 1.375em; }
.oak-heading--4 { font-size: 1.125em; }
.oak-heading--5 { font-size: 1em; }
.oak-heading--6 { font-size: 0.875em; text-transform: uppercase; letter-spacing: 0.04em; }
.oak-text { margin: 0; }
.oak-text--sm { font-size: 0.875em; }
.oak-text--lg { font-size: 1.125em; }
.oak-text--muted { color: var(--oak-muted); }
.oak-text--primary { color: var(--oak-primary); }
.oak-text--success { color: var(--oak-success); }
.oak-text--warning { color: var(--oak-warning); }
.oak-text--danger { color: var(--oak-danger); }
.oak-text--info { color: var(--oak-info); }
.oak-code {
  font-family: var(--oak-font-mono); font-size: 0.875em;
  background: var(--oak-surface-alt); border-radius: var(--oak-radius-sm);
  padding: 0.1em 0.35em;
}
.oak-code-block {
  font-family: var(--oak-font-mono); font-size: 0.875em; margin: 0;
  background: var(--oak-surface-alt); border: 1px solid var(--oak-border);
  border-radius: var(--oak-radius-md); padding: calc(var(--oak-space) * 3);
  overflow-x: auto; white-space: pre;
}
.oak-kbd {
  font-family: var(--oak-font-mono); font-size: 0.8em;
  border: 1px solid var(--oak-border-strong); border-bottom-width: 2px;
  border-radius: var(--oak-radius-sm); padding: 0.05em 0.4em;
  background: var(--oak-surface);
}
.oak-link { color: var(--oak-primary); text-decoration: none; }
.oak-link:hover { text-decoration: underline; }
"#

// ═══ The whole sheet ═══

/// Every section, in cascade order. Grows with each component family.
pub def Ui.css_all : String :=
    String.concat_list [Ui.css_base, Ui.css_layout, Ui.css_typography]

/// Variables for one theme on `:root`, then the whole sheet.
pub def Ui.stylesheet (t : Ui.Theme) : String :=
    String.concat (Ui.Theme.css_vars ":root" t) Ui.css_all

/// Light/dark variables (OS preference plus `data-theme` overrides), then
/// the whole sheet.
pub def Ui.stylesheet_auto (light : Ui.Theme) (dark : Ui.Theme) : String :=
    String.concat (Ui.Theme.css_auto light dark) Ui.css_all
