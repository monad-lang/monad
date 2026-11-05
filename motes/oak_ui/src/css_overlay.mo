// Stylesheet sections for navigation, disclosure and overlays.

// ═══ Navigation ═══

pub def Ui.css_nav : String := r#"
.oak-navbar {
  display: flex; align-items: center; gap: calc(var(--oak-space) * 4); flex-wrap: wrap;
  padding: calc(var(--oak-space) * 2) calc(var(--oak-space) * 4);
  background: var(--oak-surface); border-bottom: 1px solid var(--oak-border);
}
.oak-navbar__brand { display: flex; align-items: center; gap: calc(var(--oak-space) * 2); font-weight: 650; }
.oak-navbar__links { display: flex; align-items: center; gap: var(--oak-space); flex: 1 1 auto; }
.oak-navbar__actions { display: flex; align-items: center; gap: calc(var(--oak-space) * 2); }
.oak-navbar__toggle { display: none; margin-left: auto; }
.oak-navbar__link {
  color: var(--oak-muted); text-decoration: none; font-weight: 500;
  padding: calc(var(--oak-space) * 1.5) calc(var(--oak-space) * 3); border-radius: var(--oak-radius-md);
}
.oak-navbar__link:hover { color: var(--oak-text); background: var(--oak-surface-alt); }
.oak-navbar__link--active { color: var(--oak-text); background: var(--oak-surface-alt); }
@media (max-width: 768px) {
  .oak-navbar__toggle { display: inline-flex; }
  .oak-navbar__links, .oak-navbar__actions { display: none; flex-basis: 100%; }
  .oak-navbar--open .oak-navbar__links { display: flex; flex-direction: column; align-items: stretch; }
  .oak-navbar--open .oak-navbar__actions { display: flex; }
}
.oak-tabs__list {
  display: flex; gap: var(--oak-space); overflow-x: auto;
  box-shadow: inset 0 -1px 0 var(--oak-border);
}
.oak-tabs__tab {
  font: inherit; font-weight: 500; color: var(--oak-muted); background: none; border: 0;
  border-bottom: 2px solid transparent; cursor: pointer; white-space: nowrap;
  padding: calc(var(--oak-space) * 2) calc(var(--oak-space) * 3);
}
.oak-tabs__tab:hover { color: var(--oak-text); }
.oak-tabs__tab--active { color: var(--oak-primary); border-bottom-color: var(--oak-primary); }
.oak-tabs__panel { padding: calc(var(--oak-space) * 4) 0; }
.oak-breadcrumbs__list { display: flex; flex-wrap: wrap; list-style: none; margin: 0; padding: 0; font-size: 0.875em; }
.oak-breadcrumbs__item { color: var(--oak-muted); }
.oak-breadcrumbs__item + .oak-breadcrumbs__item::before { content: "/"; margin: 0 calc(var(--oak-space) * 2); color: var(--oak-border-strong); }
.oak-breadcrumbs__item [aria-current] { color: var(--oak-text); font-weight: 500; }
.oak-pagination__list { display: flex; align-items: center; gap: var(--oak-space); list-style: none; margin: 0; padding: 0; }
.oak-pagination__page, .oak-pagination__step {
  font: inherit; min-width: 2.25em; height: 2.25em; padding: 0 calc(var(--oak-space) * 2);
  background: var(--oak-surface); color: var(--oak-text); cursor: pointer;
  border: 1px solid var(--oak-border); border-radius: var(--oak-radius-md);
}
.oak-pagination__page:hover, .oak-pagination__step:hover { background: var(--oak-surface-alt); }
.oak-pagination__page--current { background: var(--oak-primary); border-color: var(--oak-primary); color: var(--oak-primary-fg); }
.oak-pagination__page--current:hover { background: var(--oak-primary); }
.oak-pagination__step:disabled { opacity: 0.5; cursor: not-allowed; }
.oak-pagination__gap { color: var(--oak-muted); padding: 0 var(--oak-space); }
.oak-sidenav { display: flex; flex-direction: column; gap: calc(var(--oak-space) * 4); padding: calc(var(--oak-space) * 3); }
.oak-sidenav__title {
  margin: 0 0 var(--oak-space) 0; padding: 0 calc(var(--oak-space) * 3);
  font-size: 0.75em; font-weight: 600; text-transform: uppercase; letter-spacing: 0.05em; color: var(--oak-muted);
}
.oak-sidenav__list { list-style: none; margin: 0; padding: 0; display: flex; flex-direction: column; gap: 2px; }
.oak-sidenav__link {
  display: block; padding: calc(var(--oak-space) * 1.5) calc(var(--oak-space) * 3);
  border-radius: var(--oak-radius-md); color: var(--oak-text); text-decoration: none; font-size: 0.9375em;
}
.oak-sidenav__link:hover { background: var(--oak-surface-alt); }
.oak-sidenav__link--active { background: var(--oak-primary-soft); color: var(--oak-primary); font-weight: 550; }
.oak-steps { display: flex; list-style: none; margin: 0; padding: 0; gap: calc(var(--oak-space) * 2); }
.oak-steps__step { display: flex; align-items: center; gap: calc(var(--oak-space) * 2); flex: 1 1 0; color: var(--oak-muted); }
.oak-steps__step + .oak-steps__step::before { content: ""; flex: 0 0 calc(var(--oak-space) * 6); height: 1px; background: var(--oak-border-strong); }
.oak-steps__marker {
  display: inline-flex; align-items: center; justify-content: center; flex: none;
  width: 1.75em; height: 1.75em; border-radius: 50%; font-size: 0.875em; font-weight: 600;
  border: 2px solid var(--oak-border-strong);
}
.oak-steps__step--current { color: var(--oak-text); font-weight: 550; }
.oak-steps__step--current .oak-steps__marker { border-color: var(--oak-primary); color: var(--oak-primary); }
.oak-steps__step--done .oak-steps__marker { background: var(--oak-primary); border-color: var(--oak-primary); color: var(--oak-primary-fg); }
"#

// ═══ Disclosure ═══

pub def Ui.css_disclosure : String := r#"
.oak-accordion { border: 1px solid var(--oak-border); border-radius: var(--oak-radius-md); background: var(--oak-surface); }
.oak-accordion__item + .oak-accordion__item { border-top: 1px solid var(--oak-border); }
.oak-accordion__heading { margin: 0; font-size: 1em; }
.oak-accordion__trigger {
  display: flex; width: 100%; align-items: center; justify-content: space-between;
  font: inherit; font-weight: 550; color: var(--oak-text); background: none; border: 0; cursor: pointer;
  padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 4); text-align: left;
}
.oak-accordion__trigger:hover { background: var(--oak-surface-alt); }
.oak-accordion__panel { padding: 0 calc(var(--oak-space) * 4) calc(var(--oak-space) * 4); }
.oak-details { border: 1px solid var(--oak-border); border-radius: var(--oak-radius-md); background: var(--oak-surface); }
.oak-details__summary { cursor: pointer; font-weight: 550; padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 4); }
.oak-details__body { padding: 0 calc(var(--oak-space) * 4) calc(var(--oak-space) * 4); }
"#

// ═══ Overlays ═══

pub def Ui.css_overlay : String := r#"
.oak-overlay { position: fixed; inset: 0; z-index: 50; display: flex; align-items: center; justify-content: center; padding: calc(var(--oak-space) * 4); }
.oak-backdrop { position: absolute; inset: 0; background: var(--oak-backdrop); animation: oak-fade var(--oak-duration) ease-out; }
.oak-modal, .oak-drawer {
  position: relative; display: flex; flex-direction: column; max-height: calc(100vh - var(--oak-space) * 8);
  background: var(--oak-surface); color: var(--oak-text); box-shadow: var(--oak-shadow-lg);
}
.oak-modal { width: min(32rem, 100%); border-radius: var(--oak-radius-lg); animation: oak-rise var(--oak-duration) ease-out; }
.oak-modal--sm { width: min(24rem, 100%); }
.oak-modal--lg { width: min(48rem, 100%); }
.oak-drawer { position: absolute; top: 0; bottom: 0; right: 0; width: min(24rem, 90%); max-height: none; }
.oak-drawer--start { right: auto; left: 0; }
.oak-drawer--lg { width: min(40rem, 95%); }
.oak-dialog__header {
  display: flex; align-items: center; justify-content: space-between; gap: calc(var(--oak-space) * 3);
  padding: calc(var(--oak-space) * 4) calc(var(--oak-space) * 4) calc(var(--oak-space) * 2) calc(var(--oak-space) * 5);
}
.oak-dialog__title { margin: 0; font-size: 1.125em; font-weight: 650; }
.oak-dialog__body { padding: calc(var(--oak-space) * 2) calc(var(--oak-space) * 5) calc(var(--oak-space) * 4); overflow-y: auto; }
.oak-dialog__footer {
  display: flex; justify-content: flex-end; gap: calc(var(--oak-space) * 2);
  padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 5);
  border-top: 1px solid var(--oak-border); background: var(--oak-surface-alt);
  border-radius: 0 0 var(--oak-radius-lg) var(--oak-radius-lg);
}
@keyframes oak-fade { from { opacity: 0; } }
@keyframes oak-rise { from { opacity: 0; transform: translateY(8px); } }
.oak-menu, .oak-popover { position: relative; display: inline-block; }
.oak-menu__panel, .oak-popover__panel {
  position: absolute; top: calc(100% + var(--oak-space)); left: 0; z-index: 30; min-width: 12rem;
  background: var(--oak-surface); border: 1px solid var(--oak-border);
  border-radius: var(--oak-radius-md); box-shadow: var(--oak-shadow-md);
}
.oak-menu__panel { display: flex; flex-direction: column; padding: var(--oak-space); }
.oak-popover__panel { padding: calc(var(--oak-space) * 3); min-width: 16rem; }
.oak-menu__item {
  font: inherit; text-align: left; color: var(--oak-text); background: none; border: 0; cursor: pointer;
  padding: calc(var(--oak-space) * 2) calc(var(--oak-space) * 3); border-radius: var(--oak-radius-sm);
}
.oak-menu__item:hover, .oak-menu__item:focus-visible { background: var(--oak-surface-alt); }
.oak-menu__item--danger { color: var(--oak-danger); }
.oak-menu__divider { height: 1px; background: var(--oak-border); margin: var(--oak-space) 0; }
.oak-tooltip { position: relative; display: inline-flex; }
.oak-tooltip__bubble {
  position: absolute; bottom: calc(100% + var(--oak-space) * 2); left: 50%; transform: translateX(-50%);
  z-index: 40; pointer-events: none; white-space: nowrap; font-size: 0.8125em;
  padding: var(--oak-space) calc(var(--oak-space) * 2); border-radius: var(--oak-radius-sm);
  background: var(--oak-text); color: var(--oak-bg); opacity: 0; transition: opacity var(--oak-duration);
}
.oak-tooltip:hover .oak-tooltip__bubble, .oak-tooltip:focus-within .oak-tooltip__bubble { opacity: 1; }
@media (prefers-reduced-motion: reduce) {
  .oak-backdrop, .oak-modal { animation: none; }
}
"#
