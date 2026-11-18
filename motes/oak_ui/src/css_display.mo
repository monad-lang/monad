// Stylesheet sections for feedback and data display.

// ═══ Feedback ═══

pub def Ui.css_feedback : String := r#"
.oak-alert {
  display: flex; align-items: flex-start; gap: calc(var(--oak-space) * 3);
  padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 4);
  border-radius: var(--oak-radius-md); border: 1px solid var(--ui-c);
  border-left-width: 4px; background: var(--ui-c-soft); color: var(--oak-text);
}
.oak-alert__content { flex: 1 1 auto; min-width: 0; }
.oak-alert__title { display: block; color: var(--ui-c); margin-bottom: var(--oak-space); }
.oak-dismiss { margin: calc(var(--oak-space) * -1) calc(var(--oak-space) * -1) 0 0; }
.oak-badge {
  display: inline-flex; align-items: center; font-size: 0.75em; font-weight: 600;
  line-height: 1; padding: 0.3em 0.6em; border-radius: 999px;
  background: var(--ui-c-soft); color: var(--ui-c); border: 1px solid transparent;
}
.oak-badge--solid { background: var(--ui-c); color: var(--ui-c-fg); }
.oak-badge--outline { background: transparent; border-color: var(--ui-c); }
.oak-badge--sm { font-size: 0.6875em; }
.oak-badge--lg { font-size: 0.875em; }
.oak-tone-neutral.oak-badge, .oak-tone-neutral.oak-tag { color: var(--oak-text); }
.oak-tag {
  display: inline-flex; align-items: center; gap: var(--oak-space);
  font-size: 0.875em; padding: 0.15em 0.25em 0.15em 0.65em; border-radius: var(--oak-radius-sm);
  background: var(--ui-c-soft); color: var(--ui-c); border: 1px solid transparent;
}
.oak-tag--solid { background: var(--ui-c); color: var(--ui-c-fg); }
.oak-tag--outline { background: transparent; border-color: var(--ui-c); }
.oak-tag .oak-dismiss { margin: 0; padding: 0 var(--oak-space); }
.oak-spinner {
  display: inline-block; width: 1.25em; height: 1.25em; border-radius: 50%;
  border: 2px solid var(--oak-border); border-top-color: var(--ui-c);
  animation: oak-spin 0.7s linear infinite; vertical-align: middle;
}
.oak-spinner--sm { width: 0.875em; height: 0.875em; }
.oak-spinner--lg { width: 2em; height: 2em; border-width: 3px; }
.oak-progress {
  appearance: none; -webkit-appearance: none; width: 100%; height: 0.5em;
  border: 0; border-radius: 999px; background: var(--oak-surface-alt); overflow: hidden;
  color: var(--ui-c);
}
.oak-progress::-webkit-progress-bar { background: var(--oak-surface-alt); }
.oak-progress::-webkit-progress-value { background: var(--ui-c); border-radius: 999px; }
.oak-progress::-moz-progress-bar { background: var(--ui-c); border-radius: 999px; }
.oak-progress--sm { height: 0.25em; }
.oak-progress--lg { height: 0.875em; }
.oak-skeleton { display: flex; flex-direction: column; gap: calc(var(--oak-space) * 2); }
.oak-skeleton__line {
  height: 0.875em; border-radius: var(--oak-radius-sm);
  background: linear-gradient(90deg, var(--oak-surface-alt) 25%, var(--oak-border) 50%, var(--oak-surface-alt) 75%);
  background-size: 200% 100%; animation: oak-shimmer 1.4s ease-in-out infinite;
}
.oak-skeleton__line:last-child { width: 60%; }
@keyframes oak-shimmer { from { background-position: 200% 0; } to { background-position: -200% 0; } }
@media (prefers-reduced-motion: reduce) {
  .oak-skeleton__line, .oak-spinner, .oak-btn__spinner { animation-duration: 3s; }
}
.oak-empty {
  display: flex; flex-direction: column; align-items: center; text-align: center;
  gap: calc(var(--oak-space) * 2); padding: calc(var(--oak-space) * 10) calc(var(--oak-space) * 4);
  border: 1px dashed var(--oak-border-strong); border-radius: var(--oak-radius-lg);
}
.oak-empty__title { margin: 0; font-weight: 600; font-size: 1.125em; }
.oak-empty__description { margin: 0; color: var(--oak-muted); max-width: 32rem; }
.oak-empty__actions { display: flex; gap: calc(var(--oak-space) * 2); margin-top: calc(var(--oak-space) * 2); }
.oak-toasts {
  position: fixed; right: calc(var(--oak-space) * 4); bottom: calc(var(--oak-space) * 4);
  z-index: 60; display: flex; flex-direction: column; gap: calc(var(--oak-space) * 2);
  width: min(24rem, calc(100vw - var(--oak-space) * 8));
}
.oak-toast {
  display: flex; align-items: flex-start; gap: calc(var(--oak-space) * 2);
  padding: calc(var(--oak-space) * 3); border-radius: var(--oak-radius-md);
  background: var(--oak-surface); color: var(--oak-text);
  border: 1px solid var(--oak-border); border-left: 4px solid var(--ui-c);
  box-shadow: var(--oak-shadow-md);
}
.oak-toast__content { flex: 1 1 auto; min-width: 0; }
.oak-toast__title { display: block; }
.oak-toast__body { margin: 0; color: var(--oak-muted); font-size: 0.9375em; }
"#

// ═══ Data display ═══

pub def Ui.css_data : String := r#"
.oak-card {
  background: var(--oak-surface); border: 1px solid var(--oak-border);
  border-radius: var(--oak-radius-lg); box-shadow: var(--oak-shadow-sm); overflow: hidden;
}
.oak-card__header, .oak-card__footer { padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 4); }
.oak-card__header { border-bottom: 1px solid var(--oak-border); font-weight: 600; }
.oak-card__footer { border-top: 1px solid var(--oak-border); background: var(--oak-surface-alt); }
.oak-card__body { padding: calc(var(--oak-space) * 4); }
.oak-dl {
  display: grid; grid-template-columns: minmax(8rem, max-content) 1fr;
  gap: calc(var(--oak-space) * 2) calc(var(--oak-space) * 6); margin: 0;
}
.oak-dl__term { color: var(--oak-muted); }
.oak-dl__detail { margin: 0; }
.oak-list {
  list-style: none; margin: 0; padding: 0;
  border: 1px solid var(--oak-border); border-radius: var(--oak-radius-md);
  background: var(--oak-surface);
}
.oak-list__item { padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 4); }
.oak-list__item + .oak-list__item { border-top: 1px solid var(--oak-border); }
.oak-avatar {
  display: inline-flex; align-items: center; justify-content: center; flex: none;
  width: 2.5em; height: 2.5em; border-radius: 50%; object-fit: cover;
  background: var(--ui-c-soft); color: var(--ui-c); font-weight: 600; font-size: 0.875em;
  text-transform: uppercase;
}
.oak-tone-neutral.oak-avatar { color: var(--oak-text); }
.oak-avatar--sm { width: 1.75em; height: 1.75em; font-size: 0.75em; }
.oak-avatar--lg { width: 3.5em; height: 3.5em; font-size: 1.125em; }
.oak-stat { display: flex; flex-direction: column; gap: var(--oak-space); }
.oak-stat__label { color: var(--oak-muted); font-size: 0.875em; }
.oak-stat__value { font-size: 1.75em; font-weight: 650; line-height: 1.1; }
.oak-stat__delta { font-size: 0.875em; font-weight: 600; color: var(--ui-c, var(--oak-muted)); }
.oak-table-wrap {
  overflow-x: auto; border: 1px solid var(--oak-border);
  border-radius: var(--oak-radius-md); background: var(--oak-surface);
}
.oak-table { width: 100%; border-collapse: collapse; font-size: 0.9375em; }
.oak-table__caption { caption-side: top; text-align: left; font-weight: 600; padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 4); }
.oak-table__th, .oak-table__td {
  text-align: left; padding: calc(var(--oak-space) * 2.5) calc(var(--oak-space) * 4);
  border-bottom: 1px solid var(--oak-border); vertical-align: middle;
}
.oak-table__th { font-weight: 600; color: var(--oak-muted); background: var(--oak-surface-alt); white-space: nowrap; }
.oak-table__row:last-child .oak-table__td { border-bottom: 0; }
.oak-table__cell--end { text-align: right; font-variant-numeric: tabular-nums; }
.oak-table__cell--center { text-align: center; }
.oak-table__sort {
  display: inline-flex; align-items: center; gap: var(--oak-space);
  font: inherit; color: inherit; background: none; border: 0; padding: 0; cursor: pointer;
}
.oak-table__sort:hover { color: var(--oak-text); }
.oak-table--sm .oak-table__th, .oak-table--sm .oak-table__td { padding: var(--oak-space) calc(var(--oak-space) * 3); }
.oak-table--striped .oak-table__row:nth-child(even) { background: var(--oak-surface-alt); }
.oak-table--hover .oak-table__row:hover { background: var(--oak-primary-soft); }
.oak-table--sticky .oak-table__th { position: sticky; top: 0; z-index: 1; }
"#

// ═══ Graph ═══

/// `Ui.graph`. SVG presentation lives here too (fill/stroke are CSS
/// properties), so a theme restyles a drawing like any other component.
/// Node kinds an application adds (`cls`) can colour `rect` the same way.
pub def Ui.css_graph : String := r#"
.oak-graph {
  position: relative; min-height: 20rem; height: 100%;
  border: 1px solid var(--oak-border); border-radius: var(--oak-radius-md);
  background: var(--oak-surface-alt); overflow: hidden;
}
.oak-graph__canvas { display: block; width: 100%; height: 100%; touch-action: none; user-select: none; }
.oak-graph__surface { fill: transparent; cursor: grab; }
.oak-graph--dragging .oak-graph__surface { cursor: grabbing; }
.oak-graph__toolbar {
  position: absolute; top: calc(var(--oak-space) * 2); right: calc(var(--oak-space) * 2);
  display: flex; align-items: center; gap: var(--oak-space);
  background: var(--oak-surface); border: 1px solid var(--oak-border);
  border-radius: var(--oak-radius-sm); box-shadow: var(--oak-shadow-sm); padding: 2px;
}
.oak-graph__tool {
  min-width: 1.75rem; height: 1.75rem; border: 0; border-radius: var(--oak-radius-sm);
  background: transparent; color: var(--oak-text); font: inherit; cursor: pointer;
}
.oak-graph__tool:hover { background: var(--oak-neutral-soft); }
.oak-graph__tool:focus-visible { outline: 2px solid var(--oak-focus); outline-offset: 1px; }
.oak-graph__zoom { min-width: 3rem; text-align: center; font-size: 0.8125em; color: var(--oak-muted); }
.oak-graph__group > rect { fill: var(--oak-surface); stroke: var(--oak-border-strong); stroke-width: 1; }
.oak-graph__group--depth-1 > rect { fill: var(--oak-surface-alt); stroke: var(--oak-border); }
.oak-graph__group--depth-2 > rect, .oak-graph__group--depth-3 > rect { fill: var(--oak-surface);
  stroke: var(--oak-border); stroke-dasharray: 4 3; }
.oak-graph__group--selected > rect { stroke: var(--oak-primary); stroke-width: 2; }
.oak-graph__group-label {
  fill: var(--oak-muted); font-size: 11px; font-weight: 600; font-family: var(--oak-font-mono); cursor: pointer;
}
.oak-graph__edge { fill: none; stroke: var(--oak-border-strong); opacity: 0.75; }
.oak-graph__edge--active { stroke: var(--oak-primary); opacity: 1; }
.oak-graph__edge--dim { opacity: 0.12; }
.oak-graph__arrow { fill: var(--oak-border-strong); }
.oak-graph__node { cursor: pointer; outline: none; }
.oak-graph__node > rect { fill: var(--oak-surface); stroke: var(--oak-border-strong); stroke-width: 1; }
.oak-graph__node > text { fill: var(--oak-text); font-size: 12px; font-family: var(--oak-font-mono);
  pointer-events: none; }
.oak-graph__node:hover > rect { stroke: var(--oak-primary); }
.oak-graph__node:focus-visible > rect { stroke: var(--oak-focus); stroke-width: 3; }
.oak-graph__node--match > rect { fill: var(--oak-warning-soft); stroke: var(--oak-warning); }
.oak-graph__node--selected > rect { fill: var(--oak-primary-soft); stroke: var(--oak-primary); stroke-width: 2; }
.oak-graph__node--dim { opacity: 0.3; }
"#
