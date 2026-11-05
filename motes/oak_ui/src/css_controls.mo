// Stylesheet sections for interactive controls: tones, buttons, forms.
//
// Tones are shared: `oak-tone-<slug>` sets the local `--ui-c` (colour),
// `--ui-c-fg` (text on it) and `--ui-c-soft` (tinted background) from the
// theme, and every toned component (button, badge, alert, progress, …)
// paints with those three. The `--ui-*` properties are component-local
// plumbing, not theme tokens; only `--oak-*` comes from `Ui.Theme`.

// ═══ Tones ═══

pub def Ui.css_tones : String := r#"
.oak-tone-neutral { --ui-c: var(--oak-neutral); --ui-c-fg: var(--oak-neutral-fg); --ui-c-soft: var(--oak-neutral-soft); }
.oak-tone-primary { --ui-c: var(--oak-primary); --ui-c-fg: var(--oak-primary-fg); --ui-c-soft: var(--oak-primary-soft); }
.oak-tone-success { --ui-c: var(--oak-success); --ui-c-fg: var(--oak-success-fg); --ui-c-soft: var(--oak-success-soft); }
.oak-tone-warning { --ui-c: var(--oak-warning); --ui-c-fg: var(--oak-warning-fg); --ui-c-soft: var(--oak-warning-soft); }
.oak-tone-danger { --ui-c: var(--oak-danger); --ui-c-fg: var(--oak-danger-fg); --ui-c-soft: var(--oak-danger-soft); }
.oak-tone-info { --ui-c: var(--oak-info); --ui-c-fg: var(--oak-info-fg); --ui-c-soft: var(--oak-info-soft); }
"#

// ═══ Buttons and icons ═══

pub def Ui.css_button : String := r#"
.oak-btn {
  display: inline-flex; align-items: center; justify-content: center;
  gap: calc(var(--oak-space) * 2);
  font: inherit; font-weight: 550; font-size: 0.9375em; line-height: 1.2;
  padding: calc(var(--oak-space) * 2) calc(var(--oak-space) * 4);
  border-radius: var(--oak-radius-md); border: 1px solid var(--ui-c);
  background: var(--ui-c); color: var(--ui-c-fg);
  cursor: pointer; text-decoration: none; white-space: nowrap; user-select: none;
  transition: filter var(--oak-duration), background var(--oak-duration), box-shadow var(--oak-duration);
}
.oak-btn:hover { filter: brightness(1.08); }
.oak-btn:active { filter: brightness(0.95); }
.oak-btn:disabled, .oak-btn[aria-disabled="true"] { opacity: 0.55; cursor: not-allowed; filter: none; }
.oak-btn--soft { background: var(--ui-c-soft); color: var(--ui-c); border-color: transparent; }
.oak-btn--outline { background: transparent; color: var(--ui-c); }
.oak-btn--outline:hover, .oak-btn--ghost:hover { background: var(--ui-c-soft); filter: none; }
.oak-btn--ghost { background: transparent; color: var(--ui-c); border-color: transparent; }
.oak-btn--plain {
  background: transparent; border-color: transparent; color: var(--ui-c);
  padding-left: 0; padding-right: 0;
}
.oak-btn--plain:hover { text-decoration: underline; filter: none; }
.oak-tone-neutral.oak-btn--outline, .oak-tone-neutral.oak-btn--ghost,
.oak-tone-neutral.oak-btn--soft, .oak-tone-neutral.oak-btn--plain { color: var(--oak-text); }
.oak-tone-neutral.oak-btn--outline { border-color: var(--oak-border-strong); }
.oak-btn--sm { font-size: 0.8125em; padding: var(--oak-space) calc(var(--oak-space) * 3); border-radius: var(--oak-radius-sm); }
.oak-btn--lg { font-size: 1.0625em; padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 6); }
.oak-btn--full { display: flex; width: 100%; }
.oak-btn--icon { padding: calc(var(--oak-space) * 2); aspect-ratio: 1; }
.oak-btn--loading { cursor: progress; }
.oak-btn__spinner {
  width: 1em; height: 1em; border-radius: 50%;
  border: 2px solid currentColor; border-right-color: transparent;
  animation: oak-spin 0.7s linear infinite;
}
@keyframes oak-spin { to { transform: rotate(360deg); } }
.oak-btn-group { display: inline-flex; }
.oak-btn-group > .oak-btn { border-radius: 0; }
.oak-btn-group > .oak-btn + .oak-btn { margin-left: -1px; }
.oak-btn-group > .oak-btn:first-child { border-radius: var(--oak-radius-md) 0 0 var(--oak-radius-md); }
.oak-btn-group > .oak-btn:last-child { border-radius: 0 var(--oak-radius-md) var(--oak-radius-md) 0; }
.oak-icon { display: inline-block; width: 1em; text-align: center; line-height: 1; }
"#

// ═══ Forms ═══

pub def Ui.css_form : String := r#"
.oak-form { display: flex; flex-direction: column; gap: calc(var(--oak-space) * 4); }
.oak-field { display: flex; flex-direction: column; gap: calc(var(--oak-space) * 1.5); }
.oak-field__label { font-weight: 550; font-size: 0.9375em; }
.oak-field__required { color: var(--oak-danger); margin-left: 0.25em; }
.oak-field__help { margin: 0; font-size: 0.875em; color: var(--oak-muted); }
.oak-field__error { margin: 0; font-size: 0.875em; color: var(--oak-danger); }
.oak-input {
  font: inherit; font-size: 0.9375em; color: var(--oak-text);
  background: var(--oak-surface); border: 1px solid var(--oak-border-strong);
  border-radius: var(--oak-radius-md);
  padding: calc(var(--oak-space) * 2) calc(var(--oak-space) * 3);
  min-width: 0; transition: border-color var(--oak-duration), box-shadow var(--oak-duration);
}
.oak-input::placeholder { color: var(--oak-muted); }
.oak-input:focus { outline: none; border-color: var(--oak-focus); box-shadow: 0 0 0 3px var(--oak-primary-soft); }
.oak-input:disabled { background: var(--oak-surface-alt); color: var(--oak-muted); cursor: not-allowed; }
.oak-input[aria-invalid="true"] { border-color: var(--oak-danger); }
.oak-input[aria-invalid="true"]:focus { box-shadow: 0 0 0 3px var(--oak-danger-soft); }
.oak-input--sm { font-size: 0.8125em; padding: var(--oak-space) calc(var(--oak-space) * 2); }
.oak-input--lg { font-size: 1.0625em; padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 4); }
.oak-input--full { width: 100%; }
.oak-input--textarea { min-height: 6em; resize: vertical; line-height: var(--oak-line-height); }
.oak-input--select { cursor: pointer; }
.oak-input--file { padding: calc(var(--oak-space) * 1.5); }
.oak-check { display: inline-flex; align-items: center; gap: calc(var(--oak-space) * 2); cursor: pointer; }
.oak-check__box { width: 1.1em; height: 1.1em; margin: 0; accent-color: var(--oak-primary); cursor: pointer; }
.oak-check__box:disabled, .oak-check__box:disabled + .oak-check__label { cursor: not-allowed; opacity: 0.6; }
.oak-check--switch .oak-check__box {
  appearance: none; -webkit-appearance: none; position: relative;
  width: 2.25em; height: 1.25em; border-radius: 999px;
  background: var(--oak-border-strong); transition: background var(--oak-duration);
}
.oak-check--switch .oak-check__box::after {
  content: ""; position: absolute; top: 0.125em; left: 0.125em;
  width: 1em; height: 1em; border-radius: 50%; background: var(--oak-surface);
  box-shadow: var(--oak-shadow-sm); transition: transform var(--oak-duration);
}
.oak-check--switch .oak-check__box:checked { background: var(--oak-primary); }
.oak-check--switch .oak-check__box:checked::after { transform: translateX(1em); }
.oak-radio-group { display: flex; flex-direction: column; gap: calc(var(--oak-space) * 2); }
.oak-range { width: 100%; accent-color: var(--oak-primary); }
.oak-input-group { display: flex; align-items: stretch; }
.oak-input-group > .oak-input { flex: 1 1 auto; border-radius: 0; }
.oak-input-group > :first-child { border-top-left-radius: var(--oak-radius-md); border-bottom-left-radius: var(--oak-radius-md); }
.oak-input-group > :last-child { border-top-right-radius: var(--oak-radius-md); border-bottom-right-radius: var(--oak-radius-md); }
.oak-input-group__addon {
  display: flex; align-items: center; padding: 0 calc(var(--oak-space) * 3);
  background: var(--oak-surface-alt); border: 1px solid var(--oak-border-strong);
  color: var(--oak-muted); font-size: 0.9375em;
}
.oak-input-group__addon:first-child { border-right: 0; }
.oak-input-group__addon:last-child { border-left: 0; }
"#
