# oak_ui

Reusable, composable, stylable components for [Oak](../oak/README.md):
layout, typography, buttons, forms, feedback, data display, navigation,
disclosure and overlays. Every component is a pure function returning
`Oak.Node Msg`, so the same view renders on the server (`Oak.to_html`, no
JavaScript) and in the browser runtime (`oak_wasm`).

Browse and inspect them in the explorer, [`oak_ui_book`](../oak_ui_book/README.md).

## Using a component

Every component takes a **modifier list** first, then whatever it needs, then
(usually) `attrs` and `children`:

```monad,ignore
use oak_ui::vocab {Ui.danger, Ui.small, Ui.outline}
use oak_ui::button {Ui.button}

Ui.button [Ui.danger, Ui.outline, Ui.small] [Html.on_click Delete] [Html.text "Delete"]
```

Modifiers are typed values (`List Ui.Opt`): tone (`Ui.primary`, `Ui.success`,
`Ui.warning`, `Ui.danger`, `Ui.info`, `Ui.neutral`), variant (`Ui.solid`,
`Ui.soft`, `Ui.outline`, `Ui.ghost`, `Ui.plain`), size (`Ui.small`,
`Ui.medium`, `Ui.large`), state (`Ui.full`, `Ui.busy`, `Ui.inactive`,
`Ui.required`), layout (`Ui.gap n`, `Ui.cols n`, `Ui.align a`, `Ui.justify a`,
`Ui.wrapping`) and `Ui.cls ["extra-class"]`. The last one of a kind wins; a
component ignores the ones it has no use for. They replace an options struct
on purpose: partial struct literals are filled positionally on the Rust host,
and a list of constructors has no such trap.

Event handlers ride in `attrs` (`Html.on_click`, `Html.on_input`, ...), and the
caller's attributes come after the component's own, so an `id`, `aria-*` or
handler you pass is never shadowed.

`examples/oak_ui_page.mo` is a complete server-rendered page.

## State is yours

Interactive components are **controlled**: the open flag, the active tab,
the sort order and form values live in your model, and the component reports
changes through message constructors you pass in.

```monad,ignore
Ui.modal [] "confirm" model.confirm_open "Delete project?" CloseConfirm
    [Ui.text [] [] [Html.text "This cannot be undone."]]
    [Ui.button [Ui.danger] [Html.on_click ConfirmDelete] [Html.text "Delete"]]

Ui.tabs [] "settings" [Ui.tab "general" "General" general, Ui.tab "team" "Team" team]
    model.tab SelectTab
```

A sub-view with its own message type embeds through `Oak.Node.map`.

## Forms

Controls take their `attrs` last, so a partially applied control is a
`List (Oak.Attr Msg) -> Oak.Node Msg`. `Ui.field` takes exactly that and
supplies the wiring itself (`id`, `aria-describedby`, `aria-invalid`,
`required`), so a label, help text and error can never drift from their
control:

```monad,ignore
Ui.field [Ui.required] "email" "Email" "We never share it." model.email_error
    (Ui.input [Ui.full] "email" model.email EmailChanged)
```

`Ui.form` turns submit into a message (default prevented); pass
`Html.action`/`Html.method_` so the same form still posts without JavaScript.

## Styling

`Ui.Theme` is a record of CSS values rendered to `--oak-*` custom properties.
The stylesheet reads only those variables, which gives three levels of
restyling:

1. **A theme.** `Ui.Theme.light`/`Ui.Theme.dark`, or your own record update:
   `{ Ui.Theme.light with primary := "#7c3aed", radius_md := "12px" }`.
2. **A variable.** Override one in your CSS: `:root { --oak-primary: #7c3aed }`.
3. **A class.** `Ui.cls ["mine"]` on any component, or target the stable
   `oak-<block>` / `oak-<block>--<modifier>` classes.

Ship the styles either inline (`Ui.style_tag theme` /
`Ui.style_tag_auto light dark` in the head) or as a file
(`Ui.stylesheet theme` / `Ui.stylesheet_auto light dark`, served
statically). `stylesheet_auto` follows the OS colour scheme, and
`data-theme="light"|"dark"` on any element forces a theme for that subtree.
Add `Ui.css_reset` for a themed `<body>`. Each family is its own def
(`Ui.css_button`, `Ui.css_form`, ...) if you want a subset.

## Components

| Area | Components |
|---|---|
| Layout | `stack`, `row`, `cluster`, `grid`, `container`, `center`, `spacer`, `divider`, `app_shell` |
| Typography | `heading`, `text`, `muted`, `inline`, `code`, `code_block`, `kbd`, `link` |
| Actions | `button`, `submit_button`, `link_button`, `icon_button`, `button_group`, `icon` |
| Forms | `field`, `input`, `text_input`, `textarea`, `select`, `checkbox`, `switch`, `radio_group`, `range`, `file_input`, `input_group`, `form` |
| Feedback | `alert`, `badge`, `tag`, `spinner`, `progress`, `skeleton`, `empty_state`, `toast_region` |
| Data | `card`, `description_list`, `list_group`, `avatar`, `stat`, `table` (+ `column`, `SortState`) |
| Navigation | `navbar`, `nav_link`, `tabs`, `breadcrumbs`, `pagination`, `sidebar_nav`, `steps` |
| Disclosure | `accordion`, `collapsible`, `details` |
| Overlays | `modal`, `drawer`, `dropdown_menu`, `popover`, `tooltip` |

## Accessibility

Components carry the ARIA a screen reader needs (roles, `aria-expanded`,
`aria-selected`, `aria-sort`, `aria-current`, `aria-modal`, live regions) and
name what they render: an icon button requires its label, a tooltip wires
`aria-describedby` into its trigger. The explorer's test suite runs an
accessibility lint over every story, and a finding fails it.

## Limits

- **Constructor names are prefixed** (`Ui.Tone.tone_success`): the
  self-hosted codegen keys constructor tags by bare name, and parsec's
  `success rem out` (reachable through `xml_html`) misdirected a match on a
  nullary `success`. Use the shorthands (`Ui.success`).
- **Icons are Unicode glyphs**, not SVG: the browser runtime creates elements
  without a namespace. `Ui.icon_glyphs` lists them.
- **Oak cannot move focus yet**, and three things follow from that:
  - Modals and drawers don't trap focus.
  - Escape closes a dialog only once focus is inside it. The close button
    carries `autofocus`, but browsers honour that only on page load, not
    when the runtime inserts the dialog later. The backdrop and the close
    button always work.
  - Tab arrow keys change the selection, but focus stays on the
    previously focused tab.

  A focus command in Oak would fix all three.
- **Controlled inputs can't be reset from the model once edited.** The
  runtime patches `value` and `checked` as attributes, and the browser
  ignores the attribute after the user edits the field. To clear a field
  after submit, give the input (or its wrapper) a new `Html.key`. The
  explorer does this for its Reset button.
- **A modal backdrop is the dialog's sibling.** `WebEvent` has no target, so a
  click inside a dialog cannot be told apart from one on a parent backdrop.
- **Escape closes from the dialog's own keydown listener**, not a document
  subscription (a `Subscription` handler cannot ignore other keys).
- `[affine] mode = "warn"`: one caller message is bound to several listeners
  (a modal's backdrop, close button and Escape key).

## Validation

```bash
monad test motes/oak_ui
monad check motes/oak_ui
```
