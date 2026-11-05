# oak_ui_book

A storybook-style explorer for [`oak_ui`](../oak_ui/README.md): browse every
component, tweak it with knobs, and inspect what it renders.

```bash
scripts/build-oak-ui-book.sh            # inside `nix develop` (needs the wasm toolchain)
python3 -m http.server -d target-monad/oak-ui-book
```

`index.html` is the live explorer (a wasm SPA on `oak_wasm`);
`gallery/index.html` renders every story statically, light and dark side by
side, with no JavaScript at all.

## The explorer

- **Sidebar**: stories grouped by area, filtered by the search box.
- **Canvas**: the story inside a themed frame. Light, dark or both side by side,
  and a viewport width (full, 1200, 768, 375). Overlays stay inside their
  frame.
- **Controls**: the story's knobs (text, flags, choices, numbers).
- **Actions**: the messages the story sent, newest first.
- **Source**: the serialized HTML, indented, and the listeners it binds.
- **A11y**: the accessibility lint: unlabelled controls, nameless buttons and
  links, images without alt, unlabelled dialogs, ARIA/`for` references to
  missing ids, duplicate ids.
- **Tokens**: every `--oak-*` variable, light and dark, with swatches.

The selected story and theme persist in local storage.

## Writing a story

A story is an id, a group, a title, notes, knobs and a render function from a
`Book.Ctx`:

```monad,ignore
def button_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.button [Book.tone_opt ctx, Book.size_opt ctx]
        [Html.on_click (Book.action "click" "")]
        [Html.text (Book.knob_text ctx "label")]

Book.story "button" "Actions" "Button" "What it is for."
    [Book.text "label" "Save", Book.tone_knob, Book.size_knob] button_story
```

The context also carries per-story string state, so a story can drive a
controlled component without declaring its own model: `Book.state ctx "open"
"false"` reads it, `Book.set "open" "true"` writes it, `Book.set_and_log` writes
and logs, and `Book.setter key` / `Book.bool_setter key` adapt a component's
`String -> Msg` / `Bool -> Msg` callback. Add the story to a list in
`src/stories/` (they are concatenated in `src/stories/all.mo`).

## Tests

```bash
monad test motes/oak_ui_book                                 # pure: stories, lint, update
node wasm/web/oak_ui_book_smoke.mjs <oak_ui_book.wasm>       # the live explorer over a stub DOM
```

`test_every_story_lints_clean` requires every story, at its default knobs, to
pass the accessibility lint, which makes the lint a regression gate for
`oak_ui`. The node smoke (run by `scripts/check-wasm-target.sh`) restores stored
preferences, logs a click, applies a knob, switches and persists the theme,
navigates from the sidebar and closes a modal with Escape.

Rendering two frames side by side duplicates a story's ids and radio-group
names, so "both" mode is for looking, not for interacting with radios.
