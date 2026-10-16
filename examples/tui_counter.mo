// The plan's §9 Counter App, on the landed Phase 7 loop: the whole
// `App` record in ~40 lines -- a pure update over `Event`s, a `Widget`
// view, `run_app` doing everything else (raw mode, alt screen, the
// poll/decode reader, diff-based redraw, restore on quit/EOF).
//
// Piped smoke: `printf 'q' | monad run examples/tui_counter.mo` draws
// one frame and restores; `printf '++q'` draws the count climbing to 2
// first. `tick_ms` is negative, so the loop blocks until input -- no
// tick events, and a piped run terminates at EOF instead of spinning.
#![mote { name := "tui_counter_example", deps := [tui] }]

use tui::types {Event, Key, LayoutSize}
use tui::tui {App, Cmd, run_app}
use tui::widget {Widget, BorderStyle, border, label, sized}

/// + / - count, q quits, everything else (mouse, resize, ticks) leaves
/// the model alone.
def counter_key (count : I64) (k : Key) : Pair I64 Cmd :=
    match k {
        Key.char c =>
            if c == "+"
            then Pair.pair (count + 1) Cmd.none
            else if c == "-"
            then Pair.pair (count - 1) Cmd.none
            else if c == "q"
            then Pair.pair count Cmd.quit
            else Pair.pair count Cmd.none,
        _ => Pair.pair count Cmd.none
    }

def counter_update (count : I64) (e : Event) : Pair I64 Cmd :=
    match e {
        Event.key k => counter_key count k,
        _ => Pair.pair count Cmd.none
    }

/// Header / framed count / footer -- the plan's `app_layout` shape with
/// the widgets that exist: `column` with `fixed` and `fill` shares.
def counter_view (count : I64) : Widget :=
    Widget.column [
        sized (LayoutSize.fixed 1) (label "Counter Demo"),
        sized (LayoutSize.fill 1) (border BorderStyle.plain (label (I64.to_string count))),
        sized (LayoutSize.fixed 1) (label "+ / - to change, q to quit")
    ]

def counter_app : App I64 :=
    App.app 0 counter_update counter_view (0 - 1)

def main (args : List String) : IO Unit :=
    run_app counter_app
