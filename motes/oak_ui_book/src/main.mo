// The live explorer's wasm entry: the three exports every Oak app has
// (`motes/oak_wasm/src/program.mo`) and the browser host that persists the
// selected story and theme in local storage.

use oak::app {Host}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}
use web_wasm::storage {Storage.get, Storage.set}
use lib::story {Book.Msg}
use lib::app {Book.Model, Book.Effect, Book.program}
use lib::stories::all {Book.all_stories}

def story_key : String := "oak-ui-book.story"

def theme_key : String := "oak-ui-book.theme"

def or_empty (o : Option String) : String :=
    match o {
        Option.some v => v,
        Option.none => "",
    }

def run_effect (e : Book.Effect) : IO (Option Book.Msg) :=
    match e {
        Book.Effect.book_fx_load => do {
            let story <- Storage.get story_key;
            let theme <- Storage.get theme_key;
            IO.pure (Option.some (Book.Msg.book_prefs (or_empty story) (or_empty theme)))
        },
        Book.Effect.book_fx_save story theme => do {
            Storage.set story_key story;
            Storage.set theme_key theme;
            IO.pure Option.none
        },
    }

def book_host : Host IO Book.Effect Book.Msg := Host.host run_effect

#[export "c"]
def oak_mount : IO Unit := Runtime.mount (Book.program Book.all_stories)

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick (Book.program Book.all_stories) book_host

def main : IO Unit := IO.pure unit
