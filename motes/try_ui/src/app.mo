/// The /try page: an Oak scratchpad that runs one Monad program.
///
/// `main` is the value shown (`def main : I64 := 2 + 3`), mirroring
/// `monad eval`. Run starts the worker; the animation-frame subscription
/// polls it; Cancel terminates it. The editor is uncontrolled: typing
/// updates `source` but not the rendered text, so the caret and undo stack
/// survive re-renders. Loading an example changes the editor's key, which
/// remounts the textarea with the new text.
use oak::app {Command, Host, Program}
use oak::elements {
    Html.button, Html.class_, Html.div, Html.disabled, Html.h1, Html.id_, Html.key,
    Html.node, Html.p, Html.placeholder, Html.span, Html.spellcheck, Html.text,
    Html.textarea
}
use oak::events {Html.on, Html.on_click, Html.on_input, Subscription}
use oak::typed {Oak.Attr, Oak.Node}
use web_event::event {HandlerResult, ListenerFlags, WebEvent}
use web_wasm::worker {Worker.cancel, Worker.error, Worker.notes, Worker.poll, Worker.run, Worker.status, Worker.typ, Worker.value}
// The example programs live in `eval::examples` so the engine's own tests can
// evaluate exactly the sources the page offers (`pipeline_tests.mo`).
pub use eval::examples {TryExample, try_examples}

pub struct TryModel {
    source : String,
    editor_text : String,
    /// A MONOTONIC counter, not the example index: loading the same example
    /// twice must still remount the uncontrolled textarea.
    editor_key : String,
    editor_seq : I64,
    running : Bool,
    status : String,
    value : String,
    typ : String,
    error : String,
    notes : String
}

pub type TryMsg {
    source_changed (text : String),
    load_example (index : I64),
    clear,
    run,
    cancel,
    polled,
    finished (status : String) (value : String) (typ : String) (error : String) (notes : String),
}

pub type TryEffect {
    start (source : String),
    poll,
    cancel,
}

pub def try_init : TryModel :=
    { source := first_source, editor_text := first_source, editor_key := "0", editor_seq := 0,
        running := false, status := "", value := "", typ := "", error := "", notes := "" }

def first_source : String :=
    match try_examples {
        List.cons e _ => e.source,
        List.empty => "def main : I64 := 2 + 3\n",
    }

pub def try_update (m : TryModel) (msg : TryMsg) : Pair TryModel (Command TryEffect TryMsg) :=
    match msg {
        TryMsg.source_changed text => Pair.pair { m with source := text } Command.none,
        TryMsg.load_example index => load_example_pair m index,
        TryMsg.clear => clear_pair m,
        TryMsg.run =>
            if m.running
            then Pair.pair m Command.none
            else Pair.pair (start_model m) (Command.perform (TryEffect.start m.source)),
        TryMsg.cancel => Pair.pair (idle_model m) (Command.perform TryEffect.cancel),
        TryMsg.polled =>
            if m.running
            then Pair.pair m (Command.perform TryEffect.poll)
            else Pair.pair m Command.none,
        TryMsg.finished status value typ error notes =>
            Pair.pair (finish_model m status value typ error notes) Command.none,
    }

def start_model (m : TryModel) : TryModel :=
    { m with running := true, status := "running", value := "", typ := "", error := "", notes := "" }

def idle_model (m : TryModel) : TryModel :=
    { m with running := false, status := "" }

def finish_model (m : TryModel) (status : String) (value : String) (typ : String)
    (error : String) (notes : String) : TryModel :=
    { m with running := false, status := status, value := value, typ := typ, error := error, notes := notes }

def load_example_pair (m : TryModel) (index : I64) : Pair TryModel (Command TryEffect TryMsg) :=
    match example_at index try_examples {
        Option.none => Pair.pair m Command.none,
        Option.some e =>
            let next_seq : I64 := I64.add m.editor_seq 1
            in
            let cmd : Command TryEffect TryMsg :=
                if m.running then Command.perform TryEffect.cancel else Command.none
            in
            Pair.pair
                { m with source := e.source, editor_text := e.source,
                    editor_key := I64.to_string next_seq, editor_seq := next_seq,
                    running := false, status := "", value := "", typ := "", error := "", notes := "" }
                cmd,
    }

def example_at (index : I64) (exs : List TryExample) : Option TryExample :=
    match exs {
        List.empty => Option.none,
        List.cons e rest =>
            if I64.beq index 0 then Option.some e else example_at (I64.sub index 1) rest,
    }

/// Empty the scratchpad. A fresh `editor_key` remounts the uncontrolled
/// textarea; a run in flight is cancelled so its result cannot land in the
/// cleared pane.
def clear_pair (m : TryModel) : Pair TryModel (Command TryEffect TryMsg) :=
    let next_seq : I64 := I64.add m.editor_seq 1
    in
    let cmd : Command TryEffect TryMsg :=
        if m.running then Command.perform TryEffect.cancel else Command.none
    in
    Pair.pair
        { m with source := "", editor_text := "",
            editor_key := I64.to_string next_seq, editor_seq := next_seq,
            running := false, status := "", value := "", typ := "", error := "", notes := "" }
        cmd

pub def try_subscriptions (m : TryModel) : List (Subscription TryMsg) :=
    if m.running then [Subscription.animation_frame_msg TryMsg.polled] else List.empty

// ─── Effects ──────────────────────────────────────────────────────────

pub def try_host : Host IO TryEffect TryMsg := Host.host run_effect

def run_effect (e : TryEffect) : IO (Option TryMsg) :=
    match e {
        TryEffect.start source => do {
            let _ <- Worker.run source;
            IO.pure Option.none
        },
        TryEffect.cancel => do {
            Worker.cancel;
            IO.pure Option.none
        },
        TryEffect.poll => poll_once,
    }

/// The JS host's codes: 0 idle, 1 running, 2 done, 3 timeout, 4 failed.
/// Anything past running has a result to read (timeout/failure included).
def poll_once : IO (Option TryMsg) := do {
    let code <- Worker.poll;
    if I64.lt code 2 then IO.pure Option.none else read_result
}

def read_result : IO (Option TryMsg) := do {
    let status <- Worker.status;
    let value <- Worker.value;
    let typ <- Worker.typ;
    let error <- Worker.error;
    let notes <- Worker.notes;
    IO.pure (Option.some (TryMsg.finished status value typ error notes))
}

// ─── View ─────────────────────────────────────────────────────────────

pub def try_view (m : TryModel) : Oak.Node TryMsg :=
    let intro : Oak.Node TryMsg :=
        Html.div [Html.class_ ["try-intro"]]
            [Html.h1 [] [Html.text "Try Monad"],
                Html.p [] [Html.text
                    "One module, evaluated by the self-hosted Monad compiler compiled to WebAssembly. Define `main`; the page shows its value and type. Prelude only: no imports, no IO."],
                Html.p [Html.class_ ["try-note"]]
                    [Html.text "Experimental and unoptimised: the page interprets the program directly, with no optimisation passes and no native code. Expect it to be much slower than a compiled binary."]] in
    let editor : Oak.Node TryMsg := editor_pane m in
    let result : Oak.Node TryMsg := result_pane m in
    let grid : Oak.Node TryMsg :=
        Html.div [Html.class_ ["try-grid"]] [editor, result] in
    let foot : Oak.Node TryMsg :=
        Html.div [Html.class_ ["try-foot"]]
            [Html.text "Ctrl/Cmd+Enter runs. The evaluator has a 2,000,000-step budget; Cancel terminates the worker.",
                Html.node "br" [] [],
                Html.text "The engine is a separate WebAssembly module loaded in a worker; nothing leaves your browser."] in
    Html.div [Html.class_ ["try-page"]] [intro, grid, foot]

def editor_pane (m : TryModel) : Oak.Node TryMsg :=
    let head : Oak.Node TryMsg :=
        Html.div [Html.key "head", Html.class_ ["try-pane-head"]]
            [Html.span [Html.class_ ["try-title"]] [Html.text "Scratchpad"],
                Html.span [] [Html.text "Monad"]]
    in
    let field : Oak.Node TryMsg :=
        Html.div [Html.key (String.concat "edit-" m.editor_key)]
            [Html.textarea
                [Html.id_ "try-source", Html.class_ ["try-source"],
                    Html.placeholder "def main : I64 := 2 + 3",
                    Html.spellcheck false,
                    Html.on_input TryMsg.source_changed,
                    Html.on "keydown" ListenerFlags.none key_handler]
                [Html.text m.editor_text]]
    in
    let actions : Oak.Node TryMsg :=
        Html.div [Html.key "actions", Html.class_ ["try-actions"]]
            (List.append (action_buttons m) [examples_panel])
    in
    Html.div [Html.class_ ["try-pane"]]
        [head, field, actions]

/// The example buttons, in the flex container the stylesheet already
/// defines (`.try-examples`), under their own label.
def examples_panel : Oak.Node TryMsg :=
    Html.div [Html.class_ ["try-examples"]]
        (List.cons
            (Html.span [Html.class_ ["try-examples-label"]] [Html.text "Examples"])
            (example_buttons 0 try_examples))

def action_buttons (m : TryModel) : List (Oak.Node TryMsg) :=
    let run_attrs : List (Oak.Attr TryMsg) :=
        if m.running
        then [Html.class_ ["try-btn"], Html.disabled]
        else [Html.class_ ["try-btn", "try-btn-primary"]]
    in
    let run_button : Oak.Node TryMsg :=
        Html.button (List.append run_attrs [Html.on_click TryMsg.run])
            [Html.text (if m.running then "Running…" else "Run")]
    in
    let clear_button : Oak.Node TryMsg :=
        Html.button [Html.class_ ["try-btn"], Html.on_click TryMsg.clear] [Html.text "Clear"]
    in
    if m.running
    then [run_button, Html.button [Html.class_ ["try-btn", "try-btn-danger"], Html.on_click TryMsg.cancel] [Html.text "Cancel"], clear_button]
    else [run_button, clear_button]

def example_buttons (index : I64) (exs : List TryExample) : List (Oak.Node TryMsg) :=
    match exs {
        List.empty => List.empty,
        List.cons e rest =>
            List.cons
                (Html.button [Html.class_ ["try-example"], Html.on_click (TryMsg.load_example index)]
                    [Html.text e.name])
                (example_buttons (I64.add index 1) rest),
    }

def result_pane (m : TryModel) : Oak.Node TryMsg :=
    let head : Oak.Node TryMsg :=
        Html.div [Html.class_ ["try-pane-head"]]
            [Html.span [Html.class_ ["try-title"]] [Html.text "Result"],
                Html.span [] [Html.text (status_text m)]]
    in
    let body : Oak.Node TryMsg :=
        Html.div [Html.class_ ["try-output"], Html.id_ "try-result"]
            (result_children m)
    in
    Html.div [Html.class_ ["try-pane", "try-result-pane"]] [head, body]

def status_text (m : TryModel) : String :=
    if m.running then "evaluating"
    else if String.is_empty m.status then ""
    else if String.beq m.status "ok" then "ok"
    else if String.beq m.status "timeout" then "timeout"
    else if String.beq m.status "internal" then "error"
    else if String.beq m.status "size" then "too large"
    else m.status

def result_children (m : TryModel) : List (Oak.Node TryMsg) :=
    if m.running
    then [Html.div [Html.class_ ["try-running"]] [Html.text "Evaluating in the worker…"]]
    else if Bool.not (String.is_empty m.error)
    then [Html.div [Html.class_ ["try-error"]] [Html.text m.error],
        notes_node m]
    else if String.is_empty m.status
    then [Html.div [Html.class_ ["try-idle"]] [Html.text "Press Run to evaluate the program."]]
    else [Html.div [Html.class_ ["try-value"]] [Html.text m.value],
        Html.div [Html.class_ ["try-type"]] [Html.text (String.concat ": " m.typ)],
        notes_node m]

def notes_node (m : TryModel) : Oak.Node TryMsg :=
    if String.is_empty m.notes
    then Html.node "div" [] []
    else Html.div [Html.class_ ["try-notes"]] [Html.text m.notes]

def key_handler (e : WebEvent) : HandlerResult TryMsg :=
    if String.beq e.key "Enter" && (WebEvent.mod_ctrl e || WebEvent.mod_meta e)
    then HandlerResult.prevent TryMsg.run
    else HandlerResult.ignore

// ─── Program ──────────────────────────────────────────────────────────

pub def try_app : Program TryModel TryMsg TryEffect :=
    Program.with_subs try_init try_update try_view try_subscriptions
