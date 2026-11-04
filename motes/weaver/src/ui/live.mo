/// The live turn display: what a running turn has streamed so far (its
/// reasoning and its answer), the tool it is dispatching, its token spend,
/// and the spinner row. A component: `LiveModel`, `LiveMsg`, `Live.update`,
/// `Live.rows` (the view) and `Live.subscriptions` (the polls that feed
/// it). The parent owns whether a turn is running; it embeds a fresh
/// `Live.start` at submit, routes `LiveMsg`s here while the turn runs, and
/// asks for the rows and subscriptions only then.
///
/// The turn runs on its own fiber and reports through files in the session
/// directory: `usage.txt` (the cumulative spend, after every model call),
/// the live text and `thinking.txt` (appended as the reply streams), and
/// `activity.txt` (the tool now running). The subscriptions read them back.
use shuttle::message {Usage}
use shuttle::context {usage_zero}
use weaver::usage {Usage.delta}
use weaver::format {format_tokens, format_elapsed}
use weaver::store {StoreState, Store.child, Store.read_live_from, Store.read_named_from, Store.read_named}
use weaver::theme {theme_running_style_with, theme_thinking_style_with}
use weaver::ui::rows {DisplayRow, Rows.plain, Rows.wrap, Rows.markdown, Rows.length, Rows.drop, Rows.tail_bytes}
use log::logger {Logger}
use weaver::logs {Logs.debug}
use tui::component {Subs}
use tui::text {Text.take_width}
use std::path {Path, Path.to_string}
use std::process {process_id}
use std::io {IO.read_file, IO.write_file}
use std::map {Map, BTreeMap}
use json::json {Json, Json.parse, Json.to_string, Json.make_object, Json.make_num_int, Json.get_object, Json.get_num, Json.get_num_i64, Json.object_get}

/// One poll's streamed-text delta: the new assistant text and reasoning
/// since the given offsets, the offsets after the read, and the tool
/// currently dispatching (none when nothing is).
pub struct LiveDelta {
    text : String,
    thinking : String,
    text_seen : I64,
    thinking_seen : I64,
    activity : Option String,
}

pub struct LiveModel {
    /// Frames since the turn began: the spinner phase and the elapsed time.
    frame : I64,
    /// The streamed answer and reasoning; `*_seen` are byte offsets into
    /// the turn's files.
    text : String,
    text_seen : I64,
    thinking : String,
    thinking_seen : I64,
    /// The tool currently dispatching, from the activity feed.
    activity : Option String,
    /// The cumulative spend `on_usage` last reported, and the spend at
    /// submit: their difference is the TURN's delta.
    spent : Option Usage,
    base : Option Usage,
    /// Esc asked the turn to stop; the row says so until it ends.
    stopping : Bool,
}

pub type LiveMsg {
    /// One frame of the spinner.
    tick,
    /// The usage poll (none when the file was unreadable).
    usage (u : Option Usage),
    /// The stream poll (none when there is no session store).
    delta (d : Option LiveDelta),
}

/// The display a turn starts with; `base` is the session's spend so far.
pub def Live.start (base : Option Usage) : LiveModel :=
    let m : LiveModel := {
        frame := 0, text := "", text_seen := 0, thinking := "", thinking_seen := 0,
        activity := Option.none, spent := Option.none, base := base, stopping := false,
    } in
    m

pub def Live.idle : LiveModel := Live.start Option.none

pub def Live.request_stop (m : LiveModel) : LiveModel := { m with stopping := true }

pub def Live.update (m : LiveModel) (msg : LiveMsg) : LiveModel :=
    match msg {
        LiveMsg.tick => { m with frame := m.frame + 1 },
        LiveMsg.usage u => match u {
            Option.some x => { m with spent := Option.some x },
            Option.none => m,
        },
        LiveMsg.delta d => match d {
            Option.some x => Live.fold_delta m x,
            Option.none => m,
        },
    }

pub def Live.fold_delta (m : LiveModel) (d : LiveDelta) : LiveModel :=
    { m with text := String.concat m.text d.text,
        thinking := String.concat m.thinking d.thinking,
        text_seen := d.text_seen, thinking_seen := d.thinking_seen,
        activity := d.activity }

// ── view ─────────────────────────────────────────────────────────────────

/// What the view needs from the parent: colors, the content width, and
/// the panel's height (the live blocks never take its last row).
pub struct LiveView {
    colors : Bool,
    width : I64,
    panel : I64,
}

/// The TURN's spend: the cumulative report minus the submit-time
/// baseline. Zero until the first model call reports.
pub def Live.spent (m : LiveModel) : Usage :=
    match m.spent {
        Option.some u => match m.base {
            Option.some base => Usage.delta u base,
            Option.none => u,
        },
        Option.none => usage_zero,
    }

/// The spinner's four frames, cycling on the frame count.
pub def Live.spinner_glyph (frame : I64) : String :=
    let idx : I64 := frame - (frame / 4) * 4 in
    if I64.beq idx 0 then "|"
    else if I64.beq idx 1 then "/"
    else if I64.beq idx 2 then "-"
    else "\\"

/// What the turn is doing: the dispatching tool, else "responding" once
/// answer text has streamed, else "thinking".
pub def Live.phase (m : LiveModel) : String :=
    match m.activity {
        Option.some name => String.concat "running " name,
        Option.none => if String.is_empty m.text then "thinking" else "responding",
    }

/// `| thinking 3.4s · ↑1.2k ↓345`, or `| stopping…` once Esc asked the
/// turn to stop.
pub def Live.status_text (m : LiveModel) : String :=
    if m.stopping
    then String.concat (Live.spinner_glyph m.frame) " stopping…"
    else
        let u : Usage := Live.spent m in
        let tail : String := String.concat (format_elapsed m.frame)
            (String.concat " · ↑"
                (String.concat (format_tokens u.input_tokens)
                    (String.concat " ↓" (format_tokens u.output_tokens)))) in
        let mid : String := String.concat (Live.phase m) (String.concat " " tail) in
        String.concat (Live.spinner_glyph m.frame) (String.concat " " mid)

/// The spinner row, clipped to the content width.
pub def Live.status_row (v : LiveView) (m : LiveModel) : DisplayRow :=
    Rows.plain (theme_running_style_with v.colors) (Text.take_width (Live.status_text m) v.width)

/// The most reasoning / answer bytes painted: bounds on the per-tick wrap.
pub def Live.thinking_cap_bytes : I64 := 4096
pub def Live.text_cap_bytes : I64 := 8192

/// The rows the two blocks share, leaving one transcript row. The spinner
/// spends one row of its own, so the panel never overflows.
def content_cap (v : LiveView) : I64 :=
    if I64.lt v.panel 2 then 0 else v.panel - 1

pub def Live.thinking_cap (v : LiveView) : I64 := content_cap v / 2

/// The answer's share; the separator row comes out of it.
pub def Live.text_cap (v : LiveView) (m : LiveModel) : I64 :=
    let c : I64 := content_cap v in
    let cap : I64 := c - (c / 2) - Live.separator_height m in
    if cap < 0 then 0 else cap

def last_rows (cap : I64) (all : List DisplayRow) : List DisplayRow :=
    let n : I64 := Rows.length all in
    if I64.gt n cap then Rows.drop (n - cap) all else all

pub def Live.text_source (m : LiveModel) : String :=
    let t : String := Rows.tail_bytes m.text Live.text_cap_bytes in
    if String.is_empty t then "" else String.concat t "▌"

/// Reasoning: dim magenta, its own byte and row budget, so it can never
/// evict the answer.
pub def Live.thinking_rows (v : LiveView) (m : LiveModel) : List DisplayRow :=
    let src : String := Rows.tail_bytes m.thinking Live.thinking_cap_bytes in
    if String.is_empty src then List.empty
    else last_rows (Live.thinking_cap v) (Rows.wrap (theme_thinking_style_with v.colors) v.width src)

/// The answer, rendered as Markdown while it streams (the parser is total,
/// so an unfinished fence or list is literal text until it closes).
pub def Live.text_rows (v : LiveView) (m : LiveModel) : List DisplayRow :=
    let src : String := Live.text_source m in
    if String.is_empty src then List.empty
    else last_rows (Live.text_cap v m) (Rows.markdown v.colors v.width src)

/// Reasoning and answer both streaming: a dim rule row parts them.
pub def Live.separator_height (m : LiveModel) : I64 :=
    if Bool.or (String.is_empty m.thinking) (String.is_empty m.text) then 0 else 1

pub def Live.separator_rows (v : LiveView) (m : LiveModel) : List DisplayRow :=
    if Bool.or (Live.separator_height m == 0) (v.width < 1) then List.empty
    else [Rows.plain (theme_thinking_style_with v.colors) (String.repeat "╌" v.width)]

/// The whole live block: reasoning, a separator, the answer, then the
/// spinner row.
pub def Live.rows (v : LiveView) (m : LiveModel) : List DisplayRow :=
    List.append (Live.thinking_rows v m)
        (List.append (Live.separator_rows v m) (List.append (Live.text_rows v m) [Live.status_row v m]))

pub def Live.thinking_height (v : LiveView) (m : LiveModel) : I64 :=
    Rows.length (Live.thinking_rows v m)

pub def Live.text_height (v : LiveView) (m : LiveModel) : I64 :=
    Rows.length (Live.text_rows v m)

/// The rows `Live.rows` takes.
pub def Live.height (v : LiveView) (m : LiveModel) : I64 :=
    1 + Live.thinking_height v m + Live.separator_height m + Live.text_height v m

// ── the usage file ───────────────────────────────────────────────────────

pub def Live.usage_path (store : Option StoreState) : String :=
    match store {
        Option.some s => Path.to_string (Store.child s.dir "usage.txt"),
        Option.none => String.concat "/tmp/weaver-usage-" (String.concat (I64.to_string process_id) ".txt"),
    }

def usage_json (u : Usage) : String :=
    Json.to_string (Json.make_object
        (Map.insert "in" (Json.make_num_int u.input_tokens)
            (Map.insert "out" (Json.make_num_int u.output_tokens)
                (Map.insert "cached" (Json.make_num_int u.cached_tokens) BTreeMap.empty))))

def usage_field (obj : BTreeMap String Json) (name : String) : I64 :=
    match Json.object_get name obj {
        Option.some j => match Json.get_num_i64 (Json.get_num j) {
            Result.ok n => n,
            Result.err _ => 0,
        },
        Option.none => 0,
    }

pub def Live.usage_of_json (s : String) : Option Usage :=
    match Json.parse s {
        Result.err _ => Option.none,
        Result.ok j => match Json.get_object j {
            Result.err _ => Option.none,
            Result.ok obj =>
                let u : Usage := { input_tokens := usage_field obj "in", output_tokens := usage_field obj "out", cached_tokens := usage_field obj "cached" } in
                Option.some u,
        },
    }

/// Persist the CUMULATIVE spend for the poll (the turn's baseline at
/// submit, then every model call's report).
pub def Live.store_usage (store : Option StoreState) (u : Usage) : IO Unit := do {
    let _ <- IO.write_file (Path.path (Live.usage_path store)) (usage_json u);
    IO.pure unit
}

/// The turn's `on_usage` hook: store the spend and log it.
pub def Live.write_usage (log : Option Logger) (store : Option StoreState) (u : Usage) : IO Unit := do {
    Live.store_usage store u;
    Logs.debug log (String.concat "ev=model_usage in=" (String.concat (I64.to_string u.input_tokens)
        (String.concat " out=" (String.concat (I64.to_string u.output_tokens)
            (String.concat " cached=" (I64.to_string u.cached_tokens))))))
}

pub def Live.read_usage (store : Option StoreState) : IO (Option Usage) := do {
    let r <- IO.read_file (Path.path (Live.usage_path store));
    match r {
        Result.err _ => IO.pure Option.none,
        Result.ok s => IO.pure (Live.usage_of_json s),
    }
}

// ── the stream files ─────────────────────────────────────────────────────

/// The activity file's last event: `start <name>` means that tool is
/// running; `end` (or anything else) means nothing is.
pub def Live.activity_of (line : String) : Option String :=
    let tag : String := String.concat "\u{1}activity\u{2}" "start\u{2}" in
    if String.starts_with tag line
    then Option.some (String.slice line (String.length tag) (String.length line - String.length tag))
    else Option.none

def activity_of_read (act : Option String) : Option String :=
    match act {
        Option.none => Option.none,
        Option.some line => Live.activity_of line,
    }

/// What the stream files gained since the given offsets.
pub def Live.read_delta (store : Option StoreState) (text_seen : I64) (thinking_seen : I64) : IO (Option LiveDelta) :=
    match store {
        Option.none => IO.pure Option.none,
        Option.some s => do {
            let t <- Store.read_live_from s text_seen;
            let th <- Store.read_named_from s "thinking.txt" thinking_seen;
            let act <- Store.read_named s "activity.txt";
            let d : LiveDelta := { text := t.first, thinking := th.first,
                text_seen := t.second, thinking_seen := th.second,
                activity := activity_of_read act };
            IO.pure (Option.some d)
        },
    }

// ── subscriptions ────────────────────────────────────────────────────────

/// The usage file every tenth frame (1 Hz at a 100 ms tick); it changes
/// once per model call.
pub def Live.usage_every : I64 := 10

/// The stream every third frame (~3 Hz): cheap enough for a growing file
/// and often enough to read as streaming.
pub def Live.stream_every : I64 := 3

/// While a turn runs: the spinner on every frame, and the two polls.
pub def Live.subscriptions (store : Option StoreState) (m : LiveModel) : Subs LiveMsg :=
    let text_seen : I64 := m.text_seen in
    let thinking_seen : I64 := m.thinking_seen in
    let usage : Subs LiveMsg := Subs.poll Live.usage_every (fn (_ : Unit) => do {
        let u <- Live.read_usage store;
        IO.pure (LiveMsg.usage u)
    }) in
    let stream : Subs LiveMsg := Subs.poll Live.stream_every (fn (_ : Unit) => do {
        let d <- Live.read_delta store text_seen thinking_seen;
        IO.pure (LiveMsg.delta d)
    }) in
    Subs.batch [Subs.every 1 LiveMsg.tick, usage, stream]
