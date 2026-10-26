/// The current browser event, as a pure `web_event::WebEvent` snapshot.
///
/// `WebEvent.current` reads the live DOM event through the JS host's slot. The
/// slot exists only for the duration of the synchronous `oak_dispatch_event`
/// export call, so a snapshot taken from an update or a later tick is
/// `valid := false` and every field reads as its zero value.
///
/// The getters are selector-based (a `which` word) to keep the import table
/// small. The numbers are shared with `wasm/web/web_runtime.js` and kept in
/// step by hand: the ABI drift test only checks that every import has a host
/// function, so `wasm/web/event_smoke.mjs` exercises each selector group.
///
/// The snapshot is EAGER: every dispatch reads all scalar selectors (~27
/// imports), gating only the string reads by event kind. A handler cannot
/// request a field lazily. If a hot `pointermove`/`scroll` path measures
/// badly, narrow the record or add kind-gated groups — do not rely on an
/// unread field being free.

use web_event::event {WebEvent, FileInfo}
use lib::ffi {
  event_i64_raw, event_f64_raw, event_str_raw, event_data_raw, event_types_raw,
  event_files_count_raw, event_file_i64_raw, event_file_str_raw,
  event_prevent_default_raw, event_stop_propagation_raw,
}

// ─── Selectors ────────────────────────────────────────────────────────
//
// event_i64(which): 1 button  2 buttons  3 detail  4 pointerId
//                   5 keyLocation  6 deltaMode  7 repeat  8 isPrimary
//                   9 checked  10 hasDataTransfer  11 modifiers
//                   12 valid  13 defaultPrevented  14 which
//
// event_f64(which): 1 clientX  2 clientY  3 pageX  4 pageY  5 screenX
//                   6 screenY  7 offsetX  8 offsetY  9 deltaX  10 deltaY
//                   11 deltaZ  12 pressure  13 width  14 height  15 timeStamp
//
// event_str(which): 1 type  2 pointerType  3 key  4 code  5 target.value
//                   6 effectAllowed  7 dropEffect
//
// event_file_i64(index, which): 1 size  2 lastModified
// event_file_str(index, which): 1 name  2 type

def is_pointer_kind (k : String) : Bool :=
    String.starts_with "pointer" k

def is_key_kind (k : String) : Bool :=
    String.beq k "keydown" || String.beq k "keyup" || String.beq k "keypress"

def is_form_kind (k : String) : Bool :=
    String.beq k "input" || String.beq k "change" || String.beq k "beforeinput"
        || String.beq k "submit" || String.beq k "reset"

def is_drag_kind (k : String) : Bool :=
    String.starts_with "drag" k || String.beq k "drop"

def is_clipboard_kind (k : String) : Bool :=
    String.beq k "copy" || String.beq k "cut" || String.beq k "paste"

/// A string getter, skipped (empty) when the kind does not carry that field.
def str_if (wanted : Bool) (which : I64) : IO String :=
    if wanted then IO.mk (event_str_raw which) else IO.pure ""

/// Split a newline-joined list (the JS host joins `DataTransfer.types`).
#[terminating]
def split_lines_from (s : String) (start : I64) (i : I64) (acc : List String) : List String :=
    if I64.lt i (String.length s)
    then
        match String.get s i {
            Option.some b =>
                if U8.beq b 10u8
                then split_lines_from s (i + 1i64) (i + 1i64)
                    (List.cons (String.slice s start (i - start)) acc)
                else split_lines_from s start (i + 1i64) acc,
            Option.none => List.reverse (List.cons (String.slice s start (i - start)) acc),
        }
    else if I64.beq start (String.length s)
    then List.reverse acc
    else List.reverse (List.cons (String.slice s start (String.length s - start)) acc)

pub def WebEvent.split_lines (s : String) : List String :=
    if String.is_empty s then List.empty else split_lines_from s 0i64 0i64 List.empty

#[terminating]
def read_files (count : I64) (index : I64) (acc : List FileInfo) : IO (List FileInfo) :=
    if I64.lt index count
    then read_file_at count index acc
    else IO.pure (List.reverse acc)

#[terminating]
def read_file_at (count : I64) (index : I64) (acc : List FileInfo) : IO (List FileInfo) := do {
    let name <- IO.mk (event_file_str_raw index 1i64);
    let mime <- IO.mk (event_file_str_raw index 2i64);
    let size <- IO.mk (event_file_i64_raw index 1i64);
    let modified <- IO.mk (event_file_i64_raw index 2i64);
    let info : FileInfo :=
        { name := name, size := size, mime_type := mime, last_modified := modified };
    read_files count (index + 1i64) (List.cons info acc)
}

/// Snapshot the event the JS host is currently dispatching.
pub def WebEvent.current : IO WebEvent := do {
    let valid <- IO.mk (event_i64_raw 12i64);
    if I64.beq valid 0i64
    then
        let empty : WebEvent := { valid := false } in
        IO.pure empty
    else WebEvent.read_current valid
}

def WebEvent.read_current (_valid : I64) : IO WebEvent := do {
        let kind <- IO.mk (event_str_raw 1i64);
        let pointer : Bool := is_pointer_kind kind;
        let keyed : Bool := is_key_kind kind;
        let form : Bool := is_form_kind kind;
        let drag : Bool := is_drag_kind kind;
        let clip : Bool := is_clipboard_kind kind;
        let payload : Bool := drag || clip;
        let pointer_type <- str_if pointer 2i64;
        let key <- str_if keyed 3i64;
        let code <- str_if keyed 4i64;
        let value <- str_if form 5i64;
        let effect_allowed <- str_if drag 6i64;
        let drop_effect <- str_if drag 7i64;
        let data <- if payload then IO.mk (event_data_raw "text/plain") else IO.pure "";
        let types_text <- if payload then IO.mk event_types_raw else IO.pure "";
        let file_count <- if payload then IO.mk event_files_count_raw else IO.pure 0i64;
        let files <- if payload then read_files file_count 0i64 List.empty else IO.pure List.empty;
        let time_stamp <- IO.mk (event_f64_raw 15i64);
        let modifiers <- IO.mk (event_i64_raw 11i64);
        let client_x <- IO.mk (event_f64_raw 1i64);
        let client_y <- IO.mk (event_f64_raw 2i64);
        let page_x <- IO.mk (event_f64_raw 3i64);
        let page_y <- IO.mk (event_f64_raw 4i64);
        let screen_x <- IO.mk (event_f64_raw 5i64);
        let screen_y <- IO.mk (event_f64_raw 6i64);
        let offset_x <- IO.mk (event_f64_raw 7i64);
        let offset_y <- IO.mk (event_f64_raw 8i64);
        let button <- IO.mk (event_i64_raw 1i64);
        let buttons <- IO.mk (event_i64_raw 2i64);
        let detail <- IO.mk (event_i64_raw 3i64);
        let pointer_id <- IO.mk (event_i64_raw 4i64);
        let pressure <- IO.mk (event_f64_raw 12i64);
        let is_primary_raw <- IO.mk (event_i64_raw 8i64);
        let width <- IO.mk (event_f64_raw 13i64);
        let height <- IO.mk (event_f64_raw 14i64);
        let repeat_raw <- IO.mk (event_i64_raw 7i64);
        let location <- IO.mk (event_i64_raw 5i64);
        let delta_x <- IO.mk (event_f64_raw 9i64);
        let delta_y <- IO.mk (event_f64_raw 10i64);
        let delta_z <- IO.mk (event_f64_raw 11i64);
        let delta_mode <- IO.mk (event_i64_raw 6i64);
        let checked_raw <- IO.mk (event_i64_raw 9i64);
        let default_prevented_raw <- IO.mk (event_i64_raw 13i64);
        let ev : WebEvent :=
            { kind := kind,
              valid := true,
              time_stamp := time_stamp,
              modifiers := modifiers,
              client_x := client_x,
              client_y := client_y,
              page_x := page_x,
              page_y := page_y,
              screen_x := screen_x,
              screen_y := screen_y,
              offset_x := offset_x,
              offset_y := offset_y,
              button := button,
              buttons := buttons,
              detail := detail,
              pointer_id := pointer_id,
              pointer_type := pointer_type,
              pressure := pressure,
              is_primary := I64.beq is_primary_raw 1i64,
              width := width,
              height := height,
              key := key,
              code := code,
              repeat := I64.beq repeat_raw 1i64,
              location := location,
              delta_x := delta_x,
              delta_y := delta_y,
              delta_z := delta_z,
              delta_mode := delta_mode,
              value := value,
              checked := I64.beq checked_raw 1i64,
              data := data,
              data_types := WebEvent.split_lines types_text,
              files := files,
              effect_allowed := effect_allowed,
              drop_effect := drop_effect,
              default_prevented := I64.beq default_prevented_raw 1i64 };
        IO.pure ev
}

/// Stop the browser's default action for the event in flight. Called by the
/// runtime when a handler's `HandlerResult` asks for it, while the browser is
/// still dispatching.
pub def WebEvent.prevent_default : IO Unit := IO.mk event_prevent_default_raw

/// Stop propagation for the event in flight.
pub def WebEvent.stop_propagation : IO Unit := IO.mk event_stop_propagation_raw
