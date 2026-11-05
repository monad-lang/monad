// The story model.
//
// A story is a title, notes, a list of knobs and a render function from a
// `Book.Ctx` to a view. The context carries the knob values and a small
// per-story string state, so a story can drive a CONTROLLED component (a
// modal's open flag, the active tab, a sort order) without declaring its own
// model or message types: it sends `Book.set key value` and reads
// `Book.state ctx key default`. `Book.action name payload` only logs, which
// is what the Actions panel shows.
//
// Constructors carry a `book_`/`knob_` prefix: the self-hosted codegen keys
// constructor tags by bare name (see oak_ui's vocab.mo).

use oak::typed {Oak.Node}
use oak_ui::vocab {Ui.Opt, Ui.Tone, Ui.Size, Ui.Variant}

pub type Book.Knob {
    knob_text (name : String) (default : String),
    knob_bool (name : String) (default : Bool),
    knob_choice (name : String) (options : List String) (default : String),
    knob_int (name : String) (default : I64)
}

/// What a story sees: knob values (defaults filled in) and its state.
pub struct Book.Ctx {
    knobs : List (Pair String String),
    state : List (Pair String String)
}

pub type Book.Msg {
    book_select (id : String),
    book_search (query : String),
    book_knob (name : String) (value : String),
    book_set (key : String) (value : String),
    book_action (name : String) (payload : String),
    book_set_and_log (key : String) (value : String) (name : String),
    book_theme (theme : String),
    book_viewport (viewport : String),
    book_panel (panel : String),
    book_reset,
    book_clear_log,
    book_toggle_nav,
    book_load_prefs,
    book_prefs (story : String) (theme : String)
}

pub type Book.Story {
    book_story (id : String) (group : String) (title : String) (notes : String)
        (knobs : List Book.Knob) (render : Book.Ctx -> Oak.Node Book.Msg)
}

pub def Book.story (id : String) (group : String) (title : String) (notes : String) (knobs : List Book.Knob)
    (render : Book.Ctx -> Oak.Node Book.Msg) : Book.Story :=
    Book.Story.book_story id group title notes knobs render

with Book.Story {
    pub def id (s : Book.Story) : String := match s { Book.Story.book_story i _ _ _ _ _ => i }
    pub def group (s : Book.Story) : String := match s { Book.Story.book_story _ g _ _ _ _ => g }
    pub def title (s : Book.Story) : String := match s { Book.Story.book_story _ _ t _ _ _ => t }
    pub def notes (s : Book.Story) : String := match s { Book.Story.book_story _ _ _ n _ _ => n }
    pub def knobs (s : Book.Story) : List Book.Knob := match s { Book.Story.book_story _ _ _ _ k _ => k }
    pub def render (s : Book.Story) (ctx : Book.Ctx) : Oak.Node Book.Msg :=
        match s { Book.Story.book_story _ _ _ _ _ r => r ctx }
}

// ═══ String maps (association lists; last write wins at the head) ═══

#[terminating]
pub def Book.lookup (pairs : List (Pair String String)) (key : String) : Option String :=
    match pairs {
        List.empty => Option.none,
        List.cons p rest =>
            match p { Pair.pair k v => if String.beq k key then Option.some v else Book.lookup rest key },
    }

#[terminating]
def remove_key (pairs : List (Pair String String)) (key : String) : List (Pair String String) :=
    match pairs {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair k _ => if String.beq k key then remove_key rest key else List.cons p (remove_key rest key)
            },
    }

/// Set `key` (replacing any previous value).
pub def Book.assoc (pairs : List (Pair String String)) (key : String) (value : String) : List (Pair String String) :=
    List.cons (Pair.pair key value) (remove_key pairs key)

pub def Book.lookup_or (pairs : List (Pair String String)) (key : String) (default : String) : String :=
    match Book.lookup pairs key {
        Option.some v => v,
        Option.none => default,
    }

// ═══ Knobs ═══

pub def Book.Knob.name (k : Book.Knob) : String :=
    match k {
        Book.Knob.knob_text n _ => n,
        Book.Knob.knob_bool n _ => n,
        Book.Knob.knob_choice n _ _ => n,
        Book.Knob.knob_int n _ => n,
    }

pub def Book.Knob.default_value (k : Book.Knob) : String :=
    match k {
        Book.Knob.knob_text _ d => d,
        Book.Knob.knob_bool _ d => if d then "true" else "false",
        Book.Knob.knob_choice _ _ d => d,
        Book.Knob.knob_int _ d => I64.to_string d,
    }

#[terminating]
def defaults_of (ks : List Book.Knob) : List (Pair String String) :=
    match ks {
        List.empty => List.empty,
        List.cons k rest => List.cons (Pair.pair (Book.Knob.name k) (Book.Knob.default_value k)) (defaults_of rest),
    }

#[terminating]
def overlay (values : List (Pair String String)) (base : List (Pair String String)) : List (Pair String String) :=
    match values {
        List.empty => base,
        List.cons p rest => match p { Pair.pair k v => overlay rest (Book.assoc base k v) },
    }

/// The context for `story`: its knob defaults overlaid with `knob_values`,
/// and `state`.
pub def Book.ctx_for (story : Book.Story) (knob_values : List (Pair String String))
    (state : List (Pair String String)) : Book.Ctx :=
    { knobs := overlay knob_values (defaults_of (Book.Story.knobs story)), state := state }

/// The context with every knob at its default and empty state.
pub def Book.default_ctx (story : Book.Story) : Book.Ctx :=
    { knobs := defaults_of (Book.Story.knobs story), state := List.empty }

#[terminating]
def digits_value (s : String) (i : I64) (acc : I64) : I64 :=
    match String.get s i {
        Option.none => acc,
        Option.some b =>
            if U8.lt b 48u8 || U8.lt 57u8 b
            then acc
            else digits_value s (i + 1) (I64.add (I64.mul acc 10) (I64.sub (U8.to_i64 b) 48)),
    }

/// A decimal I64 (a leading `-` negates); stops at the first non-digit.
pub def Book.parse_int (s : String) : I64 :=
    if String.starts_with "-" s then I64.sub 0 (digits_value s 1 0) else digits_value s 0 0

with Book {
    pub def text (name : String) (default : String) : Book.Knob := Book.Knob.knob_text name default
    pub def flag (name : String) (default : Bool) : Book.Knob := Book.Knob.knob_bool name default
    pub def choice (name : String) (options : List String) (default : String) : Book.Knob :=
        Book.Knob.knob_choice name options default
    pub def int (name : String) (default : I64) : Book.Knob := Book.Knob.knob_int name default

    /// Standard knobs for the shared vocabulary.
    pub def tone_knob : Book.Knob :=
        Book.Knob.knob_choice "tone" ["neutral", "primary", "success", "warning", "danger", "info"] "primary"
    pub def size_knob : Book.Knob := Book.Knob.knob_choice "size" ["sm", "md", "lg"] "md"
    pub def variant_knob : Book.Knob :=
        Book.Knob.knob_choice "variant" ["solid", "soft", "outline", "ghost", "plain"] "solid"

    pub def knob_text (ctx : Book.Ctx) (name : String) : String := Book.lookup_or ctx.knobs name ""
    pub def knob_bool (ctx : Book.Ctx) (name : String) : Bool := String.beq (Book.lookup_or ctx.knobs name "") "true"
    pub def knob_int (ctx : Book.Ctx) (name : String) : I64 := Book.parse_int (Book.lookup_or ctx.knobs name "0")

    /// Story state, `default` until the story sets it.
    pub def state (ctx : Book.Ctx) (key : String) (default : String) : String :=
        Book.lookup_or ctx.state key default
    pub def state_bool (ctx : Book.Ctx) (key : String) : Bool := String.beq (Book.lookup_or ctx.state key "") "true"
    pub def state_int (ctx : Book.Ctx) (key : String) (default : I64) : I64 :=
        match Book.lookup ctx.state key {
            Option.some v => Book.parse_int v,
            Option.none => default,
        }

    /// Messages a story's components send.
    pub def set (key : String) (value : String) : Book.Msg := Book.Msg.book_set key value
    pub def action (name : String) (payload : String) : Book.Msg := Book.Msg.book_action name payload
    /// Set state and log the change as an action named `name`.
    pub def set_and_log (key : String) (value : String) (name : String) : Book.Msg :=
        Book.Msg.book_set_and_log key value name
    /// `String -> Msg` for a component callback: stores the value under `key`.
    pub def setter (key : String) : String -> Book.Msg := fn (v : String) => Book.Msg.book_set_and_log key v key
    /// `Bool -> Msg`: stores `"true"`/`"false"` under `key`.
    pub def bool_setter (key : String) : Bool -> Book.Msg :=
        fn (b : Bool) => Book.Msg.book_set_and_log key (if b then "true" else "false") key
    /// `String -> Msg` that only logs.
    pub def logger (name : String) : String -> Book.Msg := fn (v : String) => Book.Msg.book_action name v

    /// The vocabulary knobs as modifiers.
    pub def tone_opt (ctx : Book.Ctx) : Ui.Opt := Ui.Opt.opt_tone (tone_named (Book.lookup_or ctx.knobs "tone" "neutral"))
    pub def size_opt (ctx : Book.Ctx) : Ui.Opt := Ui.Opt.opt_size (size_named (Book.lookup_or ctx.knobs "size" "md"))
    pub def variant_opt (ctx : Book.Ctx) : Ui.Opt :=
        Ui.Opt.opt_variant (variant_named (Book.lookup_or ctx.knobs "variant" "solid"))
}

def tone_named (s : String) : Ui.Tone :=
    if String.beq s "primary" then Ui.Tone.tone_primary
    else if String.beq s "success" then Ui.Tone.tone_success
    else if String.beq s "warning" then Ui.Tone.tone_warning
    else if String.beq s "danger" then Ui.Tone.tone_danger
    else if String.beq s "info" then Ui.Tone.tone_info
    else Ui.Tone.tone_neutral

def size_named (s : String) : Ui.Size :=
    if String.beq s "sm" then Ui.Size.size_sm else if String.beq s "lg" then Ui.Size.size_lg else Ui.Size.size_md

def variant_named (s : String) : Ui.Variant :=
    if String.beq s "soft" then Ui.Variant.variant_soft
    else if String.beq s "outline" then Ui.Variant.variant_outline
    else if String.beq s "ghost" then Ui.Variant.variant_ghost
    else if String.beq s "plain" then Ui.Variant.variant_plain
    else Ui.Variant.variant_solid
