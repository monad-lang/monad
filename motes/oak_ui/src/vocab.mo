// The shared vocabulary every component takes: tones, sizes, variants,
// alignment, and the modifier list.
//
// A component's first argument is `List Ui.Opt`, a typed modifier list
// (`[Ui.danger, Ui.small]`). It replaces an options struct: partial struct
// literals are filled positionally on the Rust host and constructor-valued
// defaults do not lower there (see `Html.RenderOpts`), while a list of
// constructors has neither problem and reads short at the call site. When
// one modifier appears twice, the LAST one wins; a component ignores the
// modifiers it has no use for.
//
// `Ui.resolve` folds the list into `Ui.Style`, a `Copy` record, so a
// component reads `s.tone`/`s.size` freely without re-walking the list.

use std::list {List.intercalate}

pub type Ui.Tone { neutral, primary, success, warning, danger, info }

pub type Ui.Size { sm, md, lg }

pub type Ui.Variant { solid, soft, outline, ghost, plain }

/// Flex/grid alignment. `end_` because the slug `end` reads as a keyword in
/// too many host languages; the emitted class says `end`.
pub type Ui.Align { start, center, end_, stretch, between }

pub type Ui.Opt {
    tone (t : Ui.Tone),
    size (s : Ui.Size),
    variant (v : Ui.Variant),
    full_width,
    loading,
    disabled,
    required,
    wrap,
    gap (n : I64),
    cols (n : I64),
    align (a : Ui.Align),
    justify (a : Ui.Align),
    classes (names : List String)
}

/// The resolved modifiers. Every field is named at every literal.
pub struct Ui.Style {
    tone : Ui.Tone,
    size : Ui.Size,
    variant : Ui.Variant,
    full_width : Bool,
    loading : Bool,
    disabled : Bool,
    required : Bool,
    wrap : Bool,
    gap : I64,
    cols : I64,
    align : Ui.Align,
    justify : Ui.Align,
    classes : List String
}

/// The style is an immutable value; components read several fields of it.
pub instance Copy Ui.Style {
    def copy (s : Ui.Style) : Pair Ui.Style Ui.Style := Pair.pair s s
}

pub instance Copy Ui.Tone {
    def copy (t : Ui.Tone) : Pair Ui.Tone Ui.Tone := Pair.pair t t
}

pub instance Copy Ui.Size {
    def copy (s : Ui.Size) : Pair Ui.Size Ui.Size := Pair.pair s s
}

pub instance Copy Ui.Variant {
    def copy (v : Ui.Variant) : Pair Ui.Variant Ui.Variant := Pair.pair v v
}

pub instance Copy Ui.Align {
    def copy (a : Ui.Align) : Pair Ui.Align Ui.Align := Pair.pair a a
}

// ═══ Slugs: the class-name spelling of each choice ═══

pub def Ui.Tone.slug (t : Ui.Tone) : String :=
    match t {
        Ui.Tone.neutral => "neutral",
        Ui.Tone.primary => "primary",
        Ui.Tone.success => "success",
        Ui.Tone.warning => "warning",
        Ui.Tone.danger => "danger",
        Ui.Tone.info => "info",
    }

/// Every tone, in declaration order (themes and stories iterate it).
pub def Ui.Tone.all : List Ui.Tone :=
    [Ui.Tone.neutral, Ui.Tone.primary, Ui.Tone.success, Ui.Tone.warning, Ui.Tone.danger, Ui.Tone.info]

pub def Ui.Size.slug (s : Ui.Size) : String :=
    match s {
        Ui.Size.sm => "sm",
        Ui.Size.md => "md",
        Ui.Size.lg => "lg",
    }

pub def Ui.Variant.slug (v : Ui.Variant) : String :=
    match v {
        Ui.Variant.solid => "solid",
        Ui.Variant.soft => "soft",
        Ui.Variant.outline => "outline",
        Ui.Variant.ghost => "ghost",
        Ui.Variant.plain => "plain",
    }

pub def Ui.Align.slug (a : Ui.Align) : String :=
    match a {
        Ui.Align.start => "start",
        Ui.Align.center => "center",
        Ui.Align.end_ => "end",
        Ui.Align.stretch => "stretch",
        Ui.Align.between => "between",
    }

// ═══ Resolution ═══

/// The style with no modifiers: neutral, medium, solid, gap 3, one column.
pub def Ui.Style.default : Ui.Style :=
    { tone := Ui.Tone.neutral, size := Ui.Size.md, variant := Ui.Variant.solid,
        full_width := false, loading := false, disabled := false, required := false, wrap := false,
        gap := 3, cols := 1, align := Ui.Align.stretch, justify := Ui.Align.start,
        classes := List.empty }

def apply_opt (s : Ui.Style) (o : Ui.Opt) : Ui.Style :=
    match o {
        Ui.Opt.tone t => { s with tone := t },
        Ui.Opt.size z => { s with size := z },
        Ui.Opt.variant v => { s with variant := v },
        Ui.Opt.full_width => { s with full_width := true },
        Ui.Opt.loading => { s with loading := true },
        Ui.Opt.disabled => { s with disabled := true },
        Ui.Opt.required => { s with required := true },
        Ui.Opt.wrap => { s with wrap := true },
        Ui.Opt.gap n => { s with gap := n },
        Ui.Opt.cols n => { s with cols := n },
        Ui.Opt.align a => { s with align := a },
        Ui.Opt.justify a => { s with justify := a },
        Ui.Opt.classes names => { s with classes := List.append s.classes names },
    }

#[terminating]
def apply_opts (s : Ui.Style) (opts : List Ui.Opt) : Ui.Style :=
    match opts {
        List.empty => s,
        List.cons o rest => apply_opts (apply_opt s o) rest,
    }

/// Fold modifiers over a base style (a component's own defaults).
pub def Ui.resolve_from (base : Ui.Style) (opts : List Ui.Opt) : Ui.Style :=
    apply_opts base opts

/// Fold modifiers over `Ui.Style.default`.
pub def Ui.resolve (opts : List Ui.Opt) : Ui.Style :=
    apply_opts Ui.Style.default opts

// ═══ Class names ═══

#[terminating]
def modifier_classes (block : String) (mods : List String) : List String :=
    match mods {
        List.empty => List.empty,
        List.cons m rest =>
            if String.is_empty m
            then modifier_classes block rest
            else List.cons (String.concat_list [block, "--", m]) (modifier_classes block rest),
    }

/// `oak-btn oak-btn--primary oak-btn--sm extra`: the block, one
/// `block--mod` per non-empty modifier, then caller classes verbatim.
pub def Ui.class_names (block : String) (mods : List String) (extra : List String) : String :=
    List.intercalate " " (List.cons block (List.append (modifier_classes block mods) extra))

// ═══ Shorthand modifiers ═══

with Ui {
    pub def neutral : Ui.Opt := Ui.Opt.tone Ui.Tone.neutral
    pub def primary : Ui.Opt := Ui.Opt.tone Ui.Tone.primary
    pub def success : Ui.Opt := Ui.Opt.tone Ui.Tone.success
    pub def warning : Ui.Opt := Ui.Opt.tone Ui.Tone.warning
    pub def danger : Ui.Opt := Ui.Opt.tone Ui.Tone.danger
    pub def info : Ui.Opt := Ui.Opt.tone Ui.Tone.info

    pub def small : Ui.Opt := Ui.Opt.size Ui.Size.sm
    pub def medium : Ui.Opt := Ui.Opt.size Ui.Size.md
    pub def large : Ui.Opt := Ui.Opt.size Ui.Size.lg

    pub def solid : Ui.Opt := Ui.Opt.variant Ui.Variant.solid
    pub def soft : Ui.Opt := Ui.Opt.variant Ui.Variant.soft
    pub def outline : Ui.Opt := Ui.Opt.variant Ui.Variant.outline
    pub def ghost : Ui.Opt := Ui.Opt.variant Ui.Variant.ghost
    pub def plain : Ui.Opt := Ui.Opt.variant Ui.Variant.plain

    pub def full : Ui.Opt := Ui.Opt.full_width
    pub def busy : Ui.Opt := Ui.Opt.loading
    pub def inactive : Ui.Opt := Ui.Opt.disabled
    /// A form field that must be filled (`required` + a marker).
    pub def required : Ui.Opt := Ui.Opt.required
    pub def wrapping : Ui.Opt := Ui.Opt.wrap

    /// Spacing step `n` on the theme's scale (0-8).
    pub def gap (n : I64) : Ui.Opt := Ui.Opt.gap n
    /// Grid column count (0 = auto-fit by minimum width).
    pub def cols (n : I64) : Ui.Opt := Ui.Opt.cols n
    pub def align (a : Ui.Align) : Ui.Opt := Ui.Opt.align a
    pub def justify (a : Ui.Align) : Ui.Opt := Ui.Opt.justify a
    /// Extra classes on the component's root element.
    pub def cls (names : List String) : Ui.Opt := Ui.Opt.classes names
}
