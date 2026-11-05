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
// Constructor names carry a prefix (`tone_success`, `opt_loading`): the
// self-hosted codegen keys constructor tags by BARE name, and a bare name
// claimed at a different arity elsewhere in the program (parsec's
// `success rem out`) silently misdirects a match on it
// (plans/implementations/2026-10-21-constructor-bare-name-arity-collision.md).
// Call sites use the shorthands (`Ui.success`), which are ordinary defs.
//
// `Ui.resolve` folds the list into `Ui.Style`, a `Copy` record, so a
// component reads `s.tone`/`s.size` freely without re-walking the list.

use std::list {List.intercalate}

pub type Ui.Tone { tone_neutral, tone_primary, tone_success, tone_warning, tone_danger, tone_info }

pub type Ui.Size { size_sm, size_md, size_lg }

pub type Ui.Variant { variant_solid, variant_soft, variant_outline, variant_ghost, variant_plain }

/// Flex/grid alignment.
pub type Ui.Align { align_start, align_center, align_end, align_stretch, align_between }

pub type Ui.Opt {
    opt_tone (t : Ui.Tone),
    opt_size (s : Ui.Size),
    opt_variant (v : Ui.Variant),
    opt_full_width,
    opt_loading,
    opt_disabled,
    opt_required,
    opt_wrap,
    opt_gap (n : I64),
    opt_cols (n : I64),
    opt_align (a : Ui.Align),
    opt_justify (a : Ui.Align),
    opt_classes (names : List String)
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
        Ui.Tone.tone_neutral => "neutral",
        Ui.Tone.tone_primary => "primary",
        Ui.Tone.tone_success => "success",
        Ui.Tone.tone_warning => "warning",
        Ui.Tone.tone_danger => "danger",
        Ui.Tone.tone_info => "info",
    }

/// Every tone, in declaration order (themes and stories iterate it).
pub def Ui.Tone.all : List Ui.Tone :=
    [Ui.Tone.tone_neutral, Ui.Tone.tone_primary, Ui.Tone.tone_success, Ui.Tone.tone_warning, Ui.Tone.tone_danger, Ui.Tone.tone_info]

pub def Ui.Size.slug (s : Ui.Size) : String :=
    match s {
        Ui.Size.size_sm => "sm",
        Ui.Size.size_md => "md",
        Ui.Size.size_lg => "lg",
    }

pub def Ui.Variant.slug (v : Ui.Variant) : String :=
    match v {
        Ui.Variant.variant_solid => "solid",
        Ui.Variant.variant_soft => "soft",
        Ui.Variant.variant_outline => "outline",
        Ui.Variant.variant_ghost => "ghost",
        Ui.Variant.variant_plain => "plain",
    }

pub def Ui.Align.slug (a : Ui.Align) : String :=
    match a {
        Ui.Align.align_start => "start",
        Ui.Align.align_center => "center",
        Ui.Align.align_end => "end",
        Ui.Align.align_stretch => "stretch",
        Ui.Align.align_between => "between",
    }

// ═══ Resolution ═══

/// The style with no modifiers: neutral, medium, solid, gap 3, one column.
pub def Ui.Style.default : Ui.Style :=
    { tone := Ui.Tone.tone_neutral, size := Ui.Size.size_md, variant := Ui.Variant.variant_solid,
        full_width := false, loading := false, disabled := false, required := false, wrap := false,
        gap := 3, cols := 1, align := Ui.Align.align_stretch, justify := Ui.Align.align_start,
        classes := List.empty }

def apply_opt (s : Ui.Style) (o : Ui.Opt) : Ui.Style :=
    match o {
        Ui.Opt.opt_tone t => { s with tone := t },
        Ui.Opt.opt_size z => { s with size := z },
        Ui.Opt.opt_variant v => { s with variant := v },
        Ui.Opt.opt_full_width => { s with full_width := true },
        Ui.Opt.opt_loading => { s with loading := true },
        Ui.Opt.opt_disabled => { s with disabled := true },
        Ui.Opt.opt_required => { s with required := true },
        Ui.Opt.opt_wrap => { s with wrap := true },
        Ui.Opt.opt_gap n => { s with gap := n },
        Ui.Opt.opt_cols n => { s with cols := n },
        Ui.Opt.opt_align a => { s with align := a },
        Ui.Opt.opt_justify a => { s with justify := a },
        Ui.Opt.opt_classes names => { s with classes := List.append s.classes names },
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
    pub def neutral : Ui.Opt := Ui.Opt.opt_tone Ui.Tone.tone_neutral
    pub def primary : Ui.Opt := Ui.Opt.opt_tone Ui.Tone.tone_primary
    pub def success : Ui.Opt := Ui.Opt.opt_tone Ui.Tone.tone_success
    pub def warning : Ui.Opt := Ui.Opt.opt_tone Ui.Tone.tone_warning
    pub def danger : Ui.Opt := Ui.Opt.opt_tone Ui.Tone.tone_danger
    pub def info : Ui.Opt := Ui.Opt.opt_tone Ui.Tone.tone_info

    pub def small : Ui.Opt := Ui.Opt.opt_size Ui.Size.size_sm
    pub def medium : Ui.Opt := Ui.Opt.opt_size Ui.Size.size_md
    pub def large : Ui.Opt := Ui.Opt.opt_size Ui.Size.size_lg

    pub def solid : Ui.Opt := Ui.Opt.opt_variant Ui.Variant.variant_solid
    pub def soft : Ui.Opt := Ui.Opt.opt_variant Ui.Variant.variant_soft
    pub def outline : Ui.Opt := Ui.Opt.opt_variant Ui.Variant.variant_outline
    pub def ghost : Ui.Opt := Ui.Opt.opt_variant Ui.Variant.variant_ghost
    pub def plain : Ui.Opt := Ui.Opt.opt_variant Ui.Variant.variant_plain

    pub def full : Ui.Opt := Ui.Opt.opt_full_width
    pub def busy : Ui.Opt := Ui.Opt.opt_loading
    pub def inactive : Ui.Opt := Ui.Opt.opt_disabled
    /// A form field that must be filled (`required` + a marker).
    pub def required : Ui.Opt := Ui.Opt.opt_required
    pub def wrapping : Ui.Opt := Ui.Opt.opt_wrap

    /// Spacing step `n` on the theme's scale (0-8).
    pub def gap (n : I64) : Ui.Opt := Ui.Opt.opt_gap n
    /// Grid column count (0 = auto-fit by minimum width).
    pub def cols (n : I64) : Ui.Opt := Ui.Opt.opt_cols n
    pub def align (a : Ui.Align) : Ui.Opt := Ui.Opt.opt_align a
    pub def justify (a : Ui.Align) : Ui.Opt := Ui.Opt.opt_justify a
    /// Extra classes on the component's root element.
    pub def cls (names : List String) : Ui.Opt := Ui.Opt.opt_classes names
}
