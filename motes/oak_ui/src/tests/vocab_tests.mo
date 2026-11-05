/// Modifier resolution and class-name building.

use lib::vocab {
    Ui.Style, Ui.resolve, Ui.class_names, Ui.Tone.slug, Ui.Size.slug,
    Ui.danger, Ui.primary, Ui.small, Ui.cls, Ui.gap,
}

#[test]
def test_resolve_defaults : Bool :=
    let s : Ui.Style := Ui.resolve List.empty in
    String.beq (Ui.Tone.slug s.tone) "neutral" && String.beq (Ui.Size.slug s.size) "md"
        && I64.beq s.gap 3

#[test]
def test_resolve_last_wins : Bool :=
    let s : Ui.Style := Ui.resolve [Ui.primary, Ui.small, Ui.danger, Ui.gap 5] in
    String.beq (Ui.Tone.slug s.tone) "danger" && String.beq (Ui.Size.slug s.size) "sm"
        && I64.beq s.gap 5

#[test]
def test_resolve_classes_accumulate : Bool :=
    let s : Ui.Style := Ui.resolve [Ui.cls ["a"], Ui.cls ["b", "c"]] in
    String.beq (Ui.class_names "oak-x" List.empty s.classes) "oak-x a b c"

#[test]
def test_class_names_skip_empty_mods : Bool :=
    String.beq (Ui.class_names "oak-btn" ["primary", "", "sm"] ["mine"])
        "oak-btn oak-btn--primary oak-btn--sm mine"
