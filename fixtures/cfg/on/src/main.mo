// Exactly one of these survives the load filter, decided by whether the
// owning mote's `[features]` has `on` enabled (`mote.toml`, `default`).
#[cfg {feature := "on"}]
pub def on_only : String := "on"

#[cfg [not {feature := "on"}]]
pub def off_only : String := "off"
