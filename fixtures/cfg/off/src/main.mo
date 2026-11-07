// Exactly one of each pair survives the load filter, decided by whether the
// owning mote's `[features]` has `on` enabled (`mote.toml`, `default`).
#[cfg {feature := "on"}]
def on_only : String := "on"

#[cfg [not {feature := "on"}]]
def off_only : String := "off"

#[cfg {feature := "on"}]
def main : IO Unit := IO.println on_only

#[cfg [not {feature := "on"}]]
def main : IO Unit := IO.println off_only
