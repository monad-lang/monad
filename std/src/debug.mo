/// Debug class — rust-style structural representation, distinct from
/// `std.show`'s `Show` (which is for hand-written, user-facing output).
/// `Debug` is always mechanically derivable via `#[derive Debug]`/
/// `derive_debug!` (see `std/derive.mo`), and its base instances below
/// deliberately differ from the equivalent `Show` instances where a
/// "debug repr" and a "display string" naturally diverge — e.g. `String`
/// is quoted here, unlike `Show String`.

class Debug A {
    def debug : A -> String
}

instance Debug String {
    def debug (s : String) : String := String.concat "\"" (String.concat s "\"")
}

instance Debug I64 {
    def debug (n : I64) : String := I64.to_string n
}

instance Debug Bool {
    def debug (b : Bool) : String :=
        if b then "true" else "false"
}
