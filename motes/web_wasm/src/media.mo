/// Media queries. `matches` asks the host whether a query currently holds
/// (`matchMedia(query).matches`); `watch` registers a `change` listener
/// whose spec carries the handler id, and `unwatch` removes it.

use lib::ffi {media_matches_raw, media_watch_raw, media_unwatch_raw}

pub def Media.matches (query : String) : IO Bool := do {
    let raw <- IO.mk (media_matches_raw query);
    return Bool.not (I64.beq raw 0)
}

pub def Media.watch (query : String) (spec : String) : IO Unit :=
    IO.mk (media_watch_raw query spec)

pub def Media.unwatch (query : String) : IO Unit := IO.mk (media_unwatch_raw query)
