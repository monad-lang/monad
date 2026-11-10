/// `localStorage` access, presence-aware. `get` keeps its `Option String`
/// shape but no longer conflates an absent key with an empty stored value:
/// `has` asks the host (`getItem(...) !== null`) and `get_raw` reads the
/// value directly. `remove`/`clear` delete.

use lib::ffi {
    storage_get_raw, storage_set_raw, storage_has_raw, storage_remove_raw,
    storage_clear_raw,
}

pub def Storage.has (key : String) : IO Bool := do {
    let raw <- IO.mk (storage_has_raw key);
    return Bool.not (I64.beq raw 0)
}

/// The stored value, or `Option.none` when the key is absent. An empty
/// stored value reads as `Option.some ""`.
pub def Storage.get_raw (key : String) : IO (Option String) := do {
    let present <- Storage.has key;
    if present
    then do {
        let raw <- IO.mk (storage_get_raw key);
        return (Option.some raw)
    }
    else IO.pure Option.none
}

/// The legacy accessor: an empty stored value still reads as absent. Use
/// `get_raw` when emptiness is meaningful.
pub def Storage.get (key : String) : IO (Option String) := do {
    let raw <- IO.mk (storage_get_raw key);
    if String.is_empty raw
    then IO.pure Option.none
    else IO.pure (Option.some raw)
}

pub def Storage.set (key : String) (value : String) : IO Unit :=
    IO.mk (storage_set_raw key value)

pub def Storage.remove (key : String) : IO Unit := IO.mk (storage_remove_raw key)

pub def Storage.clear : IO Unit := IO.mk storage_clear_raw
