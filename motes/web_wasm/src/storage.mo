/// `localStorage` access. `get` returns `Option.none` for an absent key; the
/// raw extern uses the empty string as the sentinel (an empty stored value
/// therefore reads back as absent — documented, and the session store does
/// not use this API for anything it cannot regenerate).

use lib::ffi {storage_get_raw, storage_set_raw}

pub def Storage.get (key : String) : IO (Option String) := do {
  let raw <- IO.mk (storage_get_raw key);
  if String.is_empty raw
  then IO.pure Option.none
  else IO.pure (Option.some raw)
}

pub def Storage.set (key : String) (value : String) : IO Unit := IO.mk (storage_set_raw key value)
