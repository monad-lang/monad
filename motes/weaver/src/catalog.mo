/// The provider's own model catalogue: fetched on demand, cached per
/// provider in `WeaverState`, and rendered for `/model` and the TUI
/// picker. The API is the authority -- nothing here knows a model family
/// or a naming convention.
use std::map {Map, BTreeMap}
use std::list {List.intercalate}
use shuttle::provider {ProviderConfig, Provider.list_models}

/// The most names `Catalog.render` prints; the picker still reaches
/// every entry.
pub def Catalog.max_shown : I64 := 200

pub def Catalog.fetch (cfg : ProviderConfig) : IO (Result String (List String)) :=
    Provider.list_models cfg

pub def Catalog.lookup (provider : String) (cat : BTreeMap String (List String)) : Option (List String) :=
    Map.lookup provider cat

pub def Catalog.remember (provider : String) (models : List String) (cat : BTreeMap String (List String)) : BTreeMap String (List String) :=
    Map.insert provider models cat

#[partial]
pub def Catalog.contains (model : String) (models : List String) : Bool :=
    match models {
        List.empty => false,
        List.cons m rest => if String.beq m model then true else Catalog.contains model rest,
    }

/// The advisory line `/model` prints when the current name
/// is absent: still selectable, because API lists can be partial.
pub def Catalog.note (provider : String) (models : List String) (model : String) : Option String :=
    if String.is_empty model then Option.none
    else if Catalog.contains model models then Option.none
    else
        Option.some (String.concat model
            (String.concat " is not in "
                (String.concat provider "'s model list (still selectable)")))

#[partial]
def catalog_count (xs : List String) : I64 :=
    match xs {
        List.empty => 0i64,
        List.cons _ rest => 1i64 + catalog_count rest,
    }

#[partial]
def catalog_take (n : I64) (xs : List String) : List String :=
    if n < 1i64 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (catalog_take (n - 1i64) rest),
    }

def catalog_indent (s : String) : String := String.concat "  " s

/// The `/model` listing: the current model, the provider and count, the
/// names (capped), and the advisory note when the current one is absent.
pub def Catalog.render (provider : String) (models : List String) (current : String) : String :=
    let total : I64 := catalog_count models in
    let shown : List String := catalog_take Catalog.max_shown models in
    let shown_count : I64 := catalog_count shown in
    let head : List String :=
        [String.concat "model: " current,
         String.concat "models (" (String.concat provider (String.concat "): " (I64.to_string total)))] in
    let body : List String := List.map catalog_indent shown in
    let more : List String :=
        if shown_count < total
        then [String.concat "  ... and "
                (String.concat (I64.to_string (total - shown_count)) " more")]
        else List.empty in
    let note : List String := match Catalog.note provider models current {
        Option.none => List.empty,
        Option.some s => [s],
    } in
    List.intercalate "\n" (List.append head (List.append body (List.append more note)))
