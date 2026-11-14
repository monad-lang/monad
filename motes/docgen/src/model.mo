/// The page model: what extraction produces and rendering consumes.
///
/// One `DocMote` per mote, one `DocModule` per source file, one `DocItem`
/// per declaration. The extraction half (`extract.mo`) fills these from the
/// compiler's own declaration ranges; the rendering half (`render.mo`) turns
/// them into acorn `Built` pages. Nothing here touches the filesystem or the
/// compiler -- the model is pure data, so the tests can build one from a
/// source string and check it without a checkout.

/// One documented declaration: its name, its kind as the file spells it, its
/// `///` doc comment (markdown, `Option.none` when it has none), and the
/// source text of its header -- the signature a reader needs before the
/// body's own code.
pub struct DocItem {
    /// The declaration's own name: `List.map` for a def, `Shared` for a
    /// struct, `_` for an unnamed instance.
    name : String,
    /// The file's own keyword: `def`, `struct`, `type`, `class`,
    /// `instance`, `infix`, `use` -- exactly `DeclText.kind`.
    kind : String,
    /// `Option.some` when the declaration is `pub`; the default
    /// (package-private) and `priv` are both `Option.none`, because the
    /// pages document a mote's public surface.
    pub_item : Bool,
    /// The `///` doc comment's text, with the leading `/// ` stripped from
    /// each line. `Option.none` when the declaration has none.
    doc : Option String,
    /// The declaration's own source text, trimmed to its extent (the same
    /// trim `decl_texts_of_source` applies) and cut to its header: for a
    /// def, up to and including the `:=` line's end; for a type or class,
    /// the whole declaration. The header is what the page shows as the
    /// item's signature.
    signature : String,
    /// The source file the item came from, relative to the repo root
    /// (`init/src/string.mo`).
    file : String,
    /// The 1-based line the declaration starts on.
    line : I64,
}

/// Every field is a `Copy` (`String`, `Bool`, `Option String`, `I64`), so
/// duplicating an item shares pointers only -- the `SiteConfig` precedent.
/// A test or a renderer reads an item's fields one at a time, and without
/// this each read would need its own `Shared` dance.
pub instance Copy DocItem {
    def copy (i : DocItem) : Pair DocItem DocItem := Pair.pair i i
}

/// One module page: the items of one source file, in source order.
///
/// `DocItem` has a `Copy` instance (every field is a pointer or a small
/// value); a module aggregates those, so it gets the same one. A renderer
/// reads a module's path and then renders it, which is two uses of one
/// value -- the affine rule's `Copy` escape hatch is exactly that.
pub struct DocModule {
    /// The module's dotted path (`init::string`), the page's identity.
    module : String,
    /// The source file, relative to the repo root.
    file : String,
    /// The file's own leading `///` block, when it has one -- the module's
    /// documentation, shown at the top of its page.
    doc : Option String,
    /// The file's documented declarations, in source order.
    items : List DocItem,
}

/// A module shares its (immutable) parts, like a single declaration does.
pub instance Copy DocModule {
    def copy (m : DocModule) : Pair DocModule DocModule := Pair.pair m m
}

/// One mote's API pages: its modules, in path order.
pub struct DocMote {
    /// The mote's name as the manifest spells it.
    mote : String,
    /// The mote's modules, in `src/` path order.
    modules : List DocModule,
}

/// This mote with only its `pub` declarations -- what a reader of the
/// reference sees unless `--include-private` asked for the rest. A module
/// left with no items keeps its page (the module doc is still worth
/// showing) but contributes nothing to the index.
pub def DocMote.public_only (m : DocMote) : DocMote :=
    match m {
        { mote, modules, .. } => { mote := mote, modules := DocModule.public_modules modules },
    }

#[partial]
def DocModule.public_modules (ms : List DocModule) : List DocModule :=
    match ms {
        List.empty => List.empty,
        List.cons m rest =>
            match m {
                { module, file, doc, items } =>
                    // Bound to an annotated local, not passed bare: a struct
                    // literal in argument position is the Rust host's gotcha
                    // (it reads it as `List.cons`'s own fields).
                    let kept : DocModule :=
                        { module := module, file := file, doc := doc, items := public_items items } in
                    List.cons kept (DocModule.public_modules rest),
            },
    }

#[partial]
def public_items (items : List DocItem) : List DocItem :=
    match items {
        List.empty => List.empty,
        List.cons i rest =>
            if i.pub_item
            then List.cons i (public_items rest)
            else public_items rest,
    }

/// The number of items across every module -- the ratchet's number.
pub def DocMote.item_count (m : DocMote) : I64 :=
    DocModule.list_item_count m.modules 0

#[terminating]
def DocModule.list_item_count (ms : List DocModule) (acc : I64) : I64 :=
    match ms {
        List.empty => acc,
        List.cons m rest => DocModule.list_item_count rest (I64.add acc (List.length m.items)),
    }

/// The number of `pub` items with a doc comment across every module -- the
/// documented share the hygiene report prints.
pub def DocMote.documented_count (m : DocMote) : I64 :=
    DocModule.list_documented_count m.modules 0

#[terminating]
def DocModule.list_documented_count (ms : List DocModule) (acc : I64) : I64 :=
    match ms {
        List.empty => acc,
        List.cons m rest => DocModule.list_documented_count rest (I64.add acc (module_documented_count m.items 0)),
    }

#[terminating]
def module_documented_count (items : List DocItem) (acc : I64) : I64 :=
    match items {
        List.empty => acc,
        List.cons i rest =>
            let shared : Shared (List DocItem) := Shared.of rest in
            let one : I64 :=
                match i.doc {
                    Option.some _ => 1,
                    Option.none => 0,
                } in
            module_documented_count (Shared.get shared) (I64.add acc one),
    }
