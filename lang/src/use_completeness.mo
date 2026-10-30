/// The self-hosted twin of the Rust host's `use`-completeness gate
/// (`check_use_completeness`, rust/core/src/term/module.rs): every name a
/// module reaches from another module must be named in its own `use`
/// line, unless the owner is ambient, the consumer itself, or the name
/// was `open`-ed. Enforced by `lang/module.mo`'s `gate_use_completeness`
/// on every load's MAIN module, so it holds for every entry point at
/// once (`check`/`test`/`compile`/the LSP), exactly as the host's
/// loader-level gate does.
///
/// Where this differs from the host, and why:
///
/// - **References are collected from the main module's PRE-expansion
///   parse.** The host clones its decls before macro expansion;
///   this compiler's loader parses through `expand_decls`
///   (`parse_all_decls`, lang/module.mo), which inlines a decl-gen
///   template's body into the consumer's own decl list -- a
///   `derive_beq! Point` would otherwise look like the consumer
///   reaching into `std::derive` for `derive_beq_meta`, a name no
///   `use` line could ever sensibly name. The gate re-parses the
///   source (the one it was handed, or the file) through
///   `decls_parser_located` alone, which is exactly the parse
///   `parse_all_decls` runs minus the expansion.
/// - **The bare/qualified axis survives in `DebugName`.** The host
///   reads it off `NameRef`; this compiler's canonical `Term` is de
///   Bruijn, but lowering (`lang/parser/lower_parse.mo`) keeps a
///   free variable's whole written spelling -- `::` in the middle for
///   a module-qualified reference (`qualified_ref_symbol`'s
///   convention), bare otherwise -- and a bound variable is already
///   an index, so the walk needs no binder tracking at all.
/// - **Macro-GENERATED names are silent, on both sides of the rule.**
///   The host folds the elaborated module's declared names into its
///   own-name set; this gate has only the parse, so a name a
///   `reflect_type_info!` call generates is absent from the index
///   (dependencies are parsed too) as well as from the consumer's
///   own-name set -- invisible, which is a false negative, never a
///   false report. The load-time expansion's declared names ARE
///   folded in (they are already in the stored decl list), which
///   covers every name expansion declares but the consumer does not
///   write.

use lang::types {
  Attribute, Class, ClassDef, DebugName, Decl, Def, Identifier, InductConstructor,
  Inductive, Instance, Literal, MatchCase, ModulePath, NamePath, Param, Struct, StructField,
  Term, TypeConstraint, UseFilter, UseItem, OpenFilter, StructLitField, Visibility,
  id_eq, module_mote_of, module_path_is_empty, module_path_to_string_colon, open_all, open_only,
  sentinel, show_identifier, show_module_path, show_name_path,
  use_bare, use_glob, use_items, use_name, use_rename, use_sub, use_sub_rename,
}
use lib::parser {decls_parser_located}
use parsec::core {ParseResult}
use lib::scope {modpath_eq}
use lib::typecheck::macro_queue {
  DeriveHandlerReg, derive_handler_regs_of_decls, derive_targets_of_args,
}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use std::map {HashMap}

// ─── String helpers: `::` and `.` are the name grammar's only separators ──
//
// Identifiers cannot contain `.` or `:`, so splitting on them is
// unambiguous. Both are ASCII and can never land inside a multi-byte
// UTF-8 sequence, so the byte-oriented `String.slice` is safe here.

/// The index of the first `::` in `s`, or `none`.
#[partial]
def index_of_colon_colon_go (s : String) (len : I64) (i : I64) : Option I64 :=
    if I64.lt i (I64.sub len 1)
    then
        if String.beq (String.slice s i 2) "::"
        then Option.some i
        else index_of_colon_colon_go s len (I64.add i 1)
    else Option.none

def index_of_colon_colon (s : String) : Option I64 :=
    index_of_colon_colon_go s (String.length s) 0

/// The segments of a `.`-joined spelling (`List.length` -> `["List", "length"]`).
#[partial]
def split_dots_go (s : String) (len : I64) (from : I64) (i : I64) (acc : List String) : List String :=
    if I64.lt i len
    then
        split_dots_step s len from i acc (String.beq (String.slice s i 1) ".")
    else List.append acc (List.cons (String.drop from s) List.empty)

// `#[terminating]`: the loop is byte-index recursion (`i + 1` is not a
// structural subterm), and the mutual `split_dots_go`/`split_dots_step`
// split exists only to keep each case small.
#[terminating]
def split_dots_step (s : String) (len : I64) (from : I64) (i : I64) (acc : List String) (at_dot : Bool) : List String :=
    match at_dot {
        true =>
            let seg : String := String.slice s from (I64.sub i from) in
            split_dots_go s len (I64.add i 1) (I64.add i 1) (List.append acc (List.cons seg List.empty)),
        false => split_dots_go s len from (I64.add i 1) acc,
    }

def split_dots (s : String) : List String :=
    split_dots_go s (String.length s) 0 0 List.empty

/// The index of the last `.` in `s`, or `-1` when there is none.
#[partial]
def last_dot_index_go (s : String) (len : I64) (i : I64) (last : I64) : I64 :=
    if I64.lt i len
    then
        last_dot_index_go s len (I64.add i 1)
            (match String.beq (String.slice s i 1) "." {
                true => i,
                false => last,
            })
    else last

/// Everything after the last `.`, or the whole string when there is none
/// (`after_last_dot "cons"` is `"cons"`, unlike `lang/module.mo`'s
/// `tail_after_last_dot`, which returns `""` there -- the two callers
/// need the two different answers).
def after_last_dot (s : String) : String :=
    let last : I64 := last_dot_index_go s (String.length s) 0 (-1) in
    if I64.lt last 0 then s else String.drop (I64.add last 1) s

/// One `A.b::C.d` written reference, split the way lowering recorded it:
/// a `::` makes it module-qualified (dotted module half, `::`, dotted
/// name half -- `qualified_ref_symbol`'s convention, which is exactly
/// what `lower_name_global` stores in the `DebugName`), anything else
/// is bare. `none` means bare.
def qualified_half (s : String) : Option (Pair ModulePath String) :=
    match index_of_colon_colon s {
        Option.some i =>
            let mod_half : String := String.slice s 0 i in
            let name_half : String := String.drop (I64.add i 2) s in
            let mp : ModulePath := ModulePath.mk (List.map Identifier.id (split_dots mod_half)) in
            Option.some (Pair.pair mp name_half),
        Option.none => Option.none,
    }

// ─── What a `use` line selects ─────────────────────────────────────
//
// The self-hosted twin of the host's `AllowedNames`/`Selection`
// (rust/core/src/term.rs). Two independent axes, because the import forms
// differ on both:
//
// | form                     | `bare`          | `qual`          |
// |--------------------------|-----------------|-----------------|
// | `use M {a, b}`           | `only [a, b]`   | `only [a, b]`   |
// | `use M {*}`              | `all`           | `all`           |
// | `use M {}` / `use M`     | `only []`       | `all`           |
//
// A module absent from the selection map is unfiltered on both axes:
// the consumer itself, and the ambient modules.

// ─── Visibility ─────────────────────────────────────────────────────
//
// The visibility boundary is enforced HERE, in the same pass that decides
// whether a reference is imported, because this is the one place that
// already knows, for every name a file reaches, WHICH module declares it.
// Enforcement therefore happens at reference resolution -- not at import
// declarations -- on every load path (`check`/`run`/`test`/`build`/LSP),
// and it covers what an import-line rule cannot see: dotted items, globs,
// `open`s and the ambient prelude.

/// `consumer_mote` is the consumer FILE's mote, resolved from its
/// manifest -- not derived from `consumer`, because the entry module of a
/// `monad check path/to/file.mo` run is named by its stem (`copy_tests`),
/// while every module it reaches is mote-qualified (`init::copy`).
/// Deriving the consumer's mote from that path would put every sibling
/// module in a different mote. `None` means the file is outside any mote
/// (a script, or `examples/` at the virtual workspace root), where there
/// is no package boundary to cross -- the same answer the Rust host gives.
pub def visibility_visible_from (consumer : ModulePath) (consumer_mote : Option String) (owner : ModulePath) (vis : Visibility) : Bool :=
    if module_path_is_empty consumer then true
    else
        match vis {
            Visibility.pub_ => true,
            Visibility.priv_ => modpath_eq owner consumer,
            Visibility.package_private =>
                match consumer_mote {
                    Option.none => true,
                    Option.some c =>
                        match module_mote_of owner {
                            // A builtin or otherwise unowned declaration has
                            // no boundary to cross.
                            Option.none => true,
                            Option.some o => String.beq o c,
                        },
                },
        }

/// Which names of a module a brace list selects, along ONE axis.
/// `an_only` holds brace-item spellings, compared against a
/// declaration's own spelled name.
type AllowedNames {
    an_all,
    an_only (names : List String),
}

/// What one consumer's `use` lines select from ONE module.
pub struct Selection {
    bare : AllowedNames,
    qual : AllowedNames,
}

/// Unfiltered -- the shape an unlisted (consumer/ambient) module gets.
def selection_unfiltered : Selection := { bare := AllowedNames.an_all, qual := AllowedNames.an_all }

/// The shape every "no names bare, every name qualified" form shares:
/// bare `use M`, `use M {}`, and the entry a `use M {Sub {...}}`
/// registers for the sub-module itself.
def selection_qualified_only : Selection := { bare := AllowedNames.an_only List.empty, qual := AllowedNames.an_all }

def merge_allowed (a : AllowedNames) (b : AllowedNames) : AllowedNames :=
    match a {
        an_all => AllowedNames.an_all,
        an_only xs =>
            match b {
                an_all => AllowedNames.an_all,
                an_only ys => AllowedNames.an_only (List.append xs ys),
            },
    }

/// Union two selections of the same module (a file may `use M` more
/// than once). `an_all` absorbs `an_only`; duplicates inside the union
/// are harmless, membership is the only question ever asked.
def selection_merge (a : Selection) (b : Selection) : Selection :=
    { bare := merge_allowed a.bare b.bare, qual := merge_allowed a.qual b.qual }

/// Whether a listed spelling is a dotted prefix of `full` -- how
/// `{List}` drags in `List.cons` and `List.length` without naming
/// either. The boundary is a `.`, so `{length}` selects nothing of
/// `List.length`.
def dotted_prefix (full : String) (n : String) : Bool :=
    Bool.and (I64.gt (String.length full) (String.length n))
        (Bool.and (String.starts_with n full)
            (String.beq (String.slice full (String.length n) 1) "."))

/// Whether a brace-list spelling selects a declaration: exact spelling,
/// a constructor's own bare name, or a dotted prefix. The
/// `spelling`/`tail` pair is the declaration's (or item's) full and
/// last-segment spellings, precomputed so the walk never rescans.
#[partial]
def spelling_selected (names : List String) (spelling : String) (tail : String) (is_ctor : Bool) : Bool :=
    match names {
        List.empty => false,
        List.cons n rest =>
            if String.beq spelling n
            then true
            else
                if Bool.and is_ctor (String.beq tail n)
                then true
                else
                    if dotted_prefix spelling n
                    then true
                    else spelling_selected rest spelling tail is_ctor,
    }

/// One declaration a loaded module provides, as the judgment needs it:
/// the owner, the declaration's own spelled name, its bare tail, and
/// whether it is a constructor of an ordinary inductive (a `struct`'s
/// synthesized `mk` is deliberately absent, exactly as it is absent
/// from the host's `declaration_index`: no brace item could ever
/// select it).
pub struct DeclRow {
    owner : ModulePath,
    spelling : String,
    bare_tail : String,
    is_ctor : Bool,
    /// The declaration's own visibility. Constructors and class methods
    /// inherit the visibility of the block that declares them, exactly
    /// as the scope builder treats them. DELIBERATELY NOT DEFAULTED: the
    /// Rust host's checker does not give a defaulted field's expression a
    /// lowering path when the literal is lowered in another def, and
    /// `bare_finding` failed the self-compile with `UnresolvedAtom`
    /// because of it.
    vis : Visibility,
}

/// The spelling a brace item must use to select `row`'s declaration:
/// the whole spelled name for a def or type, only the last segment for
/// a constructor -- the same rule `validate_use_names`'s
/// `declared_names_of` (lang/module.mo) lists constructors by.
def item_spelling (row : DeclRow) : String :=
    if row.is_ctor then row.bare_tail else row.spelling

/// Whether a declaration may be written BARE (`List.length`) in a
/// consumer holding `sel` for its owner.
def selects_bare (sel : Selection) (row : DeclRow) : Bool :=
    match sel.bare {
        an_all => true,
        an_only ns => spelling_selected ns row.spelling row.bare_tail row.is_ctor,
    }

/// Whether it may be written QUALIFIED (`std::list::List.length`).
def selects_qual (sel : Selection) (row : DeclRow) : Bool :=
    match sel.qual {
        an_all => true,
        an_only ns =>
            let item : String := item_spelling row in
            spelling_selected ns item item row.is_ctor,
    }

/// `sel` with one more allowed name on both axes.
def with_allowed (sel : Selection) (name : String) : Selection :=
    {
        bare := match sel.bare {
            an_all => AllowedNames.an_all,
            an_only ns => AllowedNames.an_only (List.append ns (List.cons name List.empty)),
        },
        qual := match sel.qual {
            an_all => AllowedNames.an_all,
            an_only ns => AllowedNames.an_only (List.append ns (List.cons name List.empty)),
        },
    }

// ─── The `use` selection map ────────────────────────────────────────

/// Merge one selection into the map under `path`.
def sel_map_merge (path : ModulePath) (sel : Selection) (m : HashMap String Selection) : HashMap String Selection :=
    let key : String := show_module_path path in
    match str_map_lookup key m {
        Option.some existing => str_map_insert key (selection_merge existing sel) m,
        Option.none => str_map_insert key sel m,
    }

/// `use M {n}` and `use M {n as _}`: `n` is selected on both axes.
def sel_map_add_allowed (path : ModulePath) (name : String) (m : HashMap String Selection) : HashMap String Selection :=
    let key : String := show_module_path path in
    match str_map_lookup key m {
        Option.some sel => str_map_insert key (with_allowed sel name) m,
        Option.none => str_map_insert key (with_allowed selection_qualified_only name) m,
    }

/// The sub-module of a `use M {Sub {...}}` item: `M` plus one segment.
def use_sub_path (path : ModulePath) (n : Identifier) : ModulePath :=
    match path {
        ModulePath.mk ids => ModulePath.mk (List.append ids (List.cons n List.empty)),
    }

#[partial]
def sel_map_of_items (path : ModulePath) (items : List UseItem) (m : HashMap String Selection) : HashMap String Selection :=
    match items {
        List.empty => m,
        List.cons item rest =>
            match item {
                UseItem.use_name n => sel_map_of_items path rest (sel_map_add_allowed path (show_identifier n) m),
                // The name half is what has to exist; the alias is the
                // importer's own spelling and resolves to no declaration,
                // so it is never this check's business.
                UseItem.use_rename n _alias => sel_map_of_items path rest (sel_map_add_allowed path (show_identifier n) m),
                UseItem.use_glob => sel_map_of_items path rest (sel_map_merge path selection_unfiltered m),
                UseItem.use_sub n sub =>
                    sel_map_of_items path rest (sel_map_of_items (use_sub_path path n) sub (sel_map_merge (use_sub_path path n) selection_qualified_only m)),
                UseItem.use_sub_rename n _alias sub =>
                    sel_map_of_items path rest (sel_map_of_items (use_sub_path path n) sub (sel_map_merge (use_sub_path path n) selection_qualified_only m)),
            },
    }

/// One `use` decl's contribution to the map.
def sel_map_of_use (path : ModulePath) (filter : UseFilter) (m : HashMap String Selection) : HashMap String Selection :=
    match filter {
        // Bare `use M` and `use M {}` mean the same thing: every name
        // reachable QUALIFIED only.
        UseFilter.use_bare => sel_map_merge path selection_qualified_only m,
        UseFilter.use_items items =>
            if List.is_empty items
            then sel_map_merge path selection_qualified_only m
            else sel_map_of_items path items (sel_map_merge path selection_qualified_only m),
    }

/// The selection each of a module's own `use` lines makes, keyed by the
/// module it names. A module absent from the map is not imported by
/// name at all: the consumer itself, or one of the ambient modules.
#[partial]
def sel_map_of_decls (decls : List Decl) (m : HashMap String Selection) : HashMap String Selection :=
    match decls {
        List.empty => m,
        List.cons d rest =>
            match d {
                Decl.use_d path filter _public => sel_map_of_decls rest (sel_map_of_use path filter m),
                _ => sel_map_of_decls rest m,
            },
    }

// ─── The ambient modules ────────────────────────────────────────────
//
// The language's own trio -- `prelude`, `init`, `std` -- plus whatever
// their hub `lib.mo` files re-export through `pub use`, transitively:
// every file sees those whole, without a `use` line. The host computes
// the closure from the hub SOURCES (`ambient_seen_modules`,
// rust/core/src/term/module.rs); this gate computes it from the loaded
// world, which is the same set once the loader has walked the trio's
// own `pub use` targets.

/// The ambient trio, in `ModulePath` form. Duplicating the three
/// one-liners `lang/module.mo` holds (`prelude_module_path` and
/// friends) rather than importing them: `lang/module.mo` imports this
/// module for the gate, so the import would be a cycle.
def prelude_module_path : ModulePath := ModulePath.mk [Identifier.id "prelude"]

def init_module_path : ModulePath := ModulePath.mk [Identifier.id "init"]

def std_module_path : ModulePath := ModulePath.mk [Identifier.id "std"]

/// Every module the world holds at `path`, or `none`.
#[partial]
def world_decls_of (world : List (Pair ModulePath (List Decl))) (path : ModulePath) : Option (List Decl) :=
    match world {
        List.empty => Option.none,
        List.cons entry rest =>
            match entry {
                Pair.pair mp ds =>
                    if modpath_eq mp path
                    then Option.some ds
                    else world_decls_of rest path,
            },
    }

/// The modules a `pub use` names.
#[partial]
def pub_use_targets (decls : List Decl) (acc : List ModulePath) : List ModulePath :=
    match decls {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.use_d path _filter public =>
                    if public
                    then pub_use_targets rest (List.cons path acc)
                    else pub_use_targets rest acc,
                _ => pub_use_targets rest acc,
            },
    }

/// The `pub use` closure of the ambient trio among the loaded world.
#[partial]
def ambient_go (world : List (Pair ModulePath (List Decl))) (frontier : List ModulePath) (seen : HashMap String Bool) : HashMap String Bool :=
    match frontier {
        List.empty => seen,
        List.cons mp rest =>
            let key : String := show_module_path mp in
            match str_map_lookup key seen {
                Option.some _ => ambient_go world rest seen,
                Option.none =>
                    let seen_now : HashMap String Bool := str_map_insert key true seen in
                    match world_decls_of world mp {
                        Option.some ds => ambient_go world (List.append (pub_use_targets ds List.empty) rest) seen_now,
                        Option.none => ambient_go world rest seen_now,
                    },
            },
    }

def ambient_seen (world : List (Pair ModulePath (List Decl))) : HashMap String Bool :=
    ambient_go world [prelude_module_path, init_module_path, std_module_path] str_map_empty

// ─── The declaration index ──────────────────────────────────────────

/// Index one row under `key`. The key is the spelling a REFERENCE
/// writes; the row carries the declaration's own spelled name, which
/// is what a brace item has to say.
def index_add_row (key : String) (row : DeclRow) (m : HashMap String (List DeclRow)) : HashMap String (List DeclRow) :=
    match str_map_lookup key m {
        Option.some rows => str_map_insert key (List.append rows (List.cons row List.empty)) m,
        Option.none => str_map_insert key (List.cons row List.empty) m,
    }

/// One constructor, indexed twice: under its bare tail and under its
/// full name. The row's `spelling` is the TWO-segment form
/// (`InductiveName.ctor`), mirroring how the HOST stores a constructor
/// (`term::induct_constructor`, rust/core/src/term.rs) even though this
/// parser writes it single-segment: the dotted-prefix rule that lets
/// `use std::stream {StreamErrorKind}` select
/// `StreamErrorKind.permission_denied` is judged against the
/// declaration's own two-segment spelling, and the two compilers must
/// agree on the SET or CI's dual-compiler corpus check rejects a file
/// one accepts. The bare tail stays the ctor's own single segment,
/// which is the only spelling a brace item can select it by.
def index_ctor (owner : ModulePath) (ind : String) (vis : Visibility) (name : NamePath) (m : HashMap String (List DeclRow)) : HashMap String (List DeclRow) :=
    let spelling : String :=
        String.concat ind (String.concat "." (show_name_path name)) in
    let row : DeclRow := { owner := owner, spelling := spelling, bare_tail := after_last_dot spelling, is_ctor := true, vis := vis } in
    index_add_row row.bare_tail row (index_add_row spelling row m)

/// A class's methods, indexed under their QUALIFIED spelling only
/// (`Map.empty`), not under the bare tail. A method is reached through
/// its type's name, and indexing `empty` bare would make every class in
/// the corpus a candidate of one short name -- an ambiguity report, not a
/// visibility one. Constructors are the opposite case (`index_ctor`
/// indexes both) because source writes them bare.
#[partial]
def index_class_methods (owner : ModulePath) (cls : String) (vis : Visibility) (methods : List ClassDef) (m : HashMap String (List DeclRow)) : HashMap String (List DeclRow) :=
    match methods {
        List.empty => m,
        List.cons md rest =>
            match md {
                ClassDef.mk name _typ _default =>
                    let spelling : String :=
                        String.concat cls (String.concat "." (show_identifier name)) in
                    index_class_methods owner cls vis rest
                        (index_add_row spelling
                            { owner := owner, spelling := spelling, bare_tail := show_identifier name, is_ctor := false, vis := vis }
                            m),
            },
    }

#[partial]
def index_decl (owner : ModulePath) (d : Decl) (m : HashMap String (List DeclRow)) : HashMap String (List DeclRow) :=
    match d {
        Decl.def_d def_ =>
            match def_ {
                Def.mk { name, vis, .. } =>
                    index_add_row (show_name_path name)
                        { owner := owner, spelling := show_name_path name, bare_tail := after_last_dot (show_name_path name), is_ctor := false, vis := vis }
                        m,
            },
        // Macro declarations are EXEMPT from the boundary: the decl-gen
        // form (`defmacro f p := decls { ... }`, `DeclGen`) carries no
        // visibility field in either compiler, so a macro name that
        // crossed a mote could not be marked `pub` -- the rule would have
        // no remedy to offer. They are compile-time-only and expanded
        // away before checking; the declarations they generate carry
        // their own visibility.
        Decl.def_macro_d def_ =>
            match def_ {
                Def.mk { name, .. } =>
                    index_add_row (show_name_path name)
                        { owner := owner, spelling := show_name_path name, bare_tail := after_last_dot (show_name_path name), is_ctor := false, vis := Visibility.pub_ }
                        m,
            },
        Decl.decl_gen_d name _params _decls _attrs =>
            index_add_row (show_name_path name)
                { owner := owner, spelling := show_name_path name, bare_tail := after_last_dot (show_name_path name), is_ctor := false, vis := Visibility.pub_ }
                m,
        Decl.inductive_d ind =>
            match ind {
                Inductive.mk name _params _typ constructors _attrs vis =>
                    index_ctors owner (show_name_path name) vis constructors
                        (index_add_row (show_name_path name)
                            { owner := owner, spelling := show_name_path name, bare_tail := after_last_dot (show_name_path name), is_ctor := false, vis := vis }
                            m),
            },
        Decl.struct_d st =>
            match st {
                Struct.mk name _fields _attrs vis =>
                    index_add_row (show_identifier name)
                        { owner := owner, spelling := show_identifier name, bare_tail := show_identifier name, is_ctor := false, vis := vis }
                        m,
            },
        Decl.class_d cls =>
            match cls {
                Class.mk name _params _constraints methods vis =>
                    index_class_methods owner (show_identifier name) vis methods
                        (index_add_row (show_identifier name)
                            { owner := owner, spelling := show_identifier name, bare_tail := show_identifier name, is_ctor := false, vis := vis }
                            m),
            },
        // Instances are deliberately not indexed, mirroring the host's
        // `declaration_index` (rust/core/src/term/module.rs): an instance is
        // reached through class resolution, and its own name binds no
        // reference a `use` line could be asked about. Their visibility is
        // enforced in the instance registries instead (`lang/scope.mo`).
        _ => m,
    }

#[partial]
def index_ctors (owner : ModulePath) (ind : String) (vis : Visibility) (cns : List InductConstructor) (m : HashMap String (List DeclRow)) : HashMap String (List DeclRow) :=
    match cns {
        List.empty => m,
        List.cons cn rest =>
            match cn {
                InductConstructor.mk name _params _typ => index_ctors owner ind vis rest (index_ctor owner ind vis name m),
            },
    }

#[partial]
def index_decls (owner : ModulePath) (decls : List Decl) (m : HashMap String (List DeclRow)) : HashMap String (List DeclRow) :=
    match decls {
        List.empty => m,
        List.cons d rest => index_decls owner rest (index_decl owner d m),
    }

/// Every spelling a loaded module's declarations can be REFERRED to by,
/// mapped to the declaration it names. Built from the PARSED decls of
/// the whole loaded world; names a decl-gen macro only GENERATES are
/// invisible here (and equally invisible as references, so the silence
/// is two-sided).
#[partial]
def declaration_index (world : List (Pair ModulePath (List Decl))) (m : HashMap String (List DeclRow)) : HashMap String (List DeclRow) :=
    match world {
        List.empty => m,
        List.cons entry rest =>
            match entry {
                Pair.pair mp ds => declaration_index rest (index_decls mp ds m),
            },
    }

// ─── The consumer's own names ────────────────────────────────────────

/// The spellings the consumer's own declarations bind, plus every
/// constructor tail its inductives carry and the `mk` a `struct`/`class`
/// synthesizes (the host's `own_declared_keys` and its constructor
/// reasoning, rust/core/src/term/module.rs): a name the consumer declares
/// itself is never "reached from another module". The expanded decl
/// list's declared names are folded in too, so a name the load-time
/// macro expansion generates (`Point.x` from `derive_lens! Point`) is
/// this module's own, exactly as the host folds the elaborated
/// module's names in.
#[partial]
def own_keys_go (decls : List Decl) (m : HashMap String Bool) : HashMap String Bool :=
    match decls {
        List.empty => m,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk { name, .. } => own_keys_go rest (str_map_insert (show_name_path name) true m),
                    },
                Decl.def_macro_d def_ =>
                    match def_ {
                        Def.mk { name, .. } => own_keys_go rest (str_map_insert (show_name_path name) true m),
                    },
                Decl.decl_gen_d name _params _decls _attrs =>
                    own_keys_go rest (str_map_insert (show_name_path name) true m),
                Decl.inductive_d ind =>
                    match ind {
                        Inductive.mk name _params _typ constructors _attrs _vis =>
                            own_ctors_go (show_name_path name) constructors (own_keys_go rest (str_map_insert (show_name_path name) true m)),
                    },
                Decl.struct_d st =>
                    match st {
                        Struct.mk name _fields _attrs _vis =>
                            own_keys_go rest (str_map_insert (show_identifier name) true (str_map_insert "mk" true m)),
                    },
                Decl.class_d cls =>
                    match cls {
                        Class.mk name _params _constraints _methods _vis =>
                            own_keys_go rest (str_map_insert (show_identifier name) true (str_map_insert "mk" true m)),
                    },
                // The host's `own` set is `names_of_decls`, which is every
                // decl's `to_ref` (rust/core/src/term.rs): the open's PATH is
                // an `open Param {mk}` file's own name for `Param`, the
                // use's flattened module path is its own name for that
                // path, and an infix/instance carries its own name too.
                // Skipping any of them is a divergence: the host accepts
                // `lang/src/codegen/test/compile_tests.mo` (bare `Param`
                // covered by its `open Param {mk}`) where a walk without
                // the open path would report it.
                Decl.use_d path _filter _public =>
                    own_keys_go rest (str_map_insert (show_module_path path) true m),
                Decl.open_d path _filter =>
                    own_keys_go rest (str_map_insert (show_name_path path) true m),
                Decl.infix_d _op path _vis =>
                    own_keys_go rest (str_map_insert (show_name_path path) true m),
                Decl.instance_d ins =>
                    match ins {
                        Instance.mk { name, .. } =>
                            own_keys_go rest (str_map_insert (show_identifier name) true m),
                    },
                // `to_ref`'s placeholders, kept for faithfulness; neither
                // spelling can be written at a reference site, so both are
                // inert here.
                Decl.macro_call_d _name _args =>
                    own_keys_go rest (str_map_insert "__macro_call__" true m),
                Decl.mote_d _attr =>
                    own_keys_go rest (str_map_insert "__mote_attr__" true m),
                // The host's `module()` unwraps scoped opens before its
                // walks, so the wrapped declaration's names and
                // references both count.
                Decl.scoped_open_d _path _filter inner => own_keys_go rest (own_keys_go (List.cons inner List.empty) m),
                _ => own_keys_go rest m,
            },
    }

/// The bare tail AND the full two-segment spelling of every own
/// constructor -- `own_declared_keys`' constructor half: the bare
/// tail is what a bare reference writes, the full spelling what a
/// qualified one does, and both are this module's own names.
#[partial]
def own_ctors_go (ind : String) (cns : List InductConstructor) (m : HashMap String Bool) : HashMap String Bool :=
    match cns {
        List.empty => m,
        List.cons cn rest =>
            match cn {
                InductConstructor.mk name _params _typ =>
                    own_ctors_go ind rest
                        (str_map_insert (String.concat ind (String.concat "." (show_name_path name))) true
                            (str_map_insert (show_name_path name) true m)),
            },
    }

// ─── The reference walk ────────────────────────────────────────────

/// The names a module's own declarations reference, kept apart by the
/// axis each one was WRITTEN on -- the twin of the host's `References`
/// (rust/core/src/term/module.rs). Merging the axes would make
/// `use std::base {}` plus a qualified `std::base::Ordering.lt` look
/// unimported.
pub struct Refs {
    bare : List String,
    bare_seen : HashMap String Bool,
    qualified : List (Pair ModulePath String),
    qual_seen : HashMap String Bool,
}

def refs_empty : Refs := { bare := List.empty, bare_seen := str_map_empty, qualified := List.empty, qual_seen := str_map_empty }

def refs_add_bare (name : String) (refs : Refs) : Refs :=
    match str_map_lookup name refs.bare_seen {
        Option.some _ => refs,
        Option.none =>
            { refs with bare := List.append refs.bare (List.cons name List.empty), bare_seen := str_map_insert name true refs.bare_seen },
    }

/// A qualified reference names its module outright, so no local binder
/// can shadow it; the walk only ever sees it as a free variable.
def refs_add_qualified (mp : ModulePath) (name : String) (refs : Refs) : Refs :=
    let key : String := String.concat (show_module_path mp) (String.concat "::" name) in
    match str_map_lookup key refs.qual_seen {
        Option.some _ => refs,
        Option.none =>
            {
                refs with
                qualified := List.append refs.qualified (List.cons (Pair.pair mp name) List.empty),
                qual_seen := str_map_insert key true refs.qual_seen,
            },
    }

/// One free variable's written spelling, on the axis it was written on.
def refs_add_free (s : String) (refs : Refs) : Refs :=
    match qualified_half s {
        Option.some halves =>
            match halves {
                Pair.pair mp name => refs_add_qualified mp name refs,
            },
        Option.none => refs_add_bare s refs,
    }

/// A `DebugName` of a free variable, classified. `unnamed` carries no
/// spelling at all.
def refs_add_debug (dbg : DebugName) (refs : Refs) : Refs :=
    match dbg {
        DebugName.named id => refs_add_free (show_identifier id) refs,
        DebugName.unnamed => refs,
    }

#[partial]
def collect_term (t : Term) (refs : Refs) : Refs :=
    match t {
        // A bound variable is a non-negative index; only a free
        // variable (`sentinel`) is a reference, and the lowering has
        // already done the binder tracking that the host's `Binders`
        // stack exists for.
        Term.var idx dbg =>
            if idx == sentinel then refs_add_debug dbg refs else refs,
        // A macro name resolves in a separate namespace, but the NAME is
        // still a reference the consumer reaches from its defining
        // module -- the host's `NameRef::Macro` arm collects it bare
        // the same way.
        Term.var_macro idx dbg =>
            if idx == sentinel then refs_add_debug dbg refs else refs,
        Term.lam _b typ body => collect_term body (collect_term typ refs),
        Term.pi _b arg ret => collect_term ret (collect_term arg refs),
        Term.app fun arg => collect_term arg (collect_term fun refs),
        Term.lit value => collect_literal value refs,
        Term.ntv native =>
            match native {
                Native.mk { args, .. } => collect_opt_terms args refs,
            },
        Term.con c =>
            match c {
                Con.mk { typ_name, args, .. } => collect_opt_terms args (refs_add_bare (show_name_path typ_name) refs),
            },
        Term.hole => refs,
        Term.quote_ inner => collect_term inner refs,
        Term.ctx _loc inner => collect_term inner refs,
        // A sort's level variables are binder-scoped, not module
        // references; a cubical primitive's arguments are interval
        // terms. Neither is a declaration reference on the host either
        // (its walk has no arm for either).
        Term.sort _level => refs,
        Term.cubical _c => refs,
        // Unlike `cubical`'s bare interval terms, `elim`'s fields are
        // ordinary ambient terms that can reference module declarations
        // (a constructor in a minor, a class method in a dependent
        // motive, ...) -- same treatment as `Literal.if_`/`match_` just
        // below, generalized to a plain list of minors instead of
        // `MatchCase`s.
        Term.elim e =>
            collect_terms e.minors (collect_term e.motive (collect_terms e.params (collect_term e.scrutinee refs))),
    }

#[partial]
def collect_opt_terms (args : List (Option Term)) (refs : Refs) : Refs :=
    match args {
        List.empty => refs,
        List.cons arg rest =>
            collect_opt_terms rest
                (match arg {
                    Option.some t => collect_term t refs,
                    Option.none => refs,
                }),
    }

#[partial]
def collect_literal (l : Literal) (refs : Refs) : Refs :=
    match l {
        Literal.str _ => refs,
        Literal.char _ => refs,
        Literal.num _ _ => refs,
        Literal.flt _ _ => refs,
        Literal.if_ one two three => collect_term three (collect_term two (collect_term one refs)),
        Literal.match_ value cases => collect_cases cases (collect_term value refs),
        Literal.struct_lit fields type_name =>
            collect_lit_fields fields (match type_name {
                Option.some t => collect_term t refs,
                Option.none => refs,
            }),
        Literal.struct_update base fields => collect_lit_fields fields (collect_term base refs),
    }

/// A match arm's constructor name is a bare reference -- this is how a
/// constructor used only in a pattern, never in a call position, still
/// counts.
#[partial]
def collect_cases (cases : List MatchCase) (refs : Refs) : Refs :=
    match cases {
        List.empty => refs,
        List.cons case rest =>
            match case {
                MatchCase.mk { name, body, .. } =>
                    collect_cases rest (collect_term body (refs_add_bare (show_identifier name) refs)),
            },
    }

#[partial]
def collect_lit_fields (fields : List StructLitField) (refs : Refs) : Refs :=
    match fields {
        List.empty => refs,
        List.cons field rest =>
            match field {
                StructLitField.mk { value, .. } => collect_lit_fields rest (collect_term value refs),
            },
    }

#[partial]
def collect_param (p : Param) (refs : Refs) : Refs :=
    match p {
        Param.mk { type_, default, .. } =>
            collect_term type_
                (match default {
                    Option.some d => collect_term d refs,
                    Option.none => refs,
                }),
    }

#[partial]
def collect_params (params : List Param) (refs : Refs) : Refs :=
    match params {
        List.empty => refs,
        List.cons p rest => collect_params rest (collect_param p refs),
    }

/// A type constraint names its class -- a bare reference, whatever the
/// constraint is attached to.
#[partial]
def collect_constraints (constraints : List TypeConstraint) (refs : Refs) : Refs :=
    match constraints {
        List.empty => refs,
        List.cons tc rest =>
            match tc {
                TypeConstraint.mk { cls, .. } => collect_constraints rest (refs_add_bare (show_name_path cls) refs),
            },
    }

#[partial]
def collect_def (d : Def) (refs : Refs) : Refs :=
    match d {
        Def.mk { typ, term, params, constraints, .. } =>
            collect_constraints constraints (collect_term term (collect_term typ (collect_params params refs))),
    }

#[partial]
def collect_struct_fields (fields : List StructField) (refs : Refs) : Refs :=
    match fields {
        List.empty => refs,
        List.cons field rest =>
            match field {
                StructField.mk { typ, default, .. } =>
                    collect_struct_fields rest
                        (collect_term typ
                            (match default {
                                Option.some d => collect_term d refs,
                                Option.none => refs,
                            })),
            },
    }

#[partial]
def collect_class_methods (methods : List ClassDef) (refs : Refs) : Refs :=
    match methods {
        List.empty => refs,
        List.cons method rest =>
            match method {
                ClassDef.mk { typ, default, .. } =>
                    collect_class_methods rest
                        (collect_term typ
                            (match default {
                                Option.some d => collect_term d refs,
                                Option.none => refs,
                            })),
            },
    }

/// One top-level declaration's references. Only the kinds the host's
/// `collect_module_references` walks are walked; `decl_gen_d` bodies
/// and `infix_d` targets are deliberately invisible to the host's
/// completeness check too.
#[partial]
def collect_decl (d : Decl) (refs : Refs) : Refs :=
    match d {
        Decl.def_d def_ => collect_def def_ refs,
        Decl.def_macro_d def_ => collect_def def_ refs,
        Decl.inductive_d ind =>
            match ind {
                Inductive.mk _name params typ constructors _attrs _vis =>
                    collect_ctors constructors (collect_term typ (collect_params params refs)),
            },
        Decl.struct_d st =>
            match st {
                Struct.mk _name fields _attrs _vis => collect_struct_fields fields refs,
            },
        Decl.class_d cls =>
            match cls {
                Class.mk _name params constraints methods _vis =>
                    collect_class_methods methods (collect_constraints constraints (collect_params params refs)),
            },
        Decl.instance_d ins =>
            match ins {
                Instance.mk { cls, constraints, args, defs, .. } =>
                    collect_defs defs (collect_constraints constraints (collect_terms args (refs_add_bare (show_name_path cls) refs))),
            },
        // `open ... in <decl>`: the wrapped declaration is one of the
        // module's own, and the host's `module()` unwraps it before
        // walking.
        Decl.scoped_open_d _path _filter inner => collect_decl inner refs,
        Decl.macro_call_d name _args =>
            // The macro NAME is the reference (the host's
            // `collect_macro_call_names`); the arguments are
            // deliberately not walked there, and not here either.
            refs_add_bare (show_identifier name) refs,
        _ => refs,
    }

#[partial]
def collect_ctors (cns : List InductConstructor) (refs : Refs) : Refs :=
    match cns {
        List.empty => refs,
        List.cons cn rest =>
            match cn {
                InductConstructor.mk _name params typ => collect_ctors rest (collect_term typ (collect_params params refs)),
            },
    }

#[partial]
def collect_terms (terms : List Term) (refs : Refs) : Refs :=
    match terms {
        List.empty => refs,
        List.cons t rest => collect_terms rest (collect_term t refs),
    }

#[partial]
def collect_defs (defs : List Def) (refs : Refs) : Refs :=
    match defs {
        List.empty => refs,
        List.cons d rest => collect_defs rest (collect_def d refs),
    }

#[partial]
def collect_decls (decls : List Decl) (refs : Refs) : Refs :=
    match decls {
        List.empty => refs,
        List.cons d rest => collect_decls rest (collect_decl d refs),
    }

// ─── Macro invocation names ─────────────────────────────────────────

/// The `#[derive Target]` targets one attribute asks for.
#[partial]
def derive_targets_of_attrs (attrs : List Attribute) (acc : List Identifier) : List Identifier :=
    match attrs {
        List.empty => acc,
        List.cons attr rest =>
            match attr {
                Attribute.mk name args =>
                    if id_eq name (Identifier.id "derive")
                    then derive_targets_of_attrs rest (List.append acc (derive_targets_of_args args))
                    else derive_targets_of_attrs rest acc,
            },
    }

/// The macro a registered handler registered for `target`, or `none`.
#[partial]
def derive_macro_of_target (regs : List DeriveHandlerReg) (target : Identifier) : Option Identifier :=
    match regs {
        List.empty => Option.none,
        List.cons reg rest =>
            if id_eq reg.dr_target target
            then Option.some reg.dr_macro
            else derive_macro_of_target rest target,
    }

/// The bare macro names a decl list invokes: declaration-position
/// `name!` calls, plus each `#[derive ...]` attribute dispatched to its
/// registered handler. Both are names the consumer reaches from the
/// macro's defining module, so both are the `use` line's business.
#[partial]
def macro_call_names_go (decls : List Decl) (regs : List DeriveHandlerReg) (acc : List String) : List String :=
    match decls {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.macro_call_d name _args =>
                    macro_call_names_go rest regs (List.append acc (List.cons (show_identifier name) List.empty)),
                Decl.inductive_d ind =>
                    match ind {
                        Inductive.mk _name _params _typ _ctors attrs _vis =>
                            macro_call_names_go rest regs (append_derive_names (derive_targets_of_attrs attrs List.empty) regs acc),
                    },
                _ => macro_call_names_go rest regs acc,
            },
    }

#[partial]
def append_derive_names (targets : List Identifier) (regs : List DeriveHandlerReg) (acc : List String) : List String :=
    match targets {
        List.empty => acc,
        List.cons target rest =>
            match derive_macro_of_target regs target {
                Option.some macro_name =>
                    append_derive_names rest regs (List.append acc (List.cons (show_identifier macro_name) List.empty)),
                // "Unresolved is not an error" here as everywhere in the
                // derive machinery: a target no registered handler
                // declares is the macro system's own report to make.
                Option.none => append_derive_names rest regs acc,
            },
    }

/// The whole world's `#[derive_handler ...]` registrations.
#[partial]
def derive_registry (world : List (Pair ModulePath (List Decl))) (acc : List DeriveHandlerReg) : List DeriveHandlerReg :=
    match world {
        List.empty => acc,
        List.cons entry rest =>
            match entry {
                Pair.pair mp ds => derive_registry rest (List.append acc (derive_handler_regs_of_decls mp ds)),
            },
    }

// ─── `open` ─────────────────────────────────────────────────────────

/// The names an `open T {n}` makes bare. An unfiltered `open T` can put
/// an unbounded set of names in scope, so anything said about the rest
/// of the file would be a guess: `collect_opens` returns `none` for the
/// whole file there, and silence is a false negative, never a false
/// positive.
pub struct Opens {
    names : HashMap String Bool,
}

#[partial]
def opens_add_names (names : List Identifier) (opens : Opens) : Opens :=
    match names {
        List.empty => opens,
        List.cons n rest =>
            let spelling : String := show_identifier n in
            let with_full : Opens :=
                { opens with names := str_map_insert spelling true opens.names } in
            opens_add_names rest { with_full with names := str_map_insert (after_last_dot spelling) true with_full.names },
    }

#[partial]
def collect_opens (decls : List Decl) (opens : Opens) : Option Opens :=
    match decls {
        List.empty => Option.some opens,
        List.cons d rest =>
            match d {
                Decl.open_d _path filter => opens_filter_step filter rest opens,
                Decl.scoped_open_d _path filter _inner => opens_filter_step filter rest opens,
                _ => collect_opens rest opens,
            },
    }

// `#[terminating]`: mutually recursive with `collect_opens`, and the
// checker is positional about which argument flows where.
#[terminating]
def opens_filter_step (filter : OpenFilter) (rest : List Decl) (opens : Opens) : Option Opens :=
    match filter {
        open_all => Option.none,
        open_only names => collect_opens rest (opens_add_names names opens),
    }

// ─── The judgment ───────────────────────────────────────────────────

/// Everything the two judgment loops need, in one value: threading
/// eight arguments through two mutually-recursive walks is how the
/// wrong argument ends up in the wrong slot.
struct Judge {
    consumer : ModulePath,
    /// The consumer FILE's mote, from its manifest (`None` outside any
    /// mote). See `visibility_visible_from`.
    consumer_mote : Option String,
    opens : HashMap String Bool,
    selection : HashMap String Selection,
    ambient : HashMap String Bool,
    index : HashMap String (List DeclRow),
    own : HashMap String Bool,
    file_path : String,
}

/// Why a name is not usable here. The two are different failures with
/// different remedies, so they render differently: an unimported name is
/// reachable once named in a `use` line, while a hidden one is not
/// reachable from this mote at all.
type FindingKind {
    fk_unimported,
    fk_hidden,
}

struct Finding {
    name : String,
    owner : ModulePath,
    spelling : String,
    kind : FindingKind,
    vis : Visibility,
}

/// One finding, in the host's message shape.
def render_finding (file_path : String) (f : Finding) : String :=
    match f.kind {
        fk_unimported =>
            let module_str : String := module_path_to_string_colon f.owner in
            String.concat_all [
                "error: `", f.name, "` is not imported\n",
                "  `", f.spelling, "` is declared in `", module_str, "`\n",
                "  hint: add it to a `use ", module_str, " {...}` line -- `use ", module_str, " {", f.spelling, "}` names it\n",
                "  in ", file_path,
            ],
        fk_hidden =>
            let module_str : String := module_path_to_string_colon f.owner in
            let declaration : String :=
                match f.vis {
                    Visibility.priv_ =>
                        String.concat_all ["`", f.spelling, "` is declared `priv` in `", module_str, "`"],
                    _ =>
                        String.concat_all ["`", f.spelling, "` is declared in `", module_str, "` and is not marked `pub`"],
                } in
            let mote_hint : String :=
                match module_mote_of f.owner {
                    Option.some m => String.concat_all [" in mote `", m, "`"],
                    Option.none => "",
                } in
            String.concat_all [
                "error: `", f.name, "` is not visible here\n",
                "  ", declaration, "\n",
                "  hint: mark `", f.spelling, "` `pub`", mote_hint, ", or reword the reference\n",
                "  in ", file_path,
            ],
    }

def set_member (key : String) (m : HashMap String Bool) : Bool :=
    match str_map_lookup key m {
        Option.some _ => true,
        Option.none => false,
    }

def ambient_member (j : Judge) (mp : ModulePath) : Bool :=
    set_member (show_module_path mp) j.ambient

/// The selection a consumer holds for `mp`, if it holds one.
def selection_of (j : Judge) (mp : ModulePath) : Option Selection :=
    str_map_lookup (show_module_path mp) j.selection

/// The row naming `mp`'s declaration called `name`, if the index has
/// one: a qualified reference names its module outright, so there is
/// no guessing which declaration was meant.
#[partial]
def row_of_owner (rows : Option (List DeclRow)) (mp : ModulePath) : Option DeclRow :=
    match rows {
        Option.none => Option.none,
        Option.some list =>
            match list {
                List.empty => Option.none,
                List.cons row rest =>
                    if modpath_eq row.owner mp
                    then Option.some row
                    else row_of_owner (Option.some rest) mp,
            },
    }

/// Whether the consumer's mote may see `row`'s declaration at all.
///
/// The own-module check comes first and does not consult motes: the ENTRY
/// module is named by its file stem (`foldable`, `optics_tests`), not
/// mote-qualified (`init::foldable`), so a file's own declarations would
/// otherwise look like another mote's. Everything a module declares is
/// visible to it, by definition.
def row_visible (j : Judge) (row : DeclRow) : Bool :=
    modpath_eq row.owner j.consumer
        || visibility_visible_from j.consumer j.consumer_mote row.owner row.vis

/// Whether a module-qualified reference is SELECTED by the consumer's
/// imports -- the import half of the judgment, before visibility.
def qualified_selected (j : Judge) (mp : ModulePath) (row : DeclRow) : Bool :=
    ambient_member j mp
        || match selection_of j mp {
            Option.some sel => selects_qual sel row,
            Option.none => false,
        }

/// Whether a module-qualified reference is accounted for.
def qualified_visible (j : Judge) (mp : ModulePath) (name : String) (row : DeclRow) : Bool :=
    modpath_eq mp j.consumer
        || set_member name j.own
        || set_member name j.opens
        || (qualified_selected j mp row && row_visible j row)

/// Whether `row` is accounted for by the IMPORT rules alone, ignoring
/// visibility. The distinction matters to the message: an unimported
/// name is fixed by naming it in a `use` line, while a hidden one is not
/// reachable from this mote at all and must be marked `pub`.
#[partial]
def row_imported (j : Judge) (row : DeclRow) : Bool :=
    modpath_eq row.owner j.consumer
        || ambient_member j row.owner
        || match selection_of j row.owner {
            Option.some sel => selects_bare sel row,
            Option.none => false,
        }

/// Whether a bare reference's candidates include one that is accounted
/// for: the consumer itself, an ambient owner, or a `use` selection
/// that names it bare -- AND whose declaration this mote may see.
#[partial]
def bare_reachable (j : Judge) (rows : List DeclRow) : Bool :=
    match rows {
        List.empty => false,
        List.cons row rest =>
            if Bool.and (row_imported j row) (row_visible j row)
            then true
            else bare_reachable j rest,
    }

/// The first candidate the import rules DO account for but visibility
/// does not: the declaration that has to be marked `pub`.
#[partial]
def bare_hidden_row (j : Judge) (rows : List DeclRow) : Option DeclRow :=
    match rows {
        List.empty => Option.none,
        List.cons row rest =>
            if Bool.and (row_imported j row) (Bool.not (row_visible j row))
            then Option.some row
            else bare_hidden_row j rest,
    }

/// Prefer naming a module the consumer already `use`s -- the fix is
/// then one more item in an existing brace list, not a new line.
#[partial]
def pick_row (j : Judge) (rows : List DeclRow) (fallback : DeclRow) : DeclRow :=
    match rows {
        List.empty => fallback,
        List.cons row rest =>
            match selection_of j row.owner {
                Option.some _ => row,
                Option.none => pick_row j rest fallback,
            },
    }

struct JudgeOut {
    findings : List Finding,
    seen : HashMap String Bool,
}

/// The module-qualified half: every `M::name` the consumer wrote.
#[partial]
def judge_qualified (j : Judge) (items : List (Pair ModulePath String)) (seen : HashMap String Bool) (acc : List Finding) : JudgeOut :=
    match items {
        List.empty => { findings := acc, seen := seen },
        List.cons item rest =>
            match item {
                Pair.pair mp name =>
                    match row_of_owner (str_map_lookup name j.index) mp {
                        // Not a top-level declaration of the named module
                        // at all: no brace item could name it, so there is
                        // nothing to suggest. Whether the name exists
                        // anywhere is resolution's business.
                        Option.none => judge_qualified j rest seen acc,
                        Option.some row =>
                            if qualified_visible j mp name row
                            then judge_qualified j rest seen acc
                            else
                                if set_member name seen
                                then judge_qualified j rest seen acc
                                else
                                    let kind : FindingKind :=
                                        if Bool.and (qualified_selected j mp row) (Bool.not (row_visible j row))
                                        then FindingKind.fk_hidden
                                        else FindingKind.fk_unimported in
                                    let finding : Finding :=
                                        { name := name, owner := mp, spelling := item_spelling row,
                                          kind := kind, vis := row.vis } in
                                    judge_qualified j rest (str_map_insert name true seen) (List.append acc (List.cons finding List.empty)),
                    },
            },
    }

/// The bare half: every name the consumer wrote without a module.
#[partial]
def judge_bare (j : Judge) (names : List String) (seen : HashMap String Bool) (acc : List Finding) : JudgeOut :=
    match names {
        List.empty => { findings := acc, seen := seen },
        List.cons name rest =>
            if set_member name j.own || set_member name j.opens || set_member name seen
            then judge_bare j rest seen acc
            else
                match str_map_lookup name j.index {
                    // Declared in no loaded module at all: either a local
                    // binding or a genuinely unknown name, which resolution
                    // reports on its own terms.
                    Option.none => judge_bare j rest (str_map_insert name true seen) acc,
                    Option.some rows =>
                        if bare_reachable j rows
                        then judge_bare j rest (str_map_insert name true seen) acc
                        else
                            let finding : Finding := bare_finding j name rows in
                            judge_bare j rest (str_map_insert name true seen) (List.append acc (List.cons finding List.empty)),
                },
    }

def first_row (rows : List DeclRow) : DeclRow :=
    match rows {
        List.cons row _rest => row,
        List.empty => { owner := init_module_path, spelling := "", bare_tail := "", is_ctor := false, vis := Visibility.package_private },
    }

/// Why a bare name with no reachable candidate is unusable. A candidate
/// the import rules account for but visibility does not is a `pub`
/// problem on the declaration; anything else is a missing import.
def bare_finding (j : Judge) (name : String) (rows : List DeclRow) : Finding :=
    match bare_hidden_row j rows {
        Option.some hidden =>
            let f : Finding :=
                { name := name, owner := hidden.owner, spelling := item_spelling hidden,
                  kind := FindingKind.fk_hidden, vis := hidden.vis } in
            f,
        Option.none =>
            let picked : DeclRow := pick_row j rows (first_row rows) in
            let f : Finding :=
                { name := name, owner := picked.owner, spelling := item_spelling picked,
                  kind := FindingKind.fk_unimported, vis := picked.vis } in
            f,
    }

/// Insertion by name, keeping the reports in the host's order (the gate
/// surfaces the first one, so the order decides which error a file
/// with several gaps sees).
#[partial]
def insert_finding (fs : List Finding) (f : Finding) : List Finding :=
    match fs {
        List.empty => List.cons f List.empty,
        List.cons hd rest =>
            if String.lt f.name hd.name
            then List.cons f fs
            else List.cons hd (insert_finding rest f),
    }

#[partial]
def sort_findings (fs : List Finding) (acc : List Finding) : List Finding :=
    match fs {
        List.empty => acc,
        List.cons f rest => sort_findings rest (insert_finding acc f),
    }

/// The `use`-completeness rule, as error messages. Empty means the
/// module is complete. `pre_decls` are the consumer's PRE-expansion
/// declarations (where the references are read from), `expanded_decls`
/// its stored, load-expanded list (whose declared names count as its
/// own), and `world` every loaded module's `(path, decls)`.
pub def use_completeness_errors (file_path : String) (consumer : ModulePath)
    (consumer_mote : Option String)
    (pre_decls : List Decl) (expanded_decls : List Decl)
    (world : List (Pair ModulePath (List Decl))) : List String :=
    match collect_opens pre_decls (struct_opens_empty) {
        // An unfiltered `open T` silences the whole file.
        Option.none => List.empty,
        Option.some opens => judge_all file_path consumer consumer_mote pre_decls expanded_decls world opens,
    }

// ─── `open` and visibility ──────────────────────────────────────────
//
// `open M {x}` puts `x` in bare scope, and the reference judges skip
// every opened name, so the `open` line is the only place that can judge
// it. The declaration is found through the index: first as the dotted
// member (`open IO {println}` -> `IO.println`, `open MetaParam {p}` ->
// `MetaParam.p`, both spellings the index carries), then as a plain
// name. An unfiltered `open T` (and `open T {*}`) still silences the
// whole gate -- it can put an unbounded set of names in scope, so any
// claim would be a guess -- exactly as it does for `use` completeness.

#[partial]
def rows_any_visible (j : Judge) (rows : List DeclRow) : Bool :=
    match rows {
        List.empty => false,
        List.cons row rest =>
            if row_visible j row then true else rows_any_visible j rest,
    }

#[partial]
def rows_first_hidden (j : Judge) (rows : List DeclRow) : Option DeclRow :=
    match rows {
        List.empty => Option.none,
        List.cons row rest =>
            if row_visible j row
            then rows_first_hidden j rest
            else Option.some row,
    }

/// The hidden row among a name's candidates, or none when at least one
/// candidate is visible (resolution may then use that one).
#[partial]
def open_row_hidden (j : Judge) (rows : List DeclRow) : Option DeclRow :=
    if rows_any_visible j rows
    then Option.none
    else rows_first_hidden j rows

#[partial]
def judge_open_names (j : Judge) (path : NamePath) (names : List Identifier)
    (rest : List Decl) (seen : HashMap String Bool) (acc : List Finding) : JudgeOut :=
    match names {
        List.empty => judge_opens j rest seen acc,
        List.cons n names_rest =>
            let name : String := show_identifier n in
            let dotted : String :=
                String.concat (show_name_path path) (String.concat "." name) in
            let hidden : Option DeclRow :=
                match str_map_lookup dotted j.index {
                    Option.some rows => open_row_hidden j rows,
                    Option.none =>
                        match str_map_lookup name j.index {
                            Option.some rows => open_row_hidden j rows,
                            Option.none => Option.none,
                        },
                } in
            match hidden {
                Option.none => judge_open_names j path names_rest rest seen acc,
                Option.some row =>
                    if set_member name seen
                    then judge_open_names j path names_rest rest seen acc
                    else
                        let finding : Finding :=
                            { name := name, owner := row.owner, spelling := name,
                              kind := FindingKind.fk_hidden, vis := row.vis } in
                        judge_open_names j path names_rest rest
                            (str_map_insert name true seen)
                            (List.append acc (List.cons finding List.empty)),
            },
    }

#[partial]
def judge_open_one (j : Judge) (path : NamePath) (filter : OpenFilter)
    (rest : List Decl) (seen : HashMap String Bool) (acc : List Finding) : JudgeOut :=
    match filter {
        open_all => judge_opens j rest seen acc,
        open_only names => judge_open_names j path names rest seen acc,
    }

#[partial]
def judge_opens (j : Judge) (decls : List Decl) (seen : HashMap String Bool) (acc : List Finding) : JudgeOut :=
    match decls {
        List.empty => { findings := acc, seen := seen },
        List.cons d rest =>
            match d {
                Decl.open_d path filter => judge_open_one j path filter rest seen acc,
                Decl.scoped_open_d path filter _inner => judge_open_one j path filter rest seen acc,
                _ => judge_opens j rest seen acc,
            },
    }

/// The body of `use_completeness_errors` once its opens are known: build
/// the selection/ambient/index/own tables, walk the references, judge
/// them, and render the findings sorted by name.
def judge_all (file_path : String) (consumer : ModulePath) (consumer_mote : Option String) (pre_decls : List Decl)
    (expanded_decls : List Decl) (world : List (Pair ModulePath (List Decl)))
    (opens : Opens) : List String :=
    let selection : HashMap String Selection := sel_map_of_decls pre_decls str_map_empty in
    let ambient : HashMap String Bool := ambient_seen world in
    let index : HashMap String (List DeclRow) := declaration_index world str_map_empty in
    let own : HashMap String Bool := own_keys_go (List.append pre_decls expanded_decls) str_map_empty in
    let regs : List DeriveHandlerReg := derive_registry world List.empty in
    let macro_names : List String := macro_call_names_go pre_decls regs List.empty in
    let refs_start : Refs := refs_add_bares macro_names refs_empty in
    let refs : Refs := collect_decls pre_decls refs_start in
    let j : Judge :=
        { consumer := consumer, consumer_mote := consumer_mote, opens := opens.names,
          selection := selection, ambient := ambient, index := index, own := own,
          file_path := file_path } in
    // `open`s first: an opened name is skipped by the two reference
    // judges (`set_member name j.opens`), so a hidden declaration reached
    // that way has to be caught at the `open` site itself.
    let open_out : JudgeOut := judge_opens j pre_decls str_map_empty List.empty in
    let qualified_out : JudgeOut := judge_qualified j refs.qualified open_out.seen open_out.findings in
    let bare_out : JudgeOut := judge_bare j refs.bare qualified_out.seen qualified_out.findings in
    let all : List Finding := List.append qualified_out.findings bare_out.findings in
    List.map (render_finding file_path) (sort_findings all List.empty)

def struct_opens_empty : Opens := { names := str_map_empty }

/// Fold a list of bare names into `refs`.
#[partial]
def refs_add_bares (names : List String) (refs : Refs) : Refs :=
    match names {
        List.empty => refs,
        List.cons n rest => refs_add_bares rest (refs_add_bare n refs),
    }

// ─── Tests ──────────────────────────────────────────────────────────
//
// Two-module (and larger) worlds parsed from text, the same probe
// style `lang/module.mo`'s `validate_use_names` tests use. The world
// entries are parsed WITHOUT expansion here too -- the probe sources
// contain no macro calls, so it changes nothing, and it is the same
// parse the gate itself reads the consumer from.

def probe_parse (src : String) : Option (List Decl) :=
    match decls_parser_located src {
        ParseResult.success _ ds => Option.some ds,
        ParseResult.fail _ => Option.none,
    }

#[partial]
def probe_world (world : List (Pair ModulePath String)) (acc : List (Pair ModulePath (List Decl))) : Option (List (Pair ModulePath (List Decl))) :=
    match world {
        List.empty => Option.some acc,
        List.cons entry rest =>
            match entry {
                Pair.pair mp src =>
                    match probe_parse src {
                        Option.some ds => probe_world rest (List.append acc (List.cons (Pair.pair mp ds) List.empty)),
                        Option.none => Option.none,
                    },
            },
    }

/// The errors for a consumer parsed from `src` against `world`, or a
/// one-message stand-in when a probe source failed to parse (so a
/// rejection test cannot pass on the parse failure instead of on the
/// rule).
def probe_errors (world : List (Pair ModulePath String)) (consumer : ModulePath) (src : String) : List String :=
    match probe_world world List.empty {
        Option.none => [ "the probe world did not parse" ],
        Option.some w =>
            match probe_parse src {
                Option.none => [ "the probe consumer did not parse" ],
                Option.some ds => use_completeness_errors "consumer.mo" consumer (module_mote_of consumer) ds ds w,
            },
    }

def widgets_path : ModulePath := ModulePath.mk [Identifier.id "widgets"]

/// The consumer the probes judge: a module of its own, never the
/// module its references reach into.
def consumer_path : ModulePath := ModulePath.mk [Identifier.id "consumer"]

def widgets_src : String := "pub def widget : I64 := 1\n"

/// The headline case: a bare name reached from another module with no
/// `use` naming it fails, and the report names both the name and the
/// module that declares it.
#[test]
def test_unimported_bare_name_fails : Bool :=
    match probe_errors [Pair.pair widgets_path widgets_src] consumer_path "def use_it : I64 := widget" {
        List.cons msg rest =>
            Bool.and (List.is_empty rest)
                (Bool.and (String.contains msg "`widget` is not imported")
                    (String.contains msg "declared in `widgets`")),
        List.empty => false,
    }

/// ...and importing it by name clears the report.
#[test]
def test_importing_the_name_clears_it : Bool :=
    List.is_empty
        (probe_errors [Pair.pair widgets_path widgets_src] consumer_path
            "use widgets {widget}\ndef use_it : I64 := widget")

// ─── Visibility at the gate ─────────────────────────────────────────
//
// The boundary is judged at the REFERENCE, not at the `use` line: an
// imported name can still be invisible, and the finding says so with the
// declaration's own remedy. Motes are the first segment of a module path;
// `consumer::child` and `consumer::widgets` are siblings in one mote.

def child_path : ModulePath := ModulePath.mk [Identifier.id "consumer", Identifier.id "child"]

def sibling_path : ModulePath := ModulePath.mk [Identifier.id "consumer", Identifier.id "widgets"]

/// Imported, but package-private and declared in another mote.
#[test]
def test_cross_mote_package_private_is_hidden : Bool :=
    match probe_errors [Pair.pair widgets_path "def widget : I64 := 1\n"] consumer_path
            "use widgets {widget}\ndef use_it : I64 := widget" {
        List.cons msg rest =>
            Bool.and (List.is_empty rest)
                (Bool.and (String.contains msg "`widget` is not visible here")
                    (Bool.and (String.contains msg "is not marked `pub`")
                        (String.contains msg "mote `widgets`"))),
        List.empty => false,
    }

/// The same declaration, reached from a SIBLING module of its own mote:
/// package-private means the mote, not the file.
#[test]
def test_same_mote_package_private_is_visible : Bool :=
    List.is_empty
        (probe_errors [Pair.pair sibling_path "def widget : I64 := 1\n"] child_path
            "use consumer::widgets {widget}\ndef use_it : I64 := widget")

/// `pub` is the remedy, and it works.
#[test]
def test_pub_declaration_crosses_motes : Bool :=
    List.is_empty
        (probe_errors [Pair.pair widgets_path widgets_src] consumer_path
            "use widgets {widget}\ndef use_it : I64 := widget")

/// `priv` is narrower than package-private: a sibling module cannot see
/// it, and the message says `priv` rather than "not pub".
#[test]
def test_priv_is_hidden_from_a_sibling_module : Bool :=
    match probe_errors [Pair.pair sibling_path "priv def widget : I64 := 1\n"] child_path
            "use consumer::widgets {widget}\ndef use_it : I64 := widget" {
        List.cons msg rest =>
            Bool.and (List.is_empty rest)
                (Bool.and (String.contains msg "`widget` is not visible here")
                    (String.contains msg "is declared `priv`")),
        List.empty => false,
    }

/// ...but its own module sees it, as ever.
#[test]
def test_priv_is_visible_in_its_own_module : Bool :=
    List.is_empty
        (probe_errors [] sibling_path
            "priv def widget : I64 := 1\ndef use_it : I64 := widget")

/// Constructors inherit the type's visibility -- here a package-private
/// `type` reached from another mote.
#[test]
def test_a_constructor_inherits_its_type_visibility : Bool :=
    match probe_errors [Pair.pair widgets_path "type Opt { some (a : I64), none }\n"] consumer_path
            "use widgets {Opt, some}\ndef f (o : Opt) : I64 := match o { some x => x, none => 0 }" {
        List.cons msg _rest => String.contains msg "is not visible here",
        List.empty => false,
    }

/// A module's own declarations are visible to it even though the ENTRY
/// module is named by its file stem (`test_constraints`) while the loaded
/// world's sibling modules are mote-qualified (`init::copy`). Both probes
/// put the consumer in the world, which is the shape the real gate sees.
#[test]
def test_a_modules_own_class_method_is_visible : Bool :=
    let src : String := "class C A { def m (a : A) : I64 := 1 }\ndef f : I64 := C.m 1" in
    List.is_empty (probe_errors [Pair.pair consumer_path src] consumer_path src)

#[test]
def test_a_modules_own_opened_constructor_is_visible : Bool :=
    let src : String :=
        "type Shape { circle (r : F64) }\nopen Shape {circle}\ndef f (s : Shape) : F64 := match s { circle r => r }" in
    List.is_empty (probe_errors [Pair.pair consumer_path src] consumer_path src)

/// A class's methods inherit its visibility, and method references are
/// indexed under their qualified spelling so the boundary can judge them.
#[test]
def test_a_class_method_inherits_the_class_visibility : Bool :=
    let cls_src : String := "class C A { def m (a : A) : I64 := 1 }\n" in
    match probe_errors [Pair.pair widgets_path cls_src] consumer_path
            "use widgets {C}\ndef f : I64 := C.m 1" {
        List.cons msg _rest => String.contains msg "`C.m` is not visible here",
        List.empty => false,
    }

#[test]
def test_a_pub_class_method_crosses_motes : Bool :=
    let cls_src : String := "pub class C A { def m (a : A) : I64 := 1 }\n" in
    List.is_empty
        (probe_errors [Pair.pair widgets_path cls_src] consumer_path
            "use widgets {C}\ndef f : I64 := C.m 1")

/// `open M {x}` is the only place an opened name can be judged: the
/// reference judges skip it by construction.
#[test]
def test_a_cross_mote_open_of_a_package_private_is_hidden : Bool :=
    match probe_errors [Pair.pair widgets_path "type MetaParam A { meta_param (a : A) }\n"] consumer_path
            "open MetaParam {meta_param}\ndef f : I64 := 0" {
        List.cons msg _rest => String.contains msg "`meta_param` is not visible here",
        List.empty => false,
    }

#[test]
def test_a_same_mote_open_of_a_package_private_is_allowed : Bool :=
    List.is_empty
        (probe_errors [Pair.pair sibling_path "type MetaParam A { meta_param (a : A) }\n"] child_path
            "open MetaParam {meta_param}\ndef f : I64 := 0")

/// The ambient prelude is a mote like any other: being visible without a
/// `use` line does not make a package-private name importable.
#[test]
def test_an_ambient_package_private_name_is_hidden : Bool :=
    match probe_errors [Pair.pair prelude_module_path "def widget : I64 := 1\n"] consumer_path
            "def use_it : I64 := widget" {
        List.cons msg _rest => String.contains msg "`widget` is not visible here",
        List.empty => false,
    }

#[test]
def test_a_pub_ambient_name_is_allowed : Bool :=
    List.is_empty
        (probe_errors [Pair.pair prelude_module_path "pub def widget : I64 := 1\n"] consumer_path
            "def use_it : I64 := widget")

/// A module-qualified reference is judged against the QUALIFIED axis:
/// `use widgets {}` holds every name of `widgets` reachable qualified
/// and none bare.
#[test]
def test_qualified_reference_with_empty_braces : Bool :=
    Bool.and
        (List.is_empty
            (probe_errors [Pair.pair widgets_path widgets_src] consumer_path
                "use widgets {}\ndef use_it : I64 := widgets::widget"))
        (Bool.not
            (List.is_empty
                (probe_errors [Pair.pair widgets_path widgets_src] consumer_path
                    "use widgets {}\ndef use_it : I64 := widget")))

/// Naming a namespace names its members: `{List}` drags in
/// `List.length` by the dotted-prefix rule, while the bare tail
/// `length` selects nothing -- the rule's own hint then says to write
/// the dotted spelling.
#[test]
def test_dotted_prefix_selects_members : Bool :=
    let dotted : String := "pub def List.length : I64 := 1\n" in
    Bool.and
        (List.is_empty
            (probe_errors [Pair.pair widgets_path dotted] consumer_path
                "use widgets {List}\ndef use_it : I64 := List.length"))
        (match probe_errors [Pair.pair widgets_path dotted] consumer_path
                "use widgets {length}\ndef use_it : I64 := List.length" {
            List.cons msg _rest =>
                Bool.and (String.contains msg "`List.length` is not imported")
                    (String.contains msg "use widgets {List.length}` names it"),
            List.empty => false,
        })

/// The consumer's own struct constructor is never an unimported name,
/// even when another loaded module declares the same spelling -- the
/// case that made the host add constructor tails to its own-name set.
#[test]
def test_own_struct_constructor_is_not_reported : Bool :=
    let foreign_mk : String := "def mk : I64 := 1\n" in
    List.is_empty
        (probe_errors [Pair.pair widgets_path foreign_mk] consumer_path
            "struct S { x : I64 }\ndef get_x (s : S) : I64 := match s { mk v => v }")

/// An inductive constructor is importable by its bare name.
#[test]
def test_constructor_import_binds_bare : Bool :=
    let sum_src : String := "pub type Opt { some (a : I64), none }\n" in
    Bool.and
        (List.is_empty
            (probe_errors [Pair.pair widgets_path sum_src] consumer_path
                "use widgets {Opt, some, none}\ndef f : Opt := some 1"))
        (Bool.not
            (List.is_empty
                (probe_errors [Pair.pair widgets_path sum_src] consumer_path
                    "def f : Opt := some 1")))

/// The ambient trio's `pub use` closure is seen whole: a name
/// re-exported by the `init` hub needs no `use` line in any consumer,
/// while an ordinary module's same-named declaration does not become
/// ambient by existing.
#[test]
def test_pub_use_reexports_are_ambient : Bool :=
    let init_path : ModulePath := ModulePath.mk [Identifier.id "init"] in
    let init_list_path : ModulePath := ModulePath.mk [Identifier.id "init", Identifier.id "list"] in
    let hub : String := "pub use init::list {*}\n" in
    let list_src : String := "pub def List.length : I64 := 1\n" in
    let world : List (Pair ModulePath String) :=
        [Pair.pair init_path hub, Pair.pair init_list_path list_src] in
    Bool.and
        (List.is_empty (probe_errors world consumer_path "def use_it : I64 := List.length"))
        (Bool.not
            (List.is_empty
                (probe_errors [Pair.pair widgets_path list_src] consumer_path
                    "def use_it : I64 := List.length")))

/// `open T {n}` makes `n` bare without a `use` line, and an unfiltered
/// `open T` silences the file.
#[test]
def test_open_names_and_unfiltered_open : Bool :=
    Bool.and
        (List.is_empty
            (probe_errors [Pair.pair widgets_path widgets_src] consumer_path
                "open widgets {widget}\ndef use_it : I64 := widget"))
        (List.is_empty
            (probe_errors [Pair.pair widgets_path widgets_src] consumer_path
                "open widgets\ndef use_it : I64 := widget"))

/// A declaration-position macro call reaches the macro's defining
/// module by name, exactly as the host's `collect_macro_call_names`
/// counts it.
#[test]
def test_macro_call_name_is_a_reference : Bool :=
    let macros_src : String := "#[derive_handler W]\ndefmacro dm T := decls { }\n" in
    Bool.and
        (Bool.not
            (List.is_empty
                (probe_errors [Pair.pair widgets_path macros_src] consumer_path "dm! Unit")))
        (List.is_empty
            (probe_errors [Pair.pair widgets_path macros_src] consumer_path
                "use widgets {dm}\ndm! Unit"))

/// An `#[derive W]` attribute is a reference to the macro its
/// registered handler names.
#[test]
def test_derive_attribute_reaches_the_handler : Bool :=
    let macros_src : String := "#[derive_handler W]\ndefmacro dw T := decls { }\n" in
    Bool.and
        (Bool.not
            (List.is_empty
                (probe_errors [Pair.pair widgets_path macros_src] consumer_path
                    "#[derive W]\ntype T2 { mk2 (u : Unit) }\n")))
        (List.is_empty
            (probe_errors [Pair.pair widgets_path macros_src] consumer_path
                "use widgets {dw}\n#[derive W]\ntype T2 { mk2 (u : Unit) }\n"))

/// A match-pattern constructor is collected by its bare tail (the
/// parser keeps only the last segment of a dotted pattern), but the
/// selection rule judges the declaration's OWN two-segment spelling:
/// `use widgets {Kind}` selects `Kind.denied` by the dotted-prefix
/// rule. This is the shape the `std::stream` kind tests use, and a
/// false positive here until the constructor rows carried the
/// inductive's name.
#[test]
def test_dotted_prefix_selects_pattern_constructors : Bool :=
    let kind_src : String := "pub type Kind { not_found, denied }\n" in
    Bool.and
        (List.is_empty
            (probe_errors [Pair.pair widgets_path kind_src] consumer_path
                "use widgets {Kind}\ndef f (k : Kind) : I64 := match k { Kind.denied => 1, _ => 0 }"))
        (match probe_errors [Pair.pair widgets_path kind_src] consumer_path
                "def f (k : Kind) : I64 := match k { Kind.denied => 1, _ => 0 }" {
            List.cons msg _rest => String.contains msg "`Kind` is not imported",
            List.empty => false,
        })

/// An `open T {n}` file owns the open's PATH name as well (the host's
/// `own` set is every decl's `to_ref`, and an `open`'s ref IS its path):
/// `open Param {mk}` covers a bare `Param` reference. The shape
/// `lang/src/codegen/test/compile_tests.mo` uses -- a false positive
/// there until the own-name walk counted `open`'s path.
#[test]
def test_open_path_is_own_name : Bool :=
    List.is_empty
        (probe_errors [Pair.pair widgets_path "def Param : I64 := 1\n"] consumer_path
            "open Param {mk}\ndef f : List Param := List.empty")

/// Several gaps report in name order, so the gate's first-error-wins
/// surfaces the alphabetically first.
#[test]
def test_findings_are_sorted_by_name : Bool :=
    let both : String := String.concat widgets_src "def aardvark : I64 := 2\n" in
    match probe_errors [Pair.pair widgets_path both] consumer_path "def u : I64 := aardvark + widget" {
        List.cons first rest =>
            match rest {
                List.cons second tail =>
                    Bool.and (List.is_empty tail)
                        (Bool.and (String.contains first "`aardvark` is not imported")
                            (String.contains second "`widget` is not imported")),
                List.empty => false,
            },
        List.empty => false,
    }
