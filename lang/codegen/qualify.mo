/// Stage 0c: give every source def its module-qualified name, and
/// re-point every reference at the module that owns it.
///
/// Runs PER MODULE, before `collect_all_decls_from_modules` flattens --
/// `ModuleInfo.path` is the only record of which module a decl came
/// from, and flattening discards it.
///
/// Why this exists: codegen used to mangle a def to its BARE name, so
/// the whole program shared one flat namespace and two places silently
/// kept one of any same-named pair. 19 top-level names are declared by
/// two or more non-test modules in this corpus, and one of them --
/// `inductive_bare_name`, `-> String` in one module and `-> Identifier`
/// in another -- put a raw `char*` into a `DebugName.named` slot and
/// crashed the self-compiled compiler. See AGENTS.md items 18/19.
use lang.types {
  Decl, Def, Identifier, ModulePath, StructField, TypeConstraint,
  sentinel, show_identifier, show_module_path,
}
use lang.module {ModuleInfo, mk}
use lang.scope {
  OpenAlias, alias_map_empty, alias_map_insert, alias_map_lookup,
  collect_open_aliases, modpath_eq, resolve_open_alias_decls,
}
use lang.codegen.free_names {free_names_of_term}
use lang.codegen.symbols {bare_modpath, symbol_identifier, unqualify_def_name}
use lang.codegen.util {
  join_semicolon_msgs, list_contains_str, str_map_empty, str_map_insert,
  str_map_lookup,
}
use std.map {}
use std.list {intercalate}

/// A decl's own declared def name, if it is a `Decl.def_d`. The name may
/// itself contain dots (`def String.beq` parses as a SINGLE-segment
/// `ModulePath` whose Identifier is the literal text `"String.beq"` --
/// see `dotted_def_name` in `lang/parser.mo`), so this deliberately does
/// not care how many dots are in it: what matters is that the name is
/// the whole of what the source declared, and qualification prepends the
/// module path to it wholesale.
#[partial]
def decl_def_name (d : Decl) : Option ModulePath := match d {
    Decl.def_d dd =>
        match dd {
            Def.mk name _typ _term _constraints _attrs _vis => Option.some name,
        },
    _ => Option.none,
}

/// `declared name -> every module path that declares it`. One pass over
/// every loaded module; `str_map_*`-backed for the same reason
/// `build_def_name_map` is (a linear scan per lookup is the measured
/// dominant cost at this corpus size).
#[partial]
def collect_def_owners (modules : List ModuleInfo) (acc : HashMap String (List ModulePath)) : HashMap String (List ModulePath) :=
    match modules {
        List.empty => acc,
        List.cons m rest =>
            collect_def_owners rest (collect_def_owners_decls (m.path) (m.decl_list) acc),
    }

#[partial]
def collect_def_owners_decls (path : ModulePath) (decls : List Decl) (acc : HashMap String (List ModulePath)) : HashMap String (List ModulePath) :=
    match decls {
        List.empty => acc,
        List.cons d rest =>
            collect_def_owners_decls path rest (add_def_owner (decl_def_name d) path acc),
    }

#[partial]
def add_def_owner (name : Option ModulePath) (path : ModulePath) (acc : HashMap String (List ModulePath)) : HashMap String (List ModulePath) :=
    match name {
        Option.none => acc,
        Option.some n =>
            let key := show_module_path n in
            let prev := match str_map_lookup key acc {
                Option.some ps => ps,
                Option.none => List.empty,
            } in
            // Deduplicated by module, not by declaration: a module that
            // declares one name twice is its own (pre-existing) problem,
            // but it must not read here as an AMBIGUOUS name.
            if modpath_list_contains prev path
            then acc
            else str_map_insert key (List.cons path prev) acc,
    }

#[partial]
def modpath_list_contains (ps : List ModulePath) (p : ModulePath) : Bool := match ps {
    List.empty => false,
    List.cons hd rest => if modpath_eq hd p then true else modpath_list_contains rest p,
}

/// The name `n`, declared in module `M`, is emitted under: `M::n`.
///
/// `::` and not `.`: a def name may itself contain dots (`def
/// String.beq`), and a module path is dotted too, so a dot separator
/// would not say where one ends and the other begins -- `init.string`
/// + `String.beq` and `init.string.String` + `beq` would both read as
/// `init.string.String.beq`. `::` cannot occur in either half, so the
/// encoding is injective by construction and the original source name
/// is recoverable with `unqualify_def_name` below (which the native
/// tables need, since they are keyed on what the source wrote).
///
/// The result stays a SINGLE-segment `ModulePath`, exactly the shape a
/// def name already had -- `show_module_path`/`module_path_to_str` are
/// the identity on it, so nothing downstream sees a new shape.
#[partial]
def qualified_def_name (modpath : ModulePath) (n : ModulePath) : ModulePath :=
    bare_modpath (qualified_def_name_str modpath n)

#[partial]
def qualified_def_name_str (modpath : ModulePath) (n : ModulePath) : String :=
    String.concat (show_module_path modpath) (String.concat "::" (show_module_path n))

/// The module paths a module imports, in any form (`use x {..}`,
/// `use x {}`, `open X {..}`, and the inner decl of a `scoped_open_d`).
/// Used only to disambiguate a name several modules declare; a name with
/// exactly one declarer never consults this.
#[partial]
def module_import_paths (decls : List Decl) : List ModulePath := match decls {
    List.empty => List.empty,
    List.cons d rest => List.append (import_paths_of_decl d) (module_import_paths rest),
}

#[partial]
def import_paths_of_decl (d : Decl) : List ModulePath := match d {
    Decl.use_d path _filter _public => List.cons path List.empty,
    Decl.open_d path _filter => List.cons path List.empty,
    Decl.scoped_open_d path _filter inner => List.cons path (import_paths_of_decl inner),
    _ => List.empty,
}

/// Owners of `name` that `M` explicitly named in a `use`/`open` ITEM
/// list -- the strongest disambiguation signal, because the source says
/// outright which module the name was taken from. `collect_open_aliases`
/// already reconstructs each item as `path ++ "." ++ bare`, which is
/// exactly the qualified name this pass mints, so the two agree by
/// construction. (That reconstruction is documented as usually WRONG in
/// `filter_valid_open_aliases`, because today's defs register under
/// plain undotted names -- qualifying them is what makes it right.)
#[partial]
def explicit_import_owners (own_aliases : List OpenAlias) (name : String) (owners : List ModulePath) : List ModulePath :=
    match owners {
        List.empty => List.empty,
        List.cons o rest =>
            let rest_hits := explicit_import_owners own_aliases name rest in
            // The alias's `qualified_name` is DOT-joined (`open_aliases_
            // from_names` builds `show_module_path (path_extend path n)`),
            // while an emitted symbol is `::`-joined. Compare in the
            // alias's own space -- comparing the two forms directly made
            // this whole rule dead code, and nothing noticed because the
            // import-set fallback below happened to answer correctly for
            // every ambiguous name then in the corpus.
            if alias_list_names own_aliases name (String.concat (show_module_path o) (String.concat "." name))
            then List.cons o rest_hits
            else rest_hits,
    }

#[partial]
def alias_list_names (aliases : List OpenAlias) (bare : String) (qualified : String) : Bool :=
    match aliases {
        List.empty => false,
        List.cons a rest =>
            match a {
                { bare_name := b, qualified_name := q } =>
                    if String.beq b bare && String.beq q qualified
                    then true
                    else alias_list_names rest bare qualified,
            },
    }

#[partial]
def modpath_list_intersect (a : List ModulePath) (b : List ModulePath) : List ModulePath :=
    match a {
        List.empty => List.empty,
        List.cons hd rest =>
            let rest_hits := modpath_list_intersect rest b in
            if modpath_list_contains b hd then List.cons hd rest_hits else rest_hits,
    }

/// Which module owns `name`, as seen from module `mpath`:
///
///   1. `mpath` declares it        -> `mpath`   (a local definition wins)
///   2. an explicit `use`/`open X {name}` names a declarer -> `X`
///   3. exactly one module declares it -> that module
///   4. otherwise                  -> error, listing every candidate
///
/// Rule 3 carries the corpus: a bare cross-module call to a uniquely
/// named def is the dominant style here, and routinely has no import at
/// all (`lang/module.mo` calls `std/path.mo`'s `raw_path_join` with no
/// `use std.path`; `lang/scope.mo` calls `show_module_path` without
/// importing it). Rules 1/2/4 exist only for the ~19 names two or more
/// modules declare.
#[partial]
def resolve_owner (mpath : ModulePath) (own_aliases : List OpenAlias) (imports : List ModulePath) (name : String) (owners : List ModulePath) : Result String ModulePath :=
    let explicit := explicit_import_owners own_aliases name owners in
    if modpath_list_contains owners mpath
    then
        // Declaring a name AND explicitly importing the same name from
        // another declarer is contradictory source, and today which one
        // wins is decided by registration order. `lang/module.mo` does
        // exactly this with `list_append` -- and AGENTS.md item 19
        // records that its own copy and `lang/scope.mo`'s are
        // deliberately NOT interchangeable (different generic binders,
        // both on `merge_scope_data`'s measured hot path). Silently
        // picking a side would move a hot path with no signal, so say so.
        match explicit {
            List.empty => Result.ok mpath,
            List.cons e _ =>
                Result.err (String.concat "module " (String.concat (show_module_path mpath)
                    (String.concat " both declares `" (String.concat name
                    (String.concat "` and imports it from " (String.concat (show_module_path e)
                    " -- drop one, they are not interchangeable")))))),
        }
    else match explicit {
        List.cons e erest =>
            match erest {
                List.empty => Result.ok e,
                List.cons _ _ => Result.err (ambiguous_owner_msg mpath name explicit),
            },
        List.empty =>
            match owners {
                List.cons o orest =>
                    match orest {
                        List.empty => Result.ok o,
                        List.cons _ _ =>
                            // Several declarers and no explicit item
                            // naming one: fall back to the modules this
                            // one imports at all, which is still a real
                            // narrowing.
                            let imported := modpath_list_intersect owners imports in
                            match imported {
                                List.cons i irest =>
                                    match irest {
                                        List.empty => Result.ok i,
                                        List.cons _ _ => Result.err (ambiguous_owner_msg mpath name imported),
                                    },
                                List.empty => Result.err (ambiguous_owner_msg mpath name owners),
                            },
                    },
                List.empty => Result.err (String.concat "no module declares `" (String.concat name "`")),
            },
    }

#[partial]
def ambiguous_owner_msg (mpath : ModulePath) (name : String) (candidates : List ModulePath) : String :=
    String.concat "`" (String.concat name
        (String.concat "` is referenced from " (String.concat (show_module_path mpath)
        (String.concat " but declared in " (String.concat (join_modpaths candidates)
        " -- add an explicit `use <module> {"
        )))))
        ++ name ++ "}` to say which"

#[partial]
def join_modpaths (ps : List ModulePath) : String :=
    List.intercalate ", " (List.map show_module_path ps)

/// Every declared def name across the whole program, deduplicated.
#[partial]
def all_declared_names (modules : List ModuleInfo) : List String :=
    all_declared_names_go modules str_map_empty

#[partial]
def all_declared_names_go (modules : List ModuleInfo) (seen : HashMap String Bool) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest =>
            match declared_names_in_decls (m.decl_list) seen {
                Pair.pair here seen2 => List.append here (all_declared_names_go rest seen2),
            },
    }

/// Accumulator-passing for the same reason `ambiguous_declared_names`
/// is: `List.cons key (recurse rest)` holds one native frame per
/// declaration, and the largest module here declares ~318 defs. Depth
/// like that is not just an overflow risk — Boehm scans the whole stack
/// conservatively at every collection, so it makes each allocation
/// underneath it slower too.
///
/// The accumulator reverses, so the result is reversed once at the end
/// to keep declaration order. That order is load-bearing: it is the
/// order `all_declared_names` hands to `build_global_rename_map` and
/// `ambiguous_declared_names`.
#[partial]
def declared_names_in_decls (decls : List Decl) (seen : HashMap String Bool) : Pair (List String) (HashMap String Bool) :=
    match declared_names_in_decls_go decls seen List.empty {
        Pair.pair rev seen2 => Pair.pair (List.reverse rev) seen2,
    }

#[partial]
def declared_names_in_decls_go (decls : List Decl) (seen : HashMap String Bool) (acc : List String) : Pair (List String) (HashMap String Bool) :=
    match decls {
        List.empty => Pair.pair acc seen,
        List.cons d rest =>
            match decl_def_name d {
                Option.none => declared_names_in_decls_go rest seen acc,
                Option.some n =>
                    let key := show_module_path n in
                    match str_map_lookup key seen {
                        Option.some _ => declared_names_in_decls_go rest seen acc,
                        Option.none =>
                            declared_names_in_decls_go rest (str_map_insert key true seen) (List.cons key acc),
                    },
            },
    }

/// `name -> qualified name` for every name exactly ONE module declares.
/// Computed once for the whole program rather than per module, because
/// the answer cannot differ between modules -- which is also what keeps
/// this pass linear: only the handful of genuinely ambiguous names ever
/// need per-module work.
#[partial]
def build_global_rename_map (names : List String) (owners_map : HashMap String (List ModulePath)) (acc : HashMap String String) : HashMap String String :=
    match names {
        List.empty => acc,
        List.cons n rest =>
            match owners_for n owners_map {
                List.cons o orest =>
                    match orest {
                        List.empty => build_global_rename_map rest owners_map (alias_map_insert n (qualified_def_name_str o (bare_modpath n)) acc),
                        List.cons _ _ => build_global_rename_map rest owners_map acc,
                    },
                List.empty => build_global_rename_map rest owners_map acc,
            },
    }

#[partial]
def owners_for (name : String) (owners_map : HashMap String (List ModulePath)) : List ModulePath :=
    match str_map_lookup name owners_map {
        Option.some ps => ps,
        Option.none => List.empty,
    }

/// The names two or more modules declare -- the only ones whose rewrite
/// target depends on which module is doing the referencing.
#[partial]
/// Accumulator-passing so the self-tail-call rewrite turns this into a
/// loop. It scans every declared name in the program -- 3,172 of them --
/// and the natural `List.cons n (recurse rest)` shape held one native
/// frame per name: a `gdb` backtrace from a stuck self-compile showed
/// 3,195 frames, nearly all of them this function. Depth that large is
/// not just a stack-overflow risk, it makes every allocation underneath
/// it slower, because Boehm scans the whole stack conservatively on each
/// collection and `GC_clear_stack` runs on the way out of each
/// `GC_malloc`.
///
/// The accumulator reverses, so the result is reversed once at the end
/// to keep the original declaration order.
def ambiguous_declared_names (names : List String) (owners_map : HashMap String (List ModulePath)) : List String :=
    List.reverse (ambiguous_declared_names_go names owners_map List.empty)

#[partial]
def ambiguous_declared_names_go (names : List String) (owners_map : HashMap String (List ModulePath)) (acc : List String) : List String :=
    match names {
        List.empty => acc,
        List.cons n rest =>
            match owners_for n owners_map {
                List.cons _ orest =>
                    match orest {
                        List.empty => ambiguous_declared_names_go rest owners_map acc,
                        List.cons _ _ => ambiguous_declared_names_go rest owners_map (List.cons n acc),
                    },
                List.empty => ambiguous_declared_names_go rest owners_map acc,
            },
    }

/// Rename every `Decl.def_d` in `decls` to its module-qualified name.
/// Definitions only -- references are rewritten separately, through the
/// existing alias rewriter.
#[partial]
def qualify_decl_names (mpath : ModulePath) (renames : HashMap String String) (decls : List Decl) : List Decl := match decls {
    List.empty => List.empty,
    List.cons d rest => List.cons (qualify_one_decl_name mpath renames d) (qualify_decl_names mpath renames rest),
}

#[partial]
def qualify_one_decl_name (mpath : ModulePath) (renames : HashMap String String) (d : Decl) : Decl := match d {
    Decl.def_d dd =>
        match dd {
            Def.mk name typ term_ constraints attrs vis =>
                Decl.def_d (Def.mk (qualified_def_name mpath name) typ term_ constraints attrs vis),
        },
    // An instance carries the module it was declared in via its own
    // name, so `promote_instance_defs` (Stage 3, on the already-flat
    // decl list, where module identity is gone) can still qualify the
    // methods and dictionary it mints -- see `mangle_instance_method_
    // name`/`instance_module_prefix` in `lang.scope`.
    Decl.instance_d ins =>
        match ins {
            Instance.mk insname cls constraints args vis implicit_params defs =>
                Decl.instance_d (Instance.mk (Identifier.id (qualified_def_name_str mpath (bare_modpath (show_identifier insname))))
                    cls constraints args vis implicit_params defs),
        },
    // An `infix (+) := I64.add` names its target by the SOURCE name, and
    // `resolve_infix_decls` (Stage 2) splices that name into every
    // operator call site -- AFTER this pass has run, so it would splice
    // a name nothing defines any more. Map the target here, through the
    // declaring module's own rename table, so the splice lands on the
    // real symbol.
    Decl.infix_d op path vis => Decl.infix_d op (rename_modpath renames path) vis,
    _ => d,
}

#[partial]
def rename_modpath (renames : HashMap String String) (p : ModulePath) : ModulePath :=
    match alias_map_lookup (show_module_path p) renames {
        Option.some q => bare_modpath q,
        Option.none => p,
    }

/// One module's rename table: the whole-program map for uniquely-owned
/// names, overlaid with this module's own answer for each ambiguous one.
/// `alias_map_insert` overwrites, so the overlay wins.
#[partial]
def module_rename_map (mpath : ModulePath) (own_aliases : List OpenAlias) (imports : List ModulePath) (owners_map : HashMap String (List ModulePath)) (ambig : List String) (acc : HashMap String String) : HashMap String String :=
    match ambig {
        List.empty => acc,
        List.cons n rest =>
            match resolve_owner mpath own_aliases imports n (owners_for n owners_map) {
                Result.ok o => module_rename_map mpath own_aliases imports owners_map rest (alias_map_insert n (qualified_def_name_str o (bare_modpath n)) acc),
                // Unresolvable here. Leave the name out of the table
                // rather than guessing; `unresolved_refs_in_module`
                // decides whether this module actually cares.
                Result.err _ => module_rename_map mpath own_aliases imports owners_map rest acc,
            },
    }

/// The ambiguous names this module leaves unresolved AND actually
/// references. Only computed when something was unresolvable, so the
/// common module pays nothing for it.
#[partial]
def unresolved_refs_in_module (mpath : ModulePath) (own_aliases : List OpenAlias) (imports : List ModulePath) (owners_map : HashMap String (List ModulePath)) (ambig : List String) (decls : List Decl) : List String :=
    let unresolved := unresolvable_names mpath own_aliases imports owners_map ambig in
    match unresolved {
        List.empty => List.empty,
        List.cons _ _ =>
            let referenced := decls_referenced_names decls in
            unresolved_messages mpath own_aliases imports owners_map unresolved referenced,
    }

#[partial]
def unresolvable_names (mpath : ModulePath) (own_aliases : List OpenAlias) (imports : List ModulePath) (owners_map : HashMap String (List ModulePath)) (ambig : List String) : List String :=
    match ambig {
        List.empty => List.empty,
        List.cons n rest =>
            let tail := unresolvable_names mpath own_aliases imports owners_map rest in
            match resolve_owner mpath own_aliases imports n (owners_for n owners_map) {
                Result.ok _ => tail,
                Result.err _ => List.cons n tail,
            },
    }

#[partial]
def unresolved_messages (mpath : ModulePath) (own_aliases : List OpenAlias) (imports : List ModulePath) (owners_map : HashMap String (List ModulePath)) (unresolved : List String) (referenced : HashMap String Bool) : List String :=
    match unresolved {
        List.empty => List.empty,
        List.cons n rest =>
            let tail := unresolved_messages mpath own_aliases imports owners_map rest referenced in
            match str_map_lookup n referenced {
                Option.none => tail,
                Option.some _ =>
                    match resolve_owner mpath own_aliases imports n (owners_for n owners_map) {
                        Result.ok _ => tail,
                        Result.err msg => List.cons msg tail,
                    },
            },
    }

/// Every name referenced from any `Def`/`Instance` body in `decls`.
#[partial]
def decls_referenced_names (decls : List Decl) : HashMap String Bool :=
    decls_referenced_names_go decls str_map_empty

#[partial]
def decls_referenced_names_go (decls : List Decl) (acc : HashMap String Bool) : HashMap String Bool :=
    match decls {
        List.empty => acc,
        List.cons d rest => decls_referenced_names_go rest (decl_referenced_names d acc),
    }

/// Binder-AWARE, unlike `collect_referenced_names` (which over-collects
/// on purpose, because reachability may safely over-approximate). Here
/// it may not: `lang/codegen/ir.mo` binds a match field named
/// `param_name`, and two unrelated modules happen to declare a def by
/// that name -- counting the binder as a reference reported an
/// ambiguity that does not exist and failed the whole compile. The
/// rewrite itself was always correct; only this report was over-eager.
#[partial]
def decl_referenced_names (d : Decl) (acc : HashMap String Bool) : HashMap String Bool := match d {
    Decl.def_d dd =>
        match dd {
            Def.mk _name _typ term_ _c _a _v => insert_all_names (identifier_names (free_names_of_term List.empty term_)) acc,
        },
    Decl.instance_d ins =>
        match ins {
            Instance.mk _n _cls _c _args _v _ip defs => instance_defs_referenced_names defs acc,
        },
    Decl.scoped_open_d _p _f inner => decl_referenced_names inner acc,
    _ => acc,
}

#[partial]
def instance_defs_referenced_names (defs : List Def) (acc : HashMap String Bool) : HashMap String Bool :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Def.mk _name _typ term_ _c _a _v =>
                    instance_defs_referenced_names rest (insert_all_names (identifier_names (free_names_of_term List.empty term_)) acc),
            },
    }

#[partial]
def identifier_names (ids : List Identifier) : List String := match ids {
    List.empty => List.empty,
    List.cons i rest => List.cons (symbol_identifier i) (identifier_names rest),
}

#[partial]
def insert_all_names (names : List String) (acc : HashMap String Bool) : HashMap String Bool :=
    match names {
        List.empty => acc,
        List.cons n rest => insert_all_names rest (str_map_insert n true acc),
    }

/// Stage 0c: qualify every source def with its module path, and
/// re-point every reference at the module that owns it.
///
/// Runs per module, before Stage 1 flattens -- `ModuleInfo.path` is the
/// only place the owning module is recorded, and it is gone the moment
/// the decls are concatenated.
#[partial]
def qualify_modules (all_modules : List ModuleInfo) : Result String (List ModuleInfo) :=
    let modules := dedup_modules_by_file all_modules in
    let owners_map := collect_def_owners modules str_map_empty in
    let names := all_declared_names modules in
    let global_map := build_global_rename_map names owners_map alias_map_empty in
    let ambig := ambiguous_declared_names names owners_map in
    let msgs := collect_qualify_errors modules owners_map ambig in
    match msgs {
        List.cons _ _ => Result.err (join_semicolon_msgs msgs ""),
        List.empty => Result.ok (qualify_modules_go modules owners_map global_map ambig),
    }

/// One `ModuleInfo` per source FILE.
///
/// The loader can register the same file under more than one module
/// path -- `init/string.mo` arrives as both `string` and `init.string`,
/// because `init/lib.mo`'s `pub use string {*}` names it relative to
/// its own directory. Under the old flat namespace that was invisible:
/// both copies declared the same bare `String.beq`, and
/// `build_def_name_map`/`dedup_funcs_by_name` silently collapsed them.
/// Qualification makes it visible and, left alone, wrong twice over --
/// every `String.*` would look ambiguous, and both copies would compile
/// under different symbols.
///
/// The longest path wins (`init.string` over `string`): it is the one
/// that actually describes where the file lives, and it is stable
/// regardless of which importer the loader happened to reach first.
/// A module with no file path (the synthesized test driver) is never
/// deduplicated -- it has no file to be the same as.
#[partial]
def dedup_modules_by_file (modules : List ModuleInfo) : List ModuleInfo :=
    let best := best_path_per_file modules str_map_empty in
    keep_canonical_modules modules best str_map_empty

#[partial]
def best_path_per_file (modules : List ModuleInfo) (acc : HashMap String String) : HashMap String String :=
    match modules {
        List.empty => acc,
        List.cons m rest =>
            match m {
                ModuleInfo.mk path file_path _decls =>
                    if String.beq file_path ""
                    then best_path_per_file rest acc
                    else
                        let candidate := show_module_path path in
                        let next := match str_map_lookup file_path acc {
                            Option.none => str_map_insert file_path candidate acc,
                            Option.some current =>
                                if I64.gt (String.length candidate) (String.length current)
                                then str_map_insert file_path candidate acc
                                else acc,
                        } in
                        best_path_per_file rest next,
            },
    }

#[partial]
def keep_canonical_modules (modules : List ModuleInfo) (best : HashMap String String) (seen : HashMap String Bool) : List ModuleInfo :=
    match modules {
        List.empty => List.empty,
        List.cons m rest =>
            match m {
                ModuleInfo.mk path file_path _decls =>
                    if String.beq file_path ""
                    then List.cons m (keep_canonical_modules rest best seen)
                    else
                        let is_best := match str_map_lookup file_path best {
                            Option.some b => String.beq b (show_module_path path),
                            Option.none => true,
                        } in
                        let already := match str_map_lookup file_path seen {
                            Option.some _ => true,
                            Option.none => false,
                        } in
                        if is_best && Bool.not already
                        then List.cons m (keep_canonical_modules rest best (str_map_insert file_path true seen))
                        else keep_canonical_modules rest best seen,
            },
    }

#[partial]
def collect_qualify_errors (modules : List ModuleInfo) (owners_map : HashMap String (List ModulePath)) (ambig : List String) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest =>
            let decls := m.decl_list in
            let here := unresolved_refs_in_module (m.path) (collect_open_aliases decls)
                (module_import_paths decls) owners_map ambig decls in
            List.append here (collect_qualify_errors rest owners_map ambig),
    }

#[partial]
def qualify_modules_go (modules : List ModuleInfo) (owners_map : HashMap String (List ModulePath)) (global_map : HashMap String String) (ambig : List String) : List ModuleInfo :=
    match modules {
        List.empty => List.empty,
        List.cons m rest =>
            List.cons (qualify_one_module m owners_map global_map ambig)
                (qualify_modules_go rest owners_map global_map ambig),
    }

#[partial]
def qualify_one_module (mi : ModuleInfo) (owners_map : HashMap String (List ModulePath)) (global_map : HashMap String String) (ambig : List String) : ModuleInfo :=
    match mi {
        ModuleInfo.mk mpath file_path decls =>
            let renames := module_rename_map mpath (collect_open_aliases decls)
                (module_import_paths decls) owners_map ambig global_map in
            // References first, then definitions: the rewriter matches a
            // reference by its BARE name, and renaming the definitions
            // first would not change that (it only touches `Def.name`),
            // but doing references first keeps the two steps independent
            // of each other's output.
            let rewritten := resolve_open_alias_decls renames decls in
            ModuleInfo.mk mpath file_path (qualify_decl_names mpath renames rewritten),
    }

#[partial]
def qtest_module (name : String) (decls : List Decl) : ModuleInfo :=
    ModuleInfo.mk (bare_modpath name) "" decls

/// `def <name> := <body_ref>` -- a def whose whole body is one bare
/// reference, which is all these tests need to watch a reference move.
#[partial]
def qtest_def (name : String) (body_ref : String) : Decl :=
    Decl.def_d (Def.mk (bare_modpath name) Term.hole
        (Term.var sentinel (DebugName.named (Identifier.id body_ref)))
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private)

#[partial]
def qtest_def_names (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (qtest_names_of_decls (m.decl_list)) (qtest_def_names rest),
    }

#[partial]
def qtest_names_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match decl_def_name d {
            Option.some n => List.cons (show_module_path n) (qtest_names_of_decls rest),
            Option.none => qtest_names_of_decls rest,
        },
}

#[partial]
def qtest_body_refs (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (qtest_refs_of_decls (m.decl_list)) (qtest_body_refs rest),
    }

#[partial]
def qtest_refs_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.def_d dd =>
                match dd {
                    Def.mk _n _t term_ _c _a _v =>
                        List.append (collect_referenced_names term_ List.empty) (qtest_refs_of_decls rest),
                },
            _ => qtest_refs_of_decls rest,
        },
}

/// The collision that crashed the self-compiled compiler: one bare name,
/// two modules. Both must survive, under distinct symbols.
#[test]
def test_qualify_same_name_in_two_modules_stays_distinct : Bool :=
    let a := qtest_module "a" (List.cons (qtest_def "shared" "x") List.empty) in
    let b := qtest_module "b" (List.cons (qtest_def "shared" "y") List.empty) in
    match qualify_modules (List.cons a (List.cons b List.empty)) {
        Result.err _ => false,
        Result.ok ms =>
            let names := qtest_def_names ms in
            if list_contains_str names "a::shared"
            then list_contains_str names "b::shared"
            else false,
    }

/// A local definition wins: `a`'s own `shared` is what `a` calls, even
/// though `b` declares the name too.
#[test]
def test_qualify_local_definition_wins : Bool :=
    let a := qtest_module "a" (List.cons (qtest_def "shared" "z")
        (List.cons (qtest_def "caller" "shared") List.empty)) in
    let b := qtest_module "b" (List.cons (qtest_def "shared" "y") List.empty) in
    match qualify_modules (List.cons a (List.cons b List.empty)) {
        Result.err _ => false,
        Result.ok ms => list_contains_str (qtest_body_refs ms) "a::shared",
    }

/// The dominant corpus shape: a bare cross-module call to a uniquely
/// named def, with no `use`/`open` naming it at all.
#[test]
def test_qualify_unique_owner_resolves_without_any_import : Bool :=
    let a := qtest_module "a" (List.cons (qtest_def "only_here" "w") List.empty) in
    let b := qtest_module "b" (List.cons (qtest_def "caller" "only_here") List.empty) in
    match qualify_modules (List.cons a (List.cons b List.empty)) {
        Result.err _ => false,
        Result.ok ms => list_contains_str (qtest_body_refs ms) "a::only_here",
    }

/// An explicit `use X {n}` picks a winner when two modules declare `n`.
///
/// This test exists because that rule shipped DEAD: the alias's own
/// `qualified_name` is dot-joined (`b.shared`) while an emitted symbol
/// is `::`-joined (`b::shared`), and the comparison used the second
/// form, so it never matched anything. Nothing caught it, because the
/// import-set fallback happened to answer correctly for every ambiguous
/// name then in the corpus.
#[test]
def test_qualify_explicit_import_picks_the_declarer : Bool :=
    let a := qtest_module "a" (List.cons (qtest_def "shared" "x") List.empty) in
    let b := qtest_module "b" (List.cons (qtest_def "shared" "y") List.empty) in
    // `c` imports BOTH declarers, so the import-set fallback cannot
    // narrow it -- only the explicit `{shared}` item on `b` can. An
    // earlier version of this test imported `b` alone and passed even
    // with the rule reverted, which is exactly how the bug shipped.
    let use_a := Decl.use_d (bare_modpath "a") (UseFilter.use_items List.empty) false in
    let use_b := Decl.use_d (bare_modpath "b")
        (UseFilter.use_items (List.cons (UseItem.use_name (Identifier.id "shared")) List.empty)) false in
    let c := qtest_module "c" (List.cons use_a (List.cons use_b (List.cons (qtest_def "caller" "shared") List.empty))) in
    match qualify_modules (List.cons a (List.cons b (List.cons c List.empty))) {
        Result.err _ => false,
        Result.ok ms => list_contains_str (qtest_body_refs ms) "b::shared",
    }

/// A struct field's DEFAULT is an executable term and must be qualified
/// like any body. The checker splices it into every struct literal that
/// omits the field, so leaving it bare while its target is renamed makes
/// those literals fail to elaborate -- and because codegen elaboration
/// is best-effort, that surfaces several stages later as an unrelated
/// gate firing. `lang/types.mo`'s `ScopeData.def_params` (defaulting to
/// `HashMap.map HashMap.empty_buckets`) is the real instance of this.
#[test]
def test_qualify_rewrites_struct_field_defaults : Bool :=
    let helper := qtest_def "make_empty" "z" in
    let fld := StructField.mk (Identifier.id "f") Term.hole
        (Option.some (Term.var sentinel (DebugName.named (Identifier.id "make_empty"))))
        Multiplicity.many in
    let st := Decl.struct_d (Struct.mk (Identifier.id "Holder") (List.cons fld List.empty) Visibility.package_private) in
    let a := qtest_module "a" (List.cons helper (List.cons st List.empty)) in
    match qualify_modules (List.cons a List.empty) {
        Result.err _ => false,
        Result.ok ms => list_contains_str (struct_default_refs ms) "a::make_empty",
    }

#[partial]
def struct_default_refs (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => List.append (struct_default_refs_of_decls (m.decl_list)) (struct_default_refs rest),
    }

#[partial]
def struct_default_refs_of_decls (decls : List Decl) : List String := match decls {
    List.empty => List.empty,
    List.cons d rest =>
        match d {
            Decl.struct_d st =>
                match st {
                    Struct.mk _n fields _v => List.append (struct_field_default_refs fields) (struct_default_refs_of_decls rest),
                },
            _ => struct_default_refs_of_decls rest,
        },
}

#[partial]
def struct_field_default_refs (fields : List StructField) : List String := match fields {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            StructField.mk _n _t default _m =>
                match default {
                    Option.some t => List.append (identifier_names (free_names_of_term List.empty t)) (struct_field_default_refs rest),
                    Option.none => struct_field_default_refs rest,
                },
        },
}

/// One FILE registered under two module paths is not an ambiguity --
/// `init/string.mo` arrives as both `string` and `init.string`, and
/// treating those as rival declarers made every `String.*` reference in
/// the corpus unresolvable.
#[test]
def test_qualify_same_file_under_two_paths_is_not_ambiguous : Bool :=
    let decls := List.cons (qtest_def "shared" "x") List.empty in
    let short_ := ModuleInfo.mk (bare_modpath "string") "init/string.mo" decls in
    let long_ := ModuleInfo.mk (bare_modpath "init.string") "init/string.mo" decls in
    let caller := qtest_module "user" (List.cons (qtest_def "caller" "shared") List.empty) in
    match qualify_modules (List.cons short_ (List.cons long_ (List.cons caller List.empty))) {
        Result.err _ => false,
        // The longer path wins, and the duplicate module is dropped
        // rather than compiled twice under two symbols.
        Result.ok ms => list_contains_str (qtest_body_refs ms) "init.string::shared",
    }

/// Two declarers and no import saying which: refusing to guess is the
/// whole point -- silently picking one is what the old flat namespace
/// did, and what crashed the compiler.
#[test]
def test_qualify_ambiguous_reference_is_an_error : Bool :=
    let a := qtest_module "a" (List.cons (qtest_def "shared" "x") List.empty) in
    let b := qtest_module "b" (List.cons (qtest_def "shared" "y") List.empty) in
    let c := qtest_module "c" (List.cons (qtest_def "caller" "shared") List.empty) in
    match qualify_modules (List.cons a (List.cons b (List.cons c List.empty))) {
        Result.err _ => true,
        Result.ok _ => false,
    }

/// `String.a` and `String_a` must not become one symbol. They did under
/// the old `replace_dots_with_underscores` mangling, which is why the
/// symbol is now the source name verbatim.
#[test]
def test_qualify_dotted_and_underscored_names_stay_distinct : Bool :=
    let a := qtest_module "m" (List.cons (qtest_def "String.a" "x")
        (List.cons (qtest_def "String_a" "y") List.empty)) in
    match qualify_modules (List.cons a List.empty) {
        Result.err _ => false,
        Result.ok ms =>
            let names := qtest_def_names ms in
            if list_contains_str names "m::String.a"
            then list_contains_str names "m::String_a"
            else false,
    }

/// `::` separates the module from the name, so the source name is
/// recoverable exactly -- which is what the native tables, keyed on what
/// the source wrote, depend on.
#[test]
def test_unqualify_recovers_the_source_name : Bool :=
    if String.beq (unqualify_def_name "init.string::String.beq") "String.beq"
    then if String.beq (unqualify_def_name "plain_name") "plain_name"
        then String.beq (unqualify_def_name "lang.main::main") "main"
        else false
    else false
