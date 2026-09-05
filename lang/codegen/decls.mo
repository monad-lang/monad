/// Decl-list manipulation and reachability.
///
/// The small vocabulary the backend uses to get from "every module's
/// declarations, flattened" to "the declarations actually worth
/// compiling": pull the `Def`s and `Inductive`s out of a decl list, and
/// walk the call graph from an entry point to discard everything the
/// program cannot reach.
///
/// `filter_reachable_decls` takes its root symbol EXPLICITLY. There is
/// no sensible default: every def carries its module now
/// (`lang.main::main`), so the literal `"main"` this used to assume
/// names nothing, and a wrapper supplying it would quietly return an
/// empty closure.
use lang.types {Decl, Def, Inductive, Term}
use lang.module {ModuleInfo}
use lang.codegen.symbols {def_symbol_name}
use lang.codegen.free_names {collect_referenced_names}
use lang.codegen.util {str_map_empty, str_map_insert, str_map_lookup}
use std.map {}

/// Extract def_d entries from a list of Decl. A def wrapped in
/// Decl.scoped_open_d is intentionally invisible to codegen for now
/// (deliberate gap — see Decl.scoped_open_d's doc comment).
#[partial]
def extract_defs (decl_list : List Decl) : List Def := match decl_list {
    List.empty => List.empty,
    List.cons d rest =>
        let rest_defs := extract_defs rest in
        match d {
            Decl.def_d def_ => List.cons def_ rest_defs,
            _ => rest_defs,
        }
}

/// Extract inductive_d entries from a list of Decl.
#[partial]
def extract_inductives (decl_list : List Decl) : List Inductive := match decl_list {
    List.empty => List.empty,
    List.cons d rest =>
        let rest_inds := extract_inductives rest in
        match d {
            Decl.inductive_d ind => List.cons ind rest_inds,
            _ => rest_inds,
        }
}

/// Restricts `decl_list` to the transitive closure of Defs reachable from a
/// top-level `main`, plus every Inductive (kept unconditionally --
/// constructor-wrapper compilation is cheap, uniform, and, after the
/// qualified-naming fix in compile_db_inductive_constructors, collision
/// -free regardless of how many are compiled, so there's no correctness
/// reason to filter them and every reason to keep this simple).
/// `compile_loaded_modules_to_ir` previously fed `compile_db_module`
/// every loaded module's ENTIRE declaration set -- prelude, init,
/// string, number, io, id, ... -- regardless of whether the program
/// being compiled actually calls into any of it, so a codegen bug in
/// ANY of those 264 defs (even ones with zero callers from the actual
/// program) blocked compiling ANYTHING.
///
/// `root` is the entry point's own qualified symbol. There is no
/// sensible default any more: every def carries its module
/// (`lang.main::main`), so the literal `"main"` this used to root at
/// names nothing at all, and a wrapper supplying it would silently
/// return the empty closure. The caller knows which module is the
/// program's entry point (`get_loaded_main`) and has to say.
#[partial]
def filter_reachable_decls (root : String) (decl_list : List Decl) : List Decl :=
    let all_defs := extract_defs decl_list in
    let all_inds := extract_inductives decl_list in
    // O(total) once, instead of `reachable_defs_from` re-scanning
    // `all_defs` per worklist item (O(reachable x total) -- confirmed the
    // dominant cost of a full self-compile via `--verbose` stage timing,
    // ~453s of ~944s). See `str_map_*`'s own doc comment for why this
    // bypasses `Map`'s typeclass dispatch (`BTreeMap.insert_loop`/
    // `lookup_loop` directly with `String.lt`/`String.gt`) instead of
    // calling `Map.insert`/`Map.lookup` -- same latent-bug workaround
    // `lang/scope.mo`'s `modpath_map_*` already uses.
    let defs_map := build_def_name_map all_defs str_map_empty in
    let reachable := reachable_defs_from defs_map (List.cons root List.empty) str_map_empty List.empty in
    List.append (map_inductive_decl all_inds) (map_def_decl reachable)

#[partial]
def build_def_name_map (defs : List Def) (acc : HashMap String Def) : HashMap String Def := match defs {
    List.empty => acc,
    List.cons d rest => build_def_name_map rest (str_map_insert (def_name_str d) d acc),
}

#[partial]
def map_def_decl (defs : List Def) : List Decl := match defs {
    List.empty => List.empty,
    List.cons d rest => List.cons (Decl.def_d d) (map_def_decl rest),
}

#[partial]
def map_inductive_decl (inds : List Inductive) : List Decl := match inds {
    List.empty => List.empty,
    List.cons i rest => List.cons (Decl.inductive_d i) (map_inductive_decl rest),
}

/// Reachability works in the same name space the emitted symbols do --
/// `collect_referenced_names` collects a reference's `symbol_identifier`
/// verbatim, so the def side has to spell its name the same way or the
/// walk from `main` finds nothing.
#[partial]
def def_name_str (d : Def) : String := match d {
    Def.mk name _typ _term _constraints _attrs _vis => def_symbol_name name,
}

#[partial]
def def_body_term (d : Def) : Term := match d {
    Def.mk _name _typ term_ _constraints _attrs _vis => term_,
}

/// Worklist-based reachability closure: BFS/DFS over Def names starting
/// from `worklist`, following every name `collect_referenced_names`
/// finds in each reached Def's body, until no new names are discovered.
/// A name that doesn't match any known Def (a native op, a constructor,
/// a bound-but-not-top-level local) is simply skipped, not an error --
/// this is a conservative over-approximation by design (collecting
/// every `Term.var`/`Con`/`MatchCase` name in a body, not just genuinely
/// free top-level references, so it may keep a few unreachable-in-
/// practice defs, but never drops one that's actually needed).
///
/// `defs_map`/`visited` are `str_map_*`-backed `HashMap String _`
/// lookups (O(log total) each) rather than the `List`-linear-scan this
/// used to do (`find_def_by_name` + `list_contains_str` over `visited`,
/// O(reachable x total) + O(reachable^2) respectively) -- confirmed via
/// `--verbose` stage timing as the single largest cost of a full
/// self-compile (~453s of ~944s, bigger than `elaborate_class`).
#[partial]
def reachable_defs_from (defs_map : HashMap String Def) (worklist : List String) (visited : HashMap String Bool) (acc : List Def) : List Def :=
    match worklist {
        List.empty => acc,
        List.cons name rest =>
            match str_map_lookup name visited {
                Option.some _ => reachable_defs_from defs_map rest visited acc,
                Option.none =>
                    match str_map_lookup name defs_map {
                        Option.some d =>
                            let referenced := collect_referenced_names (def_body_term d) List.empty in
                            reachable_defs_from defs_map (List.append referenced rest) (str_map_insert name true visited) (List.cons d acc),
                        Option.none =>
                            reachable_defs_from defs_map rest (str_map_insert name true visited) acc,
                    },
            },
    }

#[partial]
def collect_all_decls_from_modules (modules : List ModuleInfo) (acc : List Decl) : List Decl := match modules {
    List.empty => acc,
    List.cons mod_ rest => 
        let mod_decls := mod_.decl_list in
        collect_all_decls_from_modules rest (List.append mod_decls acc),
}
