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
/// (`cli.main::main`), so the literal `"main"` this used to assume
/// names nothing, and a wrapper supplying it would quietly return an
/// empty closure.
use lib::types {
  Decl, Def, Identifier, Inductive, Multiplicity, NamePath, Struct, StructField,
  Term, Visibility,
}
use lib::module {ModuleInfo}
use lib::codegen::symbols {def_symbol_name}
use lib::codegen::free_names {collect_referenced_names}
use lib::codegen::util {str_map_empty, str_map_insert, str_map_lookup}
use std::map {}

/// Extract def_d entries from a list of Decl. A def wrapped in
/// Decl.scoped_open_d is intentionally invisible to codegen for now
/// (deliberate gap — see Decl.scoped_open_d's doc comment).
///
/// Accumulator-passing, like every list builder in this module. These
/// run over the WHOLE program's flattened declarations -- 3,817 defs for
/// the compiler itself -- and the natural `List.cons x (recurse rest)`
/// shape holds one native frame per declaration. A `gdb` sample of a
/// self-compile sitting in `filter_reachable` caught exactly that:
/// thousands of stacked `extract_defs` frames with `alloc_constructor ->
/// GC_malloc_kind -> GC_collect_or_expand -> GC_mark_from` on top.
/// Boehm marks conservatively from the whole stack at every collection,
/// so depth here is paid again on each of the hundreds of collections
/// these allocations trigger.
#[partial]
def extract_defs (decl_list : List Decl) : List Def :=
    List.reverse (extract_defs_go decl_list List.empty)

#[partial]
def extract_defs_go (decl_list : List Decl) (acc : List Def) : List Def := match decl_list {
    List.empty => acc,
    List.cons d rest =>
        match d {
            Decl.def_d def_ => extract_defs_go rest (List.cons def_ acc),
            _ => extract_defs_go rest acc,
        }
}

/// Extract struct_d entries from a list of Decl.
///
/// Structs are deliberately NOT part of `extract_inductives` (a struct
/// stays `Decl.struct_d` all the way to codegen -- see `constructor_tag_at`'s
/// own note on why a struct `mk` gets no tag-map entry), but their
/// implicit `mk` constructor still needs its FIELD COUNT reachable: a
/// value-position reference to it (`Point.mk x y`, what a decl-gen macro's
/// `e_ctor` reifies to -- `std/derive.mo`'s `lens_setter`) has to be
/// recognized as a constructor application rather than an ordinary call to
/// some function named `Point.mk`, which is what compiled to
/// `llc: use of undefined value '@Point.mk'` in `examples/derive.mo`.
/// Collected separately so that reaching it costs the tag map nothing.
///
/// That is why `filter_reachable_decls` has to CARRY the struct decls
/// through: this runs on the codegen decl list, which reachability has
/// already reduced to defs plus inductives (see its own doc comment), so
/// a struct left behind there is a struct this function never sees --
/// and the reference above silently goes back to being an undefined
/// function call.
#[partial]
def extract_inductives (decl_list : List Decl) : List Inductive :=
    List.reverse (extract_inductives_go decl_list List.empty)

#[partial]
def extract_inductives_go (decl_list : List Decl) (acc : List Inductive) : List Inductive := match decl_list {
    List.empty => acc,
    List.cons d rest =>
        match d {
            Decl.inductive_d ind => extract_inductives_go rest (List.cons ind acc),
            _ => extract_inductives_go rest acc,
        }
}

#[partial]
def extract_structs (decl_list : List Decl) : List Struct :=
    List.reverse (extract_structs_go decl_list List.empty)

#[partial]
def extract_structs_go (decl_list : List Decl) (acc : List Struct) : List Struct := match decl_list {
    List.empty => acc,
    List.cons d rest =>
        match d {
            Decl.struct_d s => extract_structs_go rest (List.cons s acc),
            _ => extract_structs_go rest acc,
        }
}

/// Restricts `decl_list` to the transitive closure of Defs reachable from a
/// top-level `main`, plus every Inductive (kept unconditionally --
/// constructor-wrapper compilation is cheap, uniform, and, after the
/// qualified-naming fix in compile_db_inductive_constructors, collision
/// -free regardless of how many are compiled, so there's no correctness
/// reason to filter them and every reason to keep this simple) and every
/// Struct (which compile to nothing at all -- their only codegen
/// footprint is the ARITY claim their implicit `mk` contributes, see
/// `extract_structs`'s own doc comment, so keeping them is cheaper still).
/// `compile_loaded_modules_to_ir` previously fed `compile_db_module`
/// every loaded module's ENTIRE declaration set -- prelude, init,
/// string, number, io, id, ... -- regardless of whether the program
/// being compiled actually calls into any of it, so a codegen bug in
/// ANY of those 264 defs (even ones with zero callers from the actual
/// program) blocked compiling ANYTHING.
///
/// `root` is the entry point's own qualified symbol. There is no
/// sensible default any more: every def carries its module
/// (`cli.main::main`), so the literal `"main"` this used to root at
/// names nothing at all, and a wrapper supplying it would silently
/// return the empty closure. The caller knows which module is the
/// program's entry point (`get_loaded_main`) and has to say.
#[partial]
def filter_reachable_decls (root : String) (decl_list : List Decl) : List Decl :=
    let all_defs := extract_defs decl_list in
    let all_inds := extract_inductives decl_list in
    let all_structs := extract_structs decl_list in
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
    List.append (map_inductive_decl all_inds) (List.append (map_struct_decl all_structs) (map_def_decl reachable))

#[partial]
def build_def_name_map (defs : List Def) (acc : HashMap String Def) : HashMap String Def := match defs {
    List.empty => acc,
    List.cons d rest => build_def_name_map rest (str_map_insert (def_name_str d) d acc),
}

#[partial]
def map_def_decl (defs : List Def) : List Decl :=
    List.reverse (map_def_decl_go defs List.empty)

#[partial]
def map_def_decl_go (defs : List Def) (acc : List Decl) : List Decl := match defs {
    List.empty => acc,
    List.cons d rest => map_def_decl_go rest (List.cons (Decl.def_d d) acc),
}

#[partial]
def map_inductive_decl (inds : List Inductive) : List Decl :=
    List.reverse (map_inductive_decl_go inds List.empty)

#[partial]
def map_inductive_decl_go (inds : List Inductive) (acc : List Decl) : List Decl := match inds {
    List.empty => acc,
    List.cons i rest => map_inductive_decl_go rest (List.cons (Decl.inductive_d i) acc),
}

#[partial]
def map_struct_decl (structs : List Struct) : List Decl :=
    List.reverse (map_struct_decl_go structs List.empty)

#[partial]
def map_struct_decl_go (structs : List Struct) (acc : List Decl) : List Decl := match structs {
    List.empty => acc,
    List.cons s rest => map_struct_decl_go rest (List.cons (Decl.struct_d s) acc),
}

/// Reachability works in the same name space the emitted symbols do --
/// `collect_referenced_names` collects a reference's `symbol_identifier`
/// verbatim, so the def side has to spell its name the same way or the
/// walk from `main` finds nothing.
#[partial]
def def_name_str (d : Def) : String := match d {
    Def.mk {name, typ := _typ, term := _term, constraints := _constraints, attrs := _attrs, vis := _vis, ..} => def_symbol_name name,
}

#[partial]
def def_body_term (d : Def) : Term := match d {
    Def.mk {name := _name, typ := _typ, term := term_, constraints := _constraints, attrs := _attrs, vis := _vis, ..} => term_,
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
/// Shaped so the self-tail-call rewrite can actually fire: the whole
/// body reaches exactly ONE self-recursive call, in tail position.
///
/// The obvious spelling -- a recursive call in each arm of the `visited`
/// and `defs_map` lookups -- reads better and does not work. `tco.mo`
/// bails out (returns the blocks unchanged) if pruning a merge phi would
/// leave it with zero incoming pairs, which is its guard against a
/// function with no reachable base case. When BOTH arms of an inner
/// match are self-recursive, that inner merge trips the guard and the
/// whole function loses the rewrite, not just that merge. The result was
/// one native frame per worklist item: a `gdb` sample of a self-compile
/// at the default 8 MB stack showed 20,822 frames of this function and a
/// SIGSEGV in `filter_reachable`.
///
/// So each branch computes the NEXT state as a value and the call
/// happens once, after. Same three transitions as before: an
/// already-visited name advances the worklist and changes nothing else;
/// an unvisited name that names a Def pushes its referenced names and
/// keeps the Def; an unvisited name that matches no Def is marked
/// visited and skipped.
#[partial]
def reachable_defs_from (defs_map : HashMap String Def) (worklist : List String) (visited : HashMap String Bool) (acc : List Def) : List Def :=
    match worklist {
        List.empty => acc,
        List.cons name rest =>
            let seen := match str_map_lookup name visited {
                Option.some _ => true,
                Option.none => false,
            } in
            let found := if seen then Option.none else str_map_lookup name defs_map in
            let next_work := match found {
                Option.some d => List.append (collect_referenced_names (def_body_term d) List.empty) rest,
                Option.none => rest,
            } in
            let next_acc := match found {
                Option.some d => List.cons d acc,
                Option.none => acc,
            } in
            let next_visited := if seen then visited else str_map_insert name true visited in
            reachable_defs_from defs_map next_work next_visited next_acc,
    }

#[partial]
def collect_all_decls_from_modules (modules : List ModuleInfo) (acc : List Decl) : List Decl := match modules {
    List.empty => acc,
    List.cons mod_ rest =>
        let mod_decls := mod_.decl_list in
        collect_all_decls_from_modules rest (List.append mod_decls acc),
}

// ─── Tests ──────────────────────────────────────────────────────────

/// A one-field `Struct`, built by hand (`extract_structs` is what turns
/// real decls into these).
#[partial]
def unit_test_struct_decl (type_name : String) : Struct :=
    Struct.mk (Identifier.id type_name)
        (List.cons (StructField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) Option.none Multiplicity.many) List.empty)
        List.empty Visibility.package_private

/// A one-constructor `Inductive`, by hand -- the comparison case below.
#[partial]
def unit_test_inductive_decl (type_name : String) : Inductive :=
    Inductive.mk (NamePath.npath (List.cons (Identifier.id type_name) List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) List.empty List.empty Visibility.package_private

/// `filter_reachable_decls` must carry STRUCT decls through, exactly as
/// it carries inductives: the constructor-arity table codegen builds
/// comes from the list THIS function returns (`extract_structs`'s own
/// doc comment), so a struct dropped here is a struct whose implicit
/// `mk` codegen never learns is a constructor -- `examples/derive.mo`'s
/// `llc: use of undefined value '@Point.mk'`, which survived a first
/// attempt at the fix that taught `extract_structs` about structs but
/// left reachability still discarding them.
///
/// No Defs are needed to make the point: an unreachable root leaves the
/// def closure empty, so what comes back is exactly "inductives, structs,
/// and nothing else" -- asserted all three ways so a future filter that
/// keeps too much fails here too.
#[test]
def test_filter_reachable_decls_keeps_structs : Bool :=
    let decls : List Decl := List.cons (Decl.struct_d (unit_test_struct_decl "Point"))
        (List.cons (Decl.inductive_d (unit_test_inductive_decl "Slim")) List.empty) in
    let filtered := filter_reachable_decls "cli.main::main" decls in
    I64.beq (List.length (extract_structs filtered)) 1
        && I64.beq (List.length (extract_inductives filtered)) 1
        && I64.beq (List.length (extract_defs filtered)) 0
