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
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use std::list {List.filter_map, List.length}
use lang::types {
  Attribute, Decl, DebugName, Def, Identifier, Inductive, Multiplicity, NamePath, Struct,
  StructField, Term, Visibility, concrete, has_attr, id_eq, sentinel,
}
use lang::module {ModuleInfo}
use lib::symbols {def_symbol_name}
use lang::name_text {unqualify_def_name}
use lib::free_names {collect_referenced_names}
use lib::util {}
use std::map {HashMap}

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
def def_of_decl (d : Decl) : Option Def := match d {
    Decl.def_d def_ => Option.some def_,
    _ => Option.none,
}

#[partial]
def extract_defs (decl_list : List Decl) : List Def :=
    List.filter_map def_of_decl decl_list

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
def inductive_of_decl (d : Decl) : Option Inductive := match d {
    Decl.inductive_d ind => Option.some ind,
    _ => Option.none,
}

#[partial]
def extract_inductives (decl_list : List Decl) : List Inductive :=
    List.filter_map inductive_of_decl decl_list

#[partial]
def struct_of_decl (d : Decl) : Option Struct := match d {
    Decl.struct_d s => Option.some s,
    _ => Option.none,
}

#[partial]
def extract_structs (decl_list : List Decl) : List Struct :=
    List.filter_map struct_of_decl decl_list

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
/// `roots` must be spelled the way THIS list spells the entry points.
/// Codegen runs after `qualify_modules`, where every def carries its
/// module (`cli.main::main`), so the literal `"main"` names nothing there
/// and a wrapper defaulting to it would silently return the empty def
/// closure; those callers take the qualified symbol from `get_loaded_main`.
/// The PRE-qualification consumers -- `monad eval` and the test driver's
/// unqualified fallback -- legitimately root at the bare `"main"`, because
/// that is how defs are still spelled when they run (pinned by
/// `test_filter_reachable_decls_roots_at_a_bare_name` and
/// `slow_tests/src/codegen_eval_gate_tests.mo`).
///
/// `roots` is a LIST because a wasm program can also be entered through
/// `#[export "c"]` defs, which `main` never references (see
/// `export_roots`). Everything else is unchanged.
#[partial]
pub def filter_reachable_decls (roots : List String) (decl_list : List Decl) : List Decl :=
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
    let reachable := reachable_defs_from defs_map roots str_map_empty List.empty in
    List.append (map_inductive_decl all_inds) (List.append (map_struct_decl all_structs) (map_def_decl reachable))

#[partial]
def build_def_name_map (defs : List Def) (acc : HashMap String Def) : HashMap String Def := match defs {
    List.empty => acc,
    List.cons d rest => build_def_name_map rest (str_map_insert (def_name_str d) d acc),
}

#[partial]
def map_def_decl (defs : List Def) : List Decl :=
    List.map (fn d => Decl.def_d d) defs

#[partial]
def map_inductive_decl (inds : List Inductive) : List Decl :=
    List.map (fn i => Decl.inductive_d i) inds

#[partial]
def map_struct_decl (structs : List Struct) : List Decl :=
    List.map (fn s => Decl.struct_d s) structs

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

/// The qualified symbol of every `#[export "c"]` def, in decl order.
/// These are extra reachability roots: `main` never references an export,
/// so without them the def is filtered out before codegen and the export
/// does not exist.
#[partial]
def export_root_of_decl (d : Decl) : Option String := match d {
    Decl.def_d def_ =>
        if has_attr (Identifier.id "export") (def_attrs def_)
        then Option.some (def_name_str def_)
        else Option.none,
    _ => Option.none,
}

#[partial]
def export_roots (decl_list : List Decl) : List String :=
    List.filter_map export_root_of_decl decl_list

/// The JS-visible name of every `#[export "c"]` def: the SOURCE name
/// (`oak_mount`), not the qualified symbol every def is emitted under.
/// `wasm-ld --export=` can only export a symbol under its own name, which
/// is why `add_export_shims` (emit.mo) emits a thunk per export.
#[partial]
def export_name_of_decl (d : Decl) : Option String := match d {
    Decl.def_d def_ =>
        if has_attr (Identifier.id "export") (def_attrs def_)
        then Option.some (unqualify_def_name (def_name_str def_))
        else Option.none,
    _ => Option.none,
}

#[partial]
pub def export_names (decl_list : List Decl) : List String :=
    List.filter_map export_name_of_decl decl_list

/// `(JS name, qualified symbol)` for every `#[export "c"]` def, in decl
/// order. `add_export_shims` needs both halves to emit the thunk.
#[partial]
def export_pair_of_decl (d : Decl) : Option (Pair String String) := match d {
    Decl.def_d def_ =>
        if has_attr (Identifier.id "export") (def_attrs def_)
        then
            let qualified := def_name_str def_ in
            let plain := unqualify_def_name qualified in
            Option.some (Pair.pair plain qualified)
        else Option.none,
    _ => Option.none,
}

#[partial]
def export_pairs (decl_list : List Decl) : List (Pair String String) :=
    List.filter_map export_pair_of_decl decl_list

#[partial]
def def_attrs (d : Def) : List Attribute := match d {
    Def.mk {name := _name, typ := _typ, term := _term, constraints := _constraints, attrs, vis := _vis, ..} => attrs,
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
pub def collect_all_decls_from_modules (modules : List ModuleInfo) (acc : List Decl) : List Decl := match modules {
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
        [StructField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 1)) Option.none Multiplicity.many]
        List.empty Visibility.package_private

/// A one-constructor `Inductive`, by hand -- the comparison case below.
#[partial]
def unit_test_inductive_decl (type_name : String) : Inductive :=
    Inductive.mk (NamePath.mk (List.cons (Identifier.id type_name) List.empty))
        List.empty (Term.sort (SortLevel.concrete 1)) List.empty List.empty Visibility.package_private
