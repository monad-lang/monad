use lib::types {
  Class, ClassDef, Con, Decl, Def, DebugName, FieldPattern, FieldPatternEntry,
  Identifier, InductConstructor, Inductive,
  Infix, Instance, InstanceKey, Literal, LocalScope, LocalVar, MatchCase, Module, ModuleRegistry,
  ModulePath, NamePath, NameRef, Native, Operator, Param, QualifiedName, Scope, ScopeClassDef,
  ScopeData, ScopeDef, ScopeError, ScopeInstance, Similar, Struct, StructField, StructLitField,
  Term, class_d, class_not_found, def_d, hole, id, inductive_d, inductive_not_found, infix_d,
  instance_d, instance_not_found, mk, mp, name, name_not_found, name_path_similar, nid, nnp, nop,
  npath, nqn, open_d, scoped_open_d, show_name_path, struct_d, type_, use_d,
}
use lib::typecheck::traverse {con_map_children, native_map_children, term_map_children}
// `ScopeData.def_refs` is a `std.map` `HashMap ModulePath ScopeDef` — see
// `bench/scope_lookup.mo`. Empty import: naming any of `std.map`'s
// `Map`-class-instance exports explicitly hits a pre-existing latent
// instance/dictionary-resolution bug (same workaround `bench/scope_lookup.mo`
// and `std/map_tests.mo` already use) — everything remains available
// regardless via the same always-on mechanism that lets any top-level
// type/def resolve without being explicitly `use`d.
use std::map {}
use std::list {filter, filter_map}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}

// --- NamePath-keyed HashMap ops, bypassing `Map`'s typeclass dispatch ---
//
// `Map.insert`/`Map.lookup` (the `[Hashable K, BOrd K] Map HashMap`
// instance, `std/map.mo`) resolve `Hashable.hash key`/`BOrd.lt`/`BOrd.gt`
// as abstract class-method references INSIDE `HashMap`'s own generic
// `[K, V]`-parameterized body. AGENTS.md's own documented evaluator
// limitation ("`resolve_class_method_instance` picks the FIRST
// REGISTERED instance", not a type-directed lookup) means these can
// silently resolve to the WRONG instance's implementation whenever
// they're invoked from deep within an already-polymorphic call chain
// where `K` is still abstract at the call site -- exactly the shape
// `lang.module`'s dynamic dependency-loading path has (AGENTS.md item 3
// already documents this exact class of bug for `BTreeMap`/self-hosted-
// compiler code paths, with the same prescribed fix: bypass the class
// methods, call the concrete map's own bucket operations directly with
// PLAIN function values).
//
// Confirmed as a real, live bug for `ScopeData.def_refs`/`inductives`
// specifically (not just a theoretical risk this comment is guarding
// against): a minimal 2-file repro -- a dependency module defining a
// couple of plain dotted defs, a caller `use`-ing it with an empty
// filter and referencing them by qualified name -- fails with `unknown
// variable` when checked through `cli/src/main.mo`'s own `check` command
// (exercising the real dynamic dependency-walk), even though the exact
// same insert-then-lookup round-trip works fine in a shallow, directly-
// run `#[test]`. `scope_data_find_def`'s own PRIOR doc comment claimed
// "`Map.lookup`/`Map.insert` resolve correctly here... monomorphic over
// the concrete `ModulePath`/`ScopeDef` types" -- that reasoning doesn't
// actually hold (the fragility lives inside `HashMap`'s own generic
// body, not the call site's own polymorphism), and is superseded by this
// fix.
//
// `modpath_lt`/`modpath_gt`/`modpath_hash` delegate to the SAME
// dotted-string-based logic `BOrd ModulePath`/`Hashable ModulePath`
// (`lang/types.mo`) already use, just calling the underlying native
// `String.lt`/`String.gt`/`String.hash` directly instead of through
// `BOrd.lt`/`BOrd.gt`/`Hashable.hash`'s own abstract dispatch.
def modpath_lt (a : ModulePath) (b : ModulePath) : Bool :=
    String.lt (show_module_path a) (show_module_path b)

def modpath_gt (a : ModulePath) (b : ModulePath) : Bool :=
    String.gt (show_module_path a) (show_module_path b)

def modpath_hash (mp : ModulePath) : U64 :=
    String.hash (show_module_path mp)

// The stored key is the RENDERED path (`Foo.bar`), not the `ModulePath`
// itself, while the caller-facing argument stays a `ModulePath`. That
// one change is the whole point, and it is worth being explicit about
// why.
//
// A `ModulePath` has no cheap hash or equality: `modpath_hash` is
// `String.hash (show_module_path mp)` and `modpath_str_eq` is
// `String.beq` of two `show_module_path`s, and `show_module_path`
// (`lang/types.mo`) is `List.intercalate "." (List.map show_identifier
// ids)` -- an interpreted `List.map` plus a `String.concat` chain, built
// fresh every time. `bucket_insert_eq`/`bucket_lookup_eq` call the
// equality once PER CHAIN STEP, so with ~4,200 def names over 256
// buckets (~16 deep) a single insert rendered both sides ~16 times:
// roughly 32 full path renders per map operation, 31 of them rebuilding
// a string the table already had.
//
// AGENTS.md item 26 already halved this once -- `!lt && !gt` (four
// renders per step) to a single `eq` (two) -- for a measured -41.5% on
// `elaborate_class`. It did not remove the renders, because as long as
// the STORED key is a `ModulePath` every comparison has to re-derive it.
// Rendering once at the boundary and storing the result removes the
// remainder, and lets these maps reuse `bucket_insert_str`/
// `bucket_lookup_str` (plain native `String.beq`, no comparator value
// passed at all) exactly as `alias_map_*` below already does.
def npath_map_empty {V : Type} : HashMap String V :=
    HashMap.map HashMap.empty_buckets

def npath_map_insert {V : Type} (key : NamePath) (val : V) (m : HashMap String V) : HashMap String V :=
    match m {
        HashMap.map buckets =>
            let rendered : String := show_name_path key in
            let idx := HashMap.bucket_of (String.hash rendered) in
            let bucket := HashMap.get_bucket buckets idx in
            let new_bucket := HashMap.bucket_insert_str rendered val bucket in
            HashMap.map (HashMap.set_bucket buckets idx new_bucket)
    }

def npath_map_lookup {V : Type} (key : NamePath) (m : HashMap String V) : Option V :=
    match m {
        HashMap.map buckets =>
            let rendered : String := show_name_path key in
            let idx := HashMap.bucket_of (String.hash rendered) in
            let bucket := HashMap.get_bucket buckets idx in
            HashMap.bucket_lookup_str rendered bucket
    }

/// String-keyed map for the bare-name -> qualified-name rewrite tables
/// `resolve_open_alias_decls` drives. Mirrors `modpath_map_*` just
/// above (and `lang.codegen.emit`'s `str_map_*`) in bypassing `Map`'s
/// typeclass dispatch for direct `HashMap` bucket calls.
///
/// Deliberately NOT called `str_map_*`: `lang.codegen.emit` already
/// exports helpers by that name, and until every def carries its module
/// path those two would have been one LLVM symbol with one surviving
/// body -- the exact failure this whole change exists to remove. Named
/// apart so the gate never has to catch it.
def alias_map_empty : HashMap String String :=
    HashMap.map HashMap.empty_buckets

def alias_map_insert (key : String) (val : String) (m : HashMap String String) : HashMap String String :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            let bucket := HashMap.get_bucket buckets idx in
            let new_bucket := HashMap.bucket_insert_str key val bucket in
            HashMap.map (HashMap.set_bucket buckets idx new_bucket)
    }

def alias_map_lookup (key : String) (m : HashMap String String) : Option String :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            let bucket := HashMap.get_bucket buckets idx in
            HashMap.bucket_lookup_str key bucket
    }

#[partial]
def build_alias_map (aliases : List OpenAlias) (acc : HashMap String String) : HashMap String String :=
    match aliases {
        List.empty => acc,
        List.cons a rest =>
            match a {
                { bare_name := b, qualified_name := q } =>
                    // FIRST wins, matching `lookup_open_alias`'s own
                    // linear-scan semantics -- `resolve_open_aliases_in_
                    // module_info` relies on it, putting a module's own
                    // names ahead of the ambient root ones so they
                    // shadow.
                    match alias_map_lookup b acc {
                        Option.some _ => build_alias_map rest acc,
                        Option.none => build_alias_map rest (alias_map_insert b q acc),
                    },
            },
    }

// --- Helper: empty ScopeData ---

def scope_data_empty : ScopeData := {
    def_refs := npath_map_empty,
    class_defs := List.empty,
    instances := List.empty,
    inductives := npath_map_empty,
    classes := List.empty,
    infixes := List.empty,
    conflicts := List.empty,
}

// --- Helpers: name path / module path equality ---

def npath_eq (a : NamePath) (b : NamePath) : Bool :=
    name_path_similar a b

/// Module-PATH equality, for the places a real file/module identity is
/// still being compared (`LowerAcc`'s interned `seen` list,
/// `ModuleRegistry` entry paths, `codegen/qualify.mo`'s open-alias
/// tables) as opposed to a DECL's own name, which is a `NamePath` and
/// goes through `npath_eq` above.
def modpath_eq (a : ModulePath) (b : ModulePath) : Bool :=
    Similar.similar a b

/// Exactly `!modpath_lt(a,b) && !modpath_gt(a,b)`, but rendering each
/// side ONCE instead of twice. `String.beq` is native, and no typeclass
/// dispatch is involved -- see `modpath_map_*`'s own doc comment.
def modpath_str_eq (a : ModulePath) (b : ModulePath) : Bool :=
    String.beq (show_module_path a) (show_module_path b)

// --- Helper: add a ScopeDef to ScopeData ---

def scope_data_add_def (sd : ScopeData) (d : ScopeDef) : ScopeData :=
    match d {
        mk dname _ _ _ _ => { sd with def_refs := npath_map_insert dname d sd.def_refs }
    }

// --- Helper: add an Inductive to ScopeData ---

def scope_data_add_inductive (sd : ScopeData) (ind : Inductive) : ScopeData :=
    match ind {
        mk indname _ _ _ _ _ => { sd with inductives := npath_map_insert indname ind sd.inductives }
    }

// --- build_scope_from_decls: build ScopeData from parsed declarations ---

// Two-pass: pass 1 (`build_scope_from_decls_go`, unchanged) registers every
// real `def`/`type`/`class`/`instance`/`infix` declaration exactly as
// before, `use_d`/`open_d` still no-ops there. Pass 2 (`alias_decls_in_scope`,
// below) re-walks the SAME decl_list' `use_d`/`open_d`/`scoped_open_d` against
// the now-complete pass-1 result, registering BARE (or renamed) names
// for the real qualified names they bring in -- this has to be a separate
// pass, not folded into pass 1's single left-to-right walk, because an
// `open`/`use` very commonly appears BEFORE the def(s) it names (e.g.
// `init/prelude.mo`'s `open Bool {and, false, not, or, true}` precedes
// `def Bool.not` itself) and pass 1's fold can't see forward.
//
// Deliberately narrower than the reference compiler's own `open`/`use`
// handling in two ways, both confirmed safe by checking real usage
// first: (1) only `def_refs` entries get aliased (not inductives/classes/
// constructors -- no confirmed real corpus need for aliasing those bare,
// only plain defs like `Bool.not`); (2) a glob filter (`OpenFilter.
// open_all`/`UseFilter.use_items` containing `UseItem.use_glob`) is not
// expanded -- doing so needs enumerating every entry under a path prefix
// (a `HashMap.to_list`-shaped walk), which no confirmed real corpus case
// currently needs (the one real glob, `cli/src/main.mo`'s `use cli.args
// {*}`, is only ever referenced through its own already-qualified
// `Command.*` names, not bare) -- left for future work if that changes.
// `scoped_open_d` (`open X in <decl>`, meant to scope its alias to just
// the one wrapped declaration) is treated the same as a top-level open
// (i.e. NOT actually scoped) -- true isolation would need per-decl scope
// extension during typecheck, which this checker doesn't have, and no
// non-test `.mo` file in the corpus was found using `scoped_open_d`'s
// real scoping semantics (only `lang/parser.mo`'s own unit tests and
// `lang/pretty.mo`'s round-trip fixture construct one directly).
pub def build_scope_from_decls (path : ModulePath) (decl_list : List Decl) : ScopeData :=
    let empty : ScopeData := scope_data_empty in
    let with_decls : ScopeData := build_scope_from_decls_go decl_list path empty in
    let with_builtins : ScopeData := add_builtins with_decls in
    // Skip pass 2 entirely when this module has no use_d/open_d/
    // scoped_open_d decls at all (~12% of the current corpus, grep-
    // counted) -- there is nothing for it to alias, so re-walking every
    // decl just to find that out is wasted work. Measured directly
    // (self-hosted-compiler-perf.md Track B): alias_decls_in_scope
    // accounts for ~29% of build_scope_from_decls's own cost on a
    // representative sample -- real, but build_scope_from_decls's own
    // cost is itself a minority of a file's total "scope" phase (most
    // of which is I/O/parsing, see check_file_cached's --verbose
    // timings), so this is a modest, not dominant, win -- worth taking
    // since it's free and correctness-preserving, not because it
    // explains the bulk of any single regression.
    if decls_have_aliasable_decls decl_list
    then alias_decls_in_scope decl_list with_builtins
    else with_builtins

/// O(decls) but O(1) per decl (a bare tag match, no `ScopeData` work) --
/// far cheaper than actually running `alias_decls_in_scope`'s own walk
/// (which does real `Map.lookup`/`Map.insert` work per aliased name)
/// just to discover there's nothing to do.
def decls_have_aliasable_decls (decl_list : List Decl) : Bool :=
    match decl_list {
        List.empty => false,
        List.cons d ds =>
            match d {
                Decl.use_d _ _ _ => true,
                Decl.open_d _ _ => true,
                Decl.scoped_open_d _ _ _ => true,
                _ => decls_have_aliasable_decls ds
            }
    }

def alias_decls_in_scope (decl_list : List Decl) (acc : ScopeData) : ScopeData :=
    match decl_list {
        List.empty => acc,
        List.cons d ds => alias_decls_in_scope ds (alias_one_decl d acc)
    }

def alias_one_decl (d : Decl) (acc : ScopeData) : ScopeData :=
    match d {
        Decl.use_d path filter _public => apply_use_filter acc path filter,
        Decl.open_d path filter => apply_open_filter acc path filter,
        Decl.scoped_open_d path filter inner =>
            alias_one_decl inner (apply_open_filter acc path filter),
        _ => acc
    }

// --- Aliasing: register a bare/renamed name pointing at an already-real entry ---

/// If `real_path` is a real, already-registered `def_refs` entry, ALSO
/// register it under `alias_name` (bare, or a `use ... as` rename) --
/// same `ScopeDef`, different key, matching how `scope_data_add_def`
/// already inserts under whatever `.name` it's handed.
def alias_def (acc : ScopeData) (real_path : NamePath) (alias_name : Identifier) : ScopeData :=
    match scope_data_find_def acc real_path {
        Option.some sd =>
            match sd {
                mk _ module_ sig body vis =>
                    let alias_np : NamePath := NamePath.npath (List.cons alias_name List.empty) in
                    let aliased : ScopeDef := {
                        name := alias_np,
                        module := module_,
                        sig := sig,
                        body := body,
                        // An alias is the same declaration under another
                        // key, so it carries the same visibility.
                        vis := vis,
                    } in
                    scope_data_add_def acc aliased
            },
        Option.none => acc
    }

def path_extend (path : ModulePath) (name : Identifier) : ModulePath :=
    match path {
        ModulePath.mp ids => ModulePath.mp (list_append ids (List.cons name List.empty))
    }

/// A `use` module path widened to the `NamePath` the def-keyed tables
/// take -- `use` paths stay `ModulePath` since the qualified-names
/// split (`Decl.use_d`), def names don't.
def npath_of (path : ModulePath) : NamePath :=
    match path {
        ModulePath.mp ids => NamePath.npath ids
    }

/// The inverse boundary conversion: a `NamePath` handed to a position
/// that still carries a `ModulePath` (the core-IR `match_fail` node and
/// `LowerError`'s path-carrying variants, both kept `ModulePath` on the
/// Rust host side too, converted only where the two meet). Mirrors the
/// Rust host's `impl From<NamePath> for ModulePath`.
def modpath_of (np : NamePath) : ModulePath :=
    match np {
        NamePath.npath ids => ModulePath.mp ids
    }

/// `path_extend`'s NamePath-in, NamePath-out sibling -- `open` paths
/// are NamePaths now (`Decl.open_d`).
def npath_extend (np : NamePath) (name : Identifier) : NamePath :=
    match np {
        NamePath.npath ids => NamePath.npath (list_append ids (List.cons name List.empty))
    }

def apply_open_filter (acc : ScopeData) (path : NamePath) (filter : OpenFilter) : ScopeData :=
    match filter {
        OpenFilter.open_all => acc,
        OpenFilter.open_only names => apply_open_names acc path names
    }

def apply_open_names (acc : ScopeData) (path : NamePath) (names : List Identifier) : ScopeData :=
    match names {
        List.empty => acc,
        List.cons n rest => apply_open_names (alias_def acc (npath_extend path n) n) path rest
    }

def apply_use_filter (acc : ScopeData) (path : ModulePath) (filter : UseFilter) : ScopeData :=
    match filter {
        UseFilter.use_bare => acc,
        UseFilter.use_items items => apply_use_items acc path items
    }

def apply_use_items (acc : ScopeData) (path : ModulePath) (items : List UseItem) : ScopeData :=
    match items {
        List.empty => acc,
        List.cons item rest => apply_use_items (apply_use_item acc path item) path rest
    }

def apply_use_item (acc : ScopeData) (path : ModulePath) (item : UseItem) : ScopeData :=
    match item {
        UseItem.use_name n => alias_def acc (npath_extend (npath_of path) n) n,
        UseItem.use_rename n alias_name => alias_def acc (npath_extend (npath_of path) n) alias_name,
        UseItem.use_glob => acc,
        UseItem.use_sub n items => apply_use_items acc (path_extend path n) items,
        UseItem.use_sub_rename n _alias items => apply_use_items acc (path_extend path n) items,
    }

def build_scope_from_decls_go (decl_list : List Decl) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match decl_list {
        List.empty => acc,
        List.cons d ds =>
            let new_acc : ScopeData := build_scope_one_decl d path acc in
            build_scope_from_decls_go ds path new_acc
    }

def build_scope_one_decl (d : Decl) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match d {
        Decl.def_d df => build_scope_def df path acc,
        Decl.inductive_d ind => build_scope_inductive ind path acc,
        Decl.class_d cls => build_scope_class cls path acc,
        Decl.instance_d ins => scope_data_add_instance acc ins,
        Decl.infix_d op name _vis => scope_data_add_infix acc op name,
        Decl.use_d _ _ _ => acc,
        Decl.open_d _ _ => acc,
        Decl.struct_d s => build_scope_struct s path acc,
        Decl.scoped_open_d _ _ inner => build_scope_one_decl inner path acc,
        // `def_macro_d`/`decl_gen_d`/`macro_call_d` (macro-expansion-
        // phase additions) are pre-expansion, unexpanded declarations —
        // scope has nothing real to register from them until an
        // expansion pass turns them into ordinary def_d/inductive_d/etc
        // decl_list first. No-op, matching use_d/open_d's own existing
        // convention above (this codebase has no static match-
        // exhaustiveness check — Monad's own `NonExhaustiveMatch` is a
        // RUNTIME-only error, core/src/core_eval.rs — so leaving this
        // wildcard off would silently typecheck fine today and only
        // crash the instant a real decl of one of these 3 variants
        // reached this function).
        _ => acc,
    }

def build_scope_def (df : Def) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match df {
        Def.mk {name := defname, typ, term := term_, vis, params := decl_params, ..} =>
            let sd : ScopeDef := {
                name := defname,
                module := path,
                sig := Term.hole,
                body := Term.hole,
                vis := vis,
            } in
            let with_def : ScopeData := scope_data_add_def acc sd in
            // Additional, side-table registration -- `plans/
            // implementations/named-field-construction.md`'s Phase 6 --
            // deliberately does NOT touch `sig`/`body` above (still
            // unconditionally `Term.hole`, per this function's own
            // pre-existing doc comment: that sentinel is load-bearing for
            // dozens of existing call sites, changing it is out of
            // scope). `def_params_of_term` walks `term_`'s own `Lam`
            // chain (the def's real body, still fully available here even
            // though `sd.body` above discards it) to recover the def's
            // declared parameter (name, type) list for named-call
            // resolution to consult later.
            let params : List Param := match decl_params {
                List.empty => def_params_of_term term_,
                _ => decl_params,
            } in
            let with_params : ScopeData := scope_data_add_def_params with_def defname params in
            // `typ` (the def's own DECLARED signature, `Def.typ` -- e.g.
            // `CodegenCtx -> CtxStrPair` -- distinct from `term_`'s body
            // and never itself stored in `sd.sig` above) stripped down to
            // its final return type -- see `ScopeData.def_return_types`'s
            // own doc comment for why this side-table exists.
            let ret_typ : Term := strip_pi_chain_to_return_type typ in
            let with_ret : ScopeData := scope_data_add_def_return_type with_params defname ret_typ in
            // ... and UNSTRIPPED, too (`ScopeData.def_sigs`) -- the
            // checker's signature-driven application path
            // (`type_check_app`, `lang/typecheck/infer.mo`) needs the
            // implicit-binder and parameter types, not just the final
            // return type, to check arguments against their real
            // declared types and solve the signature's type variables.
            scope_data_add_def_sig with_ret defname typ
    }

/// FALLBACK only, now that `Def.params` carries the real declared list:
/// a def's declared parameter list, in order, recovered from its own
/// BODY's leading `Term.lam` chain -- for the defs that arrive with no
/// declared list at all, i.e. macro-synthesized ones (`reify_d_def`,
/// `lang/typecheck/meta_reflect.mo`) and any decl whose `params` was
/// never populated. `Term.lam` carries no default/multiplicity/attrs
/// slot (unlike the reference compiler's own
/// `Term::Lam{param: Par::P(Param)}`, a full `Param`), so `param_many`
/// supplies multiplicity `many` with no default and no attrs -- which
/// is exactly what a param written without `:=` means. Stops at the
/// first non-`Lam` node (the def's real body).
#[terminating]
def def_params_of_term (t : Term) : List Param :=
    match t {
        Term.lam dbg typ body =>
            List.cons (param_many (scope_debug_name_to_id dbg) typ) (def_params_of_term body),
        _ => List.empty,
    }

/// Local copy of `lang/typecheck/infer.mo`'s own `debug_name_to_id` --
/// can't import it from there (`infer.mo` itself depends on `lang.scope`,
/// so the reverse dependency would be circular) -- small enough to just
/// duplicate rather than restructure module boundaries for it.
def scope_debug_name_to_id (dbg : DebugName) : Identifier :=
    match dbg {
        DebugName.named id => id,
        DebugName.unnamed => Identifier.id "_",
    }

/// Register `name -> params` into `sd.def_params`, ADDITIONAL to (never
/// replacing) `scope_data_add_def`'s own `def_refs` registration.
def scope_data_add_def_params (sd : ScopeData) (name : NamePath) (params : List Param) : ScopeData :=
    { sd with def_params := npath_map_insert name params sd.def_params }

/// Strips a def's own declared signature (`Def.typ`, a `Term.pi`/
/// `Term.forall` chain) down to its final, non-binder return type --
/// e.g. `CodegenCtx -> CtxStrPair` (`Term.pi CodegenCtx (Term.pi ... )`
/// -- actually `Term.pi CodegenCtx CtxStrPair` for a single-arg def)
/// strips to `CtxStrPair`. Mirrors `lang/codegen/emit.mo`'s own
/// `strip_db_lams`/the checker's general "strip leading binders" idiom.
#[terminating]
def strip_pi_chain_to_return_type (t : Term) : Term :=
    match t {
        Term.pi _arg ret => strip_pi_chain_to_return_type ret,
        Term.forall _dbg _kind body => strip_pi_chain_to_return_type body,
        _ => t,
    }

/// Register `name -> return_type` into `sd.def_return_types`, ADDITIONAL
/// to (never replacing) `scope_data_add_def`'s own `def_refs`
/// registration -- see `ScopeData.def_return_types`'s own doc comment.
def scope_data_add_def_return_type (sd : ScopeData) (name : NamePath) (ret_typ : Term) : ScopeData :=
    { sd with def_return_types := npath_map_insert name ret_typ sd.def_return_types }

/// Register `name -> sig` (the def's own FULL declared signature,
/// `Def.typ` -- implicit binders and parameter types included, unlike
/// `scope_data_add_def_return_type`'s stripped form) into
/// `sd.def_sigs` -- see `ScopeData.def_sigs`'s own doc comment.
def scope_data_add_def_sig (sd : ScopeData) (name : NamePath) (sig : Term) : ScopeData :=
    { sd with def_sigs := npath_map_insert name sig sd.def_sigs }

/// Registers `ind` two ways: into `.inductives` (constructor/arity
/// lookups — `scope_find_inductive` and friends) *and*, like
/// `add_builtins`' own `add_builtin_type` does for the hardcoded
/// `Type` pseudo-type just below, as a plain `ScopeDef` for the
/// inductive's own NAME. That second registration used to be missing
/// here — `scope_resolve_name`/`resolve_name_in_scope` only ever
/// search `.def_refs` (never `.inductives`), so a type name referenced
/// as an ordinary term (e.g. a `def`'s own parameter type annotation,
/// checked via `type_check_lam`'s infer-mode branch in
/// `lang/typecheck/infer.mo`) fell through to `TypeError.unknown_var`
/// even though the type genuinely exists in scope — this is the
/// self-hosted-typechecker gap documented at length in
/// `lang/module.mo`'s `check_module_with_scope` (any parameterized
/// `def` spuriously failing on its own parameter's type, hitting
/// `Color`-style user types *and* `String`/`U8`-style native types
/// alike, since `init/prelude.mo` declares native primitive types as
/// ordinary zero-constructor `type X {}` inductives that go through
/// this exact same path). `sig`/`body` both `Term.hole`, matching
/// `add_builtin_type`'s own placeholder values — nothing downstream
/// inspects a type-name `ScopeDef`'s signature today, only that the
/// lookup succeeds.
def build_scope_inductive (ind : Inductive) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    let with_ind : ScopeData := scope_data_add_inductive acc ind in
    match ind {
        mk name _ _ constructors _ vis =>
            let type_sd : ScopeDef := {
                name := name,
                module := path,
                sig := Term.hole,
                body := Term.hole,
                vis := vis,
            } in
            let with_type_def : ScopeData := scope_data_add_def with_ind type_sd in
            // Constructors are as visible as the type they belong to --
            // visibility is declared on the inductive, never per
            // constructor (visibility-declarations.md).
            add_constructors_as_defs with_type_def constructors path vis
    }

def add_constructors_as_defs (acc : ScopeData) (cns : List InductConstructor) (path : ModulePath) (vis : Visibility) : ScopeData :=
    add_constructors_go acc cns path vis

def add_constructors_go (acc : ScopeData) (cns : List InductConstructor) (path : ModulePath) (vis : Visibility) : ScopeData :=
    match cns {
        List.empty => acc,
        List.cons cn rest =>
            match cn {
                mk cnname _ _ =>
                    let sd : ScopeDef := {
                        name := cnname,
                        module := path,
                        sig := Term.hole,
                        body := Term.hole,
                        vis := vis,
                    } in
                    let new_acc : ScopeData := scope_data_add_def acc sd in
                    add_constructors_go new_acc rest path vis
            }
    }

/// The struct sibling of `build_scope_inductive` above, fixing the same
/// class of gap for `struct Foo { ... }` declarations, which used to add
/// NOTHING to scope at all (`Decl.struct_d _ => acc`) — so a struct
/// used as an ordinary type name (a parameter annotation) failed with
/// `unknown_var` for the same reason `Color`-style inductives did before
/// `build_scope_inductive`'s own fix, and matching on a struct's
/// implicit `mk` constructor got no real arity/completeness validation
/// at all (`find_inductive_for_cases`/`validate_cases_against_inductive`
/// in `lang.typecheck.infer` only consult `.inductives`, and structs
/// were never in it — `validate_match_constructors`'s own doc comment
/// says as much: "Returns ok if valid or if no inductive found (skip
/// validation)", i.e. this was silently un-validated, not a hard error).
///
/// Fixed by registering the struct's own name as a `ScopeDef` (mirroring
/// `build_scope_inductive`) *and* synthesizing a one-constructor
/// `Inductive` (name `mk`, one `Param` per `StructField`, in field
/// order) and adding THAT into `.inductives` too — this reuses the
/// existing inductive-validation machinery as-is for structs' implicit
/// constructor, rather than teaching that machinery a second, parallel
/// notion of "struct." A struct's fields have no useful `typ` of their
/// own to give the synthetic `Inductive`, so `Term.hole` stands in,
/// matching `add_builtin_type`'s and the constructor registrations
/// above's own placeholder convention (nothing downstream inspects it).
def build_scope_struct (s : Struct) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match s {
        Struct.mk name fields _attrs vis =>
            let type_np : NamePath := NamePath.npath (List.cons name List.empty) in
            let type_sd : ScopeDef := {
                name := type_np,
                module := path,
                sig := Term.hole,
                body := Term.hole,
                vis := vis,
            } in
            let with_type_def : ScopeData := scope_data_add_def acc type_sd in
            let mk_np : NamePath := NamePath.npath (List.cons (Identifier.id "mk") List.empty) in
            let mk_params : List Param := struct_fields_to_params fields in
            let mk_con : InductConstructor := InductConstructor.mk mk_np mk_params Term.hole in
            let synthetic_ind : Inductive := Inductive.mk type_np List.empty Term.hole (List.cons mk_con List.empty) List.empty vis in
            scope_data_add_inductive with_type_def synthetic_ind
    }

def struct_fields_to_params (fields : List StructField) : List Param :=
    match fields {
        List.empty => List.empty,
        List.cons f rest =>
            match f {
                StructField.mk fname ftyp fdefault fmult =>
                    let no_attrs : List Attribute := List.empty in
                    List.cons (Param.mk fname ftyp fmult fdefault no_attrs) (struct_fields_to_params rest)
            }
    }

def build_scope_class (cls : Class) (path : ModulePath) (acc : ScopeData) : ScopeData :=
    match cls {
        mk clsname _ _ methods _vis =>
            let name_list : List Identifier := List.cons clsname List.empty in
            let cls_np : NamePath := NamePath.npath name_list in
            let with_cls : ScopeData := scope_data_add_class acc cls in
            add_class_methods with_cls methods cls_np
    }

def add_class_methods (acc : ScopeData) (methods : List ClassDef) (cls_np : NamePath) : ScopeData :=
    add_methods_go acc methods cls_np

def add_methods_go (acc : ScopeData) (methods : List ClassDef) (cls_np : NamePath) : ScopeData :=
    match methods {
        List.empty => acc,
        List.cons m rest =>
            match m {
                mk method_name _ _ =>
                    match cls_np {
                        NamePath.npath cls_ids =>
                            let method_id_list : List Identifier := List.cons method_name List.empty in
                            let method_ids : List Identifier := List.append cls_ids method_id_list in
                            let full_name : NamePath := NamePath.npath method_ids in
                            let scd : ScopeClassDef := {
                                class_name := cls_np,
                                full_name := full_name,
                                name := method_name,
                                sig := Term.hole,
                            } in
                            let new_acc : ScopeData := scope_data_add_class_def acc scd in
                            add_methods_go new_acc rest cls_np
                    }
            }
    }

// --- scope_globals: extract ScopeData from Scope ---

def scope_globals (s : Scope) : ScopeData := s.scope

// ---- scope_find_inductive ---

def scope_find_inductive (name : NamePath) (s : Scope) : Result ScopeError Inductive :=
    let g : ScopeData := scope_globals s in
    let result : Option Inductive := scope_data_find_inductive g name in
    match result {
        Option.some ind => ok ind,
        Option.none => err (ScopeError.inductive_not_found name)
    }

// --- scope_find_class: the real `Class` (params/constraints/ordered
// methods), by name -- distinct from `scope_find_class_def_by_name`
// below, which finds one already-flattened `ScopeClassDef` (a single
// method's own signature), not the class as a whole. Needed by
// `lang/typecheck/infer.mo`'s `resolve_class_method` to recover a
// class's own declared params (for skolemization, `module.mo`'s
// `locals_with_class_typevars`) and ordered method-name list (for D5
// dict-field-projection, `build_dict_field_projection`) -- neither is
// recoverable from a `ScopeClassDef` alone. ---

def scope_data_classes (sd : ScopeData) : List Class :=
    sd.classes

def scope_find_class (name : NamePath) (s : Scope) : Option Class :=
    find_class_by_name (scope_data_classes (scope_globals s)) name

// --- scope_find_inductive_by_constructor ---

def scope_find_inductive_by_constructor (con_name : NamePath) (s : Scope) : Option Inductive :=
    let g : ScopeData := scope_globals s in
    scope_data_find_inductive_by_constructor g con_name

// `inds` is a `HashMap ModulePath Inductive` (see `ScopeData`'s own doc
// comment) -- there's no by-CONSTRUCTOR index, only by-type-name, so
// this still has to scan every entry; `HashMap.to_list` walks the
// buckets once to get there. Track C (self-hosted-compiler-perf.md)
// measured this specific path as unreached in the corpus it tested, so
// it's kept as a scan rather than given its own index preemptively.
def scope_data_find_inductive_by_constructor (sd : ScopeData) (con_name : NamePath) : Option Inductive :=
    find_inductive_by_constructor_in_pairs (HashMap.to_list sd.inductives) con_name

def find_inductive_by_constructor_in_pairs (pairs : List (Pair String Inductive)) (con_name : NamePath) : Option Inductive :=
    match pairs {
        List.empty => Option.none,
        List.cons p rest =>
            match p {
                Pair.pair _ ind =>
                    if inductive_has_constructor ind con_name
                    then Option.some ind
                    else find_inductive_by_constructor_in_pairs rest con_name
            }
    }

// --- scope_find_all_inductives_by_constructor: EVERY inductive with a
// matching constructor, not just the first -- used by `lang/typecheck/
// infer.mo`'s `find_inductive_for_cases_by_constructor` to detect a
// genuine ambiguity (>1 match) and fail loudly instead of silently
// picking whichever hash-bucket order happens to find first. `struct`'s
// auto-generated constructor is always named `mk` (`build_scope_struct`
// below), so this scan is ambiguous between ANY two structs in the
// whole loaded corpus the moment a match's scrutinee type isn't known
// via a more precise path -- confirmed to silently return the WRONG
// field's value, not just fail to compile (a minimal 2-struct repro,
// matching directly on a bare function call's own result with no outer
// annotation, reproduced it). ---

def scope_data_find_all_inductives_by_constructor (sd : ScopeData) (con_name : NamePath) : List Inductive :=
    match sd {
        // 10 binders, one per ScopeData field (def_sigs, the
        // side-table behind `scope_find_def_sig`, is the newest) --
        // a positional match here must track the struct's field
        // count exactly or matching a real ScopeData value fails at
        // runtime with an arity mismatch.
        mk _ _ _ inds _ _ _ _ _ _ => find_all_inductives_by_constructor_in_pairs (HashMap.to_list inds) con_name
    }

def scope_find_all_inductives_by_constructor (con_name : NamePath) (s : Scope) : List Inductive :=
    let g : ScopeData := scope_globals s in
    scope_data_find_all_inductives_by_constructor g con_name

def find_all_inductives_by_constructor_in_pairs (pairs : List (Pair String Inductive)) (con_name : NamePath) : List Inductive :=
    match pairs {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair _ ind =>
                    if inductive_has_constructor ind con_name
                    then List.cons ind (find_all_inductives_by_constructor_in_pairs rest con_name)
                    else find_all_inductives_by_constructor_in_pairs rest con_name
            }
    }

def inductive_has_constructor (ind : Inductive) (con_name : NamePath) : Bool :=
    match ind {
        mk _ _ _ constructors _ _ =>
            match constructors {
                List.empty => false,
                List.cons cn rest =>
                    match cn {
                        mk cn_mp _ _ =>
                            if npath_eq cn_mp con_name
                            then true
                            else inductive_has_constructor_rest rest con_name
                    }
            }
    }

#[terminating]
def inductive_has_constructor_rest (cns : List InductConstructor) (con_name : NamePath) : Bool :=
    match cns {
        List.empty => false,
        List.cons cn rest =>
            match cn {
                mk cn_mp _ _ =>
                    if npath_eq cn_mp con_name
                    then true
                    else inductive_has_constructor_rest rest con_name
            }
    }

// --- Find a constructor by name in an inductive, return the constructor ---

def find_constructor_in_inductive (ind : Inductive) (con_name : NamePath) : Option InductConstructor :=
    match ind {
        mk _ _ _ constructors _ _ => find_constructor_in_list constructors con_name
    }

#[terminating]
def find_constructor_in_list (cns : List InductConstructor) (con_name : NamePath) : Option InductConstructor :=
    match cns {
        List.empty => Option.none,
        List.cons cn rest =>
            match cn {
                mk cn_mp params typ =>
                    if npath_eq cn_mp con_name
                    then Option.some cn
                    else find_constructor_in_list rest con_name
            }
    }

// --- scope_find_class_def_by_name: search by simple method name (last segment) ---

def scope_find_class_def_by_name (method_name : Identifier) (s : Scope) : Result ScopeError ScopeClassDef :=
    let g : ScopeData := scope_globals s in
    let result : Option ScopeClassDef := scope_data_find_class_def_by_name g method_name in
    match result {
        Option.some cd => ok cd,
        Option.none =>
            let np : NamePath := NamePath.npath (List.cons method_name List.empty) in
            err (ScopeError.class_not_found np)
    }

def scope_data_find_class_def_by_name (sd : ScopeData) (name : Identifier) : Option ScopeClassDef :=
    find_class_def_by_name_in_list sd.class_defs name

def find_class_def_by_name_in_list (cds : List ScopeClassDef) (name : Identifier) : Option ScopeClassDef :=
    match cds {
        List.empty => Option.none,
        List.cons cd rest =>
            match cd {
                mk _class_name _full_name cd_name _ =>
                    if Similar.similar cd_name name
                    then Option.some cd
                    else find_class_def_by_name_in_list rest name
            }
    }

// --- scope_push_local ---

def scope_push_local (lv : LocalVar) (ls : LocalScope) : LocalScope :=
    let some_ls : Option LocalScope := Option.some ls in
    {
        vars := List.cons lv List.empty,
        parent := some_ls,
    }

// --- scope_find_local ---

#[terminating]
def scope_find_local (name : Identifier) (ls : LocalScope) : Option LocalVar :=
    match ls {
        mk vars parent => find_local_in_list vars name parent
    }

#[terminating]
def find_local_in_list (vars : List LocalVar) (name : Identifier) (parent : Option LocalScope) : Option LocalVar :=
    match vars {
        List.empty =>
            match parent {
                Option.none => Option.none,
                Option.some p => scope_find_local name p
            },
        List.cons lv rest =>
            match lv {
                mk lvname _ _ =>
                    if Similar.similar lvname name
                    then Option.some lv
                    else find_local_in_list rest name parent
            }
    }

// --- scope_resolve_name ---

pub def scope_resolve_name (nref : NameRef) (s : Scope) (locals : LocalScope) : Result ScopeError ScopeDef :=
    let local_result : Option ScopeDef := resolve_name_in_locals nref locals in
    match local_result {
        Option.some d => ok d,
        Option.none => resolve_name_in_scope nref s
    }

def resolve_name_in_locals (nref : NameRef) (locals : LocalScope) : Option ScopeDef :=
    match nref {
        NameRef.nid i =>
            let lv_opt : Option LocalVar := scope_find_local i locals in
            match lv_opt {
                Option.none => Option.none,
                Option.some lv =>
                    match lv {
                        LocalVar.mk lvname lvtyp _ =>
                            let empty_id_list : List Identifier := List.empty in
                            let lv_np : NamePath := NamePath.npath (List.cons lvname empty_id_list) in
                            let empty_mp : ModulePath := ModulePath.mp empty_id_list in
                            let sd : ScopeDef := {
                                name := lv_np,
                                module := empty_mp,
                                sig := lvtyp,
                                body := Term.hole,
                                // A local binding, not a declaration --
                                // it never crosses a module boundary for
                                // visibility to mean anything.
                                vis := Visibility.package_private,
                            } in
                            Option.some sd
                    }
            },
        NameRef.nnp _ => Option.none,
        NameRef.nqn _ => Option.none,
        NameRef.nop _ => Option.none
    }

/// Index just past the LAST `::` in `s`, or -1 if there is none.
///
/// Deliberately ignores `.`: the name half of a qualified reference may
/// itself be dotted (`std::io::IO.println`), and that half must survive
/// intact. `text_after_last_sep` cuts at the last `.` OR `::`, which is
/// the right rule for a bare constructor name and the wrong one here.
#[partial]
def last_colon_colon (s : String) (i : I64) (best : I64) : I64 :=
    if i + 1 < String.length s then
        match String.get s i {
            Option.some b =>
                if U8.beq b 58u8 then
                    match String.get s (i + 1) {
                        Option.some b2 =>
                            if U8.beq b2 58u8
                            then last_colon_colon s (i + 2) (i + 2)
                            else last_colon_colon s (i + 1) best,
                        Option.none => best,
                    }
                else last_colon_colon s (i + 1) best,
            Option.none => best,
        }
    else best

/// Split a `mod::name` spelling back into a `QualifiedName`.
///
/// The parser builds a real `NameRef.nqn`, but `lower_parse.mo` renders
/// it to a flat `DebugName` string and every checker call site rebuilds
/// it as a bare `nid` -- so the `nqn` arm below was unreachable and a
/// qualified reference always reported `unknown variable`. Recovering
/// the structure here makes that arm live for all of them at once
/// (`infer.mo`'s four sites, `lower_core_ir.mo`, `module.mo`).
def split_qualified_identifier (i : Identifier) : Option QualifiedName :=
    let text : String := show_identifier i in
    let cut : I64 := last_colon_colon text 0 (0 - 1) in
    if cut < 3 then Option.none
    else
        // `String.slice` takes a LENGTH, not an end index; `cut` is the
        // index just past the `::`, so the module half is `cut - 2` long.
        let module_text : String := String.slice text 0 (cut - 2) in
        let name_text : String := String.drop cut text in
        if String.beq module_text "" then Option.none
        else if String.beq name_text "" then Option.none
        else
            let qmod : ModulePath := ModulePath.mp (split_ids module_text 58u8 true) in
            let qname : NamePath := NamePath.npath (split_ids name_text 46u8 false) in
            // Annotated local, NOT a bare `Option.some { .. }`: a struct
            // literal in argument position never desugars to a
            // constructor and silently compiles to a void placeholder
            // (`le_struct_lit_survived` rejects it outright).
            let qn : QualifiedName := { qmod := qmod, qname := qname } in
            Option.some qn

/// Split `s` on a single-byte separator (`.`) or a `::` pair, into
/// `Identifier`s. Written here rather than reused because the corpus has
/// no general string-splitting helper at all.
#[partial]
def split_ids (s : String) (sep : U8) (pair : Bool) : List Identifier :=
    split_ids_go s sep pair 0 0 List.empty

#[partial]
def split_ids_go (s : String) (sep : U8) (pair : Bool) (i : I64) (start : I64) (acc : List Identifier) : List Identifier :=
    if i < String.length s then
        match String.get s i {
            Option.some b =>
                if U8.beq b sep then
                    let width : I64 := if pair then 2 else 1 in
                    let seg : String := String.slice s start (i - start) in
                    split_ids_go s sep pair (i + width) (i + width) (List.cons (Identifier.id seg) acc)
                else split_ids_go s sep pair (i + 1) start acc,
            Option.none => finish_split_ids s start acc,
        }
    else finish_split_ids s start acc

#[partial]
def finish_split_ids (s : String) (start : I64) (acc : List Identifier) : List Identifier :=
    let seg : String := String.drop start s in
    List.reverse (List.cons (Identifier.id seg) acc)

def resolve_name_in_scope (nref : NameRef) (s : Scope) : Result ScopeError ScopeDef :=
    match nref {
        // A `::` in the spelling MAY be a `NameRef.nqn` that the parse
        // lowering flattened to a string -- but it may equally be a
        // compiler-MINTED name (`with_module_prefix` mangles a promoted
        // instance method to `lang.codegen.ctors::BEq_I64_beq`), which
        // is registered under that whole string as its own key. So try
        // the plain lookup FIRST and only fall back to re-splitting:
        // re-splitting eagerly sent minted instance methods down the
        // qualified path and broke class resolution
        // (`no instance found for BEq.beq`).
        NameRef.nid i =>
            let name : NamePath := NamePath.npath (List.cons i List.empty) in
            match resolve_def_in_scope_by_name name s {
                Result.ok d => Result.ok d,
                Result.err e =>
                    match split_qualified_identifier i {
                        Option.some qn => resolve_qualified_in_scope qn s,
                        Option.none => Result.err e,
                    },
            },
        NameRef.nnp np =>
            resolve_def_in_scope_by_name np s,
        // A module-qualified ref is always a global. First flatten
        // `mod::name` to the same `.`-rendered key a dotted-declared
        // def registers under (`IO.file_exists` in `std/io.mo`); when
        // that misses (the common cross-module case, where the def's
        // own name carries no prefix), match on the pair instead --
        // registered name == `qn.qname` and owning module == `qn.qmod`.
        NameRef.nqn qn => resolve_qualified_in_scope qn s,
        NameRef.nop _ =>
            err (ScopeError.name_not_found nref)
    }

/// Resolve a `QualifiedName`: first flatten `mod::name` to the same
/// `.`-rendered key a dotted-declared def registers under
/// (`IO.file_exists` in `std/io.mo`); when that misses (the common
/// cross-module case, where the def's own name carries no prefix),
/// match on the pair instead -- registered name == `qn.qname` and
/// owning module == `qn.qmod`.
def resolve_qualified_in_scope (qn : QualifiedName) (s : Scope) : Result ScopeError ScopeDef :=
    match resolve_def_in_scope_by_name (qualified_name_to_name_path qn) s {
        Result.ok d => Result.ok d,
        Result.err _ => resolve_def_in_scope_by_module qn s,
    }

/// `mod::name` flattened to the `.`-rendered `NamePath` key a
/// dotted-declared def registers under.
def qualified_name_to_name_path (qn : QualifiedName) : NamePath :=
    match qn {
        mk qmod qname =>
            match qmod {
                ModulePath.mp mids =>
                    match qname {
                        NamePath.npath nids => NamePath.npath (list_append mids nids),
                    },
            },
    }

def resolve_def_in_scope_by_module (qn : QualifiedName) (s : Scope) : Result ScopeError ScopeDef :=
    let g : ScopeData := scope_globals s in
    match find_def_by_module_and_name (HashMap.to_list g.def_refs) qn {
        Option.some d => ok d,
        Option.none => err (ScopeError.name_not_found (NameRef.nqn qn)),
    }

/// Linear scan over the rendered-key entries -- the flat-scope model
/// has no by-module index (`ScopeData` keeps each def's `.module`
/// separately from its key), and qualified refs are rare enough that
/// the scan is only paid where the flattened-key lookup above missed.
def find_def_by_module_and_name (pairs : List (Pair String ScopeDef)) (qn : QualifiedName) : Option ScopeDef :=
    match pairs {
        List.empty => Option.none,
        List.cons p rest =>
            match p {
                Pair.pair _ sd =>
                    if name_path_similar sd.name qn.qname && String.beq (show_module_path sd.module) (show_module_path qn.qmod)
                    then Option.some sd
                    else find_def_by_module_and_name rest qn,
            },
    }

def resolve_def_in_scope_by_name (name : NamePath) (s : Scope) : Result ScopeError ScopeDef :=
    let g : ScopeData := scope_globals s in
    let result : Option ScopeDef := scope_data_find_def g name in
    match result {
        Option.some d => ok d,
        Option.none => err (ScopeError.name_not_found (NameRef.nnp name))
    }

// --- ScopeData: find a ScopeDef by ModulePath in def_refs ---
//
// `def_refs` is a `HashMap ModulePath ScopeDef` (see `bench/scope_lookup.mo`
// for why: at realistic scope sizes, `HashMap` clearly outperforms both
// `List`+linear-scan and `BTreeMap` for this lookup-heavy access pattern) —
// uses `npath_map_lookup` (this file's own bypass of `Map.lookup`'s
// typeclass dispatch, see that function's own doc comment above for why:
// this function being monomorphic over the call SITE's own types doesn't
// make `Map.lookup`/`HashMap`'s own generic body immune to the
// evaluator's documented "first-registered-instance-wins" limitation --
// confirmed as a real, live bug via a direct repro, not just a
// theoretical risk).

def scope_data_find_def (sd : ScopeData) (name : NamePath) : Option ScopeDef :=
    npath_map_lookup name sd.def_refs

// --- ScopeData: find a def's own declared param (name, type) list ---
// (`plans/implementations/named-field-construction.md`'s Phase 6.)

def scope_data_find_def_params (sd : ScopeData) (name : NamePath) : Option (List Param) :=
    npath_map_lookup name sd.def_params

/// Top-level `Scope`-based wrapper, mirroring `scope_find_inductive_by_
/// constructor`'s own plain-`Option` shape (not `Result`, unlike `scope_
/// find_inductive`/`scope_find_class_def`) -- "not found" naturally means
/// "this SHAPE doesn't apply, fall through to a different interpretation"
/// for named-call resolution's own def-target branch, not a hard error.
def scope_find_def_params (name : NamePath) (s : Scope) : Option (List Param) :=
    let g : ScopeData := scope_globals s in
    scope_data_find_def_params g name

// --- ScopeData: find a def's own declared RETURN type ---
// (see `ScopeData.def_return_types`'s own doc comment.)

def scope_data_find_def_return_type (sd : ScopeData) (name : NamePath) : Option Term :=
    npath_map_lookup name sd.def_return_types

/// Top-level `Scope`-based wrapper, same shape as `scope_find_def_params`.
def scope_find_def_return_type (name : NamePath) (s : Scope) : Option Term :=
    let g : ScopeData := scope_globals s in
    scope_data_find_def_return_type g name

// --- ScopeData: find a def's own FULL declared signature ---

def scope_data_find_def_sig (sd : ScopeData) (name : NamePath) : Option Term :=
    npath_map_lookup name sd.def_sigs

/// Top-level `Scope`-based wrapper, same shape as
/// `scope_find_def_return_type`.
def scope_find_def_sig (name : NamePath) (s : Scope) : Option Term :=
    let g : ScopeData := scope_globals s in
    scope_data_find_def_sig g name

// --- ScopeData: find an Inductive by ModulePath ---

def scope_data_find_inductive (sd : ScopeData) (name : NamePath) : Option Inductive :=
    npath_map_lookup name sd.inductives

// --- Instance handling helpers ---

def scope_data_add_instance (sd : ScopeData) (ins : Instance) : ScopeData :=
    match ins {
        mk _ cname _ _ _ _ _ =>
            { sd with instances := scope_add_to_instances sd.instances cname ins }
    }

def scope_add_to_instances (insts : List ScopeInstance) (cls_name : NamePath) (ins : Instance) : List ScopeInstance :=
    match insts {
        List.empty =>
            let ins_list : List Instance := List.cons ins List.empty in
            let si : ScopeInstance := {
                class_name := cls_name,
                instances := ins_list,
            } in
            let empty_rest : List ScopeInstance := List.empty in
            List.cons si empty_rest,
        List.cons si rest =>
            match si {
                mk cn ins_list =>
                    if npath_eq cn cls_name
                    then
                        let new_ins_list : List Instance := List.cons ins ins_list in
                        let new_si : ScopeInstance := {
                            class_name := cn,
                            instances := new_ins_list,
                        } in
                        List.cons new_si rest
                    else List.cons si (scope_add_to_instances rest cls_name ins)
            }
    }

def scope_data_add_infix (sd : ScopeData) (op : Operator) (name : NamePath) : ScopeData :=
    let inf : Infix := { operator := op, name := name } in
    { sd with infixes := List.cons inf sd.infixes }

def scope_data_add_class (sd : ScopeData) (cls : Class) : ScopeData :=
    { sd with classes := List.cons cls sd.classes }

def scope_data_add_class_def (sd : ScopeData) (cd : ScopeClassDef) : ScopeData :=
    { sd with class_defs := List.cons cd sd.class_defs }

// --- Builtins ---

// `Type`/`Prop` were registered here but `Sort`/`Pred` weren't -- a
// straight 2-of-3 incomplete port from the native compiler, which
// registers all three as real def_refs entries (`core/src/term/
// module.rs`'s own `"Type"`/`"Prop"`/`"Pred"` insertions). Confirmed as
// the direct cause of `unknown variable 'Sort'`/`'Pred'` in
// `init/tests.mo`'s own Sort-universe/Pred-as-value tests
// (`type_check_free_var`, `lang/typecheck/infer.mo`, whose `err` arm
// after a failed `scope_resolve_name` is exactly `TypeError.unknown_
// var`). Note: the self-hosted parser has no dedicated `Sort N` literal
// syntax at all (unlike native's own `sort_parser`), so registering
// `"Sort"` here makes it resolve as an ordinary `Term.hole`-signatured
// free variable, same permissive mechanism `Type`/`Prop` already use --
// not a real Sort-universe judgment. That's enough for these tests
// (which only need the checker to accept the file), not a claim that
// full Sort-universe semantics now exist.
def add_builtins (sd : ScopeData) : ScopeData :=
    let sd_with_type : ScopeData := add_builtin_type sd in
    let sd_with_prop : ScopeData := add_builtin_prop sd_with_type in
    let sd_with_sort : ScopeData := add_builtin_sort sd_with_prop in
    add_builtin_pred sd_with_sort

def add_builtin_type (sd : ScopeData) : ScopeData :=
    let type_id : Identifier := Identifier.id "Type" in
    let empty_id_list : List Identifier := List.empty in
    let type_name : NamePath := NamePath.npath (List.cons type_id empty_id_list) in
    let empty_params : List Param := List.empty in
    let empty_constructors : List InductConstructor := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let type_ind : Inductive := Inductive.mk type_name empty_params Term.hole empty_constructors empty_attrs Visibility.package_private in
    let type_sd : ScopeDef := {
        name := type_name,
        module := ModulePath.mp empty_id_list,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.pub_,
    } in
    let sd1 : ScopeData := scope_data_add_inductive sd type_ind in
    scope_data_add_def sd1 type_sd

def add_builtin_prop (sd : ScopeData) : ScopeData :=
    let prop_id : Identifier := Identifier.id "Prop" in
    let empty_id_list : List Identifier := List.empty in
    let prop_name : NamePath := NamePath.npath (List.cons prop_id empty_id_list) in
    let empty_params : List Param := List.empty in
    let empty_constructors : List InductConstructor := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let prop_ind : Inductive := Inductive.mk prop_name empty_params Term.hole empty_constructors empty_attrs Visibility.package_private in
    let prop_sd : ScopeDef := {
        name := prop_name,
        module := ModulePath.mp empty_id_list,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.pub_,
    } in
    let sd1 : ScopeData := scope_data_add_inductive sd prop_ind in
    scope_data_add_def sd1 prop_sd

def add_builtin_sort (sd : ScopeData) : ScopeData :=
    let sort_id : Identifier := Identifier.id "Sort" in
    let empty_id_list : List Identifier := List.empty in
    let sort_name : NamePath := NamePath.npath (List.cons sort_id empty_id_list) in
    let empty_params : List Param := List.empty in
    let empty_constructors : List InductConstructor := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let sort_ind : Inductive := Inductive.mk sort_name empty_params Term.hole empty_constructors empty_attrs Visibility.package_private in
    let sort_sd : ScopeDef := {
        name := sort_name,
        module := ModulePath.mp empty_id_list,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.pub_,
    } in
    let sd1 : ScopeData := scope_data_add_inductive sd sort_ind in
    scope_data_add_def sd1 sort_sd

def add_builtin_pred (sd : ScopeData) : ScopeData :=
    let pred_id : Identifier := Identifier.id "Pred" in
    let empty_id_list : List Identifier := List.empty in
    let pred_name : NamePath := NamePath.npath (List.cons pred_id empty_id_list) in
    let empty_params : List Param := List.empty in
    let empty_constructors : List InductConstructor := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let pred_ind : Inductive := Inductive.mk pred_name empty_params Term.hole empty_constructors empty_attrs Visibility.package_private in
    let pred_sd : ScopeDef := {
        name := pred_name,
        module := ModulePath.mp empty_id_list,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.pub_,
    } in
    let sd1 : ScopeData := scope_data_add_inductive sd pred_ind in
    scope_data_add_def sd1 pred_sd

// --- build_scope_from_modules: build ScopeData from loaded modules ---

/// `path` is the module being scoped -- the consumer. Every other
/// module's `priv` declarations are dropped on the way in.
def build_scope_from_modules (path : ModulePath) (loaded : ModuleRegistry) : ScopeData :=
    match loaded {
        mk modules =>
            let empty : ScopeData := scope_data_empty in
            build_scope_from_modules_go modules path empty
    }

def build_scope_from_modules_go (modules : List Module) (consumer : ModulePath) (acc : ScopeData) : ScopeData :=
    match modules {
        List.empty => acc,
        List.cons m rest =>
            let with_mod : ScopeData := build_scope_from_one_module m consumer acc in
            build_scope_from_modules_go rest consumer with_mod
    }

def build_scope_from_one_module (m : Module) (consumer : ModulePath) (acc : ScopeData) : ScopeData :=
    match m {
        mk _path _inductives defs infxs _instances =>
            let with_defs : ScopeData := add_module_defs acc consumer defs in
            let with_inds : ScopeData := add_module_inductives with_defs _inductives in
            let with_inst : ScopeData := add_module_instances with_inds _instances in
            add_module_infixes with_inst infxs
    }

/// `priv` means module-private: visible where it is declared and nowhere
/// else. The check is on the DEF's own owning module rather than on the
/// module currently being folded in, because a re-export can carry a def
/// from one module into another's entry list.
def scope_def_visible_to (consumer : ModulePath) (d : ScopeDef) : Bool :=
    match d.vis {
        Visibility.priv_ => String.beq (show_module_path d.module) (show_module_path consumer),
        _ => true
    }

def add_module_defs (acc : ScopeData) (consumer : ModulePath) (defs : List ScopeDef) : ScopeData :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            if scope_def_visible_to consumer d
            then
                let new_acc : ScopeData := scope_data_add_def acc d in
                add_module_defs new_acc consumer rest
            else add_module_defs acc consumer rest
    }

def add_module_inductives (acc : ScopeData) (inds : List Inductive) : ScopeData :=
    match inds {
        List.empty => acc,
        List.cons ind rest =>
            let new_acc : ScopeData := scope_data_add_inductive acc ind in
            add_module_inductives new_acc rest
    }

def add_module_instances (acc : ScopeData) (insts : List ScopeInstance) : ScopeData :=
    match insts {
        List.empty => acc,
        List.cons si rest =>
            let new_acc : ScopeData := add_module_instance_group acc si in
            add_module_instances new_acc rest
    }

def add_module_instance_group (acc : ScopeData) (si : ScopeInstance) : ScopeData :=
    { acc with instances := scope_add_instance_group acc.instances si }

def scope_add_instance_group (insts : List ScopeInstance) (si : ScopeInstance) : List ScopeInstance :=
    match si {
        mk cn ins_list =>
            scope_add_instances_to_group insts cn ins_list
    }

def scope_add_instances_to_group (insts : List ScopeInstance) (cls_name : NamePath) (ins_list : List Instance) : List ScopeInstance :=
    match insts {
        List.empty =>
            let si : ScopeInstance := {
                class_name := cls_name,
                instances := ins_list,
            } in
            let empty_rest : List ScopeInstance := List.empty in
            List.cons si empty_rest,
        List.cons existing rest =>
            match existing {
                mk cn existing_list =>
                    if npath_eq cn cls_name
                    then
                        let merged_list : List Instance := list_append existing_list ins_list in
                        let new_si : ScopeInstance := {
                            class_name := cn,
                            instances := merged_list,
                        } in
                        List.cons new_si rest
                    else List.cons existing (scope_add_instances_to_group rest cls_name ins_list)
            }
    }

def add_module_infixes (acc : ScopeData) (infxs : List Infix) : ScopeData :=
    match infxs {
        List.empty => acc,
        List.cons inf rest => { acc with infixes := List.cons inf acc.infixes },
    }

// ─── Infix operator resolution ─────────────────────────────────────
//
// `expr_climb_op_rhs_expr` (lang/parser.mo) preserves an operator
// symbol like `+`/`==`/a custom one as a `Term.var`'s own name
// (`DebugName.named (Identifier.id "+")`, a "fake identifier" that
// never arises from ordinary identifier parsing) instead of resolving
// it at parse time — parsing alone doesn't know what an operator maps
// to, only a built scope does (`infixes` above, populated from every
// loaded module's own `infix (op) := target` declarations). This is
// the resolution step: walk a decl_list's own Terms, and for every var
// whose name matches a registered operator symbol, replace it with a
// real reference to that operator's resolved target `ModulePath` —
// mirrors `lang.typecheck.macro_expand`'s `expand_term`/
// `lang.typecheck.macro_queue`'s `expand_decl_terms` shape exactly
// (same per-Decl-kind field coverage), reusing `term_map_children` as
// the shared generic structural-recursion primitive both use.
//
// Must run AFTER `infixes` is actually populated — wired into
// `lang.codegen.emit`'s `compile_loaded_modules_to_ir` and
// `lang.codegen.test_driver`'s `compile_loaded_modules_to_test_ir`,
// both of which already have a flat decl_list with every loaded
// module's own `infix` declarations in it by the time codegen runs
// (see `collect_infixes` below — no separately-built `Scope` needed
// there, just a scan of the same decl_list already in hand).
//
// Deliberately does NOT resolve a typeclass-routed operator (e.g. `==`
// -> `BEq.beq`) any further than producing a reference to that class
// method — actually DISPATCHING to a concrete instance's own
// implementation is `lang.typecheck.infer`'s `resolve_class_method`'s
// job, itself a separate, still-incomplete piece of work (see that
// function's own doc comment). An operator whose registered target
// IS a plain, direct function (e.g. `init/lib.mo`'s `infix (+) :=
// I64.add`) resolves and compiles all the way through; one whose only
// registered target is typeclass-routed surfaces as a normal
// unresolved-method situation downstream instead of a silent `void`.

#[partial]
def lookup_infix (infixes : List Infix) (op_str : String) : Option NamePath :=
    match infixes {
        List.empty => Option.none,
        List.cons inf rest =>
            match inf {
                Infix.mk op target =>
                    if String.beq (show_operator op) op_str
                    then Option.some target
                    else lookup_infix rest op_str,
            },
    }

#[partial]
def resolve_infix_term (infixes : List Infix) (t : Term) : Term :=
    match t {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id =>
                    match lookup_infix infixes (show_identifier id) {
                        Option.some target => Term.var idx (DebugName.named (Identifier.id (show_name_path target))),
                        Option.none => t,
                    },
                DebugName.unnamed => t,
            },
        _ => term_map_children (resolve_infix_term infixes) t,
    }

#[partial]
def resolve_infix_opt_term (infixes : List Infix) (t : Option Term) : Option Term :=
    match t {
        Option.some x => Option.some (resolve_infix_term infixes x),
        Option.none => Option.none,
    }

#[partial]
def resolve_infix_terms (infixes : List Infix) (ts : List Term) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (resolve_infix_term infixes x) (resolve_infix_terms infixes rest),
    }

#[partial]
def resolve_infix_param (infixes : List Infix) (p : Param) : Param :=
    match p {
        Param.mk pname typ mult default attrs =>
            Param.mk pname (resolve_infix_term infixes typ) mult (resolve_infix_opt_term infixes default) attrs,
    }

#[partial]
def resolve_infix_params (infixes : List Infix) (params : List Param) : List Param :=
    match params {
        List.empty => List.empty,
        List.cons p rest => List.cons (resolve_infix_param infixes p) (resolve_infix_params infixes rest),
    }

#[partial]
def resolve_infix_induct_constructor (infixes : List Infix) (ctor : InductConstructor) : InductConstructor :=
    match ctor {
        InductConstructor.mk cname params typ =>
            InductConstructor.mk cname (resolve_infix_params infixes params) (resolve_infix_term infixes typ),
    }

#[partial]
def resolve_infix_induct_constructors (infixes : List Infix) (ctors : List InductConstructor) : List InductConstructor :=
    match ctors {
        List.empty => List.empty,
        List.cons c rest => List.cons (resolve_infix_induct_constructor infixes c) (resolve_infix_induct_constructors infixes rest),
    }

#[partial]
def resolve_infix_struct_field (infixes : List Infix) (f : StructField) : StructField :=
    match f {
        StructField.mk fname typ default mult =>
            StructField.mk fname (resolve_infix_term infixes typ) (resolve_infix_opt_term infixes default) mult,
    }

#[partial]
def resolve_infix_struct_fields (infixes : List Infix) (fields : List StructField) : List StructField :=
    match fields {
        List.empty => List.empty,
        List.cons f rest => List.cons (resolve_infix_struct_field infixes f) (resolve_infix_struct_fields infixes rest),
    }

#[partial]
def resolve_infix_class_def (infixes : List Infix) (cd : ClassDef) : ClassDef :=
    match cd {
        ClassDef.mk cname typ default => ClassDef.mk cname (resolve_infix_term infixes typ) (resolve_infix_opt_term infixes default),
    }

#[partial]
def resolve_infix_class_defs (infixes : List Infix) (cds : List ClassDef) : List ClassDef :=
    match cds {
        List.empty => List.empty,
        List.cons cd rest => List.cons (resolve_infix_class_def infixes cd) (resolve_infix_class_defs infixes rest),
    }

#[partial]
def resolve_infix_def (infixes : List Infix) (d : Def) : Def :=
    match d {
        Def.mk {name := dname, typ, term, constraints, attrs, vis, params, ..} =>
            Def.mk dname (resolve_infix_term infixes typ) (resolve_infix_term infixes term) constraints attrs vis params,
    }

#[partial]
def resolve_infix_inductive (infixes : List Infix) (ind : Inductive) : Inductive :=
    match ind {
        Inductive.mk iname params typ constructors attrs vis =>
            Inductive.mk iname (resolve_infix_params infixes params) (resolve_infix_term infixes typ)
                (resolve_infix_induct_constructors infixes constructors) attrs vis,
    }

#[partial]
def resolve_infix_struct (infixes : List Infix) (s : Struct) : Struct :=
    match s { Struct.mk sname fields attrs vis => Struct.mk sname (resolve_infix_struct_fields infixes fields) attrs vis }

#[partial]
def resolve_infix_class (infixes : List Infix) (cls : Class) : Class :=
    match cls {
        Class.mk clsname params constraints methods vis =>
            Class.mk clsname (resolve_infix_params infixes params) constraints (resolve_infix_class_defs infixes methods) vis,
    }

#[partial]
def resolve_infix_instance (infixes : List Infix) (ins : Instance) : Instance :=
    match ins {
        Instance.mk insname cls constraints args vis implicit_params defs =>
            Instance.mk insname cls constraints (resolve_infix_terms infixes args) vis (resolve_infix_params infixes implicit_params) (resolve_infix_defs_list infixes defs),
    }

/// Applies infix-operator resolution to every method `Def` in an
/// instance's own body (`Instance.defs`) -- mirrors
/// `resolve_infix_class_defs`'s identical role for `Class.methods`. An
/// instance method can itself use `+`/`==`/any user `infix` operator
/// (e.g. `Append (List A)`'s own `List.append` recursing via `++`), so
/// this must run the same as any other def body, not just the
/// instance's own `args`/`implicit_params`.
#[partial]
def resolve_infix_defs_list (infixes : List Infix) (defs : List Def) : List Def :=
    match defs {
        List.empty => List.empty,
        List.cons d rest => List.cons (resolve_infix_def infixes d) (resolve_infix_defs_list infixes rest),
    }

/// Applies infix-operator resolution to every `Term` field embedded in
/// one decl. `use_d`/`open_d`/`infix_d`/macro-related decls pass
/// through unchanged — none of them embed a `Term` that could contain
/// an unresolved operator reference. `scoped_open_d` recurses into its
/// own wrapped inner decl (mirrors `build_scope_one_decl`'s own
/// treatment of it).
#[partial]
def resolve_infix_decl (infixes : List Infix) (d : Decl) : Decl :=
    match d {
        Decl.def_d d_val => Decl.def_d (resolve_infix_def infixes d_val),
        Decl.inductive_d ind => Decl.inductive_d (resolve_infix_inductive infixes ind),
        Decl.struct_d s => Decl.struct_d (resolve_infix_struct infixes s),
        Decl.class_d cls => Decl.class_d (resolve_infix_class infixes cls),
        Decl.instance_d ins => Decl.instance_d (resolve_infix_instance infixes ins),
        Decl.scoped_open_d path filter inner => Decl.scoped_open_d path filter (resolve_infix_decl infixes inner),
        _ => d,
    }

/// Collects every `infix (op) := target` declaration already present
/// in `decl_list` — used by codegen's own entry points, which have a
/// flat, already-fully-loaded decl_list (every dependency module's own
/// decls included) but no separately-built `Scope` to read `.infixes`
/// from directly (unlike `lang.module`'s check/typecheck pipeline,
/// which already threads a real `Scope` through and should read its
/// own `ScopeData.infixes` instead of calling this).
#[partial]
def infix_from_decl (d : Decl) : Option Infix :=
    match d {
        // Annotated local, not `Option.some { ... }` -- the bare
        // struct-literal-in-argument-position pitfall
        // (`validate_no_undesugared_struct_lits`'s own message): the
        // unannotated literal never desugars to `Infix.mk` and silently
        // compiles to a void placeholder, so EVERY infix operator
        // resolution would read garbage through this backend.
        Decl.infix_d op target _vis =>
            let fx : Infix := { operator := op, name := target } in
            Option.some fx,
        _ => Option.none,
    }

def collect_infixes (decl_list : List Decl) : List Infix :=
    List.filter_map infix_from_decl decl_list

/// Resolves infix operators across a whole decl_list at once —
/// `resolve_infix_decl` applied to every entry.
#[partial]
def resolve_infix_decls (infixes : List Infix) (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest => List.cons (resolve_infix_decl infixes d) (resolve_infix_decls infixes rest),
    }

// --- Open/use alias resolution: rewrite a bare `open`/`use`-imported
// name reference to its real, fully qualified target -----------------
//
// `alias_def` (above, `apply_open_names`/`apply_use_item`) registers a
// bare-imported name (`open IO {file_exists}`, `use std.io {file_exists}`)
// as its OWN, separate `ScopeData` entry -- same signature/body as the
// real def, but under the BARE name, not the qualified one. That's
// exactly what the type checker needs to resolve a bare call's
// signature. But codegen (`lang.codegen.emit`) never consults
// `ScopeData` at all -- it walks the raw, still-bare `Term`s directly,
// and a bare call's own `Term.var` still carries whatever bare name the
// SOURCE TEXT wrote, never rewritten to the real qualified path the way
// `resolve_infix_term` already does for operators. `compile_call_head`'s
// own fallback (the ordinary, non-native/non-constructor call path)
// mangles THAT bare name directly (`replace_dots_with_underscores`),
// producing a call to a global that was never actually compiled (the
// real one compiled under its qualified, mangled name instead) --
// `llc: undefined value '@file_exists'`, confirmed live compiling
// `cli/src/main.mo` itself (`lang/module.mo`'s own `open IO {file_exists,
// is_dir, list_dir, read_file}`, used bare throughout). `println` never
// exposed this: it's ALSO separately registered as a native fast-path
// name (`native_op_table`'s bare "println" key), so its bare calls are
// term-level-inlined before ever reaching `compile_call_head`'s
// fallback at all.
//
// Fixed the same way `resolve_infix_decls` fixes its own analogous
// "operator not yet resolved to its real target" gap: a dedicated pass,
// run once per compile over the flat, already-loaded decl_list, that
// finds every `open`/`use` alias declared anywhere in it and rewrites
// every bare `Term.var` reference matching one to the real, fully
// qualified name -- mirrors `resolve_infix_term`'s own recursion
// exactly (a blind, name-only `term_map_children` walk, no local-
// binder-shadowing check -- same tolerated risk `resolve_infix_term`
// already accepts, low in practice: none of `file_exists`/`is_dir`/
// `list_dir`/`read_file`/`write_file` collide with any local variable
// name anywhere in this corpus).
pub struct OpenAlias {
    bare_name : String,
    qualified_name : String,
}

#[partial]
def mk_open_alias (bare : String) (qualified : String) : OpenAlias :=
    { bare_name := bare, qualified_name := qualified }

#[partial]
def append_open_aliases (a : List OpenAlias) (b : List OpenAlias) : List OpenAlias :=
    match a {
        List.empty => b,
        List.cons x rest => List.cons x (append_open_aliases rest b),
    }

#[partial]
def open_aliases_from_names (path : NamePath) (names : List Identifier) : List OpenAlias :=
    match names {
        List.empty => List.empty,
        List.cons n rest =>
            List.cons (mk_open_alias (show_identifier n) (show_name_path (npath_extend path n))) (open_aliases_from_names path rest),
    }

#[partial]
def open_aliases_from_filter (path : NamePath) (filter : OpenFilter) : List OpenAlias :=
    match filter {
        OpenFilter.open_all => List.empty,
        OpenFilter.open_only names => open_aliases_from_names path names,
    }

#[partial]
def use_aliases_from_item (path : ModulePath) (item : UseItem) : List OpenAlias :=
    match item {
        UseItem.use_name n => List.cons (mk_open_alias (show_identifier n) (show_name_path (npath_extend (npath_of path) n))) List.empty,
        UseItem.use_rename n alias_name => List.cons (mk_open_alias (show_identifier alias_name) (show_name_path (npath_extend (npath_of path) n))) List.empty,
        UseItem.use_glob => List.empty,
        UseItem.use_sub n items => use_aliases_from_items (path_extend path n) items,
        UseItem.use_sub_rename n _alias items => use_aliases_from_items (path_extend path n) items,
    }

#[partial]
def use_aliases_from_items (path : ModulePath) (items : List UseItem) : List OpenAlias :=
    match items {
        List.empty => List.empty,
        List.cons item rest => append_open_aliases (use_aliases_from_item path item) (use_aliases_from_items path rest),
    }

#[partial]
def open_aliases_from_decl (d : Decl) : List OpenAlias :=
    match d {
        Decl.open_d path filter => open_aliases_from_filter path filter,
        Decl.scoped_open_d path filter inner =>
            append_open_aliases (open_aliases_from_filter path filter) (open_aliases_from_decl inner),
        Decl.use_d path filter _public =>
            match filter {
                UseFilter.use_bare => List.empty,
                UseFilter.use_items items => use_aliases_from_items path items,
            },
        _ => List.empty,
    }

/// Collects every `open`/`use` bare-name alias declared anywhere in
/// `decl_list` -- mirrors `collect_infixes`'s identical role/doc
/// comment for operators. These are CANDIDATES only -- see `filter_
/// valid_open_aliases`'s own doc comment for why the reconstructed
/// qualified name isn't always real, and must be validated against the
/// whole program's own known def names before being used to rewrite
/// anything.
#[partial]
def collect_open_aliases (decl_list : List Decl) : List OpenAlias :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest => append_open_aliases (open_aliases_from_decl d) (collect_open_aliases rest),
    }

#[partial]
def def_name_from_decl (d : Decl) : Option String :=
    match d {
        Decl.def_d dd => match dd { Def.mk {name, typ := _typ, term := _term, constraints := _constraints, attrs := _attrs, vis := _vis, ..} => Option.some (show_name_path name) },
        _ => Option.none,
    }

/// Every real, existing top-level `Def`'s own registered name in
/// `decl_list` -- used by `filter_valid_open_aliases` to validate a
/// candidate alias's reconstructed qualified name actually refers to
/// something real, not a guess. Mirrors `lang.codegen.emit`'s own
/// `extract_defs` (`Decl.def_d` only -- promoted instance methods don't
/// exist as real `Def`s yet at the point this runs, before `promote_
/// instance_defs`, but a `use`/`open` alias targeting one specifically
/// is not a shape this corpus actually uses).
#[partial]
def collect_def_names (decl_list : List Decl) : List String :=
    List.filter_map def_name_from_decl decl_list

/// Filters `candidates` (from `collect_open_aliases`) down to the ones
/// whose RECONSTRUCTED qualified name (`path_extend`'s `use`/`open`
/// path prepended onto the bare imported name, then `show_module_path`)
/// actually matches a real, existing top-level `Def` somewhere in
/// `known_names` (the whole loaded program's own def names, gathered
/// once via `collect_def_names` across every loaded module -- a `use`/
/// `open`'s own `path` argument usually names a DIFFERENT file than the
/// one currently being resolved).
///
/// This reconstruction is only correct when the target def's OWN
/// declared name genuinely carries that dotted prefix (`IO.file_exists`,
/// declared exactly that way in `std/io.mo`) -- NOT for the far more
/// common cross-file `use some.file.path {bare_name}` shape, where the
/// real def is registered under its own plain, undotted name and
/// `path` merely names which FILE it lives in, no part of its own
/// identity. Confirmed as a real, severe regression via the full self-
/// compile: EVERY bare-imported, bare-called cross-file def (`use
/// lang.module {load_file_modules}`-style, the dominant import style
/// across this whole 51-module corpus) was being "resolved" to a bogus
/// qualified name matching no real def at all, dropping `Reachable
/// decl_list` from ~1925 to ~171 -- including `compile_loaded_modules_
/// to_ir` itself, `main`'s own entry point into codegen. A candidate
/// whose qualified name doesn't validate is simply dropped (not
/// rewritten at all) -- its bare form was already the term's real name
/// all along in that case, so leaving it alone is correct, matching
/// `alias_def`'s own conservative `Option.none => acc` fallback for the
/// type checker's identical situation.
#[partial]
def filter_valid_open_aliases (known_names : List String) (aliases : List OpenAlias) : List OpenAlias :=
    List.filter (fn (a : OpenAlias) => str_list_contains known_names a.qualified_name) aliases

/// Deliberately does NOT mirror `resolve_infix_term`'s family all the
/// way down into `Param`/`InductConstructor`/`StructField`/`ClassDef`
/// TYPE positions the way `resolve_infix_decl` does -- those are pure
/// type-level annotations, never "compiled as a call" the way
/// `compile_call_head`'s buggy fallback is, so they don't need this
/// fix. Rewriting them anyway is actively WRONG: `IO` itself is
/// routinely brought in bare (`use io {IO, println}`), and `emit_type_
/// head_is_io` (`lang.scope`, used by `compile_db_def_ir_body`'s own
/// "does `main`'s `IO`-typed return value need unwrapping for the C
/// runtime's `int main()`" check) matches the type head by EXACT STRING
/// COMPARISON against literal `"IO"` -- rewriting a bare `IO` type
/// annotation to some qualified alternative breaks that match, leaving
/// `main`'s real computed value wrapped and an arbitrary tag/pointer
/// returned as the process exit code instead. Confirmed as a real
/// regression from an earlier, broader version of this same pass (which
/// did walk `Def.typ` too, mirroring `resolve_infix_def` exactly): every
/// `lang/codegen/test/test_closure_capture_e2e.mo` test started failing
/// with a plausible-looking but wrong number (e.g. expected 15, got 16)
/// the moment it landed, all four sharing this exact "IO", used both as
/// an opened value name and a bare type annotation" shape. Restricted to
/// `Def.term` (and `Instance.defs`' own method bodies) only -- the two
/// places an executable `Term.var` naming a bare `open`/`use`d function
/// can actually reach `compile_call_head`'s fallback.
///
/// Unlike `resolve_infix_term` (whose blind, name-only rewrite this
/// pass originally mirrored exactly), this ALSO needs real local-binder
/// shadowing awareness, threaded as `bound` -- a plain-English bare
/// import name (`use std.path {Path}`, `use lang.types {content}`, ...)
/// coincides with an ordinary `let`-bound/lambda-param/match-arm local
/// variable name FAR more often than an operator symbol like `+` ever
/// would, and this codebase's own `Term` here is still name-based (not
/// yet lowered to real de Bruijn indices -- a synthesized reference at
/// this stage, e.g. `resolve_class_method`'s own `Term.var 0 (DebugName.
/// named ...)`, uses a placeholder index regardless of true binder
/// depth, so `idx` can't discriminate "genuinely local" from "genuinely
/// free" here either). Confirmed as a real regression from the
/// non-shadowing-aware version: the full `cli/src/main.mo` self-compile's
/// own `Reachable decl_list` collapsed from ~1925 to ~181 even after
/// alias collection/resolution was correctly scoped per-module --
/// because a `use`/`open` alias in one FUNCTION was still incorrectly
/// shadowing an unrelated local variable of the same bare name in a
/// DIFFERENT function within the very same module.
#[partial]
def resolve_open_alias_term (names : HashMap String String) (t : Term) : Term :=
    resolve_open_alias_term_scoped names List.empty t

#[partial]
def str_list_contains (xs : List String) (x : String) : Bool := match xs {
    List.empty => false,
    List.cons hd rest => if String.beq hd x then true else str_list_contains rest x,
}

#[partial]
def push_bound_dbg (bound : List String) (dbg : DebugName) : List String :=
    match dbg {
        DebugName.named id => List.cons (show_identifier id) bound,
        DebugName.unnamed => bound,
    }

#[partial]
def push_bound_names (bound : List String) (names : List Identifier) : List String :=
    match names {
        List.empty => bound,
        List.cons n rest => push_bound_names (List.cons (show_identifier n) bound) rest,
    }

#[partial]
def push_bound_field_pattern (bound : List String) (fp : Option FieldPattern) : List String :=
    match fp {
        Option.none => bound,
        Option.some pat => match pat {
            FieldPattern.mk entries _rest => push_bound_field_entries bound entries,
        },
    }

#[partial]
def push_bound_field_entries (bound : List String) (entries : List FieldPatternEntry) : List String :=
    match entries {
        List.empty => bound,
        List.cons e rest =>
            match e {
                FieldPatternEntry.mk _field binder => push_bound_field_entries (List.cons (show_identifier binder) bound) rest,
            },
    }

#[partial]
def resolve_open_alias_term_scoped (names : HashMap String String) (bound : List String) (t : Term) : Term :=
    match t {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id =>
                    let name := show_identifier id in
                    if str_list_contains bound name
                    then t
                    else match alias_map_lookup name names {
                        Option.some qualified => Term.var idx (DebugName.named (Identifier.id qualified)),
                        Option.none => t,
                    },
                DebugName.unnamed => t,
            },
        Term.lam dbg typ body =>
            Term.lam dbg (resolve_open_alias_term_scoped names bound typ) (resolve_open_alias_term_scoped names (push_bound_dbg bound dbg) body),
        Term.forall dbg kind body =>
            Term.forall dbg (resolve_open_alias_term_scoped names bound kind) (resolve_open_alias_term_scoped names (push_bound_dbg bound dbg) body),
        Term.pi arg ret =>
            Term.pi (resolve_open_alias_term_scoped names bound arg) (resolve_open_alias_term_scoped names bound ret),
        Term.app fun_ arg =>
            Term.app (resolve_open_alias_term_scoped names bound fun_) (resolve_open_alias_term_scoped names bound arg),
        Term.lit value => Term.lit (resolve_open_alias_literal_scoped names bound value),
        Term.ntv n => Term.ntv (native_map_children (resolve_open_alias_term_scoped names bound) n),
        Term.con c => Term.con (con_map_children (resolve_open_alias_term_scoped names bound) c),
        Term.type_ u => Term.type_ u,
        Term.hole => Term.hole,
        Term.quote_ inner => Term.quote_ (resolve_open_alias_term_scoped names bound inner),
        Term.var_macro idx dbg => Term.var_macro idx dbg,
        // Preserving: this rewrites names in place and must not drop a
        // position while doing it.
        Term.ctx loc inner => Term.ctx loc (resolve_open_alias_term_scoped names bound inner),
    }

#[partial]
def resolve_open_alias_literal_scoped (names : HashMap String String) (bound : List String) (l : Literal) : Literal :=
    match l {
        Literal.str v => Literal.str v,
        Literal.char v => Literal.char v,
        Literal.num n suf => Literal.num n suf,
        Literal.flt txt suf => Literal.flt txt suf,
        Literal.if_ a b c =>
            Literal.if_ (resolve_open_alias_term_scoped names bound a) (resolve_open_alias_term_scoped names bound b) (resolve_open_alias_term_scoped names bound c),
        Literal.match_ scrut cases =>
            Literal.match_ (resolve_open_alias_term_scoped names bound scrut) (resolve_open_alias_match_cases names bound cases),
        Literal.struct_lit fields type_name =>
            Literal.struct_lit (resolve_open_alias_struct_lit_fields names bound fields) (resolve_open_alias_opt_term_scoped names bound type_name),
        Literal.struct_update base fields =>
            Literal.struct_update (resolve_open_alias_term_scoped names bound base) (resolve_open_alias_struct_lit_fields names bound fields),
    }

#[partial]
def resolve_open_alias_opt_term_scoped (names : HashMap String String) (bound : List String) (t : Option Term) : Option Term :=
    match t {
        Option.some x => Option.some (resolve_open_alias_term_scoped names bound x),
        Option.none => Option.none,
    }

#[partial]
def resolve_open_alias_struct_lit_fields (names : HashMap String String) (bound : List String) (fields : List StructLitField) : List StructLitField :=
    match fields {
        List.empty => List.empty,
        List.cons f rest =>
            match f {
                StructLitField.mk name value =>
                    List.cons (StructLitField.mk name (resolve_open_alias_term_scoped names bound value)) (resolve_open_alias_struct_lit_fields names bound rest),
            },
    }

#[partial]
def resolve_open_alias_match_cases (names : HashMap String String) (bound : List String) (cases : List MatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest => List.cons (resolve_open_alias_match_case names bound c) (resolve_open_alias_match_cases names bound rest),
    }

#[partial]
def resolve_open_alias_match_case (names : HashMap String String) (bound : List String) (c : MatchCase) : MatchCase :=
    match c {
        MatchCase.mc name args body fp =>
            let bound1 := push_bound_names bound args in
            let bound2 := push_bound_field_pattern bound1 fp in
            MatchCase.mc name args (resolve_open_alias_term_scoped names bound2 body) fp,
    }

#[partial]
def resolve_open_alias_def (names : HashMap String String) (d : Def) : Def :=
    match d {
        Def.mk {name := dname, typ, term, constraints, attrs, vis, params, ..} =>
            Def.mk dname typ (resolve_open_alias_term names term) constraints attrs vis params,
    }

#[partial]
def resolve_open_alias_defs_list (names : HashMap String String) (defs : List Def) : List Def :=
    match defs {
        List.empty => List.empty,
        List.cons d rest => List.cons (resolve_open_alias_def names d) (resolve_open_alias_defs_list names rest),
    }

#[partial]
def resolve_open_alias_instance (names : HashMap String String) (ins : Instance) : Instance :=
    match ins {
        Instance.mk insname cls constraints args vis implicit_params defs =>
            Instance.mk insname cls constraints args vis implicit_params (resolve_open_alias_defs_list names defs),
    }

#[partial]
def resolve_open_alias_decl (names : HashMap String String) (d : Decl) : Decl :=
    match d {
        Decl.def_d d_val => Decl.def_d (resolve_open_alias_def names d_val),
        Decl.instance_d ins => Decl.instance_d (resolve_open_alias_instance names ins),
        Decl.scoped_open_d path filter inner => Decl.scoped_open_d path filter (resolve_open_alias_decl names inner),
        // A struct field's DEFAULT and a class method's DEFAULT are
        // executable terms that reach codegen like any other body: the
        // checker splices a field default into every struct literal that
        // omits that field. `lang/types.mo`'s `ScopeData.def_params`
        // defaults to `HashMap.map HashMap.empty_buckets`, so leaving it
        // alone while `HashMap.empty_buckets` was renamed made every
        // `ScopeData` literal fail to elaborate with "unknown variable"
        // -- and, because codegen elaboration is best-effort, that
        // surfaced only as `scope_data_empty` tripping the
        // undesugared-struct-literal gate, several stages later.
        //
        // Only the DEFAULTS are walked. A field's/method's `typ` stays
        // untouched for the same reason `resolve_open_alias_def` skips
        // `Def.typ` -- see this module's own note about
        // `emit_type_head_is_io`'s literal `"IO"` match.
        Decl.struct_d st => Decl.struct_d (resolve_open_alias_struct names st),
        Decl.class_d cls => Decl.class_d (resolve_open_alias_class names cls),
        _ => d,
    }

#[partial]
def resolve_open_alias_struct (names : HashMap String String) (st : Struct) : Struct :=
    match st {
        Struct.mk name fields attrs vis => Struct.mk name (resolve_open_alias_struct_field_defaults names fields) attrs vis,
    }

#[partial]
def resolve_open_alias_struct_field_defaults (names : HashMap String String) (fields : List StructField) : List StructField :=
    match fields {
        List.empty => List.empty,
        List.cons f rest =>
            match f {
                StructField.mk fname typ default mult =>
                    List.cons (StructField.mk fname typ (resolve_open_alias_opt_term_scoped names List.empty default) mult)
                        (resolve_open_alias_struct_field_defaults names rest),
            },
    }

#[partial]
def resolve_open_alias_class (names : HashMap String String) (cls : Class) : Class :=
    match cls {
        Class.mk name params constraints methods vis =>
            Class.mk name params constraints (resolve_open_alias_class_defs names methods) vis,
    }

#[partial]
def resolve_open_alias_class_defs (names : HashMap String String) (methods : List ClassDef) : List ClassDef :=
    match methods {
        List.empty => List.empty,
        List.cons m rest =>
            match m {
                ClassDef.mk mname typ default =>
                    List.cons (ClassDef.mk mname typ (resolve_open_alias_opt_term_scoped names List.empty default))
                        (resolve_open_alias_class_defs names rest),
            },
    }

/// Resolves open/use names across a whole decl_list at once --
/// `resolve_open_alias_decl` applied to every entry. Wired in right
/// alongside `resolve_infix_decls` (`lang.codegen.emit`'s
/// `compile_loaded_modules_to_ir`).
#[partial]
def resolve_open_alias_decls (names : HashMap String String) (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest => List.cons (resolve_open_alias_decl names d) (resolve_open_alias_decls names rest),
    }

// --- Phase 2 (dictionary-passing plan, see
// plans/bootstrapping/self-hosted-compiler.md): promote instance
// methods to real top-level defs, and synthesize one dictionary VALUE
// def per instance. Mirrors `collect_infixes`'s own "flat decl_list
// scan, no Scope needed" style (this runs at the same pre-Scope
// codegen-entry-point stage, and has the same acknowledged limitation:
// a Class/Instance buried inside a `scoped_open_d` wrapper isn't found
// either, matching `collect_infixes`'s own existing gap).
//
// No real `Decl.struct_d`/`Decl.inductive_d` declaration is synthesized
// for a "dictionary type" -- confirmed unnecessary: `compile_con_ir`/
// `compile_match_ir` (lang/codegen/emit.mo) work structurally off a
// `Con`'s own name/typ_name/num_args/args and a `MatchCase`'s own
// constructor name, neither needing a registered Inductive/Struct. A
// dictionary value is built directly as `Term.con`; `Con.mk` carries no
// numeric tag field at all -- every dictionary is destructured via
// exactly one match arm (`compile_match_ir` skips tag comparison
// entirely for a single-case match) -- confirmed by direct reading, not
// assumed. (A `dict_tag_placeholder` sentinel constant existed here for
// this doc comment to point at, but was never actually wired to
// anything -- removed as dead code 2026-08-25.)

/// Flat scan for every top-level Class declaration.
#[partial]
def class_from_decl (d : Decl) : Option Class :=
    match d {
        Decl.class_d cls => Option.some cls,
        _ => Option.none,
    }

def collect_classes (decl_list : List Decl) : List Class :=
    List.filter_map class_from_decl decl_list

/// Flat scan for every top-level Instance declaration.
#[partial]
def instance_from_decl (d : Decl) : Option Instance :=
    match d {
        Decl.instance_d ins => Option.some ins,
        _ => Option.none,
    }

def collect_instances (decl_list : List Decl) : List Instance :=
    List.filter_map instance_from_decl decl_list

/// The ordered list of method names a class declares -- load-bearing:
/// this exact order is the dictionary's own field order, used both when
/// BUILDING a dict value here (Phase 2) and when PROJECTING a field
/// back out of one (Phase 4) -- the two must agree, and both derive it
/// from this same function so they can't drift apart.
#[partial]
def class_method_names (cls : Class) : List Identifier :=
    match cls {
        Class.mk _ _ _ methods _ => class_defs_names methods,
    }

#[partial]
def class_defs_names (cds : List ClassDef) : List Identifier :=
    match cds {
        List.empty => List.empty,
        List.cons cd rest =>
            match cd {
                ClassDef.mk name _ _ => List.cons name (class_defs_names rest),
            },
    }

/// Class-name equality, tolerant of the TWO spellings the same class
/// arrives in:
///
///   * the class DECL's own name is ONE joined identifier -- `class
///     Json.Deserializer (D : Type)` is recorded as the single segment
///     `"Json.Deserializer"`, because `Class.name` is an `Identifier` and
///     the elaborated dotted name is `show_name_path`-joined into it
///     (`class_own_name` below re-wraps it the same way);
///   * every REFERENCE to that class is a genuine multi-segment
///     `NamePath` -- `instance Json.Deserializer Bool { ... }`'s head is
///     parsed by `name_path_parser` into `[Json, Deserializer]`.
///
/// `npath_eq` is `name_path_similar` (types.mo), element-wise with
/// `String.beq` per segment, so the two spellings DISAGREE despite
/// `show_name_path` rendering both as `Json.Deserializer`: every dotted
/// class name found zero instances and zero declared signatures, and
/// `lang/src/json.mo`'s `Json.Deserializer.deserialize` calls reported
/// `no instance found` however concrete the carrier (measured: the
/// `filter_instances_by_class` result was empty while the same file's
/// four `Json.Deserializer` instances were right there).
///
/// Render before comparing. `join_identifiers` is `.`-joined and an
/// Identifier cannot contain `.` (see `BOrd Identifier`, types.mo), so
/// equal renders mean the same name and nothing else; a module-qualified
/// spelling (`json::Json.Deserializer`) still renders differently and
/// stays distinct, where a last-segment comparison would coarsen the two
/// apart.
#[partial]
def class_name_eq (a : NamePath) (b : NamePath) : Bool :=
    String.beq (show_name_path a) (show_name_path b)

/// Finds the `Class` an instance's own `cls : NamePath` field names,
/// among a flat `List Class` (`collect_classes`'s output). Every single-
/// segment class in the corpus (`BEq`, `Append`, ...) matches under
/// either spelling, which is why `npath_eq` served here for so long;
/// `class_name_eq` is what the dotted ones (`Json.Deserializer`) need --
/// see its own comment.
#[partial]
def find_class_by_name (classes : List Class) (cls_name : NamePath) : Option Class :=
    match classes {
        List.empty => Option.none,
        List.cons cls rest =>
            match cls {
                Class.mk cname _ _ _ _ =>
                    if class_name_eq (NamePath.npath (List.cons cname List.empty)) cls_name
                    then Option.some cls
                    else find_class_by_name rest cls_name,
            },
    }

/// Finds a method Def in an instance's own body (`Instance.defs`) by
/// bare name (the last segment of the Def's own, possibly-mangled-by-
/// the-parser `ModulePath` name -- instance methods are parsed with
/// their own bare name, e.g. "beq", not yet qualified, confirmed via
/// `instance_method_single`/`instance_method_name`, lang/parser.mo).
#[partial]
def find_instance_method (defs : List Def) (method_name : Identifier) : Option Def :=
    match defs {
        List.empty => Option.none,
        List.cons d rest =>
            match d {
                Def.mk {name := dname, ..} =>
                    if instance_method_name_matches dname method_name
                    then Option.some d
                    else find_instance_method rest method_name,
            },
    }

#[partial]
def instance_method_name_matches (dname : NamePath) (method_name : Identifier) : Bool :=
    match dname {
        NamePath.npath ids =>
            match ids {
                List.cons only_id rest =>
                    match rest {
                        List.empty => Similar.similar only_id method_name,
                        List.cons _ _ => false,
                    },
                List.empty => false,
            },
    }

/// A short, readable (not formally unique-guaranteed for pathological
/// input, but sufficient for this corpus's actual instance args --
/// concrete `Var`s or `App` chains of them, per the corpus-reality-check
/// in plans/bootstrapping/self-hosted-compiler.md) slug for one instance
/// type argument, used by `mangle_instance_method_name` below.
#[partial]
def term_to_slug (t : Term) : String :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => show_identifier id,
                DebugName.unnamed => "T",
            },
        // `String.concat`, not `++` (`Append.append`) chained with a
        // recursive call as the outermost RHS -- same shallow-carrier-
        // inference gap `mangle_instance_method_name` (this function's
        // own caller) hits, see its doc comment.
        Term.app f a => String.concat (String.concat (term_to_slug f) "_") (term_to_slug a),
        _ => "T",
    }

#[partial]
def terms_to_slug (args : List Term) : String :=
    match args {
        List.empty => "",
        List.cons t rest =>
            match rest {
                List.empty => term_to_slug t,
                _ => String.concat (String.concat (term_to_slug t) "_") (terms_to_slug rest),
            },
    }

/// The module an instance was declared in, taken from its own
/// (qualified) name -- `""` when the instance carries no qualifier,
/// which is the case for one synthesized in a test fixture.
#[partial]
def instance_module_prefix (insname : Identifier) : String :=
    let s := show_identifier insname in
    let idx := find_qualifier_sep s 0 (String.length s) in
    if I64.beq idx (0 - 1) then "" else String.slice s 0 idx

#[partial]
def find_qualifier_sep (s : String) (i : I64) (n : I64) : I64 :=
    if I64.gt (i + 2) n then (0 - 1)
    else if String.beq (String.slice s i 2) "::" then i
    else find_qualifier_sep s (i + 1) n

/// Prepend an instance's declaring module to a synthesized name, in the
/// same `module::name` form `lang.codegen.emit`'s `qualified_def_name`
/// uses for source defs.
///
/// Needed because the slug is built from the instance's type ARGS by
/// their bare names: two modules each declaring `instance Show MyType`
/// for their OWN distinct `MyType` both mint `Show_MyType_show`, and
/// one of them is then silently dropped. The class+type pair is only
/// unique per module, not program-wide.
#[partial]
def with_module_prefix (prefix : String) (full : String) : String :=
    if String.is_empty prefix then full else String.concat prefix (String.concat "::" full)

/// The mangled top-level name a promoted instance method gets. A
/// single-segment `ModulePath` (not dotted) -- `filter_reachable_decls`/
/// reachability matching is a string-based walk over already-flat
/// names, so single-segment sidesteps any dot-vs-underscore ambiguity
/// there, the same reasoning `28d98dc`'s infix-resolution pass already
/// established for its own resolved names.
///
/// The name is additionally prefixed with the instance's declaring
/// module (`instance_module_prefix`) -- see `with_module_prefix` for
/// why the class+type pair alone is not unique program-wide.
#[partial]
def mangle_instance_method_name (prefix : String) (cls_name : NamePath) (ins_args : List Term) (method_name : Identifier) : NamePath :=
    let cls_str := show_name_path cls_name in
    let args_str := terms_to_slug ins_args in
    let sep_args := if String.is_empty args_str then "" else "_" ++ args_str in
    // `++` (`Append.append`) chained 3+ deep, with neither operand of
    // the OUTERMOST call a literal/bare-var/constructor once the inner
    // ones are already resolved (both are opaque already-resolved
    // calls), defeats `infer_carrier_from_args`'s shallow, one-level
    // syntactic guess -- same root cause class as `Append_append`
    // (`lang/module.mo`'s `load_file_modules`, fixed via `List.append`
    // instead of `++`) and `2026-08-29-show-show-unresolved-carrier-
    // in-nested-match-arm.md`, but NOT fixed by that fix's env/
    // ctor_owners threading (the args here are already-resolved calls,
    // not bare local vars). `String.concat` is the same idiom already
    // used elsewhere to sidestep this class of gap entirely.
    let full := String.concat (String.concat cls_str sep_args) (String.concat "_" (show_identifier method_name)) in
    NamePath.npath (List.cons (Identifier.id (with_module_prefix prefix full)) List.empty)

/// The mangled top-level name an instance's own dictionary VALUE def
/// gets (distinct from any of its promoted methods' own names above).
#[partial]
def mangle_instance_dict_name (prefix : String) (cls_name : NamePath) (ins_args : List Term) : NamePath :=
    let cls_str := show_name_path cls_name in
    let args_str := terms_to_slug ins_args in
    let sep_args := if String.is_empty args_str then "" else "_" ++ args_str in
    let full := String.concat (String.concat "__Dict_" cls_str) sep_args in
    NamePath.npath (List.cons (Identifier.id (with_module_prefix prefix full)) List.empty)

/// Builds one instance's promoted method Decls (real top-level defs,
/// renamed via `mangle_instance_method_name`) plus its own dictionary
/// VALUE Decl (a `Term.con` whose fields are `Term.var` references to
/// those just-minted methods, in `cls`'s own declared method order --
/// boxed correctly as callable closures by Phase 0's `Term.var`
/// value-position fix, not eager-called). `Option.none` if `defs` is
/// missing a method the class declares (a hard, clean failure -- see
/// this instance's own doc comment on `Instance.defs`, no default-
/// method fallback exists in this corpus today).
#[partial]
def promote_instance (cls : Class) (ins : Instance) : Option (List Decl) :=
    match ins {
        Instance.mk insname cls_name ins_constraints ins_args _ _ defs =>
            let method_names := class_method_names cls in
            let prefix := instance_module_prefix insname in
            match build_dict_fields prefix cls_name ins_args defs method_names {
                Option.some field_terms =>
                    // `ins_constraints` (the instance's own `[Add A]` in
                    // e.g. `instance [Add A] HAdd A A A { ... }`) is
                    // threaded onto EVERY promoted method's own
                    // `Def.constraints` -- a method's `def add := ...`
                    // clause inside the instance body has no `[...]`
                    // clause of its own; the constraint genuinely lives
                    // on the instance, but Phase 3's own
                    // `add_constraint_dict_params` only ever looks at a
                    // Def's own `.constraints` (it can't see the
                    // enclosing Instance at all once promoted to a
                    // flat top-level Def) -- without this, the generic-
                    // instance-forwarding case (this exact HAdd/Add
                    // shape) would never gain the dict param its own
                    // body (`Add.add a b`) needs.
                    let method_decls := promote_methods prefix cls_name ins_args ins_constraints defs method_names in
                    let dict_name := mangle_instance_dict_name prefix cls_name ins_args in
                    let dict_con := Con.mk (Identifier.id "mk") dict_name (List.length field_terms) (options_of field_terms) in
                    let dict_def := Def.mk dict_name (Term.type_ 1) (Term.con dict_con)
                        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private List.empty in
                    Option.some (List.cons (Decl.def_d dict_def) method_decls),
                Option.none => Option.none,
            },
    }

/// One `Decl.def_d` per method in `method_names`, each a renamed copy
/// of the matching entry in `defs` (found by bare name via
/// `find_instance_method`) -- everything but the name is copied
/// unchanged, mirroring how `28d98dc`'s infix-resolution pass and
/// Phase 0's own boxing both leave a Def's own shape otherwise alone.
#[partial]
def promote_methods (prefix : String) (cls_name : NamePath) (ins_args : List Term) (ins_constraints : List TypeConstraint) (defs : List Def) (method_names : List Identifier) : List Decl :=
    match method_names {
        List.empty => List.empty,
        List.cons mname rest =>
            match find_instance_method defs mname {
                Option.some d =>
                    match d {
                        Def.mk {typ, term := term_, constraints := own_constraints, attrs, vis, params, ..} =>
                            let new_name := mangle_instance_method_name prefix cls_name ins_args mname in
                            // `ins_constraints` prepended ahead of the
                            // method's own (usually empty) constraints --
                            // see promote_instance's own doc comment on
                            // why this is here.
                            let all_constraints := List.append ins_constraints own_constraints in
                            let renamed := Def.mk new_name typ term_ all_constraints attrs vis params in
                            List.cons (Decl.def_d renamed) (promote_methods prefix cls_name ins_args ins_constraints defs rest),
                    },
                Option.none => promote_methods prefix cls_name ins_args ins_constraints defs rest,
            },
    }

/// Builds the dict value's own field terms, in `method_names` order --
/// each field is a bare `Term.var` reference (in VALUE position, so
/// Phase 0's `alloc_closure` boxing applies) to that method's own
/// mangled name. `Option.none` (propagated by the caller as a hard
/// failure) the moment any declared method is missing from `defs`.
#[partial]
def build_dict_fields (prefix : String) (cls_name : NamePath) (ins_args : List Term) (defs : List Def) (method_names : List Identifier) : Option (List Term) :=
    match method_names {
        List.empty => Option.some List.empty,
        List.cons mname rest =>
            match find_instance_method defs mname {
                Option.none => Option.none,
                Option.some _ =>
                    match build_dict_fields prefix cls_name ins_args defs rest {
                        Option.none => Option.none,
                        Option.some rest_terms =>
                            let mangled := mangle_instance_method_name prefix cls_name ins_args mname in
                            // Sentinel (`-1`), not `Term.var 0` -- `mangled`
                            // is always a globally-unique mangled name,
                            // NEVER a real local binding at whatever depth
                            // this dict VALUE's own field ends up embedded
                            // at, so this must use the checker/evaluator's
                            // real free-variable convention (see
                            // `build_dict_field_projection_checked`'s own
                            // doc comment for the general rule this
                            // follows) -- confirmed load-bearing via direct
                            // repro: `lang/lower_core_ir.mo`'s own de-Bruijn-
                            // index-driven lowering (unlike codegen's NAME-
                            // driven `compile_db_term_ir`, which tolerates
                            // any index for a `DebugName.named` var) reads
                            // `Term.var 0` here as "the innermost real
                            // local," not a global reference, whenever this
                            // dict value's own body is lowered by
                            // `reflect_type_info!`'s meta-eval
                            // (`lang/typecheck/meta_eval.mo`).
                            let method_ref := Term.var (0 - 1) (DebugName.named (mangled_to_identifier mangled)) in
                            Option.some (List.cons method_ref rest_terms),
                    },
            },
    }

/// A single-segment `ModulePath` (as every `mangle_instance_*_name`
/// above always produces) back down to the bare `Identifier` a
/// `Term.var`'s `DebugName.named` needs.
#[partial]
def mangled_to_identifier (np : NamePath) : Identifier :=
    match np {
        NamePath.npath ids =>
            match ids {
                List.cons only_id rest =>
                    match rest {
                        List.empty => only_id,
                        List.cons _ _ => Identifier.id "__mangle_error",
                    },
                List.empty => Identifier.id "__mangle_error",
            },
    }

#[partial]
def options_of (ts : List Term) : List (Option Term) :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (Option.some t) (options_of rest),
    }

/// Top-level Phase 2 driver: scans `decl_list` for every `Decl.instance_d`,
/// looks up its own class (skipping it, silently, if not found -- a
/// dangling instance with no registered class is out of scope for this
/// pass, same "leave unresolved rather than guess" fallback style used
/// throughout this codebase), and APPENDS its promoted decls
/// (non-destructive -- the original `instance_d` stays in place,
/// ignored by reachability filtering exactly like an infix declaration
/// already is).
#[partial]
def promote_instance_defs (decl_list : List Decl) : List Decl :=
    let classes := collect_classes decl_list in
    let instances := collect_instances decl_list in
    List.append decl_list (promote_all_instances classes instances)

#[partial]
def promote_all_instances (classes : List Class) (instances : List Instance) : List Decl :=
    match instances {
        List.empty => List.empty,
        List.cons ins rest =>
            match ins {
                Instance.mk _ cls_name _ _ _ _ _ =>
                    match find_class_by_name classes cls_name {
                        Option.some cls =>
                            match promote_instance cls ins {
                                Option.some new_decls => List.append new_decls (promote_all_instances classes rest),
                                Option.none => promote_all_instances classes rest,
                            },
                        Option.none => promote_all_instances classes rest,
                    },
            },
    }

// --- Phase 3 (dictionary-passing plan, see
// plans/bootstrapping/self-hosted-compiler.md): a constrained def whose
// body actually references a single-var class constraint gains one
// leading dictionary parameter for it (a new outer Term.pi on .typ and
// a matching outer Term.lam on .term). Mirrors the Rust reference's
// `elaborate_constrained_type` (core_check_module.rs), done here as a
// plain structural AST rewrite (not through the real bidirectional type
// checker, which the `compile` pipeline never runs at all -- confirmed
// while investigating this plan's own Phase 0/1). A def's `.typ`/
// `.term` don't encode a `[Constraint]` as a real Pi/Lam the way the
// Rust reference's elaborated term does (`TypeConstraint` is separate
// metadata on `Def.constraints`) -- this pass is what closes that gap,
// specifically for codegen's own purposes.
//
// The new dict parameter's own `typ` annotation is never actually
// consulted by codegen (confirmed: every param is compiled as a plain
// boxed i64 regardless of its declared type, `build_llvm_params_db`) --
// it's a documentation-only placeholder (`dict_param_type_placeholder`),
// not load-bearing.

/// Only constraints with exactly one bound var (`[Show A]`, not
/// `[Convert A B]`-shaped multi-var constraints, which have no real
/// corpus need today -- see this plan's own corpus-reality-check) AND
/// whose class is genuinely referenced in the def's own body qualify --
/// skips a phantom/unused constraint rather than adding a dead
/// parameter every caller would still need to supply.
#[partial]
def qualifying_dict_constraints (constraints : List TypeConstraint) (body : Term) : List TypeConstraint :=
    match constraints {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                TypeConstraint.mk cls vars =>
                    let single_var := match vars { List.cons _ v_rest => match v_rest { List.empty => true, List.cons _ _ => false, }, List.empty => false, } in
                    if single_var && def_references_class (show_name_path cls) body
                    then List.cons c (qualifying_dict_constraints rest body)
                    else qualifying_dict_constraints rest body,
            },
    }

/// Syntactic scan for any `Term.var` whose own name is a dotted
/// reference into `cls_str` (e.g. `"Show.show"` for `cls_str = "Show"`)
/// anywhere inside `t` -- deliberately conservative/best-effort, not a
/// fully exhaustive walk of every `Term`/`Literal` shape (e.g. a class
/// reference buried inside a `quote_`'d term's own nested structure
/// beyond one level, or an exotic native-arg shape, could in principle
/// be missed) -- matching this codebase's "approximate, don't guess"
/// fallback style elsewhere: missing a real reference here means a
/// constrained def doesn't get a dict param it needed, which surfaces
/// as a clean link-time "undefined symbol" failure later (the class
/// method reference stays unresolved), not a silent miscompile.
#[partial]
def def_references_class (cls_str : String) (t : Term) : Bool :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => String.starts_with (cls_str ++ ".") (show_identifier id),
                DebugName.unnamed => false,
            },
        Term.lam _ typ body => def_references_class cls_str typ || def_references_class cls_str body,
        Term.forall _ kind body => def_references_class cls_str kind || def_references_class cls_str body,
        Term.pi arg ret => def_references_class cls_str arg || def_references_class cls_str ret,
        Term.app f a => def_references_class cls_str f || def_references_class cls_str a,
        Term.lit v => literal_references_class cls_str v,
        Term.con c =>
            match c { Con.mk _ _ _ args => opt_terms_reference_class cls_str args },
        Term.ntv n =>
            match n { Native.mk _ _ args => opt_terms_reference_class cls_str args },
        Term.type_ _ => false,
        Term.hole => false,
        Term.quote_ inner => def_references_class cls_str inner,
        Term.ctx _loc inner => def_references_class cls_str inner,
    }

#[partial]
def literal_references_class (cls_str : String) (l : Literal) : Bool :=
    match l {
        Literal.str _ => false,
        Literal.char _ => false,
        Literal.num _ _ => false,
        Literal.flt _ _ => false,
        Literal.if_ a b c => def_references_class cls_str a || def_references_class cls_str b || def_references_class cls_str c,
        Literal.match_ scrut cases => def_references_class cls_str scrut || match_cases_reference_class cls_str cases,
        Literal.struct_lit fields _ => struct_fields_reference_class cls_str fields,
        Literal.struct_update base fields => def_references_class cls_str base || struct_fields_reference_class cls_str fields,
    }

#[partial]
def match_cases_reference_class (cls_str : String) (cases : List MatchCase) : Bool :=
    match cases {
        List.empty => false,
        List.cons c rest =>
            match c { MatchCase.mc _ _ body _ => def_references_class cls_str body || match_cases_reference_class cls_str rest },
    }

#[partial]
def struct_fields_reference_class (cls_str : String) (fields : List StructLitField) : Bool :=
    match fields {
        List.empty => false,
        List.cons f rest =>
            match f { StructLitField.mk _ value => def_references_class cls_str value || struct_fields_reference_class cls_str rest },
    }

#[partial]
def opt_terms_reference_class (cls_str : String) (args : List (Option Term)) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            match a {
                Option.some t => def_references_class cls_str t || opt_terms_reference_class cls_str rest,
                Option.none => opt_terms_reference_class cls_str rest,
            },
    }

/// The dictionary parameter's own `typ` annotation -- genuinely non-load-
/// bearing: codegen never consults it (every param compiles as a plain
/// boxed i64 regardless of its declared type, `build_llvm_params_db`),
/// and the checker treats it as an unknown type. This MUST be `Term.hole`
/// (which `type_check` always succeeds on, returning `expected_type`)
/// rather than a bound `Term.var 0`: `check_def_with_scope` checks a def's
/// body against `Term.hole`, so `type_check_lam`'s non-`pi` branch
/// (`lang.typecheck.infer`) re-checks each lambda's OWN written param
/// type against the current `local_types` stack -- and the outermost
/// dict lambda is checked with that stack EMPTY, so a `Term.var 0`
/// placeholder reported a spurious out-of-range `bound_var` for the one
/// real corpus case: a promoted instance method that both carries a
/// constraint and forwards to that constraint's own class method
/// (`instance [Add A] HAdd A A A`'s own `add` -> `Add.add a b`, the
/// `HAdd_A_A_A_add` self-hosted-check gap). The dict parameter's binding
/// NAME -- load-bearing for Phase 4's D5 forwarding -- is separate
/// (`dict_param_name` below); this annotation never participates in
/// resolution. `Term.hole` mirrors the Rust reference's own dictionary /
/// projected-method placeholder (`CoreTerm::Hole`, `core_check_module`).
def dict_param_type_placeholder (_c : TypeConstraint) : Term :=
    Term.hole

/// One dict param per qualifying constraint, prepended in constraint-
/// list order (the first constraint becomes the first/outermost new
/// parameter) -- both `.typ` (a new leading Pi) and `.term` (a matching
/// new leading Lam) grow together, keeping the def's own arity/param-
/// count agreement intact.
#[partial]
def prepend_dict_pis (constraints : List TypeConstraint) (typ : Term) : Term :=
    match constraints {
        List.empty => typ,
        List.cons c rest => Term.pi (dict_param_type_placeholder c) (prepend_dict_pis rest typ),
    }

#[partial]
def prepend_dict_lams (constraints : List TypeConstraint) (term_ : Term) : Term :=
    match constraints {
        List.empty => term_,
        List.cons c rest =>
            match c {
                TypeConstraint.mk cls _ =>
                    let dbg := DebugName.named (Identifier.id (dict_param_name cls)) in
                    Term.lam dbg (dict_param_type_placeholder c) (prepend_dict_lams rest term_),
            },
    }

/// The bound NAME a dict parameter gets in the term (distinct from its
/// TYPE placeholder above, though built from the same class name) --
/// Phase 4's own D5 (genuine-polymorphism) resolution reads this same
/// name back out of its threaded environment to forward an already-
/// bound dict to a nested call, so the naming scheme here is load-
/// bearing for that phase, not just cosmetic.
#[partial]
def dict_param_name (cls : NamePath) : String :=
    "__dict_" ++ show_name_path cls

/// Adds one leading dictionary parameter per qualifying constraint (see
/// `qualifying_dict_constraints`) to a single Def. A no-op (returns `d`
/// unchanged) when no constraint qualifies -- the overwhelmingly common
/// case (an ordinary, unconstrained def).
#[partial]
def add_constraint_dict_params (d : Def) : Def :=
    match d {
        Def.mk {name, typ, term := term_, constraints, attrs, vis, params, ..} =>
            let qualifying := qualifying_dict_constraints constraints term_ in
            match qualifying {
                List.empty => d,
                List.cons _ _ =>
                    let new_typ := prepend_dict_pis qualifying typ in
                    let new_term := prepend_dict_lams qualifying term_ in
                    Def.mk name new_typ new_term constraints attrs vis params,
            },
    }

/// Applies `add_constraint_dict_params` to every `Decl.def_d` in a flat
/// decl list -- other decl kinds pass through unchanged (an instance's
/// own promoted methods, from Phase 2, are ordinary concrete defs with
/// no constraints of their own to add a param for -- except the one
/// real corpus case, `instance [Add A] HAdd A A A`'s own `add` method,
/// which DOES carry the instance's own `[Add A]` constraint through to
/// its promoted Def -- `promote_methods`, Phase 2, copies `constraints`
/// from the original method Def unchanged, so this pass reaches it the
/// same as any other constrained def).
#[partial]
def add_constraint_dict_params_decls (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_ => List.cons (Decl.def_d (add_constraint_dict_params def_)) (add_constraint_dict_params_decls rest),
                _ => List.cons d (add_constraint_dict_params_decls rest),
            },
    }

// --- Phase 4 (D4/D5, dictionary-passing plan, see
// plans/bootstrapping/self-hosted-compiler.md): the core resolution
// pass. At every class-method-shaped call site (`Class.method arg1
// ...`), either (D4) rewrites it into a direct call to the resolved
// concrete instance's own promoted method -- recursively supplying any
// dict ARGUMENT that method's own constraints require (the ONE real
// corpus case, `[Add A] HAdd A A A`'s own `add` forwarding to
// `Add.add`, needs exactly this: `HAdd.add 2 3` becomes a direct call
// to the promoted `HAdd`-instance's own `add`, with `Add I64`'s dict
// VALUE spliced in as its own leading arg) -- or (D5) rewrites it into
// a field projection on an already-bound dict parameter, when we're
// inside a still-polymorphic function that itself received this exact
// dictionary (Phase 3's own added parameter) and the carrier type is
// the function's own abstract type variable, not a concrete type at
// all. D5 is checked FIRST when a bound dict for the class exists in
// scope -- inside a generic body, a class-method call on the body's own
// type parameter should always use ITS OWN dict parameter, not attempt
// (impossible, since the type is abstract here) a fresh concrete
// lookup; this ordering sidesteps needing to disambiguate "concrete
// carrier that happens to shadow an outer bound dict" cases which have
// no real corpus need today.

/// One local variable's own declared type, as literally written at its
/// binding site (a `Term.lam`'s own `typ` field) -- threaded down
/// through the walk so a later reference to that variable can recover
/// its type for carrier inference.
pub type LocalTypeBinding {
    mk (var_id : Identifier) (declared_type : Term),
}

/// One already-bound dictionary parameter currently in scope, keyed by
/// its own class -- threaded down the same way, extended whenever the
/// walk descends into one of Phase 3's own dict-binding `Term.lam`s
/// (recognized by `dict_param_name`'s own naming scheme).
pub type DictBinding {
    mk (cls : NamePath) (dict_id : Identifier),
}

/// One 0-arg constructor's own owning inductive type -- e.g. `true`/
/// `false` both owned by `Bool` -- needed for carrier inference on a
/// bare constructor reference like `true` in `true == false`.
pub type CtorOwner {
    mk (ctor_name : Identifier) (owner : NamePath),
}

/// One top-level `def`'s own declared `.typ`, verbatim -- lets
/// `infer_carrier_type`'s `Term.app` arm (below) recover a carrier from
/// the DECLARED return type of a called function, when the operand is
/// itself a computed call (`I64.to_string x`) rather than a literal/
/// bare-var/constructor -- exactly the shape the self-hosted test
/// driver's own synthesized summary line produces
/// (`lang/codegen/test_driver.mo`'s `synthesize_test_driver_source`),
/// and the root cause of the `Append_append` self-compile bug this
/// table exists to close. Deliberately reads `Def.typ` directly from the
/// decl list rather than going through `scope_resolve_name`: `ScopeData`
/// registers every def's own `ScopeDef.sig` as `Term.hole`
/// unconditionally (`build_scope_def`'s own doc comment -- a load-
/// bearing sentinel for dozens of other call sites, not something to
/// change) -- confirmed via direct debugging that this is genuinely why
/// `lang.typecheck.infer`'s own type-checker-based dictionary resolution
/// (Stage 2 of `bootstrapping/unify-check-compile-test-elaboration.md`)
/// can't recover a real return type for an ordinary function call in
/// pure-infer mode. This syntactic pass, unlike the type checker, reads
/// straight from the parsed decl list and isn't affected by that gap.
pub type DefTypeEntry {
    mk (name : NamePath) (typ : Term),
}

/// The table `lookup_def_type` reads, built ONCE per
/// `resolve_class_calls_decls` rather than scanned per call site.
///
/// This was a `List DefTypeEntry` walked linearly, and `lookup_def_type`
/// fires on every `Term.app` node in the whole decl graph -- so at
/// self-compile scale (4,020 defs) it was ~4,020 steps per application
/// node, each step rendering a `ModulePath` via `show_module_path`.
/// Measured: `resolve_class_calls_decls` was 424646ms of a 953084ms
/// self-compile (45%), against 81ms of 2399ms (3.4%) for
/// `examples/hello.mo`'s 349 defs -- a 5242x blow-up for an 11.5x input.
/// Same disease and same cure as `filter_reachable_decls` (AGENTS.md,
/// `2026-08-29-filter-reachable-perf.md`): index it.
///
/// **Keyed under BOTH forms, first-wins, to preserve the linear scan's
/// exact answer.** The scan matched an entry when its full dotted name
/// equalled the query OR its bare last segment did (see
/// `lookup_def_type`'s own doc comment for why both are needed), and
/// returned the FIRST such entry in decl order. Inserting each entry
/// under both keys, earlier entries winning, reproduces that exactly: if
/// entry 5 matches by last segment and entry 50 by full name, key
/// "foo" still resolves to entry 5, as the scan did. Both predicates are
/// plain string equality -- `Similar.similar` on `Identifier` is
/// `String.beq` of the two strings (`lang/types.mo`), and
/// `show_identifier` is a pass-through -- so no comparison semantics
/// change, only how many times they run.
#[partial]
def collect_def_types (decl_list : List Decl) : HashMap String Term :=
    collect_def_types_go decl_list str_map_empty

/// First-wins insert: an existing key is left alone, matching the scan's
/// "first entry in decl order that matches" semantics. `str_map_insert`
/// on its own REPLACES, which would give last-wins.
#[partial]
def def_type_insert_first (key : String) (typ : Term) (m : HashMap String Term) : HashMap String Term :=
    match str_map_lookup key m {
        Option.some _ => m,
        Option.none => str_map_insert key typ m,
    }

#[partial]
def collect_def_types_go (decl_list : List Decl) (acc : HashMap String Term) : HashMap String Term :=
    match decl_list {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk {name := dname, typ := dtyp, ..} =>
                            let with_full : HashMap String Term :=
                                def_type_insert_first (show_name_path dname) dtyp acc in
                            let with_last : HashMap String Term :=
                                def_type_insert_first (show_identifier (last_segment dname)) dtyp with_full in
                            collect_def_types_go rest with_last,
                    },
                _ => collect_def_types_go rest acc,
            },
    }

/// `ename`'s own `last_segment` used to be the ONLY comparison against
/// `name` -- correct for an UNQUALIFIED call site (`open IO {println};
/// println "x"`, `name = "println"`, matching `IO.println`'s own
/// registered entry via its bare last segment,
/// `test_lookup_def_type_finds_dotted_own_name_def_by_bare_query`'s own
/// coverage) but WRONG for a QUALIFIED one (`String.length a`, `name =
/// "String.length"` -- the call site's own full dotted text, per
/// `show_identifier`'s trivial pass-through -- never matches `ename`'s
/// bare last segment `"length"`), so `infer_carrier_type`'s `Term.app`
/// case (looking up a called def's own declared return type to infer a
/// class-method carrier from it, e.g. `String.length a - String.length
/// b`'s own `Sub.sub`/`HAdd.add`) silently never fired for any QUALIFIED
/// dotted call -- confirmed via `bootstrap compile cli/src/main.mo monad`:
/// `lang/parser.mo`'s `string_find_last` hit exactly this
/// (`String.length haystack - String.length needle`). Try the FULL
/// dotted text first (`show_module_path`/`show_identifier`, both
/// "."-joined, matching surface syntax -- covers the qualified case),
/// falling back to the existing bare-last-segment match (covers the
/// unqualified case) -- same "try the fully-qualified form first, then
/// the bare form" idiom `lookup_native_any`'s own doc comment already
/// establishes for the identical dotted-vs-bare ambiguity elsewhere in
/// this file.
#[partial]
def lookup_def_type (entries : HashMap String Term) (name : Identifier) : Option Term :=
    str_map_lookup (show_identifier name) entries

/// Strip `n` leading `Term.pi` binders (skipping any leading `Term.forall`
/// binders at each step -- they don't correspond to an applied value
/// argument), returning the final codomain. A promoted, constrained
/// instance method's own declared type can interleave Phase 3's
/// prepended dict-parameter Pis with surviving Foralls, hence re-
/// checking for a leading Forall before every single Pi strip, not just
/// once up front.
#[partial]
def return_type_after_n_args (typ : Term) (n : I64) : Term :=
    if I64.lt n 1 then typ
    else
        match typ {
            Term.forall _ _ body => return_type_after_n_args body n,
            Term.pi _ ret => return_type_after_n_args ret (n - 1),
            _ => typ,
        }

/// Local copy of `lang.typecheck.infer`'s own `type_head_name` -- can't
/// import it: `infer.mo` already `use`s `lang.scope`, so importing back
/// would be a module cycle. Same dodge as this module's other small,
/// deliberately-duplicated helpers.
#[partial]
def type_head_name_local (t : Term) : Option Identifier :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => Option.some id,
                DebugName.unnamed => Option.none,
            },
        Term.app f _ => type_head_name_local f,
        _ => Option.none,
    }

/// One constructor's own declared field types, positionally -- lets a
/// `match p { Ctor a b => ... }` arm recover `a`/`b`'s real types from
/// `Ctor`'s own declared params, the same way `Term.lam` already
/// registers a lambda param's declared type into `env` (see
/// `resolve_class_call_term`'s `Literal.match_` case below). `ctor_name`
/// is the constructor's bare name (`last_segment`), matching
/// `CtorOwner`'s own convention -- `MatchCase.mc`'s own `name` field is
/// bare too, with no type-qualification available structurally at this
/// syntactic pass.
/// `owner` -- the owning inductive's own name path -- is what makes the
/// table usable at all: EVERY `struct`'s own constructor is named `mk`,
/// so a whole-program table holds one `mk` entry per struct in the
/// corpus, and a name-only lookup hands a match arm whichever struct was
/// declared first. See `lookup_ctor_field_types_owned`.
/// `owner_params` -- the OWNING inductive's own declared type-param
/// identifiers (e.g. `[A, B]` for `type Pair A B { pair (fst:A) (snd:B) }`)
/// -- in the same order `field_types` references them. Needed because a
/// generic constructor's own declared field types are the ABSTRACT type
/// params, not any particular use site's concrete instantiation (`Pair
/// String Json`'s `fst`/`snd` are declared `A`/`B` in `Pair`'s own decl,
/// not `String`/`Json`) -- `match_arm_env` below substitutes using the
/// scrutinee's own concrete type args once it has both pieces.
pub type CtorFieldTypes {
    mk (ctor_name : Identifier) (owner : NamePath) (owner_params : List Identifier) (field_types : List Term),
}

#[partial]
def collect_ctor_field_types (decl_list : List Decl) : List CtorFieldTypes :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.inductive_d ind =>
                    match ind {
                        Inductive.mk owner params _ constructors _ _ =>
                            List.append (ctor_field_types_of owner (param_names_of params) constructors) (collect_ctor_field_types rest),
                    },
                Decl.struct_d s => List.append (ctor_field_types_of_struct s) (collect_ctor_field_types rest),
                _ => collect_ctor_field_types rest,
            },
    }

/// A `struct` decl's own single `mk` constructor. `struct` is a distinct
/// decl kind all the way through this pass -- `struct_to_inductive`
/// (`lang/typecheck/meta_reflect.mo`) is what the meta-eval side uses --
/// so a table that read only `Decl.inductive_d` had NO entry for ANY
/// struct. MEASURED on `lang/src/json.mo`: `match p { mk name age => ... }`
/// with `p : Person` fell back to whichever other struct's `mk` the decl
/// order put first (`Param`'s `(Identifier, Term)` fields), so `name`
/// bound as `Identifier` and `Json.Serializer.serialize name` resolved to
/// no instance at all -- an undefined `@Json.Serializer.serialize` in the
/// driver's IR. `Struct` carries no type params of its own (a generic
/// record is a `type` decl), so `owner_params` is empty.
#[partial]
def ctor_field_types_of_struct (s : Struct) : List CtorFieldTypes :=
    match s {
        Struct.mk name fields _attrs _vis =>
            let owner : NamePath := NamePath.npath (List.cons name List.empty) in
            let field_types : List Term := param_types_of (struct_fields_to_params fields) in
            List.cons (CtorFieldTypes.mk (Identifier.id "mk") owner List.empty field_types) List.empty,
    }

#[partial]
def ctor_field_types_of (owner : NamePath) (owner_params : List Identifier) (constructors : List InductConstructor) : List CtorFieldTypes :=
    match constructors {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                InductConstructor.mk cname params _ =>
                    List.cons (CtorFieldTypes.mk (last_segment cname) owner owner_params (param_types_of params)) (ctor_field_types_of owner owner_params rest),
            },
    }

#[partial]
def param_types_of (params : List Param) : List Term :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Param.mk _name typ_ _mult _default _attrs => List.cons typ_ (param_types_of rest),
            },
    }

#[partial]
def param_names_of (params : List Param) : List Identifier :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Param.mk name_ _typ _mult _default _attrs => List.cons name_ (param_names_of rest),
            },
    }

#[partial]
def lookup_ctor_field_types (entries : List CtorFieldTypes) (ctor_name : Identifier) : Option CtorFieldTypes :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                CtorFieldTypes.mk ename _ _ _ =>
                    if Similar.similar ename ctor_name
                    then Option.some e
                    else lookup_ctor_field_types rest ctor_name,
            },
    }

/// `ctor_name`'s entry whose OWNER is `head` -- the scrutinee's own
/// declared type head (`Person` for `match p { mk name age => ... }`,
/// `p : Person`). Needed because every `struct`'s own constructor is
/// named `mk`: the table holds one `mk` entry per struct in the whole
/// program (`Attribute`, `ParseParam`, `ParseMatchCase`, `Person`, ...),
/// and matching on the NAME alone hands the arm whichever struct the
/// decl order put first. Measured on `lang/src/json.mo`: the arm for
/// `Person` picked up `ParseMatchCase`'s fields (`Identifier`, `List
/// Identifier`), so `Json.Serializer.serialize name` derived the carrier
/// `Identifier`, no instance matched it, and the driver's IR kept a
/// reference to a `Json.Serializer.serialize` that was never emitted.
/// Two spellings again: the decl's `owner` is module-stamped
/// (`json.Person`) while the env's own annotation is as written
/// (`Person`), and `last_segment` splits a single joined dotted segment
/// -- so `owner_head_match` compares both renderings.
#[partial]
def lookup_ctor_field_types_owned (entries : List CtorFieldTypes) (ctor_name : Identifier) (head : Identifier) : Option CtorFieldTypes :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                CtorFieldTypes.mk ename owner _ _ =>
                    if Similar.similar ename ctor_name && owner_head_match owner head
                    then Option.some e
                    else lookup_ctor_field_types_owned rest ctor_name head,
            },
    }

/// The decl's `owner` (`json.Person`) against the scrutinee's own
/// annotation (`Person`): equal full renderings first, else equal last
/// segments. `bare_ctor_name` on the head mirrors what `last_segment`
/// does to the owner for a joined `Module.Type` identifier.
#[partial]
def owner_head_match (owner : NamePath) (head : Identifier) : Bool :=
    String.beq (show_name_path owner) (show_identifier head)
        || String.beq (show_identifier (last_segment owner)) (show_identifier (bare_ctor_name head))

/// The entry to use for an arm: the owner-scoped one when the
/// scrutinee's own type is recoverable, else the old name-only first
/// match (a scrutinee this pass cannot type -- a call, a nested match --
/// keeps exactly its previous environment, which is the behavior every
/// currently-passing file depends on).
#[partial]
def lookup_ctor_field_types_for (entries : List CtorFieldTypes) (ctor_name : Identifier) (head : Option Identifier) : Option CtorFieldTypes :=
    match head {
        Option.some id =>
            match lookup_ctor_field_types_owned entries ctor_name id {
                Option.some e => Option.some e,
                Option.none => lookup_ctor_field_types entries ctor_name,
            },
        Option.none => lookup_ctor_field_types entries ctor_name,
    }

/// Position of `id` within `owner_params` (0-indexed), if present --
/// used to find which of the scrutinee's own concrete type args a bare
/// type-param reference in a field type should substitute to.
#[partial]
def index_of_ident (owner_params : List Identifier) (id : Identifier) (i : I64) : Option I64 :=
    match owner_params {
        List.empty => Option.none,
        List.cons p rest =>
            if Similar.similar p id then Option.some i else index_of_ident rest id (i + 1),
    }

#[partial]
def nth_term (ts : List Term) (i : I64) : Option Term :=
    match ts {
        List.empty => Option.none,
        List.cons t rest => if I64.beq i 0 then Option.some t else nth_term rest (i - 1),
    }

/// A field type's own concrete instantiation. Two cases:
/// - The field's declared type is a BARE reference to one of the owning
///   inductive's own type params (`fst : A` in `Pair A B`) -- substitute
///   the scrutinee's own concrete arg at that position (`String` for
///   `fst` on a `Pair String Json` scrutinee). Needed so an ELEMENT
///   field's carrier is the real concrete type, not the abstract param
///   name itself (a bare "A" matches no real instance).
/// - The field's declared type is an APPLICATION whose own head is
///   something OTHER than one of `owner_params` (`left : BTreeMap K V`
///   in `type BTreeMap K V { node ... (left: BTreeMap K V) ... }`,
///   `xs : List A` in a `Cons`-like constructor) -- pass it through
///   UNCHANGED rather than attempting full substitution of its own
///   nested args. Sound because carrier inference only ever needs the
///   HEAD (`infer_carrier_type`'s `type_head_name_local` reduction,
///   downstream of whatever `env` entry this produces) and the head
///   here is ALREADY a concrete type constructor name regardless of
///   what its own type arguments reference -- confirmed load-bearing by
///   `std/map.mo`'s `instance [BOrd K] Map BTreeMap`'s own `lookup`:
///   `match m { BTreeMap.node k v left right _ => ... Map.lookup key
///   left ... }`'s `left`/`right` need exactly this to recover
///   "BTreeMap" as their own recursive `Map.lookup` call's carrier.
/// A field type matching NEITHER shape (an unnamed/anonymous var, the
/// only remaining possibility) yields no substitution, leaving that one
/// pattern var out of `env` -- the existing, safe "no carrier found"
/// outcome.
#[partial]
def subst_field_type (owner_params : List Identifier) (concrete_args : List Term) (field_type : Term) : Option Term :=
    match field_type {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match index_of_ident owner_params id 0 {
                        Option.some i => nth_term concrete_args i,
                        Option.none => Option.some field_type,
                    },
                DebugName.unnamed => Option.none,
            },
        Term.app _ _ => Option.some field_type,
        _ => Option.none,
    }

/// Zip a match arm's own pattern-bound variable names (`MatchCase.args`)
/// against the matched constructor's declared field types, substituting
/// each field's abstract type param for the scrutinee's own concrete
/// arg (`subst_field_type`) -- a field whose substitution doesn't
/// resolve (a non-bare-var field type, e.g. `List A`, or a mismatched
/// arity) is simply left out of `env`, not guessed at.
#[partial]
def extend_env_with_ctor_fields (env : List LocalTypeBinding) (owner_params : List Identifier) (concrete_args : List Term) (arg_names : List Identifier) (field_types : List Term) : List LocalTypeBinding :=
    match arg_names {
        List.empty => env,
        List.cons a arest =>
            match field_types {
                List.empty => env,
                List.cons t trest =>
                    let rest_env := extend_env_with_ctor_fields env owner_params concrete_args arest trest in
                    match subst_field_type owner_params concrete_args t {
                        Option.some concrete_typ => List.cons (LocalTypeBinding.mk a concrete_typ) rest_env,
                        Option.none => rest_env,
                    },
            },
    }

/// The scrutinee's own concrete type ARGS (`[String, Json]` for a
/// scrutinee declared `p : Pair String Json`) -- only recoverable when
/// the scrutinee is itself a bare, already-`env`-registered local
/// (`lookup_local_type`, the SAME lookup `infer_carrier_type`'s
/// `Term.var` branch already uses, just without that branch's own
/// "reduce to head" step, since the whole point here is the type ARGS,
/// not the head). Any other scrutinee shape (a computed call, a nested
/// match, ...) yields `List.empty` -- match arms in that position get
/// no field-type env enrichment, same as before this fix.
#[partial]
def scrutinee_type_spine (env : List LocalTypeBinding) (scrutinee : Term) : Option CallSpine :=
    // Peels. A match scrutinee IS located (`lower_parse.mo`'s
    // `Literal.match_` lowers it with `lower_parse_term`, not `_bare`), so
    // without this every located scrutinee fell to the `Option.none` arm
    // below and match arms silently lost their field-type enrichment --
    // which `Map.insert k v acc`-shaped calls in an arm depend on to find
    // their carrier.
    match term_peel scrutinee {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match lookup_local_type env id {
                        Option.some raw_typ => Option.some (flatten_call_spine raw_typ),
                        Option.none => Option.none,
                    },
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

#[partial]
def scrutinee_type_args (env : List LocalTypeBinding) (scrutinee : Term) : List Term :=
    match scrutinee_type_spine env scrutinee {
        Option.some spine =>
            match spine {
                CallSpine.mk _head args => args,
            },
        Option.none => List.empty,
    }

/// The scrutinee's own declared type HEAD, bare (`Person` for a scrutinee
/// declared `p : Person`) -- what tells one same-named constructor from
/// another in `match_arm_env` below. `Option.none` whenever the
/// scrutinee's type isn't recoverable from `env`, which falls the lookup
/// back to name-only.
#[partial]
def scrutinee_type_head (env : List LocalTypeBinding) (scrutinee : Term) : Option Identifier :=
    match scrutinee_type_spine env scrutinee {
        Option.some spine =>
            match spine {
                CallSpine.mk head _args => term_head_identifier head,
            },
        Option.none => Option.none,
    }

#[partial]
def term_head_identifier (t : Term) : Option Identifier :=
    match term_peel t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => Option.some id,
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

/// `env` for one match arm's own body -- looks up the matched
/// constructor's declared field types (`ctor_field_types`), substitutes
/// each against the scrutinee's own concrete type args
/// (`scrutinee_type_args`), and extends `env` accordingly; falls back to
/// the unchanged `env` when the constructor isn't found (e.g. a name
/// this pass doesn't recognize) -- the existing behavior, not a
/// regression. The entry is chosen by OWNER first (`lookup_ctor_field_types_for`),
/// since `mk` names every struct's constructor.
#[partial]
def match_arm_env (ctor_field_types : List CtorFieldTypes) (env : List LocalTypeBinding) (scrutinee : Term) (case_ : MatchCase) : List LocalTypeBinding :=
    match case_ {
        MatchCase.mc cname cargs _body _fp =>
            match lookup_ctor_field_types_for ctor_field_types cname (scrutinee_type_head env scrutinee) {
                Option.some entry =>
                    match entry {
                        CtorFieldTypes.mk _ _owner owner_params field_types =>
                            let concrete_args := scrutinee_type_args env scrutinee in
                            extend_env_with_ctor_fields env owner_params concrete_args cargs field_types,
                    },
                Option.none => env,
            },
    }

#[partial]
def collect_ctor_owners (decl_list : List Decl) : List CtorOwner :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.inductive_d ind =>
                    match ind {
                        Inductive.mk owner _ _ constructors _ _ =>
                            List.append (ctor_owners_of owner constructors) (collect_ctor_owners rest),
                    },
                Decl.struct_d s => List.append (struct_ctor_owners s) (collect_ctor_owners rest),
                _ => collect_ctor_owners rest,
            },
    }

/// A `struct` decl's own `mk` owner -- same decl-kind blindness as
/// `ctor_field_types_of_struct` above, and the same fix: without it
/// `Person.mk "Alice" 30` in argument position has no owner to resolve a
/// carrier from.
#[partial]
def struct_ctor_owners (s : Struct) : List CtorOwner :=
    match s {
        Struct.mk name _fields _attrs _vis =>
            List.cons (CtorOwner.mk (Identifier.id "mk") (NamePath.npath (List.cons name List.empty))) List.empty,
    }

/// Collects EVERY constructor's owner, not just the 0-arg ones: a
/// carrier must be inferable from a constructor APPLICATION in
/// argument position too (`Foldable.foldl f 0 (some 42)` -- `some`
/// takes a param, so the old params-only-empty filter left it out and
/// the whole `Option` carrier went missing, failing resolution with
/// "no instance found for Foldable.foldl"; confirmed via direct
/// repro, `init/src/foldable_tests.mo`'s `test_foldl_option_some`).
/// Keyed by the ctor's bare name component (`bare_ctor_name` below,
/// which also strips a dotted/`::`-qualified prefix) -- the same shape
/// `lookup_ctor_owner`'s callers pass after normalizing a call-site
/// reference.
#[partial]
def ctor_owners_of (owner : NamePath) (constructors : List InductConstructor) : List CtorOwner :=
    match constructors {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                InductConstructor.mk cname _params _ =>
                    // `last_segment` first: `cname` is a `ModulePath`,
                    // and for a single-segment dotted name ("Option.some")
                    // that split is what isolates "some"; `bare_ctor_name`
                    // then strips any '::' prefix the same segment carries.
                    List.cons (CtorOwner.mk (bare_ctor_name (last_segment cname)) owner) (ctor_owners_of owner rest),
            },
    }

/// The bare component of a possibly-qualified name -- `some`,
/// `Option.some`, `prelude::Option::some` all give `some`. A
/// constructor's OWNER is what a carrier inference needs, and a
/// call-site reference may spell the ctor with any prefix its module
/// chain allows; `lookup_ctor_owner` compares the WHOLE identifier
/// string (`Similar.similar` on `Identifier` is a full `String.beq`),
/// so an unnormalized qualified reference matches nothing. Splits at
/// the last `.` and at the last `::` -- the two joiners this codebase
/// mints (`qualified_def_name_str` uses `::`, source-dotted names
/// like `Option.some` keep their `.`).
#[partial]
def bare_ctor_name (id : Identifier) : Identifier :=
    Identifier.id (text_after_last_sep (show_identifier id) 0 (0 - 1) (0 - 1))

/// Scan for the last separator: `dot`/`colon` track the index AFTER the
/// most recent `.` (single byte) or `::` (two bytes) seen so far,
/// `-1` meaning none. Bytes, not chars -- identifiers are ASCII here
/// by construction (parser-generated or `::`-joined), matching the
/// byte-level `last_dot_index` scan beside it.
///
/// One scanner serves both directions of the split -- `bare_ctor_name`
/// wants what FOLLOWS the last separator, `qualifier_of` what precedes
/// it -- so the recursion returns the INDEX and the two wrappers below
/// cut the string.
#[partial]
def last_separator_cut (s : String) (i : I64) (dot : I64) (colon : I64) : I64 :=
    if i < String.length s then
        match String.get s i {
            Option.some b =>
                if U8.beq b 46u8 then last_separator_cut s (i + 1) (i + 1) colon
                else if U8.beq b 58u8 then
                    // ':' is only a separator as a "::" PAIR -- check the
                    // next byte before claiming it.
                    match String.get s (i + 1) {
                        Option.some b2 =>
                            if U8.beq b2 58u8 then last_separator_cut s (i + 2) dot (i + 2)
                            else last_separator_cut s (i + 1) dot colon,
                        Option.none => finish_separator_cut dot colon,
                    }
                else last_separator_cut s (i + 1) dot colon,
            Option.none => finish_separator_cut dot colon,
        }
    else finish_separator_cut dot colon

#[partial]
def finish_separator_cut (dot : I64) (colon : I64) : I64 :=
    if colon > dot then colon else dot

#[partial]
def text_after_last_sep (s : String) (i : I64) (dot : I64) (colon : I64) : String :=
    let cut := last_separator_cut s i dot colon in
    if cut < 1 then s else String.drop cut s

/// The component BEFORE a possibly-qualified reference's last separator
/// -- `BTreeMap` for `BTreeMap.empty`, `prelude::List` for
/// `prelude::List::empty`, and `Option.none` for a bare `empty` (a
/// reference with no separator carries no qualifier, so there is
/// nothing to check an owner against). Callers that need the single
/// OWNER component rather than the whole prefix run the result through
/// `bare_ctor_name`, exactly as they do with a ctor name.
#[partial]
def qualifier_of (id : Identifier) : Option Identifier :=
    let s := show_identifier id in
    let cut := last_separator_cut s 0 (0 - 1) (0 - 1) in
    if cut < 1 then Option.none
    else
        // `cut` is the index PAST the separator, so the separator's own
        // bytes end at `cut - 1`; a `::` pair is two bytes, and
        // `last_separator_cut` only advances past one when both colons
        // were seen adjacent -- so a ':' at `cut - 2` means the pair.
        let sep_len :=
            if cut < 2 then 1
            else match String.get s (cut - 2) {
                     Option.some b => if U8.beq b 58u8 then 2 else 1,
                     Option.none => 1,
                 } in
        let qlen := cut - sep_len in
        if qlen < 1 then Option.none else Option.some (Identifier.id (String.slice s 0 qlen))

#[partial]
def last_segment (np : NamePath) : Identifier :=
    match np {
        NamePath.npath ids => last_segment_of ids,
    }

#[partial]
def last_segment_of (ids : List Identifier) : Identifier :=
    match ids {
        List.empty => Identifier.id "",
        List.cons only_id rest =>
            match rest {
                // A single remaining segment can itself be a DOTTED name:
                // `def IO.println (...)` parses its own declared name as
                // ONE joined Identifier "IO.println" (`def_to_decl`,
                // `lang/parser.mo`, wraps it as a single-element
                // ModulePath), not two separate ModulePath segments -- so
                // "last list element" alone isn't the same as "last
                // dotted component". Split on the segment's own trailing
                // '.' too (mirroring `class_method_ref`'s identical
                // string-level `method_suffix_of` split for a call-site
                // reference) before returning it. Confirmed as a real
                // gap: `lookup_def_type`'s carrier-inference caller
                // silently failed to find `IO.println`'s declared return
                // type this way (matching bare query "println" against
                // the UNSPLIT "IO.println" and never equal), leaving a
                // do-notation `Monad.bind` call over it unresolved at
                // codegen time (undefined `@Monad_bind` at link time).
                List.empty =>
                    match method_suffix_of (show_identifier only_id) {
                        Option.some suffix => Identifier.id suffix,
                        Option.none => only_id,
                    },
                List.cons _ _ => last_segment_of rest,
            },
    }

#[partial]
def lookup_local_type (env : List LocalTypeBinding) (id : Identifier) : Option Term :=
    match env {
        List.empty => Option.none,
        List.cons b rest =>
            match b {
                LocalTypeBinding.mk bid btyp =>
                    if Similar.similar bid id
                    then Option.some btyp
                    else lookup_local_type rest id,
            },
    }

#[partial]
def lookup_ctor_owner (owners : List CtorOwner) (id : Identifier) : Option NamePath :=
    match owners {
        List.empty => Option.none,
        List.cons o rest =>
            match o {
                CtorOwner.mk cname owner =>
                    if Similar.similar cname id
                    then Option.some owner
                    else lookup_ctor_owner rest id,
            },
    }

/// `lookup_ctor_owner` for a possibly-QUALIFIED reference: when `id`
/// carries a qualifier it names the owner outright, so the lookup must
/// match on both the bare name and that owner before it may fall back
/// to a name-only match (which is all an unqualified `some` can offer).
///
/// Matching the bare name alone is what made
/// `Map.insert "a" 1 BTreeMap.empty` resolve against the class's
/// DEFAULT carrier and crash on a tag mismatch. `empty` names `List`'s
/// first constructor as well as `BTreeMap`'s (`init/src/prelude.mo:313`,
/// `std/src/map.mo:26`), so the name-only lookup answered `List` for a
/// `BTreeMap` value -- a wrong carrier, and never repaired downstream:
/// nothing else in the call revealed `BTreeMap`, so the instance search
/// fell through to `HashMap` and the emitted call became
/// `Map_HashMap_insert(..., alloc_constructor(5, 0))`, a `BTreeMap` tag
/// handed to `HashMap`'s dictionary. Same collision class as the
/// bare-`mk` one `CtorFieldTypes.owner` closed; the qualifier is what
/// distinguishes them.
#[partial]
def lookup_ctor_owner_for (owners : List CtorOwner) (id : Identifier) : Option NamePath :=
    match qualifier_of id {
        Option.some qualifier =>
            match lookup_ctor_owner_owned owners (bare_ctor_name id) qualifier {
                Option.some owner => Option.some owner,
                // The qualifier matched no owner -- still better to try
                // the name alone than to report nothing (a ctor reached
                // through an import alias the owners map spells
                // differently, say).
                Option.none => lookup_ctor_owner owners (bare_ctor_name id),
            },
        Option.none => lookup_ctor_owner owners (bare_ctor_name id),
    }

#[partial]
def lookup_ctor_owner_owned (owners : List CtorOwner) (cname : Identifier) (qualifier : Identifier) : Option NamePath :=
    match owners {
        List.empty => Option.none,
        List.cons o rest =>
            match o {
                CtorOwner.mk oname owner =>
                    if Similar.similar oname cname && owner_head_match owner qualifier
                    then Option.some owner
                    else lookup_ctor_owner_owned rest cname qualifier,
            },
    }

#[partial]
def lookup_dict_binding (dict_env : List DictBinding) (cls_name : NamePath) : Option Identifier :=
    match dict_env {
        List.empty => Option.none,
        List.cons b rest =>
            match b {
                DictBinding.mk bcls bid =>
                    if npath_eq bcls cls_name
                    then Option.some bid
                    else lookup_dict_binding rest cls_name,
            },
    }

/// A concrete type-name `Term` for a numeric literal's own suffix, in
/// the same bare-identifier shape `find_class_by_name`/instance
/// matching already expects (`Term.var _ (DebugName.named (Identifier.id
/// "I64"))`, ...). Unsuffixed literals default to I64 at parse time
/// (verified against the parser's own numeric-literal default).
#[partial]
def numsuffix_carrier_name (suffix : NumSuffix) : String :=
    match suffix {
        NumSuffix.i8 => "I8", NumSuffix.i16 => "I16", NumSuffix.i32 => "I32", NumSuffix.i64 => "I64",
        NumSuffix.u8 => "U8", NumSuffix.u16 => "U16", NumSuffix.u32 => "U32", NumSuffix.u64 => "U64",
        NumSuffix.f32 => "F32", NumSuffix.f64 => "F64",
    }

#[partial]
def carrier_var (name : String) : Term :=
    Term.var 0 (DebugName.named (Identifier.id name))

/// `typ` with its head replaced by the bare `carrier_var` naming it --
/// the same normalization every branch of `infer_carrier_type` does, but
/// keeping the ARGUMENTS the head is applied to (`BTreeMap I64 I64`
/// stays applied: those arguments are the information
/// `method_sig_bindings`/`carrier_bindings` bind a class's own type
/// variables from, and dropping them is what left `Map`'s `[BOrd K]`
/// with nothing to resolve against).
///
/// A qualified head (`map::BTreeMap`) is normalized to its bare spelling
/// the same way the bare-carrier branch already did: an instance's own
/// declared arg is bare, and `Similar.similar` does not see through a
/// qualifier.
#[partial]
def carrier_with_normalized_head (head_name : String) (typ : Term) : Term :=
    match typ {
        Term.app f a => Term.app (carrier_with_normalized_head head_name f) a,
        Term.var _ _ => carrier_var head_name,
        _ => typ,
    }

/// The carrier of a `(value : T)` ASCRIPTION, which the self-hosted
/// parser desugars to the identity function at `T` applied to `value`
/// (`paren_ann_value`, `lang/parser.mo`). `T` is the value's type --
/// WITH its arguments, which is the point (`(List.empty : List I64)`
/// must answer `List I64`, so that `BEq.beq`'s own `A` binds to `I64`).
///
/// The IDENTITY test is what keeps this from swallowing the language's
/// other `app (lam ...) value` shape, an annotated binding (`let x : T :=
/// value in body`, `DoStmt.let_s`): that application's result type is
/// `body`'s, not `T`, so reading `T` for it would hand a call site a
/// carrier its argument does not have.
#[partial]
def ann_lambda_carrier (dbg : DebugName) (typ : Term) (body : Term) : Option Term :=
    match dbg {
        DebugName.named id =>
            match body {
                Term.var _ bdbg =>
                    match bdbg {
                        DebugName.named bid => if Similar.similar id bid then expected_carrier_of typ else Option.none,
                        DebugName.unnamed => Option.none,
                    },
                _ => Option.none,
            },
        DebugName.unnamed => Option.none,
    }

/// Narrow, deliberately conservative syntactic carrier-type guesser --
/// see this section's own top doc comment. Returns `Option.none` for
/// any shape not covered below (a nested `App` not a literal/known-
/// constructor/declared-param, an un-annotated bound var, `if`/`match`
/// scrutinees, ...) -- the caller (`resolve_class_call_term`) treats
/// that the same as "no matching instance", failing clean at link time
/// rather than guessing.
#[partial]
def infer_carrier_type (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (t : Term) : Option Term :=
    // Peels. This reads a CALL'S ARGUMENTS, and placement rule R3
    // (`lang/parser/lower_parse.mo`) keeps wrappers out of a spine's HEAD
    // but deliberately puts one on every argument -- so every arm below
    // was dead for located input and every argument returned
    // `Option.none`, i.e. "no carrier", i.e. "no matching instance".
    //
    // That is how `monad compile cli/src/main.mo` -- the default invocation,
    // debug info being on by default -- died at `no instance found for
    // `Append.append``: `"lit" ++ e` offered no carrier, so nothing chose
    // `instance Append String`, the call kept its class-method name, and
    // `validate_no_unresolved_class_calls` reported it. It also cost two
    // reachable defs (the promoted instance method and its dictionary),
    // since an unresolved call names no `Def` the reachability walk can
    // follow.
    //
    // Worth knowing: the `Term.app` arm below was ADDED to fix exactly
    // this bug once before (see its own comment), and the wrapper made it
    // unreachable, reintroducing it. The type-checker cannot cover for
    // this shape -- that arm's comment says so explicitly.
    match term_peel t {
        // `Literal.if_`'s own two branches are the operand shape the
        // self-hosted test driver's own synthesized summary line
        // ACTUALLY produces (`synth_sum_expr`, lang/codegen/test_driver.mo:
        // `(if test_one then 1 else 0) + (if test_two then 1 else 0)`) --
        // `literal_carrier_type` below only covers bare `num`/`str`
        // literals, so an if-expression operand fell through to `None`
        // (the same "no carrier found" outcome as a genuinely
        // uninformative shape), leaving THIS `HAdd.add` call unresolved
        // and, at codegen, naively dot-to-underscore-renamed into an
        // undefined `@HAdd_add` symbol -- confirmed as a real gap via
        // direct repro (`monad test` on a file with 2+ `#[test]` defs).
        // Recurse into both branches -- a well-typed if's THEN and ELSE
        // share the same type, so either one revealing a carrier is
        // sound and sufficient (mirrors `lang.elaborate`'s own `free_vars`
        // walking all three of an if's subterms).
        Term.lit v =>
            match v {
                Literal.if_ _cond then_ else_ =>
                    match infer_carrier_type env ctor_owners def_types ctor_field_types then_ {
                        Option.some c => Option.some c,
                        Option.none => infer_carrier_type env ctor_owners def_types ctor_field_types else_,
                    },
                _ => literal_carrier_type v,
            },
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match lookup_local_type env id {
                        // A local's own DECLARED type is often a fully-
                        // APPLIED type (e.g. `acc : BTreeMap String Json`,
                        // an App chain), not the bare type-constructor
                        // name a class carrier actually is (`BTreeMap`).
                        //
                        // This arm used to collapse that to the bare head,
                        // and had to: `term_matches_carrier` compared an
                        // instance's own bare declared arg structurally,
                        // so a fully-applied carrier NEVER matched a bare
                        // instance arg, and `examples/json.mo`'s
                        // `Map.insert k v acc` (`acc : BTreeMap String
                        // Json`) resolved nothing at all. The applied shape
                        // matches now (the bare-instance-arg-vs-applied-
                        // carrier arm), and collapsing to the head throws
                        // away the only thing that can answer a class's own
                        // PARAMETERS: `instance [BOrd K] Map BTreeMap`'s
                        // `K`/`V` come from `acc`'s `String`/`Json` (via
                        // `method_sig_bindings`), so a bare-head carrier
                        // leaves `[BOrd K]` unresolvable. MEASURED on
                        // `std/src/map_tests.mo`'s `int_map_has_all_keys`
                        // (`Map.lookup k m`, `m : BTreeMap I64 I64`, `k` an
                        // untyped lambda param with nothing to say): carrier
                        // inference contributed only `[<placeholder>;
                        // BTreeMap]`, no binding could be made from the
                        // bare head, and the call died at `no instance
                        // found for `Map.lookup_DICT__T_BTreeMap``.
                        //
                        // The head is still normalized (`carrier_with_
                        // normalized_head`), matching every other branch's
                        // own convention; only the arguments are kept.
                        Option.some typ =>
                            match type_head_name_local typ {
                                Option.some head_name =>
                                    match term_peel typ {
                                        Term.app _ _ => Option.some (carrier_with_normalized_head (show_identifier head_name) typ),
                                        _ => Option.some (carrier_var (show_identifier head_name)),
                                    },
                                Option.none => Option.some typ,
                            },
                        Option.none =>
                            // Normalized (`bare_ctor_name`) and
                            // qualifier-scoped (`lookup_ctor_owner_for`):
                            // a 0-arg ctor reference is often spelled
                            // qualified (`Map.empty`, `BTreeMap.empty`),
                            // and the owners map keys the bare component
                            // (`empty`) -- which every `empty`/`mk`/`map`
                            // ctor in the corpus shares, so the
                            // qualifier has to break the tie. See
                            // `lookup_ctor_owner_for` for the measured
                            // crash the name-only match caused.
                            match lookup_ctor_owner_for ctor_owners id {
                                Option.some owner => Option.some (carrier_var (show_name_path owner)),
                                // Not a ctor either -- a bare 0-arg
                                // DEF reference. The app arm below
                                // already recovers a computed operand's
                                // carrier from the called def's own
                                // DECLARED return type; a 0-arg def has
                                // no app to key on, so do the same
                                // lookup here. The load-bearing case:
                                // `[]` desugars to
                                // `FromListLiteral.empty`, inside-out
                                // resolution rewrites it to the
                                // promoted `FromListLiteral_List_empty`
                                // (whose own declared type -- the
                                // INSTANCE body's concrete `List A`,
                                // not the class's abstract `L A` -- is
                                // what makes the carrier a real
                                // `List`), and the enclosing
                                // `Foldable.foldr f 0 []` then has no
                                // other List-revealing arg to infer
                                // from.
                                Option.none =>
                                    match lookup_def_type def_types id {
                                        Option.some typ =>
                                            match type_head_name_local typ {
                                                Option.some carrier_name => Option.some (carrier_var (show_identifier carrier_name)),
                                                Option.none => Option.none,
                                            },
                                        Option.none => Option.none,
                                    },
                            },
                    },
                DebugName.unnamed => Option.none,
            },
        // A constructed value's own `typ_name` names its owning type
        // directly -- more reliable than the `ctor_owners` name lookup
        // above (which only ever applies to a bare `Term.var` reference
        // to a constructor's own NAME, not an already-built
        // `Term.con` value like this one -- confirmed as a real gap via
        // a genuine crash: a call site passing an already-constructed
        // value (e.g. `show_twice mytrue` where `mytrue` reached this
        // point already as a `Term.con`, not a bare var) resolved NO
        // carrier at all and silently skipped dict-arg insertion,
        // producing a real arity-mismatched call and a runtime segfault).
        Term.con c =>
            match c { Con.mk _ typ_name _ _ => Option.some (carrier_var (show_name_path typ_name)) },
        // A COMPUTED operand (a call, not a literal/bare-var/constructor)
        // -- e.g. `I64.to_string x` inside `I64.to_string x ++ y` -- look
        // up the called function's own DECLARED return type. This is the
        // exact shape the self-hosted test driver's own synthesized
        // summary line produces (`lang/codegen/test_driver.mo`), and the
        // root cause of the `Append_append` self-compile bug: previously
        // this fell through to the wildcard below and failed clean
        // rather than resolving. See `DefTypeEntry`'s own doc comment for
        // why this reads the declared type directly rather than relying
        // on `lang.typecheck.infer`'s own (structurally unable, for this
        // shape) type-checker-based resolution.
        Term.app _ _ =>
            match flatten_call_spine t {
                CallSpine.mk head args =>
                    match head {
                        // `(value : T)` -- the parser's identity-lambda
                        // desugaring of an ascription (`ann_lambda_carrier`
                        // above). Checked BEFORE the def/ctor lookups below
                        // because the head here is a lambda, which none of
                        // them can key on: without this the whole argument
                        // reported no carrier, and `std/src/list_tests2.mo`'s
                        // `BEq.beq ([] : List I64) ([] : List I64)` had
                        // nothing to infer `BEq (List A)`'s own `A := I64`
                        // from (both args are ascribed empties).
                        Term.lam ldbg ltyp lbody => ann_lambda_carrier ldbg ltyp lbody,
                        Term.var _ dbg =>
                            match dbg {
                                DebugName.named id =>
                                    match lookup_def_type def_types id {
                                        Option.some typ =>
                                            // Try the callee's own binders
                                            // first: with an argument that
                                            // reveals a carrier, the
                                            // instantiated return type
                                            // (`List I64`) says strictly more
                                            // than its bare head (`List`) --
                                            // see `instantiate_def_carrier`'s
                                            // own section comment. Falling
                                            // back keeps every call whose
                                            // arguments determine nothing on
                                            // today's behavior verbatim.
                                            match instantiate_def_carrier env ctor_owners def_types ctor_field_types typ args {
                                                Option.some carrier => Option.some carrier,
                                                // Nothing to instantiate -- the callee
                                                // has no type variable at all
                                                // (`get_obj : I64 -> IO Obj`) or its
                                                // arguments reveal none -- so its own
                                                // declared return type IS the answer,
                                                // ARGUMENTS AND ALL: the same applied
                                                // shape the local-variable arm above
                                                // returns, and the same one
                                                // `full_return_carrier` documents.
                                                //
                                                // Collapsing it to the bare head (what
                                                // this arm used to do) throws away
                                                // exactly what the callee-signature
                                                // hint channel needs: a parameter
                                                // shape like `M A` binds `M := IO`
                                                // only against an APPLIED `IO Obj`,
                                                // and against a bare `IO` it binds
                                                // nothing, so `concrete_hint` drops
                                                // the whole parameter hint, the
                                                // enclosing lambda's body expectation
                                                // stays the class's abstract `M B`,
                                                // and every class call inside that
                                                // lambda is left unresolved.
                                                //
                                                // MEASURED: `Monad.bind (get_obj 1)
                                                // (fn o => Monad.bind (f o) (fn r =>
                                                // IO.pure r))` reports `no instance
                                                // found for `Monad.bind`` -- while the
                                                // byte-for-byte same call with
                                                // `IO.pure obj` or `IO.io obj` in that
                                                // argument position resolves. The only
                                                // difference is whether the
                                                // argument's carrier came back applied.
                                                Option.none =>
                                                    let ret_typ : Term := return_type_after_n_args typ (List.length args) in
                                                    match type_head_name_local ret_typ {
                                                        Option.some carrier_name => Option.some (carrier_with_normalized_head (show_identifier carrier_name) ret_typ),
                                                        Option.none => Option.none,
                                                    },
                                            },
                                        // The head isn't a def -- it may be
                                        // a CONSTRUCTOR application
                                        // (`some 42`, `Option.some 42`):
                                        // the ctor's owning inductive IS the
                                        // carrier (`Option`). Both spellings
                                        // normalize via `bare_ctor_name`.
                                        // This is the bare-ctor-in-argument-
                                        // position case: an annotated local
                                        // (`let o : Option I64 := ...`) and
                                        // a `List` literal both already
                                        // resolved, only a bare ctor
                                        // application fell through.
                                        //
                                        // The carrier is the ctor's own
                                        // APPLIED owner (`Option I64`), not
                                        // the bare one, whenever the field
                                        // types can be bound from the
                                        // arguments -- see
                                        // `ctor_app_carrier`'s own doc
                                        // comment for the measured gap the
                                        // bare owner leaves.
                                        Option.none =>
                                            match lookup_ctor_owner_for ctor_owners id {
                                                Option.some owner =>
                                                    Option.some (ctor_app_carrier env ctor_owners def_types ctor_field_types (bare_ctor_name id) owner args),
                                                // Not a def and not a ctor -- so the
                                                // head is a LOCAL: a lambda
                                                // parameter or a `let`-bound
                                                // variable whose declared type
                                                // is in `env`. Its return type
                                                // after `args` is the callee's
                                                // own answer, exactly as for the
                                                // def arm above, and it must be
                                                // kept APPLIED for the same
                                                // reason that arm's fallback
                                                // keeps it applied.
                                                //
                                                // MEASURED (2026-09-21) on
                                                // `std/src/concurrent/combine.mo`'s
                                                // `scoped (f : Scope -> IO A)`:
                                                // the inner `Monad.bind (f s)
                                                // (fn r => ...)` reported `no
                                                // instance found for `Monad.bind``.
                                                // `f s`'s head is the def's own
                                                // parameter, so it is in NEITHER
                                                // `def_types` nor `ctor_owners`,
                                                // and this arm returned
                                                // `Option.none` for the whole
                                                // argument -- leaving the enclosing
                                                // `bind` with no argument-derived
                                                // carrier to resolve `IO` from. The
                                                // other two binds in the same def
                                                // (`scope_new`, `scope_drop s`)
                                                // are named defs and always had
                                                // one, which is why only this
                                                // shape fails and why the
                                                // do-block spelling and the
                                                // hand-written nest fail
                                                // identically.
                                                Option.none =>
                                                    match lookup_local_type env id {
                                                        Option.some local_typ =>
                                                            let ret_typ : Term := return_type_after_n_args local_typ (List.length args) in
                                                            match type_head_name_local ret_typ {
                                                                Option.some head_name => Option.some (carrier_with_normalized_head (show_identifier head_name) ret_typ),
                                                                Option.none => Option.none,
                                                            },
                                                        Option.none => Option.none,
                                                    },
                                            },
                                    },
                                DebugName.unnamed => Option.none,
                            },
                        _ => Option.none,
                    },
            },
        _ => Option.none,
    }

#[partial]
def literal_carrier_type (v : Literal) : Option Term :=
    match v {
        Literal.num _ suffix => Option.some (carrier_var (numsuffix_carrier_name suffix)),
        // A FLOAT literal's carrier comes from its suffix exactly as an
        // integer's does. This arm was missing until the F64 backend
        // landed, and the consequence was the class default: measured on
        // `let s : F64 := 0.1 + 0.2 in ...` and `(5.0 * 2.0) + 0.5 ==
        // 10.5`, both of which resolved `Add`/`BEq` to `I64` and
        // reported "type mismatch: `F64` vs. `I64`". Nothing could have
        // depended on the old outcome -- a float literal in a class-call
        // position was an error before this, not a resolution -- and it
        // only ever changes the carrier of an expression whose own
        // literal says `F32`/`F64` outright. The suffix is read rather
        // than assumed `f64`, so an `F32` literal keeps its own answer.
        Literal.flt _ suffix => Option.some (carrier_var (numsuffix_carrier_name suffix)),
        Literal.str _ => Option.some (carrier_var "String"),
        _ => Option.none,
    }

/// The names an instance's own `args` may match ANYTHING against --
/// both explicit `{A : Type}` binders (`implicit_params`) AND
/// constraint-only binders (`[Add A]` on `instance [Add A] HAdd A A A`,
/// which has no `implicit_params` entry for its own `A` at all).
///
/// A THIRD source reaches `implicit_params` by the time an instance list
/// is matched against: the unquantified type variables of the instance's
/// own args, recovered by `refine_instance_wildcards` -- see the section
/// comment below.
#[partial]
def instance_wildcard_names (ins : Instance) : List Identifier :=
    match ins {
        Instance.mk _ _ constraints _ _ implicit_params _ =>
            List.append (param_names implicit_params) (constraint_vars constraints),
    }

// ─── Unquantified instance type variables ───────────────────────────
//
// `instance Monad (Protocol I I)` (`examples/indexed_monads.mo`) and
// `instance Monad (State S)` (`examples/state_monad.mo`) write a type
// variable in their own args WITHOUT declaring it: no `{I : Type}`
// binder and no `[C I]` constraint, so `implicit_params` and
// `constraints` are both empty and `instance_wildcard_names` names
// nothing at all.
//
// The Rust reference resolves such an instance by SUBSTITUTION -- its
// args are patterns, and a bare name in one is a pattern variable, so
// `Monad (State S)` matches the `State I64` carrier and binds `S :=
// I64`. That is the language's behavior, not a host quirk: both example
// files run their tests on the Rust runner today.
// `term_matches_carrier` instead asks whether the name is in
// `instance_wildcard_names`, and with an empty set the leaf falls to
// `Similar.similar S I64` and fails, leaving the call unresolved
// (`no instance found for `Monad.pure``).
//
// So the unbound names of an instance's args are added to its
// `implicit_params`, which is exactly what they are. The filter matters
// as much as the recovery: `instance Json.Deserializer Bool`,
// `instance BEq (BTreeMap String Json)` and `instance Show Json.Number`
// name real types in the same position, and treating one of those as a
// variable would make its instance match ANY carrier -- a silent
// dispatch to the wrong dictionary, not a resolution failure. A name is
// kept only when it is not the tail of any type the program declares.
//
// Filtering by TAIL (`last_segment_of`) rather than by the whole
// spelling, because the two sides are spelled differently in general:
// a decl's own name can be qualified (`json::Number`, the module-
// qualified spelling `qualify.mo` mints) while a reference to it is
// written `Json.Number` or bare, and `Similar.similar` does not see
// through a qualifier.
//
// Fail-closed by construction: a name this pass cannot prove is a
// variable leaves its instance exactly as concrete as it was before, so
// no instance that resolves today resolves differently.

/// Every type name the program's own decls introduce, as tail segments --
/// the set `filter_unknown_types` rules an instance arg's names against.
/// Classes count: a class name is a real name in this position too, and
/// keeping one out of the variable set is the fail-closed direction.
#[partial]
def declared_type_names (decl_list : List Decl) : List Identifier :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest => List.append (decl_type_names d) (declared_type_names rest),
    }

#[partial]
def decl_type_names (d : Decl) : List Identifier :=
    match d {
        Decl.inductive_d i => match i { Inductive.mk nm _p _t _c _a _v => List.cons (last_segment nm) List.empty },
        Decl.struct_d s => match s { Struct.mk nm _f _a _v => List.cons nm List.empty },
        Decl.class_d c => match c { Class.mk nm _p _c _m _v => List.cons nm List.empty },
        _ => List.empty,
    }

/// The names an instance's own args mention as types: each arg's own
/// bare name when the whole arg IS a name (`A` in `instance Foo A`), plus
/// every name in an application's argument position inside it
/// (`Protocol I I` -> `I`, `BTreeMap K V` -> `K`, `V`). The head of an
/// application is NOT collected -- it names the type being applied, which
/// `declared_type_names` already accounts for.
#[partial]
def instance_arg_free_names (args : List Term) : List Identifier :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            List.append (bare_type_var_name a) (List.append (collect_app_arg_names a) (instance_arg_free_names rest)),
    }

/// `ids` minus every name whose tail segment is one of `known`'s -- see
/// the section comment above.
#[partial]
def filter_unknown_types (ids : List Identifier) (known : List Identifier) : List Identifier :=
    match ids {
        List.empty => List.empty,
        List.cons hd rest =>
            if tail_member hd known
            then filter_unknown_types rest known
            else List.cons hd (filter_unknown_types rest known),
    }

#[partial]
def tail_member (id : Identifier) (known : List Identifier) : Bool :=
    match known {
        List.empty => false,
        List.cons k rest =>
            if String.beq (identifier_tail id) (identifier_tail k)
            then true
            else tail_member id rest,
    }

/// A name's last dotted/colon-separated component (`Json.Number` ->
/// `Number`, `json::Number` -> `Number`), through the same splitting
/// `last_segment_of` already does for a decl's own name-path.
#[partial]
def identifier_tail (id : Identifier) : String :=
    show_identifier (last_segment_of (List.cons id List.empty))

/// One `implicit_params` entry per recovered name -- `{A : Type}`'s own
/// shape (`params_for_names`, `lang/parser.mo`), so everything that reads
/// `implicit_params` sees the same thing it would have seen had the
/// instance spelled its binders out.
#[partial]
def params_of_ids (ids : List Identifier) : List Param :=
    match ids {
        List.empty => List.empty,
        List.cons id rest =>
            List.cons (Param.mk id (Term.type_ 1) Multiplicity.many Option.none List.empty) (params_of_ids rest),
    }

#[partial]
def add_unquantified_instance_vars (known_types : List Identifier) (ins : Instance) : Instance :=
    match ins {
        Instance.mk nm cls constraints args vis implicit_params defs =>
            let extra := params_of_ids (filter_unknown_types (instance_arg_free_names args) known_types) in
            Instance.mk nm cls constraints args vis (List.append implicit_params extra) defs,
    }

#[partial]
def refine_instance_wildcards (known_types : List Identifier) (instances : List Instance) : List Instance :=
    match instances {
        List.empty => List.empty,
        List.cons ins rest =>
            List.cons (add_unquantified_instance_vars known_types ins) (refine_instance_wildcards known_types rest),
    }

#[partial]
def param_names (params : List Param) : List Identifier :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                mk pname _ _ _ _ => List.cons pname (param_names rest),
            },
    }

#[partial]
def constraint_vars (constraints : List TypeConstraint) : List Identifier :=
    match constraints {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                TypeConstraint.mk _ vars => List.append vars (constraint_vars rest),
            },
    }

#[partial]
def id_in_list (id : Identifier) (ids : List Identifier) : Bool :=
    match ids {
        List.empty => false,
        List.cons hd rest => if Similar.similar hd id then true else id_in_list id rest,
    }

/// Whether `t` is one of the class's own type parameters -- the
/// match-anything leaves `term_matches_carrier` is built around. Used to
/// decide whether an APPLIED instance arg stands for its head alone
/// (`Show (List A)`: `A` is the class's parameter, so the arg constrains
/// nothing), as opposed to a genuinely concrete one (`Show (Option I64)`,
/// whose `I64` must not be waved through).
#[partial]
def term_is_wildcard (wildcard_names : List Identifier) (t : Term) : Bool :=
    match term_peel t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => id_in_list id wildcard_names,
                DebugName.unnamed => false,
            },
        _ => false,
    }

/// Structural match between one instance-declared type arg and a
/// concrete carrier, treating any leaf `Var` in `wildcard_names` as a
/// match-anything hole. Handles nested shapes (`Append (List A)`'s own
/// `App (Var "List") (Var "A")` against a carrier `App (Var "List")
/// (Var "I64")`) via ordinary structural recursion.
#[partial]
def term_matches_carrier (wildcard_names : List Identifier) (ins_term : Term) (carrier : Term) : Bool :=
    // Peels BOTH sides. The instance side is R1-bare by construction
    // (`Instance.args` lowers through `lower_parse_term_bare`), but the
    // CARRIER is not always: `class_default_carrier` takes it from a class
    // parameter's `default`, and a param default lowers as a VALUE
    // (`lower_parse_opt` -> `lower_parse_term`), so it is located.
    //
    // Unpeeled, a located carrier fell to the `_ => false` arms below and
    // matched nothing. That broke `class FromListLiteral (L : Type := List)`
    // (`init/prelude.mo`) -- i.e. EVERY list literal and `Map.empty`, since
    // those desugar to `FromListLiteral.cons`/`.empty` and have no argument
    // to infer a carrier from, so the class default is the only source.
    // Surfaced as `no instance found for `FromListLiteral.empty`` the moment
    // located terms reached every path.
    //
    // Peeling at entry also covers the `Term.app` recursion below, whose
    // sub-terms can be wrapped on the carrier side for the same reason.
    match term_peel ins_term {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    if id_in_list id wildcard_names
                    then true
                    else match term_peel carrier {
                        Term.var _ cdbg =>
                            match cdbg {
                                DebugName.named cid => Similar.similar id cid,
                                DebugName.unnamed => false,
                            },
                        // An APPLIED carrier against a BARE instance arg
                        // -- `instance FromListLiteral List` (the head
                        // alone, as `lower_parse_term_bare` lowers it)
                        // meeting the `List (List U8)` `List.flatten`
                        // returns. The instance's arg names the head and
                        // says nothing about the parameters (those are
                        // the class's own wildcards, checked at the top
                        // of this arm), so asking the same question one
                        // level down is exactly right: match the head,
                        // ignore what the carrier applies it to. Without
                        // this arm a bare-head instance can only ever
                        // match a bare-head carrier, so `Show`/`BEq`/
                        // `FromListLiteral` on any APPLIED type report
                        // `no instance found` however concrete the
                        // carrier is (live: `std/src/sha256.mo`'s
                        // `List.flatten [Sha256.unpack_word a, ...]`).
                        Term.app chead _ => term_matches_carrier wildcard_names ins_term chead,
                        _ => false,
                    },
                DebugName.unnamed => false,
            },
        Term.app _ _ =>
            match term_peel carrier {
                Term.app _ _ => spine_matches wildcard_names (flatten_call_spine ins_term) (flatten_call_spine carrier),
                // A BARE carrier against an APPLIED instance arg -- the
                // mirror of the arm above, and the shape the carrier
                // guesser actually produces: `infer_carrier_type`
                // deliberately normalizes to the bare HEAD
                // (`type_head_name_local`, `List I64` -> `List`), because
                // that is all the call site's own arguments reveal. So
                // `instance [Show A] Show (List A)` never matched the
                // carrier of `Show.show [42]`, and every class method on a
                // list literal reported `no instance found` however
                // concrete the list was. The instance arg's own parameters
                // are its class's wildcards (`A` here), which constrain
                // nothing the carrier could answer, so the arg stands for
                // its head alone -- exactly the arm above, one level in.
                // A CONCRETE applied arg (`Show (Option I64)`) is NOT a
                // wildcard and must keep failing here: the bare carrier
                // says nothing about its element type.
                _ =>
                    all_args_are_wildcards wildcard_names (spine_args (flatten_call_spine ins_term))
                        && term_matches_carrier wildcard_names (spine_head (flatten_call_spine ins_term)) carrier,
            },
        _ => Similar.similar ins_term carrier,
    }

#[partial]
def instance_args_match_carrier (ins : Instance) (carrier : Term) : Bool :=
    match ins {
        Instance.mk _ _ _ args _ _ _ =>
            let wildcards := instance_wildcard_names ins in
            all_args_match wildcards args carrier,
    }

#[partial]
def all_args_match (wildcards : List Identifier) (args : List Term) (carrier : Term) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            match rest {
                List.empty => term_matches_carrier wildcards a carrier,
                List.cons _ _ => term_matches_carrier wildcards a carrier && all_args_match wildcards rest carrier,
            },
    }

#[partial]
def instance_is_fully_concrete (ins : Instance) : Bool :=
    match ins {
        Instance.mk _ _ _ args _ _ _ =>
            let wildcards := instance_wildcard_names ins in
            not (any_arg_is_wildcard wildcards args),
    }

#[partial]
def any_arg_is_wildcard (wildcards : List Identifier) (args : List Term) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            (term_contains_wildcard wildcards a) || any_arg_is_wildcard wildcards rest,
    }

#[partial]
def term_contains_wildcard (wildcards : List Identifier) (t : Term) : Bool :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => id_in_list id wildcards,
                DebugName.unnamed => false,
            },
        Term.app f a => term_contains_wildcard wildcards f || term_contains_wildcard wildcards a,
        _ => false,
    }

/// The type-variable bindings a MATCHED instance's own head implies for
/// the call site: walk the instance's declared args against the carrier
/// the call resolved with, recording every position where the instance's
/// arg is one of its own class's wildcards (`instance_wildcard_names` --
/// `A` in `instance [Show A] Show (List A)`) and the carrier has a
/// concrete subterm there (`List I64` binds `A := I64`).
///
/// This is the piece `resolve_dict_arg`'s own doc comment says was
/// missing: the instance's constraint (`[Show A]`) names its WILDCARD,
/// and with no binding the only carrier that resolution had was the
/// whole call-site carrier (`List I64`), which matches the very instance
/// being expanded (`Show (List A)`) -- so the element dict came back as
/// the instance's OWN dictionary (`__Dict_Show_List_A`, a self-
/// reference) and was applied to each element instead of the element
/// instance's (`__Dict_Show_I64`).
///
/// Every arg is walked against the SAME carrier, mirroring
/// `all_args_match`'s own convention: a multi-param class's instance
/// (`instance [Add A] HAdd A A A`) names its wildcard in several
/// positions, all of which the one carrier answers.
#[partial]
def carrier_bindings (wildcards : List Identifier) (ins_args : List Term) (carrier : Term) : List (Pair Identifier Term) :=
    match ins_args {
        List.empty => List.empty,
        List.cons a rest =>
            bind_term_vars wildcards a carrier (carrier_bindings wildcards rest carrier),
    }

/// Record `wildcards`-named leaves of an instance's declared arg `shape`
/// against the concrete `actual` carrier subterm at that position.
/// Structural, mirroring `term_matches_carrier`'s own walk: a bare
/// wildcard leaf binds the whole `actual` subterm, an applied shape
/// descends into the matching applied carrier (so
/// `(List A)` against `List I64` binds `A := I64`), and anything else
/// records nothing -- a non-wildcard leaf (`List` in `instance
/// FromListLiteral List`) constrains no variable of its own.
#[partial]
def bind_term_vars (wildcards : List Identifier) (shape : Term) (actual : Term) (bindings : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match term_peel shape {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    if id_in_list id wildcards
                    then List.cons (Pair.pair id actual) bindings
                    else bindings,
                DebugName.unnamed => bindings,
            },
        Term.app sf sa =>
            match term_peel actual {
                Term.app af aa => bind_term_vars wildcards sf af (bind_term_vars wildcards sa aa bindings),
                _ => bindings,
            },
        _ => bindings,
    }

/// What `id` was bound to by `carrier_bindings`, if anything.
#[partial]
def lookup_binding (bindings : List (Pair Identifier Term)) (id : Identifier) : Option Term :=
    match bindings {
        List.empty => Option.none,
        List.cons b rest =>
            match b {
                Pair.pair bid bterm =>
                    if Similar.similar bid id
                    then Option.some bterm
                    else lookup_binding rest id,
            },
    }

/// The carrier a single constraint's own type VARIABLE is bound to by
/// the matched instance's head -- `[Show A]` with `A := I64`. `Option.
/// none` when no variable this constraint names was bound (the `Map`
/// case: `instance [BOrd K] Map BTreeMap`'s `K` comes from the method's
/// own signature, not from the instance's args), which leaves the caller
/// on the pre-existing whole-carrier order.
#[partial]
def bound_constraint_carrier (bindings : List (Pair Identifier Term)) (vars : List Identifier) : Option Term :=
    match vars {
        List.empty => Option.none,
        List.cons v rest =>
            match lookup_binding bindings v {
                Option.some t => Option.some t,
                Option.none => bound_constraint_carrier bindings rest,
            },
    }

/// The carrier candidate list a constraint resolves its dict against:
/// the bound variable's own concrete type FIRST (that is what the
/// constraint is actually about), then the whole call-site carrier
/// (the pre-existing behavior, kept as the fallback so an instance whose
/// binding doesn't itself have the constrained instance still resolves
/// exactly as it used to).
#[partial]
def constraint_carriers (bindings : List (Pair Identifier Term)) (vars : List Identifier) (carrier : Term) : List Term :=
    match bound_constraint_carrier bindings vars {
        Option.some bound => List.cons bound (List.cons carrier List.empty),
        Option.none => List.cons carrier List.empty,
    }

// ─── Callee-signature instantiation ─────────────────────────────────
//
// `infer_carrier_type`'s `Term.app` arm reduces the called def's own
// DECLARED return type to its bare HEAD (`return_type_after_n_args`
// then `type_head_name_local`) -- all a call site's arguments were
// assumed to be able to justify. That is enough to PICK an instance but
// not enough to say what the instance's own type parameters are: a list
// literal desugars to `FromListLiteral.cons`, whose promoted declared
// type `A -> List A -> List A` reveals `List` and drops the element type
// entirely, so `Show.show [1, 2, 3]` matched `instance [Show A] Show
// (List A)` and then had no `A` to resolve the instance's own `[Show A]`
// dictionary against (see `carrier_bindings`' own doc comment) -- the
// self-referential `__Dict_Show_List_A` applied to each element.
//
// The fix is to instantiate the callee's own binders against the
// carriers its ARGUMENTS reveal, exactly as a type checker would:
// `FromListLiteral.cons`'s `A` meets the literal `1`'s own carrier
// `I64`, and the applied return type becomes `List I64` -- precise
// enough both to match and to bind (`carrier_bindings (List I64)`
// against `(List A)` is what turns `[Show A]` into `__Dict_Show_I64`).
//
// Deliberately conservative in three ways, each of which leaves the
// pre-existing bare-head behavior completely untouched:
//
//   * only Forall-bound names are bindable (`collect_forall_names`), so
//     a monomorphic def's declared type (`I64.add`'s) records nothing
//     and this path is skipped for it;
//   * nothing bound at all (`List.empty` bindings) means `Option.none`,
//     and the caller falls back to today's head reduction verbatim;
//   * an argument whose own carrier is `Option.none` records nothing
//     for its position, so an under-determined call resolves as before.
//
// An APPLIED carrier is a strictly better answer than a bare head
// wherever both are available -- `term_matches_carrier` accepts either
// shape against an applied instance arg (its bare-head mirror arm) --
// so the only dispatches that can move are ones that were resolving
// with a carrier that said strictly less.

/// The names a declared type's own leading `Forall` binders introduce --
/// exactly the set `bind_params_against_args` may bind. `wrap_forall`
/// (`lang/elaborate.mo`) puts every free type variable at the FRONT, so
/// this only ever needs to walk binders, but it keeps walking defensively
/// rather than assuming.
#[partial]
def collect_forall_names (typ : Term) : List Identifier :=
    match term_peel typ {
        Term.forall dbg _ body =>
            match dbg {
                DebugName.named id => List.cons id (collect_forall_names body),
                DebugName.unnamed => collect_forall_names body,
            },
        _ => List.empty,
    }

/// The names a declared type with NO `Forall` binder at all still leaves
/// standing for its own parameters -- the mirror `collect_forall_names`
/// needs for the one shape `elaborate_def` (`lang/elaborate.mo`) never
/// runs on: a promoted INSTANCE METHOD.
///
/// `instance FromListLiteral List { def cons (a : A) (l : List A) : List A }`
/// registers `FromListLiteral_List_cons` with the type `A -> List A -> List A`
/// (`promote_methods` copies the instance method's own `Def` verbatim), and
/// `A` is bound by the instance HEAD, not by the def -- so no Forall is ever
/// added and `collect_forall_names` correctly reports that the def's own
/// type binds nothing. Left at that, the ONE call shape whose whole point
/// is the element type -- `[42]`, `[1, 2, 3]` -- is exactly the one that
/// never gets instantiated: its carrier stays the bare head `List`, the
/// `Show (List A)` instance matches, and its `[Show A]` dictionary has no
/// `A` to resolve against.
///
/// Both halves of the set are load-bearing, and each rules out a real
/// misbinding rather than a hypothetical one:
///
///   * a name must appear as a STANDALONE parameter type (`A` in
///     `A -> List A -> List A`) -- the position a caller's own argument
///     determines directly. A name that only ever appears inside an
///     application (`I64` in `I64.add`'s `I64 -> I64 -> I64`, itself
///     reached here because a concrete type names no free variable either)
///     is a type being NAMED, not a parameter, and binding it would rewrite
///     the return type of every call to that def -- `I64.add x 1` would
///     stop reporting `I64` and start reporting whatever the first
///     argument's own carrier inference said.
///   * a name must ALSO appear as an application's own argument (`A` in
///     `List A`) -- i.e. somewhere a type VARIABLE legitimately stands.
///     Without this, `instance Foo Bar { def m (x : Bar) : Bar }` registers
///     `Bar -> Bar`, whose only name is the very type being dispatched on:
///     binding it would replace a correct carrier with an inferred one.
///
/// No ordinary def is reachable: `elaborate_def` wraps every free type
/// variable in Forall by construction, so `collect_forall_names` is
/// non-empty for it and this set is never consulted (`instantiate_def_carrier`
/// only falls back here when that set is empty).
#[partial]
def collect_free_param_names (typ : Term) : List Identifier :=
    keep_ids_present (collect_bare_param_names typ) (collect_app_arg_names typ)

/// Names standing alone as a Pi chain's own parameter types -- see
/// `collect_free_param_names`.
#[partial]
def collect_bare_param_names (typ : Term) : List Identifier :=
    match term_peel typ {
        Term.forall _ _ body => collect_bare_param_names body,
        Term.pi ptyp ret => List.append (bare_type_var_name ptyp) (collect_bare_param_names ret),
        _ => List.empty,
    }

/// Every name sitting in an application's own argument position anywhere
/// in a type (`A` in `List A`) -- see `collect_free_param_names`.
#[partial]
def collect_app_arg_names (t : Term) : List Identifier :=
    match term_peel t {
        Term.app f a => List.append (bare_type_var_name a) (List.append (collect_app_arg_names f) (collect_app_arg_names a)),
        Term.lam _ _ body => collect_app_arg_names body,
        Term.forall _ _ body => collect_app_arg_names body,
        Term.pi ptyp ret => List.append (collect_app_arg_names ptyp) (collect_app_arg_names ret),
        _ => List.empty,
    }

/// A bare `Term.var` type's own name, if it has one.
#[partial]
def bare_type_var_name (t : Term) : List Identifier :=
    match term_peel t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => List.cons id List.empty,
                DebugName.unnamed => List.empty,
            },
        _ => List.empty,
    }

/// `ids` filtered down to those that also occur in `keep` -- the
/// intersection `collect_free_param_names` needs. (`types.mo`'s own
/// `union_ids`/`id_member` are the union/membership pair; nothing there
/// intersects, and `filter_known` is the difference, not this.)
#[partial]
def keep_ids_present (ids : List Identifier) (keep : List Identifier) : List Identifier :=
    match ids {
        List.cons hd rest =>
            if id_member hd keep
            then List.cons hd (keep_ids_present rest keep)
            else keep_ids_present rest keep,
        List.empty => List.empty,
    }

/// A class's own declared type parameters, as names -- the wildcard set
/// `bind_term_vars`/`concrete_hint` may treat as variables inside that
/// class's own method signatures.
///
/// A class's methods are written in terms of its parameters (`def beq : A
/// -> A -> Bool` for `class [BEq A] BEq A`), so the declaration itself is
/// exactly the set of names in them that stand for a TYPE VARIABLE rather
/// than a type being named -- and it is read off the declaration because
/// shape cannot tell the two apart: `I64 -> I64 -> I64` (`I64.add`) and `A
/// -> A -> Bool` (`BEq.beq`) have the same shape, and a PROMOTED instance
/// method is fully monomorphic -- `number::BEq_I64_beq`, what an infix
/// `==` against an `I64` sibling is rewritten to before this walk even
/// runs (`promote_instance_defs`), has domains that ARE the concrete
/// `I64`, written as a bare name.
///
/// MEASURED, not reasoned: reading the names off the SIGNATURE instead (a
/// union of `collect_bare_param_names`/`collect_app_arg_names`) bound `I64
/// := DefaultValue` while solving `Default.default == 1i64` against the
/// promoted `number::BEq_I64_beq : I64 -> I64 -> Bool`, which turned that
/// call's own first parameter -- concretely `I64` -- into the expected
/// carrier `DefaultValue`: the one carrier no `Default` instance has. (For
/// `A -> A -> Bool` the same union is correct, which is why the class-side
/// branch of the hint channel keeps it; there `A` really is a parameter.)
///
/// An over-inclusive set here is worse than useless, because a name is
/// only ever used to read a sibling argument's carrier into a candidate
/// list the ordinary resolution then tries and rejects on its own
/// (`sig_arg_bindings`, `concrete_hint`): it adds no authority, it just
/// renames the type it was supposed to reveal.
#[partial]
def class_param_names (cls : Class) : List Identifier :=
    match cls {
        Class.mk _name params _constraints _methods _vis => param_names params,
    }

/// The bare names standing as a Pi chain's own parameter types that ALSO
/// occur somewhere else in the same signature -- as an application's
/// argument, or as the signature's own RESULT type.
///
/// This is the set `class_method_var_names` was missing. A class method's
/// own implicit parameters are not all reachable by "argument applied to a
/// class parameter": `class Foldable (T : Type -> Type) { def foldr (f : A
/// -> B -> B) (z : B) (t : T A) : B }` names its element type `A` only
/// inside `T A` (found), but its ACCUMULATOR type `B` stands bare as the
/// second domain and as the result -- and a name no caller-side walk can
/// attribute to a class parameter is still a type variable.
///
/// MEASURED, not reasoned: with `B` outside the set, `Foldable.foldl (fn
/// acc x => acc + x) 0 [1, 2, 3]` could not solve `B` from the `0`
/// argument (`sig_arg_bindings` refuses to bind a name it does not
/// recognize as a variable), so the lambda's own accumulator binder stayed
/// the leaked signature variable `B`; carrier inference then read `B` off
/// `acc`, `B` matched the prelude's wildcard-headed `instance [HAdd A A A]
/// Add A`, and the generated dictionary self-recursed forever
/// (`HAdd_A_A_A_add (__Dict_Add_A ())`) -- the driver died with `-1` while
/// the Rust evaluator ran the same program fine.
///
/// Both guards rule out a real misbinding, the same way
/// `collect_free_param_names`'s own pair does:
///
///   * the name must stand ALONE as a domain (`z : B`), never merely
///     inside a Pi (`f : A -> B -> B` names `A`/`B` but as the SHAPE of a
///     function argument, not as a parameter a single call argument
///     determines).
///   * it must recur somewhere else in the signature (`B -> B`, `: B`) --
///     so a concrete type a class method merely takes (`def parse (s :
///     String) : A`) stays out: it appears once, as a domain, and names a
///     type rather than a variable.
#[partial]
def collect_recurring_domain_names (typ : Term) : List Identifier :=
    keep_ids_present (collect_bare_param_names typ) (List.append (collect_app_arg_names typ) (bare_type_var_name (final_result_type typ)))

/// The type a Pi chain ultimately returns -- the innermost `ret` of a
/// (possibly `Forall`-prefixed) function type. See
/// `collect_recurring_domain_names`.
#[partial]
def final_result_type (typ : Term) : Term :=
    match term_peel typ {
        Term.forall _ _ body => final_result_type body,
        Term.pi _ ret => final_result_type ret,
        _ => term_peel typ,
    }

/// The variable names of a CLASS's own method signature: the class's
/// declared parameters (`class_param_names`) plus every name standing as
/// an argument to one of them -- the method's own implicit parameters --
/// plus the bare domains `collect_recurring_domain_names` recovers.
///
/// A class parameter can itself be a type-level FUNCTION, and its
/// signature's own Pi binds the arguments applied to it:
/// `class Map (M : (K : Type) -> (V : Type) -> Type := HashMap)` declares
/// `empty : M K V`, so `K` and `V` are variables too -- bound by `M`'s
/// declared Pi, not by the parameter list -- and `instance [BOrd K] Map
/// BTreeMap`'s `[BOrd K]` can only be resolved against the call's carrier
/// (a `BTreeMap I64 String` pins `K := I64`) if this set contains `K`.
///
/// MEASURED, not reasoned: with the class's parameters alone, `let m :
/// BTreeMap I64 String := Map.empty` matched its instance (the expected
/// carrier reached it -- the annotated binding's own channel) and then
/// failed with only `M` bound (`..._DICT_M=BTreeMap,_BTreeMap_I64_String`
/// under a temporary diagnostic), i.e. exactly the `[BOrd K]` dict
/// argument the class-side signature is here to answer for.
///
/// Restricted to names applied to a CLASS PARAMETER deliberately, rather
/// than every name in argument position anywhere (`collect_app_arg_names`,
/// the wider half of `collect_free_param_names`): a class-side signature
/// can also mention a concrete type inside an application (`def bar (x :
/// List I64) : A`), and that `I64` names a TYPE, not a variable. The
/// class param's own Pi is what makes its arguments variables.
#[partial]
def class_method_var_names (cls : Class) (sig : Term) : List Identifier :=
    let params := class_param_names cls in
    union_ids (union_ids params (collect_param_app_arg_names params sig)) (collect_recurring_domain_names sig)

/// Every name standing as an argument to an application whose own head
/// chain bottoms out in one of `params` -- see `class_method_var_names`.
#[partial]
def collect_param_app_arg_names (params : List Identifier) (t : Term) : List Identifier :=
    match term_peel t {
        Term.app f a =>
            let here := if app_head_is_param params f then bare_type_var_name a else List.empty in
            union_ids here (union_ids (collect_param_app_arg_names params f) (collect_param_app_arg_names params a)),
        Term.pi p r => union_ids (collect_param_app_arg_names params p) (collect_param_app_arg_names params r),
        Term.forall _ _ body => collect_param_app_arg_names params body,
        Term.lam _ ty body => union_ids (collect_param_app_arg_names params ty) (collect_param_app_arg_names params body),
        _ => List.empty,
    }

/// Does this application head chain bottom out in one of `params`?
#[partial]
def app_head_is_param (params : List Identifier) (t : Term) : Bool :=
    match term_peel t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => id_in_list id params,
                DebugName.unnamed => false,
            },
        Term.app f _ => app_head_is_param params f,
        _ => false,
    }

/// Strip every leading `Term.forall` binder -- the shape a signature's
/// own body has to be in before anything can be matched against a
/// carrier (`term_peel` itself only ever peels `Term.ctx`, so a bare
/// `bind_term_vars` on a `Forall`-wrapped type would match nothing).
#[partial]
def strip_foralls (typ : Term) : Term :=
    match term_peel typ {
        Term.forall _ _ body => strip_foralls body,
        _ => term_peel typ,
    }

/// A class's own declared signature for one of its methods -- `ClassDef.
/// typ` (`M K V` for `Map.empty`, wrapped in the class's own type-param
/// binders by `elaborate_class_def`, `lang/elaborate.mo`). This is the
/// CLASS-SIDE answer to "what shape is this method's carrier", and it
/// says things no call site's arguments can: `Map.empty` has no
/// arguments at all.
#[partial]
def class_method_declared_type (cls : Class) (method_name : Identifier) : Option Term :=
    match cls {
        Class.mk _name _params _constraints methods_ _vis => class_defs_type_of methods_ method_name,
    }

#[partial]
def class_defs_type_of (defs : List ClassDef) (method_name : Identifier) : Option Term :=
    match defs {
        List.empty => Option.none,
        List.cons d rest =>
            match d {
                ClassDef.mk name typ _default =>
                    if Similar.similar name method_name then Option.some typ else class_defs_type_of rest method_name,
            },
    }

/// What a matched instance's CLASS METHOD SIGNATURE binds for the call
/// site -- the one family the instance's own head cannot answer.
///
/// `instance [BOrd K] Map BTreeMap` names `K` NOWHERE in its head (the
/// head argument is the bare constructor `BTreeMap`), so its `[BOrd K]`
/// constraint has nothing to resolve against, and `Map.empty` -- which
/// has no argument of its own either -- stays unresolved even once the
/// call's carrier is known. The call site does know what `K` is: the
/// method's own declared signature (`empty : M K V`, `ClassDef.typ`)
/// matched against the carrier the call resolved with reads it straight
/// off (`BTreeMap I64 String` binds `M := BTreeMap`, `K := I64`,
/// `V := String`).
///
/// Appended AFTER `carrier_bindings`' own result at the call site, and
/// `lookup_binding` is first-match, so a name the instance's head already
/// bound keeps that binding: this only ever ADDS an answer where nothing
/// else had one.
///
/// Only the signature's APPLIED shapes are walked
/// (`carrier_shape_candidates`): `Map.lookup`'s own first parameter is
/// the bare `K`, and a bare wildcard shape "binds" against anything at
/// all -- walking it would record `K := BTreeMap I64 I64`, the whole
/// carrier, which is exactly the answer `constraint_carriers` falls back
/// to when there is no binding to be had. The applied `m : M K V` is
/// what actually says `K := I64`.
#[partial]
def method_sig_bindings (classes : List Class) (cls_name : NamePath) (method_name : Identifier) (carrier : Term) : List (Pair Identifier Term) :=
    match find_class_by_name classes cls_name {
        Option.none => List.empty,
        Option.some cls =>
            match class_method_declared_type cls method_name {
                Option.none => List.empty,
                Option.some typ =>
                    bind_shape_candidates (class_method_var_names cls typ) (carrier_shape_candidates typ) carrier List.empty,
            },
    }

/// The applied shapes inside a declared signature that can describe a
/// CARRIER: every Pi domain that is an application, then the return type
/// if it is one. See `method_sig_bindings` on why a bare domain is
/// skipped.
#[partial]
def carrier_shape_candidates (typ : Term) : List Term :=
    match term_peel typ {
        Term.pi dom ret =>
            let here := match term_peel dom {
                Term.app _ _ => List.cons dom List.empty,
                _ => List.empty,
            } in
            List.append here (carrier_shape_candidates ret),
        Term.forall _ _ body => carrier_shape_candidates body,
        Term.app _ _ => List.cons typ List.empty,
        _ => List.empty,
    }

#[partial]
def bind_shape_candidates (names : List Identifier) (shapes : List Term) (carrier : Term) (acc : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match shapes {
        List.empty => acc,
        List.cons s rest => bind_shape_candidates names rest carrier (bind_term_vars names s carrier acc),
    }

/// Walk a declared signature's Pi chain in lockstep with a call's own
/// argument list, recording what each parameter's declared SHAPE binds
/// against the carrier that argument reveals: `A -> List A -> List A`
/// against `[42]` records `A := I64` at the first Pi, and stops at the
/// end of the (usually shorter) argument list -- so a def applied to
/// fewer arguments than it declares still instantiates everything the
/// written arguments determine.
///
/// The arguments' carriers come from `infer_carrier_type` itself, which
/// is what makes this mutual: an argument that is itself a call has its
/// own signature instantiated first, so `[[1]]` binds `A := List I64`
/// rather than `List`. The recursion is structural on the argument's own
/// subterm, so it terminates.
#[partial]
def bind_params_against_args (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (wildcards : List Identifier) (typ : Term) (args : List Term) (bindings : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match term_peel typ {
        Term.forall _ _ body => bind_params_against_args env ctor_owners def_types ctor_field_types wildcards body args bindings,
        Term.pi ptyp ret =>
            match args {
                List.empty => bindings,
                List.cons a rest =>
                    let inner := match infer_carrier_type env ctor_owners def_types ctor_field_types a {
                        Option.some actual => bind_term_vars wildcards ptyp actual bindings,
                        Option.none => bindings,
                    } in
                    bind_params_against_args env ctor_owners def_types ctor_field_types wildcards ret rest inner,
            },
        _ => bindings,
    }

/// Substitute a binding list throughout a type -- the same walk
/// `lang.typecheck.name_subst`'s `name_subst_term` does (that module
/// isn't reachable from here: `lang.typecheck.infer` imports THIS file,
/// not the reverse), built on the `term_map_children` this file already
/// imports. A bound name is replaced wholesale with the concrete carrier
/// recorded for it, and everything else is ordinary structural
/// recursion -- including `Term.ctx` wrappers, which `term_map_children`
/// rebuilds. Names are matched by string equality (`lookup_binding`'s
/// `Similar.similar`), the same convention `bind_term_vars` records them
/// with.
#[partial]
def subst_carrier_bindings (bindings : List (Pair Identifier Term)) (t : Term) : Term :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match lookup_binding bindings id {
                        Option.some bound => bound,
                        Option.none => t,
                    },
                DebugName.unnamed => t,
            },
        _ => term_map_children (subst_carrier_bindings bindings) t,
    }

/// A called def's declared return type with its own binders instantiated
/// from the call's arguments -- `FromListLiteral.cons` applied to a
/// literal and an empty list yields `List I64`, not `List A`.
///
/// `Option.none` means "this def's arguments determine nothing" (no
/// Forall binders at all, or none of them met a carrier-revealing
/// argument), which is exactly the case the caller's bare-head fallback
/// still handles. Also `Option.none` when the instantiated type's own
/// head isn't a plain name (a `Term.hole`-headed type, say): a carrier
/// nothing can match is worse than the head reduction, which at least
/// says `Option.none` itself and fails clean.
#[partial]
def instantiate_def_carrier (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (typ : Term) (args : List Term) : Option Term :=
    // The def's binders: its own `Forall` names when it has any (every
    // ordinary def -- `elaborate_def` wraps free type variables), and
    // otherwise the names a promoted instance method's forall-free
    // signature still leaves standing (`collect_free_param_names`'s own
    // doc comment: `FromListLiteral_List_cons`'s `A`). The second set is
    // never consulted for a def that has the first, so no def that
    // instantiates today changes behavior here.
    let binders := collect_forall_names typ in
    let wildcards :=
        match binders {
            List.empty => collect_free_param_names typ,
            List.cons _ _ => binders,
        } in
    let bindings := bind_params_against_args env ctor_owners def_types ctor_field_types wildcards typ args List.empty in
    match bindings {
        List.empty => Option.none,
        List.cons _ _ =>
            let substituted := subst_carrier_bindings bindings (return_type_after_n_args typ (List.length args)) in
            match type_head_name_local substituted {
                Option.some _ => Option.some substituted,
                Option.none => Option.none,
            },
    }

/// The carrier of a CONSTRUCTOR APPLICATION -- `some 42`, `Option.some 42`,
/// `FromListLiteral.cons 1 rest`. The ctor's own declared FIELD TYPES are
/// bound positionally against the call's argument carriers, substituted
/// into the owning inductive's declared type parameters, and applied to
/// the owner: `List.cons 42 rest` answers `List I64`, not `List`.
///
/// Why the bare owner isn't enough: a bare carrier says nothing any
/// class's own parameters can be solved from, and the callee-signature
/// hint channel is ALL-OR-NOTHING (`concrete_hint`) -- so one signature
/// variable that only a constructor's field types could bind drops the
/// ENTIRE hint for the call. `Foldable.foldr (fn x acc => x + acc) 0
/// [1, 2, 3]` is exactly that: `foldr`'s element type `A` is said by the
/// literal's own `cons` field types and by nothing else, the lambda
/// argument gets no expected type, its `x` stays abstract, and `HAdd.add`
/// picks the mutually-recursive generic `instance [Add A] HAdd A A A`
/// (init/src/prelude.mo) whose `__Dict_Add_A` self-recurses --
/// `driver exited -1`, measured on `init/src/foldable_tests.mo` and
/// `init/src/foldable_tests_fold.mo`. MEASURED discriminator: the SAME
/// call with an ascription, `... 0 ([1, 2, 3] : List I64)`, already
/// resolved correctly, via `ann_lambda_carrier`'s own `List I64`; this is
/// that same carrier, recovered from the constructor itself instead of
/// from the ascription.
///
/// Falls back to the bare owner in every case that isn't a clean
/// instantiation (unknown ctor, nothing bound, a parameter left
/// unsubstituted), which is today's answer verbatim -- so no call that
/// resolves today resolves differently.
#[partial]
def ctor_app_carrier (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (ctor_name : Identifier) (owner : NamePath) (args : List Term) : Term :=
    let fallback : Term := carrier_var (show_name_path owner) in
    // Owner-scoped: the caller already HAS the ctor's owner
    // (`lookup_ctor_owner`), and `mk` names every struct's own
    // constructor -- a name-only lookup here reads a different struct's
    // fields, the same collision `match_arm_env` had.
    match lookup_ctor_field_types_owned ctor_field_types ctor_name (last_segment owner) {
        Option.none => fallback,
        Option.some entry =>
            match entry {
                CtorFieldTypes.mk _ _ owner_params field_types =>
                    match bind_field_types_against_args env ctor_owners def_types ctor_field_types owner_params field_types args List.empty {
                        List.empty => fallback,
                        List.cons b rest =>
                            let bindings : List (Pair Identifier Term) := List.cons b rest in
                            let applied : Term := apply_carrier_params fallback (carrier_params_of bindings owner_params) in
                            // A parameter the arguments never bound (a
                            // phantom one, or a field type mentioning one
                            // at a position no argument reached) leaves the
                            // carrier half-applied: a wildcard wearing a
                            // concrete head, which is the guess this pass
                            // must not make. The bare owner is at least an
                            // answer it already gave.
                            if type_mentions_any owner_params applied
                            then fallback
                            else applied,
                    },
            },
    }

/// The owning inductive's own declared type parameters as a carrier's
/// ARGUMENTS: each parameter's own name, except where the field types
/// bound it to something concrete (`ctor_app_carrier`'s binding list).
/// A `List Identifier`, not a `Term` -- which is why this cannot be
/// `subst_carrier_bindings` (that substitutes inside a type, and a
/// parameter LIST is not one).
#[partial]
def carrier_params_of (bindings : List (Pair Identifier Term)) (owner_params : List Identifier) : List Term :=
    match owner_params {
        List.empty => List.empty,
        List.cons p rest =>
            match lookup_binding bindings p {
                Option.some bound => List.cons bound (carrier_params_of bindings rest),
                Option.none => List.cons (carrier_var (show_identifier p)) (carrier_params_of bindings rest),
            },
    }


/// Bind a constructor's declared FIELD TYPES positionally against a
/// call's own argument carriers: `List.cons`'s `[A, List A]` against
/// `[42, rest]` records `A := I64`. The same walk
/// `bind_params_against_args` does for a def's Pi chain -- which is
/// exactly the shape a constructor's own fields are NOT: they are the
/// inductive declaration's flat parameter list, already in
/// constructor-argument order. The wildcard set is the OWNER's declared
/// parameters, the only names a field type is written in terms of.
#[partial]
def bind_field_types_against_args (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (owner_params : List Identifier) (field_types : List Term) (args : List Term) (acc : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match field_types {
        List.empty => acc,
        List.cons ft rest =>
            match args {
                List.empty => acc,
                List.cons a arest =>
                    let inner := match infer_carrier_type env ctor_owners def_types ctor_field_types a {
                        Option.some actual => bind_term_vars owner_params ft actual acc,
                        Option.none => acc,
                    } in
                    bind_field_types_against_args env ctor_owners def_types ctor_field_types owner_params rest arest inner,
            },
    }

/// `head` applied to `params`, left to right -- `List` and `[I64]` give
/// `List I64`, the shape a class carrier carries its own arguments in.
#[partial]
def apply_carrier_params (head : Term) (params : List Term) : Term :=
    match params {
        List.empty => head,
        List.cons p rest => apply_carrier_params (Term.app head p) rest,
    }

/// Finds the best-matching instance for `cls_name` against a concrete
/// `carrier` -- fully-concrete candidates preferred over wildcard-
/// matching ones (specificity preference), first-match-wins within each
/// tier (mirrors `first_matching_instance`'s own existing "first match,
/// not exhaustive/best match" precedent). No hard ambiguity error --
/// `Option.none` (fail clean at link time) if nothing matches at all.
#[partial]
def find_matching_instance (instances : List Instance) (cls_name : NamePath) (carrier : Term) : Option Instance :=
    let candidates := filter_instances_by_class instances cls_name in
    let concrete := filter_concrete candidates in
    match first_instance_matching concrete carrier {
        Option.some ins => Option.some ins,
        Option.none =>
            // Third tier: head-concrete before the catch-alls. See
            // `filter_head_concrete` for the catch-all this exists to
            // lose to a specific instance.
            let headed := filter_head_concrete candidates in
            match first_instance_matching headed carrier {
                Option.some ins => Option.some ins,
                Option.none => first_instance_matching candidates carrier,
            },
    }

/// Filters a flat `List Instance` (`collect_instances`'s output) down
/// to those naming `cls_name` -- distinct from `find_instances_by_class`
/// just below, which operates on the `Scope`-registry's own
/// `ScopeInstance` grouping (a different, pre-existing structure this
/// pre-Scope pass has no access to, same reasoning `collect_infixes`'s
/// own doc comment already gives for why this pass can't use `Scope`).
#[partial]
def filter_instances_by_class (instances : List Instance) (cls_name : NamePath) : List Instance :=
    List.filter (fn (ins : Instance) => class_name_eq ins.cls cls_name) instances

#[partial]
def filter_concrete (instances : List Instance) : List Instance :=
    List.filter instance_is_fully_concrete instances

/// The middle specificity tier `find_matching_instance` falls back to
/// before it will consider a catch-all: instances whose every declared
/// arg's own HEAD is concrete -- no wildcard in head position.
///
/// `instance_is_fully_concrete` above is the first tier, and it is not
/// enough on its own: a wildcard at an ARGUMENT position is ordinary
/// genericity (`instance Monad (State S)`, whose `S` the carrier
/// supplies), but a wildcard at the HEAD is a catch-all that matches
/// every carrier whatsoever. `init/src/prelude.mo`'s bridge
/// `instance {I : Type} [IndexedMonad M] Monad (M I I)` is exactly that
/// shape: its own head `M` is unquantified, so `refine_instance_wildcards`
/// adds it to the wildcard set and the arg matches ANY carrier -- even a
/// bare `Unit` (measured). It sits FIRST in the instance list (prelude
/// decls precede every consumer's), so `first_instance_matching`'s
/// first-match-wins picked it over the specific instance the call site
/// meant: the call then resolved to a `Monad` dictionary whose
/// `IndexedMonad M` constraint cannot resolve, and the class-call pass
/// reported `no instance found for `Monad.pure`` in
/// `examples/indexed_monads.mo` and `examples/state_monad.mo` although the
/// right instance was declared in the same file.
#[partial]
def filter_head_concrete (instances : List Instance) : List Instance :=
    List.filter instance_head_is_concrete instances

#[partial]
def instance_head_is_concrete (ins : Instance) : Bool :=
    match ins {
        Instance.mk _ _ _ args _ _ _ =>
            let wildcards := instance_wildcard_names ins in
            not (any_arg_head_is_wildcard wildcards args),
    }

#[partial]
def any_arg_head_is_wildcard (wildcards : List Identifier) (args : List Term) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            term_is_wildcard wildcards (spine_head (flatten_call_spine a)) || any_arg_head_is_wildcard wildcards rest,
    }

#[partial]
def first_instance_matching (instances : List Instance) (carrier : Term) : Option Instance :=
    match instances {
        List.empty => Option.none,
        List.cons ins rest =>
            if instance_args_match_carrier ins carrier
            then Option.some ins
            else first_instance_matching rest carrier,
    }

/// A flat call spine (`f a b c` -> head `f`, args `[a, b, c]`) -- local
/// to this pass (emit.mo's own `AppSpine` isn't reachable from here
/// without a circular module dependency, since emit.mo itself already
/// `use`s this module).
pub type CallSpine {
    mk (head : Term) (args : List Term),
}

// Was `List.append args [a]` per level -- O(arity) per step, O(n^2)
// total for an n-arg call spine (a real, if usually small-in-practice,
// algorithmic smell flagged in the 2026-08-25 review refresh). Fixed by
// prepending onto an accumulator as the recursion unwinds instead:
// since `Term.app f a` peels off its OUTERMOST (last-applied) arg first
// and recurses into `f` (the remaining, earlier applications) before
// this level's own `a` gets consed on, the accumulator naturally ends
// up in left-to-right declared-argument order with no final reverse
// needed -- `f a b c` visits `c` innermost-recursion-first, consing
// `[c]` -> `[b,c]` -> `[a,b,c]`, each step O(1).
#[partial]
def flatten_call_spine (t : Term) : CallSpine :=
    flatten_call_spine_go t List.empty

#[partial]
def flatten_call_spine_go (t : Term) (acc : List Term) : CallSpine :=
    // Peels. A wrapper between two `app`s of a spine would end the flatten
    // early, and the head this returns would be an `app` rather than the
    // `var` `class_method_ref` needs -- so the class call silently fails to
    // resolve and the link fails with `undefined @Monad_bind`. Placement
    // rule R3 keeps wrappers out of head position; this covers the rest.
    match term_peel t {
        Term.app f a => flatten_call_spine_go f (List.cons a acc),
        _ => CallSpine.mk (term_peel t) acc,
    }

#[partial]
def rebuild_call (head : Term) (args : List Term) : Term :=
    match args {
        List.empty => head,
        List.cons a rest => rebuild_call (Term.app head a) rest,
    }

#[partial]
def spine_head (s : CallSpine) : Term := match s { CallSpine.mk h _ => h }

#[partial]
def spine_args (s : CallSpine) : List Term := match s { CallSpine.mk _ a => a }

/// Structural match of two APPLIED shapes, LEFT-ALIGNED over the length
/// they share: heads first (each side's head alone, so the bare-vs-
/// applied head rule the arms below encode keeps working), then the
/// arguments pairwise from the first.
///
/// The two sides routinely have different arities, because an instance's
/// own arg is a PARTIAL application of the carrier's head -- `instance
/// Monad (Protocol I I)` names two of `Protocol`'s three parameters --
/// while the carrier at a call site is fully applied
/// (`Protocol Init Init I64`). Comparing the two chains in lockstep from
/// the OUTSIDE (what the previous `Term.app`/`Term.app` arm did, one
/// level per recursion) pairs the instance's LAST arg against the
/// carrier's outermost one: `Init` against `I64`, always false. The
/// instance could then only ever match through a wildcard at that
/// position, which is why `instance Monad (Protocol Init Init)` -- every
/// argument concrete -- matched nothing at all, and why the prelude's
/// wildcard-headed bridge got the call in `examples/indexed_monads.mo`.
///
/// Arguments the INSTANCE names beyond the carrier's own must all be
/// wildcards (`all_args_are_wildcards` below), which is the pre-existing
/// `instance [Show A] Show (List A)` against a bare `List` case; what the
/// carrier applies the head to BEYOND the instance's own args is not
/// constrained by that instance at all.
#[partial]
def spine_matches (wildcard_names : List Identifier) (i : CallSpine) (c : CallSpine) : Bool :=
    term_matches_carrier wildcard_names (spine_head i) (spine_head c)
        && args_prefix_match wildcard_names (spine_args i) (spine_args c)

#[partial]
def args_prefix_match (wildcard_names : List Identifier) (iargs : List Term) (cargs : List Term) : Bool :=
    match iargs {
        List.empty => true,
        List.cons ia irest =>
            match cargs {
                List.empty => all_args_are_wildcards wildcard_names iargs,
                List.cons ca crest => term_matches_carrier wildcard_names ia ca && args_prefix_match wildcard_names irest crest,
            },
    }

#[partial]
def all_args_are_wildcards (wildcard_names : List Identifier) (args : List Term) : Bool :=
    match args {
        List.empty => true,
        List.cons a rest => term_is_wildcard wildcard_names a && all_args_are_wildcards wildcard_names rest,
    }

/// If `id`'s own text is a dotted reference into a known class
/// (`"Show.show"` for a registered class `Show`), returns that class
/// and the bare method name (`"show"`). `Option.none` for any other
/// var (an ordinary global, a local, an unrelated dotted path).
#[partial]
def class_method_ref (classes : List Class) (id : Identifier) : Option ClassMethodRef :=
    let text := show_identifier id in
    match class_prefix_of text {
        Option.none => Option.none,
        Option.some cls_str =>
            match find_class_by_name classes (NamePath.npath (List.cons (Identifier.id cls_str) List.empty)) {
                Option.none => Option.none,
                Option.some cls =>
                    match method_suffix_of text {
                        Option.none => Option.none,
                        Option.some method_str =>
                            Option.some (ClassMethodRef.mk cls (Identifier.id method_str)),
                    },
            },
    }

pub type ClassMethodRef {
    mk (cls : Class) (method_name : Identifier),
}

#[partial]
def last_dot_index (s : String) (i : I64) (found : I64) : I64 :=
    if i < String.length s then
        match String.get s i {
            Option.some b => if U8.beq b 46u8 then last_dot_index s (i + 1) i else last_dot_index s (i + 1) found,
            Option.none => found,
        }
    else found

#[partial]
def class_prefix_of (s : String) : Option String :=
    let idx := last_dot_index s 0 (0 - 1) in
    if idx < 0 then Option.none else Option.some (String.slice s 0 idx)

#[partial]
def method_suffix_of (s : String) : Option String :=
    let idx := last_dot_index s 0 (0 - 1) in
    if idx < 0 then Option.none else Option.some (String.drop (idx + 1) s)

/// Class name's own `Identifier` -> the `Class`'s own declared name.
#[partial]
def class_own_name (cls : Class) : NamePath :=
    match cls { Class.mk cname _ _ _ _ => NamePath.npath (List.cons cname List.empty) }

#[partial]
def find_matching_instance_any (instances : List Instance) (cls_name : NamePath) (carriers : List Term) : Option Instance :=
    match carriers {
        List.empty => Option.none,
        List.cons c rest =>
            match find_matching_instance instances cls_name c {
                Option.some ins => Option.some ins,
                Option.none => find_matching_instance_any instances cls_name rest,
            },
    }

/// Does the candidate carrier `c` mention any of the matched instance's
/// own wildcard type variables?
///
/// A candidate that does is a GENERIC instantiation of that instance:
/// `instance [BEq A] BEq (Option A)` matched at the candidate `Option A`
/// (which is what `List.get 0 [1, 2, 3]` -- a def-headed application
/// whose declared return still carries the callee's own binder --
/// reports as its carrier) says nothing about what `A` is, so the
/// instance's own `[BEq A]` constraint has no type to resolve against and
/// falls back onto the whole carrier, which re-matches the very instance
/// being expanded -- `__Dict_BEq_Option_A` handed to `__Dict_BEq_Option_A`'s
/// element slot, and unbounded recursion at the first element read. The
/// same candidate matched at `Option I64` (the other operand, `some 1`,
/// whose ctor application does bind its element) mentions no wildcard and
/// resolves the constraint to `__Dict_BEq_I64`.
def carrier_mentions_wildcards (wildcards : List Identifier) (c : Term) : Bool :=
    mentions_any_name (instance_arg_free_names (List.cons c List.empty)) wildcards

def mentions_any_name (names : List Identifier) (wildcards : List Identifier) : Bool :=
    match names {
        List.empty => false,
        List.cons n rest => if id_member n wildcards then true else mentions_any_name rest wildcards,
    }

/// `find_matching_instance_carrier_any`, but preferring a candidate that
/// actually PINS DOWN the matched instance's own type variables -- see
/// `carrier_mentions_wildcards`' own doc comment for what goes wrong when
/// a generic one wins. Falls back to the plain first-match-wins order
/// when EVERY candidate is generic, so a call whose arguments reveal no
/// concrete carrier resolves exactly as it did before this preference
/// existed.
///
/// This is why the fix has to live here and not only in the checker: the
/// checker's own D4 path has no argument carriers at all (`List.empty`
/// for `extra_carriers`), so it can only DEFER on a self-reference (see
/// `typecheck/infer.mo`'s `dict_args_contain_self`), and this pass -- which
/// does have them -- is what then has to pick the concrete one.
#[partial]
def find_concrete_matching_carrier_any (instances : List Instance) (cls_name : NamePath) (carriers : List Term) : Option (Pair Term Instance) :=
    match find_carrier_any_avoiding_wildcards instances cls_name carriers {
        Option.some p => Option.some p,
        Option.none => find_matching_instance_carrier_any instances cls_name carriers,
    }

#[partial]
def find_carrier_any_avoiding_wildcards (instances : List Instance) (cls_name : NamePath) (carriers : List Term) : Option (Pair Term Instance) :=
    match carriers {
        List.empty => Option.none,
        List.cons c rest =>
            match find_matching_instance instances cls_name c {
                Option.none => find_carrier_any_avoiding_wildcards instances cls_name rest,
                Option.some ins =>
                    if carrier_mentions_wildcards (instance_wildcard_names ins) c
                    then find_carrier_any_avoiding_wildcards instances cls_name rest
                    else Option.some (Pair.pair c ins),
            },
    }

/// Sibling of `find_matching_instance_any` that also returns WHICH
/// candidate carrier matched -- needed by `resolve_class_method_call_d4_
/// from_args` (unlike `resolve_dict_arg`'s own use of the `_any` form,
/// which only needs the instance itself; the OUTER call-site dispatch
/// also needs the matched carrier term to hand to `resolve_class_method_
/// call_with_instance`/`_with_dict_args` for THEIR OWN nested-constraint
/// resolution).
#[partial]
def find_matching_instance_carrier_any (instances : List Instance) (cls_name : NamePath) (carriers : List Term) : Option (Pair Term Instance) :=
    match carriers {
        List.empty => Option.none,
        List.cons c rest =>
            match find_matching_instance instances cls_name c {
                Option.some ins => Option.some (Pair.pair c ins),
                Option.none => find_matching_instance_carrier_any instances cls_name rest,
            },
    }

/// `find_matching_instance_carrier_any` for a SPECIFIC (non-catch-all)
/// match only: the first candidate carrier that matches a fully-concrete
/// instance, else the first that matches a head-concrete one. `Option.none`
/// when every candidate only reaches the catch-all tier -- the caller then
/// falls back to the ordinary first-match-wins path, so nothing that
/// resolves today stops resolving.
///
/// This exists for `Monad.pure`, the one class method whose evidence is
/// ALL guesswork: its own argument is the monad's ELEMENT type, never the
/// monad, so the args-derived candidate is a wrong answer rather than a
/// weak one (`pure 0` reveals `I64`), and the enclosing def's declared
/// return type is only the monad for a def that returns the do-block's
/// own type. MEASURED on `examples/state_monad.mo`'s `test_state_pure`
/// (`... := do { ... } == expected`, so `def_carrier` is `Bool`): the
/// `pure` call's REAL evidence -- the projected expectation, `State I64`
/// -- was in the candidate list, but `I64`/`Bool` both matched
/// `init/src/prelude.mo`'s unquantified bridge
/// `instance {I : Type} [IndexedMonad M] Monad (M I I)`, whose wildcard
/// head matches literally any type, so the first candidate's catch-all
/// match won and the call resolved to a dictionary whose `IndexedMonad M`
/// constraint cannot resolve -- `no instance found for `Monad.pure``.
/// Specificity is the only evidence that separates the two, since a
/// catch-all by definition fits every candidate equally well.
#[partial]
def find_specific_matching_carrier (instances : List Instance) (cls_name : NamePath) (carriers : List Term) : Option (Pair Term Instance) :=
    match find_matching_carrier_at_tier instances cls_name carriers 1 {
        Option.some p => Option.some p,
        Option.none => find_matching_carrier_at_tier instances cls_name carriers 2,
    }

#[partial]
def find_matching_carrier_at_tier (instances : List Instance) (cls_name : NamePath) (carriers : List Term) (tier : I64) : Option (Pair Term Instance) :=
    match carriers {
        List.empty => Option.none,
        List.cons c rest =>
            match first_instance_matching (instance_tier_candidates instances cls_name tier) c {
                Option.some ins => Option.some (Pair.pair c ins),
                Option.none => find_matching_carrier_at_tier instances cls_name rest tier,
            },
    }

/// `find_matching_instance`'s tiers as a selectable list, so a search can
/// ask for one tier at a time (the catch-all tier is the full candidate
/// list, exactly as `find_matching_instance`'s own last fallback is).
#[partial]
def instance_tier_candidates (instances : List Instance) (cls_name : NamePath) (tier : I64) : List Instance :=
    let cands := filter_instances_by_class instances cls_name in
    if I64.beq tier 1 then filter_concrete cands
    else if I64.beq tier 2 then filter_head_concrete cands
    else cands

/// Resolves ONE dict argument a promoted method's own constraint
/// needs, given the concrete `carrier` already established at the outer
/// call site. Checks `dict_env` first (D5 forwarding, for completeness/
/// generality), then a fresh D4 lookup against `carrier` itself (the
/// common case: the constraint is on the SAME type variable as the
/// instance's own carrier, e.g. `instance [Show A] Foo A`'s own `A`).
///
/// `extra_carriers` is the fallback for the OTHER real corpus shape:
/// `instance [BOrd K] Map BTreeMap`'s `[BOrd K]` constrains `K` (the
/// map's KEY type), a DIFFERENT type variable than `Map`'s own carrier
/// (`M = BTreeMap`) -- `carrier` alone can never match a `BOrd`
/// instance (there is no `instance BOrd BTreeMap`), so this pass used
/// to give up on `Map.insert`/`Map.lookup`/... entirely (confirmed via
/// `examples/json.mo`'s `pairs_to_map_insert`). `extra_carriers` is the
/// call's own argument carriers (`infer_all_carriers_from_args_go`,
/// computed once per call site from the SAME `resolved_args` this
/// pass's carrier inference already reads) -- for `Map.insert k v acc`,
/// `k`'s own inferred carrier (`String`, once `match_arm_env` below can
/// see it) finds `instance BOrd String` here. Tried only after the
/// primary `carrier` fails, preserving the existing, already-correct
/// behavior for the common same-type-variable case.
#[partial]
def resolve_dict_arg (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (bindings : List (Pair Identifier Term)) (carrier : Term) (extra_carriers : List Term) (c : TypeConstraint) : Option Term :=
    match c {
        TypeConstraint.mk cls_name vars =>
            match lookup_dict_binding dict_env cls_name {
                Option.some bound_id => Option.some (Term.var 0 (DebugName.named bound_id)),
                Option.none =>
                    // The constraint's own type VARIABLE (`[Show A]`'s
                    // `A`), bound by the matched instance's head against
                    // the carrier (`instance [Show A] Show (List A)` with
                    // `A := I64`), is the RIGHT carrier for this dict --
                    // the whole call-site carrier (`List I64`) resolves
                    // straight back to the instance being expanded, which
                    // is how the self-referential `__Dict_Show_List_A`
                    // element dict was born. `constraint_carriers` keeps
                    // the old order (whole carrier, then `extra_carriers`)
                    // as its fallback for a constraint whose variable the
                    // instance head does not bind.
                    let found := match find_matching_instance_any instances cls_name (constraint_carriers bindings vars carrier) {
                        Option.some ins => Option.some ins,
                        Option.none => find_matching_instance_any instances cls_name extra_carriers,
                    } in
                    match found {
                        Option.some ins =>
                            match ins {
                                Instance.mk found_insname _ _ ins_args _ _ _ =>
                                    // Sentinel, not `Term.var 0` -- a
                                    // mangled dict-VALUE name is never a
                                    // real local either; see
                                    // `build_dict_fields`'s own doc comment
                                    // just above for the full rationale.
                                    Option.some (Term.var (0 - 1) (DebugName.named (mangled_to_identifier (mangle_instance_dict_name (instance_module_prefix found_insname) cls_name ins_args)))),
                            },
                        Option.none => Option.none,
                    },
            },
    }

#[partial]
def resolve_dict_args (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (bindings : List (Pair Identifier Term)) (carrier : Term) (extra_carriers : List Term) (constraints : List TypeConstraint) : Option (List Term) :=
    match constraints {
        List.empty => Option.some List.empty,
        List.cons c rest =>
            match resolve_dict_arg classes instances dict_env bindings carrier extra_carriers c {
                Option.none => Option.none,
                Option.some arg =>
                    match resolve_dict_args classes instances dict_env bindings carrier extra_carriers rest {
                        Option.none => Option.none,
                        Option.some rest_args => Option.some (List.cons arg rest_args),
                    },
            },
    }

/// The full field-name list a D5 field-projection match needs to bind
/// (even fields other than the one being projected -- match's own
/// field-binding is positional, `bind_match_fields`, so every field
/// needs a pattern var even when unused).
#[partial]
def dict_match_pattern_vars (method_names : List Identifier) (target : Identifier) : List Identifier :=
    match method_names {
        List.empty => List.empty,
        List.cons m rest =>
            let this_var := if Similar.similar m target then target else Identifier.id ("_unused_" ++ show_identifier m) in
            List.cons this_var (dict_match_pattern_vars rest target),
    }

/// D5: rewrites a class-method call into a field projection on an
/// already-bound dict local -- `match __dict_Show { mk show _... =>
/// show real_args }`.
///
/// The `Term.var 0 (...)` index here is CODEGEN's own free-standing
/// convention (`lang/codegen/emit.mo` lowers this straight to LLVM
/// without ever running it back through the bidirectional checker --
/// same convention `promote_instance_defs`' own `__Dict_ClassName`
/// value defs use, `module.mo`'s `is_dict_value_def` skips checking
/// those for exactly this reason). It is NOT a real de Bruijn index
/// into whatever `local_types`/`LocalScope` happen to be in scope
/// wherever this term gets embedded -- reusing it as-is for a checker-
/// facing result resolves the WRONG binder (or none at all) the moment
/// this projection sits inside a real, already-non-empty local
/// environment (a constrained def's own params, an enclosing match's
/// own pattern vars, ...), surfacing a bogus `unknown variable
/// 'bound_var'` diagnostic -- confirmed as the exact D5 dict-forwarding
/// bug (`module.mo`'s own D4/D5 test area). See `build_dict_field_
/// projection_checked` below for the checker-facing sibling that fixes
/// this WITHOUT touching this function -- codegen's own consumer
/// (`resolve_class_calls`, `lang/scope.mo`) depends on this exact
/// index-`0` shape and is confirmed working; changing it here would
/// regress that.
#[partial]
def build_dict_field_projection (cls : Class) (dict_id : Identifier) (method_name : Identifier) (real_args : List Term) : Term :=
    let method_names := class_method_names cls in
    let pattern_vars := dict_match_pattern_vars method_names method_name in
    let call := rebuild_call (Term.var 0 (DebugName.named method_name)) real_args in
    let case_ := MatchCase.mc (Identifier.id "mk") pattern_vars call Option.none in
    Term.lit (Literal.match_ (Term.var 0 (DebugName.named dict_id)) (List.cons case_ List.empty))

/// Checker-facing sibling of `build_dict_field_projection` (D5 dict-
/// forwarding, see that function's own doc comment for the full
/// story). Structurally identical EXCEPT both `Term.var` references use
/// the checker's real free-variable convention (`Term.var sentinel
/// (DebugName.named _)`, `sentinel = -1` -- `lang.typecheck.infer`'s own
/// `type_check_var` dispatches on this exact sentinel to resolve by
/// NAME via `scope_resolve_name`/`LocalScope`, the same path D4 and
/// every ordinary bound-var lookup already use successfully) instead of
/// a raw de Bruijn index -- so the produced term re-typechecks
/// correctly no matter what's already bound in the surrounding
/// `LocalScope` (`dict_id` resolves to the already-bound dict
/// parameter; the match arm's own `method_name` pattern var resolves
/// via `prepend_typed_local_vars`, exactly like any other match-bound
/// local). `-1` is inlined directly (not imported from `infer.mo`'s own
/// `sentinel` constant) to avoid a circular module dependency --
/// `infer.mo` already imports FROM `lang.scope`, not the reverse.
#[partial]
def build_dict_field_projection_checked (cls : Class) (dict_id : Identifier) (method_name : Identifier) (real_args : List Term) : Term :=
    let free_var_sentinel : I64 := 0 - 1 in
    let method_names := class_method_names cls in
    let pattern_vars := dict_match_pattern_vars method_names method_name in
    let call := rebuild_call (Term.var free_var_sentinel (DebugName.named method_name)) real_args in
    let case_ := MatchCase.mc (Identifier.id "mk") pattern_vars call Option.none in
    Term.lit (Literal.match_ (Term.var free_var_sentinel (DebugName.named dict_id)) (List.cons case_ List.empty))

/// The main per-term rewrite -- `term_map_children`-driven fallback for
/// every shape that isn't a class-method-shaped call spine, mirroring
/// `resolve_infix_term`'s own recursion pattern, extended with the
/// `env`/`dict_env` threading D4/D5 both need.
///
/// `def_carrier` is the ENCLOSING def's own declared-return-type carrier
/// (`full_return_carrier`, computed once per top-level def by
/// `resolve_class_calls_decls_go` and threaded down unchanged through
/// every recursive call here -- it never varies within one def's body,
/// same reasoning as `classes`/`instances`/etc. above). It's the D4
/// fallback of last resort for a class-method call whose OWN args carry
/// no carrier-revealing type at all -- the do-notation case this exists
/// for: `Monad.pure x`'s only argument is the MONAD'S ELEMENT type, not
/// the monad itself, so `infer_carrier_from_args` can never recover "IO"
/// from it no matter how good the arg-shape coverage gets; the one
/// carrier ALWAYS available for a bare `pure`/final `bind` at the tail
/// of a do-block is the enclosing function's own declared return type
/// (every do-block's `pure`/`bind` chain shares that same monad).
/// Confirmed as a real gap via direct repro: `Monad.bind`'s own carrier
/// (inferable from its first, real, `M A`-shaped argument) started
/// resolving once `last_segment_of`'s dotted-single-segment fix landed,
/// but its continuation's trailing `Monad.pure unit`/`Monad.pure 0`
/// still failed (`undefined @Monad_pure` at link time) -- exactly this
/// gap.
///
/// `expect` is the carrier this very term is EXPECTED to have, handed
/// down from the one place the source itself pins one: the argument of an
/// annotated binding's own desugared lambda (`Term.app (Term.lam _dbg T
/// _) value` -- see `lam_param_hints`). It is threaded as an EXTRA
/// candidate carrier, after the ones the call's own arguments reveal, so
/// a call that already resolves keeps resolving exactly as it did; it
/// only gets consulted where nothing else did (`Map.empty`'s nullary
/// shape, `Bounded.max_bound`), which is precisely the family of
/// calls the args-only channel can never resolve. This is the channel
/// `lang/typecheck/infer.mo`'s `carrier_from_expected_type` gives the
/// checker, and here it is deliberately NARROWER than that one: it
/// comes from a syntactic annotation on the binding itself, never from
/// "the enclosing term's expected type", which in a def body is the
/// def's declared RETURN type and has nothing to do with a carrier
/// (measured: `def t1 : Bool := Show.show [42]` dispatched to
/// `Show_Bool_show`).
#[partial]
def resolve_class_call_term_go (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (def_constraints : List DefConstraintEntry) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (env : List LocalTypeBinding) (dict_env : List DictBinding) (def_carrier : Option Term) (expect : Option Term) (t : Term) : Term :=
    match t {
        // R3 (`lang/parser/lower_parse.mo`) puts a position wrapper on
        // every call ARGUMENT, and the expected carrier threaded here is
        // a property of the argument's own VALUE -- so it passes straight
        // through the wrapper, which is data and not structure
        // (`term_map_children`'s own `Term.ctx` arm, same rebuilding
        // shape). Falling through to the generic `_` arm instead -- which
        // is what this function did when the channel was first wired --
        // still traverses the wrapper but DISCARDS the hint one level
        // above the call it was meant for, because that arm's partial
        // application is the no-expectation wrapper. MEASURED: this is
        // exactly why `let e : List I64 := Monoid.mempty unit` (and every
        // `let m : BTreeMap K V := Map.empty`) stayed unresolved while
        // the identical unwrapped shape resolved.
        Term.ctx loc inner =>
            Term.ctx loc (resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier expect inner),
        Term.lam dbg typ body =>
            match dbg {
                DebugName.named id =>
                    let bound_typ : Term := lam_binder_type typ expect in
                    let dict_class := dict_binding_class_of id in
                    let new_env := List.cons (LocalTypeBinding.mk id bound_typ) env in
                    let new_dict_env := match dict_class {
                        Option.some cls_name => List.cons (DictBinding.mk cls_name id) dict_env,
                        Option.none => dict_env,
                    } in
                    Term.lam dbg (resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier Option.none bound_typ)
                        (resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types new_env new_dict_env def_carrier (lam_body_expect expect) body),
                DebugName.unnamed =>
                    Term.lam dbg (resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier Option.none typ)
                        (resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier Option.none body),
            },
        Term.app _ _ =>
            match flatten_call_spine t {
                CallSpine.mk head args =>
                    let hints := call_arg_hints classes def_types env ctor_owners ctor_field_types head args expect in
                    let resolved_args := resolve_class_call_terms classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier hints args in
                    // `App(Lam(id, typ, body), value)` -- the parser's
                    // desugaring of EVERY `let`, annotated or not -- gets its
                    // binder's type from the resolved VALUE when the source
                    // wrote none (`let_binder_rewrite`, whose own comment
                    // carries the measured failure). Only the head of the
                    // spine is touched, and only for the one-argument shape:
                    // two or more arguments is a curried `lambda`
                    // application, whose binders the hint channel already
                    // answers (`lam_binder_type`'s own `expect`).
                    let dispatch_head : Term := let_binder_rewrite env ctor_owners def_types ctor_field_types head resolved_args in
                    match head {
                        Term.var _ dbg =>
                            match dbg {
                                DebugName.named id =>
                                    match class_method_ref classes id {
                                        Option.some ref =>
                                            match ref {
                                                ClassMethodRef.mk cls method_name =>
                                                    resolve_class_method_call classes instances dict_env def_types ctor_field_types cls method_name resolved_args head args def_carrier env ctor_owners expect,
                                            },
                                        Option.none => resolve_ordinary_constrained_call classes instances dict_env def_constraints def_types ctor_field_types id head resolved_args env ctor_owners,
                                    },
                                DebugName.unnamed => rebuild_call head resolved_args,
                            },
                        _ => rebuild_call (resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier Option.none dispatch_head) resolved_args,
                    },
            },
        // A NULLARY class method reference (e.g. `FromListLiteral.empty`,
        // `MakeEmpty.empty`) is a bare `Term.var`, never wrapped in a
        // `Term.app` -- the `Term.app` arm above is the ONLY place this
        // function otherwise ever recognizes a class-method call, so
        // without this arm a zero-arg method call is silently never even
        // CONSIDERED for resolution (falls straight into the generic
        // `term_map_children` no-op below, which has no children to
        // recurse into for a `Term.var` anyway). Confirmed load-bearing
        // via direct repro: `std/derive.mo`'s `lens_getter`'s own list-
        // literal-desugared `FromListLiteral.empty` (`lang/parser.mo`'s
        // list-literal grammar) hits exactly this gap.
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match class_method_ref classes id {
                        Option.some ref =>
                            match ref {
                                ClassMethodRef.mk cls method_name =>
                                    resolve_class_method_call classes instances dict_env def_types ctor_field_types cls method_name List.empty t List.empty def_carrier env ctor_owners expect,
                            },
                        Option.none => t,
                    },
                DebugName.unnamed => t,
            },
        // `Literal.match_` gets its OWN case (not the generic
        // `term_map_children` fallback below) so each arm's own body can
        // see an `env` enriched with that arm's pattern-bound variable
        // types (`match_arm_env`, `lang/scope.mo`'s own `CtorFieldTypes`
        // section above) -- `k`/`v` in `match p { Pair.pair k v => ...
        // }` are otherwise still bare, type-less names by the time
        // carrier inference runs on a class-method call inside the arm
        // (e.g. `Map.insert k v acc`'s `k`), the same gap `a47856c`
        // already fixed for `let`/lambda bindings (which desugar to
        // `Term.lam`, handled above) but never extended to match-bound
        // ones. Every OTHER `Literal` variant still goes through
        // `term_map_children` unchanged.
        Term.lit lit_ =>
            match lit_ {
                Literal.match_ scrutinee cases =>
                    let resolved_scrutinee := resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier Option.none scrutinee in
                    Term.lit (Literal.match_ resolved_scrutinee (resolve_class_call_cases classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier scrutinee cases)),
                _ => term_map_children (resolve_class_call_term classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier) t,
            },
        _ => term_map_children (resolve_class_call_term classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier) t,
    }

/// The no-expectation entry point every OTHER caller in this file uses --
/// `resolve_class_call_terms`/`resolve_class_call_cases`'s own
/// `term_map_children` partial applications, and
/// `resolve_class_calls_decls_go`'s top-level per-def walk. A thin
/// wrapper rather than a second parameter at those ~10 sites: the only
/// terms that ever HAVE an expectation are the arguments of an annotated
/// binding's desugared lambda, and those are reached through `_go`
/// directly (the app arm's own `lam_param_hints`).
#[partial]
def resolve_class_call_term (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (def_constraints : List DefConstraintEntry) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (env : List LocalTypeBinding) (dict_env : List DictBinding) (def_carrier : Option Term) (t : Term) : Term :=
    resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier Option.none t

/// Is `t` unusable as an expected carrier? A hole, or a bare universe
/// placeholder (`Term.type_ 1`, what a literal reports when it is checked
/// in pure-infer mode) -- the same two shapes `is_uninformative_carrier`
/// (`lang/typecheck/infer.mo`) rejects. An un-annotated binding's
/// desugared lambda carries one of these as its parameter type and says
/// nothing about the value's carrier, so it must not be handed down as if
/// it did.
def expected_carrier_of (t : Term) : Option Term :=
    match t {
        Term.hole => Option.none,
        Term.type_ _ => Option.none,
        _ => Option.some t,
    }

/// The type to bind a lambda's own parameter at: the lambda's WRITTEN
/// type when it has one, else the domain of whatever expected type the
/// call site handed down. `fn x acc => x + acc` passed to
/// `Foldable.foldr` writes nothing at all -- an unannotated parameter is
/// the parser's `Term.type_ 1` placeholder, not a type -- so `x`'s type,
/// and with it the carrier every class call in the body resolves
/// against, is recoverable only from the callee's instantiated
/// signature, which is exactly what the hint channel already hands this
/// arm (`sig_hints`/`sig_arg_hints`, positionally, for the argument this
/// lambda IS).
///
/// MEASURED (2026-09-19): without this, `init/src/foldable_tests.mo`'s
/// `Foldable.foldr (fn x acc => x + acc) 0 [1, 2, 3]` resolved that `+`
/// with the class's own parameter name as its carrier (`A`), which
/// matches `instance [Add A] HAdd A A A` -- a dict whose field IS the
/// mutually-recursive `instance [HAdd A A A] Add A` -- so the driver
/// called itself forever and died by signal (`driver exited -1`, both
/// foldable files). The same fold with `(x : I64) (acc : I64)` written
/// out compiles to `number::Add_I64_add`, which is what pinning the
/// binder type here recovers.
///
/// A written type always wins, INFORMATIVE or not (`expected_carrier_of`
/// is the same "is this a real type" test `call_arg_hints`'
/// `lam_param_hints` sibling applies), so every lambda that already
/// knew its parameter type is emitted exactly as it was.
def lam_binder_type (written : Term) (expect : Option Term) : Term :=
    match expected_carrier_of written {
        Option.some _ => written,
        Option.none =>
            match expect {
                Option.some e =>
                    match term_peel e {
                        Term.pi arg _ret => arg,
                        _ => written,
                    },
                Option.none => written,
            },
    }

/// The type to bind a `let`'s OWN binder at when the source wrote none.
///
/// `let x := e in body` desugars to `Term.app (Term.lam x _ body) e` --
/// `try_compile_let_beta_db`'s own comment describes that shape -- so the
/// un-annotated spelling reaches the lambda arm with the parser's
/// `Term.type_ 1` placeholder and binds the placeholder into the body's
/// own `env`. Every class call in that body which reads `x`'s carrier
/// (`infer_carrier_type`'s `Term.var` arm) then finds nothing usable and
/// falls back to the class's DEFAULT carrier -- silently, since the
/// default is a legal pick for the class, just not for this value.
///
/// MEASURED (2026-09-19) on `std/src/map_tests.mo`'s
/// `test_insert_avl_drop_repro`: `let m1 : BTreeMap String I64 :=
/// Map.insert "d" 4 Map.empty in let m2 := Map.insert "c" 3 m1 in
/// let m3 := ... m2 in let m4 := ... m3 in` -- one annotated binding and
/// three chained un-annotated ones. `m1` and `m2` emitted
/// `Map_BTreeMap_insert`; `m3` and `m4` emitted `Map_HashMap_insert`,
/// `Map`'s declared default, on BTreeMap values, and the driver died in
/// `monad_get_tag` reading the wrong constructor. No amount of argument
/// inspection recovers the carrier there: the argument IS `m2`, a bare
/// local, and its own declared type was a placeholder.
///
/// So the binder's type comes from the VALUE it is bound to, read the
/// same way the app arm already reads a computed operand's carrier: for a
/// class-method call that is the promoted instance method's own declared
/// return type (the concrete `BTreeMap K V`, not the class's abstract
/// `M K V`), which is exactly what makes the ANNOTATED chain work one
/// binding up. This is not a guess -- it is the resolution's own
/// conclusion, one step earlier.
///
/// A written type always wins, informative or not -- `expected_carrier_of`
/// is the same test `lam_binder_type` applies -- so every annotated `let`
/// is emitted exactly as it was.
#[partial]
def let_binder_type (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (written : Term) (value : Term) : Term :=
    match expected_carrier_of written {
        Option.some _ => written,
        Option.none =>
            match infer_carrier_type env ctor_owners def_types ctor_field_types value {
                Option.some carrier => carrier,
                Option.none => written,
            },
    }

/// A call spine's HEAD as the lambda arm should see it: a single-argument
/// `Term.lam` head -- the shape `let x := e in body` desugars to -- has its
/// written binder type replaced by `let_binder_type`'s reading of the one
/// RESOLVED argument. Every other head, and every other arity, is returned
/// unchanged, so this is a no-op for all input the old pass already
/// resolved.
#[partial]
def let_binder_rewrite (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (head : Term) (args : List Term) : Term :=
    match head {
        Term.lam ldbg ltyp lbody =>
            match ldbg {
                DebugName.named _ =>
                    match args {
                        List.cons v rest =>
                            match rest {
                                List.empty => Term.lam ldbg (let_binder_type env ctor_owners def_types ctor_field_types ltyp v) lbody,
                                List.cons _ _ => head,
                            },
                        List.empty => head,
                    },
                DebugName.unnamed => head,
            },
        _ => head,
    }

/// The expected type for a lambda's BODY, given the expected type for the
/// lambda itself: peel one Pi. `fn x acc => body` is nested `Term.lam`s,
/// so the outer binder consumes the outer domain and hands the rest down
/// -- that is what lets the second unannotated parameter (`acc` above)
/// find its type from the same signature-derived hint.
def lam_body_expect (expect : Option Term) : Option Term :=
    match expect {
        Option.some e =>
            match term_peel e {
                Term.pi _arg ret => Option.some ret,
                _ => Option.none,
            },
        Option.none => Option.none,
    }

/// `Option Term` as a 0/1-element candidate list, for appending to the
/// args-derived carriers `find_matching_instance_carrier_any` and
/// `resolve_dict_arg` already search.
def carrier_hint_list (hint : Option Term) : List Term :=
    match hint {
        Option.some t => List.cons t List.empty,
        Option.none => List.empty,
    }

/// A class's own first declared type parameter -- the position its
/// carrier stands in (`M` in `class Monad (M : Type -> Type)`, `D` in
/// `class Json.Deserializer (D : Type)`). The carrier is the first
/// parameter by the language's own convention, and it is the one
/// `method_carrier_hint` projects a full type hint through.
#[partial]
def first_param_name (params : List Param) : Option Identifier :=
    match params {
        List.empty => Option.none,
        List.cons p _rest => match p { Param.mk pname _t _m _d _a => Option.some pname },
    }

#[partial]
def class_first_param_name (cls : Class) : Option Identifier :=
    match cls {
        Class.mk _nm params _c _m _v => first_param_name params,
    }

/// The carrier a call's own FULL type hint implies, by projecting that
/// hint through the callee's declared class signature.
///
/// Where the hint is a whole type -- an annotated binding's expected type
/// (`(Monad.pure 42 : State I64 I64)`), or the enclosing def's declared
/// return type (`def increment : State I64 I64 := MonadState.modify_get
/// ...`) -- the carrier it implies is not the type ITSELF. It is that
/// type with the class's own carrier parameter identified: `M A` against
/// `State I64 I64` puts the carrier at `M := State I64`, exactly the
/// shape an instance's own args are written in (`instance MonadState
/// (State I64)`). Handing the whole type over instead matches NOTHING,
/// which is why these two files report `no instance found` for a call
/// whose carrier is plainly written out in the enclosing annotation
/// (`lang/src/json.mo`'s `Json.Deserializer.deserialize`: `Result String
/// Person` against `instance Json.Deserializer Person`).
///
/// `bind_term_vars` over `final_result_type sig` is the projection, and
/// `class_method_var_names` its wildcard set -- both already exist for
/// the instance side (`method_sig_bindings`, `carrier_bindings`). The
/// lookup is for the CLASS'S FIRST PARAM, so a signature whose codomain
/// is not headed by that parameter (`Show.show : A -> String`) binds
/// nothing and yields `Option.none`: no candidate, no guess. That is the
/// soundness condition this channel rests on -- "the method's result type
/// IS the carrier applied to its arguments", which is precisely the
/// codomain case the args-derived channel cannot see.
///
/// Appended to the candidate list AFTER everything that channel already
/// produced, so a call that resolved before resolves to the same instance
/// it did.
#[partial]
def method_carrier_hint (cls : Class) (method_name : Identifier) (hint : Option Term) : Option Term :=
    match hint {
        Option.none => Option.none,
        Option.some full =>
            match class_method_declared_type cls method_name {
                Option.none => Option.none,
                Option.some sig =>
                    match class_first_param_name cls {
                        Option.none => Option.none,
                        Option.some carrier_name =>
                            lookup_binding (bind_term_vars (class_method_var_names cls sig) (final_result_type sig) full List.empty) carrier_name,
                    },
            },
    }

/// The candidates `method_carrier_hint` contributes for one call: the
/// projection of `hint`, and (when they differ) of the enclosing def's
/// own declared return type. Both are `Option Term`s already, so this is
/// just the two of them as a candidate list -- see `resolve_class_method_
/// call`'s doc comment on where it goes and why.
#[partial]
def method_carrier_hints (cls : Class) (method_name : Identifier) (hint : Option Term) (def_carrier : Option Term) : List Term :=
    List.append (carrier_hint_list (method_carrier_hint cls method_name hint)) (carrier_hint_list (method_carrier_hint cls method_name def_carrier))

/// One expected-carrier hint per argument of a call spine, read off the
/// spine's own HEAD when it is a lambda. `Term.app (Term.lam _dbg T body)
/// value` is exactly what an annotated binding desugars to (`let x : T :=
/// value in body`, and its do-block equivalent), so `T` is the value's
/// expected carrier -- the same shape, read the same way, as
/// `app_arg_expected_type` reads it in the checker
/// (`lang/typecheck/infer.mo`). A curried head lines the hints up
/// positionally; anything else gets no hint at all, leaving every
/// existing resolution path exactly as it was.
#[partial]
def lam_param_hints (head : Term) (args : List Term) : List (Option Term) :=
    match args {
        List.empty => List.empty,
        List.cons _ rest =>
            match head {
                Term.lam _dbg typ body => List.cons (expected_carrier_of typ) (lam_param_hints body rest),
                _ => List.empty,
            },
    }

/// Every argument's own inferred carrier, POSITIONALLY -- index-aligned
/// with `args`, unlike `infer_all_carriers_from_args_go`, which DROPS the
/// ones that reveal nothing. The callee-signature channel below has to
/// know WHICH argument said nothing, because that is the one it answers
/// for.
#[partial]
def infer_carriers_each (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (args : List Term) : List (Option Term) :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            List.cons (infer_carrier_type env ctor_owners def_types ctor_field_types a) (infer_carriers_each env ctor_owners def_types ctor_field_types rest),
    }

/// Pass 1 of the callee-signature channel: walk a declared signature's Pi
/// chain in lockstep with the call's own argument carriers, recording what
/// each parameter's declared SHAPE binds. `BEq.beq`'s `A -> A -> Bool`
/// against `[<nothing>; Ordering]` binds `A := Ordering` -- off the
/// SIBLING argument, which is the whole point: the call's own
/// `Bounded.max_bound` argument has no argument list at all, so nothing
/// inside it can ever say what it is.
#[partial]
def sig_arg_bindings (sig : Term) (names : List Identifier) (each : List (Option Term)) (acc : List (Pair Identifier Term)) : List (Pair Identifier Term) :=
    match term_peel sig {
        Term.forall _ _ body => sig_arg_bindings body names each acc,
        Term.pi ptyp ret =>
            match each {
                List.empty => acc,
                List.cons c rest =>
                    let inner := match c {
                        Option.some carrier => bind_term_vars names ptyp carrier acc,
                        Option.none => acc,
                    } in
                    sig_arg_bindings ret names rest inner,
            },
        _ => acc,
    }

/// Pass 2: one hint per declared parameter, in order -- that parameter's
/// own declared type with the pass-1 bindings substituted.
#[partial]
def sig_arg_hints (sig : Term) (names : List Identifier) (bindings : List (Pair Identifier Term)) : List (Option Term) :=
    match term_peel sig {
        Term.forall _ _ body => sig_arg_hints body names bindings,
        Term.pi ptyp ret => List.cons (concrete_hint ptyp names bindings) (sig_arg_hints ret names bindings),
        _ => List.empty,
    }

/// A declared parameter type as an expected carrier: substituted, and only
/// if it is CONCRETE afterwards -- no name the signature itself could bind
/// survives in it. An unbound `A` handed down as an expected carrier would
/// match the first instance whose head is a wildcard, which is a guess
/// dressed up as an inference. `Bounded.max_bound`'s parameter type here
/// is the bare `A`, and it is the sibling's `Ordering` being substituted in
/// that turns it into a hint at all; this check is what stops every OTHER
/// still-generic parameter from becoming one.
///
/// A LAMBDA-typed parameter (`Monad.bind`'s `A -> M B`) is split instead,
/// because the two halves of the arrow reach two different consumers and
/// only ONE of them needs its half to be name-free:
///
/// * the DOMAIN is the type `lam_binder_type` binds the lambda's own
///   parameter at, so it carries the hazard above by itself -- a generic
///   `A` there is exactly the foldr misresolution
///   `init/src/foldable_tests.mo` measured. A domain that still names a
///   signature variable is replaced by `Term.hole`, which is what the
///   parser writes for a binder the source never annotated: the hint then
///   says nothing about the binder, exactly as an omitted annotation does,
///   and `lam_binder_type` keeps whatever the lambda wrote (if anything).
/// * the CODOMAIN is a lambda BODY's expectation, and there the only thing
///   that matters is which type the class's carrier parameter lands on.
///   That projection goes through the class's own declared signature
///   (`method_carrier_hint`), so a leftover name beside the carrier cannot
///   become one: `Protocol Init Init B` against `Monad.pure : A -> M A`
///   binds `M := Protocol Init Init` and nothing else.
///
/// So a `B` that nothing binds -- the call's own result position, which the
/// expectation does not reach -- no longer throws the whole arrow away.
///
/// MEASURED (2026-09-21) on `examples/indexed_monads.mo`'s
/// `do_bind_result`: the do-block desugars to `Monad.bind e (fn x => return
/// (x + 1))`, whose second parameter is `A -> M B`. `M` is bound to
/// `Protocol Init Init` by the ascription's expected type, but `A` is
/// bound by NOTHING -- the sibling argument is `Protocol.protocol 42`,
/// whose own carrier comes back as the bare `Protocol` (its `I`/`J` indices
/// are phantom, so `ctor_app_carrier` refuses to guess them), and a bare
/// carrier binds no variable at all (`bind_term_vars`'s `Term.app` arm needs
/// an applied actual to descend into). Rejecting the arrow on that unbound
/// `A` left `Monad.pure` with only its own argument's `I64` to guess from
/// (`AD_I64`, no expected type at all), and `I64` has no `Monad` instance --
/// `no instance found for Monad.pure`. Annotating ONLY that argument
/// (`(Protocol.protocol 42 : Protocol Init Init I64)`) resolves the whole
/// file, which is what isolates this channel as the one missing.
///
/// Every hint the old check ACCEPTED is still accepted with the same value
/// (`hint_arrow_domain` returns the domain verbatim whenever it is usable),
/// so this only ever adds resolutions.
#[partial]
def concrete_hint (ptyp : Term) (names : List Identifier) (bindings : List (Pair Identifier Term)) : Option Term :=
    let sub := subst_carrier_bindings bindings ptyp in
    match term_peel sub {
        Term.pi dom ret =>
            match expected_carrier_of ret {
                // A codomain of a hole or a bare universe placeholder says
                // nothing about the body, so there is nothing to hand down.
                Option.none => Option.none,
                Option.some _ => Option.some (Term.pi (hint_arrow_domain names dom) ret),
            },
        _ => if type_mentions_any names sub then Option.none else expected_carrier_of sub,
    }

/// The domain an expected-carrier hint's arrow should carry: the declared
/// one when it is usable as a lambda parameter's type, else `Term.hole` --
/// the same value the parser writes for a binder the source left
/// un-annotated, so a hint with an unusable domain degrades to exactly the
/// information an omitted annotation carries (none) rather than to a guess.
#[partial]
def hint_arrow_domain (names : List Identifier) (dom : Term) : Term :=
    if type_mentions_any names dom then Term.hole
    else match expected_carrier_of dom {
             Option.some d => d,
             Option.none => Term.hole,
         }

/// Does any bare name in `names` occur anywhere in `t`?
#[partial]
def type_mentions_any (names : List Identifier) (t : Term) : Bool :=
    match term_peel t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => id_member id names,
                DebugName.unnamed => false,
            },
        Term.app f a => if type_mentions_any names f then true else type_mentions_any names a,
        Term.pi p ret => if type_mentions_any names p then true else type_mentions_any names ret,
        Term.forall _ _ body => type_mentions_any names body,
        Term.lam _ ty body => if type_mentions_any names ty then true else type_mentions_any names body,
        _ => false,
    }

/// Expected-carrier hints for a call's arguments, read off the CALLEE's
/// own declared signature. The signature's own variables are solved
/// against the arguments that DO reveal a carrier (`sig_arg_bindings`),
/// and only then handed back to the arguments that do not
/// (`sig_arg_hints`) -- the source the checker has
/// (`lang/typecheck/infer.mo` solves a class method's signature against
/// the call site the same way) and the only one that can answer a
/// nullary method inside an argument position, e.g. `BEq.beq
/// Bounded.max_bound gt`: the call's carrier is pinned to `Ordering` by
/// `gt`, and the sibling that reveals nothing is the one that needs it.
///
/// `names` is the wildcard set this signature's own variables are drawn
/// from -- supplied by the caller, because WHICH names are variables
/// depends on where the signature came from and not on its shape at all:
/// a class method's from the class declaration (`class_param_names`), a
/// def's from its own `Forall` binders (`collect_forall_names`). See
/// `class_param_names` for the measured failure that shape-reading caused.
def sig_hints (names : List Identifier) (sig : Option Term) (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (args : List Term) (expect : Option Term) : List (Option Term) :=
    match sig {
        Option.none => List.empty,
        Option.some typ =>
            // Only when the signature's own arity matches the call's, so
            // parameter i of the signature is always argument i of the
            // call. A constrained def's registered type carries Phase 3's
            // PREPENDED dict parameters (`Dict_Show_A -> A -> Bool` for
            // `def f [Show A] (x : A)`), which would shift every hint one
            // position left and hand an argument the parameter type of
            // the one after it. Fewer written arguments than declared
            // parameters is the same hazard in reverse, so the guard is
            // exact equality, not a bound.
            if I64.beq (pi_arity typ) (arg_count args) then
                let each := infer_carriers_each env ctor_owners def_types ctor_field_types args in
                // Pass 0 (`sig_expect_bindings`) is the SEED, so every
                // binding the arguments themselves reveal still wins
                // (`sig_arg_bindings` prepends, and `lookup_binding`
                // scans from the head): this only answers the variables
                // the arguments said nothing about.
                let bindings := sig_arg_bindings typ names each (sig_expect_bindings typ names expect) in
                sig_arg_hints typ names bindings
            else List.empty,
    }

/// Pass 0 of the callee-signature channel: what the call's OWN expected
/// carrier binds of the signature's variables, recorded before the
/// arguments are walked so `sig_arg_bindings` can leave those variables
/// to the arguments wherever an argument has something to say.
///
/// This is the same binding `sig_arg_bindings` performs, one position
/// over: the signature's RESULT type (`M K V` for `Map.insert`) against
/// the type the call site expects the whole call to have
/// (`BTreeMap String I64` from `let m : BTreeMap String I64 := Map.insert
/// ...`), which binds `M := BTreeMap`, `K := String`, `V := I64`.
///
/// MEASURED (2026-09-19) -- this is what `std/src/map_tests.mo`'s
/// `test_insert_avl_drop_repro` needs, and it is the one channel the
/// arguments cannot supply: `Map.insert "d" 4 Map.empty`'s own carrier
/// is pinned by the ARGUMENT `Map.empty` -- which, with no expectation
/// in hand, resolves to the class's declared DEFAULT (`HashMap`) and so
/// presents the outer call with `HashMap` as its strongest carrier
/// evidence. The annotation is then only a hint APPENDED after it, tried
/// second and never reached, so the compiled call is
/// `Map_HashMap_insert` on a value the annotation says is a `BTreeMap`
/// -- one constructor read as the other, corrupting the tree
/// (`BTreeMap.to_list_asc` segfaulting on a bogus field read, `driver
/// exited -1`). Seeding the channel fixes the INNER call first
/// (`Map.empty`'s own hint is now the concrete `BTreeMap String I64`),
/// which is what makes the outer call's argument-derived carrier right
/// as well -- no ordering change in `find_matching_instance_carrier_any`
/// and so no change at all for a call whose arguments already reveal a
/// concrete carrier.
///
/// The seed can never CONTRADICT a well-typed call: the checker has
/// already unified the method's own result type with the expected type,
/// so a variable bound here is bound to what the checker itself
/// instantiated it to. Ill-typed programs are rejected before codegen
/// (`expected_carrier_of` additionally drops a hole or a bare universe
/// placeholder, which say nothing).
#[partial]
def sig_expect_bindings (typ : Term) (names : List Identifier) (expect : Option Term) : List (Pair Identifier Term) :=
    match expect {
        Option.none => List.empty,
        Option.some e =>
            match expected_carrier_of e {
                Option.none => List.empty,
                Option.some carrier => bind_term_vars names (final_result_type typ) carrier List.empty,
            },
    }

/// The number of value parameters a declared signature takes (its own
/// Pi chain, `Forall` binders skipped -- they bind types, not values).
#[partial]
def pi_arity (sig : Term) : I64 :=
    match term_peel sig {
        Term.forall _ _ body => pi_arity body,
        Term.pi _ ret => 1 + pi_arity ret,
        _ => 0,
    }

#[partial]
def arg_count (args : List Term) : I64 :=
    match args {
        List.empty => 0,
        List.cons _ rest => 1 + arg_count rest,
    }

/// One expected carrier per argument of a call spine, from whichever
/// source actually has one: the annotated-binding lambda the spine's head
/// is (`lam_param_hints`), or the callee's own declared signature
/// (`sig_hints`). Anything else yields no hint at all, which leaves every
/// existing resolution path exactly as it was.
#[partial]
def call_arg_hints (classes : List Class) (def_types : HashMap String Term) (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (ctor_field_types : List CtorFieldTypes) (head : Term) (args : List Term) (expect : Option Term) : List (Option Term) :=
    match head {
        Term.lam _ _ _ => lam_param_hints head args,
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match class_method_ref classes id {
                        Option.some ref =>
                            // A class method's variables are its class's own
                            // parameters plus the arguments applied to them
                            // and its own bare domains
                            // (`class_method_var_names`); the class-side
                            // signature is written in those, so its
                            // `Forall` binder -- when it has one -- names
                            // the same set the shape walk would find anyway.
                            match ref {
                                ClassMethodRef.mk cls method_name =>
                                    match class_method_declared_type cls method_name {
                                        Option.none => List.empty,
                                        Option.some typ => sig_hints (class_method_var_names cls typ) (Option.some typ) env ctor_owners def_types ctor_field_types args expect,
                                    },
                            },
                        Option.none =>
                            // A def's own variables are its `Forall` binders
                            // (`elaborate_def` wraps every free type variable
                            // in one by construction), so a foraller-free
                            // signature -- a promoted instance method, whose
                            // domains are the concrete types themselves -- has
                            // NO variables, and its parameter types are handed
                            // down as they are. See `class_method_var_names`
                            // for the measured failure shape-reading caused.
                            match lookup_def_type def_types id {
                                Option.some typ => sig_hints (collect_forall_names typ) (Option.some typ) env ctor_owners def_types ctor_field_types args expect,
                                Option.none => List.empty,
                            },
                    },
                DebugName.unnamed => List.empty,
            },
        _ => List.empty,
    }

#[partial]
def resolve_class_call_terms (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (def_constraints : List DefConstraintEntry) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (env : List LocalTypeBinding) (dict_env : List DictBinding) (def_carrier : Option Term) (hints : List (Option Term)) (args : List Term) : List Term :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            // A shorter (or absent) hint list is not an error: it means
            // the spine's head had nothing to say about the remaining
            // arguments (`lam_param_hints`), so they resolve exactly as
            // they did before this channel existed.
            match hints {
                List.cons h hs =>
                    List.cons (resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier h a) (resolve_class_call_terms classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier hs rest),
                List.empty =>
                    List.cons (resolve_class_call_term_go classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier Option.none a) (resolve_class_call_terms classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier List.empty rest),
            },
    }

#[partial]
def resolve_class_call_cases (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (def_constraints : List DefConstraintEntry) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (env : List LocalTypeBinding) (dict_env : List DictBinding) (def_carrier : Option Term) (scrutinee : Term) (cases : List MatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (resolve_class_call_case classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier scrutinee c) (resolve_class_call_cases classes instances ctor_owners def_constraints def_types ctor_field_types env dict_env def_carrier scrutinee rest),
    }

#[partial]
def resolve_class_call_case (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (def_constraints : List DefConstraintEntry) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (env : List LocalTypeBinding) (dict_env : List DictBinding) (def_carrier : Option Term) (scrutinee : Term) (c : MatchCase) : MatchCase :=
    match c {
        MatchCase.mc name args body fp =>
            let new_env := match_arm_env ctor_field_types env scrutinee c in
            MatchCase.mc name args (resolve_class_call_term classes instances ctor_owners def_constraints def_types ctor_field_types new_env dict_env def_carrier body) fp,
    }

/// D5-first, D4-fallback resolution for one class-method call, given
/// its own (already-resolved-inside-out) real args. `orig_head`/
/// `orig_args` are the pre-resolution originals, used ONLY for the "no
/// match found" fallback (leaves the call exactly as it structurally
/// resolved via ordinary recursion, per this pass's own "leave
/// unresolved rather than guess" style, matching `resolve_infix_term`).
#[partial]
def resolve_class_method_call (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (cls : Class) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (def_carrier : Option Term) (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (expected : Option Term) : Term :=
    let cls_name := class_own_name cls in
    match lookup_dict_binding dict_env cls_name {
        Option.some dict_id => build_dict_field_projection cls dict_id method_name resolved_args,
        Option.none =>
            // Computed once here (the highest point `resolved_args`/`env`/
            // `ctor_owners`/`def_types` are all still together) and
            // threaded unchanged through the whole D4 chain down to
            // `resolve_dict_arg`'s own `extra_carriers` fallback -- see
            // that function's doc comment for why this exists.
            //
            // The call's OWN expected carrier (`expected`, the annotated
            // binding this call is the value of) is APPENDED, not
            // prepended: every candidate the arguments already revealed is
            // tried first, so a call that resolved before this channel
            // existed resolves to exactly the same instance it did. The
            // hint is only consulted where the args revealed nothing at
            // all -- `Map.empty`'s nullary shape, `Bounded.max_bound` --
            // which is the family that could never resolve.
            //
            // Then the SAME two hints again, projected through the
            // callee's own class signature (`method_carrier_hints`): a
            // hint is a whole type, and the carrier an instance's args are
            // written in is the class's own carrier parameter applied to
            // its arguments, which is a subterm of that type in the
            // codomain position. The raw hint is kept FIRST so the
            // existing channel's own order, and therefore every resolution
            // that already worked, is untouched.
            let ad := infer_all_carriers_from_args_go env ctor_owners def_types ctor_field_types resolved_args in
            let ex := carrier_hint_list expected in
            let pj := method_carrier_hints cls method_name expected def_carrier in
            let extra_carriers := List.append ad (List.append ex pj) in
            resolve_class_method_call_d4 classes instances dict_env def_types cls_name method_name resolved_args orig_head orig_args def_carrier env ctor_owners extra_carriers,
    }

/// D4: no bound dict for this class in scope -- try a fresh concrete
/// lookup from the call's own args, falling back to the enclosing def's
/// own declared-return-type carrier (`def_carrier`) if the args alone
/// don't reveal one (see `resolve_class_call_term`'s own doc comment for
/// why that fallback is needed at all). The fallback is deliberately
/// restricted to the `Monad` class itself (`monad_class_name`) -- "this
/// call's carrier equals the enclosing function's own declared return
/// type" is only a sound assumption for a do-notation `bind`/`pure`
/// (every statement in one do-block shares the same monad, and that
/// monad IS the function's own declared return type by construction);
/// it is NOT sound in general for an arbitrary class method with no
/// carrier-revealing arg (e.g. `Show.show`), where guessing the
/// enclosing function's unrelated return type as a carrier could
/// silently dispatch to the WRONG instance instead of correctly leaving
/// the call unresolved.
///
/// `Monad.pure : A -> M A` needs its OWN special case within that:
/// `def_carrier` must be tried FIRST, before `infer_carrier_from_args`,
/// not merely as its fallback -- `pure`'s only argument is the MONAD'S
/// ELEMENT type (`A`), never the monad itself (`M`), so
/// `infer_carrier_from_args` inferring a carrier from it at all (e.g.
/// `Some I64` from a bare `pure 0`, via `literal_carrier_type`) is
/// already the WRONG answer, not merely a less-good one -- and because
/// it's `Option.some`, the ordinary "args first, def_carrier only on
/// None" order never even reaches the (correct) `def_carrier` fallback.
/// Confirmed as a real gap via direct repro: `pure 0` resolved to a
/// bogus "I64" carrier (no `Monad I64` instance exists, so lookup failed
/// and the call was left unresolved) even after `def_carrier` landed for
/// `bind`.
#[partial]
def resolve_class_method_call_d4 (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (def_types : HashMap String Term) (cls_name : NamePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (def_carrier : Option Term) (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (extra_carriers : List Term) : Term :=
    if npath_eq cls_name monad_class_name && String.beq (show_identifier method_name) "pure" then
        // `def_carrier` first (the order this case has always used), then
        // the call's own evidence -- but only a SPECIFIC match is taken
        // from the list; see `find_specific_matching_carrier` for why
        // `pure` alone needs that and what it was measured to fix.
        match find_specific_matching_carrier instances cls_name (instance_carrier_candidates def_carrier extra_carriers) {
            Option.some found =>
                match found {
                    Pair.pair carrier ins => resolve_class_method_call_with_instance classes instances dict_env method_name resolved_args orig_head carrier ins extra_carriers,
                },
            Option.none =>
                match def_carrier {
                    Option.some carrier => resolve_class_method_call_with_carrier classes instances dict_env cls_name method_name resolved_args orig_head orig_args carrier extra_carriers,
                    Option.none => resolve_class_method_call_d4_from_args classes instances dict_env def_types cls_name method_name resolved_args orig_head orig_args def_carrier env ctor_owners extra_carriers,
                },
        }
    else resolve_class_method_call_d4_from_args classes instances dict_env def_types cls_name method_name resolved_args orig_head orig_args def_carrier env ctor_owners extra_carriers

/// Every carrier `resolve_class_method_call_d4`'s `pure` case may try, in
/// order: the enclosing def's declared return type first (its documented
/// precedence), then whatever the call's own arguments and expected type
/// revealed.
#[partial]
def instance_carrier_candidates (def_carrier : Option Term) (extra_carriers : List Term) : List Term :=
    List.append (carrier_hint_list def_carrier) extra_carriers

/// `env`/`ctor_owners` are the REAL lexical carrier-inference context
/// (threaded from `resolve_class_call_term`'s own recursive walk), NOT
/// `infer_carrier_from_args`'s own hardcoded-empty ones -- see
/// `2026-08-29-show-show-unresolved-carrier-in-nested-match-arm.md`:
/// `infer_carrier_from_args`'s doc comment claims "there's no lambda-
/// binding context at a call site's own argument position" so an empty
/// env is fine, but that's wrong for a BARE local-variable argument
/// (`Show.show mp`, `mp` a plain `let`-bound local with no class-method
/// call of its own) -- `resolve_class_call_terms` recursing over `args`
/// leaves a bare `Term.var` completely unchanged (it's not itself a
/// class-method call), so by the time we get here it's still just a
/// name, and only the REAL `env` can say what type that name was
/// declared with.
#[partial]
def resolve_class_method_call_d4_from_args (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (def_types : HashMap String Term) (cls_name : NamePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (def_carrier : Option Term) (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (extra_carriers : List Term) : Term :=
    // Was `infer_carrier_from_args_go` (first arg that reveals ANY
    // carrier) feeding a single candidate into a "try it, else class
    // default" two-step -- sound when an arg's own type IS the class's
    // carrier (`Show.show x` -> `x`'s type), but wrong for a method
    // whose FIRST arg(s) are ELEMENT types, not the container the class
    // is actually parameterized over: `FromListLiteral.cons (a : A) (L
    // A) : L A`'s `[1, 2, 3]` desugar (confirmed via `bootstrap compile
    // cli/src/main.mo monad`: `lang/parser/core.mo`'s `op_chars : List
    // String := [...]`) and, once `match_arm_env` (above) could recover
    // `k`'s own type inside `match p { Pair.pair k v => Map.insert k v
    // acc }`, `Map.insert (key:K) (val:V) (m:M K V) : M K V` too --
    // `k`'s carrier (`String`) used to be the FIRST (and only-tried)
    // candidate, matched no `instance Map String`, and silently fell
    // through to the class's own declared DEFAULT carrier (`HashMap`)
    // instead of ever trying `acc`'s real carrier (`BTreeMap`) --
    // confirmed as a real, live regression via `examples/json.mo`:
    // `pairs_to_map_insert` compiled to a call to `Map_HashMap_insert`
    // on a value actually tagged `BTreeMap`, corrupting the tree
    // (`BTreeMap_to_list_asc` later segfaulting on a bogus field read).
    // Fixed by trying EVERY arg's own candidate carrier (`infer_all_
    // carriers_from_args_go`, the same "candidate list, first that
    // actually matches an instance wins" pattern `resolve_dict_arg`'s
    // own `extra_carriers` fallback already uses) against a REAL
    // instance lookup (`find_matching_instance_carrier_any`) before
    // ever falling back to the class's own default -- `k`'s "String"
    // candidate is tried and correctly rejected (no `instance Map
    // String`), and `acc`'s "BTreeMap" candidate (tried next) succeeds.
    // `extra_carriers` is the args-derived candidate list with the call's
    // own expected carrier (if any) appended -- computed once by
    // `resolve_class_method_call`, which is also the only reason this
    // function no longer recomputes it here. Same candidates, same
    // order: with no expectation in hand this is byte-for-byte the
    // previous behavior.
    match find_concrete_matching_carrier_any instances cls_name extra_carriers {
        Option.some found =>
            match found {
                Pair.pair carrier ins => resolve_class_method_call_with_instance classes instances dict_env method_name resolved_args orig_head carrier ins extra_carriers,
            },
        Option.none =>
            if npath_eq cls_name monad_class_name then
                match def_carrier {
                    Option.some carrier => resolve_class_method_call_with_carrier classes instances dict_env cls_name method_name resolved_args orig_head orig_args carrier extra_carriers,
                    Option.none => resolve_class_method_call_d4_default_carrier classes instances dict_env cls_name method_name resolved_args orig_head orig_args extra_carriers,
                }
            else resolve_class_method_call_d4_default_carrier classes instances dict_env cls_name method_name resolved_args orig_head orig_args extra_carriers,
    }

/// Last-resort fallback once neither the call's own args nor (for
/// `Monad`) the enclosing def's declared return type reveal a carrier:
/// the class's own DECLARED DEFAULT type param, if it has one (e.g.
/// `class FromListLiteral (L : Type -> Type := List)` -- `[x, y]`'s
/// desugared `FromListLiteral.cons`/`.empty`, `lang/parser.mo`, has NO
/// carrier-revealing arg of its own: `.empty` has no args at all, and
/// `.cons`'s own element arg says nothing about which COLLECTION type
/// it's being built into). Unlike the `Monad`+`def_carrier` fallback
/// above (an explicit "guessing the enclosing function's own return
/// type is NOT sound in general" tradeoff, restricted to `Monad`
/// specifically), a class's OWN declared default is author-specified,
/// sound BY CONSTRUCTION for every class that declares one -- not a
/// guess. Confirmed load-bearing via direct repro: `std/derive.mo`'s
/// `lens_getter`'s own `[match_arm ...]` (a list literal passed
/// straight as a CONSTRUCTOR argument, `Expr.e_match`'s own `arms`
/// param -- no local var/let-binding's declared type to lean on)
/// otherwise left `FromListLiteral.cons`/`.empty` permanently
/// unresolved, unlike every list literal that DOES sit in a directly
/// type-annotated position.
#[partial]
def resolve_class_method_call_d4_default_carrier (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (cls_name : NamePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (extra_carriers : List Term) : Term :=
    match find_class_by_name classes cls_name {
        Option.none => rebuild_call orig_head resolved_args,
        Option.some cls =>
            match class_default_carrier cls {
                Option.none => rebuild_call orig_head resolved_args,
                Option.some carrier => resolve_class_method_call_with_carrier classes instances dict_env cls_name method_name resolved_args orig_head orig_args carrier extra_carriers,
            },
    }

/// A class's own first declared type param's default value, if any
/// (e.g. `L` in `class FromListLiteral (L : Type -> Type := List)`,
/// `Param.default`). Only ever consulted as the LAST-resort fallback
/// above.
def class_default_carrier (cls : Class) : Option Term :=
    match cls {
        Class.mk _name params _constraints _methods _vis => first_param_default params,
    }

def first_param_default (params : List Param) : Option Term :=
    match params {
        List.empty => Option.none,
        List.cons p _rest => match p { Param.mk _name _typ _mult default_ _attrs => default_ },
    }

#[partial]
def monad_class_name : NamePath :=
    NamePath.npath (List.cons (Identifier.id "Monad") List.empty)

#[partial]
def resolve_class_method_call_with_carrier (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (cls_name : NamePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (carrier : Term) (extra_carriers : List Term) : Term :=
    match find_matching_instance instances cls_name carrier {
        Option.none => rebuild_call orig_head resolved_args,
        Option.some ins => resolve_class_method_call_with_instance classes instances dict_env method_name resolved_args orig_head carrier ins extra_carriers,
    }

#[partial]
def resolve_class_method_call_with_instance (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (carrier : Term) (ins : Instance) (extra_carriers : List Term) : Term :=
    match ins {
        Instance.mk insname ins_cls_name ins_constraints ins_args _ _ _ =>
            // What the matched instance's own head binds: the carrier the
            // call resolved with, walked against the instance's declared
            // args (`List I64` against `(List A)` binds `A := I64`).
            // `resolve_dict_args` needs it to resolve the instance's own
            // constraint against the BOUND variable rather than the whole
            // carrier -- see `carrier_bindings`' own doc comment. The
            // method's own declared signature is appended for the
            // instances whose head names no variable at all
            // (`method_sig_bindings`).
            let bindings := List.append (carrier_bindings (instance_wildcard_names ins) ins_args carrier) (method_sig_bindings classes ins_cls_name method_name carrier) in
            resolve_class_method_call_with_dict_args (instance_module_prefix insname) classes instances dict_env ins_cls_name method_name resolved_args orig_head carrier bindings (emitted_dict_constraints ins method_name) ins_args extra_carriers,
    }

/// The instance constraints whose dictionary parameter the EMITTED
/// method actually carries -- `qualifying_dict_constraints` applied to
/// the very body `add_constraint_dict_params_decls` filters, so that the
/// dict arguments this call site prepends (one per constraint, in
/// constraint order -- `resolve_dict_args`) line up with the mangled
/// def's own leading parameters, count and order both.
///
/// MEASURED: without this, `std/src/map.mo`'s `instance [BOrd K] Map
/// BTreeMap` resolved `let m : BTreeMap I64 String := Map.empty` to
/// `apply_closure1(Map_BTreeMap_empty(), __Dict_BOrd_I64)` -- the
/// instance HAS a constraint, so the call site prepended a dict, but
/// `Map.empty`'s body (`BTreeMap.empty`) references no `BOrd.` and so
/// was emitted with no dict parameter at all. Applying a dict to a
/// nullary constructor segfaults (the driver died with -1), which is how
/// this was found. The same mismatch is systematic, not Map-specific:
/// `instance [BEq K, BEq V] BEq BTreeMap K V`'s own `beq` body is
/// `BTreeMap.beq a b` -- two constraints, no `BEq.` reference, no dict
/// parameters emitted.
///
/// `promote_methods` copies a method's `term` VERBATIM out of the
/// instance decl into the promoted `Def` (only the name and the
/// concatenated constraint list change), and `promote_instance_defs` is
/// non-destructive -- the original `Decl.instance_d` stays in the list
/// scope data is built from -- so reading the body back out of the
/// instance here reads the same term the emission pass scanned, whether
/// or not an earlier pass rewrote infix operators inside it.
///
/// `Option.none` (the instance does not implement this method at all)
/// keeps the unfiltered list: nothing was promoted in that case
/// (`build_dict_fields` fails and `promote_instance` returns
/// `Option.none`), so the mangled name is a dangling global either way --
/// a loud link-time undefined symbol, not a silent miscompile.
#[partial]
def emitted_dict_constraints (ins : Instance) (method_name : Identifier) : List TypeConstraint :=
    match ins {
        Instance.mk _ _ ins_constraints _ _ _ defs =>
            match find_instance_method defs method_name {
                Option.none => ins_constraints,
                Option.some d =>
                    match d {
                        Def.mk {term := body, constraints := own_constraints, ..} =>
                            qualifying_dict_constraints (List.append ins_constraints own_constraints) body,
                    },
            },
    }

#[partial]
def resolve_class_method_call_with_dict_args (prefix : String) (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (cls_name : NamePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (carrier : Term) (bindings : List (Pair Identifier Term)) (ins_constraints : List TypeConstraint) (ins_args : List Term) (extra_carriers : List Term) : Term :=
    match resolve_dict_args classes instances dict_env bindings carrier extra_carriers ins_constraints {
        Option.none => rebuild_call orig_head resolved_args,
        Option.some dict_args =>
            let mangled := mangle_instance_method_name prefix cls_name ins_args method_name in
            // Sentinel, not `Term.var 0` -- same rationale as
            // `build_dict_fields`'s own mangled-method reference just
            // above: a mangled instance-method name is never a real
            // local, at any depth this D4-resolved call ends up embedded
            // at.
            let method_fn_ref := Term.var (0 - 1) (DebugName.named (mangled_to_identifier mangled)) in
            rebuild_call method_fn_ref (List.append dict_args resolved_args),
    }

/// Carrier inference from a call spine's own args -- takes the first
/// one that resolves (see this section's own top doc comment on why
/// this doesn't require every arg to agree).
///
/// Both real callers (`resolve_class_method_call_d4_from_args`,
/// `resolve_ordinary_constrained_call`) now call `infer_carrier_from_args_go`
/// directly with the REAL `env`/`ctor_owners` threaded from
/// `resolve_class_call_term`'s own recursive walk, not an empty one --
/// see `2026-08-29-show-show-unresolved-carrier-in-nested-match-arm.md`.
/// A bare local-variable argument (`Show.show mp`, `mp` a plain
/// `let`-bound local, not itself a class-method call) is left completely
/// UNCHANGED by `resolve_class_call_terms`'s own recursive resolution of
/// `args` -- it's still just a name by the time carrier inference runs,
/// and only the real `env` can say what type that name was declared
/// with. An empty env silently failed to resolve every such call,
/// leaving it as an unrewritten reference that `llc` later rejected as
/// an undefined symbol.
/// Sibling of `infer_carrier_from_args_go` that collects EVERY arg's own
/// inferred carrier, not just the first -- used as the candidate list
/// for a NESTED instance constraint on a type variable different from
/// the outer call's own carrier (e.g. `instance [BOrd K] Map BTreeMap`'s
/// `K`, vs. `Map`'s own carrier `M = BTreeMap`) -- see
/// `resolve_dict_arg`'s own doc comment for the full story. The outer
/// carrier itself is still tried FIRST by `resolve_dict_arg` (the
/// existing, already-correct behavior for the common "same type
/// variable" case); this list is only consulted once that fails.
#[partial]
def infer_all_carriers_from_args_go (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (args : List Term) : List Term :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            match infer_carrier_type env ctor_owners def_types ctor_field_types a {
                Option.some t => List.cons t (infer_all_carriers_from_args_go env ctor_owners def_types ctor_field_types rest),
                Option.none => infer_all_carriers_from_args_go env ctor_owners def_types ctor_field_types rest,
            },
    }

#[partial]
def infer_carrier_from_args_go (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (args : List Term) : Option Term :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            match infer_carrier_type env ctor_owners def_types ctor_field_types a {
                Option.some t => Option.some t,
                Option.none => infer_carrier_from_args_go env ctor_owners def_types ctor_field_types rest,
            },
    }

/// Recognizes a Phase-3-added dict-binding lambda by
/// `dict_param_name`'s own naming scheme, recovering which class it's
/// for.
#[partial]
def dict_binding_class_of (id : Identifier) : Option NamePath :=
    let text := show_identifier id in
    if String.starts_with "__dict_" text
    then Option.some (NamePath.npath (List.cons (Identifier.id (String.drop (String.length "__dict_") text)) List.empty))
    else Option.none

/// Top-level Phase 4 driver -- applies `resolve_class_call_term` (empty
/// env/dict_env: nothing is bound yet at a decl's own top level) to
/// every `Decl.def_d`'s own `.term` (not `.typ` -- a type's own Pi-chain
/// never contains a class-method CALL to resolve, only Phase 3's own
/// dict-parameter Pi's, which this pass doesn't touch).
#[partial]
pub def resolve_class_calls_decls (decl_list : List Decl) : List Decl :=
    let classes := collect_classes decl_list in
    // The instance list every match below reads is the refined one: an
    // instance that writes a type variable in its own args without
    // declaring it names nothing to `term_matches_carrier` otherwise --
    // see `refine_instance_wildcards`' section comment. Refined HERE, at
    // the pass that needs it and that this function's own doc comment
    // documents as running "on the FULL loaded decl graph" (which is what
    // makes `declared_type_names` see every type the program can name),
    // rather than in `collect_instances` itself -- `promote_instance_defs`
    // shares that function and must keep seeing the instance as written.
    let instances := refine_instance_wildcards (declared_type_names decl_list) (collect_instances decl_list) in
    let ctor_owners := collect_ctor_owners decl_list in
    let ctor_field_types := collect_ctor_field_types decl_list in
    let def_constraints := collect_def_constraints decl_list in
    let def_types := collect_def_types decl_list in
    resolve_class_calls_decls_go classes instances ctor_owners ctor_field_types def_constraints def_types decl_list

/// `resolve_class_call_term`'s own resolution chain has a SILENT give-up
/// built in by design (`rebuild_call orig_head resolved_args`, used
/// throughout `resolve_class_method_call_with_carrier`/`_with_dict_args`/
/// `_d4_default_carrier`/`resolve_ordinary_constrained_call` whenever no
/// matching instance/carrier is found) -- it just leaves the ORIGINAL
/// `ClassName.method` reference in the term tree untouched, no error. That
/// silent survivor then gets dot-to-underscore-mangled by codegen into an
/// `@ClassName_method` global reference that was never compiled, caught
/// only by `llc`'s own "undefined value" check many pipeline stages (and,
/// in a real self-compile, minutes) later -- this is what the
/// `Append_append`/`Show_show` bug family (`6cf8da7`, `a47856c`, `855be99`)
/// all turned out to be, each requiring its own manual archaeology session
/// to even FIND which call was unresolved.
///
/// Fail fast instead -- but deliberately NOT inside `resolve_class_calls_
/// decls` itself: that pass runs on the FULL loaded decl graph, before
/// reachability filtering, so validating its own output directly would
/// fail a compile over a bug in dead code the program never actually
/// uses (confirmed via a direct repro: `std/list.mo`'s own unreachable
/// `test_length` def blocked `bootstrap compile cli/src/main.mo monad`,
/// exactly the "any codegen bug anywhere in the whole standard library,
/// reached or not, blocked compiling any program at all" problem
/// `filter_reachable_decls`'s own doc comment says THAT pass exists to
/// avoid). Callers that filter reachability should validate the
/// REACHABLE decls, after `filter_reachable_decls`, not the full ones --
/// see `compile_loaded_modules_to_ir`'s own use of this for the pattern.
///
/// Walk `decl_list` for any surviving `Term.var` that still matches
/// `class_method_ref classes` -- by construction, a successful resolution
/// always REWRITES such a reference to a concrete mangled name (no longer
/// matching `class_method_ref`), so any survivor found here is
/// unambiguously a real "no instance available" failure, reported with
/// the class/method/enclosing-def named directly instead of discovered
/// via a cryptic downstream `llc` error.
///
/// `classes` is taken as its own explicit param, NOT recomputed via
/// `collect_classes decl_list` -- `filter_reachable_decls`'s own output
/// (the intended `decl_list` here, see this def's own doc comment above)
/// contains ONLY `Decl.def_d`/`Decl.inductive_d` entries; `Decl.class_d`
/// is unconditionally dropped (never reachability-filtered at all, since
/// nothing downstream of `resolve_class_calls_decls` needs it), so
/// `collect_classes` on THAT decl_list always finds zero classes,
/// silently turning this whole check into a no-op. Callers must compute
/// `classes` from the PRE-filter decls (`collect_classes dispatched_decls`
/// -- confirmed via a direct repro, the same one that found the dead-code
/// false-positive above).
#[partial]
def validate_no_unresolved_class_calls (classes : List Class) (decl_list : List Decl) : Result String (List Decl) :=
    match find_unresolved_class_calls_decls classes decl_list {
        List.empty => Result.ok decl_list,
        List.cons msg _rest => Result.err msg,
    }

/// Walks every top-level def's own term looking for a `Term.var`
/// reference that still matches `class_method_ref classes` -- see
/// `resolve_class_calls_decls`'s own doc comment for why any such
/// survivor is unambiguously a real unresolved-instance failure.
#[partial]
def find_unresolved_class_calls_decls (classes : List Class) (decl_list : List Decl) : List String :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk {name, typ := _typ, term := term_, constraints := _constraints, attrs := _attrs, vis := _vis, ..} =>
                            let found := find_unresolved_class_calls_term classes term_ List.empty in
                            List.append (format_unresolved_class_calls (name_path_to_str_scope name) found) (find_unresolved_class_calls_decls classes rest),
                    },
                _ => find_unresolved_class_calls_decls classes rest,
            },
    }

#[partial]
def format_unresolved_class_calls (def_name : String) (refs : List ClassMethodRef) : List String :=
    match refs {
        List.empty => List.empty,
        List.cons r rest => List.cons (format_unresolved_class_call def_name r) (format_unresolved_class_calls def_name rest),
    }

#[partial]
def format_unresolved_class_call (def_name : String) (ref : ClassMethodRef) : String :=
    match ref {
        ClassMethodRef.mk cls method_name =>
            match cls {
                Class.mk cname _ _ _ _ =>
                    let cls_name := show_identifier cname in
                    let method_str := show_identifier method_name in
                    let call := String.concat cls_name (String.concat "." method_str) in
                    let prefix := String.concat "no instance found for `" call in
                    let suffix := String.concat "` (needed in `" (String.concat def_name "`)") in
                    String.concat prefix suffix
            }
    }

#[partial]
def find_unresolved_class_calls_term (classes : List Class) (t : Term) (acc : List ClassMethodRef) : List ClassMethodRef := match t {
    Term.var _idx dbg =>
        match dbg {
            DebugName.named id =>
                match class_method_ref classes id {
                    Option.some ref => List.cons ref acc,
                    Option.none => acc,
                },
            DebugName.unnamed => acc,
        },
    Term.lam _dbg typ body => find_unresolved_class_calls_term classes body (find_unresolved_class_calls_term classes typ acc),
    Term.forall _dbg kind body => find_unresolved_class_calls_term classes body (find_unresolved_class_calls_term classes kind acc),
    Term.pi arg ret => find_unresolved_class_calls_term classes ret (find_unresolved_class_calls_term classes arg acc),
    Term.app fun_ arg_ => find_unresolved_class_calls_term classes arg_ (find_unresolved_class_calls_term classes fun_ acc),
    Term.ntv native => find_unresolved_class_calls_native classes native acc,
    Term.con con_ => find_unresolved_class_calls_con classes con_ acc,
    Term.lit lit_ => find_unresolved_class_calls_lit classes lit_ acc,
    Term.type_ _universe => acc,
    Term.hole => acc,
    // Must recurse: an unresolved class call under a located term is still
    // unresolved, and this is what reports it.
    Term.ctx _loc inner => find_unresolved_class_calls_term classes inner acc,
}

#[partial]
def find_unresolved_class_calls_lit (classes : List Class) (l : Literal) (acc : List ClassMethodRef) : List ClassMethodRef := match l {
    Literal.num _n _suffix => acc,
    Literal.flt _text _suffix => acc,
    Literal.str _s => acc,
    Literal.char _c => acc,
    Literal.if_ cond then_ else_ => find_unresolved_class_calls_term classes else_ (find_unresolved_class_calls_term classes then_ (find_unresolved_class_calls_term classes cond acc)),
    Literal.match_ scrutinee cases => find_unresolved_class_calls_cases classes cases (find_unresolved_class_calls_term classes scrutinee acc),
    Literal.struct_lit fields _type_name => find_unresolved_class_calls_struct_fields classes fields acc,
    Literal.struct_update base fields => find_unresolved_class_calls_struct_fields classes fields (find_unresolved_class_calls_term classes base acc),
}

#[partial]
def find_unresolved_class_calls_struct_fields (classes : List Class) (fields : List StructLitField) (acc : List ClassMethodRef) : List ClassMethodRef :=
    match fields {
        List.empty => acc,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value => find_unresolved_class_calls_struct_fields classes rest (find_unresolved_class_calls_term classes value acc),
            }
    }

#[partial]
def find_unresolved_class_calls_cases (classes : List Class) (cases : List MatchCase) (acc : List ClassMethodRef) : List ClassMethodRef := match cases {
    List.empty => acc,
    List.cons c rest =>
        match c {
            MatchCase.mc _name _args body _fp => find_unresolved_class_calls_cases classes rest (find_unresolved_class_calls_term classes body acc),
        },
}

#[partial]
def find_unresolved_class_calls_native (classes : List Class) (n : Native) (acc : List ClassMethodRef) : List ClassMethodRef := match n {
    Native.mk _name _num_args args => find_unresolved_class_calls_opt_list classes args acc,
}

#[partial]
def find_unresolved_class_calls_con (classes : List Class) (c : Con) (acc : List ClassMethodRef) : List ClassMethodRef := match c {
    Con.mk _name _typ_name _num_args args => find_unresolved_class_calls_opt_list classes args acc,
}

#[partial]
def find_unresolved_class_calls_opt_list (classes : List Class) (args : List (Option Term)) (acc : List ClassMethodRef) : List ClassMethodRef := match args {
    List.empty => acc,
    List.cons opt_ rest =>
        match opt_ {
            Option.some t => find_unresolved_class_calls_opt_list classes rest (find_unresolved_class_calls_term classes t acc),
            Option.none => find_unresolved_class_calls_opt_list classes rest acc,
        },
}

/// One ordinary (non-class-method) def's own constraints -- needed so a
/// CALL SITE to a constrained def (e.g. `show_twice 5`, where
/// `show_twice` itself carries `[Show A]`) can also gain the dict
/// argument(s) Phase 3 added a matching PARAMETER for on its
/// definition -- Phase 3 only ever rewrites the definition side; this
/// is the call-site half of the same mechanism, needed for genuine
/// polymorphism (D5) to have anything to actually supply at a call
/// site in the first place.
pub type DefConstraintEntry {
    mk (name : NamePath) (constraints : List TypeConstraint),
}

#[partial]
def collect_def_constraints (decl_list : List Decl) : List DefConstraintEntry :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk {name := dname, constraints, ..} =>
                            match constraints {
                                List.empty => collect_def_constraints rest,
                                List.cons _ _ => List.cons (DefConstraintEntry.mk dname constraints) (collect_def_constraints rest),
                            },
                    },
                _ => collect_def_constraints rest,
            },
    }

#[partial]
def lookup_def_constraints (entries : List DefConstraintEntry) (name : NamePath) : Option (List TypeConstraint) :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                DefConstraintEntry.mk ename constraints =>
                    if npath_eq ename name
                    then Option.some constraints
                    else lookup_def_constraints rest name,
            },
    }

/// Does this already-resolved call's FIRST argument name a dictionary?
/// A true answer means the call's dictionary arguments are ALREADY in
/// its argument list, and `resolve_ordinary_constrained_call` must not
/// supply them a second time.
///
/// There are exactly two names a promoted dictionary is ever bound to --
/// `dict_param_name`'s own `__dict_<Cls>` forwarding parameter (Phase
/// 3/4's D5) and `mangle_instance_dict_name`'s `__Dict_<Cls>_<args>`
/// value (D4) -- and the source language can write NEITHER of them, so
/// a leading argument of that shape can only have been put there by the
/// compiler. The one producer that reaches this pass is the checker's
/// own D4 rewrite (`resolve_class_method_d4`, `lang.typecheck.infer`),
/// which returns `mangled_ref` applied to its resolved dict arguments;
/// every codegen path then runs `resolve_class_calls_decls` over those
/// already-rewritten terms. MEASURED: `std/src/list.mo`'s `BEq (List A)`
/// body -- the checker rewrote its recursive `BEq.beq x_tail y_tail` to
/// `BEq_List_A_beq __dict_BEq_A x_tail y_tail` (correct: the element
/// dictionary, two lists the instance is FOR), and this pass then
/// prepended a SECOND `__dict_BEq_A`, giving the arity-3 def four
/// arguments and handing the tail comparison the element dictionary --
/// `driver exited -1` on the probe, where the un-rewritten p64 build at
/// least answered the empty-list case.
///
/// A source-written call to a constrained def never starts with a
/// dictionary argument -- the dicts are implicit in source and are
/// exactly what this pass exists to add -- so the check costs that case
/// nothing.
///
/// The name is read AFTER its `module::` qualifier: a D4 dict value is
/// minted as `lang.types::__Dict_Similar_Identifier` (`with_module_prefix`
/// in `mangle_instance_dict_name`), so a bare `starts_with "__Dict_"` on
/// the qualified name misses exactly the values this guard exists for --
/// MEASURED: the first version of this guard did, and `sha256_tests.mo`'s
/// `hex_bytes_of_byte 255u8 == [102u8, 102u8]` kept its doubled dictionary.
#[partial]
def arg_is_dict (args : List Term) : Bool :=
    match args {
        List.empty => false,
        List.cons a _ =>
            match term_peel a {
                Term.var _ dbg =>
                    match dbg {
                        DebugName.named id =>
                            let text := unqualify_minted_name (show_identifier id) in
                            Bool.or (String.starts_with "__dict_" text) (String.starts_with "__Dict_" text),
                        DebugName.unnamed => false,
                    },
                _ => false,
            },
    }

/// The part of a compiler-MINTED name after its `module::` qualifier, or
/// the whole name when it has none. Mirrors `lang.module`'s own
/// `unqualify_instance_name` (and `lang.codegen.emit`'s
/// `unqualify_def_name`); kept here rather than imported because
/// `lang.module` is a DEPENDENCY of this file, not the other way round.
#[partial]
pub def unqualify_minted_name (s : String) : String :=
    let idx := find_minted_name_sep s 0 (String.length s) in
    if I64.beq idx (0 - 1) then s else String.slice s (idx + 2) (String.length s - idx - 2)

#[partial]
def find_minted_name_sep (s : String) (i : I64) (n : I64) : I64 :=
    if I64.gt (i + 2) n then (0 - 1)
    else if String.beq (String.slice s i 2) "::" then i
    else find_minted_name_sep s (i + 1) n

/// Resolves a call to an ORDINARY (non-class-method) global whose own
/// def carries constraints (registered in `def_constraints`) -- if
/// found, resolves and prepends the same dict argument(s)
/// `add_constraint_dict_params` (Phase 3) added matching PARAMETERS
/// for, using a carrier inferred from this call's own (already-
/// resolved) args, checking `dict_env` first (D5 forwarding) same as
/// any other dict resolution. A def with no registered constraints (the
/// overwhelmingly common case), one that ALREADY carries its dict
/// arguments (`arg_is_dict`), or one whose dict args can't be resolved
/// passes through completely unchanged -- this must never touch an
/// ordinary, unconstrained call.
#[partial]
def resolve_ordinary_constrained_call (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (def_constraints : List DefConstraintEntry) (def_types : HashMap String Term) (ctor_field_types : List CtorFieldTypes) (id : Identifier) (head : Term) (resolved_args : List Term) (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) : Term :=
    match lookup_def_constraints def_constraints (NamePath.npath (List.cons id List.empty)) {
        Option.none => rebuild_call head resolved_args,
        Option.some constraints =>
            if arg_is_dict resolved_args
            then rebuild_call head resolved_args
            else match infer_carrier_from_args_go env ctor_owners def_types ctor_field_types resolved_args {
                Option.none => rebuild_call head resolved_args,
                Option.some carrier =>
                    // No instance head here (an ordinary constrained DEF call), so no
                    // bindings: `List.empty` keeps the pre-existing whole-carrier order.
                    match resolve_dict_args classes instances dict_env List.empty carrier (infer_all_carriers_from_args_go env ctor_owners def_types ctor_field_types resolved_args) constraints {
                        Option.none => rebuild_call head resolved_args,
                        Option.some dict_args => rebuild_call head (List.append dict_args resolved_args),
                    },
            },
    }

#[partial]
def resolve_class_calls_decls_go (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (ctor_field_types : List CtorFieldTypes) (def_constraints : List DefConstraintEntry) (def_types : HashMap String Term) (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk {name, typ, term := term_, constraints, attrs, vis, params, ..} =>
                            let def_carrier := full_return_carrier typ in
                            let new_term := resolve_class_call_term classes instances ctor_owners def_constraints def_types ctor_field_types List.empty List.empty def_carrier term_ in
                            List.cons (Decl.def_d (Def.mk name typ new_term constraints attrs vis params)) (resolve_class_calls_decls_go classes instances ctor_owners ctor_field_types def_constraints def_types rest),
                    },
                _ => List.cons d (resolve_class_calls_decls_go classes instances ctor_owners ctor_field_types def_constraints def_types rest),
            },
    }

/// Strip EVERY leading `Term.pi`/`Term.forall` binder (unlike
/// `return_type_after_n_args`, which strips a fixed `n`) -- used to find
/// a top-level def's own ULTIMATE codomain regardless of arity, for
/// `full_return_carrier`'s do-notation fallback (see
/// `resolve_class_call_term`'s doc comment).
#[partial]
pub def strip_all_leading_binders (typ : Term) : Term :=
    match typ {
        Term.forall _ _ body => strip_all_leading_binders body,
        Term.pi _ ret => strip_all_leading_binders ret,
        _ => typ,
    }

/// A top-level def's own declared return-type carrier, e.g. `IO` for a
/// def declared `: IO Unit` -- see `resolve_class_call_term`'s doc
/// comment for why this is the right (and only sound, restricted to the
/// `Monad` class) D4 fallback for a do-notation `bind`/`pure` call
/// whose own args don't reveal a carrier.
///
/// With its ARGUMENTS, normalized head and all (`State I64 I64` stays
/// applied, head bare) -- `carrier_with_normalized_head`, the same shape
/// every other carrier candidate carries. It used to be reduced to the
/// bare head, which matched (the bare-carrier arm of
/// `term_matches_carrier` reads an applied arg's head against it) but
/// could never BIND anything: `method_carrier_hint` projects this type
/// through the callee's own class signature, and
/// `bind_term_vars [M, A] (M A) (var State)` binds nothing (an applied
/// shape against a bare actual), so no projection was possible at all.
/// `State I64 I64` binds `M := State I64` -- the carrier the class's own
/// `M A` codomain names -- which is what `examples/state_monad.mo`'s
/// `MonadState.modify_get` needs.
#[partial]
def full_return_carrier (typ : Term) : Option Term :=
    let stripped : Term := strip_all_leading_binders typ in
    match type_head_name_local stripped {
        Option.some carrier_name => Option.some (carrier_with_normalized_head (show_identifier carrier_name) stripped),
        Option.none => Option.none,
    }

// --- scope_resolve_instance: find concrete instance by class name ---

def scope_resolve_instance (class_name : NamePath) (instance_key : InstanceKey) (s : Scope) : Result ScopeError Instance :=
    let g : ScopeData := scope_globals s in
    let candidates : List Instance := scope_instance_candidates g class_name in
    first_matching_instance candidates instance_key

def scope_instance_candidates (sd : ScopeData) (cls_name : NamePath) : List Instance :=
    find_instances_by_class sd.instances cls_name

def find_instances_by_class (insts : List ScopeInstance) (cls_name : NamePath) : List Instance :=
    match insts {
        List.empty => List.empty,
        List.cons si rest =>
            match si {
                mk cn ins_list =>
                    if npath_eq cn cls_name
                    then list_append ins_list (find_instances_by_class rest cls_name)
                    else find_instances_by_class rest cls_name
            }
    }

def first_matching_instance (candidates : List Instance) (key : InstanceKey) : Result ScopeError Instance :=
    match candidates {
        List.empty => err (ScopeError.instance_not_found key),
        List.cons ins rest =>
            if instance_key_matches ins key
            then ok ins
            else first_matching_instance rest key
    }

def instance_key_matches (ins : Instance) (key : InstanceKey) : Bool :=
    match ins {
        mk _ cls_name constraints ins_args _ _ _ =>
            match key {
                mk key_cls _ key_args =>
                    if Similar.similar cls_name key_cls
                    then term_args_match ins_args key_args
                    else false
            }
    }

/// Compare instance type args (List Term) against key type args (List Param).
/// Extracts type_ field from each Param and uses term_similar_pairwise.
def term_args_match (ins_args : List Term) (key_args : List Param) : Bool :=
    match ins_args {
        List.empty =>
            match key_args {
                List.empty => true,
                _ => false,
            },
        List.cons t rest_ins =>
            match key_args {
                List.empty => false,
                List.cons p rest_key =>
                    match p {
                        mk _ p_typ _ _ _ =>
                            if Similar.similar t p_typ
                            then term_args_match rest_ins rest_key
                            else false,
                    },
            },
    }

// --- list_append helper (prelude List.append is curried) ---
//
// `ys`-empty short-circuit, checked once rather than per recursive step
// -- see `lang/module.mo`'s own `list_append`/`merge_instances` doc
// comment for why this matters on `merge_scope_data`'s hot path.

def list_append {A : Type} (xs : List A) (ys : List A) : List A :=
    match ys {
        List.empty => xs,
        List.cons _ _ => list_append_go xs ys
    }

def list_append_go {A : Type} (xs : List A) (ys : List A) : List A :=
    match xs {
        List.empty => ys,
        List.cons x rest => List.cons x (list_append_go rest ys)
    }

// Exports
// infix (++) := list_append

// Regression test for the `unresolved global: Map.empty` evaluator
// limitation documented on `lang/types.mo`'s `use std.map {}` — verifies
// `scope_data_empty`'s `def_refs := Map.empty` actually resolves and
// round-trips through `scope_data_find_def` at runtime.
#[test]
def test_scope_data_empty_lookup_misses : Bool :=
    let sd := scope_data_empty in
    match scope_data_find_def sd (NamePath.npath List.empty) {
        Option.some _ => false,
        Option.none => true
    }

// Regression test for `scope_data_find_all_inductives_by_constructor`'s
// POSITIONAL `ScopeData` pattern: it binds one variable per field, so
// adding a field to `ScopeData` (`def_sigs` was the most recent) without
// widening that pattern makes every call fail at RUNTIME with "expected
// N constructor fields, got N+1" -- an abort with no location and no
// def name, which took down the whole self-hosted `check lang/scope.mo`
// (and `lang/module.mo`) run rather than reporting a diagnostic. No
// static arity check catches it: `mk _ _ _ x _ _ _ _ _` typechecks fine
// against a 10-field struct. This test calls the function against a
// REAL `ScopeData` (not just constructing one), which is exactly what
// the crashing path did.
#[test]
def test_find_all_inductives_by_constructor_matches_scope_data_arity : Bool :=
    let ind_name : NamePath := NamePath.npath (List.cons (Identifier.id "Pair2") List.empty) in
    let con_name : NamePath := NamePath.npath (List.cons (Identifier.id "both") List.empty) in
    let cn : InductConstructor := InductConstructor.mk con_name List.empty (Term.type_ 1) in
    let ind : Inductive := Inductive.mk ind_name List.empty (Term.type_ 1)
        (List.cons cn List.empty) List.empty Visibility.package_private in
    let sd : ScopeData := scope_data_add_inductive scope_data_empty ind in
    match scope_data_find_all_inductives_by_constructor sd con_name {
        List.cons _ _ => true,
        List.empty => false,
    }

// Regression tests for `build_scope_one_decl`'s wildcard arm covering
// the 3 macro-expansion-phase `Decl` variants (def_macro_d/decl_gen_d/
// macro_call_d) — this codebase has no static match-exhaustiveness
// check, so a missing arm here would silently typecheck fine and only
// crash at RUNTIME the instant a real decl of one of these variants
// reached this function (which real corpus `.mo` files now do, once
// they successfully parse). These prove the fix is real: each
// constructs a real value of the new variant and confirms
// `build_scope_one_decl` handles it (a no-op — scope stays empty)
// without crashing.

def dummy_macro_call_decl : Decl :=
    let name : Identifier := Identifier.id "foo" in
    let no_args : List Term := List.empty in
    Decl.macro_call_d name no_args

def dummy_def_macro_decl : Decl :=
    let np : NamePath := NamePath.npath (List.cons (Identifier.id "foo") List.empty) in
    let no_constraints : List TypeConstraint := List.empty in
    let no_attrs : List Attribute := List.empty in
    Decl.def_macro_d (Def.mk np Term.hole Term.hole no_constraints no_attrs Visibility.package_private List.empty)

def dummy_decl_gen_decl : Decl :=
    let np : NamePath := NamePath.npath (List.cons (Identifier.id "foo") List.empty) in
    let no_params : List Param := List.empty in
    let no_decls : List Decl := List.empty in
    let no_attrs : List Attribute := List.empty in
    Decl.decl_gen_d np no_params no_decls no_attrs

#[test]
def test_build_scope_one_decl_macro_call_d_is_noop : Bool :=
    let sd := scope_data_empty in
    let path : ModulePath := ModulePath.mp List.empty in
    let sd2 := build_scope_one_decl dummy_macro_call_decl path sd in
    match scope_data_find_def sd2 (NamePath.npath (List.cons (Identifier.id "foo") List.empty)) {
        Option.some _ => false,
        Option.none => true
    }

#[test]
def test_build_scope_one_decl_def_macro_d_is_noop : Bool :=
    let sd := scope_data_empty in
    let path : ModulePath := ModulePath.mp List.empty in
    let sd2 := build_scope_one_decl dummy_def_macro_decl path sd in
    match scope_data_find_def sd2 (NamePath.npath (List.cons (Identifier.id "foo") List.empty)) {
        Option.some _ => false,
        Option.none => true
    }

#[test]
def test_build_scope_one_decl_decl_gen_d_is_noop : Bool :=
    let sd := scope_data_empty in
    let path : ModulePath := ModulePath.mp List.empty in
    let sd2 := build_scope_one_decl dummy_decl_gen_decl path sd in
    match scope_data_find_def sd2 (NamePath.npath (List.cons (Identifier.id "foo") List.empty)) {
        Option.some _ => false,
        Option.none => true
    }

// --- Infix operator resolution tests ---

def dummy_infixes : List Infix :=
    let plus : Infix := { operator := Operator.operator "+", name := NamePath.npath (List.cons (Identifier.id "I64") (List.cons (Identifier.id "add") List.empty)) } in
    List.cons plus List.empty

#[test]
def test_lookup_infix_found : Bool :=
    match lookup_infix dummy_infixes "+" {
        Option.some target => String.beq (show_name_path target) "I64.add",
        Option.none => false,
    }

#[test]
def test_lookup_infix_not_found : Bool :=
    match lookup_infix dummy_infixes "==" {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_resolve_infix_term_bare_op_var : Bool :=
    let op_var : Term := Term.var 0 (DebugName.named (Identifier.id "+")) in
    match resolve_infix_term dummy_infixes op_var {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => String.beq (show_identifier id) "I64.add",
                DebugName.unnamed => false,
            },
        _ => false,
    }

/// The actual shape `expr_climb_op_rhs_expr` produces for `n + 1`:
/// `app (app (var "+") n) one`. Only the operator var's own name
/// should change; `n`/`one` pass through untouched (structural
/// recursion via `term_map_children`).
#[test]
def test_resolve_infix_term_full_application : Bool :=
    let op_var : Term := Term.var 0 (DebugName.named (Identifier.id "+")) in
    let n_var : Term := Term.var 0 (DebugName.named (Identifier.id "n")) in
    let one_lit : Term := Term.lit (Literal.num 1 NumSuffix.i64) in
    let combined : Term := Term.app (Term.app op_var n_var) one_lit in
    match resolve_infix_term dummy_infixes combined {
        Term.app fun_outer arg_outer =>
            match arg_outer {
                Term.lit _ =>
                    match fun_outer {
                        Term.app fun_inner arg_inner =>
                            (match fun_inner {
                                Term.var _ dbg =>
                                    match dbg {
                                        DebugName.named id => String.beq (show_identifier id) "I64.add",
                                        DebugName.unnamed => false,
                                    },
                                _ => false,
                            }) &&
                            (match arg_inner {
                                Term.var _ dbg2 =>
                                    match dbg2 {
                                        DebugName.named id2 => String.beq (show_identifier id2) "n",
                                        DebugName.unnamed => false,
                                    },
                                _ => false,
                            }),
                        _ => false,
                    },
                _ => false,
            },
        _ => false,
    }

/// An ordinary named var that just happens NOT to be a registered
/// operator (e.g. a real function called "n") passes through
/// unchanged, not rewritten.
#[test]
def test_resolve_infix_term_non_operator_var_unchanged : Bool :=
    let n_var : Term := Term.var 0 (DebugName.named (Identifier.id "n")) in
    match resolve_infix_term dummy_infixes n_var {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => String.beq (show_identifier id) "n",
                DebugName.unnamed => false,
            },
        _ => false,
    }

#[test]
def test_collect_infixes_finds_declared_operator : Bool :=
    let op := Operator.operator "+" in
    let target := NamePath.npath (List.cons (Identifier.id "I64") (List.cons (Identifier.id "add") List.empty)) in
    let decl_list : List Decl := List.cons (Decl.infix_d op target Visibility.package_private) List.empty in
    match collect_infixes decl_list {
        List.cons inf rest =>
            (match inf { Infix.mk o _ => String.beq (show_operator o) "+" }) &&
            (match rest { List.empty => true, List.cons _ _ => false }),
        List.empty => false,
    }

#[test]
def test_collect_infixes_ignores_other_decls : Bool :=
    let decl_list : List Decl := List.cons dummy_macro_call_decl List.empty in
    match collect_infixes decl_list {
        List.empty => true,
        List.cons _ _ => false,
    }

#[test]
def test_resolve_infix_decls_rewrites_def_body : Bool :=
    let op_var : Term := Term.var 0 (DebugName.named (Identifier.id "+")) in
    let n_var : Term := Term.var 0 (DebugName.named (Identifier.id "n")) in
    let one_lit : Term := Term.lit (Literal.num 1 NumSuffix.i64) in
    let body : Term := Term.app (Term.app op_var n_var) one_lit in
    let name : NamePath := NamePath.npath (List.cons (Identifier.id "helper") List.empty) in
    let d := Def.mk name Term.hole body List.empty List.empty Visibility.package_private List.empty in
    let decl_list : List Decl := List.cons (Decl.def_d d) List.empty in
    match resolve_infix_decls dummy_infixes decl_list {
        List.cons resolved_decl _ =>
            match resolved_decl {
                Decl.def_d resolved_def =>
                    match resolved_def {
                        Def.mk {term := resolved_body, ..} =>
                            match resolved_body {
                                Term.app fun_outer _ =>
                                    match fun_outer {
                                        Term.app fun_inner _ =>
                                            match fun_inner {
                                                Term.var _ dbg =>
                                                    match dbg {
                                                        DebugName.named id => String.beq (show_identifier id) "I64.add",
                                                        DebugName.unnamed => false,
                                                    },
                                                _ => false,
                                            },
                                        _ => false,
                                    },
                                _ => false,
                            },
                    },
                _ => false,
            },
        List.empty => false,
    }

// --- Phase 2 (dictionary-passing plan) tests ---

/// Fixture: `class BEq A { def beq : A -> A -> Bool }`.
#[partial]
def dummy_beq_class : Class :=
    let a_param := param_many (Identifier.id "A") (Term.type_ 1) in
    let beq_method := ClassDef.mk (Identifier.id "beq") Term.hole Option.none in
    Class.mk (Identifier.id "BEq") (List.cons a_param List.empty) List.empty
        (List.cons beq_method List.empty) Visibility.package_private

/// Fixture: `instance BEq Bool { def beq := <true_body> }`.
#[partial]
def dummy_beq_bool_instance : Instance :=
    let cls_name := NamePath.npath (List.cons (Identifier.id "BEq") List.empty) in
    let bool_arg := Term.var 0 (DebugName.named (Identifier.id "Bool")) in
    let beq_name := NamePath.npath (List.cons (Identifier.id "beq") List.empty) in
    let true_body := Term.var 0 (DebugName.named (Identifier.id "true")) in
    let beq_def := Def.mk beq_name Term.hole true_body List.empty List.empty Visibility.package_private List.empty in
    Instance.mk (Identifier.id "_") cls_name List.empty (List.cons bool_arg List.empty)
        Visibility.package_private List.empty (List.cons beq_def List.empty)

#[test]
def test_promote_instance_defs_mangled_method_name : Bool :=
    let decl_list := List.cons (Decl.class_d dummy_beq_class) (List.cons (Decl.instance_d dummy_beq_bool_instance) List.empty) in
    let promoted := promote_instance_defs decl_list in
    decl_list_has_def_named promoted "BEq_Bool_beq"

#[test]
def test_promote_instance_defs_dict_value_name : Bool :=
    let decl_list := List.cons (Decl.class_d dummy_beq_class) (List.cons (Decl.instance_d dummy_beq_bool_instance) List.empty) in
    let promoted := promote_instance_defs decl_list in
    decl_list_has_def_named promoted "__Dict_BEq_Bool"

#[test]
def test_promote_instance_defs_is_additive : Bool :=
    let decl_list := List.cons (Decl.class_d dummy_beq_class) (List.cons (Decl.instance_d dummy_beq_bool_instance) List.empty) in
    let promoted := promote_instance_defs decl_list in
    // The original instance_d decl stays in place -- promotion is
    // additive, not a rewrite.
    decl_list_has_instance_named promoted "BEq"

#[test]
def test_promote_instance_defs_missing_method_skips_instance : Bool :=
    // A class declaring TWO methods, an instance only implementing one
    // -- promote_instance's own Option.none path (build_dict_fields
    // finds a missing method) should skip this instance entirely
    // (neither its dict value nor its one real method gets promoted),
    // not half-emit a broken dictionary.
    let show_method := ClassDef.mk (Identifier.id "show") Term.hole Option.none in
    let extra_method := ClassDef.mk (Identifier.id "extra") Term.hole Option.none in
    let cls := Class.mk (Identifier.id "Show") List.empty List.empty
        (List.cons show_method (List.cons extra_method List.empty)) Visibility.package_private in
    let cls_name := NamePath.npath (List.cons (Identifier.id "Show") List.empty) in
    let show_name := NamePath.npath (List.cons (Identifier.id "show") List.empty) in
    let show_def := Def.mk show_name Term.hole (mk_i64_dummy 1) List.empty List.empty Visibility.package_private List.empty in
    let ins := Instance.mk (Identifier.id "_") cls_name List.empty List.empty
        Visibility.package_private List.empty (List.cons show_def List.empty) in
    let decl_list := List.cons (Decl.class_d cls) (List.cons (Decl.instance_d ins) List.empty) in
    let promoted := promote_instance_defs decl_list in
    not (decl_list_has_def_named promoted "Show_show") && not (decl_list_has_def_named promoted "__Dict_Show")

#[partial]
def mk_i64_dummy (n : I64) : Term := Term.lit (Literal.num n NumSuffix.i64)

#[partial]
def decl_list_has_def_named (decl_list : List Decl) (name : String) : Bool :=
    match decl_list {
        List.empty => false,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk {name := dname, ..} =>
                            if String.beq (name_path_to_str_scope dname) name
                            then true
                            else decl_list_has_def_named rest name,
                    },
                _ => decl_list_has_def_named rest name,
            },
    }

#[partial]
def decl_list_has_instance_named (decl_list : List Decl) (cls_str : String) : Bool :=
    match decl_list {
        List.empty => false,
        List.cons d rest =>
            match d {
                Decl.instance_d ins =>
                    match ins {
                        Instance.mk _ cls_name _ _ _ _ _ =>
                            if String.beq (show_name_path cls_name) cls_str
                            then true
                            else decl_list_has_instance_named rest cls_str,
                    },
                _ => decl_list_has_instance_named rest cls_str,
            },
    }

/// A bare `module_path_to_str`-equivalent local to scope.mo (that
/// function lives in lang/codegen/emit.mo, not imported here) --
/// single-segment only, matching every name `mangle_instance_*_name`
/// ever produces.
#[partial]
def name_path_to_str_scope (np : NamePath) : String :=
    show_name_path np

// --- Phase 3 (dictionary-passing plan) tests ---

#[test]
def test_add_constraint_dict_params_adds_pi_and_lam : Bool :=
    // def show_twice [Show A] (x : A) : String := Show.show x
    let show_call := Term.app (Term.var 1 (DebugName.named (Identifier.id "Show.show"))) (Term.var 0 (DebugName.named (Identifier.id "x"))) in
    let orig_term := Term.lam (DebugName.named (Identifier.id "x")) Term.hole show_call in
    let orig_typ := Term.pi Term.hole (Term.type_ 1) in
    let constraint := TypeConstraint.mk (NamePath.npath (List.cons (Identifier.id "Show") List.empty)) (List.cons (Identifier.id "A") List.empty) in
    let d := Def.mk (NamePath.npath (List.cons (Identifier.id "show_twice") List.empty)) orig_typ orig_term
        (List.cons constraint List.empty) List.empty Visibility.package_private List.empty in
    let d2 := add_constraint_dict_params d in
    match d2 {
        Def.mk {typ := new_typ, term := new_term, ..} =>
            match new_typ {
                Term.pi _ rest_typ => Similar.similar rest_typ orig_typ,
                _ => false,
            } &&
            match new_term {
                Term.lam _ _ rest_term => Similar.similar rest_term orig_term,
                _ => false,
            },
    }

#[test]
def test_add_constraint_dict_params_skips_unreferenced_constraint : Bool :=
    // A [Show A] constraint whose body never actually calls Show.show
    // -- no dict param should be added (a phantom/unused constraint).
    let unrelated_body := Term.lit (Literal.num 42 NumSuffix.i64) in
    let constraint := TypeConstraint.mk (NamePath.npath (List.cons (Identifier.id "Show") List.empty)) (List.cons (Identifier.id "A") List.empty) in
    let d := Def.mk (NamePath.npath (List.cons (Identifier.id "unrelated") List.empty)) (Term.type_ 1) unrelated_body
        (List.cons constraint List.empty) List.empty Visibility.package_private List.empty in
    let d2 := add_constraint_dict_params d in
    match d2 {
        Def.mk {typ := new_typ, term := new_term, ..} =>
            Similar.similar new_typ (Term.type_ 1) && Similar.similar new_term unrelated_body,
    }

#[test]
def test_def_references_class_true_for_dotted_var : Bool :=
    let t := Term.app (Term.var 0 (DebugName.named (Identifier.id "Show.show"))) (Term.var 1 (DebugName.named (Identifier.id "x"))) in
    def_references_class "Show" t

#[test]
def test_def_references_class_false_for_unrelated_var : Bool :=
    let t := Term.var 0 (DebugName.named (Identifier.id "I64.add")) in
    not (def_references_class "Show" t)

// Regression test for `last_segment_of`'s dotted-single-segment gap: a
// def declared with an already-qualified own name (`def IO.println (...)`)
// parses to a ONE-element ModulePath whose sole Identifier's TEXT is
// "IO.println" (`def_to_decl`, lang/parser.mo), not two separate
// ModulePath segments -- `last_segment_of` must split on the trailing
// '.' inside that single segment too, or `lookup_def_type`'s carrier-
// inference caller silently fails to match a bare "println" query
// against it, exactly the bug that left do-notation's `Monad.bind`
// unresolved over a call to a native/qualified-name def like
// `IO.println` (undefined `@Monad_bind` at link time).
#[test]
def test_last_segment_splits_dotted_single_segment_name : Bool :=
    let mp := NamePath.npath (List.cons (Identifier.id "IO.println") List.empty) in
    Similar.similar (last_segment mp) (Identifier.id "println")

#[test]
def test_last_segment_leaves_undotted_single_segment_name_unchanged : Bool :=
    let mp := NamePath.npath (List.cons (Identifier.id "greet") List.empty) in
    Similar.similar (last_segment mp) (Identifier.id "greet")

#[test]
def test_lookup_def_type_finds_dotted_own_name_def_by_bare_query : Bool :=
    let println_typ := Term.pi (Term.var 0 (DebugName.named (Identifier.id "String")))
        (Term.app (Term.var 0 (DebugName.named (Identifier.id "IO"))) (Term.var 0 (DebugName.named (Identifier.id "Unit")))) in
    let dname : NamePath := NamePath.npath (List.cons (Identifier.id "IO.println") List.empty) in
    let d : Def := {
        name := dname,
        typ := println_typ,
        term := Term.hole,
        constraints := List.empty,
        attrs := List.empty,
        vis := Visibility.pub_,
        params := List.empty,
    } in
    // Goes through `collect_def_types` rather than hand-building the
    // table: the bare-query answer depends on the builder registering
    // each def under its last segment as well as its full dotted name,
    // so testing the pair together is what actually covers the
    // behaviour this test is named for.
    match lookup_def_type (collect_def_types (List.cons (Decl.def_d d) List.empty)) (Identifier.id "println") {
        Option.some _ => true,
        Option.none => false,
    }

// Regression test for `infer_carrier_type`'s `Literal.if_` gap: the
// self-hosted test driver's own synthesized summary line chains
// `+`/`HAdd.add` over TWO if-expression operands
// (`synth_sum_expr`, lang/codegen/test_driver.mo:
// `(if test_one then 1 else 0) + (if test_two then 1 else 0)`) --
// `literal_carrier_type` only covers bare `num`/`str` literals, so
// this fell through to `None`, leaving `HAdd.add` unresolved and
// naively dot-to-underscore-renamed at codegen into an undefined
// `@HAdd_add` symbol (confirmed via direct repro, `monad test` on a
// file with 2+ `#[test]` defs).
#[test]
def test_infer_carrier_type_recurses_into_if_branches : Bool :=
    let if_term := Term.lit (Literal.if_ (Term.var 0 (DebugName.named (Identifier.id "cond")))
        (Term.lit (Literal.num 1 NumSuffix.i64)) (Term.lit (Literal.num 0 NumSuffix.i64))) in
    match infer_carrier_type List.empty List.empty str_map_empty List.empty if_term {
        Option.some _ => true,
        Option.none => false,
    }

#[test]
def test_infer_carrier_type_if_branch_none_falls_through_to_else : Bool :=
    // THEN branch is a bare bound var with no local type (uninformative);
    // carrier must still be found from the ELSE branch.
    let if_term := Term.lit (Literal.if_ (Term.var 0 (DebugName.named (Identifier.id "cond")))
        (Term.var 1 (DebugName.named (Identifier.id "uninformative"))) (Term.lit (Literal.str "x"))) in
    match infer_carrier_type List.empty List.empty str_map_empty List.empty if_term {
        Option.some _ => true,
        Option.none => false,
    }

#[test]
def test_bare_ctor_name_splits_dotted_and_double_colon : Bool :=
    Similar.similar (bare_ctor_name (Identifier.id "Option.some")) (Identifier.id "some")
    && Similar.similar (bare_ctor_name (Identifier.id "prelude::Option::some")) (Identifier.id "some")
    && Similar.similar (bare_ctor_name (Identifier.id "some")) (Identifier.id "some")

// Regression tests for the class-side hint channel's own variable set
// (`class_method_var_names` / `collect_recurring_domain_names`).
//
// `class Foldable (T : Type -> Type) { def foldl (f : B -> A -> B) (z :
// B) (t : T A) : B }` declares its accumulator type `B` as a BARE domain
// -- it is never an argument applied to a class parameter, so the walk
// that keyed on class parameters alone never put it in the wildcard set,
// and `sig_arg_bindings` (which binds only names it recognizes as
// variables) could not solve it from the call's own `0` argument. The
// lambda's accumulator binder then stayed the leaked signature variable
// `B`; carrier inference read `B` off it; `B` matched the prelude's
// wildcard-headed `instance [HAdd A A A] Add A`; and the emitted
// dictionary self-recursed (`HAdd_A_A_A_add (__Dict_Add_A ())`) until the
// driver died. Measured end to end: `init/src/foldable_tests.mo` and
// `init/src/foldable_tests_fold.mo` went from `driver exited -1` to
// 24/24, and the emitted call now carries `number::__Dict_Add_I64`.

/// A bare named type variable in a declared type -- see `foldl_hint_sig`.
def hint_var (s : String) : Term :=
    Term.var 0 (DebugName.named (Identifier.id s))

/// `Foldable.foldl`'s own class-side signature, written in the class
/// parameter `T` applied to the method's own variables: `(B -> A -> B) ->
/// B -> T A -> B`.
def foldl_hint_sig : Term :=
    Term.pi (Term.pi (hint_var "B") (Term.pi (hint_var "A") (hint_var "B")))
        (Term.pi (hint_var "B") (Term.pi (Term.app (hint_var "T") (hint_var "A")) (hint_var "B")))

#[test]
def test_final_result_type_peels_the_pi_chain : Bool :=
    match final_result_type foldl_hint_sig {
        Term.var _ dbg => match dbg {
            DebugName.named id => Similar.similar id (Identifier.id "B"),
            DebugName.unnamed => false,
        },
        _ => false,
    }

#[test]
def test_collect_recurring_domain_names_finds_the_bare_accumulator : Bool :=
    id_member (Identifier.id "B") (collect_recurring_domain_names foldl_hint_sig)

#[test]
def test_collect_recurring_domain_names_skips_a_concrete_domain : Bool :=
    // `Path` stands alone as a domain but recurs nowhere else in the
    // signature -- it names a TYPE, not a parameter (`def parse (s :
    // Path) : A`), and binding it would rewrite the parameter's own
    // declared type from whatever a caller's argument happened to infer.
    let sig : Term := Term.pi (hint_var "Path") (hint_var "A") in
    Bool.not (id_member (Identifier.id "Path") (collect_recurring_domain_names sig))

#[test]
def test_class_method_var_names_includes_bare_domains : Bool :=
    let params : List Param := List.cons (Param.mk (Identifier.id "T") Term.hole Multiplicity.many Option.none List.empty) List.empty in
    let no_constraints : List TypeConstraint := List.empty in
    let no_methods : List ClassDef := List.empty in
    let cls : Class := Class.mk (Identifier.id "Foldable") params no_constraints no_methods Visibility.package_private in
    let names : List Identifier := class_method_var_names cls foldl_hint_sig in
    // `T` from the class's own parameters, `A` from `T A`, `B` from the
    // bare accumulator domain.
    id_member (Identifier.id "T") names
    && id_member (Identifier.id "A") names
    && id_member (Identifier.id "B") names


// --- Qualified-name re-split (`split_qualified_identifier`) ---
//
// `lower_parse.mo` flattens a parsed `NameRef.nqn` to a `DebugName`
// string and every checker call site rebuilds it as a bare `nid`, so
// `resolve_name_in_scope`'s `nqn` arm was unreachable and every
// qualified reference reported `unknown variable`. These pin the
// recovery that makes that arm live.

#[test]
def test_split_qualified_simple : Bool :=
    match split_qualified_identifier (Identifier.id "std::process::process_id") {
        Option.some qn =>
            String.beq (show_module_path qn.qmod) "std.process"
                && String.beq (show_name_path qn.qname) "process_id",
        Option.none => false,
    }

/// The NAME half may itself be dotted (`IO.println` is how std declares
/// most of its defs), and it must survive intact -- splitting on the
/// last separator of ANY kind would cut it down to `println`.
#[test]
def test_split_qualified_keeps_dotted_name_half : Bool :=
    match split_qualified_identifier (Identifier.id "std::io::IO.println") {
        Option.some qn =>
            String.beq (show_module_path qn.qmod) "std.io"
                && String.beq (show_name_path qn.qname) "IO.println",
        Option.none => false,
    }

/// A bare name has no `::` and must not be mistaken for a qualified one.
#[test]
def test_split_qualified_bare_is_none : Bool :=
    match split_qualified_identifier (Identifier.id "process_id") {
        Option.some _ => false,
        Option.none => true,
    }

/// A compiler-MINTED name (`qualify.mo`'s `qualified_def_name_str`) has a
/// DOTTED module half, unlike a source spelling's `::`-joined one. Both
/// must recover the same `QualifiedName`, since after this branch the
/// parse lowering renders references in the minted convention too.
#[test]
def test_split_qualified_accepts_minted_dotted_module : Bool :=
    match split_qualified_identifier (Identifier.id "std.process::process_id") {
        Option.some qn =>
            String.beq (show_module_path qn.qmod) "std.process"
                && String.beq (show_name_path qn.qname) "process_id",
        Option.none => false,
    }

/// The lowering now renders references in the DEF-side convention, whose
/// module half is DOTTED (`std.process::process_id`). Splitting that half
/// on `::` yields one segment, but `show_module_path` re-joins segments
/// with `.`, so the rendered comparison in `find_def_by_module_and_name`
/// still matches -- this pins that equivalence rather than leaving it to
/// luck.
#[test]
def test_split_qualified_module_renders_back : Bool :=
    match split_qualified_identifier (Identifier.id "std.process::process_id") {
        Option.some qn => String.beq (show_module_path qn.qmod) "std.process",
        Option.none => false,
    }

/// End-to-end of the `nid` arm: a flattened qualified reference, in the
/// exact DEF-side spelling the parse lowering now emits, must resolve
/// through the re-split when the def's own registered name is bare.
#[test]
def test_nid_arm_resolves_flattened_qualified : Bool :=
    let mod_path : ModulePath := ModulePath.mp
        (List.cons (Identifier.id "std") (List.cons (Identifier.id "process") List.empty)) in
    let def_name : NamePath := NamePath.npath (List.cons (Identifier.id "process_id") List.empty) in
    let def_entry : ScopeDef := {
        name := def_name,
        module := mod_path,
        sig := Term.hole,
        body := Term.hole,
        vis := Visibility.package_private,
    } in
    let sd : ScopeData := scope_data_add_def scope_data_empty def_entry in
    let s : Scope := {
        module_id := ModulePath.mp (List.cons (Identifier.id "Main") List.empty),
        scope := sd,
        parent := Option.none,
    } in
    match resolve_name_in_scope (NameRef.nid (Identifier.id "std.process::process_id")) s {
        Result.ok _ => true,
        Result.err _ => false,
    }
