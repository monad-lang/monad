use lang.types {
  Class, ClassDef, Decl, Def, DebugName, Identifier, InductConstructor, Inductive,
  Infix, Instance, InstanceKey, LoadedModules, LocalScope, LocalVar, Module,
  ModulePath, NameRef, Operator, Param, Scope, ScopeClassDef, ScopeData, ScopeDef,
  ScopeError, ScopeInstance, Similar, Struct, StructField, Term, class_d,
  class_not_found, def_d, hole, id, inductive_d, inductive_not_found, infix_d,
  instance_d, instance_not_found, mk, mp, name, name_not_found, nid, nmp, nop,
  open_d, scoped_open_d, struct_d, type_, use_d,
}
use lang.typecheck.macro_expand {term_map_children}
// `ScopeData.def_refs` is a `std.map` `HashMap ModulePath ScopeDef` — see
// `bench/scope_lookup.mo`. Empty import: naming any of `std.map`'s
// `Map`-class-instance exports explicitly hits a pre-existing latent
// instance/dictionary-resolution bug (same workaround `bench/scope_lookup.mo`
// and `std/map_tests.mo` already use) — everything remains available
// regardless via the same always-on mechanism that lets any top-level
// type/def resolve without being explicitly `use`d.
use std.map {}

// --- Helper: empty ScopeData ---

def scope_data_empty : ScopeData := {
    def_refs := Map.empty,
    class_defs := List.empty,
    instances := List.empty,
    inductives := Map.empty,
    classes := List.empty,
    infixes := List.empty,
    conflicts := List.empty,
}

// --- Helper: module path equality ---

def modpath_eq (a : ModulePath) (b : ModulePath) : Bool :=
    Similar.similar a b

// --- Helper: add a ScopeDef to ScopeData ---

def scope_data_add_def (sd : ScopeData) (d : ScopeDef) : ScopeData :=
    match sd {
        mk dr cd ins ind cls infs conf dp =>
            match d {
                mk dname _ _ _ => {
                    def_refs := Map.insert dname d dr,
                    class_defs := cd,
                    instances := ins,
                    inductives := ind,
                    classes := cls,
                    infixes := infs,
                    conflicts := conf,
                    def_params := dp,
                }
            }
    }

// --- Helper: add an Inductive to ScopeData ---

def scope_data_add_inductive (sd : ScopeData) (ind : Inductive) : ScopeData :=
    match sd {
        mk dr cd ins inds cls infs conf dp =>
            match ind {
                mk indname _ _ _ _ _ => {
                    def_refs := dr,
                    class_defs := cd,
                    instances := ins,
                    inductives := Map.insert indname ind inds,
                    classes := cls,
                    infixes := infs,
                    conflicts := conf,
                    def_params := dp,
                }
            }
    }

// --- build_scope_from_decls: build ScopeData from parsed declarations ---

// Two-pass: pass 1 (`build_scope_from_decls_go`, unchanged) registers every
// real `def`/`type`/`class`/`instance`/`infix` declaration exactly as
// before, `use_d`/`open_d` still no-ops there. Pass 2 (`alias_decls_in_scope`,
// below) re-walks the SAME decl_list' `use_d`/`open_d`/`scoped_open_d` against
// the now-complete pass-1 result, registering BARE (or renamed) aliases
// for the real qualified names they bring in -- this has to be a separate
// pass, not folded into pass 1's single left-to-right walk, because an
// `open`/`use` very commonly appears BEFORE the def(s) it aliases (e.g.
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
// currently needs (the one real glob, `lang/main.mo`'s `use lang.cli
// {*}`, is only ever referenced through its own already-qualified
// `Command.*` names, not bare) -- left for future work if that changes.
// `scoped_open_d` (`open X in <decl>`, meant to scope its alias to just
// the one wrapped declaration) is treated the same as a top-level open
// (i.e. NOT actually scoped) -- true isolation would need per-decl scope
// extension during typecheck, which this checker doesn't have, and no
// non-test `.mo` file in the corpus was found using `scoped_open_d`'s
// real scoping semantics (only `lang/parser.mo`'s own unit tests and
// `lang/pretty.mo`'s round-trip fixture construct one directly).
def build_scope_from_decls (path : ModulePath) (decl_list : List Decl) : ScopeData :=
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
def alias_def (acc : ScopeData) (real_path : ModulePath) (alias_name : Identifier) : ScopeData :=
    match scope_data_find_def acc real_path {
        Option.some sd =>
            match sd {
                mk _ module_ sig body =>
                    let alias_mp : ModulePath := ModulePath.mp (List.cons alias_name List.empty) in
                    let aliased : ScopeDef := {
                        name := alias_mp,
                        module := module_,
                        sig := sig,
                        body := body,
                    } in
                    scope_data_add_def acc aliased
            },
        Option.none => acc
    }

def path_extend (path : ModulePath) (name : Identifier) : ModulePath :=
    match path {
        ModulePath.mp ids => ModulePath.mp (list_append ids (List.cons name List.empty))
    }

def apply_open_filter (acc : ScopeData) (path : ModulePath) (filter : OpenFilter) : ScopeData :=
    match filter {
        OpenFilter.open_all => acc,
        OpenFilter.open_only names => apply_open_names acc path names
    }

def apply_open_names (acc : ScopeData) (path : ModulePath) (names : List Identifier) : ScopeData :=
    match names {
        List.empty => acc,
        List.cons n rest => apply_open_names (alias_def acc (path_extend path n) n) path rest
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
        UseItem.use_name n => alias_def acc (path_extend path n) n,
        UseItem.use_rename n alias_name => alias_def acc (path_extend path n) alias_name,
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
        mk defname _ term_ _ _ _ =>
            let sd : ScopeDef := {
                name := defname,
                module := path,
                sig := Term.hole,
                body := Term.hole,
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
            let params : List (Pair Identifier Term) := def_params_of_term term_ in
            scope_data_add_def_params with_def defname params
    }

/// A def's declared parameter (name, type) list, in order, recovered
/// from its own BODY's leading `Term.lam` chain -- `Term.lam` carries no
/// default/multiplicity slot at all (unlike the reference compiler's own
/// `Term::Lam{param: Par::P(Param)}`, a full `Param`), so only name+type
/// survive here -- matches this plan's own `lang/` Non-Goal (no def-param
/// defaults for v1, see the plan's Phase 7 doc comment). Stops at the
/// first non-`Lam` node (the def's real body).
#[terminating]
def def_params_of_term (t : Term) : List (Pair Identifier Term) :=
    match t {
        Term.lam dbg typ body =>
            List.cons (Pair.pair (scope_debug_name_to_id dbg) typ) (def_params_of_term body),
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
def scope_data_add_def_params (sd : ScopeData) (name : ModulePath) (params : List (Pair Identifier Term)) : ScopeData :=
    match sd {
        mk dr cd ins ind cls infs conf dp => {
            def_refs := dr,
            class_defs := cd,
            instances := ins,
            inductives := ind,
            classes := cls,
            infixes := infs,
            conflicts := conf,
            def_params := Map.insert name params dp,
        }
    }

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
        mk name _ _ constructors _ _ =>
            let type_sd : ScopeDef := {
                name := name,
                module := path,
                sig := Term.hole,
                body := Term.hole,
            } in
            let with_type_def : ScopeData := scope_data_add_def with_ind type_sd in
            add_constructors_as_defs with_type_def constructors path
    }

def add_constructors_as_defs (acc : ScopeData) (cns : List InductConstructor) (path : ModulePath) : ScopeData :=
    add_constructors_go acc cns path

def add_constructors_go (acc : ScopeData) (cns : List InductConstructor) (path : ModulePath) : ScopeData :=
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
                    } in
                    let new_acc : ScopeData := scope_data_add_def acc sd in
                    add_constructors_go new_acc rest path
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
        Struct.mk name fields vis =>
            let type_mp : ModulePath := ModulePath.mp (List.cons name List.empty) in
            let type_sd : ScopeDef := {
                name := type_mp,
                module := path,
                sig := Term.hole,
                body := Term.hole,
            } in
            let with_type_def : ScopeData := scope_data_add_def acc type_sd in
            let mk_mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "mk") List.empty) in
            let mk_params : List Param := struct_fields_to_params fields in
            let mk_con : InductConstructor := InductConstructor.mk mk_mp mk_params Term.hole in
            let synthetic_ind : Inductive := Inductive.mk type_mp List.empty Term.hole (List.cons mk_con List.empty) List.empty vis in
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
            let cls_mp : ModulePath := ModulePath.mp name_list in
            let with_cls : ScopeData := scope_data_add_class acc cls in
            add_class_methods with_cls methods cls_mp
    }

def add_class_methods (acc : ScopeData) (methods : List ClassDef) (cls_mp : ModulePath) : ScopeData :=
    add_methods_go acc methods cls_mp

def add_methods_go (acc : ScopeData) (methods : List ClassDef) (cls_mp : ModulePath) : ScopeData :=
    match methods {
        List.empty => acc,
        List.cons m rest =>
            match m {
                mk method_name _ _ =>
                    match cls_mp {
                        ModulePath.mp cls_ids =>
                            let method_id_list : List Identifier := List.cons method_name List.empty in
                            let method_ids : List Identifier := List.append cls_ids method_id_list in
                            let full_name : ModulePath := ModulePath.mp method_ids in
                            let scd : ScopeClassDef := {
                                class_name := cls_mp,
                                full_name := full_name,
                                name := method_name,
                                sig := Term.hole,
                            } in
                            let new_acc : ScopeData := scope_data_add_class_def acc scd in
                            add_methods_go new_acc rest cls_mp
                    }
            }
    }

// --- scope_globals: extract ScopeData from Scope ---

def scope_globals (s : Scope) : ScopeData :=
    match s {
        Scope.mk _ d _ => d,
        _ => scope_data_empty
    }

// ---- scope_find_inductive ---

def scope_find_inductive (name : ModulePath) (s : Scope) : Result ScopeError Inductive :=
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
    match sd {
        mk _ _ _ _ cls _ _ _ => cls
    }

def scope_find_class (name : ModulePath) (s : Scope) : Option Class :=
    find_class_by_name (scope_data_classes (scope_globals s)) name

// --- scope_find_inductive_by_constructor ---

def scope_find_inductive_by_constructor (con_name : ModulePath) (s : Scope) : Option Inductive :=
    let g : ScopeData := scope_globals s in
    scope_data_find_inductive_by_constructor g con_name

// `inds` is a `HashMap ModulePath Inductive` (see `ScopeData`'s own doc
// comment) -- there's no by-CONSTRUCTOR index, only by-type-name, so
// this still has to scan every entry; `HashMap.to_list` walks the
// buckets once to get there. Track C (self-hosted-compiler-perf.md)
// measured this specific path as unreached in the corpus it tested, so
// it's kept as a scan rather than given its own index preemptively.
def scope_data_find_inductive_by_constructor (sd : ScopeData) (con_name : ModulePath) : Option Inductive :=
    match sd {
        mk _ _ _ inds _ _ _ _ => find_inductive_by_constructor_in_pairs (HashMap.to_list inds) con_name
    }

def find_inductive_by_constructor_in_pairs (pairs : List (Pair ModulePath Inductive)) (con_name : ModulePath) : Option Inductive :=
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

def inductive_has_constructor (ind : Inductive) (con_name : ModulePath) : Bool :=
    match ind {
        mk _ _ _ constructors _ _ =>
            match constructors {
                List.empty => false,
                List.cons cn rest =>
                    match cn {
                        mk cn_mp _ _ =>
                            if modpath_eq cn_mp con_name
                            then true
                            else inductive_has_constructor_rest rest con_name
                    }
            }
    }

#[terminating]
def inductive_has_constructor_rest (cns : List InductConstructor) (con_name : ModulePath) : Bool :=
    match cns {
        List.empty => false,
        List.cons cn rest =>
            match cn {
                mk cn_mp _ _ =>
                    if modpath_eq cn_mp con_name
                    then true
                    else inductive_has_constructor_rest rest con_name
            }
    }

// --- Find a constructor by name in an inductive, return the constructor ---

def find_constructor_in_inductive (ind : Inductive) (con_name : ModulePath) : Option InductConstructor :=
    match ind {
        mk _ _ _ constructors _ _ => find_constructor_in_list constructors con_name
    }

#[terminating]
def find_constructor_in_list (cns : List InductConstructor) (con_name : ModulePath) : Option InductConstructor :=
    match cns {
        List.empty => Option.none,
        List.cons cn rest =>
            match cn {
                mk cn_mp params typ =>
                    if modpath_eq cn_mp con_name
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
            let mp : ModulePath := ModulePath.mp (List.cons method_name List.empty) in
            err (ScopeError.class_not_found mp)
    }

def scope_data_find_class_def_by_name (sd : ScopeData) (name : Identifier) : Option ScopeClassDef :=
    match sd {
        mk _ cds _ _ _ _ _ _ => find_class_def_by_name_in_list cds name
    }

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

def scope_resolve_name (nref : NameRef) (s : Scope) (locals : LocalScope) : Result ScopeError ScopeDef :=
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
                            let lv_mp : ModulePath := ModulePath.mp (List.cons lvname empty_id_list) in
                            let empty_mp : ModulePath := ModulePath.mp empty_id_list in
                            let sd : ScopeDef := {
                                name := lv_mp,
                                module := empty_mp,
                                sig := lvtyp,
                                body := Term.hole,
                            } in
                            Option.some sd
                    }
            },
        NameRef.nmp _ => Option.none,
        NameRef.nop _ => Option.none
    }

def resolve_name_in_scope (nref : NameRef) (s : Scope) : Result ScopeError ScopeDef :=
    match nref {
        NameRef.nid i =>
            let name : ModulePath := ModulePath.mp (List.cons i List.empty) in
            resolve_def_in_scope_by_name name s,
        NameRef.nmp mp =>
            resolve_def_in_scope_by_name mp s,
        NameRef.nop _ =>
            err (ScopeError.name_not_found nref)
    }

def resolve_def_in_scope_by_name (name : ModulePath) (s : Scope) : Result ScopeError ScopeDef :=
    let g : ScopeData := scope_globals s in
    let result : Option ScopeDef := scope_data_find_def g name in
    match result {
        Option.some d => ok d,
        Option.none => err (ScopeError.name_not_found (NameRef.nmp name))
    }

// --- ScopeData: find a ScopeDef by ModulePath in def_refs ---
//
// `def_refs` is a `HashMap ModulePath ScopeDef` (see `bench/scope_lookup.mo`
// for why: at realistic scope sizes, `HashMap` clearly outperforms both
// `List`+linear-scan and `BTreeMap` for this lookup-heavy access pattern) —
// `Map.lookup`/`Map.insert` resolve correctly here because this function
// (like the rest of `scope.mo`) is monomorphic over the concrete
// `ModulePath`/`ScopeDef` types, not a generic `[Constraint]`-annotated
// helper; see `std/map.mo`'s `HashMap.to_list` doc comment for the
// evaluator limitation this sidesteps.

def scope_data_find_def (sd : ScopeData) (name : ModulePath) : Option ScopeDef :=
    match sd {
        mk dr _ _ _ _ _ _ _ => Map.lookup name dr
    }

// --- ScopeData: find a def's own declared param (name, type) list ---
// (`plans/implementations/named-field-construction.md`'s Phase 6.)

def scope_data_find_def_params (sd : ScopeData) (name : ModulePath) : Option (List (Pair Identifier Term)) :=
    match sd {
        mk _ _ _ _ _ _ _ dp => Map.lookup name dp
    }

/// Top-level `Scope`-based wrapper, mirroring `scope_find_inductive_by_
/// constructor`'s own plain-`Option` shape (not `Result`, unlike `scope_
/// find_inductive`/`scope_find_class_def`) -- "not found" naturally means
/// "this SHAPE doesn't apply, fall through to a different interpretation"
/// for named-call resolution's own def-target branch, not a hard error.
def scope_find_def_params (name : ModulePath) (s : Scope) : Option (List (Pair Identifier Term)) :=
    let g : ScopeData := scope_globals s in
    scope_data_find_def_params g name

// --- ScopeData: find an Inductive by ModulePath ---

def scope_data_find_inductive (sd : ScopeData) (name : ModulePath) : Option Inductive :=
    match sd {
        mk _ _ _ inds _ _ _ _ => Map.lookup name inds
    }

// --- Instance handling helpers ---

def scope_data_add_instance (sd : ScopeData) (ins : Instance) : ScopeData :=
    match ins {
        mk _ cname _ _ _ _ _ =>
            match sd {
                mk dr cd insts ind cls infs conf dp =>
                    let updated_insts : List ScopeInstance := scope_add_to_instances insts cname ins in
                    {
                        def_refs := dr,
                        class_defs := cd,
                        instances := updated_insts,
                        inductives := ind,
                        classes := cls,
                        infixes := infs,
                        conflicts := conf,
                        def_params := dp,
                    }
            }
    }

def scope_add_to_instances (insts : List ScopeInstance) (cls_name : ModulePath) (ins : Instance) : List ScopeInstance :=
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
                    if modpath_eq cn cls_name
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

def scope_data_add_infix (sd : ScopeData) (op : Operator) (name : ModulePath) : ScopeData :=
    let inf : Infix := { operator := op, name := name } in
    match sd {
        mk dr cd ins ind cls infs conf dp => {
            def_refs := dr,
            class_defs := cd,
            instances := ins,
            inductives := ind,
            classes := cls,
            infixes := List.cons inf infs,
            conflicts := conf,
            def_params := dp,
        }
    }

def scope_data_add_class (sd : ScopeData) (cls : Class) : ScopeData :=
    match sd {
        mk dr cd ins ind clss infs conf dp => {
            def_refs := dr,
            class_defs := cd,
            instances := ins,
            inductives := ind,
            classes := List.cons cls clss,
            infixes := infs,
            conflicts := conf,
            def_params := dp,
        }
    }

def scope_data_add_class_def (sd : ScopeData) (cd : ScopeClassDef) : ScopeData :=
    match sd {
        mk dr cds ins ind cls infs conf dp => {
            def_refs := dr,
            class_defs := List.cons cd cds,
            instances := ins,
            inductives := ind,
            classes := cls,
            infixes := infs,
            conflicts := conf,
            def_params := dp,
        }
    }

// --- Builtins ---

def add_builtins (sd : ScopeData) : ScopeData :=
    let sd_with_type : ScopeData := add_builtin_type sd in
    add_builtin_prop sd_with_type

def add_builtin_type (sd : ScopeData) : ScopeData :=
    let type_id : Identifier := Identifier.id "Type" in
    let empty_id_list : List Identifier := List.empty in
    let type_name : ModulePath := ModulePath.mp (List.cons type_id empty_id_list) in
    let empty_params : List Param := List.empty in
    let empty_constructors : List InductConstructor := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let type_ind : Inductive := Inductive.mk type_name empty_params Term.hole empty_constructors empty_attrs Visibility.package_private in
    let type_sd : ScopeDef := {
        name := type_name,
        module := ModulePath.mp empty_id_list,
        sig := Term.hole,
        body := Term.hole,
    } in
    let sd1 : ScopeData := scope_data_add_inductive sd type_ind in
    scope_data_add_def sd1 type_sd

def add_builtin_prop (sd : ScopeData) : ScopeData :=
    let prop_id : Identifier := Identifier.id "Prop" in
    let empty_id_list : List Identifier := List.empty in
    let prop_name : ModulePath := ModulePath.mp (List.cons prop_id empty_id_list) in
    let empty_params : List Param := List.empty in
    let empty_constructors : List InductConstructor := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let prop_ind : Inductive := Inductive.mk prop_name empty_params Term.hole empty_constructors empty_attrs Visibility.package_private in
    let prop_sd : ScopeDef := {
        name := prop_name,
        module := ModulePath.mp empty_id_list,
        sig := Term.hole,
        body := Term.hole,
    } in
    let sd1 : ScopeData := scope_data_add_inductive sd prop_ind in
    scope_data_add_def sd1 prop_sd

// --- build_scope_from_modules: build ScopeData from loaded modules ---

def build_scope_from_modules (path : ModulePath) (loaded : LoadedModules) : ScopeData :=
    match loaded {
        mk modules =>
            let empty : ScopeData := scope_data_empty in
            build_scope_from_modules_go modules empty
    }

def build_scope_from_modules_go (modules : List Module) (acc : ScopeData) : ScopeData :=
    match modules {
        List.empty => acc,
        List.cons m rest =>
            let with_mod : ScopeData := build_scope_from_one_module m acc in
            build_scope_from_modules_go rest with_mod
    }

def build_scope_from_one_module (m : Module) (acc : ScopeData) : ScopeData :=
    match m {
        mk _path _inductives defs infxs _instances =>
            let with_defs : ScopeData := add_module_defs acc defs in
            let with_inds : ScopeData := add_module_inductives with_defs _inductives in
            let with_inst : ScopeData := add_module_instances with_inds _instances in
            add_module_infixes with_inst infxs
    }

def add_module_defs (acc : ScopeData) (defs : List ScopeDef) : ScopeData :=
    match defs {
        List.empty => acc,
        List.cons d rest =>
            let new_acc : ScopeData := scope_data_add_def acc d in
            add_module_defs new_acc rest
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
    match acc {
        mk dr cd insts ind cls infs conf dp =>
            let merged : List ScopeInstance := scope_add_instance_group insts si in
            {
                def_refs := dr,
                class_defs := cd,
                instances := merged,
                inductives := ind,
                classes := cls,
                infixes := infs,
                conflicts := conf,
                def_params := dp,
            }
    }

def scope_add_instance_group (insts : List ScopeInstance) (si : ScopeInstance) : List ScopeInstance :=
    match si {
        mk cn ins_list =>
            scope_add_instances_to_group insts cn ins_list
    }

def scope_add_instances_to_group (insts : List ScopeInstance) (cls_name : ModulePath) (ins_list : List Instance) : List ScopeInstance :=
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
                    if modpath_eq cn cls_name
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
        List.cons inf rest =>
            match acc {
                mk dr cd ins ind cls infs conf dp => {
                    def_refs := dr,
                    class_defs := cd,
                    instances := ins,
                    inductives := ind,
                    classes := cls,
                    infixes := List.cons inf infs,
                    conflicts := conf,
                    def_params := dp,
                }
            }
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
// IS a plain, direct function (e.g. `init/init.mo`'s `infix (+) :=
// I64.add`) resolves and compiles all the way through; one whose only
// registered target is typeclass-routed surfaces as a normal
// unresolved-method situation downstream instead of a silent `void`.

#[partial]
def lookup_infix (infixes : List Infix) (op_str : String) : Option ModulePath :=
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
                        Option.some target => Term.var idx (DebugName.named (Identifier.id (show_module_path target))),
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
        Def.mk dname typ term constraints attrs vis =>
            Def.mk dname (resolve_infix_term infixes typ) (resolve_infix_term infixes term) constraints attrs vis,
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
    match s { Struct.mk sname fields vis => Struct.mk sname (resolve_infix_struct_fields infixes fields) vis }

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
def collect_infixes (decl_list : List Decl) : List Infix :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.infix_d op target _vis =>
                    let inf : Infix := { operator := op, name := target } in
                    List.cons inf (collect_infixes rest),
                _ => collect_infixes rest,
            },
    }

/// Resolves infix operators across a whole decl_list at once —
/// `resolve_infix_decl` applied to every entry.
#[partial]
def resolve_infix_decls (infixes : List Infix) (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest => List.cons (resolve_infix_decl infixes d) (resolve_infix_decls infixes rest),
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
def collect_classes (decl_list : List Decl) : List Class :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.class_d cls => List.cons cls (collect_classes rest),
                _ => collect_classes rest,
            },
    }

/// Flat scan for every top-level Instance declaration.
#[partial]
def collect_instances (decl_list : List Decl) : List Instance :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.instance_d ins => List.cons ins (collect_instances rest),
                _ => collect_instances rest,
            },
    }

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

/// Finds the `Class` an instance's own `cls : ModulePath` field names,
/// among a flat `List Class` (`collect_classes`'s output). Every real
/// class in the corpus is a single-segment name (`BEq`, `Append`, ...,
/// confirmed by direct reading) -- comparing `ModulePath.mp [cls.name]`
/// against the instance's own `cls` field this way is exactly the same
/// single-segment assumption `scope_resolve_instance`'s own class-name
/// matching already makes elsewhere.
#[partial]
def find_class_by_name (classes : List Class) (cls_name : ModulePath) : Option Class :=
    match classes {
        List.empty => Option.none,
        List.cons cls rest =>
            match cls {
                Class.mk cname _ _ _ _ =>
                    if modpath_eq (ModulePath.mp (List.cons cname List.empty)) cls_name
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
                Def.mk dname _ _ _ _ _ =>
                    if instance_method_name_matches dname method_name
                    then Option.some d
                    else find_instance_method rest method_name,
            },
    }

#[partial]
def instance_method_name_matches (dname : ModulePath) (method_name : Identifier) : Bool :=
    match dname {
        ModulePath.mp ids =>
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
        Term.app f a => term_to_slug f ++ "_" ++ term_to_slug a,
        _ => "T",
    }

#[partial]
def terms_to_slug (args : List Term) : String :=
    match args {
        List.empty => "",
        List.cons t rest =>
            match rest {
                List.empty => term_to_slug t,
                _ => term_to_slug t ++ "_" ++ terms_to_slug rest,
            },
    }

/// The mangled top-level name a promoted instance method gets. A
/// single-segment `ModulePath` (not dotted) -- `filter_reachable_decls`/
/// reachability matching is a string-based walk over already-flat
/// names, so single-segment sidesteps any dot-vs-underscore ambiguity
/// there, the same reasoning `28d98dc`'s infix-resolution pass already
/// established for its own resolved names.
#[partial]
def mangle_instance_method_name (cls_name : ModulePath) (ins_args : List Term) (method_name : Identifier) : ModulePath :=
    let cls_str := show_module_path cls_name in
    let args_str := terms_to_slug ins_args in
    let sep_args := if String.is_empty args_str then "" else "_" ++ args_str in
    let full := cls_str ++ sep_args ++ "_" ++ show_identifier method_name in
    ModulePath.mp (List.cons (Identifier.id full) List.empty)

/// The mangled top-level name an instance's own dictionary VALUE def
/// gets (distinct from any of its promoted methods' own names above).
#[partial]
def mangle_instance_dict_name (cls_name : ModulePath) (ins_args : List Term) : ModulePath :=
    let cls_str := show_module_path cls_name in
    let args_str := terms_to_slug ins_args in
    let sep_args := if String.is_empty args_str then "" else "_" ++ args_str in
    let full := "__Dict_" ++ cls_str ++ sep_args in
    ModulePath.mp (List.cons (Identifier.id full) List.empty)

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
        Instance.mk _ cls_name ins_constraints ins_args _ _ defs =>
            let method_names := class_method_names cls in
            match build_dict_fields cls_name ins_args defs method_names {
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
                    let method_decls := promote_methods cls_name ins_args ins_constraints defs method_names in
                    let dict_name := mangle_instance_dict_name cls_name ins_args in
                    let dict_con := Con.mk (Identifier.id "mk") dict_name (List.length field_terms) (options_of field_terms) in
                    let dict_def := Def.mk dict_name (Term.type_ 1) (Term.con dict_con)
                        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private in
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
def promote_methods (cls_name : ModulePath) (ins_args : List Term) (ins_constraints : List TypeConstraint) (defs : List Def) (method_names : List Identifier) : List Decl :=
    match method_names {
        List.empty => List.empty,
        List.cons mname rest =>
            match find_instance_method defs mname {
                Option.some d =>
                    match d {
                        Def.mk _ typ term_ own_constraints attrs vis =>
                            let new_name := mangle_instance_method_name cls_name ins_args mname in
                            // `ins_constraints` prepended ahead of the
                            // method's own (usually empty) constraints --
                            // see promote_instance's own doc comment on
                            // why this is here.
                            let all_constraints := List.append ins_constraints own_constraints in
                            let renamed := Def.mk new_name typ term_ all_constraints attrs vis in
                            List.cons (Decl.def_d renamed) (promote_methods cls_name ins_args ins_constraints defs rest),
                    },
                Option.none => promote_methods cls_name ins_args ins_constraints defs rest,
            },
    }

/// Builds the dict value's own field terms, in `method_names` order --
/// each field is a bare `Term.var` reference (in VALUE position, so
/// Phase 0's `alloc_closure` boxing applies) to that method's own
/// mangled name. `Option.none` (propagated by the caller as a hard
/// failure) the moment any declared method is missing from `defs`.
#[partial]
def build_dict_fields (cls_name : ModulePath) (ins_args : List Term) (defs : List Def) (method_names : List Identifier) : Option (List Term) :=
    match method_names {
        List.empty => Option.some List.empty,
        List.cons mname rest =>
            match find_instance_method defs mname {
                Option.none => Option.none,
                Option.some _ =>
                    match build_dict_fields cls_name ins_args defs rest {
                        Option.none => Option.none,
                        Option.some rest_terms =>
                            let mangled := mangle_instance_method_name cls_name ins_args mname in
                            let method_ref := Term.var 0 (DebugName.named (mangled_to_identifier mangled)) in
                            Option.some (List.cons method_ref rest_terms),
                    },
            },
    }

/// A single-segment `ModulePath` (as every `mangle_instance_*_name`
/// above always produces) back down to the bare `Identifier` a
/// `Term.var`'s `DebugName.named` needs.
#[partial]
def mangled_to_identifier (mp : ModulePath) : Identifier :=
    match mp {
        ModulePath.mp ids =>
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
                    if single_var && def_references_class (show_module_path cls) body
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
    }

#[partial]
def literal_references_class (cls_str : String) (l : Literal) : Bool :=
    match l {
        Literal.str _ => false,
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
def dict_param_name (cls : ModulePath) : String :=
    "__dict_" ++ show_module_path cls

/// Adds one leading dictionary parameter per qualifying constraint (see
/// `qualifying_dict_constraints`) to a single Def. A no-op (returns `d`
/// unchanged) when no constraint qualifies -- the overwhelmingly common
/// case (an ordinary, unconstrained def).
#[partial]
def add_constraint_dict_params (d : Def) : Def :=
    match d {
        Def.mk name typ term_ constraints attrs vis =>
            let qualifying := qualifying_dict_constraints constraints term_ in
            match qualifying {
                List.empty => d,
                List.cons _ _ =>
                    let new_typ := prepend_dict_pis qualifying typ in
                    let new_term := prepend_dict_lams qualifying term_ in
                    Def.mk name new_typ new_term constraints attrs vis,
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
type LocalTypeBinding {
    mk (var_id : Identifier) (declared_type : Term),
}

/// One already-bound dictionary parameter currently in scope, keyed by
/// its own class -- threaded down the same way, extended whenever the
/// walk descends into one of Phase 3's own dict-binding `Term.lam`s
/// (recognized by `dict_param_name`'s own naming scheme).
type DictBinding {
    mk (cls : ModulePath) (dict_id : Identifier),
}

/// One 0-arg constructor's own owning inductive type -- e.g. `true`/
/// `false` both owned by `Bool` -- needed for carrier inference on a
/// bare constructor reference like `true` in `true == false`.
type CtorOwner {
    mk (ctor_name : Identifier) (owner : ModulePath),
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
type DefTypeEntry {
    mk (name : ModulePath) (typ : Term),
}

#[partial]
def collect_def_types (decl_list : List Decl) : List DefTypeEntry :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk dname dtyp _ _ _ _ =>
                            List.cons (DefTypeEntry.mk dname dtyp) (collect_def_types rest),
                    },
                _ => collect_def_types rest,
            },
    }

#[partial]
def lookup_def_type (entries : List DefTypeEntry) (name : Identifier) : Option Term :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                DefTypeEntry.mk ename etyp =>
                    if Similar.similar (last_segment ename) name
                    then Option.some etyp
                    else lookup_def_type rest name,
            },
    }

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
                _ => collect_ctor_owners rest,
            },
    }

#[partial]
def ctor_owners_of (owner : ModulePath) (constructors : List InductConstructor) : List CtorOwner :=
    match constructors {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                InductConstructor.mk cname params _ =>
                    match params {
                        List.empty =>
                            List.cons (CtorOwner.mk (last_segment cname) owner) (ctor_owners_of owner rest),
                        List.cons _ _ => ctor_owners_of owner rest,
                    },
            },
    }

#[partial]
def last_segment (mp : ModulePath) : Identifier :=
    match mp {
        ModulePath.mp ids => last_segment_of ids,
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
def lookup_ctor_owner (owners : List CtorOwner) (id : Identifier) : Option ModulePath :=
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

#[partial]
def lookup_dict_binding (dict_env : List DictBinding) (cls_name : ModulePath) : Option Identifier :=
    match dict_env {
        List.empty => Option.none,
        List.cons b rest =>
            match b {
                DictBinding.mk bcls bid =>
                    if modpath_eq bcls cls_name
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

/// Narrow, deliberately conservative syntactic carrier-type guesser --
/// see this section's own top doc comment. Returns `Option.none` for
/// any shape not covered below (a nested `App` not a literal/known-
/// constructor/declared-param, an un-annotated bound var, `if`/`match`
/// scrutinees, ...) -- the caller (`resolve_class_call_term`) treats
/// that the same as "no matching instance", failing clean at link time
/// rather than guessing.
#[partial]
def infer_carrier_type (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : List DefTypeEntry) (t : Term) : Option Term :=
    match t {
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
                    match infer_carrier_type env ctor_owners def_types then_ {
                        Option.some c => Option.some c,
                        Option.none => infer_carrier_type env ctor_owners def_types else_,
                    },
                _ => literal_carrier_type v,
            },
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match lookup_local_type env id {
                        Option.some typ => Option.some typ,
                        Option.none =>
                            match lookup_ctor_owner ctor_owners id {
                                Option.some owner => Option.some (carrier_var (show_module_path owner)),
                                Option.none => Option.none,
                            },
                    },
                DebugName.unnamed => Option.none,
            },
        // A constructed value's own `typ_name` names its owning type
        // directly -- more reliable than the `ctor_owners` name lookup
        // above (which only ever applies to a bare `Term.var` reference
        // to a 0-arg constructor's own NAME, not an already-built
        // `Term.con` value like this one -- confirmed as a real gap via
        // a genuine crash: a call site passing an already-constructed
        // value (e.g. `show_twice mytrue` where `mytrue` reached this
        // point already as a `Term.con`, not a bare var) resolved NO
        // carrier at all and silently skipped dict-arg insertion,
        // producing a real arity-mismatched call and a runtime segfault).
        Term.con c =>
            match c { Con.mk _ typ_name _ _ => Option.some (carrier_var (show_module_path typ_name)) },
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
                        Term.var _ dbg =>
                            match dbg {
                                DebugName.named id =>
                                    match lookup_def_type def_types id {
                                        Option.some typ =>
                                            match type_head_name_local (return_type_after_n_args typ (List.length args)) {
                                                Option.some carrier_name => Option.some (carrier_var (show_identifier carrier_name)),
                                                Option.none => Option.none,
                                            },
                                        Option.none => Option.none,
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
        Literal.str _ => Option.some (carrier_var "String"),
        _ => Option.none,
    }

/// The names an instance's own `args` may match ANYTHING against --
/// both explicit `{A : Type}` binders (`implicit_params`) AND
/// constraint-only binders (`[Add A]` on `instance [Add A] HAdd A A A`,
/// which has no `implicit_params` entry for its own `A` at all).
#[partial]
def instance_wildcard_names (ins : Instance) : List Identifier :=
    match ins {
        Instance.mk _ _ constraints _ _ implicit_params _ =>
            List.append (param_names implicit_params) (constraint_vars constraints),
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

/// Structural match between one instance-declared type arg and a
/// concrete carrier, treating any leaf `Var` in `wildcard_names` as a
/// match-anything hole. Handles nested shapes (`Append (List A)`'s own
/// `App (Var "List") (Var "A")` against a carrier `App (Var "List")
/// (Var "I64")`) via ordinary structural recursion.
#[partial]
def term_matches_carrier (wildcard_names : List Identifier) (ins_term : Term) (carrier : Term) : Bool :=
    match ins_term {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    if id_in_list id wildcard_names
                    then true
                    else match carrier {
                        Term.var _ cdbg =>
                            match cdbg {
                                DebugName.named cid => Similar.similar id cid,
                                DebugName.unnamed => false,
                            },
                        _ => false,
                    },
                DebugName.unnamed => false,
            },
        Term.app if_ ia =>
            match carrier {
                Term.app cf ca => term_matches_carrier wildcard_names if_ cf && term_matches_carrier wildcard_names ia ca,
                _ => false,
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

/// Finds the best-matching instance for `cls_name` against a concrete
/// `carrier` -- fully-concrete candidates preferred over wildcard-
/// matching ones (specificity preference), first-match-wins within each
/// tier (mirrors `first_matching_instance`'s own existing "first match,
/// not exhaustive/best match" precedent). No hard ambiguity error --
/// `Option.none` (fail clean at link time) if nothing matches at all.
#[partial]
def find_matching_instance (instances : List Instance) (cls_name : ModulePath) (carrier : Term) : Option Instance :=
    let candidates := filter_instances_by_class instances cls_name in
    let concrete := filter_concrete candidates in
    match first_instance_matching concrete carrier {
        Option.some ins => Option.some ins,
        Option.none => first_instance_matching candidates carrier,
    }

/// Filters a flat `List Instance` (`collect_instances`'s output) down
/// to those naming `cls_name` -- distinct from `find_instances_by_class`
/// just below, which operates on the `Scope`-registry's own
/// `ScopeInstance` grouping (a different, pre-existing structure this
/// pre-Scope pass has no access to, same reasoning `collect_infixes`'s
/// own doc comment already gives for why this pass can't use `Scope`).
#[partial]
def filter_instances_by_class (instances : List Instance) (cls_name : ModulePath) : List Instance :=
    match instances {
        List.empty => List.empty,
        List.cons ins rest =>
            match ins {
                Instance.mk _ ins_cls _ _ _ _ _ =>
                    if modpath_eq ins_cls cls_name
                    then List.cons ins (filter_instances_by_class rest cls_name)
                    else filter_instances_by_class rest cls_name,
            },
    }

#[partial]
def filter_concrete (instances : List Instance) : List Instance :=
    match instances {
        List.empty => List.empty,
        List.cons ins rest =>
            if instance_is_fully_concrete ins
            then List.cons ins (filter_concrete rest)
            else filter_concrete rest,
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
type CallSpine {
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
    match t {
        Term.app f a => flatten_call_spine_go f (List.cons a acc),
        _ => CallSpine.mk t acc,
    }

#[partial]
def rebuild_call (head : Term) (args : List Term) : Term :=
    match args {
        List.empty => head,
        List.cons a rest => rebuild_call (Term.app head a) rest,
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
            match find_class_by_name classes (ModulePath.mp (List.cons (Identifier.id cls_str) List.empty)) {
                Option.none => Option.none,
                Option.some cls =>
                    match method_suffix_of text {
                        Option.none => Option.none,
                        Option.some method_str =>
                            Option.some (ClassMethodRef.mk cls (Identifier.id method_str)),
                    },
            },
    }

type ClassMethodRef {
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
def class_own_name (cls : Class) : ModulePath :=
    match cls { Class.mk cname _ _ _ _ => ModulePath.mp (List.cons cname List.empty) }

/// Resolves ONE dict argument a promoted method's own constraint
/// needs, given the SAME concrete `carrier` already established at the
/// outer call site (the one-level, non-deeply-recursive simplification
/// this plan's own corpus-reality-check calls for -- every real corpus
/// case has at most one inner constraint, on the same type variable as
/// the instance's own carrier). Checks `dict_env` first (D5 forwarding,
/// for completeness/generality), then falls back to a fresh D4 concrete
/// lookup.
#[partial]
def resolve_dict_arg (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (carrier : Term) (c : TypeConstraint) : Option Term :=
    match c {
        TypeConstraint.mk cls_name _ =>
            match lookup_dict_binding dict_env cls_name {
                Option.some bound_id => Option.some (Term.var 0 (DebugName.named bound_id)),
                Option.none =>
                    match find_matching_instance instances cls_name carrier {
                        Option.some ins =>
                            match ins {
                                Instance.mk _ _ _ ins_args _ _ _ =>
                                    Option.some (Term.var 0 (DebugName.named (mangled_to_identifier (mangle_instance_dict_name cls_name ins_args)))),
                            },
                        Option.none => Option.none,
                    },
            },
    }

#[partial]
def resolve_dict_args (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (carrier : Term) (constraints : List TypeConstraint) : Option (List Term) :=
    match constraints {
        List.empty => Option.some List.empty,
        List.cons c rest =>
            match resolve_dict_arg classes instances dict_env carrier c {
                Option.none => Option.none,
                Option.some arg =>
                    match resolve_dict_args classes instances dict_env carrier rest {
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
#[partial]
def resolve_class_call_term (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (def_constraints : List DefConstraintEntry) (def_types : List DefTypeEntry) (env : List LocalTypeBinding) (dict_env : List DictBinding) (def_carrier : Option Term) (t : Term) : Term :=
    match t {
        Term.lam dbg typ body =>
            match dbg {
                DebugName.named id =>
                    let dict_class := dict_binding_class_of id in
                    let new_env := List.cons (LocalTypeBinding.mk id typ) env in
                    let new_dict_env := match dict_class {
                        Option.some cls_name => List.cons (DictBinding.mk cls_name id) dict_env,
                        Option.none => dict_env,
                    } in
                    Term.lam dbg (resolve_class_call_term classes instances ctor_owners def_constraints def_types env dict_env def_carrier typ)
                        (resolve_class_call_term classes instances ctor_owners def_constraints def_types new_env new_dict_env def_carrier body),
                DebugName.unnamed =>
                    Term.lam dbg (resolve_class_call_term classes instances ctor_owners def_constraints def_types env dict_env def_carrier typ)
                        (resolve_class_call_term classes instances ctor_owners def_constraints def_types env dict_env def_carrier body),
            },
        Term.app _ _ =>
            match flatten_call_spine t {
                CallSpine.mk head args =>
                    let resolved_args := resolve_class_call_terms classes instances ctor_owners def_constraints def_types env dict_env def_carrier args in
                    match head {
                        Term.var _ dbg =>
                            match dbg {
                                DebugName.named id =>
                                    match class_method_ref classes id {
                                        Option.some ref =>
                                            match ref {
                                                ClassMethodRef.mk cls method_name =>
                                                    resolve_class_method_call classes instances dict_env def_types cls method_name resolved_args head args def_carrier,
                                            },
                                        Option.none => resolve_ordinary_constrained_call classes instances dict_env def_constraints def_types id head resolved_args,
                                    },
                                DebugName.unnamed => rebuild_call head resolved_args,
                            },
                        _ => rebuild_call (resolve_class_call_term classes instances ctor_owners def_constraints def_types env dict_env def_carrier head) resolved_args,
                    },
            },
        _ => term_map_children (resolve_class_call_term classes instances ctor_owners def_constraints def_types env dict_env def_carrier) t,
    }

#[partial]
def resolve_class_call_terms (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (def_constraints : List DefConstraintEntry) (def_types : List DefTypeEntry) (env : List LocalTypeBinding) (dict_env : List DictBinding) (def_carrier : Option Term) (args : List Term) : List Term :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            List.cons (resolve_class_call_term classes instances ctor_owners def_constraints def_types env dict_env def_carrier a) (resolve_class_call_terms classes instances ctor_owners def_constraints def_types env dict_env def_carrier rest),
    }

/// D5-first, D4-fallback resolution for one class-method call, given
/// its own (already-resolved-inside-out) real args. `orig_head`/
/// `orig_args` are the pre-resolution originals, used ONLY for the "no
/// match found" fallback (leaves the call exactly as it structurally
/// resolved via ordinary recursion, per this pass's own "leave
/// unresolved rather than guess" style, matching `resolve_infix_term`).
#[partial]
def resolve_class_method_call (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (def_types : List DefTypeEntry) (cls : Class) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (def_carrier : Option Term) : Term :=
    let cls_name := class_own_name cls in
    match lookup_dict_binding dict_env cls_name {
        Option.some dict_id => build_dict_field_projection cls dict_id method_name resolved_args,
        Option.none => resolve_class_method_call_d4 classes instances dict_env def_types cls_name method_name resolved_args orig_head orig_args def_carrier,
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
def resolve_class_method_call_d4 (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (def_types : List DefTypeEntry) (cls_name : ModulePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (def_carrier : Option Term) : Term :=
    if modpath_eq cls_name monad_class_name && String.beq (show_identifier method_name) "pure" then
        match def_carrier {
            Option.some carrier => resolve_class_method_call_with_carrier classes instances dict_env cls_name method_name resolved_args orig_head orig_args carrier,
            Option.none => resolve_class_method_call_d4_from_args classes instances dict_env def_types cls_name method_name resolved_args orig_head orig_args def_carrier,
        }
    else resolve_class_method_call_d4_from_args classes instances dict_env def_types cls_name method_name resolved_args orig_head orig_args def_carrier

#[partial]
def resolve_class_method_call_d4_from_args (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (def_types : List DefTypeEntry) (cls_name : ModulePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (def_carrier : Option Term) : Term :=
    match infer_carrier_from_args def_types resolved_args {
        Option.some carrier => resolve_class_method_call_with_carrier classes instances dict_env cls_name method_name resolved_args orig_head orig_args carrier,
        Option.none =>
            if modpath_eq cls_name monad_class_name then
                match def_carrier {
                    Option.some carrier => resolve_class_method_call_with_carrier classes instances dict_env cls_name method_name resolved_args orig_head orig_args carrier,
                    Option.none => rebuild_call orig_head resolved_args,
                }
            else rebuild_call orig_head resolved_args,
    }

#[partial]
def monad_class_name : ModulePath :=
    ModulePath.mp (List.cons (Identifier.id "Monad") List.empty)

#[partial]
def resolve_class_method_call_with_carrier (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (cls_name : ModulePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (orig_args : List Term) (carrier : Term) : Term :=
    match find_matching_instance instances cls_name carrier {
        Option.none => rebuild_call orig_head resolved_args,
        Option.some ins => resolve_class_method_call_with_instance classes instances dict_env method_name resolved_args orig_head carrier ins,
    }

#[partial]
def resolve_class_method_call_with_instance (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (carrier : Term) (ins : Instance) : Term :=
    match ins {
        Instance.mk _ ins_cls_name ins_constraints ins_args _ _ _ =>
            resolve_class_method_call_with_dict_args classes instances dict_env ins_cls_name method_name resolved_args orig_head carrier ins_constraints ins_args,
    }

#[partial]
def resolve_class_method_call_with_dict_args (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (cls_name : ModulePath) (method_name : Identifier) (resolved_args : List Term) (orig_head : Term) (carrier : Term) (ins_constraints : List TypeConstraint) (ins_args : List Term) : Term :=
    match resolve_dict_args classes instances dict_env carrier ins_constraints {
        Option.none => rebuild_call orig_head resolved_args,
        Option.some dict_args =>
            let mangled := mangle_instance_method_name cls_name ins_args method_name in
            let method_fn_ref := Term.var 0 (DebugName.named (mangled_to_identifier mangled)) in
            rebuild_call method_fn_ref (List.append dict_args resolved_args),
    }

/// Carrier inference from a call spine's own args -- takes the first
/// one that resolves (see this section's own top doc comment on why
/// this doesn't require every arg to agree).
#[partial]
def infer_carrier_from_args (def_types : List DefTypeEntry) (args : List Term) : Option Term :=
    infer_carrier_from_args_go empty_local_types empty_ctor_owners_placeholder def_types args

/// `infer_carrier_from_args` deliberately does NOT thread the real
/// `env`/`ctor_owners` down to here -- by the time this runs, every arg
/// has ALREADY been recursively resolved by `resolve_class_call_term`
/// (inside-out), so a class-method call nested inside an arg is already
/// rewritten; what's left to inspect here is the arg's own OUTERMOST
/// shape (a literal, a bare var, ...), which `infer_carrier_type`'s
/// literal/constructor cases already handle without needing env context
/// -- the `env`-dependent "declared local param" case genuinely can't
/// apply here (there's no lambda-binding context at a call site's own
/// argument position), so an empty env is correct, not a shortcut.
#[partial]
def empty_local_types : List LocalTypeBinding := List.empty

#[partial]
def empty_ctor_owners_placeholder : List CtorOwner := List.empty

#[partial]
def infer_carrier_from_args_go (env : List LocalTypeBinding) (ctor_owners : List CtorOwner) (def_types : List DefTypeEntry) (args : List Term) : Option Term :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            match infer_carrier_type env ctor_owners def_types a {
                Option.some t => Option.some t,
                Option.none => infer_carrier_from_args_go env ctor_owners def_types rest,
            },
    }

/// Recognizes a Phase-3-added dict-binding lambda by
/// `dict_param_name`'s own naming scheme, recovering which class it's
/// for.
#[partial]
def dict_binding_class_of (id : Identifier) : Option ModulePath :=
    let text := show_identifier id in
    if String.starts_with "__dict_" text
    then Option.some (ModulePath.mp (List.cons (Identifier.id (String.drop (String.length "__dict_") text)) List.empty))
    else Option.none

/// Top-level Phase 4 driver -- applies `resolve_class_call_term` (empty
/// env/dict_env: nothing is bound yet at a decl's own top level) to
/// every `Decl.def_d`'s own `.term` (not `.typ` -- a type's own Pi-chain
/// never contains a class-method CALL to resolve, only Phase 3's own
/// dict-parameter Pi's, which this pass doesn't touch).
#[partial]
def resolve_class_calls_decls (decl_list : List Decl) : List Decl :=
    let classes := collect_classes decl_list in
    let instances := collect_instances decl_list in
    let ctor_owners := collect_ctor_owners decl_list in
    let def_constraints := collect_def_constraints decl_list in
    let def_types := collect_def_types decl_list in
    resolve_class_calls_decls_go classes instances ctor_owners def_constraints def_types decl_list

/// One ordinary (non-class-method) def's own constraints -- needed so a
/// CALL SITE to a constrained def (e.g. `show_twice 5`, where
/// `show_twice` itself carries `[Show A]`) can also gain the dict
/// argument(s) Phase 3 added a matching PARAMETER for on its
/// definition -- Phase 3 only ever rewrites the definition side; this
/// is the call-site half of the same mechanism, needed for genuine
/// polymorphism (D5) to have anything to actually supply at a call
/// site in the first place.
type DefConstraintEntry {
    mk (name : ModulePath) (constraints : List TypeConstraint),
}

#[partial]
def collect_def_constraints (decl_list : List Decl) : List DefConstraintEntry :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk dname _ _ constraints _ _ =>
                            match constraints {
                                List.empty => collect_def_constraints rest,
                                List.cons _ _ => List.cons (DefConstraintEntry.mk dname constraints) (collect_def_constraints rest),
                            },
                    },
                _ => collect_def_constraints rest,
            },
    }

#[partial]
def lookup_def_constraints (entries : List DefConstraintEntry) (name : ModulePath) : Option (List TypeConstraint) :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                DefConstraintEntry.mk ename constraints =>
                    if modpath_eq ename name
                    then Option.some constraints
                    else lookup_def_constraints rest name,
            },
    }

/// Resolves a call to an ORDINARY (non-class-method) global whose own
/// def carries constraints (registered in `def_constraints`) -- if
/// found, resolves and prepends the same dict argument(s)
/// `add_constraint_dict_params` (Phase 3) added matching PARAMETERS
/// for, using a carrier inferred from this call's own (already-
/// resolved) args, checking `dict_env` first (D5 forwarding) same as
/// any other dict resolution. A def with no registered constraints (the
/// overwhelmingly common case) or one whose dict args can't be resolved
/// passes through completely unchanged -- this must never touch an
/// ordinary, unconstrained call.
#[partial]
def resolve_ordinary_constrained_call (classes : List Class) (instances : List Instance) (dict_env : List DictBinding) (def_constraints : List DefConstraintEntry) (def_types : List DefTypeEntry) (id : Identifier) (head : Term) (resolved_args : List Term) : Term :=
    match lookup_def_constraints def_constraints (ModulePath.mp (List.cons id List.empty)) {
        Option.none => rebuild_call head resolved_args,
        Option.some constraints =>
            match infer_carrier_from_args def_types resolved_args {
                Option.none => rebuild_call head resolved_args,
                Option.some carrier =>
                    match resolve_dict_args classes instances dict_env carrier constraints {
                        Option.none => rebuild_call head resolved_args,
                        Option.some dict_args => rebuild_call head (List.append dict_args resolved_args),
                    },
            },
    }

#[partial]
def resolve_class_calls_decls_go (classes : List Class) (instances : List Instance) (ctor_owners : List CtorOwner) (def_constraints : List DefConstraintEntry) (def_types : List DefTypeEntry) (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk name typ term_ constraints attrs vis =>
                            let def_carrier := full_return_carrier typ in
                            let new_term := resolve_class_call_term classes instances ctor_owners def_constraints def_types List.empty List.empty def_carrier term_ in
                            List.cons (Decl.def_d (Def.mk name typ new_term constraints attrs vis)) (resolve_class_calls_decls_go classes instances ctor_owners def_constraints def_types rest),
                    },
                _ => List.cons d (resolve_class_calls_decls_go classes instances ctor_owners def_constraints def_types rest),
            },
    }

/// Strip EVERY leading `Term.pi`/`Term.forall` binder (unlike
/// `return_type_after_n_args`, which strips a fixed `n`) -- used to find
/// a top-level def's own ULTIMATE codomain regardless of arity, for
/// `full_return_carrier`'s do-notation fallback (see
/// `resolve_class_call_term`'s doc comment).
#[partial]
def strip_all_leading_binders (typ : Term) : Term :=
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
#[partial]
def full_return_carrier (typ : Term) : Option Term :=
    match type_head_name_local (strip_all_leading_binders typ) {
        Option.some carrier_name => Option.some (carrier_var (show_identifier carrier_name)),
        Option.none => Option.none,
    }

// --- scope_resolve_instance: find concrete instance by class name ---

def scope_resolve_instance (class_name : ModulePath) (instance_key : InstanceKey) (s : Scope) : Result ScopeError Instance :=
    let g : ScopeData := scope_globals s in
    let candidates : List Instance := scope_instance_candidates g class_name in
    first_matching_instance candidates instance_key

def scope_instance_candidates (sd : ScopeData) (cls_name : ModulePath) : List Instance :=
    match sd {
        mk _ _ insts _ _ _ _ _ => find_instances_by_class insts cls_name
    }

def find_instances_by_class (insts : List ScopeInstance) (cls_name : ModulePath) : List Instance :=
    match insts {
        List.empty => List.empty,
        List.cons si rest =>
            match si {
                mk cn ins_list =>
                    if modpath_eq cn cls_name
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
    match scope_data_find_def sd (ModulePath.mp List.empty) {
        Option.some _ => false,
        Option.none => true
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
    let mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "foo") List.empty) in
    let no_constraints : List TypeConstraint := List.empty in
    let no_attrs : List Attribute := List.empty in
    Decl.def_macro_d (Def.mk mp Term.hole Term.hole no_constraints no_attrs Visibility.package_private)

def dummy_decl_gen_decl : Decl :=
    let mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "foo") List.empty) in
    let no_params : List Param := List.empty in
    let no_decls : List Decl := List.empty in
    let no_attrs : List Attribute := List.empty in
    Decl.decl_gen_d mp no_params no_decls no_attrs

#[test]
def test_build_scope_one_decl_macro_call_d_is_noop : Bool :=
    let sd := scope_data_empty in
    let path : ModulePath := ModulePath.mp List.empty in
    let sd2 := build_scope_one_decl dummy_macro_call_decl path sd in
    match scope_data_find_def sd2 (ModulePath.mp (List.cons (Identifier.id "foo") List.empty)) {
        Option.some _ => false,
        Option.none => true
    }

#[test]
def test_build_scope_one_decl_def_macro_d_is_noop : Bool :=
    let sd := scope_data_empty in
    let path : ModulePath := ModulePath.mp List.empty in
    let sd2 := build_scope_one_decl dummy_def_macro_decl path sd in
    match scope_data_find_def sd2 (ModulePath.mp (List.cons (Identifier.id "foo") List.empty)) {
        Option.some _ => false,
        Option.none => true
    }

#[test]
def test_build_scope_one_decl_decl_gen_d_is_noop : Bool :=
    let sd := scope_data_empty in
    let path : ModulePath := ModulePath.mp List.empty in
    let sd2 := build_scope_one_decl dummy_decl_gen_decl path sd in
    match scope_data_find_def sd2 (ModulePath.mp (List.cons (Identifier.id "foo") List.empty)) {
        Option.some _ => false,
        Option.none => true
    }

// --- Infix operator resolution tests ---

def dummy_infixes : List Infix :=
    let plus : Infix := { operator := Operator.operator "+", name := ModulePath.mp (List.cons (Identifier.id "I64") (List.cons (Identifier.id "add") List.empty)) } in
    List.cons plus List.empty

#[test]
def test_lookup_infix_found : Bool :=
    match lookup_infix dummy_infixes "+" {
        Option.some target => String.beq (show_module_path target) "I64.add",
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
    let target := ModulePath.mp (List.cons (Identifier.id "I64") (List.cons (Identifier.id "add") List.empty)) in
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
    let name : ModulePath := ModulePath.mp (List.cons (Identifier.id "helper") List.empty) in
    let d := Def.mk name Term.hole body List.empty List.empty Visibility.package_private in
    let decl_list : List Decl := List.cons (Decl.def_d d) List.empty in
    match resolve_infix_decls dummy_infixes decl_list {
        List.cons resolved_decl _ =>
            match resolved_decl {
                Decl.def_d resolved_def =>
                    match resolved_def {
                        Def.mk _ _ resolved_body _ _ _ =>
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
    let cls_name := ModulePath.mp (List.cons (Identifier.id "BEq") List.empty) in
    let bool_arg := Term.var 0 (DebugName.named (Identifier.id "Bool")) in
    let beq_name := ModulePath.mp (List.cons (Identifier.id "beq") List.empty) in
    let true_body := Term.var 0 (DebugName.named (Identifier.id "true")) in
    let beq_def := Def.mk beq_name Term.hole true_body List.empty List.empty Visibility.package_private in
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
    let cls_name := ModulePath.mp (List.cons (Identifier.id "Show") List.empty) in
    let show_name := ModulePath.mp (List.cons (Identifier.id "show") List.empty) in
    let show_def := Def.mk show_name Term.hole (mk_i64_dummy 1) List.empty List.empty Visibility.package_private in
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
                        Def.mk dname _ _ _ _ _ =>
                            if String.beq (module_path_to_str_scope dname) name
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
                            if String.beq (show_module_path cls_name) cls_str
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
def module_path_to_str_scope (mp : ModulePath) : String :=
    show_module_path mp

// --- Phase 3 (dictionary-passing plan) tests ---

#[test]
def test_add_constraint_dict_params_adds_pi_and_lam : Bool :=
    // def show_twice [Show A] (x : A) : String := Show.show x
    let show_call := Term.app (Term.var 1 (DebugName.named (Identifier.id "Show.show"))) (Term.var 0 (DebugName.named (Identifier.id "x"))) in
    let orig_term := Term.lam (DebugName.named (Identifier.id "x")) Term.hole show_call in
    let orig_typ := Term.pi Term.hole (Term.type_ 1) in
    let constraint := TypeConstraint.mk (ModulePath.mp (List.cons (Identifier.id "Show") List.empty)) (List.cons (Identifier.id "A") List.empty) in
    let d := Def.mk (ModulePath.mp (List.cons (Identifier.id "show_twice") List.empty)) orig_typ orig_term
        (List.cons constraint List.empty) List.empty Visibility.package_private in
    let d2 := add_constraint_dict_params d in
    match d2 {
        Def.mk _ new_typ new_term _ _ _ =>
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
    let constraint := TypeConstraint.mk (ModulePath.mp (List.cons (Identifier.id "Show") List.empty)) (List.cons (Identifier.id "A") List.empty) in
    let d := Def.mk (ModulePath.mp (List.cons (Identifier.id "unrelated") List.empty)) (Term.type_ 1) unrelated_body
        (List.cons constraint List.empty) List.empty Visibility.package_private in
    let d2 := add_constraint_dict_params d in
    match d2 {
        Def.mk _ new_typ new_term _ _ _ =>
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
    let mp := ModulePath.mp (List.cons (Identifier.id "IO.println") List.empty) in
    Similar.similar (last_segment mp) (Identifier.id "println")

#[test]
def test_last_segment_leaves_undotted_single_segment_name_unchanged : Bool :=
    let mp := ModulePath.mp (List.cons (Identifier.id "greet") List.empty) in
    Similar.similar (last_segment mp) (Identifier.id "greet")

#[test]
def test_lookup_def_type_finds_dotted_own_name_def_by_bare_query : Bool :=
    let println_typ := Term.pi (Term.var 0 (DebugName.named (Identifier.id "String")))
        (Term.app (Term.var 0 (DebugName.named (Identifier.id "IO"))) (Term.var 0 (DebugName.named (Identifier.id "Unit")))) in
    let entry := DefTypeEntry.mk (ModulePath.mp (List.cons (Identifier.id "IO.println") List.empty)) println_typ in
    match lookup_def_type (List.cons entry List.empty) (Identifier.id "println") {
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
    match infer_carrier_type List.empty List.empty List.empty if_term {
        Option.some _ => true,
        Option.none => false,
    }

#[test]
def test_infer_carrier_type_if_branch_none_falls_through_to_else : Bool :=
    // THEN branch is a bare bound var with no local type (uninformative);
    // carrier must still be found from the ELSE branch.
    let if_term := Term.lit (Literal.if_ (Term.var 0 (DebugName.named (Identifier.id "cond")))
        (Term.var 1 (DebugName.named (Identifier.id "uninformative"))) (Term.lit (Literal.str "x"))) in
    match infer_carrier_type List.empty List.empty List.empty if_term {
        Option.some _ => true,
        Option.none => false,
    }
