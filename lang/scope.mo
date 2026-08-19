use lang.types {
  Class, ClassDef, Decl, Def, Identifier, InductConstructor, Inductive, Infix,
  Instance, InstanceKey, LoadedModules, LocalScope, LocalVar, Module, ModulePath,
  NameRef, Operator, Param, Scope, ScopeClassDef, ScopeData, ScopeDef, ScopeError,
  ScopeInstance, Similar, Struct, StructField, Term, class_d, class_not_found,
  def_d, hole, id, inductive_d, inductive_not_found, infix_d, instance_d,
  instance_not_found, mk, mp, name, name_not_found, nid, nmp, nop, open_d,
  scoped_open_d, struct_d, type_, use_d,
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
        mk dr cd ins ind cls infs conf =>
            match d {
                mk dname _ _ _ => {
                    def_refs := Map.insert dname d dr,
                    class_defs := cd,
                    instances := ins,
                    inductives := ind,
                    classes := cls,
                    infixes := infs,
                    conflicts := conf,
                }
            }
    }

// --- Helper: add an Inductive to ScopeData ---

def scope_data_add_inductive (sd : ScopeData) (ind : Inductive) : ScopeData :=
    match sd {
        mk dr cd ins inds cls infs conf =>
            match ind {
                mk indname _ _ _ _ _ => {
                    def_refs := dr,
                    class_defs := cd,
                    instances := ins,
                    inductives := Map.insert indname ind inds,
                    classes := cls,
                    infixes := infs,
                    conflicts := conf,
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
        mk defname _ _ _ _ _ =>
            let sd : ScopeDef := {
                name := defname,
                module := path,
                sig := Term.hole,
                body := Term.hole,
            } in
            scope_data_add_def acc sd
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
            let empty_params : List Param := List.empty in
            let empty_constructors : List InductConstructor := List.empty in
            let empty_attrs : List Attribute := List.empty in
            let dummy_ind : Inductive := Inductive.mk cls_mp empty_params (Term.type_ 1) empty_constructors empty_attrs Visibility.package_private in
            let with_cls : ScopeData := scope_data_add_class acc dummy_ind in
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

// --- ScopeData: find a class def (method) by ModulePath ---

def scope_data_find_class_def (sd : ScopeData) (name : ModulePath) : Option ScopeClassDef :=
    match sd {
        mk _ cds _ _ _ _ _ => find_class_def_in_list cds name
    }

def find_class_def_in_list (cds : List ScopeClassDef) (name : ModulePath) : Option ScopeClassDef :=
    match cds {
        List.empty => Option.none,
        List.cons cd rest =>
            match cd {
                mk _class_name full_name _ _ =>
                    if modpath_eq full_name name
                    then Option.some cd
                    else find_class_def_in_list rest name
            }
    }

// ---- scope_find_inductive ---

def scope_find_inductive (name : ModulePath) (s : Scope) : Result ScopeError Inductive :=
    let g : ScopeData := scope_globals s in
    let result : Option Inductive := scope_data_find_inductive g name in
    match result {
        Option.some ind => ok ind,
        Option.none => err (ScopeError.inductive_not_found name)
    }

// --- scope_find_class_def ---

def scope_find_class_def (name : ModulePath) (s : Scope) : Result ScopeError ScopeClassDef :=
    let g : ScopeData := scope_globals s in
    let result : Option ScopeClassDef := scope_data_find_class_def g name in
    match result {
        Option.some cd => ok cd,
        Option.none => err (ScopeError.class_not_found name)
    }

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
        mk _ _ _ inds _ _ _ => find_inductive_by_constructor_in_pairs (HashMap.to_list inds) con_name
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

// --- scope_find_constructor: find a constructor by name in the scope ---

def scope_find_constructor (con_name : ModulePath) (s : Scope) : Option InductConstructor :=
    match scope_find_inductive_by_constructor con_name s {
        Option.some ind => find_constructor_in_inductive ind con_name,
        Option.none => Option.none,
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
        mk _ cds _ _ _ _ _ => find_class_def_by_name_in_list cds name
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
        mk dr _ _ _ _ _ _ => Map.lookup name dr
    }

// --- ScopeData: find an Inductive by ModulePath ---

def scope_data_find_inductive (sd : ScopeData) (name : ModulePath) : Option Inductive :=
    match sd {
        mk _ _ _ inds _ _ _ => Map.lookup name inds
    }

// --- Instance handling helpers ---

def scope_data_add_instance (sd : ScopeData) (ins : Instance) : ScopeData :=
    match ins {
        mk _ cname _ _ _ _ =>
            match sd {
                mk dr cd insts ind cls infs conf =>
                    let updated_insts : List ScopeInstance := scope_add_to_instances insts cname ins in
                    {
                        def_refs := dr,
                        class_defs := cd,
                        instances := updated_insts,
                        inductives := ind,
                        classes := cls,
                        infixes := infs,
                        conflicts := conf,
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
        mk dr cd ins ind cls infs conf => {
            def_refs := dr,
            class_defs := cd,
            instances := ins,
            inductives := ind,
            classes := cls,
            infixes := List.cons inf infs,
            conflicts := conf,
        }
    }

def scope_data_add_class (sd : ScopeData) (cls : Inductive) : ScopeData :=
    match sd {
        mk dr cd ins ind clss infs conf => {
            def_refs := dr,
            class_defs := cd,
            instances := ins,
            inductives := ind,
            classes := List.cons cls clss,
            infixes := infs,
            conflicts := conf,
        }
    }

def scope_data_add_class_def (sd : ScopeData) (cd : ScopeClassDef) : ScopeData :=
    match sd {
        mk dr cds ins ind cls infs conf => {
            def_refs := dr,
            class_defs := List.cons cd cds,
            instances := ins,
            inductives := ind,
            classes := cls,
            infixes := infs,
            conflicts := conf,
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
        mk dr cd insts ind cls infs conf =>
            let merged : List ScopeInstance := scope_add_instance_group insts si in
            {
                def_refs := dr,
                class_defs := cd,
                instances := merged,
                inductives := ind,
                classes := cls,
                infixes := infs,
                conflicts := conf,
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
                mk dr cd ins ind cls infs conf => {
                    def_refs := dr,
                    class_defs := cd,
                    instances := ins,
                    inductives := ind,
                    classes := cls,
                    infixes := List.cons inf infs,
                    conflicts := conf,
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
        Instance.mk insname cls constraints args vis implicit_params =>
            Instance.mk insname cls constraints (resolve_infix_terms infixes args) vis (resolve_infix_params infixes implicit_params),
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

// --- scope_resolve_instance: find concrete instance by class name ---

def scope_resolve_instance (class_name : ModulePath) (instance_key : InstanceKey) (s : Scope) : Result ScopeError Instance :=
    let g : ScopeData := scope_globals s in
    let candidates : List Instance := scope_instance_candidates g class_name in
    first_matching_instance candidates instance_key

def scope_instance_candidates (sd : ScopeData) (cls_name : ModulePath) : List Instance :=
    match sd {
        mk _ _ insts _ _ _ _ => find_instances_by_class insts cls_name
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
        mk _ cls_name constraints ins_args _ _ =>
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
