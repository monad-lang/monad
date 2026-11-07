/// Ownership classification and drop planning for the compiled backend
/// (ownership-regions-memory O1/O3/O4).
///
/// The self-hosted backend compiles `Term` directly, so the ownership
/// analysis lives here rather than in `lang/core_ir.mo` (the evaluator IR).
/// This module is **pure**: it turns a whole-program scope and decl list
/// into an `OwnershipTables` verdict, and a def's parameters and body into a
/// `DropPlan`. Nothing here emits code; `emit.mo` consults the tables at
/// allocation sites and emits the plan's drops.
///
/// ## The v1 verdict, and why it is this narrow
///
/// Only a **monomorphic inductive** can be `Owned`: no type parameters, no
/// nullary constructor (those values are `g_nullary` singletons), not
/// `#[shared]`/`#[opaque]`/`#[proof]`/`#[linear]`, not `Copy`, and every
/// field either `Copy` (skipped by drop glue) or itself Owned. Everything
/// else is `Region` and is never freed.
///
/// Containment (I10) is a monotone fixed point over the whole program, and
/// it runs in **both** directions along a field edge:
///
/// - a type reachable from a Region value -- a field of a Region type, or a
///   type argument of a Region generic (`List`, `Thunk`, `IO`, `Ref`, ...) --
///   is Region, because the Region value is never freed and could otherwise
///   dangle into a freed Owned cell;
/// - a type reachable **from an Owned cell** through a heap pointer is Region
///   too, because an Owned cell is `malloc`'d and the collector does not scan
///   it: a GC-managed pointer stored there would be invisible to Boehm and
///   could be reclaimed while the cell still points at it. Only primitive
///   scalars (pointer-free) and all-nullary types (static `g_nullary`
///   singletons) are exempt.
///
/// ## The drop predicate, and why it needs no move analysis
///
/// A drop point is emitted only for a binder that is completely unused
/// (`BinderUse.count == 0`). That is deliberately stronger than "not moved":
/// `usage.mo` treats an ordinary call argument as a *read* (the callee may
/// borrow), and a match scrutinee's fields can escape into the arm, so any
/// use at all can leave an alias behind. An unused binder has no alias by
/// construction, so dropping it at the def's exit is trivially sound. The
/// move-mode widening (function_moves plus scrutinee handling) is O4b.
///
/// A `let` is additionally restricted to a fresh constructor initializer:
/// `let y := x` aliases an existing Owned value, and dropping both would be
/// a double free. Parameters are always fresh incoming values.
use llvm::ir {LLVMBasicBlock, LLVMInstruction, LLVMType, LLVMValue}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use std::map {HashMap}
use std::list {List.contains_by, List.length}
use lang::types {
    Attribute, Con, DebugName, Decl, Identifier, Inductive, InductConstructor,
    Multiplicity, NamePath, Param, Scope, Struct, StructField, Term, id_eq,
    show_identifier, show_name_path, term_peel,
}
use lang::typecheck::copy_class {CopyVerdict, copy_verdict}
use lang::typecheck::traverse {term_children}
use lang::typecheck::usage {
    BinderKind, BinderUse, collect_binder_uses_with_params, ctor_name_set,
    shared_name_set, typ_is_function,
}
use lib::attrs {find_attr_args}
use lib::decls {extract_inductives, extract_structs}

/// `$MONAD_OWNERSHIP`'s three states. `poison` keeps the owned allocator but
/// turns every free into a 0xDE fill, so a use-after-free is deterministic.
pub type OwnershipMode {
    ownership_off,
    ownership_on,
    ownership_poison,
}

/// Pure parser for the variable's value: unset, empty and `0` are off;
/// `poison` is poison; any other non-empty value is on. Shared by codegen
/// and the CLI gate so both read one spelling.
pub def ownership_mode_of_env (v : Option String) : OwnershipMode :=
    match v {
        Option.none => OwnershipMode.ownership_off,
        Option.some raw =>
            let t : String := String.trim raw in
            if String.is_empty t || String.beq t "0" then OwnershipMode.ownership_off
            else if String.beq t "poison" then OwnershipMode.ownership_poison
            else OwnershipMode.ownership_on,
    }

pub def ownership_mode_on (m : OwnershipMode) : Bool :=
    match m {
        OwnershipMode.ownership_off => false,
        OwnershipMode.ownership_on => true,
        OwnershipMode.ownership_poison => true,
    }

/// The whole-program verdict. `owned` maps a type name (qualified, plus the
/// bare spelling when it is unambiguous) to its drop function symbol;
/// membership is the Owned verdict. `region` records every name the fixed
/// point demoted, kept as the diagnostic record of the classification (and
/// read by the unit tests). `ctor_owner` maps a constructor key to its owning
/// type, so an allocation site whose `Con.typ_name` is empty still finds the
/// verdict.
pub struct OwnershipTables {
    owned : HashMap String String,
    region : HashMap String Bool,
    ctor_owner : HashMap String String,
    ctors : HashMap String Bool,
    borrows : HashMap String Bool,
}

/// No ownership: every lookup misses, every allocation stays on the region
/// path, and no drops are emitted. This is the default build.
pub def ownership_tables_empty : OwnershipTables := {
    owned := str_map_empty,
    region := str_map_empty,
    ctor_owner := str_map_empty,
    ctors := str_map_empty,
    borrows := str_map_empty,
}

/// One value to drop at a def exit. `name` is the source binder (for the
/// bind-site match); `val` is its LLVM value.
pub struct DropBinding {
    name : Identifier,
    val : LLVMValue,
    drop_fn : String,
}

pub struct DropCandidate {
    name : Identifier,
    drop_fn : String,
}

/// One def's drop decisions. Empty means "drop nothing here" -- the
/// fail-closed outcome for a def with an unprovable candidate or a rewrite
/// (self-TCO) that makes exit drops unsound.
pub struct DropPlan {
    candidates : List DropCandidate,
}

pub def drop_plan_empty : DropPlan := { candidates := List.empty }

pub def drop_plan_for (plan : DropPlan) (name : Identifier) : Option String :=
    drop_plan_for_go name plan.candidates

#[partial]
def drop_plan_for_go (name : Identifier) (cs : List DropCandidate) : Option String :=
    match cs {
        List.empty => Option.none,
        List.cons c rest =>
            if id_eq name c.name then Option.some c.drop_fn else drop_plan_for_go name rest,
    }

// ─── Name tables ────────────────────────────────────────────────────────

/// Every declared inductive's qualified name, plus a bare-name index that
/// records ambiguity as `""` instead of picking one. A bare name that maps
/// to two types is exactly the `mk`/`cons` collision `usage.mo` already
/// fails closed on.
struct NameTable {
    qualified : HashMap String Bool,
    bare_owner : HashMap String String,
}

/// The bare tail of a rendered type name: text after the last `.` or
/// `:`. Qualification encodes the mote either as extra NamePath segments
/// (`own.Box`) or inside one identifier (`own::Box`, which is what the
/// loaded declarations actually carry), so splitting on `.` alone leaves
/// the bare alias unregistered and every lookup by a written `Box` misses.
#[partial]
def bare_name_go (s : String) (i : I64) (start : I64) : String :=
    if Bool.not (I64.lt i (String.length s)) then String.slice s start (String.length s - start)
    else
        match (String.get s i : Option U8) {
            Option.some b =>
                if U8.beq b 46u8 || U8.beq b 58u8
                then bare_name_go s (i + 1) (i + 1)
                else bare_name_go s (i + 1) start,
            Option.none => String.slice s start (String.length s - start),
        }

pub def bare_name_string (s : String) : String := bare_name_go s 0 0

/// A pointer-free primitive. Such a field can live in an Owned cell without
/// the collector needing to scan that cell -- see `field_edges_of`.
def scalar_type_name (s : String) : Bool :=
    List.contains_by (fn a b => String.beq a b) s
        ["I8", "I16", "I32", "I64", "U8", "U16", "U32", "U64", "F32", "F64"]

#[partial]
def name_table_add (name : NamePath) (acc : NameTable) : NameTable :=
    let full : String := show_name_path name in
    let q : HashMap String Bool := str_map_insert full true acc.qualified in
    let key : String := bare_name_string full in
    if String.is_empty key then { qualified := q, bare_owner := acc.bare_owner }
    else
        match str_map_lookup key acc.bare_owner {
            Option.none => { qualified := q, bare_owner := str_map_insert key full acc.bare_owner },
            Option.some prev =>
                if String.beq prev full then { qualified := q, bare_owner := acc.bare_owner }
                else { qualified := q, bare_owner := str_map_insert key "" acc.bare_owner },
        }

#[partial]
def build_name_table (inds : List Inductive) (acc : NameTable) : NameTable :=
    match inds {
        List.empty => acc,
        List.cons ind rest => build_name_table rest (name_table_add ind.name acc),
    }

/// Resolve a written type name to its qualified spelling, or `none` when it
/// names no known inductive or its bare spelling is ambiguous.
def resolve_name (t : NameTable) (s : String) : Option String :=
    match str_map_lookup s t.qualified {
        Option.some _ => Option.some s,
        Option.none =>
            match str_map_lookup s t.bare_owner {
                Option.none => Option.none,
                Option.some q => if String.is_empty q then Option.none else Option.some q,
            },
    }

def member (m : HashMap String Bool) (k : String) : Bool :=
    match str_map_lookup k m {
        Option.none => false,
        Option.some b => b,
    }

// ─── Type-term shapes ───────────────────────────────────────────────────

#[partial]
def spine_head (t : Term) : Term := match t {
    Term.ctx _ inner => spine_head inner,
    Term.app callee _arg => spine_head callee,
    _ => t,
}

#[partial]
def spine_args (t : Term) (acc : List Term) : List Term := match t {
    Term.ctx _ inner => spine_args inner acc,
    Term.app callee arg => spine_args callee (List.cons arg acc),
    _ => acc,
}

/// The written head name of a type or an application spine, e.g. `List` in
/// `List I64`, or `Point`. `none` for anything with no name (a hole, a
/// function type, an anonymous variable).
#[partial]
def head_name (t : Term) : Option String :=
    match spine_head t {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => Option.some (show_identifier id),
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

/// A carrier term for resolving `Copy` through the checker's own instance
/// table. The index is the free-variable sentinel; only the name matters.
def carrier_of_name (name : NamePath) : Term :=
    let bare : String := bare_name_string (show_name_path name) in
    if String.is_empty bare then Term.hole
    else Term.var (0 - 1) (DebugName.named (Identifier.id bare))

/// Attribute presence on an inductive declaration. Deliberately NOT named
/// `has_attr`: that is `lang::types`'s public helper (it takes an
/// `Identifier`), and a package-private name in this mote shadows the
/// imported one for every other codegen module.
def has_type_attr (name : String) (attrs : List Attribute) : Bool :=
    match find_attr_args name attrs {
        Option.some _ => true,
        Option.none => false,
    }

// ─── Classification ────────────────────────────────────────────────────

def is_candidate (scope : Scope) (names : NameTable) (ind : Inductive) : Bool :=
    List.is_empty ind.params
        && Bool.not (List.is_empty ind.constructors)
        && Bool.not (any_nullary ind.constructors)
        && Bool.not (has_type_attr "shared" ind.attrs)
        && Bool.not (has_type_attr "opaque" ind.attrs)
        && Bool.not (has_type_attr "proof" ind.attrs)
        && Bool.not (has_type_attr "linear" ind.attrs)
        && Bool.not (copy_granted scope ind.name)
        && fields_classifiable names ind.constructors

/// Every field type must be a primitive scalar or a declared type. A hole or
/// an unresolved head fails closed: the field could be a pointer, and the
/// collector cannot see through an Owned cell.
#[partial]
def fields_classifiable (names : NameTable) (ctors : List InductConstructor) : Bool :=
    match ctors {
        List.empty => true,
        List.cons c rest =>
            fields_classifiable_params names c.params && fields_classifiable names rest,
    }

#[partial]
def fields_classifiable_params (names : NameTable) (ps : List Param) : Bool :=
    match ps {
        List.empty => true,
        List.cons p rest =>
            let ok := match head_name p.type_ {
                Option.none => false,
                Option.some h =>
                    scalar_type_name h
                        || (match resolve_name names h {
                            Option.some _ => true,
                            Option.none => false,
                        }),
            } in
            ok && fields_classifiable_params names rest,
    }

/// `Copy` (or an ambiguous pair of instances) makes the type Region: a Copy
/// value is duplicated freely and must never be freed.
def copy_granted (scope : Scope) (name : NamePath) : Bool :=
    match copy_verdict scope (carrier_of_name name) {
        CopyVerdict.cv_copy => true,
        CopyVerdict.cv_ambiguous => true,
        CopyVerdict.cv_not_copy => false,
    }

#[partial]
def any_nullary (ctors : List InductConstructor) : Bool :=
    match ctors {
        List.empty => false,
        List.cons c rest =>
            if List.is_empty c.params then true else any_nullary rest,
    }

/// Every constructor is nullary, so every value is a `g_nullary` singleton in
/// static storage. Such a value is safe in an unscanned Owned cell: the
/// collector roots the singleton table, so it can never be collected.
#[partial]
def all_nullary (ctors : List InductConstructor) : Bool :=
    match ctors {
        List.empty => true,
        List.cons c rest =>
            if List.is_empty c.params then all_nullary rest else false,
    }

/// Every field type of an inductive, flattened across its constructors.
#[partial]
def field_types_of (ctors : List InductConstructor) (acc : List Term) : List Term :=
    match ctors {
        List.empty => acc,
        List.cons c rest => field_types_of rest (field_types_of_params c.params acc),
    }

#[partial]
def field_types_of_params (ps : List Param) (acc : List Term) : List Term :=
    match ps {
        List.empty => acc,
        List.cons p rest => field_types_of_params rest (List.cons p.type_ acc),
    }

/// Edges `owner <-> field head` for every type, used by the I10 closure.
///
/// Both directions matter. `owner -> field` is I10 proper: a Region value is
/// never freed, so everything it can point at must be Region too. `field ->
/// owner` is the collector rule: an Owned cell is allocated with `malloc`, so
/// Boehm does not scan it; a Region (GC-managed) pointer stored in it would be
/// invisible to the collector and could be reclaimed while the cell still
/// points at it. A field is exempt from the edge only when it is a primitive
/// scalar (pointer-free) or an all-nullary type (a `g_nullary` singleton,
/// which the collector roots in static storage).
#[partial]
def field_edges_of (names : NameTable) (static : HashMap String Bool) (owner : String) (fields : List Term) (acc : List (Pair String String)) : List (Pair String String) :=
    match fields {
        List.empty => acc,
        List.cons f rest =>
            let acc1 := match head_name f {
                Option.none => acc,
                Option.some h =>
                    if scalar_type_name h then acc
                    else
                        match resolve_name names h {
                            Option.none => acc,
                            Option.some q =>
                                if member static q
                                then acc
                                else List.cons (Pair.pair owner q) (List.cons (Pair.pair q owner) acc),
                        },
            } in
            field_edges_of names static owner rest acc1,
    }

#[partial]
def inductive_field_edges (names : NameTable) (static : HashMap String Bool) (inds : List Inductive) (acc : List (Pair String String)) : List (Pair String String) :=
    match inds {
        List.empty => acc,
        List.cons ind rest =>
            let owner : String := show_name_path ind.name in
            let acc1 := field_edges_of names static owner (field_types_of ind.constructors List.empty) acc in
            inductive_field_edges names static rest acc1,
    }

#[partial]
def struct_field_types (fs : List StructField) (acc : List Term) : List Term :=
    match fs {
        List.empty => acc,
        List.cons f rest => struct_field_types rest (List.cons f.typ acc),
    }

#[partial]
def struct_field_edges (names : NameTable) (static : HashMap String Bool) (structs : List Struct) (acc : List (Pair String String)) : List (Pair String String) :=
    match structs {
        List.empty => acc,
        List.cons s rest =>
            let owner : String := show_identifier s.name in
            let acc1 := field_edges_of names static owner (struct_field_types s.fields List.empty) acc in
            struct_field_edges names static rest acc1,
    }

/// Edges `H -> arg` for every type application in the program's type
/// positions: a Region generic demotes each type argument it can hold.
#[partial]
def application_edges_term (names : NameTable) (t : Term) (acc : List (Pair String String)) : List (Pair String String) :=
    let acc1 := application_edges_node names t acc in
    application_edges_terms names (term_children t) acc1

#[partial]
def application_edges_terms (names : NameTable) (ts : List Term) (acc : List (Pair String String)) : List (Pair String String) :=
    match ts {
        List.empty => acc,
        List.cons t rest => application_edges_terms names rest (application_edges_term names t acc),
    }

#[partial]
def application_edges_node (names : NameTable) (t : Term) (acc : List (Pair String String)) : List (Pair String String) :=
    match t {
        Term.app _ _ =>
            match head_name t {
                Option.none => acc,
                Option.some h =>
                    match resolve_name names h {
                        Option.none => acc,
                        Option.some q => application_edges_args names q (spine_args t List.empty) acc,
                    },
            },
        _ => acc,
    }

#[partial]
def application_edges_args (names : NameTable) (owner : String) (args : List Term) (acc : List (Pair String String)) : List (Pair String String) :=
    match args {
        List.empty => acc,
        List.cons a rest =>
            let acc1 := match head_name a {
                Option.none => acc,
                Option.some h =>
                    match resolve_name names h {
                        Option.none => acc,
                        Option.some q => List.cons (Pair.pair owner q) acc,
                    },
            } in
            application_edges_args names owner rest acc1,
    }

#[partial]
def application_edges_decl (names : NameTable) (d : Decl) (acc : List (Pair String String)) : List (Pair String String) :=
    match d {
        Decl.def_d def_ =>
            let acc1 := application_edges_term names def_.typ acc in
            application_edges_term names def_.term acc1,
        Decl.inductive_d ind =>
            let acc1 := application_edges_term names ind.typ acc in
            application_edges_params names ind.constructors acc1,
        Decl.struct_d s =>
            application_edges_terms names (struct_field_types s.fields List.empty) acc,
        _ => acc,
    }

#[partial]
def application_edges_params (names : NameTable) (ctors : List InductConstructor) (acc : List (Pair String String)) : List (Pair String String) :=
    match ctors {
        List.empty => acc,
        List.cons c rest =>
            let acc1 := application_edges_terms names (field_types_of_params c.params List.empty) acc in
            application_edges_params names rest acc1,
    }

#[partial]
def application_edges_decls (names : NameTable) (decls : List Decl) (acc : List (Pair String String)) : List (Pair String String) :=
    match decls {
        List.empty => acc,
        List.cons d rest => application_edges_decls names rest (application_edges_decl names d acc),
    }

/// One fixed-point round: follow every edge out of a Region name and mark
/// the target Region.
struct CloseStep {
    changed : Bool,
    region : HashMap String Bool,
}

#[partial]
def close_step (edges : List (Pair String String)) (region : HashMap String Bool) (changed : Bool) : CloseStep :=
    match edges {
        List.empty => { changed := changed, region := region },
        List.cons e rest =>
            match e {
                Pair.pair from to =>
                    if member region from && Bool.not (member region to)
                    then close_step rest (str_map_insert to true region) true
                    else close_step rest region changed,
            },
    }

#[partial]
def close_region (edges : List (Pair String String)) (region : HashMap String Bool) : HashMap String Bool :=
    let step : CloseStep := close_step edges region false in
    if step.changed then close_region edges step.region else step.region

/// The Region seed: every declared inductive that is not a candidate, plus
/// every struct. Unknown heads (scalars, `String`, opaque handles) never
/// enter the tables, so they cannot be demoted into a drop function.
#[partial]
def insert_static (names : NameTable) (full : String) (m : HashMap String Bool) : HashMap String Bool :=
    let m1 : HashMap String Bool := str_map_insert full true m in
    let key : String := bare_name_string full in
    if String.is_empty key then m1
    else
        match str_map_lookup key names.bare_owner {
            Option.some q => if String.beq q full then str_map_insert key true m1 else m1,
            Option.none => m1,
        }

/// Every type whose values are all `g_nullary` singletons -- the field types
/// an unscanned Owned cell may hold without the collector missing them.
#[partial]
def static_types_of (names : NameTable) (inds : List Inductive) (acc : HashMap String Bool) : HashMap String Bool :=
    match inds {
        List.empty => acc,
        List.cons ind rest =>
            if Bool.not (List.is_empty ind.constructors) && all_nullary ind.constructors
            then static_types_of names rest (insert_static names (show_name_path ind.name) acc)
            else static_types_of names rest acc,
    }

#[partial]
def seed_region (scope : Scope) (names : NameTable) (inds : List Inductive) (structs : List Struct) (acc : HashMap String Bool) : HashMap String Bool :=
    match inds {
        List.empty => seed_structs names structs acc,
        List.cons ind rest =>
            let full : String := show_name_path ind.name in
            let acc1 := if is_candidate scope names ind then acc else str_map_insert full true acc in
            seed_region scope names rest structs acc1,
    }

#[partial]
def seed_structs (names : NameTable) (structs : List Struct) (acc : HashMap String Bool) : HashMap String Bool :=
    match structs {
        List.empty => acc,
        List.cons s rest => seed_structs names rest (str_map_insert (show_identifier s.name) true acc),
    }

#[partial]
def candidate_names (scope : Scope) (names : NameTable) (inds : List Inductive) (acc : List String) : List String :=
    match inds {
        List.empty => acc,
        List.cons ind rest =>
            if is_candidate scope names ind
            then candidate_names scope names rest (List.cons (show_name_path ind.name) acc)
            else candidate_names scope names rest acc,
    }

#[partial]
def split_on_dot (s : String) (start : I64) (i : I64) (acc : List Identifier) : List Identifier :=
    if Bool.not (I64.lt i (String.length s)) then
        List.reverse (List.cons (Identifier.id (String.slice s start (String.length s - start))) acc)
    else
        match (String.get s i : Option U8) {
            Option.some b =>
                if U8.beq b 46u8
                then split_on_dot s (i + 1) (i + 1) (List.cons (Identifier.id (String.slice s start (i - start))) acc)
                else split_on_dot s start (i + 1) acc,
            Option.none => List.reverse acc,
        }

/// Split a rendered dotted name into identifiers. Every name in the table
/// was rendered by `show_name_path`, so `.` is unambiguous here.
def split_name_path (s : String) : List Identifier :=
    split_on_dot s 0 0 List.empty

#[partial]
def mangle_name (segs : List Identifier) (acc : String) : String :=
    match segs {
        List.empty => acc,
        List.cons s rest =>
            let part : String := show_identifier s in
            let next : String := if String.is_empty acc then part else String.concat acc (String.concat "_" part) in
            mangle_name rest next,
    }

def drop_symbol_of (full : String) : String :=
    String.concat "monad_owned_drop_" (mangle_name (split_name_path full) "")

#[partial]
def insert_owned (names : NameTable) (full : String) (symbol : String) (m : HashMap String String) : HashMap String String :=
    let m1 : HashMap String String := str_map_insert full symbol m in
    let key : String := bare_name_string full in
    if String.is_empty key then m1
    else
        match str_map_lookup key names.bare_owner {
            Option.some q => if String.beq q full then str_map_insert key symbol m1 else m1,
            Option.none => m1,
        }

#[partial]
def build_owned (names : NameTable) (candidates : List String) (region : HashMap String Bool) (acc : HashMap String String) : HashMap String String :=
    match candidates {
        List.empty => acc,
        List.cons full rest =>
            if member region full then build_owned names rest region acc
            else build_owned names rest region (insert_owned names full (drop_symbol_of full) acc),
    }

#[partial]
def count_params (ps : List Param) (n : I64) : I64 :=
    match ps {
        List.empty => n,
        List.cons _ rest => count_params rest (n + 1),
    }

#[partial]
def build_ctor_owner (type_full : String) (ctors : List InductConstructor) (acc : HashMap String String) : HashMap String String :=
    match ctors {
        List.empty => acc,
        List.cons c rest =>
            let bare : String := bare_name_string (show_name_path c.name) in
            let arity : I64 := count_params c.params 0 in
            let key : String := String.concat bare (String.concat "#" (I64.to_string arity)) in
            let acc1 : HashMap String String := str_map_insert key type_full acc in
            let qualified_key : String := String.concat type_full (String.concat "." bare) in
            build_ctor_owner type_full rest (str_map_insert qualified_key type_full acc1),
    }

#[partial]
def ctor_owners (inds : List Inductive) (acc : HashMap String String) : HashMap String String :=
    match inds {
        List.empty => acc,
        List.cons ind rest =>
            ctor_owners rest (build_ctor_owner (show_name_path ind.name) ind.constructors acc),
    }

/// Classify a whole program. `decls` must be the full elaborated decl set
/// (`CompileInput.decls`), not the reachability-filtered subset: the verdict
/// is a property of every type the program can construct.
pub def classify_program (scope : Scope) (decls : List Decl) : OwnershipTables :=
    let inds : List Inductive := extract_inductives decls in
    let structs : List Struct := extract_structs decls in
    let empty_names : NameTable := { qualified := str_map_empty, bare_owner := str_map_empty } in
    let names : NameTable := build_name_table inds empty_names in
    let static : HashMap String Bool := static_types_of names inds str_map_empty in
    let candidates : List String := candidate_names scope names inds List.empty in
    let seed : HashMap String Bool := seed_region scope names inds structs str_map_empty in
    let edges : List (Pair String String) :=
        List.append (inductive_field_edges names static inds List.empty)
            (List.append (struct_field_edges names static structs List.empty) (application_edges_decls names decls List.empty)) in
    let region : HashMap String Bool := close_region edges seed in
    let owned : HashMap String String := build_owned names candidates region str_map_empty in
    {
        owned := owned,
        region := region,
        ctor_owner := ctor_owners inds str_map_empty,
        ctors := ctor_name_set scope,
        borrows := shared_name_set scope,
    }

/// The Owned verdict for a type term: its drop function, or `none` when it
/// is Region/unknown. Used both for drop planning and for field recursion.
pub def drop_fn_for_type (tables : OwnershipTables) (typ : Term) : Option String :=
    match head_name typ {
        Option.none => Option.none,
        Option.some h => str_map_lookup h tables.owned,
    }

/// The drop function for a FRESH constructor initializer.
///
/// A `let` binder's own type is frequently a hole (`let x := Box.box 7`
/// carries no written annotation), so `BinderUse.typ` cannot name the
/// allocated type. The initializer can: a `Term.con` names its inductive,
/// and an application spine headed by a known constructor resolves through
/// the `ctor_owner` table. Anything else (a variable alias, a call result)
/// is `none`, which is what keeps `let y := x` from being dropped twice.
pub def drop_fn_for_initializer (tables : OwnershipTables) (t : Term) : Option String :=
    match term_peel t {
        Term.con con => drop_fn_for_con tables con,
        Term.app _ _ =>
            match head_name t {
                Option.none => Option.none,
                Option.some h =>
                    if member tables.ctors h
                    then ctor_key_drop tables h (List.length (spine_args t List.empty))
                    else Option.none,
            },
        _ => Option.none,
    }

#[partial]
def drop_fn_for_con (tables : OwnershipTables) (con : Con) : Option String :=
    match con {
        Con.mk name typ_name _num_args _args =>
            if List.is_empty typ_name.segments then Option.none
            else
                match str_map_lookup (show_name_path typ_name) tables.owned {
                    Option.some f => Option.some f,
                    Option.none => ctor_key_drop tables (show_identifier name) (count_opt_args con.args 0),
                },
    }

#[partial]
def count_opt_args (args : List (Option Term)) (n : I64) : I64 :=
    match args {
        List.empty => n,
        List.cons _ rest => count_opt_args rest (n + 1),
    }

def ctor_key_drop (tables : OwnershipTables) (ctor_name : String) (arity : I64) : Option String :=
    let key : String := String.concat ctor_name (String.concat "#" (I64.to_string arity)) in
    match str_map_lookup key tables.ctor_owner {
        Option.none => Option.none,
        Option.some owner => str_map_lookup owner tables.owned,
    }

/// The allocator symbol a constructor allocation must use. `owner` is
/// `Con.typ_name` when it carries the owning type (the ordinary path);
/// when it is empty the `ctor_owner` key table resolves the constructor.
pub def alloc_fn_for_ctor (tables : OwnershipTables) (ctor_name : Identifier) (owner : Option NamePath) (arity : I64) : String :=
    match resolve_ctor_owner tables ctor_name owner arity {
        Option.none => "alloc_constructor",
        Option.some o =>
            match str_map_lookup o tables.owned {
                Option.some _ => "alloc_constructor_owned",
                Option.none => "alloc_constructor",
            },
    }

def resolve_ctor_owner (tables : OwnershipTables) (ctor_name : Identifier) (owner : Option NamePath) (arity : I64) : Option String :=
    match owner {
        Option.some np =>
            if List.is_empty np.segments then ctor_key_lookup tables ctor_name arity
            else Option.some (show_name_path np),
        Option.none => ctor_key_lookup tables ctor_name arity,
    }

def ctor_key_lookup (tables : OwnershipTables) (ctor_name : Identifier) (arity : I64) : Option String :=
    let key : String := String.concat (show_identifier ctor_name) (String.concat "#" (I64.to_string arity)) in
    str_map_lookup key tables.ctor_owner

// ─── Drop planning ─────────────────────────────────────────────────────

def not_zero_mult (m : Multiplicity) : Bool :=
    match m {
        Multiplicity.zero => false,
        _ => true,
    }

/// The v1 rule: an unused, non-view, uncaptured, non-zero-multiplicity,
/// non-function binder whose type is Owned.
def binder_droppable (tables : OwnershipTables) (u : BinderUse) : Bool :=
    match BinderUse.kind u {
        BinderKind.bk_match => false,
        BinderKind.bk_lam =>
            I64.beq (BinderUse.count u) 0
                && Bool.not (BinderUse.view u)
                && I64.beq (BinderUse.captured u) 0
                && not_zero_mult (BinderUse.declared u)
                && Bool.not (typ_is_function (BinderUse.typ u)),
    }

/// A binder whose name occurs more than once cannot be matched to a bind
/// site reliably (shadowing), so it is dropped nowhere.
#[partial]
def name_occurs (name : Identifier) (uses : List BinderUse) : I64 :=
    match uses {
        List.empty => 0,
        List.cons u rest =>
            if id_eq name (BinderUse.name u) then 1 + name_occurs name rest else name_occurs name rest,
    }

/// The declared parameter types, by name. The usage walker reads each
/// leading binder's type off the `Term.lam` annotation, which elaboration
/// frequently leaves as a hole even when the def wrote the type -- so a
/// declared parameter is re-typed from `Param.type_` here.
#[partial]
def param_type_for (name : Identifier) (params : List Param) : Option Term :=
    match params {
        List.empty => Option.none,
        List.cons p rest =>
            if id_eq name p.name then Option.some p.type_ else param_type_for name rest,
    }

#[partial]
def apply_param_types (params : List Param) (uses : List BinderUse) : List BinderUse :=
    match uses {
        List.empty => List.empty,
        List.cons u rest =>
            let u2 : BinderUse := match param_type_for (BinderUse.name u) params {
                Option.some t => { u with typ := t },
                Option.none => u,
            } in
            List.cons u2 (apply_param_types params rest),
    }

#[partial]
def plan_go (tables : OwnershipTables) (all_uses : List BinderUse) (rest : List BinderUse) (acc : List DropCandidate) : List DropCandidate :=
    match rest {
        List.empty => List.reverse acc,
        List.cons u tail =>
            if binder_droppable tables u && I64.beq (name_occurs (BinderUse.name u) all_uses) 1 then
                match drop_fn_for_type tables (BinderUse.typ u) {
                    Option.some fn_ =>
                        plan_go tables all_uses tail (List.cons (DropCandidate.mk (BinderUse.name u) fn_) acc),
                    Option.none =>
                        match BinderUse.init u {
                            Option.some init =>
                                match drop_fn_for_initializer tables init {
                                    Option.some fn_ =>
                                        plan_go tables all_uses tail (List.cons (DropCandidate.mk (BinderUse.name u) fn_) acc),
                                    Option.none => plan_go tables all_uses tail acc,
                                },
                            Option.none => plan_go tables all_uses tail acc,
                        },
                }
            else plan_go tables all_uses tail acc,
    }

/// One def's plan. `params` must be the def's declared parameters and
/// `term_` its **unstripped** term: `collect_binder_uses_with_params`
/// matches the leading lambda chain against `params`, so it needs the
/// lambdas `compile_db_def_ir_body` strips before compiling.
pub def plan_def (tables : OwnershipTables) (params : List Param) (term_ : Term) : DropPlan :=
    let uses0 : List BinderUse := collect_binder_uses_with_params params tables.ctors tables.borrows term_ in
    let uses : List BinderUse := apply_param_types params uses0 in
    { candidates := plan_go tables uses uses List.empty }

// ─── Drop insertion (IR) ───────────────────────────────────────────────

#[partial]
def last_instruction (instrs : List LLVMInstruction) : Option LLVMInstruction :=
    match instrs {
        List.empty => Option.none,
        List.cons i rest =>
            match rest {
                List.empty => Option.some i,
                List.cons _ _ => last_instruction rest,
            },
    }

#[partial]
def without_last (instrs : List LLVMInstruction) : List LLVMInstruction :=
    match instrs {
        List.empty => List.empty,
        List.cons i rest =>
            match rest {
                List.empty => List.empty,
                List.cons _ _ => List.cons i (without_last rest),
            },
    }

#[partial]
def block_targets (instrs : List LLVMInstruction) : List String :=
    match last_instruction instrs {
        Option.none => List.empty,
        Option.some i =>
            match i {
                LLVMInstruction.branch _c then_l else_l => [then_l, else_l],
                LLVMInstruction.jump l => [l],
                _ => List.empty,
            },
    }

#[partial]
def block_edge_table (blocks : List LLVMBasicBlock) (acc : HashMap String (List String)) : HashMap String (List String) :=
    match blocks {
        List.empty => acc,
        List.cons b rest =>
            match b {
                LLVMBasicBlock.mk label instrs =>
                    block_edge_table rest (str_map_insert label (block_targets instrs) acc),
            },
    }

#[partial]
def reach_go (table : HashMap String (List String)) (work : List String) (seen : HashMap String Bool) : HashMap String Bool :=
    match work {
        List.empty => seen,
        List.cons l rest =>
            if member seen l then reach_go table rest seen
            else
                let seen1 : HashMap String Bool := str_map_insert l true seen in
                match str_map_lookup l table {
                    Option.none => reach_go table rest seen1,
                    Option.some next => reach_go table (List.append next rest) seen1,
                },
    }

#[partial]
def drop_instrs (drops : List DropBinding) : List LLVMInstruction :=
    match drops {
        List.empty => List.empty,
        List.cons d rest =>
            List.cons
                (LLVMInstruction.call_void (LLVMValue.call d.drop_fn LLVMType.void [d.val] false))
                (drop_instrs rest),
    }

#[partial]
def insert_into_block (reachable : HashMap String Bool) (drops : List DropBinding) (b : LLVMBasicBlock) : LLVMBasicBlock :=
    match b {
        LLVMBasicBlock.mk label instrs =>
            if member reachable label then
                match last_instruction instrs {
                    Option.none => b,
                    Option.some i =>
                        match i {
                            LLVMInstruction.ret v =>
                                LLVMBasicBlock.mk label
                                    (List.append (without_last instrs)
                                        (List.append (drop_instrs drops) [LLVMInstruction.ret v])),
                            _ => b,
                        },
                }
            else b,
    }

#[partial]
def insert_into_blocks (reachable : HashMap String Bool) (drops : List DropBinding) (blocks : List LLVMBasicBlock) : List LLVMBasicBlock :=
    match blocks {
        List.empty => List.empty,
        List.cons b rest => List.cons (insert_into_block reachable drops b) (insert_into_blocks reachable drops rest),
    }

/// Insert `call void @drop_<T>(value)` before every reachable `ret`.
///
/// Unreachable blocks are skipped: codegen emits a dead merge block whose
/// `ret` would otherwise reference values it does not dominate. Blocks that
/// end in `branch`/`jump` are left alone -- they have no exit to drop on.
/// An empty drop list returns the input list unchanged, so the default
/// build's IR is byte-identical.
pub def insert_drops_before_rets (drops : List DropBinding) (blocks : List LLVMBasicBlock) : List LLVMBasicBlock :=
    if List.is_empty drops then blocks
    else
        let reachable : HashMap String Bool := reach_go (block_edge_table blocks str_map_empty) ["entry"] str_map_empty in
        insert_into_blocks reachable drops blocks
