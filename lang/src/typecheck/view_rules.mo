/// The view-types soundness rules (`plans/type-system/view-types.md`,
/// Phase 1).
///
/// These are ERRORS on every path, regardless of a mote's `[affine] mode`
/// (`lang/mote.toml` is `warn`): a safety rule that a warn mote could
/// downgrade is not a rule. `module.mo`'s
/// `check_module_with_scope_classified` appends them to `errors` in both
/// modes.
///
/// The rules, in the order they appear below:
///
/// 1. **Forced linearity** lives in `affine.mo`'s
///    `effective_mult_with_kinds`: a `#[proof]` type is linear, a
///    `#[linear]` type is linear unless `?x` relaxes it to affine.
///    `?`/`%` on a proof is rejected there (`proof_erased_binder`).
/// 2. **No Copy/Clone**: a declared instance for one is rejected
///    (`check_instance_kinds`). The affine rule consults
///    `is_linear_type`/`is_proof_type` BEFORE `is_copy`, so no implicit
///    ω-route reaches a linear type; an explicit `Copy.copy` would need
///    the instance this rule rejects.
/// 3. **No capture (P10)**: a linear or proof value used under a nested
///    lambda. The closure body counts it once but may run many times, and
///    eager fibers run closures on other threads.
/// 4. **No re-readable container (P11)**: a linear/proof value passed to
///    `Shared.of` (counted as `BinderUse.borrowed`), or a signature/field
///    typed `Shared`/`Ref`/`Array` over one.
/// 5. **Proofs are phantom in v1**: a user def may not bind or return a
///    proof type, because nothing erases it yet.
///
/// Deliberately NOT a rule in v1: passing a linear value to an arbitrary
/// polymorphic function whose parameter type is a bare type variable. That
/// needs the callee's instantiated signature at the call site (the same
/// interprocedural information gap as `Shared.get`'s owning-argument case,
/// QTT Known Gap 12) and is documented as a residual.
use lib::types {
  Decl, Def, Identifier, InductConstructor, Inductive, Instance, NamePath,
  Param, Scope, Struct, StructField, Term, TypeError, show_identifier, show_name_path,
}
use lib::typecheck::usage {
  BinderUse, attribute_binder_types, collect_binder_uses_with_params,
  ctor_name_set, shared_name_set,
}
use lib::typecheck::type_kinds {
  TypeKinds, container_wraps_linear, is_linear_or_proof, is_proof_type,
  mentions_linear_or_proof, type_kinds,
}
use std::map {HashMap}
use lib::typecheck::diagnostic {render_type_error}

/// Every view/proof diagnostic a module earns. Built once per module:
/// the kind sets and the two name sets are scope scans, not per-binder
/// lookups.
pub def check_module_view_errors (scope : Scope) (decl_list : List Decl) : List TypeError :=
    let kinds : TypeKinds := type_kinds scope in
    let ctors : HashMap String Bool := ctor_name_set scope in
    let borrows : HashMap String Bool := shared_name_set scope in
    check_module_view_go kinds ctors borrows scope decl_list

#[partial]
def check_module_view_go (kinds : TypeKinds) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (scope : Scope) (decl_list : List Decl) : List TypeError :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            List.append (check_decl_view kinds ctors borrows scope d)
                        (check_module_view_go kinds ctors borrows scope rest),
    }

/// The same errors, rendered with the owning declaration's name as the
/// diagnostic context. Always `error:` — a warn mote must not downgrade a
/// safety rule.
pub def check_module_view_diags (path : Option String) (scope : Scope) (decl_list : List Decl) : List String :=
    let kinds : TypeKinds := type_kinds scope in
    let ctors : HashMap String Bool := ctor_name_set scope in
    let borrows : HashMap String Bool := shared_name_set scope in
    render_module_view_go kinds ctors borrows scope decl_list path

#[partial]
def render_module_view_go (kinds : TypeKinds) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (scope : Scope) (decl_list : List Decl) (path : Option String) : List String :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            List.append
                (render_view_errors (decl_context_name d) path
                    (check_decl_view kinds ctors borrows scope d))
                (render_module_view_go kinds ctors borrows scope rest path),
    }

#[partial]
def render_view_errors (context_name : String) (path : Option String) (errs : List TypeError) : List String :=
    match errs {
        List.empty => List.empty,
        List.cons e rest =>
            List.cons (render_type_error context_name path e)
                     (render_view_errors context_name path rest),
    }

#[partial]
def decl_context_name (d : Decl) : String :=
    match d {
        Decl.def_d df => show_name_path df.name,
        Decl.inductive_d ind =>
            match ind { Inductive.mk name _params _typ _ctors _attrs _vis => show_name_path name },
        Decl.struct_d s =>
            match s { Struct.mk name _fields _attrs _vis => show_identifier name },
        Decl.instance_d ins =>
            match ins { Instance.mk name _cls _cs _args _vis _params _defs => show_identifier name },
        _ => "",
    }

#[partial]
def check_decl_view (kinds : TypeKinds) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (scope : Scope) (d : Decl) : List TypeError :=
    match d {
        Decl.def_d df =>
            if is_dict_value_def df
            then List.empty
            else check_def_view kinds ctors borrows scope df,
        Decl.inductive_d ind => check_inductive_shapes kinds ind,
        Decl.struct_d s => check_struct_shapes kinds s,
        Decl.instance_d ins => check_instance_kinds kinds ins,
        Decl.scoped_open_d _path _filter inner =>
            check_decl_view kinds ctors borrows scope inner,
        _ => List.empty,
    }

/// A `promote_instance_defs` dictionary value (`__Dict_Class_Args`) is a
/// codegen artifact, not source; its body uses a sentinel `Term.var 0`
/// convention. Same skip as `module.mo`'s own.
#[partial]
def is_dict_value_def (df : Def) : Bool :=
    String.starts_with "__Dict_" (last_name_segment (show_name_path df.name))

/// The segment after the LAST `::` (or the whole string).
/// `name_text`'s `unqualify_def_name` is the first-`::` twin; this needs
/// the last-`::` spelling, so it keeps its own walk.
#[partial]
def last_name_segment (s : String) : String :=
    let idx : I64 := last_sep_index s 0 (String.length s) (0 - 1) in
    if I64.lt idx 0 then s
    else String.slice s (idx + 2) (String.length s - idx - 2)

#[partial]
def last_sep_index (s : String) (i : I64) (n : I64) (found : I64) : I64 :=
    if I64.gt (i + 2) n then found
    else if String.beq (String.slice s i 2) "::" then last_sep_index s (i + 1) n i
    else last_sep_index s (i + 1) n found

// ─── A def ─────────────────────────────────────────────────────────

#[partial]
def check_def_view (kinds : TypeKinds) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (scope : Scope) (d : Def) : List TypeError :=
    let shape : List TypeError :=
        if container_wraps_linear kinds d.typ
        then List.cons (TypeError.view_in_container d.typ) List.empty
        else List.empty in
    let params : List TypeError := check_param_shapes kinds d.params in
    let returned : List TypeError := check_return_shape kinds d.typ in
    let body : List TypeError := check_def_body_view kinds scope ctors borrows d in
    List.append shape (List.append params (List.append returned body))

#[partial]
def check_param_shapes (kinds : TypeKinds) (params : List Param) : List TypeError :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            let here : List TypeError := param_shape_errors kinds p in
            List.append here (check_param_shapes kinds rest),
    }

def param_shape_errors (kinds : TypeKinds) (p : Param) : List TypeError :=
    match p {
        Param.mk name typ _mult _default _attrs =>
            let proof : List TypeError :=
                if is_proof_type kinds typ
                then List.cons (TypeError.proof_at_runtime_position name typ) List.empty
                else List.empty in
            let shape : List TypeError :=
                if container_wraps_linear kinds typ
                then List.cons (TypeError.view_in_container typ) List.empty
                else List.empty in
            List.append proof shape,
    }

#[partial]
def check_return_shape (kinds : TypeKinds) (t : Term) : List TypeError :=
    let ret : Term := pi_codomain t in
    if is_proof_type kinds ret
    then List.cons (TypeError.proof_at_runtime_position (Identifier.id "result") ret) List.empty
    else if container_wraps_linear kinds ret
    then List.cons (TypeError.view_in_container ret) List.empty
    else List.empty

/// Peel `ctx` and every `pi`, leaving the codomain. `def`'s `typ` is the
/// full parameter chain; its codomain is the declared return type.
#[partial]
def pi_codomain (t : Term) : Term :=
    match t {
        Term.ctx _loc inner => pi_codomain inner,
        Term.pi _b _arg ret => pi_codomain ret,
        _ => t,
    }

#[partial]
def check_def_body_view (kinds : TypeKinds) (scope : Scope) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (d : Def) : List TypeError :=
    let us : List BinderUse :=
        attribute_binder_types scope
            (collect_binder_uses_with_params d.params ctors borrows d.term) in
    check_binder_view_go kinds us

#[partial]
def check_binder_view_go (kinds : TypeKinds) (us : List BinderUse) : List TypeError :=
    match us {
        List.empty => List.empty,
        List.cons u rest =>
            List.append (binder_view_errors kinds u) (check_binder_view_go kinds rest),
    }

def binder_view_errors (kinds : TypeKinds) (u : BinderUse) : List TypeError :=
    let typ : Term := BinderUse.typ u in
    let name : Identifier := BinderUse.name u in
    if is_proof_type kinds typ then
        let capture : List TypeError := captured_error name typ u in
        let stored : List TypeError := container_error name typ u in
        // A proof has no run-time representation; owning it (storing it
        // in a constructor or returning it) is the v1-unsupported shape.
        let owning : List TypeError :=
            if I64.gt (BinderUse.owning u) 0
            then List.cons (TypeError.proof_at_runtime_position name typ) List.empty
            else List.empty in
        List.append capture (List.append stored owning)
    else if is_linear_or_proof kinds typ then
        List.append (captured_error name typ u) (container_error name typ u)
    // A CONTAINER that holds a linear/proof type is not itself linear
    // (`Ref (Cell A)`'s head is `Ref`), but wrapping it in `Shared` is the
    // same hazard one level down: `Shared` is `Copy`, `Ref.get` twice would
    // yield two Cells. Reject the `Shared.of` of any type that mentions one.
    else if I64.gt (BinderUse.borrowed u) 0 && mentions_linear_or_proof kinds typ
    then List.cons (TypeError.view_stored_in_container name typ) List.empty
    else List.empty

def captured_error (name : Identifier) (typ : Term) (u : BinderUse) : List TypeError :=
    if I64.gt (BinderUse.captured u) 0
    then List.cons (TypeError.view_captured name typ) List.empty
    else List.empty

def container_error (name : Identifier) (typ : Term) (u : BinderUse) : List TypeError :=
    // `borrowed` is the count of direct `Shared.of` arguments -- the
    // affine rule exempts them, so this is the one place that sees them.
    if I64.gt (BinderUse.borrowed u) 0
    then List.cons (TypeError.view_stored_in_container name typ) List.empty
    else List.empty

// ─── Inductives, structs, instances ─────────────────────────────────

#[partial]
def check_inductive_shapes (kinds : TypeKinds) (ind : Inductive) : List TypeError :=
    match ind {
        Inductive.mk _name _params _typ ctors _attrs _vis =>
            check_ctor_shapes kinds ctors,
    }

#[partial]
def check_ctor_shapes (kinds : TypeKinds) (ctors : List InductConstructor) : List TypeError :=
    match ctors {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                InductConstructor.mk _name params _typ =>
                    List.append (check_param_shapes kinds params)
                                (check_ctor_shapes kinds rest),
            },
    }

#[partial]
def check_struct_shapes (kinds : TypeKinds) (s : Struct) : List TypeError :=
    match s {
        Struct.mk _name fields _attrs _vis => check_field_shapes kinds fields,
    }

#[partial]
def check_field_shapes (kinds : TypeKinds) (fields : List StructField) : List TypeError :=
    match fields {
        List.empty => List.empty,
        List.cons f rest =>
            match f {
                StructField.mk name typ _default _mult =>
                    let here : List TypeError :=
                        if is_proof_type kinds typ
                        then List.cons (TypeError.proof_at_runtime_position name typ) List.empty
                        else if container_wraps_linear kinds typ
                        then List.cons (TypeError.view_in_container typ) List.empty
                        else List.empty in
                    List.append here (check_field_shapes kinds rest),
            },
    }

#[partial]
def check_instance_kinds (kinds : TypeKinds) (ins : Instance) : List TypeError :=
    match ins {
        Instance.mk _name cls _constraints args _vis _implicit _defs =>
            if is_copy_or_clone cls then check_instance_args kinds args
            else List.empty,
    }

def is_copy_or_clone (cls : NamePath) : Bool :=
    match cls.segments {
        List.cons s rest =>
            List.is_empty rest
                && (String.beq (show_identifier s) "Copy"
                    || String.beq (show_identifier s) "Clone"),
        List.empty => false,
    }

#[partial]
def check_instance_args (kinds : TypeKinds) (args : List Term) : List TypeError :=
    match args {
        List.empty => List.empty,
        List.cons t rest =>
            let here : List TypeError :=
                if is_linear_or_proof kinds t
                then List.cons (TypeError.proof_copied t) List.empty
                else List.empty in
            List.append here (check_instance_args kinds rest),
    }
