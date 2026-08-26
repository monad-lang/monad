/// Data-shape conversions between self-hosted `Term`/`Decl`/`Inductive`/
/// `Struct` (`lang/types.mo`) and the reflection-as-data `Value`
/// (`lang/core_value.mo`) shape of `init/meta.mo`'s `TypeInfo`/`CtorInfo`/
/// `FieldInfo`/`Expr`/`MatchArm`/`Param`/`Decl` types -- mirrors
/// `core/src/eval/meta_reflect.rs` (Rust). Pure: no evaluation, no IO.
/// `lang/typecheck/meta_eval.mo` is the sibling module that actually
/// EVALUATES a meta-`def` against the `Value` this module builds; this
/// module only converts data shapes on both sides of that call.
///
/// **Constructor tags are hardcoded, not looked up.** `TypeInfo`/
/// `CtorInfo`/`FieldInfo` are single-constructor types (`init/meta.mo`),
/// so their own constructor's tag is always 0 -- no lookup needed.
/// `Expr`/`Decl`/`MatchArm`/`Param` are also types THIS design fully
/// owns (`init/meta.mo`), so their tags are hardcoded directly from that
/// file's own literal declaration order below, matching this whole
/// codebase's own established precedent for this exact situation
/// (`lang/core_eval.mo`'s `bool_value`/`lang/lower_core_ir.mo`'s own doc
/// comment on `Bool`'s hardcoded true=0/false=1 tag order). `List`/
/// `Option`/`Bool` (prelude types) are hardcoded the same way, citing
/// `init/prelude.mo`'s own literal declaration order. If any of these
/// declarations are ever reordered, this file's own tests below (which
/// exercise real round-trips) will catch it.
///
/// **De-Bruijn locals convention.** Reifying `Expr.e_lam`/`e_match`/a
/// `Decl.d_def`'s own `params` into real `Term.lam`/`Literal.match_`
/// nodes needs to assign correct de-Bruijn indices to any nested
/// `e_var` reference that names a LOCALLY bound name (a lambda param, a
/// match-arm-bound field, an outer `d_def` param) -- confirmed directly
/// against `lang/typecheck/infer.mo`'s `prepend_typed` (the type
/// checker's own positional local-type list builder for match-case
/// arg lists) that the convention throughout this codebase is: the
/// LAST-declared name in a same-level binder group ends up de-Bruijn
/// index 0 (innermost), matching `lang/core_eval.mo`'s own
/// `extend_env_with_fields`/`dispatch_arm` runtime behavior exactly.
/// `push_locals` below is the one place that convention is applied.
use lang.core_eval {value_as_i64, value_as_str}
use lang.core_ir {IrLit}
use lang.core_value {Value}
use lang.scope {struct_fields_to_params}
use lang.types {
  Attribute, Decl, Def, Identifier, InductConstructor,
  Inductive, MatchCase, ModulePath, Param, Struct,
  Term, TypeConstraint, show_module_path,
}

def sentinel : I64 := -1

// ─── Value-construction helpers (host -> Value, the INPUT side) ────────

def str_val (s : String) : Value := Value.v_lit (IrLit.ir_str s)
def num_val (n : I64) : Value := Value.v_lit (IrLit.ir_num n NumSuffix.i64)
def bool_val (b : Bool) : Value := if b then Value.v_con 0 List.empty else Value.v_con 1 List.empty

/// `List A` -- `List.empty`/`List.cons` are `init/prelude.mo`'s first
/// two declared constructors (tags 0/1 respectively).
#[partial]
def list_value (xs : List Value) : Value :=
    match xs {
        List.empty => Value.v_con 0 List.empty,
        List.cons hd rest => Value.v_con 1 (List.cons hd (List.cons (list_value rest) List.empty)),
    }

def e_var_val (name : String) : Value := Value.v_con 0 (List.cons (str_val name) List.empty)
def e_str_val (value : String) : Value := Value.v_con 1 (List.cons (str_val value) List.empty)
def e_int_val (n : I64) : Value := Value.v_con 2 (List.cons (num_val n) List.empty)
def e_app_val (f : Value) (a : Value) : Value := Value.v_con 4 (List.cons f (List.cons a List.empty))

def field_info_val (name : Value) (typ : Value) (attrs : Value) : Value :=
    Value.v_con 0 (List.cons name (List.cons typ (List.cons attrs List.empty)))

def ctor_info_val (name : Value) (fields : Value) : Value :=
    Value.v_con 0 (List.cons name (List.cons fields List.empty))

def type_info_val (name : Value) (ctors : Value) : Value :=
    Value.v_con 0 (List.cons name (List.cons ctors List.empty))

// ─── Resolving the target type `T` -- Inductive/Struct collection ──────

/// Every `Inductive` reachable in `decl_list`, including a `Decl.struct_d`
/// converted into the same single-`mk`-constructor shape scope-building
/// synthesizes (`lang/scope.mo`'s `build_scope_struct`) -- reuses
/// `struct_fields_to_params` directly rather than duplicating that
/// synthesis logic.
#[partial]
def collect_inductives (decl_list : List Decl) : List Inductive :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.inductive_d ind => List.cons ind (collect_inductives rest),
                Decl.struct_d s => List.cons (struct_to_inductive s) (collect_inductives rest),
                _ => collect_inductives rest,
            },
    }

def struct_to_inductive (s : Struct) : Inductive :=
    match s {
        Struct.mk name fields vis =>
            let type_mp : ModulePath := ModulePath.mp (List.cons name List.empty) in
            let mk_mp : ModulePath := ModulePath.mp (List.cons (Identifier.id "mk") List.empty) in
            let mk_params : List Param := struct_fields_to_params fields in
            let mk_con : InductConstructor := InductConstructor.mk mk_mp mk_params Term.hole in
            Inductive.mk type_mp List.empty Term.hole (List.cons mk_con List.empty) List.empty vis,
    }

def inductive_bare_name (ind : Inductive) : String :=
    match ind { Inductive.mk name _ _ _ _ _ => show_module_path name } // single-segment -- no dots

#[partial]
def find_inductive_by_bare_name (inds : List Inductive) (name : String) : Option Inductive :=
    match inds {
        List.empty => Option.none,
        List.cons ind rest =>
            if String.beq (inductive_bare_name ind) name
            then Option.some ind
            else find_inductive_by_bare_name rest name,
    }

/// Extract `T`'s own bare type name from the `Term` `reflect_type_info!`
/// was invoked with -- the only shape this corpus ever needs: a plain
/// (possibly still-sentinel-idx, DebugName-named) variable reference.
def term_free_var_name (t : Term) : Option String :=
    match t {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => Option.some (show_identifier_ id),
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

def show_identifier_ (id : Identifier) : String := match id { Identifier.id s => s }

// ─── Input side: Inductive -> TypeInfo Value ────────────────────────────

def ctor_bare_name (ctor : InductConstructor) : String :=
    match ctor { InductConstructor.mk name _ _ => show_module_path name }

def attr_bare_name (a : Attribute) : String :=
    match a { Attribute.mk name _ => show_identifier_ name }

#[partial]
def attr_names_val (attrs : List Attribute) : Value :=
    list_value (attr_names_val_list attrs)

#[partial]
def attr_names_val_list (attrs : List Attribute) : List Value :=
    match attrs {
        List.empty => List.empty,
        List.cons a rest => List.cons (str_val (attr_bare_name a)) (attr_names_val_list rest),
    }

def field_info_value (p : Param) : Result String Value :=
    match p {
        Param.mk pname ptyp _mult _default pattrs =>
            match term_to_expr_value ptyp {
                Result.ok typ_val => Result.ok (field_info_val (str_val (show_identifier_ pname)) typ_val (attr_names_val pattrs)),
                Result.err e => Result.err e,
            },
    }

#[partial]
def fields_value (params : List Param) : Result String (List Value) :=
    match params {
        List.empty => Result.ok List.empty,
        List.cons p rest =>
            match field_info_value p {
                Result.err e => Result.err e,
                Result.ok fv =>
                    match fields_value rest {
                        Result.err e => Result.err e,
                        Result.ok fvs => Result.ok (List.cons fv fvs),
                    },
            },
    }

def ctor_info_value (ctor : InductConstructor) : Result String Value :=
    match ctor {
        InductConstructor.mk _name params _typ =>
            match fields_value params {
                Result.err e => Result.err e,
                Result.ok fvs => Result.ok (ctor_info_val (str_val (ctor_bare_name ctor)) (list_value fvs)),
            },
    }

#[partial]
def ctors_value (ctors : List InductConstructor) : Result String (List Value) :=
    match ctors {
        List.empty => Result.ok List.empty,
        List.cons c rest =>
            match ctor_info_value c {
                Result.err e => Result.err e,
                Result.ok cv =>
                    match ctors_value rest {
                        Result.err e => Result.err e,
                        Result.ok cvs => Result.ok (List.cons cv cvs),
                    },
            },
    }

/// The one real INPUT-side entry point: `Inductive` -> a `Value` shaped
/// exactly like `init/meta.mo`'s `TypeInfo`, ready to hand to a meta-def
/// via `lang/typecheck/meta_eval.mo`.
def build_type_info_value (ind : Inductive) : Result String Value :=
    match ind {
        Inductive.mk _name _params _typ constructors _attrs _vis =>
            match ctors_value constructors {
                Result.err e => Result.err e,
                Result.ok cvs => Result.ok (type_info_val (str_val (inductive_bare_name ind)) (list_value cvs)),
            },
    }

/// `Term` -> `Expr` Value -- deliberately as limited as `init/meta.mo`'s
/// own `Expr` surface (a field's declared TYPE is the only thing this
/// direction is ever used for in this corpus): a plain var reference,
/// an application chain, or a string/int literal. Anything else is a
/// clear, immediate error rather than a silently-wrong reflection.
#[partial]
def term_to_expr_value (t : Term) : Result String Value :=
    match t {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => Result.ok (e_var_val (show_identifier_ id)),
                DebugName.unnamed => Result.err "term_to_expr_value: unnamed free variable",
            },
        Term.app f a =>
            match term_to_expr_value f {
                Result.err e => Result.err e,
                Result.ok fv =>
                    match term_to_expr_value a {
                        Result.err e => Result.err e,
                        Result.ok av => Result.ok (e_app_val fv av),
                    },
            },
        Term.lit lit_ =>
            match lit_ {
                Literal.str s => Result.ok (e_str_val s),
                Literal.num n _suffix => Result.ok (e_int_val n),
                _ => Result.err "term_to_expr_value: unsupported literal shape",
            },
        _ => Result.err "term_to_expr_value: unsupported term shape",
    }

// ─── Output side: reify a computed `Value` back into real Decls ────────

/// Push a same-level group of binder names onto a locals stack, per this
/// file's own doc comment: the LAST name in `names` ends up innermost
/// (index 0). Used uniformly for `e_lam`'s single param, a `d_def`'s own
/// top-level params, and a match arm's field binders.
def push_locals (names : List String) (locals : List String) : List String :=
    List.append (List.reverse names) locals

#[partial]
def local_index_of_go (i : I64) (locals : List String) (name : String) : Option I64 :=
    match locals {
        List.empty => Option.none,
        List.cons hd rest => if String.beq hd name then Option.some i else local_index_of_go (i + 1) rest name,
    }

def local_index_of (locals : List String) (name : String) : Option I64 :=
    local_index_of_go 0 locals name

def var_term (locals : List String) (name : String) : Term :=
    match local_index_of locals name {
        Option.some idx => Term.var idx (DebugName.named (Identifier.id name)),
        Option.none => Term.var sentinel (DebugName.named (Identifier.id name)),
    }

/// A `Value` shaped as a `List A` (`v_con 1 [head, tail]` /
/// `v_con 0 []`) -> a plain `List Value`, or a clear error if `v`
/// isn't actually list-shaped -- a genuine "the meta-def returned
/// something malformed" condition, not an internal bug.
#[partial]
def value_list_to_values (v : Value) : Result String (List Value) :=
    match v {
        Value.v_con tag args =>
            if I64.beq tag 0 then Result.ok List.empty
            else if I64.beq tag 1 then
                match args {
                    List.cons hd rest_args =>
                        match rest_args {
                            List.cons tl _ =>
                                match value_list_to_values tl {
                                    Result.err e => Result.err e,
                                    Result.ok tail_vs => Result.ok (List.cons hd tail_vs),
                                },
                            List.empty => Result.err "malformed list value: cons missing tail",
                        },
                    List.empty => Result.err "malformed list value: cons missing head",
                }
            else Result.err "expected a list value (List.empty/cons), got an unrecognized constructor tag",
        _ => Result.err "expected a list value, got a non-constructor value",
    }

def value_string_list (v : Value) : Result String (List String) :=
    match value_list_to_values v {
        Result.err e => Result.err e,
        Result.ok vs => strings_of_values vs,
    }

#[partial]
def strings_of_values (vs : List Value) : Result String (List String) :=
    match vs {
        List.empty => Result.ok List.empty,
        List.cons hd rest =>
            match value_as_str hd {
                Option.none => Result.err "expected a String value",
                Option.some s =>
                    match strings_of_values rest {
                        Result.err e => Result.err e,
                        Result.ok ss => Result.ok (List.cons s ss),
                    },
            },
    }

/// `Expr` Value -> `Term`, in de-Bruijn scope `locals` (innermost
/// first). Tags mirror `init/meta.mo`'s own `Expr` declaration order
/// (this file's own doc comment): 0=e_var 1=e_str 2=e_int 3=e_bool
/// 4=e_app 5=e_lam 6=e_if 7=e_match 8=e_ctor.
#[partial]
def reify_expr_value (locals : List String) (v : Value) : Result String Term :=
    match v {
        Value.v_con tag args =>
            if I64.beq tag 0 then reify_e_var locals args
            else if I64.beq tag 1 then reify_e_str args
            else if I64.beq tag 2 then reify_e_int args
            else if I64.beq tag 3 then reify_e_bool args
            else if I64.beq tag 4 then reify_e_app locals args
            else if I64.beq tag 5 then reify_e_lam locals args
            else if I64.beq tag 6 then reify_e_if locals args
            else if I64.beq tag 7 then reify_e_match locals args
            else if I64.beq tag 8 then reify_e_ctor locals args
            else Result.err "reify_expr_value: unrecognized Expr constructor tag",
        _ => Result.err "reify_expr_value: expected an Expr value (v_con)",
    }

def reify_e_var (locals : List String) (args : List Value) : Result String Term :=
    match args {
        List.cons name_val _ =>
            match value_as_str name_val {
                Option.some name => Result.ok (var_term locals name),
                Option.none => Result.err "e_var: expected a String name",
            },
        List.empty => Result.err "e_var: missing name arg",
    }

def reify_e_str (args : List Value) : Result String Term :=
    match args {
        List.cons v_val _ =>
            match value_as_str v_val {
                Option.some s => Result.ok (Term.lit (Literal.str s)),
                Option.none => Result.err "e_str: expected a String value",
            },
        List.empty => Result.err "e_str: missing value arg",
    }

def reify_e_int (args : List Value) : Result String Term :=
    match args {
        List.cons v_val _ =>
            match value_as_i64 v_val {
                Option.some n => Result.ok (Term.lit (Literal.num n NumSuffix.i64)),
                Option.none => Result.err "e_int: expected an I64 value",
            },
        List.empty => Result.err "e_int: missing value arg",
    }

/// A `Bool` VALUE argument (the runtime value carried by `e_bool`'s own
/// `value : Bool` field) -- tag 0 = true, 1 = false, per
/// `init/prelude.mo`'s own declaration order (matches
/// `lang/core_eval.mo`'s `bool_value`).
def value_as_bool_tag (v : Value) : Option Bool :=
    match v {
        Value.v_con tag _ =>
            if I64.beq tag 0 then Option.some true
            else if I64.beq tag 1 then Option.some false
            else Option.none,
        _ => Option.none,
    }

/// Reifies to a bare `true`/`false` global reference -- the same shape
/// ordinary parsed Monad source uses (`Literal` has no dedicated bool
/// variant; `true`/`false` are ordinary identifiers resolved against
/// `Bool`'s two nullary constructors).
def reify_e_bool (args : List Value) : Result String Term :=
    match args {
        List.cons v_val _ =>
            match value_as_bool_tag v_val {
                Option.some b => Result.ok (Term.var sentinel (DebugName.named (Identifier.id (if b then "true" else "false")))),
                Option.none => Result.err "e_bool: expected a Bool value",
            },
        List.empty => Result.err "e_bool: missing value arg",
    }

def reify_e_app (locals : List String) (args : List Value) : Result String Term :=
    match args {
        List.cons f_val rest =>
            match rest {
                List.cons a_val _ =>
                    match reify_expr_value locals f_val {
                        Result.err e => Result.err e,
                        Result.ok f_term =>
                            match reify_expr_value locals a_val {
                                Result.err e => Result.err e,
                                Result.ok a_term => Result.ok (Term.app f_term a_term),
                            },
                    },
                List.empty => Result.err "e_app: missing arg operand",
            },
        List.empty => Result.err "e_app: missing func operand",
    }

def reify_e_lam (locals : List String) (args : List Value) : Result String Term :=
    match args {
        List.cons name_val rest1 =>
            match rest1 {
                List.cons typ_val rest2 =>
                    match rest2 {
                        List.cons body_val _ =>
                            match value_as_str name_val {
                                Option.none => Result.err "e_lam: expected a String param_name",
                                Option.some pname =>
                                    match reify_expr_value locals typ_val {
                                        Result.err e => Result.err e,
                                        Result.ok ptyp_term =>
                                            match reify_expr_value (push_locals (List.cons pname List.empty) locals) body_val {
                                                Result.err e => Result.err e,
                                                Result.ok body_term =>
                                                    Result.ok (Term.lam (DebugName.named (Identifier.id pname)) ptyp_term body_term),
                                            },
                                    },
                            },
                        List.empty => Result.err "e_lam: missing body",
                    },
                List.empty => Result.err "e_lam: missing param_typ",
            },
        List.empty => Result.err "e_lam: missing param_name",
    }

def reify_e_if (locals : List String) (args : List Value) : Result String Term :=
    match args {
        List.cons cond_val rest1 =>
            match rest1 {
                List.cons then_val rest2 =>
                    match rest2 {
                        List.cons else_val _ =>
                            match reify_expr_value locals cond_val {
                                Result.err e => Result.err e,
                                Result.ok cond_term =>
                                    match reify_expr_value locals then_val {
                                        Result.err e => Result.err e,
                                        Result.ok then_term =>
                                            match reify_expr_value locals else_val {
                                                Result.err e => Result.err e,
                                                Result.ok else_term =>
                                                    Result.ok (Term.lit (Literal.if_ cond_term then_term else_term)),
                                            },
                                    },
                            },
                        List.empty => Result.err "e_if: missing else_",
                    },
                List.empty => Result.err "e_if: missing then_",
            },
        List.empty => Result.err "e_if: missing cond",
    }

/// `e_ctor ctor_name args` -- `ctor_name` is already the fully-qualified
/// dotted name (e.g. "Point.mk", built by the CALLER via
/// `String.concat`, see `std/derive.mo`'s `lens_setter`) -- reifies to
/// a free `Term.var` (never a local: a qualified dotted name can never
/// collide with a bare field/param binder) applied left-to-right over
/// each reified arg, mirroring the Rust reference's own documented
/// reason for this shape: only the `Var`+`App` path lets the type
/// checker correctly instantiate a constructor's type parameters, not
/// a raw `Term.con`.
def reify_e_ctor (locals : List String) (args : List Value) : Result String Term :=
    match args {
        List.cons ctor_name_val rest =>
            match rest {
                List.cons ctor_args_val _ =>
                    match value_as_str ctor_name_val {
                        Option.none => Result.err "e_ctor: expected a String ctor_name",
                        Option.some ctor_name =>
                            match value_list_to_values ctor_args_val {
                                Result.err e => Result.err e,
                                Result.ok arg_vals =>
                                    match reify_exprs locals arg_vals {
                                        Result.err e => Result.err e,
                                        Result.ok arg_terms =>
                                            Result.ok (apply_chain (Term.var sentinel (DebugName.named (Identifier.id ctor_name))) arg_terms),
                                    },
                            },
                    },
                List.empty => Result.err "e_ctor: missing args",
            },
        List.empty => Result.err "e_ctor: missing ctor_name",
    }

#[partial]
def reify_exprs (locals : List String) (vs : List Value) : Result String (List Term) :=
    match vs {
        List.empty => Result.ok List.empty,
        List.cons hd rest =>
            match reify_expr_value locals hd {
                Result.err e => Result.err e,
                Result.ok t =>
                    match reify_exprs locals rest {
                        Result.err e => Result.err e,
                        Result.ok ts => Result.ok (List.cons t ts),
                    },
            },
    }

#[partial]
def apply_chain (f : Term) (args : List Term) : Term :=
    match args {
        List.empty => f,
        List.cons hd rest => apply_chain (Term.app f hd) rest,
    }

def reify_e_match (locals : List String) (args : List Value) : Result String Term :=
    match args {
        List.cons scrutinee_val rest =>
            match rest {
                List.cons arms_val _ =>
                    match reify_expr_value locals scrutinee_val {
                        Result.err e => Result.err e,
                        Result.ok scrutinee_term =>
                            match value_list_to_values arms_val {
                                Result.err e => Result.err e,
                                Result.ok arm_vals =>
                                    match reify_match_arms locals arm_vals {
                                        Result.err e => Result.err e,
                                        Result.ok cases => Result.ok (Term.lit (Literal.match_ scrutinee_term cases)),
                                    },
                            },
                    },
                List.empty => Result.err "e_match: missing arms",
            },
        List.empty => Result.err "e_match: missing scrutinee",
    }

#[partial]
def reify_match_arms (locals : List String) (arm_vals : List Value) : Result String (List MatchCase) :=
    match arm_vals {
        List.empty => Result.ok List.empty,
        List.cons a rest =>
            match reify_match_arm locals a {
                Result.err e => Result.err e,
                Result.ok case_ =>
                    match reify_match_arms locals rest {
                        Result.err e => Result.err e,
                        Result.ok cases => Result.ok (List.cons case_ cases),
                    },
            },
    }

/// A `MatchArm` Value (`init/meta.mo`'s single-ctor `match_arm ctor_name
/// binders body`, tag 0) -> a real `MatchCase`. The field binders (in
/// DECLARATION order, matching `case_.args`'s own expected shape) get
/// pushed onto `locals` per `push_locals`'s convention before reifying
/// `body`.
def reify_match_arm (locals : List String) (v : Value) : Result String MatchCase :=
    match v {
        Value.v_con _tag args =>
            match args {
                List.cons ctor_name_val rest1 =>
                    match rest1 {
                        List.cons binders_val rest2 =>
                            match rest2 {
                                List.cons body_val _ =>
                                    match value_as_str ctor_name_val {
                                        Option.none => Result.err "MatchArm: expected a String ctor_name",
                                        Option.some ctor_name =>
                                            match value_string_list binders_val {
                                                Result.err e => Result.err e,
                                                Result.ok binder_names =>
                                                    match reify_expr_value (push_locals binder_names locals) body_val {
                                                        Result.err e => Result.err e,
                                                        Result.ok body_term =>
                                                            Result.ok (MatchCase.mc (Identifier.id ctor_name) (identifiers_of binder_names) body_term Option.none),
                                                    },
                                            },
                                    },
                                List.empty => Result.err "MatchArm: missing body",
                            },
                        List.empty => Result.err "MatchArm: missing binders",
                    },
                List.empty => Result.err "MatchArm: missing ctor_name",
            },
        _ => Result.err "reify_match_arm: expected a MatchArm value (v_con)",
    }

#[partial]
def identifiers_of (names : List String) : List Identifier :=
    match names {
        List.empty => List.empty,
        List.cons hd rest => List.cons (Identifier.id hd) (identifiers_of rest),
    }

// ─── Reifying a generated `Decl`'s own Param/type/body shape ───────────

/// `init/meta.mo`'s `Param` (single-ctor `meta_param name typ`, tag 0)
/// -> the reified name plus its reified type `Term`.
def reify_meta_param (v : Value) : Result String (Pair String Term) :=
    match v {
        Value.v_con _tag args =>
            match args {
                List.cons name_val rest =>
                    match rest {
                        List.cons typ_val _ =>
                            match value_as_str name_val {
                                Option.none => Result.err "Param: expected a String name",
                                Option.some name =>
                                    match reify_expr_value List.empty typ_val {
                                        Result.err e => Result.err e,
                                        Result.ok typ_term => Result.ok (Pair.pair name typ_term),
                                    },
                            },
                        List.empty => Result.err "Param: missing typ",
                    },
                List.empty => Result.err "Param: missing name",
            },
        _ => Result.err "reify_meta_param: expected a Param value (v_con)",
    }

#[partial]
def reify_meta_params (vs : List Value) : Result String (List (Pair String Term)) :=
    match vs {
        List.empty => Result.ok List.empty,
        List.cons hd rest =>
            match reify_meta_param hd {
                Result.err e => Result.err e,
                Result.ok p =>
                    match reify_meta_params rest {
                        Result.err e => Result.err e,
                        Result.ok ps => Result.ok (List.cons p ps),
                    },
            },
    }

def pair_names (ps : List (Pair String Term)) : List String :=
    match ps {
        List.empty => List.empty,
        List.cons p rest => match p { Pair.pair n _ => List.cons n (pair_names rest) },
    }

/// `Term.pi p1_typ (Term.pi p2_typ (... ret))` -- mirrors
/// `lang/parser.mo`'s own `build_param_pi_chain` exactly (non-dependent:
/// no param's type ever references an earlier one).
#[partial]
def build_pi_chain (ps : List (Pair String Term)) (ret : Term) : Term :=
    match ps {
        List.empty => ret,
        List.cons p rest =>
            match p { Pair.pair _ typ => Term.pi typ (build_pi_chain rest ret) },
    }

/// `Term.lam p1 (Term.lam p2 (... body))` -- mirrors
/// `lang/parser.mo`'s own `lam_params` exactly.
#[partial]
def build_lam_chain (ps : List (Pair String Term)) (body : Term) : Term :=
    match ps {
        List.empty => body,
        List.cons p rest =>
            match p { Pair.pair name typ => Term.lam (DebugName.named (Identifier.id name)) typ (build_lam_chain rest body) },
    }

def no_constraints : List TypeConstraint := List.empty
def no_attrs : List Attribute := List.empty

/// `Decl.d_def name params ret_typ body` (tag 0) -> a real `Def`. Body
/// is reified with `params`'s own names already pushed onto `locals`
/// (last-declared param innermost, per this file's own convention) so
/// the body may reference them by name.
def reify_d_def (args : List Value) : Result String Def :=
    match args {
        List.cons name_val rest1 =>
            match rest1 {
                List.cons params_val rest2 =>
                    match rest2 {
                        List.cons ret_typ_val rest3 =>
                            match rest3 {
                                List.cons body_val _ =>
                                    match value_as_str name_val {
                                        Option.none => Result.err "d_def: expected a String name",
                                        Option.some name =>
                                            match value_list_to_values params_val {
                                                Result.err e => Result.err e,
                                                Result.ok param_vals =>
                                                    match reify_meta_params param_vals {
                                                        Result.err e => Result.err e,
                                                        Result.ok params =>
                                                            match reify_expr_value List.empty ret_typ_val {
                                                                Result.err e => Result.err e,
                                                                Result.ok ret_term =>
                                                                    match reify_expr_value (push_locals (pair_names params) List.empty) body_val {
                                                                        Result.err e => Result.err e,
                                                                        Result.ok body_term =>
                                                                            Result.ok (Def.mk
                                                                                (ModulePath.mp (List.cons (Identifier.id name) List.empty))
                                                                                (build_pi_chain params ret_term)
                                                                                (build_lam_chain params body_term)
                                                                                no_constraints no_attrs Visibility.package_private),
                                                                    },
                                                            },
                                                    },
                                            },
                                    },
                                List.empty => Result.err "d_def: missing body",
                            },
                        List.empty => Result.err "d_def: missing ret_typ",
                    },
                List.empty => Result.err "d_def: missing params",
            },
        List.empty => Result.err "d_def: missing name",
    }

/// `Decl.d_instance class_name target_typ methods` (tag 1) -> a real
/// `Instance`. `name` uses the same `Identifier.id "_"` placeholder
/// `lang/parser.mo`'s own `instance_close` always uses (never load-
/// bearing content, confirmed directly).
def reify_d_instance (args : List Value) : Result String Decl :=
    match args {
        List.cons class_name_val rest1 =>
            match rest1 {
                List.cons target_typ_val rest2 =>
                    match rest2 {
                        List.cons methods_val _ =>
                            match value_as_str class_name_val {
                                Option.none => Result.err "d_instance: expected a String class_name",
                                Option.some class_name =>
                                    match reify_expr_value List.empty target_typ_val {
                                        Result.err e => Result.err e,
                                        Result.ok target_term =>
                                            match value_list_to_values methods_val {
                                                Result.err e => Result.err e,
                                                Result.ok method_vals =>
                                                    match reify_defs method_vals {
                                                        Result.err e => Result.err e,
                                                        Result.ok defs =>
                                                            Result.ok (Decl.instance_d (Instance.mk
                                                                (Identifier.id "_")
                                                                (ModulePath.mp (List.cons (Identifier.id class_name) List.empty))
                                                                no_constraints
                                                                (List.cons target_term List.empty)
                                                                Visibility.package_private
                                                                List.empty
                                                                defs)),
                                                    },
                                            },
                                    },
                            },
                        List.empty => Result.err "d_instance: missing methods",
                    },
                List.empty => Result.err "d_instance: missing target_typ",
            },
        List.empty => Result.err "d_instance: missing class_name",
    }

/// A meta `Decl` value that isn't `d_error` reifies into ordinary
/// `def`s at the TOP level (`d_def`) or into an instance's own METHODS
/// (`reify_defs` below, `Instance.defs : List Def`) -- both cases need
/// the bare `Def`, not a wrapping `Decl.def_d`, hence this separate
/// entry point from `reify_decl_value`.
def reify_meta_decl_as_def (v : Value) : Result String Def :=
    match v {
        Value.v_con tag args =>
            if I64.beq tag 0 then reify_d_def args
            else if I64.beq tag 2 then reify_d_error args
            else Result.err "reify_meta_decl_as_def: expected d_def (d_instance cannot nest inside another instance's methods)",
        _ => Result.err "reify_meta_decl_as_def: expected a Decl value (v_con)",
    }

/// `d_error` never actually returns a `Def` -- always short-circuits
/// into `Result.err`, at whichever level it's found (top-level list or
/// nested inside an instance's methods), matching `init/meta.mo`'s own
/// doc comment on `d_error`.
def reify_d_error (args : List Value) : Result String Def :=
    match args {
        List.cons msg_val _ =>
            match value_as_str msg_val {
                Option.some msg => Result.err msg,
                Option.none => Result.err "d_error: expected a String message",
            },
        List.empty => Result.err "d_error: missing message",
    }

#[partial]
def reify_defs (vs : List Value) : Result String (List Def) :=
    match vs {
        List.empty => Result.ok List.empty,
        List.cons hd rest =>
            match reify_meta_decl_as_def hd {
                Result.err e => Result.err e,
                Result.ok d =>
                    match reify_defs rest {
                        Result.err e => Result.err e,
                        Result.ok ds => Result.ok (List.cons d ds),
                    },
            },
    }

/// One top-level `Decl` Value (`init/meta.mo`'s `Decl`, tag 0=d_def
/// 1=d_instance 2=d_error) -> a real `lang.types.Decl`.
def reify_decl_value (v : Value) : Result String Decl :=
    match v {
        Value.v_con tag args =>
            if I64.beq tag 0 then
                match reify_d_def args {
                    Result.err e => Result.err e,
                    Result.ok d => Result.ok (Decl.def_d d),
                }
            else if I64.beq tag 1 then reify_d_instance args
            else if I64.beq tag 2 then
                match reify_d_error args {
                    Result.err e => Result.err e,
                    Result.ok _ => Result.err "unreachable: d_error always errs",
                }
            else Result.err "reify_decl_value: unrecognized Decl constructor tag",
        _ => Result.err "reify_decl_value: expected a Decl value (v_con)",
    }

#[partial]
def reify_decls_go (vs : List Value) : Result String (List Decl) :=
    match vs {
        List.empty => Result.ok List.empty,
        List.cons hd rest =>
            match reify_decl_value hd {
                Result.err e => Result.err e,
                Result.ok d =>
                    match reify_decls_go rest {
                        Result.err e => Result.err e,
                        Result.ok ds => Result.ok (List.cons d ds),
                    },
            },
    }

/// The one real OUTPUT-side entry point: a `Value` shaped as `List
/// Decl` (`init/meta.mo`'s `Decl`) -- the reified result of calling a
/// meta-def -- -> real `lang.types.Decl`s ready to splice into the
/// program. A `d_error` anywhere short-circuits the whole call, per
/// `init/meta.mo`'s own doc comment.
def reify_decls_value_to_decls (v : Value) : Result String (List Decl) :=
    match value_list_to_values v {
        Result.err e => Result.err e,
        Result.ok vs => reify_decls_go vs,
    }

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Inductive`/`Value` fixtures -- same convention as the
// rest of this effort's `lang/typecheck/*.mo` tests, no pipeline
// wiring. Structural `Value`/`Term` equality helpers are pure-data-only
// (no `v_closure` case ever appears in these test values).

def field_param (name : String) (typ_name : String) : Param :=
    Param.mk (Identifier.id name) (Term.var sentinel (DebugName.named (Identifier.id typ_name))) Multiplicity.many Option.none List.empty

def point_ctor : InductConstructor :=
    InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "mk") List.empty))
        (List.cons (field_param "x" "I64") (List.cons (field_param "y" "I64") List.empty)) Term.hole

def point_ind : Inductive :=
    Inductive.mk (ModulePath.mp (List.cons (Identifier.id "Point") List.empty)) List.empty Term.hole
        (List.cons point_ctor List.empty) List.empty Visibility.package_private

#[partial]
def values_eq (a : List Value) (b : List Value) : Bool :=
    match a {
        List.empty => match b { List.empty => true, List.cons _ _ => false },
        List.cons ha ta => match b { List.empty => false, List.cons hb tb => value_eq ha hb && values_eq ta tb },
    }

#[partial]
def value_eq (a : Value) (b : Value) : Bool :=
    match a {
        Value.v_lit la => match b { Value.v_lit lb => irlit_eq la lb, _ => false },
        Value.v_con ta aa => match b { Value.v_con tb ba => I64.beq ta tb && values_eq aa ba, _ => false },
        Value.v_closure _ _ => false,
        Value.v_partial_ntv _ _ => false,
    }

def irlit_eq (a : IrLit) (b : IrLit) : Bool :=
    match a {
        IrLit.ir_str sa => match b { IrLit.ir_str sb => String.beq sa sb, _ => false },
        IrLit.ir_num na _ => match b { IrLit.ir_num nb _ => I64.beq na nb, _ => false },
        IrLit.ir_char _ => false,
        IrLit.ir_float _ _ => false,
        IrLit.ir_sort la => match b { IrLit.ir_sort lb => I64.beq la lb, _ => false },
    }

def expected_point_type_info : Value :=
    type_info_val (str_val "Point") (list_value (List.cons
        (ctor_info_val (str_val "mk") (list_value (List.cons
            (field_info_val (str_val "x") (e_var_val "I64") (list_value List.empty))
            (List.cons (field_info_val (str_val "y") (e_var_val "I64") (list_value List.empty)) List.empty))))
        List.empty))

#[test]
def test_build_type_info_value_two_field_struct : Bool :=
    match build_type_info_value point_ind {
        Result.err _ => false,
        Result.ok v => value_eq v expected_point_type_info,
    }

#[test]
def test_term_to_expr_value_qualified_var_and_app : Bool :=
    let lens_typ : Term :=
        Term.app (Term.app (Term.var sentinel (DebugName.named (Identifier.id "Lens"))) (Term.var sentinel (DebugName.named (Identifier.id "Point")))) (Term.var sentinel (DebugName.named (Identifier.id "I64"))) in
    match term_to_expr_value lens_typ {
        Result.err _ => false,
        Result.ok v => value_eq v (e_app_val (e_app_val (e_var_val "Lens") (e_var_val "Point")) (e_var_val "I64")),
    }

// ─── e_lam / e_match binder-index convention (the highest-risk logic) ──

def e_lam_val (name : String) (typ : Value) (body : Value) : Value :=
    Value.v_con 5 (List.cons (str_val name) (List.cons typ (List.cons body List.empty)))

def e_match_val (scrutinee : Value) (arms : List Value) : Value :=
    Value.v_con 7 (List.cons scrutinee (List.cons (list_value arms) List.empty))

def match_arm_val (ctor_name : String) (binders : List String) (body : Value) : Value :=
    Value.v_con 0 (List.cons (str_val ctor_name) (List.cons (list_value (str_vals binders)) (List.cons body List.empty)))

#[partial]
def str_vals (ss : List String) : List Value :=
    match ss { List.empty => List.empty, List.cons hd rest => List.cons (str_val hd) (str_vals rest) }

def e_ctor_val (ctor_name : String) (args : List Value) : Value :=
    Value.v_con 8 (List.cons (str_val ctor_name) (List.cons (list_value args) List.empty))

/// The exact shape `std/derive.mo`'s `lens_getter` builds for
/// `Point.x`: `fn s => match s { mk x y => x }`. Binders declared
/// `["x", "y"]` -- per this file's own convention, "y" (last-declared)
/// must end up index 0, "x" index 1.
def getter_shape_val : Value :=
    e_lam_val "s" (e_var_val "Point")
        (e_match_val (e_var_val "s") (List.cons (match_arm_val "mk" (List.cons "x" (List.cons "y" List.empty)) (e_var_val "x")) List.empty))

#[test]
def test_reify_e_lam_and_match_arm_first_binder_index : Bool :=
    match reify_expr_value List.empty getter_shape_val {
        Result.err _ => false,
        Result.ok t =>
            match t {
                Term.lam _ _ body =>
                    match body {
                        Term.lit lit_ =>
                            match lit_ {
                                Literal.match_ _ cases =>
                                    match cases {
                                        List.cons case_ _ =>
                                            match case_ {
                                                MatchCase.mc _ _ case_body _ =>
                                                    match case_body {
                                                        Term.var idx _ => I64.beq idx 1, // "x", first-declared
                                                        _ => false,
                                                    },
                                            },
                                        List.empty => false,
                                    },
                                _ => false,
                            },
                        _ => false,
                    },
                _ => false,
            },
    }

/// The exact shape `lens_setter` builds for `Point.x`:
/// `fn v => fn s => match s { mk x y => Point.mk v y }`. Deepest test of
/// the index convention: by the time the innermost `e_ctor` args are
/// reified, locals = ["y","x","s","v"] (innermost first) -- "v" (the
/// OUTERMOST lambda, bound first) ends up index 3, "y" (the LAST match
/// binder) ends up index 0.
def setter_shape_val : Value :=
    e_lam_val "v" (e_var_val "I64")
        (e_lam_val "s" (e_var_val "Point")
            (e_match_val (e_var_val "s")
                (List.cons (match_arm_val "mk" (List.cons "x" (List.cons "y" List.empty))
                    (e_ctor_val "Point.mk" (List.cons (e_var_val "v") (List.cons (e_var_val "y") List.empty))))
                List.empty)))

#[test]
def test_reify_e_ctor_args_reference_correct_outer_and_field_indices : Bool :=
    match reify_expr_value List.empty setter_shape_val {
        Result.err _ => false,
        Result.ok t =>
            match t {
                Term.lam _ _ inner1 =>
                    match inner1 {
                        Term.lam _ _ body =>
                            match body {
                                Term.lit lit_ =>
                                    match lit_ {
                                        Literal.match_ _ cases =>
                                            match cases {
                                                List.cons case_ _ =>
                                                    match case_ {
                                                        MatchCase.mc _ _ case_body _ =>
                                                            match case_body {
                                                                // Point.mk v y -- App(App(Var "Point.mk"), Var v), Var y
                                                                Term.app applied_v_term y_term =>
                                                                    match applied_v_term {
                                                                        Term.app _ v_term =>
                                                                            match v_term {
                                                                                Term.var v_idx _ =>
                                                                                    match y_term {
                                                                                        Term.var y_idx _ => I64.beq v_idx 3 && I64.beq y_idx 0,
                                                                                        _ => false,
                                                                                    },
                                                                                _ => false,
                                                                            },
                                                                        _ => false,
                                                                    },
                                                                _ => false,
                                                            },
                                                    },
                                                List.empty => false,
                                            },
                                        _ => false,
                                    },
                                _ => false,
                            },
                        _ => false,
                    },
                _ => false,
            },
    }

// ─── d_def / d_instance reification, and d_error short-circuiting ──────

def d_def_val (name : String) (params : List Value) (ret_typ : Value) (body : Value) : Value :=
    Value.v_con 0 (List.cons (str_val name) (List.cons (list_value params) (List.cons ret_typ (List.cons body List.empty))))

def meta_param_val (name : String) (typ : Value) : Value :=
    Value.v_con 0 (List.cons (str_val name) (List.cons typ List.empty))

def d_error_val (msg : String) : Value := Value.v_con 2 (List.cons (str_val msg) List.empty)

/// `d_def "Point.x" [] (Lens Point I64) <getter/setter shape>` --
/// zero params (mirrors `lens_field_decl`'s real shape exactly: the
/// getter/setter closures are already fully self-contained `Expr`
/// values, not further wrapped by an outer `d_def`-level param list).
def point_x_def_val : Value :=
    d_def_val "Point.x" List.empty
        (e_app_val (e_app_val (e_var_val "Lens") (e_var_val "Point")) (e_var_val "I64"))
        (e_app_val (e_app_val (e_var_val "lens") getter_shape_val) setter_shape_val)

#[test]
def test_reify_decl_value_d_def_zero_params : Bool :=
    match reify_decl_value point_x_def_val {
        Result.err _ => false,
        Result.ok d =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk name _typ _term _c _a _v =>
                            match name { ModulePath.mp ids => match ids { List.cons id _ => id_is id "Point.x", List.empty => false } },
                    },
                _ => false,
            },
    }

def id_is (id : Identifier) (expected : String) : Bool :=
    match id { Identifier.id s => String.beq s expected }

/// `d_def "beq" [meta_param "a" ..., meta_param "b" ...] Bool <body>` --
/// two OUTER-level params this time (mirrors `derive_beq_meta`'s own
/// `beq` method shape). Per this file's own convention, "b"
/// (last-declared) must end up index 0 for a reference inside `body`.
def beq_method_val : Value :=
    d_def_val "beq"
        (List.cons (meta_param_val "a" (e_var_val "Point")) (List.cons (meta_param_val "b" (e_var_val "Point")) List.empty))
        (e_var_val "Bool")
        (e_var_val "b")

#[test]
def test_reify_d_def_outer_params_last_is_index_zero : Bool :=
    match reify_decl_value beq_method_val {
        Result.err _ => false,
        Result.ok d =>
            match d {
                Decl.def_d def_ =>
                    match def_ {
                        Def.mk _name _typ term _c _a _v =>
                            match term {
                                // fn a => fn b => b
                                Term.lam _ _ inner =>
                                    match inner {
                                        Term.lam _ _ body =>
                                            match body { Term.var idx _ => I64.beq idx 0, _ => false },
                                        _ => false,
                                    },
                                _ => false,
                            },
                    },
                _ => false,
            },
    }

def d_instance_val (class_name : String) (target_typ : Value) (methods : List Value) : Value :=
    Value.v_con 1 (List.cons (str_val class_name) (List.cons target_typ (List.cons (list_value methods) List.empty)))

#[test]
def test_reify_decl_value_d_instance_wraps_methods : Bool :=
    match reify_decl_value (d_instance_val "Debug" (e_var_val "Point") (List.cons beq_method_val List.empty)) {
        Result.err _ => false,
        Result.ok d =>
            match d {
                Decl.instance_d ins =>
                    match ins {
                        Instance.mk _name cls _c _args _vis _ip defs =>
                            (match cls { ModulePath.mp ids => match ids { List.cons id _ => id_is id "Debug", List.empty => false } })
                            && match defs { List.cons _ rest => (match rest { List.empty => true, List.cons _ _ => false }), List.empty => false },
                    },
                _ => false,
            },
    }

#[test]
def test_reify_decls_value_to_decls_propagates_d_error : Bool :=
    let decls_val : Value := list_value (List.cons point_x_def_val (List.cons (d_error_val "boom") List.empty)) in
    match reify_decls_value_to_decls decls_val {
        Result.err msg => String.beq msg "boom",
        Result.ok _ => false,
    }

#[test]
def test_reify_decls_value_to_decls_two_defs : Bool :=
    let decls_val : Value := list_value (List.cons point_x_def_val (List.cons point_x_def_val List.empty)) in
    match reify_decls_value_to_decls decls_val {
        Result.err _ => false,
        Result.ok ds => match ds { List.cons _ rest => (match rest { List.cons _ r2 => (match r2 { List.empty => true, List.cons _ _ => false }), List.empty => false }), List.empty => false },
    }
