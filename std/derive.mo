/// Derive macros: `derive_lens`, `derive_debug`, `derive_beq`,
/// `derive_bord` — written using Monad's own macro system.
///
/// All four are ported to the reflection-as-data kernel (`init/meta.mo`'s
/// `TypeInfo`/`Expr`/`Decl` values + `core/src/eval/meta_compile.rs`'s
/// `MetaEvalContext`, invoked via the `reflect_type_info!` intrinsic) —
/// see `plans/review-and-reduce-the-greedy-nest.md`: each `derive_*`
/// stays an ordinary `defmacro`/decl-gen wrapper (so `derive_*!`/
/// `#[derive ...]` dispatch is completely unchanged), but its BODY is now
/// just `reflect_type_info! T derive_*_meta`, splicing in the result of
/// CALLING an ordinary `TypeInfo -> List Decl` function, evaluated for
/// real (arbitrary Monad computation — `List.map`/`match`/recursion), not
/// template-substituted — rather than composing built-in per-constructor/
/// per-field dispatch intrinsics. The OLDER 5-intrinsic kernel these
/// replaced (`reflect_ctors!`/`reflect_ctor_fields!`/
/// `reflect_pairwise_ctors!`/`reflect_fields!`/`reflect_set_field!`) has
/// since been deleted outright — see `core/src/eval/macro_expand.rs`'s
/// `BUILTIN_INTRINSICS` doc comment for the current (`reflect_type_info!`-
/// only) design.
use init.meta {TypeInfo, CtorInfo, FieldInfo, Expr, MatchArm, Decl}

open TypeInfo {type_info}
open CtorInfo {ctor_info}
open FieldInfo {field_info}
open Expr {e_var, e_str, e_bool, e_app, e_lam, e_if, e_match, e_ctor}
open MatchArm {match_arm}
open Param {meta_param}
open Decl {d_def, d_instance}

def field_name_of (field : FieldInfo) : String :=
    match field { field_info name typ attrs => name }

/// The getter half of a field's lens: `fn (s : T) => match s { ctor
/// field1 field2 ... => <target field> }` — the (required single)
/// constructor's fields are all bound by their own declared name, and
/// the arm just returns the one this lens is for.
def lens_getter (type_name : String) (ctor_name : String) (field_names : List String) (target : String) : Expr :=
    e_lam "s" (e_var type_name)
        (e_match (e_var "s") [match_arm ctor_name field_names (e_var target)])

/// The setter half: `fn (v : field_typ) => fn (s : T) => match s { ctor
/// field1 field2 ... => ctor field1 ... v ... fieldN }` — rebuilds the
/// constructor application with exactly the target field replaced by the
/// new value `v`, every other field passed through unchanged. `e_ctor`
/// needs the constructor's QUALIFIED name (`<Type>.<ctor>`, e.g.
/// `"Point.mk"`) to reify to a real value-constructing reference — unlike
/// a match arm's pattern, which uses the bare constructor name.
def lens_setter (type_name : String) (ctor_name : String) (field_names : List String) (field_typ : Expr) (target : String) : Expr :=
    e_lam "v" field_typ
        (e_lam "s" (e_var type_name)
            (e_match (e_var "s")
                [match_arm ctor_name field_names
                    (e_ctor (String.concat type_name (String.concat "." ctor_name))
                            (List.map (rebuild_field target) field_names))]))

def rebuild_field (target : String) (field_name : String) : Expr :=
    if field_name == target then e_var "v" else e_var field_name

/// One field -> its `Lens`-typed `def`, named `<Type>.<field>`.
def lens_field_decl (type_name : String) (ctor_name : String) (field_names : List String) (field : FieldInfo) : Decl :=
    match field {
        field_info fname ftyp fattrs =>
            d_def
                (String.concat type_name (String.concat "." fname))
                List.empty
                (e_app (e_app (e_var "Lens") (e_var type_name)) ftyp)
                (e_app (e_app (e_var "lens") (lens_getter type_name ctor_name field_names fname))
                       (lens_setter type_name ctor_name field_names ftyp fname))
    }

/// `derive_lens_meta`'s work for one already-known-single constructor:
/// one `Decl` per field.
def lens_decls_for_ctor (type_name : String) (ctor : CtorInfo) : List Decl :=
    match ctor {
        ctor_info ctor_name fields =>
            let field_names := List.map field_name_of fields in
            List.map (lens_field_decl type_name ctor_name field_names) fields
    }

/// `derive_lens! Point` (or `#[derive Lens] struct Point {...}`) generates
/// `Point.x : Lens Point I64`/`Point.y : Lens Point I64` — one field lens
/// per field. `T` must have exactly one constructor (a struct, or a
/// single-constructor `type`) — a lens focuses on exactly one field of
/// exactly one shape; a multi-constructor type generates nothing (silent,
/// matching this port's scope — see `init.optics`'s `Prism` for sum-type
/// variant access instead).
pub def derive_lens_meta (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            match ctors {
                cons c tail =>
                    match tail {
                        empty => lens_decls_for_ctor type_name c,
                        cons _ _ => List.empty,
                    },
                empty => List.empty,
            }
    }

defmacro derive_lens T := decls {
    reflect_type_info! T derive_lens_meta
}

/// One field's `"name: repr"` piece of a `Debug.debug` output, as an
/// `Expr` — `Debug.debug` is applied to the field's OWN runtime value (the
/// field is bound, by its declared name, inside the enclosing match arm),
/// not called here; only the code that will call it is built.
def debug_piece (field_name : String) : Expr :=
    e_app (e_app (e_var "String.concat") (e_str (String.concat field_name ": ")))
          (e_app (e_var "Debug.debug") (e_var field_name))

/// Right-folds a list of `Expr`s into one `String.concat`-chained `Expr`,
/// each pair separated by the literal string `sep` — e.g. `[a, b, c]`
/// becomes the code for `a ++ sep ++ b ++ sep ++ c`. Field count/order is
/// already known at meta-expansion time (unlike a field's own runtime
/// value), so this fold runs directly in `derive_debug_meta`, not as
/// generated runtime code the way the old `reflect_ctor_fields!`-based
/// accumulator had to.
def join_with_sep (sep : String) (pieces : List Expr) : Expr :=
    match pieces {
        empty => e_str "",
        cons p tail =>
            match tail {
                empty => p,
                cons _ _ =>
                    e_app (e_app (e_var "String.concat") p)
                          (e_app (e_app (e_var "String.concat") (e_str sep)) (join_with_sep sep tail)),
            }
    }

/// A constructor's label: just the type name for a single-constructor
/// type (a struct), or `TypeName::CtorName` for one variant of a
/// multi-constructor type — decided once, here, from the already-known
/// `is_single` flag, not by generated runtime code.
def debug_label (type_name : String) (ctor_name : String) (is_single : Bool) : String :=
    if is_single then type_name else String.concat type_name (String.concat "::" ctor_name)

/// This constructor's whole `Debug.debug` output, as an `Expr`: the bare
/// label for a zero-field constructor (field count is known here, at
/// meta-expansion time, so this needs no runtime `if fields == ""` check
/// the way the old accumulator-based approach did), or
/// `"Label { f1: r1, ..., fN: rN }"` for one with fields.
def debug_arm_body (type_name : String) (ctor_name : String) (is_single : Bool) (field_names : List String) : Expr :=
    let label := debug_label type_name ctor_name is_single in
    match field_names {
        empty => e_str label,
        cons _ _ =>
            let fields_expr := join_with_sep ", " (List.map debug_piece field_names) in
            e_app (e_app (e_var "String.concat") (e_str (String.concat label " { ")))
                  (e_app (e_app (e_var "String.concat") fields_expr) (e_str " }")),
    }

/// One constructor -> its whole `debug` match arm.
def debug_ctor_arm (type_name : String) (is_single : Bool) (ctor : CtorInfo) : MatchArm :=
    match ctor {
        ctor_info ctor_name fields =>
            let field_names := List.map field_name_of fields in
            match_arm ctor_name field_names (debug_arm_body type_name ctor_name is_single field_names)
    }

/// Whether `ctors` has exactly one element — mirrors `derive_lens_meta`'s
/// own single-vs-multi-constructor check.
def is_single_ctor_list (ctors : List CtorInfo) : Bool :=
    match ctors {
        cons _ tail => match tail { empty => true, cons _ _ => false },
        empty => false,
    }

/// `#[derive Debug] struct Point { x : I64, y : I64 }` (or, called
/// directly, `derive_debug! Point`) generates a rust-style structural
/// `Debug Point` instance: `Debug.debug` produces `"Point { x: 1, y: 2 }"`
/// for a struct, or `"TypeName::CtorName { field: repr, ... }"` per
/// variant for a multi-constructor `type`.
///
/// Every field's own type must have a `Debug` instance in scope (`Debug`
/// is applied recursively, field by field) — `std/debug.mo` ships base
/// instances for `String`/`I64`/`Bool`.
pub def derive_debug_meta (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            let is_single := is_single_ctor_list ctors in
            let arms := List.map (debug_ctor_arm type_name is_single) ctors in
            [d_instance "Debug" (e_var type_name)
                [d_def "debug" [meta_param "self" (e_var type_name)] (e_var "String")
                    (e_match (e_var "self") arms)]]
    }

defmacro derive_debug T := decls {
    reflect_type_info! T derive_debug_meta
}

/// Both `derive_beq`/`derive_bord` need the same pairwise shape: match on
/// `a`'s constructor, then (nested) on `b`'s constructor, covering every
/// `(ctor_i, ctor_j)` pair. Unlike the old `reflect_pairwise_ctors!`
/// intrinsic (which took a same-constructor and a different-constructor
/// template and resolved `i`/`j`/`i_lt_j` internally), the constructor
/// list's declaration order is ordinary data here — `map_indexed_ctor_arms`
/// just threads a running `I64` index through an `List.map`-like walk, so
/// each per-pair handler decides its own behaviour from `i`/`j` directly
/// (no separate "diff" callback needed).
def map_indexed_ctor_arms (i_start : I64) (f : I64 -> CtorInfo -> MatchArm) (ctors : List CtorInfo) : List MatchArm :=
    match ctors {
        empty => List.empty,
        cons c tail => List.cons (f i_start c) (map_indexed_ctor_arms (i_start + 1) f tail),
    }

def prefixed (prefix : String) (name : String) : String := String.concat prefix name

/// One field's `BEq.beq a_field b_field` piece, for the (already-known-
/// same) constructor's field-wise `&&`-fold.
def beq_piece (field_name : String) : Expr :=
    e_app (e_app (e_var "BEq.beq") (e_var (prefixed "a_" field_name))) (e_var (prefixed "b_" field_name))

/// Right-folds field-wise `BEq.beq` pieces with `Bool.and` — `true` for a
/// zero-field constructor (nothing to AND against, so trivially equal).
def and_fold (pieces : List Expr) : Expr :=
    match pieces {
        empty => e_bool true,
        cons p tail => match tail { empty => p, cons _ _ => e_app (e_app (e_var "Bool.and") p) (and_fold tail) },
    }

/// The inner (`b`) match arm for one `(ctor_a, ctor_b)` pair of
/// `derive_beq`'s `beq`: same constructor (`i == j`) folds field-wise
/// equality; different constructors are never equal, regardless of
/// declaration order.
def beq_inner_arm (i : I64) (field_names_a : List String) (j : I64) (ctor_b : CtorInfo) : MatchArm :=
    match ctor_b {
        ctor_info ctor_b_name fields_b =>
            let b_binders := List.map (prefixed "b_") (List.map field_name_of fields_b) in
            let body := if i == j then and_fold (List.map beq_piece field_names_a) else e_bool false in
            match_arm ctor_b_name b_binders body
    }

/// The outer (`a`) match arm for one constructor of `derive_beq`'s `beq`:
/// binds `a`'s fields (`a_`-prefixed, to stay distinct from `b`'s own
/// binders when the same constructor is matched on both sides), then
/// matches `b` against every constructor in turn.
def beq_outer_arm (all_ctors : List CtorInfo) (i : I64) (ctor_a : CtorInfo) : MatchArm :=
    match ctor_a {
        ctor_info ctor_a_name fields_a =>
            let field_names_a := List.map field_name_of fields_a in
            let a_binders := List.map (prefixed "a_") field_names_a in
            let inner_arms := map_indexed_ctor_arms 0 (beq_inner_arm i field_names_a) all_ctors in
            match_arm ctor_a_name a_binders (e_match (e_var "b") inner_arms)
    }

/// `#[derive BEq] struct Point { x : I64, y : I64 }` (or, called directly,
/// `derive_beq! Point`) generates a structural `BEq Point` instance:
/// `a == b` iff `a`/`b` were built with the same constructor and every
/// field is pairwise `==`.
///
/// Every field's own type must have a `BEq` instance in scope (`BEq` is
/// applied recursively, field by field) — `init/prelude.mo` and
/// `init/number.mo`/`init/string.mo` ship base instances for the numeric
/// types, `Bool`, `String`, and `Nat`.
pub def derive_beq_meta (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            let arms := map_indexed_ctor_arms 0 (beq_outer_arm ctors) ctors in
            [d_instance "BEq" (e_var type_name)
                [d_def "beq" [meta_param "a" (e_var type_name), meta_param "b" (e_var type_name)] (e_var "Bool")
                    (e_match (e_var "a") arms)]]
    }

defmacro derive_beq T := decls {
    reflect_type_info! T derive_beq_meta
}

def cmp_piece_lt (field_name : String) : Expr :=
    e_app (e_app (e_var "BOrd.lt") (e_var (prefixed "a_" field_name))) (e_var (prefixed "b_" field_name))
def cmp_piece_gt (field_name : String) : Expr :=
    e_app (e_app (e_var "BOrd.gt") (e_var (prefixed "a_" field_name))) (e_var (prefixed "b_" field_name))

/// Field-wise "first deciding field wins" priority chain for `lt`: the
/// first field where `a`/`b` disagree decides the whole comparison, later
/// fields only run if every earlier one was equal, and running out of
/// fields (or being called on a zero-field constructor) means `a`/`b` are
/// equal — neither `lt` nor `gt`. Field count/order is known here, at
/// meta-expansion time, so (unlike the old `reflect_ctor_fields!`-based
/// `cmp_combine` accumulator, which had to fold a 3-valued `""`/`"lt"`/
/// `"gt"` string through generated runtime code specifically because it
/// couldn't see field count up front) this is just an ordinary recursive
/// walk building nested `if`s directly — see
/// `test_derive_bord_left_fold_uses_first_deciding_field` in
/// `core/src/eval/macro_test.rs` for the regression this guards against.
def lt_chain (field_names : List String) : Expr :=
    match field_names {
        empty => e_bool false,
        cons f tail => e_if (cmp_piece_lt f) (e_bool true) (e_if (cmp_piece_gt f) (e_bool false) (lt_chain tail)),
    }

/// `gt`'s mirror of `lt_chain` — same field-priority walk, `lt`/`gt` roles
/// swapped at each field.
def gt_chain (field_names : List String) : Expr :=
    match field_names {
        empty => e_bool false,
        cons f tail => e_if (cmp_piece_gt f) (e_bool true) (e_if (cmp_piece_lt f) (e_bool false) (gt_chain tail)),
    }

/// The inner (`b`) match arm for one `(ctor_a, ctor_b)` pair of one of
/// `derive_bord`'s `lt`/`gt` methods: `chain_fn` runs the field-priority
/// walk when `i == j`; otherwise declaration order alone decides —
/// `diff_lt_is_true` is `true` for `lt` (an earlier-declared constructor
/// sorts lower) and `false` for `gt` (its mirror).
def bord_inner_arm (chain_fn : List String -> Expr) (diff_lt_is_true : Bool) (i : I64) (field_names_a : List String) (j : I64) (ctor_b : CtorInfo) : MatchArm :=
    match ctor_b {
        ctor_info ctor_b_name fields_b =>
            let b_binders := List.map (prefixed "b_") (List.map field_name_of fields_b) in
            let body :=
                if i == j
                    then chain_fn field_names_a
                    else if i < j then e_bool diff_lt_is_true else e_bool (Bool.not diff_lt_is_true) in
            match_arm ctor_b_name b_binders body
    }

/// The outer (`a`) match arm for one constructor of one of `derive_bord`'s
/// `lt`/`gt` methods — same binding shape as `beq_outer_arm`.
def bord_outer_arm (chain_fn : List String -> Expr) (diff_lt_is_true : Bool) (all_ctors : List CtorInfo) (i : I64) (ctor_a : CtorInfo) : MatchArm :=
    match ctor_a {
        ctor_info ctor_a_name fields_a =>
            let field_names_a := List.map field_name_of fields_a in
            let a_binders := List.map (prefixed "a_") field_names_a in
            let inner_arms := map_indexed_ctor_arms 0 (bord_inner_arm chain_fn diff_lt_is_true i field_names_a) all_ctors in
            match_arm ctor_a_name a_binders (e_match (e_var "b") inner_arms)
    }

/// One of `derive_bord`'s two methods (`lt`/`gt`), built from its own
/// field-priority chain function and declaration-order tiebreak sense.
def bord_method (name : String) (chain_fn : List String -> Expr) (diff_lt_is_true : Bool) (type_name : String) (ctors : List CtorInfo) : Decl :=
    let arms := map_indexed_ctor_arms 0 (bord_outer_arm chain_fn diff_lt_is_true ctors) ctors in
    d_def name [meta_param "a" (e_var type_name), meta_param "b" (e_var type_name)] (e_var "Bool")
        (e_match (e_var "a") arms)

/// `#[derive BOrd] struct Point { x : I64, y : I64 }` (or, called
/// directly, `derive_bord! Point`) generates a structural `BOrd Point`
/// instance: constructors ordered by declaration position (first sorts
/// lowest), fields within the same constructor compared lexicographically
/// in declared order.
///
/// Every field's own type must have a `BOrd` instance in scope, same
/// requirement as `derive_beq`'s `BEq` above.
pub def derive_bord_meta (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            [d_instance "BOrd" (e_var type_name)
                [bord_method "lt" lt_chain true type_name ctors,
                 bord_method "gt" gt_chain false type_name ctors]]
    }

defmacro derive_bord T := decls {
    reflect_type_info! T derive_bord_meta
}
