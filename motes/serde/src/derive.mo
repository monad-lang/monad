/// The format-agnostic generation half of serde: walks a `TypeInfo` the
/// same way `std/src/derive.mo`'s `derive_lens_meta` does, but dispatches
/// on each field's TYPE (mirroring `motes/clap/src/args.mo`'s
/// `derive_cli_meta`) to build a `serialize`/`deserialize` function
/// against `format.mo`'s `Serializer`/`Deserializer` classes for one
/// NAMED, CONCRETE format -- `format_typ_name` is supplied by the format
/// backend's own thin wrapper meta-function (e.g. `motes/json`'s
/// `derive_json_serialize_meta`), since `reflect_type_info!` requires its
/// own meta-def argument to be a bare top-level name, not a partially
/// applied expression (`lang/src/module.mo`'s own
/// `"reflect_type_info!: meta-def argument must be a plain name"`).
use init::meta {TypeInfo, CtorInfo, FieldInfo, Expr, MatchArm, Param, Decl}

open TypeInfo {type_info}
open CtorInfo {ctor_info}
open FieldInfo {field_info}
open Expr {e_var, e_str, e_app, e_lam, e_if, e_match, e_ctor}
open MatchArm {match_arm}
open Param {meta_param}
open Decl {d_def, d_error}

/// `List Expr` as an `Expr` -- `Expr` has no list-literal node, so a list
/// value is built the same way any other value is: nested constructor
/// applications. `e_ctor` needs QUALIFIED constructor names (unlike a
/// match arm's bare pattern name -- `std/src/derive.mo`'s `lens_setter`
/// documents the same asymmetry for `e_ctor` generally).
#[partial]
def e_list_lit (items : List Expr) : Expr :=
    match items {
        List.empty => e_ctor "List.empty" List.empty,
        List.cons hd tl => e_ctor "List.cons" (List.cons hd (List.cons (e_list_lit tl) List.empty)),
    }

def e_pair_lit (a : Expr) (b : Expr) : Expr :=
    e_ctor "Pair.pair" (List.cons a (List.cons b List.empty))

/// The bare type name a field's `Expr` names, when it's a direct `e_var`
/// (a primitive or a nested struct reference) -- `Option X`/`List X` are
/// `e_app`, handled by their own cases in the callers below, never reach
/// here for their own head.
def expr_head_name (e : Expr) : Option String :=
    match e {
        Expr.e_var name => Option.some name,
        _ => Option.none,
    }

/// `e_app`'s own function position, when it's a direct `e_var` -- one
/// match level, read apart from `expr_head_name` so a two-level pattern
/// (`e_app (e_var ...) ...`) is never needed: patterns here stay exactly
/// one constructor deep.
def app_head_name (e : Expr) : Option String :=
    match e {
        Expr.e_app f _ => expr_head_name f,
        _ => Option.none,
    }

def app_arg (e : Expr) : Option Expr :=
    match e {
        Expr.e_app _ a => Option.some a,
        _ => Option.none,
    }

def is_head_named (e : Expr) (name : String) : Bool :=
    match app_head_name e {
        Option.some n => String.beq n name,
        Option.none => false,
    }

/// Does this field's type `Expr` have the shape `Option X`, and if so,
/// what is `X`? `Option`-typed fields get special treatment in both
/// directions (serialize: a present `Option` field always serializes,
/// `none` included, as `ser_null`; deserialize: a missing key decodes to
/// `none`, not an error).
def option_inner (e : Expr) : Option Expr :=
    if is_head_named e "Option" then app_arg e else Option.none

def list_inner (e : Expr) : Option Expr :=
    if is_head_named e "List" then app_arg e else Option.none

def field_name_of (f : FieldInfo) : String :=
    match f { field_info name typ attrs default => name }

def field_typ_of (f : FieldInfo) : Expr :=
    match f { field_info name typ attrs default => typ }

def field_default_of (f : FieldInfo) : Option Expr :=
    match f { field_info name typ attrs default => default }

// ─── Serialize direction ────────────────────────────────────────────────

/// The format's own wrapper-function name for one `Serializer` method --
/// `<format_tag>_ser_<suffix>`, e.g. `"json_ser_int"`. NEVER the class
/// method name itself (`Serializer.ser_int`): a macro-REIFIED bare
/// top-level `d_def` calling a class method that way fails at run time
/// with `unresolved global`, even though the identical call, normally
/// PARSED, dispatches fine (probed directly -- see `format.mo`'s note).
/// Every format backend must provide these wrappers alongside its
/// `instance Serializer`/`Deserializer`.
def fmt_fn (format_tag : String) (suffix : String) : Expr :=
    e_var (String.concat format_tag suffix)

/// The format's own representation type's bare name, when `format_typ`
/// is a plain `e_var` (true for every real format: `Expr.e_var "Json"`,
/// `Expr.e_var "Toy"`) -- `""` otherwise, which simply never matches any
/// real field type name below. Used to recognize a field whose declared
/// type IS the format's own type (e.g. `ToolDef.parameters : Json` when
/// deriving for `Json`) -- such a field is already a value of the target
/// format, so it passes through unchanged rather than being (de)serialized.
def format_typ_name (format_typ : Expr) : String :=
    match expr_head_name format_typ {
        Option.some n => n,
        Option.none => "",
    }

/// The wrapper-function reference for a primitive or nested-struct type
/// name -- binds the name via `match`, compares with `==` in the arm
/// body (never a literal string INSIDE a pattern; `motes/clap/src/
/// args.mo`'s `cli_is_bool_typ` is the precedent this follows: `match t
/// { e_var name => name == "Bool", ... }`).
def primitive_serialize_fn (format_tag : String) (fmt_typ_name : String) (type_name : String) : Expr :=
    if type_name == "String" then fmt_fn format_tag "_ser_string"
    else if type_name == "I64" then fmt_fn format_tag "_ser_int"
    else if type_name == "Bool" then fmt_fn format_tag "_ser_bool"
    else if type_name == fmt_typ_name then e_lam "__serde_id" (e_var type_name) (e_var "__serde_id")
    else e_var (String.concat type_name (String.concat ".serialize_" format_tag))

/// The wrapper/`Type.serialize_<format>` call applied to one already-bound
/// field variable, dispatched on the field's declared type. `#[terminating]`:
/// `inner` (the recursive `Option`-unwrap case) comes from `option_inner`,
/// not direct pattern destructuring, so the checker can't see it's
/// structurally smaller.
#[terminating]
def serialize_field_expr (format_tag : String) (fmt_typ_name : String) (field_typ : Expr) (field_name : String) : Expr :=
    let v := e_var field_name in
    match option_inner field_typ {
        Option.some inner =>
            e_match v (List.cons
                (match_arm "none" List.empty (fmt_fn format_tag "_ser_null"))
                (List.cons (match_arm "some" (List.cons "__serde_inner" List.empty)
                    (serialize_field_expr format_tag fmt_typ_name inner "__serde_inner")) List.empty)),
        Option.none =>
            match list_inner field_typ {
                Option.some elem_typ =>
                    e_app (fmt_fn format_tag "_ser_list")
                        (e_app (e_app (e_var "List.map") (serialize_elem_fn format_tag fmt_typ_name elem_typ)) v),
                Option.none =>
                    match expr_head_name field_typ {
                        Option.some name => e_app (primitive_serialize_fn format_tag fmt_typ_name name) v,
                        Option.none => e_app (fmt_fn format_tag "_ser_string") v,
                    },
            },
    }

/// A bare function VALUE (not applied) serializing one element of a
/// `List X` field, for `List.map`. Primitive cases reference the format's
/// own wrapper function, used unapplied (ordinary first-class reference
/// to a plain function, ordinary everywhere in this codebase -- unlike a
/// class method, which this file never references unapplied either).
def serialize_elem_fn (format_tag : String) (fmt_typ_name : String) (elem_typ : Expr) : Expr :=
    match expr_head_name elem_typ {
        Option.some name => primitive_serialize_fn format_tag fmt_typ_name name,
        Option.none => fmt_fn format_tag "_ser_string",
    }

def serialize_field_pair (format_tag : String) (fmt_typ_name : String) (f : FieldInfo) : Expr :=
    e_pair_lit (e_str (field_name_of f)) (serialize_field_expr format_tag fmt_typ_name (field_typ_of f) (field_name_of f))

/// `def <Type>.serialize_<format> (v : <Type>) : <FormatType> := match v
/// { ctor f1 f2 ... => <format>_ser_object [(f1, ser f1), ...] }` -- the
/// fields are bound by the match, then re-read via `serialize_field_pair`.
def serialize_decl_for_ctor (format_tag : String) (format_typ : Expr) (type_name : String) (ctor : CtorInfo) : Decl :=
    match ctor {
        ctor_info ctor_name fields =>
            let fmt_typ_name := format_typ_name format_typ in
            let field_names := List.map field_name_of fields in
            let pairs := e_list_lit (List.map (serialize_field_pair format_tag fmt_typ_name) fields) in
            let body := e_match (e_var "v") (List.cons (match_arm ctor_name field_names (e_app (fmt_fn format_tag "_ser_object") pairs)) List.empty) in
            d_def
                (String.concat type_name (String.concat ".serialize_" format_tag))
                (List.cons (meta_param "v" (e_var type_name)) List.empty)
                format_typ
                body
    }

/// Single-constructor (struct) only, matching `derive_lens_meta`'s own
/// precedent -- a multi-constructor `type`'s serializer needs one match
/// arm per constructor, which this generation pass does not build; such
/// a type's codec stays hand-written, as `agent-skills.md`'s `Role`/
/// `Content`/`StopReason` already plan to be.
pub def derive_serialize_meta (format_tag : String) (format_typ : Expr) (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            match ctors {
                List.cons c tail =>
                    match tail {
                        List.empty => List.cons (serialize_decl_for_ctor format_tag format_typ type_name c) List.empty,
                        List.cons _ _ => List.cons (d_error (String.concat "derive_serialize: " (String.concat type_name " has more than one constructor"))) List.empty,
                    },
                List.empty => List.cons (d_error (String.concat "derive_serialize: " (String.concat type_name " has no constructors"))) List.empty,
            }
    }

// ─── Deserialize direction ──────────────────────────────────────────────

/// Decode every element of a `List D`, short-circuiting on the first
/// error -- ordinary parametric polymorphism (`decode_elem` is an
/// explicit function ARGUMENT, no class constraint anywhere in this
/// signature), so it is called directly by name from generated code
/// (`derive.mo`'s own established rule is "never reference a class
/// method from generated code," not "never reference a generic
/// function" -- this one was never the broken shape to begin with: no
/// class, no type-variable-only-in-return-position).
#[terminating]
pub def traverse_decode_list {D : Type} {X : Type} (decode_elem : D -> Result String X) (items : List D) : Result String (List X) :=
    match items {
        List.empty => Result.ok List.empty,
        List.cons hd tl =>
            match decode_elem hd {
                Result.err e => Result.err e,
                Result.ok x =>
                    match traverse_decode_list decode_elem tl {
                        Result.err e => Result.err e,
                        Result.ok xs => Result.ok (List.cons x xs),
                    }
            }
    }

def result_err (e : Expr) : Expr := e_ctor "Result.err" (List.cons e List.empty)
def result_ok (v : Expr) : Expr := e_ctor "Result.ok" (List.cons v List.empty)

/// The format's own wrapper-function name for one `Deserializer` method.
def primitive_deserialize_fn (format_tag : String) (fmt_typ_name : String) (type_name : String) : Expr :=
    if type_name == "String" then fmt_fn format_tag "_de_get_string"
    else if type_name == "I64" then fmt_fn format_tag "_de_get_int"
    else if type_name == "Bool" then fmt_fn format_tag "_de_get_bool"
    else if type_name == fmt_typ_name then e_lam "__serde_id" (e_var type_name) (result_ok (e_var "__serde_id"))
    else e_var (String.concat type_name (String.concat ".deserialize_" format_tag))

/// One already-bound raw value (named `raw_name`, of the format's own
/// type) decoded as `field_typ`, as an `Expr` of type `Result String
/// <field_typ>`. `Option`-ness is handled by the caller (a missing key
/// is `none` without ever reaching here); a PRESENT `Option X` value
/// still reaches this function, decoded as `X` then re-wrapped in `some`.
#[terminating]
def decode_value_expr (format_tag : String) (fmt_typ_name : String) (field_typ : Expr) (raw_name : String) : Expr :=
    let raw := e_var raw_name in
    match option_inner field_typ {
        Option.some inner =>
            e_if (e_app (fmt_fn format_tag "_de_is_null") raw)
                (result_ok (e_ctor "Option.none" List.empty))
                (e_match (decode_value_expr format_tag fmt_typ_name inner raw_name)
                    (List.cons (match_arm "err" (List.cons "__e" List.empty) (result_err (e_var "__e")))
                    (List.cons (match_arm "ok" (List.cons "__v" List.empty) (result_ok (e_ctor "Option.some" (List.cons (e_var "__v") List.empty)))) List.empty))),
        Option.none =>
            match list_inner field_typ {
                Option.some elem_typ =>
                    e_match (e_app (fmt_fn format_tag "_de_get_list") raw)
                        (List.cons (match_arm "err" (List.cons "__e" List.empty) (result_err (e_var "__e")))
                        (List.cons (match_arm "ok" (List.cons "__items" List.empty)
                            (e_app (e_app (e_var "traverse_decode_list") (decode_elem_fn format_tag fmt_typ_name elem_typ)) (e_var "__items"))) List.empty)),
                Option.none =>
                    match expr_head_name field_typ {
                        Option.some name => e_app (primitive_deserialize_fn format_tag fmt_typ_name name) raw,
                        Option.none => e_app (fmt_fn format_tag "_de_get_string") raw,
                    },
            },
    }

/// A bare function VALUE decoding one element of a `List X` field, for
/// `traverse_decode_list` -- same shape as `serialize_elem_fn`, same
/// reasoning: a primitive's wrapper function already has the right
/// `D -> Result String X` signature; a nested struct's generated
/// `deserialize_<format>` does too.
def decode_elem_fn (format_tag : String) (fmt_typ_name : String) (elem_typ : Expr) : Expr :=
    match expr_head_name elem_typ {
        Option.some name => primitive_deserialize_fn format_tag fmt_typ_name name,
        Option.none => fmt_fn format_tag "_de_get_string",
    }

/// What a field's value `Expr` is when its key was ABSENT from the
/// format value: its declared default (reified `Expr`, used as-is -- it
/// is already a value of the field's own type, no decoding needed), else
/// `none` if the field is `Option`-typed, else a hard decode error.
def missing_field_value (field_name : String) (field_typ : Expr) (default : Option Expr) : Expr :=
    match default {
        Option.some d => result_ok d,
        Option.none =>
            match option_inner field_typ {
                Option.some _ => result_ok (e_ctor "Option.none" List.empty),
                Option.none => result_err (e_str (String.concat "missing field: " field_name)),
            },
    }

/// One field's slice of the decode continuation: get the field, branch
/// on present/absent, decode if present, bind the result to the field's
/// own name, and recurse into `rest` of the chain -- `cont` is already
/// the FULLY BUILT remainder (built outside-in by `build_decode_chain`
/// below, since each field's own bound name must be in scope for every
/// field that follows it, including the final constructor call).
def decode_one_field (format_tag : String) (fmt_typ_name : String) (f : FieldInfo) (cont : Expr) : Expr :=
    let fname := field_name_of f in
    let ftyp := field_typ_of f in
    let get_call := e_app (e_app (fmt_fn format_tag "_de_get_field") (e_var "d")) (e_str fname) in
    e_match get_call
        (List.cons (match_arm "err" (List.cons "__e" List.empty) (result_err (e_var "__e")))
        (List.cons (match_arm "ok" (List.cons "__maybe" List.empty)
            (e_match (e_var "__maybe")
                (List.cons (match_arm "none" List.empty (decode_continue fname (missing_field_value fname ftyp (field_default_of f)) cont))
                (List.cons (match_arm "some" (List.cons "__raw" List.empty)
                    (decode_continue fname (decode_value_expr format_tag fmt_typ_name ftyp "__raw") cont)) List.empty)))) List.empty))

/// Thread one field's own `Result String <FieldType>` (`step`) into the
/// rest of the chain (`cont`), binding the success value to the field's
/// own name -- the "continuation-function style" every hand-written
/// multi-field decoder in this codebase already uses by hand
/// (`motes/json/src/json.mo`'s `Person.deserialize_with_name`).
def decode_continue (field_name : String) (step : Expr) (cont : Expr) : Expr :=
    e_match step
        (List.cons (match_arm "err" (List.cons "__e" List.empty) (result_err (e_var "__e")))
        (List.cons (match_arm "ok" (List.cons field_name List.empty) cont) List.empty))

/// Build the whole field-by-field decode chain, outside-in: the
/// INNERMOST expression (built first, here) is the final constructor
/// call; `decode_one_field` wraps progressively earlier fields around it
/// moving right-to-left, so by the time the first field's own
/// `decode_one_field` wraps everything, every later field's bound name
/// is already in scope inside `cont`.
#[partial]
def build_decode_chain (format_tag : String) (fmt_typ_name : String) (type_name : String) (ctor_name : String) (fields : List FieldInfo) : Expr :=
    build_decode_chain_from format_tag fmt_typ_name fields type_name ctor_name List.empty

/// `build_decode_chain`'s own recursion: `seen` accumulates the fields
/// already bound (outermost to this point), used to build the final
/// constructor call once `fields` runs out.
#[partial]
def build_decode_chain_from (format_tag : String) (fmt_typ_name : String) (fields : List FieldInfo) (type_name : String) (ctor_name : String) (seen : List FieldInfo) : Expr :=
    match fields {
        List.empty => result_ok (e_ctor (String.concat type_name (String.concat "." ctor_name)) (List.map (fn f => e_var (field_name_of f)) seen)),
        List.cons f rest =>
            decode_one_field format_tag fmt_typ_name f (build_decode_chain_from format_tag fmt_typ_name rest type_name ctor_name (List.append seen (List.cons f List.empty))),
    }

def deserialize_decl_for_ctor (format_tag : String) (format_typ : Expr) (type_name : String) (ctor : CtorInfo) : Decl :=
    match ctor {
        ctor_info ctor_name fields =>
            d_def
                (String.concat type_name (String.concat ".deserialize_" format_tag))
                (List.cons (meta_param "d" format_typ) List.empty)
                (e_app (e_app (e_var "Result") (e_var "String")) (e_var type_name))
                (build_decode_chain format_tag (format_typ_name format_typ) type_name ctor_name fields)
    }

pub def derive_deserialize_meta (format_tag : String) (format_typ : Expr) (info : TypeInfo) : List Decl :=
    match info {
        type_info type_name ctors =>
            match ctors {
                List.cons c tail =>
                    match tail {
                        List.empty => List.cons (deserialize_decl_for_ctor format_tag format_typ type_name c) List.empty,
                        List.cons _ _ => List.cons (d_error (String.concat "derive_deserialize: " (String.concat type_name " has more than one constructor"))) List.empty,
                    },
                List.empty => List.cons (d_error (String.concat "derive_deserialize: " (String.concat type_name " has no constructors"))) List.empty,
            }
    }
