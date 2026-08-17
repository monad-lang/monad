/// Reflection-as-data types for the metaprogramming/derive system — see
/// `plans/review-and-reduce-the-greedy-nest.md` for the full design.
/// `TypeInfo`/`CtorInfo`/`FieldInfo` expose a type's structure
/// (constructors, fields, field names/types) as ordinary Monad values;
/// `Expr`/`MatchArm`/`Param`/`Decl` are a small, deliberately minimal
/// mirror of the compiler's own `Term`/`Decl` surface, letting a "meta"
/// function — an ordinary `def` invoked via
/// `core/src/eval/meta_compile.rs`, NOT a `defmacro` template — build new
/// code with ordinary function calls (`List.map`/`Foldable.foldl`/
/// `match`/recursion) and hand the result back to be spliced into the
/// program. This is the Monad-source half of the design; the Rust half
/// (`std/eval/meta_reflect.rs`) converts between these values and the
/// compiler's real `Inductive`/`Term`/`Decl`.

/// One field of one constructor: its declared name, and its type as a
/// constructible `Expr` (so it can be echoed straight into generated
/// code, e.g. a lens's `Lens T field_typ` type).
type FieldInfo {
    field_info (name : String) (typ : Expr)
}

/// One constructor: its declared name, and its fields in declared order.
type CtorInfo {
    ctor_info (name : String) (fields : List FieldInfo)
}

/// A type's full structure: its own name, and its constructors in
/// declared order. Does not carry the type's own generic parameters
/// (`Inductive.params`) or per-field attributes/defaults/multiplicity —
/// no existing derive needs them; see the design doc for why this scope
/// is deliberate, not an oversight.
type TypeInfo {
    type_info (name : String) (ctors : List CtorInfo)
}

/// A minimal, constructible mirror of the compiler's own `Term` surface —
/// deliberately NOT a full mirror. `Pi`/`Forall`/`Sort`/`Ann`/`Ntv`/`Ctx`/
/// `Hole`/`Quote` are excluded: compiler-internal, derivable from a
/// generated `def`'s param-list/return-type shape (see `Decl.d_def`
/// below), or simply never needed by any of this design's target
/// derives' generated code. `e_ctor` is a deliberate ergonomic addition
/// over the raw `Term` surface (constructor rebuild is common to every
/// derive) rather than forcing callers to spell out nested `e_app`s.
type Expr {
    e_var (name : String),
    e_str (value : String),
    e_int (value : I64),
    e_bool (value : Bool),
    e_app (func : Expr) (arg : Expr),
    e_lam (param_name : String) (param_typ : Expr) (body : Expr),
    e_if (cond : Expr) (then_ : Expr) (else_ : Expr),
    e_match (scrutinee : Expr) (arms : List MatchArm),
    e_ctor (ctor_name : String) (args : List Expr),
}

/// One arm of an `e_match` — the constructor it matches, its bound field
/// names (in declared order), and the arm's body.
type MatchArm {
    match_arm (ctor_name : String) (binders : List String) (body : Expr)
}

/// One parameter of a generated `def` (`Decl.d_def`).
type Param {
    meta_param (name : String) (typ : Expr)
}

/// A minimal, constructible mirror of the compiler's own `Decl` surface —
/// just enough for the four derives this design targets: a `def` (name,
/// params, return type, body) and an `instance` (class name, target
/// type, methods — each itself a `d_def`).
type Decl {
    d_def (name : String) (params : List Param) (ret_typ : Expr) (body : Expr),
    d_instance (class_name : String) (target_typ : Expr) (methods : List Decl),
}
