/// The pre-elaboration term and declaration AST.
///
/// `Surface` is exactly what the parser lowering can build: canonical de
/// Bruijn names, but WITH the four surface forms core `Term` must not carry
/// past the checker (`match`, `if`, struct literal, struct update). It has
/// no `con`, `ntv` or `elim` because no lowering produces them; those come
/// out of elaboration.
///
/// `surface_to_legacy` embeds a `Surface` back into today's core AST, so the
/// pipeline between lowering and S4's boundary flip keeps seeing `Term`.
/// The conversion is total and purely structural; S6 deletes the `Literal`
/// constructors it targets, and the four `Surface` cases become what
/// elaboration compiles directly.
use lang::types {
    Attribute, Binder, Class, ClassDef, DebugName, Decl, Def,
    FieldPattern, FieldPatternEntry, Identifier, InductConstructor, Inductive,
    Instance, Literal, Location, MatchCase, ModulePath, Multiplicity, NamePath,
    NumSuffix, Operator, OpenFilter, Param, SortLevel, Struct,
    StructField, StructLitField, Term, TypeConstraint, UseFilter, Visibility,
}

/// A pre-elaboration term. The payloads are the LOWERED ones, so `lam`/`pi`
/// carry a `Binder` (lowering has already applied `binder_named`/
/// `pi_binder`), not an `Identifier`.
pub type Surface {
    var (idx : I64) (dbg : DebugName),
    var_macro (idx : I64) (dbg : DebugName),
    lam (b : Binder) (typ : Surface) (body : Surface),
    pi (b : Binder) (arg : Surface) (ret : Surface),
    app (fun : Surface) (arg : Surface),
    lit (value : SLiteral),
    sort (level : SortLevel),
    quote_ (term : Surface),
    ctx (loc : Location) (term : Surface),
    hole,
    match_ (value : Surface) (cases : List SMatchCase),
    if_ (one : Surface) (two : Surface) (three : Surface),
    struct_lit (fields : List SStructLitField) (type_name : Option Surface),
    struct_update (base : Surface) (fields : List SStructLitField),
}

/// The immediates only. The four surface forms are `Surface` constructors,
/// not literal cases, so no `SLiteral` can ever be a `match`/`if`/struct
/// form the way `Literal` still spells them.
pub type SLiteral {
    str (value : String),
    char (value : Char),
    num (value : I64) (suffix : NumSuffix),
    flt (text : String) (suffix : NumSuffix),
}

/// A match arm. `field_pattern` is the SHARED `FieldPattern` (it holds no
/// terms), `Option.some` only pre-elaboration for a `{ x, y } => ...` arm;
/// `typ_name` is `Option.none` until the checker resolves the owner.
pub struct SMatchCase {
    name : Identifier,
    args : List Identifier,
    body : Surface,
    field_pattern : Option FieldPattern,
    typ_name : Option NamePath,
}

pub struct SStructLitField {
    name : Identifier,
    value : Surface,
}

// --- Declaration twins --------------------------------------------------
//
// Every declaration a lowering can produce, with its term-carrying fields
// replaced by `Surface`. The term-free fields (`attrs`, `constraints`,
// `vis`, `mult`, filters) are the SHARED canonical types: twinning them
// would only create a second thing to keep in step.

pub struct ParamS {
    name : Identifier,
    type_ : Surface,
    mult : Multiplicity,
    default : Option Surface,
    attrs : List Attribute,
}

pub struct DefS {
    name : NamePath,
    typ : Surface,
    term : Surface,
    constraints : List TypeConstraint,
    attrs : List Attribute,
    vis : Visibility,
    /// The EXPLICIT list only; the implicit clauses are already folded into
    /// `typ` by `wrap_implicit_params` before this twin is built.
    params : List ParamS,
}

pub struct InductConstructorS {
    name : NamePath,
    params : List ParamS,
    typ : Surface,
}

pub struct InductiveS {
    name : NamePath,
    params : List ParamS,
    typ : Surface,
    constructors : List InductConstructorS,
    attrs : List Attribute,
    vis : Visibility,
}

pub struct ClassDefS {
    name : Identifier,
    typ : Surface,
    default : Option Surface,
}

pub struct ClassS {
    name : Identifier,
    params : List ParamS,
    constraints : List TypeConstraint,
    methods : List ClassDefS,
    vis : Visibility,
    sort : Option Surface,
    determined : List ParamS,
}

pub struct StructFieldS {
    name : Identifier,
    typ : Surface,
    default : Option Surface,
    mult : Multiplicity,
}

pub struct StructS {
    name : Identifier,
    fields : List StructFieldS,
    attrs : List Attribute,
    vis : Visibility,
}

pub struct InstanceS {
    name : Identifier,
    cls : NamePath,
    constraints : List TypeConstraint,
    args : List Surface,
    vis : Visibility,
    implicit_params : List ParamS,
    defs : List DefS,
}

pub type DeclS {
    def_ds (DefS),
    inductive_ds (InductiveS),
    struct_ds (StructS),
    class_ds (ClassS),
    instance_ds (InstanceS),
    infix_ds (op : Operator) (path : NamePath) (vis : Visibility),
    use_ds (path : ModulePath) (filter : UseFilter) (public : Bool),
    open_ds (path : NamePath) (filter : OpenFilter),
    scoped_open_ds (path : NamePath) (filter : OpenFilter) (decl : DeclS),
    def_macro_ds (DefS),
    decl_gen_ds (name : NamePath) (params : List ParamS) (decl_list : List DeclS) (attrs : List Attribute),
    macro_call_ds (name : Identifier) (args : List Surface),
    mote_ds (attr : Attribute),
}

// --- The legacy embedding ----------------------------------------------
//
// One conversion per type. The mutually recursive cluster is
// `#[terminating]` (not `#[partial]`): the two are equivalent for the
// termination checker, but `#[partial]` is the parser-table idiom and the
// style ratchet counts `partial_attr_no_self_call`, which a conversion SCC
// would inflate. The recursion is structural, so the claim is honest.

#[terminating]
pub def surface_to_legacy (s : Surface) : Term :=
    match s {
        Surface.var idx dbg => Term.var idx dbg,
        Surface.var_macro idx dbg => Term.var_macro idx dbg,
        Surface.lam b typ body =>
            Term.lam b (surface_to_legacy typ) (surface_to_legacy body),
        Surface.pi b arg ret =>
            Term.pi b (surface_to_legacy arg) (surface_to_legacy ret),
        Surface.app f a => Term.app (surface_to_legacy f) (surface_to_legacy a),
        Surface.lit l => Term.lit (surface_literal_to_legacy l),
        Surface.sort level => Term.sort level,
        Surface.quote_ t => Term.quote_ (surface_to_legacy t),
        Surface.ctx loc t => Term.ctx loc (surface_to_legacy t),
        Surface.hole => Term.hole,
        Surface.match_ v cs =>
            Term.lit (Literal.match_ (surface_to_legacy v) (surface_match_cases_to_legacy cs)),
        Surface.if_ a b c =>
            Term.lit (Literal.if_ (surface_to_legacy a) (surface_to_legacy b) (surface_to_legacy c)),
        Surface.struct_lit fs tn =>
            Term.lit (Literal.struct_lit (surface_struct_lit_fields_to_legacy fs) (surface_opt_to_legacy tn)),
        Surface.struct_update base fs =>
            Term.lit (Literal.struct_update (surface_to_legacy base) (surface_struct_lit_fields_to_legacy fs)),
    }

#[terminating]
pub def surface_opt_to_legacy (t : Option Surface) : Option Term :=
    match t {
        Option.some x => Option.some (surface_to_legacy x),
        Option.none => Option.none,
    }

pub def surface_literal_to_legacy (l : SLiteral) : Literal :=
    match l {
        SLiteral.str v => Literal.str v,
        SLiteral.char v => Literal.char v,
        SLiteral.num n suf => Literal.num n suf,
        SLiteral.flt t suf => Literal.flt t suf,
    }

/// A match arm binds its pattern's names over its BODY; the conversion
/// must not reorder or re-resolve anything.
#[terminating]
pub def surface_match_cases_to_legacy (cs : List SMatchCase) : List MatchCase :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (surface_match_case_to_legacy c) (surface_match_cases_to_legacy rest),
    }

#[terminating]
pub def surface_match_case_to_legacy (c : SMatchCase) : MatchCase :=
    match c {
        SMatchCase.mk { name, args, body, field_pattern, typ_name } =>
            MatchCase.mk name args (surface_to_legacy body) field_pattern typ_name,
    }

pub def surface_struct_lit_fields_to_legacy (fs : List SStructLitField) : List StructLitField :=
    match fs {
        List.empty => List.empty,
        List.cons f rest =>
            List.cons (surface_struct_lit_field_to_legacy f)
                (surface_struct_lit_fields_to_legacy rest),
    }

pub def surface_struct_lit_field_to_legacy (f : SStructLitField) : StructLitField :=
    match f {
        SStructLitField.mk { name, value } => StructLitField.mk name (surface_to_legacy value),
    }

#[terminating]
pub def surface_terms_to_legacy (ts : List Surface) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons t rest =>
            List.cons (surface_to_legacy t) (surface_terms_to_legacy rest),
    }

/// A struct-field ACCESS chain (`p.first.second`) as one-arm matches, the
/// twin of `lang::types.field_access_chain`. Kept identical to the original
/// on purpose: it must embed to the same term, and the checker's own caller
/// keeps the `Term` version until S6.
pub def s_field_access_chain (scrutinee : Surface) (fields : List Identifier) : Surface :=
    match fields {
        List.empty => scrutinee,
        List.cons field rest =>
            let value : Surface := s_field_access_chain (Surface.var 0 (DebugName.named field)) rest in
            let entry : FieldPatternEntry := FieldPatternEntry.mk field field in
            let fp : FieldPattern := FieldPattern.mk (List.cons entry List.empty) true in
            let binders : List Identifier := List.cons field List.empty in
            let case_ : SMatchCase := SMatchCase.mk (Identifier.id "") binders value (Option.some fp) Option.none in
            Surface.match_ scrutinee (List.cons case_ List.empty),
    }

// --- Declarations ------------------------------------------------------

#[terminating]
pub def surface_decls_to_legacy (ds : List DeclS) : List Decl :=
    match ds {
        List.empty => List.empty,
        List.cons d rest =>
            List.append (surface_decl_to_legacy d) (surface_decls_to_legacy rest),
    }

/// One surface declaration's core declarations: exactly one, except a
/// `with` block, which the lowering has already spliced out flat, and a
/// `scoped_open`, which wraps one.
pub def surface_decl_to_legacy (d : DeclS) : List Decl :=
    match d {
        DeclS.def_ds def_ => [Decl.def_d (surface_def_to_legacy def_)],
        DeclS.inductive_ds i => [Decl.inductive_d (surface_inductive_to_legacy i)],
        DeclS.struct_ds s => [Decl.struct_d (surface_struct_to_legacy s)],
        DeclS.class_ds c => [Decl.class_d (surface_class_to_legacy c)],
        DeclS.instance_ds i => [Decl.instance_d (surface_instance_to_legacy i)],
        DeclS.infix_ds op path vis => [Decl.infix_d op path vis],
        DeclS.use_ds path filter public => [Decl.use_d path filter public],
        DeclS.open_ds path filter => [Decl.open_d path filter],
        DeclS.scoped_open_ds path filter inner =>
            scoped_open_legacy path filter (surface_decl_to_legacy inner),
        DeclS.def_macro_ds def_ => [Decl.def_macro_d (surface_def_to_legacy def_)],
        DeclS.decl_gen_ds name params decl_list attrs =>
            [Decl.decl_gen_d name (surface_params_to_legacy params) (surface_decls_to_legacy decl_list) attrs],
        DeclS.macro_call_ds name args =>
            [Decl.macro_call_d name (surface_terms_to_legacy args)],
        DeclS.mote_ds attr => [Decl.mote_d attr],
    }

#[partial]
def scoped_open_legacy (path : NamePath) (filter : OpenFilter) (ds : List Decl) : List Decl :=
    match ds {
        List.empty => List.empty,
        List.cons d rest =>
            List.cons (Decl.scoped_open_d path filter d) (scoped_open_legacy path filter rest),
    }

pub def surface_def_to_legacy (d : DefS) : Def :=
    match d {
        DefS.mk { name := nm, typ, term, constraints, attrs, vis, params } =>
            { name := nm,
                typ := surface_to_legacy typ,
                term := surface_to_legacy term,
                constraints := constraints,
                attrs := attrs,
                vis := vis,
                params := surface_params_to_legacy params },
    }

pub def surface_defs_to_legacy (ds : List DefS) : List Def :=
    match ds {
        List.empty => List.empty,
        List.cons d rest =>
            List.cons (surface_def_to_legacy d) (surface_defs_to_legacy rest),
    }

pub def surface_param_to_legacy (p : ParamS) : Param :=
    match p {
        ParamS.mk { name, type_, mult, default, attrs } =>
            { name := name,
                type_ := surface_to_legacy type_,
                mult := mult,
                default := surface_opt_to_legacy default,
                attrs := attrs },
    }

pub def surface_params_to_legacy (ps : List ParamS) : List Param :=
    match ps {
        List.empty => List.empty,
        List.cons p rest =>
            List.cons (surface_param_to_legacy p) (surface_params_to_legacy rest),
    }

pub def surface_inductive_to_legacy (i : InductiveS) : Inductive :=
    match i {
        InductiveS.mk { name := nm, params, typ, constructors, attrs, vis } =>
            Inductive.mk nm (surface_params_to_legacy params) (surface_to_legacy typ)
                (surface_induct_ctors_to_legacy constructors) attrs vis,
    }

pub def surface_induct_ctors_to_legacy (cs : List InductConstructorS) : List InductConstructor :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (surface_induct_ctor_to_legacy c) (surface_induct_ctors_to_legacy rest),
    }

pub def surface_induct_ctor_to_legacy (c : InductConstructorS) : InductConstructor :=
    match c {
        InductConstructorS.mk { name := nm, params, typ } =>
            InductConstructor.mk nm (surface_params_to_legacy params) (surface_to_legacy typ),
    }

pub def surface_struct_to_legacy (s : StructS) : Struct :=
    match s {
        StructS.mk { name, fields, attrs, vis } =>
            Struct.mk name (surface_struct_fields_to_legacy fields) attrs vis,
    }

pub def surface_struct_fields_to_legacy (fs : List StructFieldS) : List StructField :=
    match fs {
        List.empty => List.empty,
        List.cons f rest =>
            List.cons (surface_struct_field_to_legacy f) (surface_struct_fields_to_legacy rest),
    }

pub def surface_struct_field_to_legacy (f : StructFieldS) : StructField :=
    match f {
        StructFieldS.mk { name, typ, default, mult } =>
            { name := name,
                typ := surface_to_legacy typ,
                default := surface_opt_to_legacy default,
                mult := mult },
    }

pub def surface_class_to_legacy (c : ClassS) : Class :=
    match c {
        ClassS.mk { name, params, constraints, methods, vis, sort, determined } =>
            Class.mk name (surface_params_to_legacy params) constraints
                (surface_class_defs_to_legacy methods) vis
                (surface_opt_to_legacy sort)
                (surface_params_to_legacy determined),
    }

pub def surface_class_defs_to_legacy (ms : List ClassDefS) : List ClassDef :=
    match ms {
        List.empty => List.empty,
        List.cons m rest =>
            List.cons (surface_class_def_to_legacy m) (surface_class_defs_to_legacy rest),
    }

pub def surface_class_def_to_legacy (m : ClassDefS) : ClassDef :=
    match m {
        ClassDefS.mk { name, typ, default } =>
            ClassDef.mk name (surface_to_legacy typ) (surface_opt_to_legacy default),
    }

pub def surface_instance_to_legacy (i : InstanceS) : Instance :=
    match i {
        InstanceS.mk { name, cls, constraints, args, vis, implicit_params, defs } =>
            Instance.mk name cls constraints (surface_terms_to_legacy args) vis
                (surface_params_to_legacy implicit_params) (surface_defs_to_legacy defs),
    }
