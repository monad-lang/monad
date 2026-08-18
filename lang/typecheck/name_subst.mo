/// NAME-based `Term`/`Decl` substitution — the primitive DECL-generating
/// macro templates (`defmacro name params := decls { ... }`) need,
/// sibling to [[lang/typecheck/subst.mo]]'s de-Bruijn `term_shift`/
/// `term_subst` (which cover the OTHER macro form, `defmacro name
/// params := <term>`, and explicitly don't apply here — see that
/// file's own doc comment for why the two forms need genuinely
/// different substitution mechanisms).
///
/// A decl-gen template's own top-level decl_list have no enclosing lambda
/// binder — a macro param referenced inside one (typically inside a
/// nested `Decl.macro_call_d`'s own `args`, e.g. `std/derive.mo`'s
/// `reflect_type_info! T derive_lens_meta`) is an ordinary FREE
/// `Term.var sentinel (DebugName.named X)` reference (`sentinel = -1`,
/// see `lang/typecheck/infer.mo`), not a bound de Bruijn index. This
/// module walks a `Term`/`Decl` tree looking for exactly that shape —
/// a `Term.var` whose `DebugName` is `named` and matches the target
/// identifier by string equality (`id_eq`) — and replaces it wholesale
/// with a given replacement `Term`, leaving every bound index alone
/// untouched (nothing here is de-Bruijn-sensitive, so unlike
/// `subst.mo` there is no depth/cutoff bookkeeping at all).
///
/// Mirrors the Rust reference's own `subst_macro`/`subst_decl_var`
/// (`core/src/eval/macro_expand.rs`), minus `subst_decl_var`'s
/// `subst_path_component` handling of a macro param appearing inside a
/// generated DECL'S OWN NAME (e.g. templated `def get_$field := ...`)
/// — self-hosted's grammar has no string-interpolated-decl-name syntax
/// to parse that from in the first place (`ModulePath`/`Identifier`
/// are plain, non-templated strings throughout), so there is nothing
/// for that case to substitute into here.
///
/// Deliberate simplification, matching the reference's own equally
/// simple walk-and-replace (no shadow-tracking there either): if a
/// template itself locally re-binds the same name the macro param
/// uses (e.g. a nested `def`/`defmacro`'s own param shares the outer
/// macro's param name), this walk does NOT stop substituting inside
/// that shadowed scope. Not exercised by any real corpus template
/// today (`std/derive.mo`'s own templates only ever reference their
/// macro param from a nested `macro_call_d`'s `args`, no nested
/// binders of the same name) — flagged here rather than silently
/// assumed correct.
use lang.types {
  Attribute, Class, ClassDef, Con, Decl, Def, Identifier, InductConstructor,
  Inductive, Instance, Literal, MatchCase, ModulePath, Native, Param, Struct,
  StructField, StructLitField, Term, TypeConstraint,
  id_eq,
}

// ─── Term-level walk ─────────────────────────────────────────────────

#[partial]
def name_subst_term (target : Identifier) (replacement : Term) (t : Term) : Term :=
    match t {
        Term.var idx dbg =>
            match dbg {
                DebugName.named id => if id_eq id target then replacement else Term.var idx dbg,
                DebugName.unnamed => Term.var idx dbg,
            },
        // `name!` macro-call references are a different reference kind
        // entirely (see `lang/types.mo`'s own `Term.var_macro` doc
        // comment) -- never a plain param reference, so never a
        // substitution target here, and (being a leaf) nothing to
        // recurse into either.
        Term.var_macro idx dbg => Term.var_macro idx dbg,
        Term.lam dbg typ body =>
            Term.lam dbg (name_subst_term target replacement typ) (name_subst_term target replacement body),
        Term.forall dbg kind body =>
            Term.forall dbg (name_subst_term target replacement kind) (name_subst_term target replacement body),
        Term.pi arg ret =>
            Term.pi (name_subst_term target replacement arg) (name_subst_term target replacement ret),
        Term.app callee arg =>
            Term.app (name_subst_term target replacement callee) (name_subst_term target replacement arg),
        Term.lit value => Term.lit (literal_name_subst target replacement value),
        Term.ntv n => Term.ntv (native_name_subst target replacement n),
        Term.con c => Term.con (con_name_subst target replacement c),
        Term.type_ u => Term.type_ u,
        Term.hole => Term.hole,
        // Walk INTO quote (matches the reference's own `subst_macro`,
        // which substitutes before `resolve_quote` ever runs) -- a
        // quoted `unquote(param)` needs the same treatment as a bare
        // reference, and this module has no `resolve_quote`-equivalent
        // of its own to defer to.
        Term.quote_ inner => Term.quote_ (name_subst_term target replacement inner),
    }

#[partial]
def literal_name_subst (target : Identifier) (replacement : Term) (l : Literal) : Literal :=
    match l {
        Literal.str v => Literal.str v,
        Literal.num n suf => Literal.num n suf,
        Literal.flt t suf => Literal.flt t suf,
        Literal.if_ a b c =>
            Literal.if_ (name_subst_term target replacement a) (name_subst_term target replacement b) (name_subst_term target replacement c),
        Literal.match_ scrut cases =>
            Literal.match_ (name_subst_term target replacement scrut) (match_cases_name_subst target replacement cases),
        Literal.struct_lit fields type_name =>
            Literal.struct_lit (struct_fields_name_subst target replacement fields) (opt_term_name_subst target replacement type_name),
        Literal.struct_update base fields =>
            Literal.struct_update (name_subst_term target replacement base) (struct_fields_name_subst target replacement fields),
    }

#[partial]
def match_cases_name_subst (target : Identifier) (replacement : Term) (cases : List MatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest => List.cons (match_case_name_subst target replacement c) (match_cases_name_subst target replacement rest),
    }

#[partial]
def match_case_name_subst (target : Identifier) (replacement : Term) (c : MatchCase) : MatchCase :=
    match c { MatchCase.mc name args body => MatchCase.mc name args (name_subst_term target replacement body) }

#[partial]
def struct_fields_name_subst (target : Identifier) (replacement : Term) (fields : List StructLitField) : List StructLitField :=
    match fields {
        List.empty => List.empty,
        List.cons f rest => List.cons (struct_field_name_subst target replacement f) (struct_fields_name_subst target replacement rest),
    }

#[partial]
def struct_field_name_subst (target : Identifier) (replacement : Term) (f : StructLitField) : StructLitField :=
    match f { StructLitField.mk name value => StructLitField.mk name (name_subst_term target replacement value) }

#[partial]
def opt_term_name_subst (target : Identifier) (replacement : Term) (t : Option Term) : Option Term :=
    match t {
        Option.some x => Option.some (name_subst_term target replacement x),
        Option.none => Option.none,
    }

#[partial]
def opt_terms_name_subst (target : Identifier) (replacement : Term) (ts : List (Option Term)) : List (Option Term) :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (opt_term_name_subst target replacement x) (opt_terms_name_subst target replacement rest),
    }

#[partial]
def terms_name_subst (target : Identifier) (replacement : Term) (ts : List Term) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (name_subst_term target replacement x) (terms_name_subst target replacement rest),
    }

#[partial]
def con_name_subst (target : Identifier) (replacement : Term) (c : Con) : Con :=
    match c { Con.mk name typ_name num_args args => Con.mk name typ_name num_args (opt_terms_name_subst target replacement args) }

#[partial]
def native_name_subst (target : Identifier) (replacement : Term) (n : Native) : Native :=
    match n { Native.mk name num_args args => Native.mk name num_args (opt_terms_name_subst target replacement args) }

// ─── Param / signature-level walk ───────────────────────────────────

#[partial]
def param_name_subst (target : Identifier) (replacement : Term) (p : Param) : Param :=
    match p {
        Param.mk name typ mult default attrs =>
            Param.mk name (name_subst_term target replacement typ) mult (opt_term_name_subst target replacement default) attrs,
    }

#[partial]
def params_name_subst (target : Identifier) (replacement : Term) (params : List Param) : List Param :=
    match params {
        List.empty => List.empty,
        List.cons p rest => List.cons (param_name_subst target replacement p) (params_name_subst target replacement rest),
    }

#[partial]
def induct_constructor_name_subst (target : Identifier) (replacement : Term) (ctor : InductConstructor) : InductConstructor :=
    match ctor {
        InductConstructor.mk name params typ =>
            InductConstructor.mk name (params_name_subst target replacement params) (name_subst_term target replacement typ),
    }

#[partial]
def induct_constructors_name_subst (target : Identifier) (replacement : Term) (ctors : List InductConstructor) : List InductConstructor :=
    match ctors {
        List.empty => List.empty,
        List.cons c rest => List.cons (induct_constructor_name_subst target replacement c) (induct_constructors_name_subst target replacement rest),
    }

#[partial]
def struct_field_sig_name_subst (target : Identifier) (replacement : Term) (f : StructField) : StructField :=
    match f {
        StructField.mk name typ default mult =>
            StructField.mk name (name_subst_term target replacement typ) (opt_term_name_subst target replacement default) mult,
    }

#[partial]
def struct_fields_sig_name_subst (target : Identifier) (replacement : Term) (fields : List StructField) : List StructField :=
    match fields {
        List.empty => List.empty,
        List.cons f rest => List.cons (struct_field_sig_name_subst target replacement f) (struct_fields_sig_name_subst target replacement rest),
    }

#[partial]
def class_def_name_subst (target : Identifier) (replacement : Term) (cd : ClassDef) : ClassDef :=
    match cd {
        ClassDef.mk name typ default =>
            ClassDef.mk name (name_subst_term target replacement typ) (opt_term_name_subst target replacement default),
    }

#[partial]
def class_defs_name_subst (target : Identifier) (replacement : Term) (cds : List ClassDef) : List ClassDef :=
    match cds {
        List.empty => List.empty,
        List.cons cd rest => List.cons (class_def_name_subst target replacement cd) (class_defs_name_subst target replacement rest),
    }

// ─── Decl-level walk ─────────────────────────────────────────────────

#[partial]
def def_name_subst (target : Identifier) (replacement : Term) (d : Def) : Def :=
    match d {
        Def.mk name typ term constraints attrs vis =>
            Def.mk name (name_subst_term target replacement typ) (name_subst_term target replacement term) constraints attrs vis,
    }

#[partial]
def inductive_name_subst (target : Identifier) (replacement : Term) (ind : Inductive) : Inductive :=
    match ind {
        Inductive.mk name params typ constructors attrs vis =>
            Inductive.mk name (params_name_subst target replacement params) (name_subst_term target replacement typ)
                (induct_constructors_name_subst target replacement constructors) attrs vis,
    }

#[partial]
def struct_name_subst (target : Identifier) (replacement : Term) (s : Struct) : Struct :=
    match s { Struct.mk name fields vis => Struct.mk name (struct_fields_sig_name_subst target replacement fields) vis }

#[partial]
def class_name_subst (target : Identifier) (replacement : Term) (cls : Class) : Class :=
    match cls {
        Class.mk name params constraints methods vis =>
            Class.mk name (params_name_subst target replacement params) constraints (class_defs_name_subst target replacement methods) vis,
    }

#[partial]
def instance_name_subst (target : Identifier) (replacement : Term) (ins : Instance) : Instance :=
    match ins {
        Instance.mk name cls constraints args vis implicit_params =>
            Instance.mk name cls constraints (terms_name_subst target replacement args) vis (params_name_subst target replacement implicit_params),
    }

/// Substitute `target` for `replacement` throughout one `Decl` — the
/// per-template-decl step `expand_macro_call`'s own loop (Step 4, not
/// yet written) folds over every `(param, arg)` pair for every decl in
/// a `Decl.decl_gen_d`'s own `decl_list` list. This function handles ONE
/// `(target, replacement)` pair for ONE decl, mirroring the reference's
/// own `subst_decl_var`'s equally single-substitution shape.
#[partial]
def name_subst_decl (target : Identifier) (replacement : Term) (d : Decl) : Decl :=
    match d {
        Decl.def_d d_val => Decl.def_d (def_name_subst target replacement d_val),
        Decl.inductive_d ind => Decl.inductive_d (inductive_name_subst target replacement ind),
        Decl.struct_d s => Decl.struct_d (struct_name_subst target replacement s),
        Decl.class_d cls => Decl.class_d (class_name_subst target replacement cls),
        Decl.instance_d ins => Decl.instance_d (instance_name_subst target replacement ins),
        Decl.infix_d op path vis => Decl.infix_d op path vis,
        Decl.use_d path filter public => Decl.use_d path filter public,
        Decl.open_d path filter => Decl.open_d path filter,
        Decl.scoped_open_d path filter inner => Decl.scoped_open_d path filter (name_subst_decl target replacement inner),
        Decl.def_macro_d d_val => Decl.def_macro_d (def_name_subst target replacement d_val),
        Decl.decl_gen_d name params decl_list attrs =>
            Decl.decl_gen_d name (params_name_subst target replacement params) (name_subst_decls target replacement decl_list) attrs,
        Decl.macro_call_d name args => Decl.macro_call_d name (terms_name_subst target replacement args),
    }

#[partial]
def name_subst_decls (target : Identifier) (replacement : Term) (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest => List.cons (name_subst_decl target replacement d) (name_subst_decls target replacement rest),
    }

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Term`/`Decl` fixtures, asserted directly against the
// returned shape (same convention as `lang/typecheck/subst.mo`'s own
// tests) -- no pipeline wiring yet, purely exercising this primitive
// in isolation.

def t_ident : Identifier := Identifier.id "T"
def other_ident : Identifier := Identifier.id "U"
def named_ref (id : Identifier) : Term := Term.var (0 - 1) (DebugName.named id)

#[partial]
def term_type_level (t : Term) : I64 :=
    match t { Term.type_ u => u }

#[test]
def test_name_subst_term_replaces_matching_named_var : Bool :=
    let replacement : Term := Term.type_ 7 in
    I64.beq (term_type_level (name_subst_term t_ident replacement (named_ref t_ident))) 7

#[test]
def test_name_subst_term_leaves_other_named_var_untouched : Bool :=
    // `U` is a different identifier than the substitution target `T`
    // -- must come back completely unchanged.
    let replacement : Term := Term.type_ 7 in
    match name_subst_term t_ident replacement (named_ref other_ident) {
        Term.var _ dbg => match dbg { DebugName.named id => id_eq id other_ident, DebugName.unnamed => false },
        _ => false,
    }

#[test]
def test_name_subst_term_leaves_bound_var_untouched : Bool :=
    // A real (non-`sentinel`, `DebugName.unnamed`) de Bruijn-bound
    // occurrence has no name to match against at all -- never a
    // substitution target, regardless of `target`/`replacement`.
    let replacement : Term := Term.type_ 7 in
    let bound : Term := Term.var 0 DebugName.unnamed in
    match name_subst_term t_ident replacement bound {
        Term.var idx _ => I64.beq idx 0,
        _ => false,
    }

#[test]
def test_name_subst_term_recurses_into_quote : Bool :=
    // Matches the reference's own `subst_macro`, which substitutes
    // INTO a `Quote` body before `resolve_quote` ever runs.
    let replacement : Term := Term.type_ 9 in
    let quoted : Term := Term.quote_ (named_ref t_ident) in
    match name_subst_term t_ident replacement quoted {
        Term.quote_ inner => I64.beq (term_type_level inner) 9,
        _ => false,
    }

#[test]
def test_name_subst_decl_macro_call_d_substitutes_args : Bool :=
    // Mirrors `std/derive.mo`'s real decl-gen template shape:
    // `reflect_type_info! T derive_lens_meta` inside a `decls { ... }`
    // body, with `T` the macro's own param.
    let replacement : Term := Term.type_ 3 in
    let call : Decl :=
        Decl.macro_call_d (Identifier.id "reflect_type_info")
            (List.cons (named_ref t_ident) (List.cons (named_ref other_ident) List.empty)) in
    match name_subst_decl t_ident replacement call {
        Decl.macro_call_d _ args =>
            match args {
                List.cons first rest =>
                    I64.beq (term_type_level first) 3 &&
                    match rest {
                        List.cons second _ =>
                            match second { Term.var _ dbg => match dbg { DebugName.named id => id_eq id other_ident, DebugName.unnamed => false }, _ => false },
                        List.empty => false,
                    },
                List.empty => false,
            },
        _ => false,
    }

#[test]
def test_name_subst_decl_def_d_substitutes_typ_and_term : Bool :=
    let replacement : Term := Term.type_ 5 in
    let empty_constraints : List TypeConstraint := List.empty in
    let empty_attrs : List Attribute := List.empty in
    let d : Decl :=
        Decl.def_d (Def.mk (ModulePath.mp (List.cons (Identifier.id "make") List.empty)) (named_ref t_ident) (named_ref t_ident) empty_constraints empty_attrs Visibility.package_private) in
    match name_subst_decl t_ident replacement d {
        Decl.def_d d_val =>
            match d_val {
                Def.mk _ typ term _ _ _ => I64.beq (term_type_level typ) 5 && I64.beq (term_type_level term) 5,
            },
        _ => false,
    }

#[test]
def test_name_subst_decl_decl_gen_d_recurses_into_nested_decls : Bool :=
    // The real `std/derive.mo` shape one level up: a `Decl.decl_gen_d`
    // template whose own `decl_list` list holds exactly one
    // `Decl.macro_call_d` referencing the template's own param.
    let replacement : Term := Term.type_ 11 in
    let nested_call : Decl := Decl.macro_call_d (Identifier.id "reflect_type_info") (List.cons (named_ref t_ident) List.empty) in
    let template : Decl :=
        Decl.decl_gen_d (ModulePath.mp (List.cons (Identifier.id "derive_lens") List.empty)) List.empty (List.cons nested_call List.empty) List.empty in
    match name_subst_decl t_ident replacement template {
        Decl.decl_gen_d _ _ decl_list _ =>
            match decl_list {
                List.cons inner_decl _ =>
                    match inner_decl {
                        Decl.macro_call_d _ args =>
                            match args { List.cons a _ => I64.beq (term_type_level a) 11, List.empty => false },
                        _ => false,
                    },
                List.empty => false,
            },
        _ => false,
    }

#[test]
def test_name_subst_decl_use_d_passthrough_unchanged : Bool :=
    // `use`/`open`/`infix` decl_list carry no `Term` fields at all --
    // must pass through completely unchanged (mirrors the reference's
    // own `subst_decl_var` no-op arms for these same decl kinds).
    let replacement : Term := Term.type_ 1 in
    let path : ModulePath := ModulePath.mp (List.cons (Identifier.id "std") List.empty) in
    let d : Decl := Decl.use_d path UseFilter.use_bare true in
    match name_subst_decl t_ident replacement d {
        Decl.use_d _ _ public => public,
        _ => false,
    }

#[test]
def test_name_subst_decls_maps_over_list : Bool :=
    let replacement : Term := Term.type_ 2 in
    let call1 : Decl := Decl.macro_call_d (Identifier.id "a") (List.cons (named_ref t_ident) List.empty) in
    let call2 : Decl := Decl.macro_call_d (Identifier.id "b") (List.cons (named_ref t_ident) List.empty) in
    let results : List Decl := name_subst_decls t_ident replacement (List.cons call1 (List.cons call2 List.empty)) in
    match results {
        List.cons r1 rest =>
            match rest {
                List.cons r2 _ =>
                    match r1 {
                        Decl.macro_call_d _ args1 =>
                            match args1 {
                                List.cons a1 _ =>
                                    match r2 {
                                        Decl.macro_call_d _ args2 =>
                                            match args2 {
                                                List.cons a2 _ => I64.beq (term_type_level a1) 2 && I64.beq (term_type_level a2) 2,
                                                List.empty => false,
                                            },
                                        _ => false,
                                    },
                                List.empty => false,
                            },
                        _ => false,
                    },
                List.empty => false,
            },
        List.empty => false,
    }
