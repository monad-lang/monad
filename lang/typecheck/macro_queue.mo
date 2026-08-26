/// The decl-level entry point — `expand_decls`, mirroring the Rust
/// reference's own `expand_macros` (`core/src/eval/macro_expand.rs`):
/// one module's own already-parsed decl_list in, decl_list with every macro
/// resolved out.
///
/// Builds a macro registry directly from the decl_list list itself (bare
/// name -> definition, matching how [[lang/typecheck/macro_expand.mo]]'s
/// `expand_term`/`resolve_quote` already expect their own `lookup`
/// argument shaped), then walks the list once: `Decl.def_macro_d`/
/// `Decl.decl_gen_d` are macro DEFINITIONS, consumed into the registry
/// and dropped from the output (they don't correspond to any real
/// runtime definition); `Decl.macro_call_d` is resolved against the
/// decl-gen registry and replaced by its expansion; every other decl
/// kind is kept, with its own embedded `Term` fields run through
/// `expand_term` (so term-position macro calls inside an ordinary
/// `def`/`struct`/... get resolved too).
///
/// **Single-pass, not fixpoint** — a deliberate, explicitly-flagged
/// scope-narrowing (see the macro-expansion plan's own Step 6 note):
/// the reference's `expand_macros` uses a work-queue that re-queues a
/// `Decl.macro_call_d`'s own expansion result at the QUEUE FRONT, so a
/// decl-gen template whose own body itself contains a nested decl-
/// position macro call gets fully resolved, however deep. This
/// version expands a `macro_call_d`'s result's own `Term` fields
/// (so a *term*-position macro nested inside a decl-gen template's
/// output still resolves) but does NOT re-scan the result for further
/// NESTED *decl*-position macro calls. `std/derive.mo` — the one real
/// corpus target this whole effort has — doesn't need that: its own
/// four decl-gen templates each produce exactly one
/// `reflect_type_info!` call and nothing nests inside it. Flagged
/// here, not silently assumed sufficient forever — genuine fixpoint
/// requeuing is a follow-up if a real template ever needs it.
use lang.types {
  Attribute, Class, ClassDef, Decl, Def, Identifier, InductConstructor,
  Inductive, Instance, ModulePath, Param, Struct, StructField, Term,
  TypeConstraint, id_eq,
}
use lang.typecheck.macro_apply {expand_decl_gen_call}
use lang.typecheck.macro_expand {expand_term}

// ─── Registry ───────────────────────────────────────────────────────

type TermMacroEntry { tm_entry (name: Identifier) (body: Term) }
type DeclGenEntry { dg_entry (name: Identifier) (params: List Param) (decl_list: List Decl) }

#[partial]
def module_path_last (mp : ModulePath) : Option Identifier :=
    match mp { ModulePath.mp ids => List.last ids }

#[partial]
def build_term_macro_registry (decl_list : List Decl) : List TermMacroEntry :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_macro_d d_val =>
                    match d_val {
                        Def.mk name _ term _ _ _ =>
                            match module_path_last name {
                                Option.some id => List.cons (TermMacroEntry.tm_entry id term) (build_term_macro_registry rest),
                                Option.none => build_term_macro_registry rest,
                            },
                    },
                _ => build_term_macro_registry rest,
            },
    }

#[partial]
def build_decl_gen_registry (decl_list : List Decl) : List DeclGenEntry :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.decl_gen_d name params gen_decls _attrs =>
                    match module_path_last name {
                        Option.some id => List.cons (DeclGenEntry.dg_entry id params gen_decls) (build_decl_gen_registry rest),
                        Option.none => build_decl_gen_registry rest,
                    },
                _ => build_decl_gen_registry rest,
            },
    }

#[partial]
def lookup_term_macro (registry : List TermMacroEntry) (target : Identifier) : Option Term :=
    match registry {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                TermMacroEntry.tm_entry name body =>
                    if id_eq name target then Option.some body else lookup_term_macro rest target,
            },
    }

#[partial]
def lookup_decl_gen (registry : List DeclGenEntry) (target : Identifier) : Option DeclGenEntry :=
    match registry {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                DeclGenEntry.dg_entry name _ _ =>
                    if id_eq name target then Option.some e else lookup_decl_gen rest target,
            },
    }

// ─── Term-position expansion of an ordinary decl's own fields ────────
//
// Same per-Decl-variant field coverage as
// [[lang/typecheck/name_subst.mo]]'s own `name_subst_decl` family
// (`Def`/`Inductive`/`Struct`/`Class`/`Instance`, their nested
// `Param`/`InductConstructor`/`StructField`/`ClassDef` shapes) — here
// applying `expand_term lookup` to each embedded `Term` field instead
// of substituting a name. `Decl.def_macro_d`/`decl_gen_d`/
// `macro_call_d` are handled separately by `expand_decls_go` itself
// (registry consumption / decl-position resolution), not here.

#[partial]
def param_terms_expand (lookup : Identifier -> Option Term) (p : Param) : Param :=
    match p {
        Param.mk name typ mult default attrs =>
            Param.mk name (expand_term lookup typ) mult (opt_term_expand lookup default) attrs,
    }

#[partial]
def params_terms_expand (lookup : Identifier -> Option Term) (params : List Param) : List Param :=
    match params {
        List.empty => List.empty,
        List.cons p rest => List.cons (param_terms_expand lookup p) (params_terms_expand lookup rest),
    }

#[partial]
def opt_term_expand (lookup : Identifier -> Option Term) (t : Option Term) : Option Term :=
    match t {
        Option.some x => Option.some (expand_term lookup x),
        Option.none => Option.none,
    }

#[partial]
def terms_expand (lookup : Identifier -> Option Term) (ts : List Term) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (expand_term lookup x) (terms_expand lookup rest),
    }

#[partial]
def induct_constructor_terms_expand (lookup : Identifier -> Option Term) (ctor : InductConstructor) : InductConstructor :=
    match ctor {
        InductConstructor.mk name params typ =>
            InductConstructor.mk name (params_terms_expand lookup params) (expand_term lookup typ),
    }

#[partial]
def induct_constructors_terms_expand (lookup : Identifier -> Option Term) (ctors : List InductConstructor) : List InductConstructor :=
    match ctors {
        List.empty => List.empty,
        List.cons c rest => List.cons (induct_constructor_terms_expand lookup c) (induct_constructors_terms_expand lookup rest),
    }

#[partial]
def struct_field_terms_expand (lookup : Identifier -> Option Term) (f : StructField) : StructField :=
    match f {
        StructField.mk name typ default mult =>
            StructField.mk name (expand_term lookup typ) (opt_term_expand lookup default) mult,
    }

#[partial]
def struct_fields_terms_expand (lookup : Identifier -> Option Term) (fields : List StructField) : List StructField :=
    match fields {
        List.empty => List.empty,
        List.cons f rest => List.cons (struct_field_terms_expand lookup f) (struct_fields_terms_expand lookup rest),
    }

#[partial]
def class_def_terms_expand (lookup : Identifier -> Option Term) (cd : ClassDef) : ClassDef :=
    match cd {
        ClassDef.mk name typ default => ClassDef.mk name (expand_term lookup typ) (opt_term_expand lookup default),
    }

#[partial]
def class_defs_terms_expand (lookup : Identifier -> Option Term) (cds : List ClassDef) : List ClassDef :=
    match cds {
        List.empty => List.empty,
        List.cons cd rest => List.cons (class_def_terms_expand lookup cd) (class_defs_terms_expand lookup rest),
    }

#[partial]
def def_terms_expand (lookup : Identifier -> Option Term) (d : Def) : Def :=
    match d {
        Def.mk name typ term constraints attrs vis =>
            Def.mk name (expand_term lookup typ) (expand_term lookup term) constraints attrs vis,
    }

#[partial]
def inductive_terms_expand (lookup : Identifier -> Option Term) (ind : Inductive) : Inductive :=
    match ind {
        Inductive.mk name params typ constructors attrs vis =>
            Inductive.mk name (params_terms_expand lookup params) (expand_term lookup typ)
                (induct_constructors_terms_expand lookup constructors) attrs vis,
    }

#[partial]
def struct_terms_expand (lookup : Identifier -> Option Term) (s : Struct) : Struct :=
    match s { Struct.mk name fields vis => Struct.mk name (struct_fields_terms_expand lookup fields) vis }

#[partial]
def class_terms_expand (lookup : Identifier -> Option Term) (cls : Class) : Class :=
    match cls {
        Class.mk name params constraints methods vis =>
            Class.mk name (params_terms_expand lookup params) constraints (class_defs_terms_expand lookup methods) vis,
    }

#[partial]
def instance_terms_expand (lookup : Identifier -> Option Term) (ins : Instance) : Instance :=
    match ins {
        Instance.mk name cls constraints args vis implicit_params defs =>
            Instance.mk name cls constraints (terms_expand lookup args) vis (params_terms_expand lookup implicit_params) (defs_terms_expand lookup defs),
    }

/// Expands every method Def in an instance's own body (`Instance.defs`)
/// -- mirrors `class_defs_terms_expand`'s identical role for
/// `Class.methods`, reusing the already-existing per-Def
/// `def_terms_expand`.
#[partial]
def defs_terms_expand (lookup : Identifier -> Option Term) (defs : List Def) : List Def :=
    match defs {
        List.empty => List.empty,
        List.cons d rest => List.cons (def_terms_expand lookup d) (defs_terms_expand lookup rest),
    }

/// Expand every `Term` field embedded in one ordinary (non-macro)
/// decl. `Decl.def_macro_d`/`decl_gen_d`/`macro_call_d` pass through
/// unchanged here — `expand_decls_go` never calls this on them (they
/// get their own, separate treatment: registry consumption or
/// decl-position resolution).
#[partial]
def expand_decl_terms (lookup : Identifier -> Option Term) (d : Decl) : Decl :=
    match d {
        Decl.def_d d_val => Decl.def_d (def_terms_expand lookup d_val),
        Decl.inductive_d ind => Decl.inductive_d (inductive_terms_expand lookup ind),
        Decl.struct_d s => Decl.struct_d (struct_terms_expand lookup s),
        Decl.class_d cls => Decl.class_d (class_terms_expand lookup cls),
        Decl.instance_d ins => Decl.instance_d (instance_terms_expand lookup ins),
        Decl.infix_d op path vis => Decl.infix_d op path vis,
        Decl.use_d path filter public => Decl.use_d path filter public,
        Decl.open_d path filter => Decl.open_d path filter,
        Decl.scoped_open_d path filter inner => Decl.scoped_open_d path filter (expand_decl_terms lookup inner),
        Decl.def_macro_d d_val => Decl.def_macro_d d_val,
        Decl.decl_gen_d name params gen_decls attrs => Decl.decl_gen_d name params gen_decls attrs,
        Decl.macro_call_d name args => Decl.macro_call_d name args,
    }

#[partial]
def expand_decls_terms_only (lookup : Identifier -> Option Term) (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest => List.cons (expand_decl_terms lookup d) (expand_decls_terms_only lookup rest),
    }

// ─── The work-queue itself ─────────────────────────────────────────

/// Entry point: expand every macro call (term- and decl-position) in
/// one module's own decl_list list. Registry is built from THIS list only
/// — cross-module macro imports (a macro `def_macro_d`/`decl_gen_d`
/// declared in a DIFFERENT, already-loaded module) are out of scope
/// for this single-pass version, matching the same scope-narrowing
/// this file's own doc comment already flags for nested decl-position
/// calls.
#[partial]
def expand_decls (decl_list : List Decl) : List Decl :=
    let term_registry : List TermMacroEntry := build_term_macro_registry decl_list in
    let decl_gen_registry : List DeclGenEntry := build_decl_gen_registry decl_list in
    let lookup : Identifier -> Option Term := fn id => lookup_term_macro term_registry id in
    expand_decls_go lookup decl_gen_registry decl_list

#[partial]
def expand_decls_go (lookup : Identifier -> Option Term) (decl_gen_registry : List DeclGenEntry) (decl_list : List Decl) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                // Macro DEFINITIONS -- already folded into the
                // registry built once at `expand_decls`'s own entry;
                // consumed, not part of the expanded output.
                Decl.def_macro_d _ => expand_decls_go lookup decl_gen_registry rest,
                // Retained in the output (unlike `def_macro_d` above) --
                // a decl-gen template may never be invoked within its
                // OWN file (e.g. every `defmacro derive_lens T := ...`
                // in `std/derive.mo` is only ever invoked from a
                // DIFFERENT, later-loaded file). Dropping it here would
                // make it permanently unresolvable once this file's own
                // per-file `expand_decls` pass has run -- a later,
                // whole-graph pass (`expand_decls_graph`) needs to still
                // see it. Still folded into `decl_gen_registry` for
                // same-file resolution, exactly as before.
                Decl.decl_gen_d name params gen_decls attrs =>
                    List.cons d (expand_decls_go lookup decl_gen_registry rest),
                Decl.macro_call_d name args =>
                    match lookup_decl_gen decl_gen_registry name {
                        Option.some entry =>
                            match entry {
                                DeclGenEntry.dg_entry _ params gen_decls =>
                                    match expand_decl_gen_call params gen_decls args {
                                        Option.some expanded =>
                                            List.append (expand_decls_terms_only lookup expanded) (expand_decls_go lookup decl_gen_registry rest),
                                        // Arity mismatch -- can't expand; leave the
                                        // call unresolved rather than silently
                                        // dropping it (a later pipeline-wiring pass
                                        // is the right place to turn this into a
                                        // real diagnostic).
                                        Option.none => List.cons d (expand_decls_go lookup decl_gen_registry rest),
                                    },
                            },
                        // Unregistered decl-position macro name -- NOT
                        // an error here either (mirrors expand_term's
                        // own "unresolved is not an error" rule).
                        Option.none => List.cons d (expand_decls_go lookup decl_gen_registry rest),
                    },
                _ => List.cons (expand_decl_terms lookup d) (expand_decls_go lookup decl_gen_registry rest),
            },
    }

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Decl` lists — same convention as the rest of this
// effort's `lang/typecheck/*.mo` tests, no pipeline wiring.

#[partial]
def term_type_level (t : Term) : I64 :=
    match t { Term.type_ u => u }

def empty_constraints : List TypeConstraint := List.empty
def empty_attrs : List Attribute := List.empty
def dummy_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "dummy") List.empty)

#[test]
def test_expand_decls_drops_term_macro_definitions : Bool :=
    // `defmacro double x := x` on its own -- consumed into the
    // registry, produces zero output decl_list.
    let double_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "double") List.empty) in
    let body : Term := Term.lam DebugName.unnamed Term.hole (Term.var 0 DebugName.unnamed) in
    let macro_def : Decl := Decl.def_macro_d (Def.mk double_name Term.hole body empty_constraints empty_attrs Visibility.package_private) in
    match expand_decls (List.cons macro_def List.empty) {
        List.empty => true,
        List.cons _ _ => false,
    }

#[test]
def test_expand_decls_expands_term_position_macro_call_inside_a_def : Bool :=
    // `defmacro double x := x` + `def y : Hole := double! 9` --
    // ordinary def's own `term` field gets its macro call resolved,
    // and the macro definition itself is dropped from the output.
    let double_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "double") List.empty) in
    let body : Term := Term.lam DebugName.unnamed Term.hole (Term.var 0 DebugName.unnamed) in
    let macro_def : Decl := Decl.def_macro_d (Def.mk double_name Term.hole body empty_constraints empty_attrs Visibility.package_private) in
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named (Identifier.id "double"))) (Term.type_ 9) in
    let y_def : Decl := Decl.def_d (Def.mk dummy_path Term.hole call empty_constraints empty_attrs Visibility.package_private) in
    match expand_decls (List.cons macro_def (List.cons y_def List.empty)) {
        List.cons only_decl rest =>
            (match rest { List.empty => true, List.cons _ _ => false }) &&
            match only_decl {
                Decl.def_d d_val =>
                    match d_val { Def.mk _ _ term _ _ _ => I64.beq (term_type_level term) 9 },
                _ => false,
            },
        List.empty => false,
    }

#[test]
def test_expand_decls_resolves_std_derive_shape_end_to_end : Bool :=
    // The real `std/derive.mo` shape, both decl_list together:
    // `defmacro derive_lens T := decls { reflect_type_info! T
    // derive_lens_meta }` followed by `derive_lens! Point` --
    // expands `derive_lens! Point` to the template's own
    // `reflect_type_info!` call with `T` substituted by `Point`. Unlike
    // before the cross-module decl-gen fix, the `decl_gen_d` DEFINITION
    // itself now SURVIVES this per-file pass (it may be invoked only
    // from a different, later-loaded file -- see `expand_decls_go`'s
    // own doc comment on the `decl_gen_d` arm) -- so the output is TWO
    // decls: the still-present template, then the resolved
    // `reflect_type_info!` call. Only the original `macro_call_d
    // "derive_lens"` invocation itself is gone, consumed into its
    // expansion.
    let lens_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "derive_lens") List.empty) in
    let t_param : Param := Param.mk (Identifier.id "T") Term.hole Multiplicity.many Option.none List.empty in
    let named_t : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "T")) in
    let meta_ref : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "derive_lens_meta")) in
    let template_decls : List Decl :=
        List.cons (Decl.macro_call_d (Identifier.id "reflect_type_info") (List.cons named_t (List.cons meta_ref List.empty))) List.empty in
    let gen_def : Decl := Decl.decl_gen_d lens_name (List.cons t_param List.empty) template_decls List.empty in
    let point_ref : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "Point")) in
    let invocation : Decl := Decl.macro_call_d (Identifier.id "derive_lens") (List.cons point_ref List.empty) in
    match expand_decls (List.cons gen_def (List.cons invocation List.empty)) {
        List.cons first_decl rest =>
            (match first_decl {
                Decl.decl_gen_d name _ _ _ =>
                    match module_path_last name {
                        Option.some id => id_eq id (Identifier.id "derive_lens"),
                        Option.none => false,
                    },
                _ => false,
            }) &&
            match rest {
                List.cons only_decl rest2 =>
                    (match rest2 { List.empty => true, List.cons _ _ => false }) &&
                    match only_decl {
                        Decl.macro_call_d call_name args =>
                            id_eq call_name (Identifier.id "reflect_type_info") &&
                            match args {
                                List.cons a1 rest_args =>
                                    (match a1 { Term.var _ dbg => match dbg { DebugName.named id => id_eq id (Identifier.id "Point"), DebugName.unnamed => false }, _ => false }) &&
                                    match rest_args {
                                        List.cons a2 _ =>
                                            match a2 { Term.var _ dbg => match dbg { DebugName.named id => id_eq id (Identifier.id "derive_lens_meta"), DebugName.unnamed => false }, _ => false },
                                        List.empty => false,
                                    },
                                List.empty => false,
                            },
                        _ => false,
                    },
                List.empty => false,
            },
        List.empty => false,
    }

#[test]
def test_expand_decls_leaves_unregistered_macro_call_unresolved : Bool :=
    // An unregistered decl-position macro call -- NOT an error,
    // passed through unresolved (mirrors expand_term's own rule).
    let call : Decl := Decl.macro_call_d (Identifier.id "totally_unknown") List.empty in
    match expand_decls (List.cons call List.empty) {
        List.cons only_decl rest =>
            (match rest { List.empty => true, List.cons _ _ => false }) &&
            match only_decl { Decl.macro_call_d name _ => id_eq name (Identifier.id "totally_unknown"), _ => false },
        List.empty => false,
    }

#[test]
def test_expand_decls_arity_mismatch_leaves_call_unresolved : Bool :=
    // `decl_gen_d` now survives its own file's `expand_decls` pass
    // (see the `decl_gen_d` arm's own doc comment) -- so the output is
    // TWO decls: the still-present template, then the still-unresolved
    // (arity-mismatched) `macro_call_d`.
    let gen_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "needs_one") List.empty) in
    let one_param : Param := Param.mk (Identifier.id "T") Term.hole Multiplicity.many Option.none List.empty in
    let gen_def : Decl := Decl.decl_gen_d gen_name (List.cons one_param List.empty) List.empty List.empty in
    let no_args : List Term := List.empty in
    let invocation : Decl := Decl.macro_call_d (Identifier.id "needs_one") no_args in
    match expand_decls (List.cons gen_def (List.cons invocation List.empty)) {
        List.cons first_decl rest =>
            (match first_decl { Decl.decl_gen_d _ _ _ _ => true, _ => false }) &&
            match rest {
                List.cons only_decl rest2 =>
                    (match rest2 { List.empty => true, List.cons _ _ => false }) &&
                    match only_decl { Decl.macro_call_d name _ => id_eq name (Identifier.id "needs_one"), _ => false },
                List.empty => false,
            },
        List.empty => false,
    }

#[test]
def test_expand_decls_ordinary_decl_with_no_macros_is_unchanged : Bool :=
    let ordinary : Decl := Decl.def_d (Def.mk dummy_path Term.hole (Term.type_ 4) empty_constraints empty_attrs Visibility.package_private) in
    match expand_decls (List.cons ordinary List.empty) {
        List.cons only_decl rest =>
            (match rest { List.empty => true, List.cons _ _ => false }) &&
            match only_decl {
                Decl.def_d d_val => match d_val { Def.mk _ _ term _ _ _ => I64.beq (term_type_level term) 4 },
                _ => false,
            },
        List.empty => false,
    }
