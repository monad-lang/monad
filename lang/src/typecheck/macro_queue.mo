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
use lib::types {
  AttrArg, Attribute, Class, ClassDef, Decl, Def, Identifier,
  InductConstructor, Inductive, Instance, ModulePath, Param, Struct,
  StructField, Term, TypeConstraint, id_eq, level_const, sentinel,
}
use lib::typecheck::macro_apply {expand_decl_gen_call}
use lib::typecheck::macro_expand {expand_term}

// ─── Registry ───────────────────────────────────────────────────────

type TermMacroEntry { tm_entry (name: Identifier) (body: Term) }
type DeclGenEntry { dg_entry (name: Identifier) (params: List Param) (decl_list: List Decl) }

/// A decl NAME's own last segment (`Def`/`DeclGenDef` names are
/// `NamePath`s since the qualified-names split) -- the bare name a
/// registry entry is keyed by.
#[partial]
def name_path_last (np : NamePath) : Option Identifier :=
    match np { NamePath.npath ids => List.last ids }

#[partial]
def build_term_macro_registry (decl_list : List Decl) : List TermMacroEntry :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_macro_d d_val =>
                    match d_val {
                        Def.mk {name, term, ..} =>
                            match name_path_last name {
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
                    match name_path_last name {
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
        Def.mk {name, typ, term, constraints, attrs, vis, params, ..} =>
            Def.mk name (expand_term lookup typ) (expand_term lookup term) constraints attrs vis params,
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
    match s { Struct.mk name fields attrs vis => Struct.mk name (struct_fields_terms_expand lookup fields) attrs vis }

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
        // `#![mote { ... }]` holds an `Attribute`, which contains no
        // `Term` at all, so there is nothing for this pass to rewrite --
        // but the arm is REQUIRED, not optional: this match has no
        // wildcard, so an unmatched `mote_d` is a runtime
        // `NonExhaustiveMatch`, and this pass runs over every decl of
        // every loaded module.
        Decl.mote_d attr => Decl.mote_d attr,
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
pub def expand_decls (decl_list : List Decl) : List Decl :=
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

// ─── Attribute → macro bridge (`#[derive ...]` / `#[derive_cli]`) ────
//
// Mirrors `core/src/eval/macro_expand.rs`'s `Decl::Type(induct)` arm: an
// attributed type declaration is not a macro CALL in the source at all,
// so nothing in `expand_decls_go` above would ever look at it — the
// attribute has to be read back off the decl and turned into the
// decl-gen macro call the user could have written by hand
// (`derive_beq! Point` for `#[derive BEq]`). Three pieces, in the
// reference's own order:
//
//   1. `derive_attribute_targets`'s equivalent — flatten a `derive`
//      attribute's own args (bare-word `#[derive BEq BOrd]` and the
//      bracketed-group `#[derive [BEq, BOrd]]` both parse, so both are
//      accepted here too) into target names, and map each through
//      `derive_macro_name` (`BEq` -> `derive_beq`, …); plus the
//      independently-named `#[derive_cli]` -> `derive_cli`.
//   2. Synthesize the macro call exactly as `named_ref` shapes a
//      type-name argument (`lang/typecheck/name_subst.mo`), then run it
//      through the SAME registry lookup/template substitution a written
//      `derive_beq! Point` goes through.
//   3. The type decl itself is emitted UNCHANGED and its attributes are
//      left in place (the reference's own choice — it pushes the type
//      straight to `batch` and only avoids regenerating by never
//      re-queueing it). Safe here for the same structural reason: this
//      bridge lives in `lang/module.mo`'s `decl_gen_subst_decls`, which
//      `expand_decls_graph` runs exactly ONCE per elaboration, and the
//      per-file `expand_decls` above deliberately does NOT bridge — so
//      there is no second pass to regenerate from the still-present
//      attribute. Putting it in `expand_decls_go` as well WOULD double
//      every generated instance (parse-time pass, then graph pass).
//
// Not carried over from the reference: its hard error on an unknown
// `#[derive Foo]` target. An unregistered macro name is not an error
// anywhere else in this file (`expand_decls_go`'s own "unresolved is
// not an error" rule), and `derive_macro_name` is a total four-way map,
// so an unknown target simply contributes nothing — the same silent
// shape `#[derive]`-on-a-multi-constructor-type's `derive_lens` already
// has.

/// `#[derive ...]` target name -> the `std/derive.mo` decl-gen macro
/// that implements it, verbatim from the reference's own
/// `derive_macro_name`. `Option.none` for anything else (including a
/// correctly-spelled target this build has no macro for).
pub def derive_macro_name (target : Identifier) : Option Identifier :=
    if id_eq target (Identifier.id "BEq") then Option.some (Identifier.id "derive_beq")
    else if id_eq target (Identifier.id "BOrd") then Option.some (Identifier.id "derive_bord")
    else if id_eq target (Identifier.id "Debug") then Option.some (Identifier.id "derive_debug")
    else if id_eq target (Identifier.id "Lens") then Option.some (Identifier.id "derive_lens")
    else Option.none

/// One `#[derive ...]` attribute's own args -> its target names.
/// `AttrArg.group` recurses (the bracketed form); every other arg kind
/// (`str`/`num`/`named`) is not a target name and contributes nothing —
/// the reference errors on those instead, see this section's own note.
#[partial]
def derive_targets_of_args (args : List AttrArg) : List Identifier :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            match a {
                AttrArg.ident id => List.cons id (derive_targets_of_args rest),
                AttrArg.group items => List.append (derive_targets_of_args items) (derive_targets_of_args rest),
                _ => derive_targets_of_args rest,
            },
    }

/// Target names -> macro names, dropping the unknown ones.
#[partial]
def derive_macro_names_of_targets (targets : List Identifier) : List Identifier :=
    match targets {
        List.empty => List.empty,
        List.cons t rest =>
            match derive_macro_name t {
                Option.some m => List.cons m (derive_macro_names_of_targets rest),
                Option.none => derive_macro_names_of_targets rest,
            },
    }

/// One attribute -> the macros it asks for. `derive` goes through the
/// target map above; `derive_cli` IS its own macro name (the reference
/// hard-codes the same pair); anything else asks for nothing.
#[partial]
def derive_macro_names_of_attr (attr : Attribute) : List Identifier :=
    match attr {
        Attribute.mk name args =>
            if id_eq name (Identifier.id "derive") then derive_macro_names_of_targets (derive_targets_of_args args)
            else if id_eq name (Identifier.id "derive_cli") then List.cons (Identifier.id "derive_cli") List.empty
            else List.empty,
    }

#[partial]
def derive_macro_names_of_attrs (attrs : List Attribute) : List Identifier :=
    match attrs {
        List.empty => List.empty,
        List.cons a rest => List.append (derive_macro_names_of_attr a) (derive_macro_names_of_attrs rest),
    }

/// The attributes an attributed TYPE declaration carries — the two decl
/// shapes the reference's `Decl::Type` arm covers. NOTE the self-hosted
/// split the reference doesn't have: `struct` is its OWN `Decl` variant
/// here, where the reference represents both as one `Inductive` with
/// `variant: Struct` (`core/src/term.rs`), which is why `#[derive ...]`
/// on a `struct` needs a parser change (`ParseStruct`/`Struct`'s own
/// `attrs` slot) as well as this bridge.
pub def decl_type_attrs (d : Decl) : List Attribute :=
    match d {
        Decl.struct_d s => match s { Struct.mk _ _ attrs _ => attrs },
        Decl.inductive_d ind => match ind { Inductive.mk _ _ _ _ attrs _ => attrs },
        _ => List.empty,
    }

/// Every macro name an attributed type declaration asks for.
pub def decl_derive_macro_names (d : Decl) : List Identifier :=
    derive_macro_names_of_attrs (decl_type_attrs d)

/// Whether any macro name in the list is registered.
#[partial]
def macro_names_registered (registry : List DeclGenEntry) (names : List Identifier) : Bool :=
    match names {
        List.empty => false,
        List.cons n rest =>
            match lookup_decl_gen registry n {
                Option.some _ => true,
                Option.none => macro_names_registered registry rest,
            },
    }

/// Whether `d` is an attributed type declaration whose derive would
/// actually EXPAND — i.e. at least one of its macro names is in the
/// registry. The registry-dependence is what keeps the flag honest: an
/// `#[derive BEq]` in a file that never brings `derive_beq` into the
/// graph generates nothing, so it must not count as a graph change
/// (`lang/module.mo`'s `raw_changed`/`changed` consumers would otherwise
/// splice an unexpanded `macro_call_d` into the codegen decl list).
pub def decl_derive_expands (registry : List DeclGenEntry) (d : Decl) : Bool :=
    macro_names_registered registry (decl_derive_macro_names d)

#[partial]
pub def has_derive_expansion (registry : List DeclGenEntry) (decls : List Decl) : Bool :=
    match decls {
        List.empty => false,
        List.cons d rest => if decl_derive_expands registry d then true else has_derive_expansion registry rest,
    }

/// The `Term` a synthesized macro call passes as its type argument —
/// the free (sentinel-indexed, `DebugName.named`) variable reference
/// `lang/typecheck/name_subst.mo`'s own `named_ref` builds, and the
/// shape `lang/module.mo`'s `term_free_var_name` reads the type's bare
/// name back out of.
pub def derive_name_ref (id : Identifier) : Term := Term.var (0 - 1) (DebugName.named id)

/// One synthesized `derive_*! <T>` call -> its expansion, via the same
/// registry lookup + `expand_decl_gen_call` template substitution
/// `expand_decls_go` gives a written call. An unregistered name (or an
/// arity mismatch) yields `List.empty` rather than a leftover
/// `macro_call_d` — unlike a written call, this one was never in the
/// source, so there is nothing to preserve on failure.
#[partial]
def derive_bridge_one (registry : List DeclGenEntry) (name : Identifier) (arg : Term) : List Decl :=
    match lookup_decl_gen registry name {
        Option.some entry =>
            match entry {
                DeclGenEntry.dg_entry _ params gen_decls =>
                    match expand_decl_gen_call params gen_decls (List.cons arg List.empty) {
                        Option.some expanded => expanded,
                        Option.none => List.empty,
                    },
            },
        Option.none => List.empty,
    }

#[partial]
def derive_bridge_names (registry : List DeclGenEntry) (arg : Term) (names : List Identifier) : List Decl :=
    match names {
        List.empty => List.empty,
        List.cons n rest => List.append (derive_bridge_one registry n arg) (derive_bridge_names registry arg rest),
    }

/// The decls an attributed type declaration generates — empty for every
/// other decl kind, and for an attributed type whose derive macros this
/// graph doesn't have. The type decl itself is NOT part of the result;
/// its own list already carries it (`lang/module.mo`'s
/// `decl_gen_subst_decls` appends these right after it).
#[partial]
pub def derive_bridge_decls (registry : List DeclGenEntry) (d : Decl) : List Decl :=
    match d {
        Decl.struct_d s =>
            match s {
                Struct.mk name _fields attrs _vis =>
                    derive_bridge_names registry (derive_name_ref name) (derive_macro_names_of_attrs attrs),
            },
        Decl.inductive_d ind =>
            match ind {
                Inductive.mk name _params _typ _cons attrs _vis =>
                    match name_path_last name {
                        Option.some id => derive_bridge_names registry (derive_name_ref id) (derive_macro_names_of_attrs attrs),
                        Option.none => List.empty,
                    },
            },
        _ => List.empty,
    }

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Decl` lists — same convention as the rest of this
// effort's `lang/typecheck/*.mo` tests, no pipeline wiring.

#[partial]
def term_type_level (t : Term) : I64 :=
    match t {
        // A sort with an unresolved level (a `var`, or a `succ`/`max` over
        // one) has no I64 to report, so it answers the free-variable
        // sentinel rather than a guessed level.
        Term.sort l => match level_const l {
            Option.some n => n,
            Option.none => sentinel,
        },
    }

def empty_constraints : List TypeConstraint := List.empty
def dummy_path : NamePath := NamePath.npath (List.cons (Identifier.id "dummy") List.empty)

#[test]
def test_expand_decls_drops_term_macro_definitions : Bool :=
    // `defmacro double x := x` on its own -- consumed into the
    // registry, produces zero output decl_list.
    let double_name : NamePath := NamePath.npath (List.cons (Identifier.id "double") List.empty) in
    let body : Term := Term.lam DebugName.unnamed Term.hole (Term.var 0 DebugName.unnamed) in
    let macro_def : Decl := Decl.def_macro_d (Def.mk double_name Term.hole body empty_constraints empty_attrs Visibility.package_private List.empty) in
    match expand_decls (List.cons macro_def List.empty) {
        List.empty => true,
        List.cons _ _ => false,
    }

#[test]
def test_expand_decls_expands_term_position_macro_call_inside_a_def : Bool :=
    // `defmacro double x := x` + `def y : Hole := double! 9` --
    // ordinary def's own `term` field gets its macro call resolved,
    // and the macro definition itself is dropped from the output.
    let double_name : NamePath := NamePath.npath (List.cons (Identifier.id "double") List.empty) in
    let body : Term := Term.lam DebugName.unnamed Term.hole (Term.var 0 DebugName.unnamed) in
    let macro_def : Decl := Decl.def_macro_d (Def.mk double_name Term.hole body empty_constraints empty_attrs Visibility.package_private List.empty) in
    let call : Term := Term.app (Term.var_macro (0 - 1) (DebugName.named (Identifier.id "double"))) (Term.sort (SortLevel.concrete 9)) in
    let y_def : Decl := Decl.def_d (Def.mk dummy_path Term.hole call empty_constraints empty_attrs Visibility.package_private List.empty) in
    match expand_decls (List.cons macro_def (List.cons y_def List.empty)) {
        List.cons only_decl rest =>
            (match rest { List.empty => true, List.cons _ _ => false }) &&
            match only_decl {
                Decl.def_d d_val =>
                    match d_val { Def.mk {term, ..} => I64.beq (term_type_level term) 9 },
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
    let lens_name : NamePath := NamePath.npath (List.cons (Identifier.id "derive_lens") List.empty) in
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
                    match name_path_last name {
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
    let gen_name : NamePath := NamePath.npath (List.cons (Identifier.id "needs_one") List.empty) in
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
    let ordinary : Decl := Decl.def_d (Def.mk dummy_path Term.hole (Term.sort (SortLevel.concrete 4)) empty_constraints empty_attrs Visibility.package_private List.empty) in
    match expand_decls (List.cons ordinary List.empty) {
        List.cons only_decl rest =>
            (match rest { List.empty => true, List.cons _ _ => false }) &&
            match only_decl {
                Decl.def_d d_val => match d_val { Def.mk {term, ..} => I64.beq (term_type_level term) 4 },
                _ => false,
            },
        List.empty => false,
    }

// ─── Attribute → macro bridge ───────────────────────────────────────

/// The `derive_*! <T>` template shape `std/derive.mo` really has, minus
/// the other three: one param `T`, one `reflect_type_info! T <meta>`
/// call. `meta` is named after the macro so `bridge_call_arg_name`'s own
/// assertions can also tell the templates apart by their meta-def.
def bridge_template (macro_name : String) : Decl :=
    let t_param : Param := Param.mk (Identifier.id "T") Term.hole Multiplicity.many Option.none List.empty in
    let own_name : NamePath := NamePath.npath (List.cons (Identifier.id macro_name) List.empty) in
    let meta_name : String := String.concat macro_name "_meta" in
    let body : Decl :=
        Decl.macro_call_d (Identifier.id "reflect_type_info")
            (List.cons (derive_name_ref (Identifier.id "T")) (List.cons (derive_name_ref (Identifier.id meta_name)) List.empty)) in
    Decl.decl_gen_d own_name (List.cons t_param List.empty) (List.cons body List.empty) List.empty

/// `#[derive BEq BOrd]` -- the bare-word form (one attribute, two
/// positional ident args), the form `examples/derive.mo` writes.
def bridge_derive_attr : Attribute :=
    Attribute.mk (Identifier.id "derive")
        (List.cons (AttrArg.ident (Identifier.id "BEq")) (List.cons (AttrArg.ident (Identifier.id "BOrd")) List.empty))

/// `#[derive [Debug, Lens]]` -- the bracketed-group form, which
/// `attr_arg_parser` also accepts (the reference accepts both).
def bridge_derive_group_attr : Attribute :=
    Attribute.mk (Identifier.id "derive")
        (List.cons (AttrArg.group
            (List.cons (AttrArg.ident (Identifier.id "Debug")) (List.cons (AttrArg.ident (Identifier.id "Lens")) List.empty)))
            List.empty)

def bridge_struct (attrs : List Attribute) : Decl :=
    let fld : StructField := StructField.mk (Identifier.id "x") (Term.sort (SortLevel.concrete 0)) Option.none Multiplicity.many in
    Decl.struct_d (Struct.mk (Identifier.id "Point") (List.cons fld List.empty) attrs Visibility.package_private)

/// The type-name argument of a bridge result's first generated call —
/// what `lang/module.mo`'s `term_free_var_name` reads back out to name
/// the reflected type.
#[partial]
def bridge_call_arg_name (ds : List Decl) : Option String :=
    match ds {
        List.empty => Option.none,
        List.cons d _ =>
            match d {
                Decl.macro_call_d _ args =>
                    match args {
                        List.cons a _ =>
                            match a {
                                Term.var _ dbg =>
                                    match dbg {
                                        DebugName.named id => Option.some (show_identifier id),
                                        DebugName.unnamed => Option.none,
                                    },
                                _ => Option.none,
                            },
                        List.empty => Option.none,
                    },
                _ => Option.none,
            },
    }

/// The meta-def name a bridge result's own generated `reflect_type_info!`
/// call names — the second argument, i.e. which of the four `derive_*`
/// macros actually produced it.
#[partial]
def bridge_call_meta_name (d : Decl) : Option String :=
    match d {
        Decl.macro_call_d name args =>
            if id_eq name (Identifier.id "reflect_type_info") then
                match args {
                    List.cons _ rest =>
                        match rest {
                            List.cons m _ =>
                                match m {
                                    Term.var _ dbg =>
                                        match dbg {
                                            DebugName.named id => Option.some (show_identifier id),
                                            DebugName.unnamed => Option.none,
                                        },
                                    _ => Option.none,
                                },
                            List.empty => Option.none,
                        },
                    List.empty => Option.none,
                }
            else Option.none,
        _ => Option.none,
    }

#[test]
def test_derive_macro_name_maps_the_four_real_targets : Bool :=
    (match derive_macro_name (Identifier.id "BEq") { Option.some m => String.beq (show_identifier m) "derive_beq", Option.none => false }) &&
    (match derive_macro_name (Identifier.id "BOrd") { Option.some m => String.beq (show_identifier m) "derive_bord", Option.none => false }) &&
    (match derive_macro_name (Identifier.id "Debug") { Option.some m => String.beq (show_identifier m) "derive_debug", Option.none => false }) &&
    (match derive_macro_name (Identifier.id "Lens") { Option.some m => String.beq (show_identifier m) "derive_lens", Option.none => false }) &&
    // Case-sensitive, like the reference's own `match`: `beq`/`LENS` are
    // not targets.
    (match derive_macro_name (Identifier.id "beq") { Option.some _ => false, Option.none => true })

#[test]
def test_derive_bridge_bare_word_form_generates_one_call_per_target : Bool :=
    // `#[derive BEq BOrd] struct Point {...}` with both macros in the
    // registry -> two generated decls, each a `reflect_type_info!` call
    // naming `Point`, in attribute order.
    let a : Decl := bridge_template "derive_beq" in
    let b : Decl := bridge_template "derive_bord" in
    let registry : List DeclGenEntry := build_decl_gen_registry (List.cons a (List.cons b List.empty)) in
    let generated : List Decl := derive_bridge_decls registry (bridge_struct (List.cons bridge_derive_attr List.empty)) in
    I64.beq (List.length generated) 2 &&
    match bridge_call_arg_name generated {
        Option.some n => String.beq n "Point",
        Option.none => false,
    } &&
    match generated {
        List.cons first rest =>
            (match bridge_call_meta_name first { Option.some m => String.beq m "derive_beq_meta", Option.none => false }) &&
            match rest {
                List.cons second _ =>
                    match bridge_call_meta_name second { Option.some m => String.beq m "derive_bord_meta", Option.none => false },
                List.empty => false,
            },
        List.empty => false,
    }

#[test]
def test_derive_bridge_group_form_flattens : Bool :=
    // `#[derive [Debug, Lens]]` -- one `AttrArg.group` of two idents,
    // same two generated decls as the bare-word form.
    let a : Decl := bridge_template "derive_debug" in
    let b : Decl := bridge_template "derive_lens" in
    let registry : List DeclGenEntry := build_decl_gen_registry (List.cons a (List.cons b List.empty)) in
    let generated : List Decl := derive_bridge_decls registry (bridge_struct (List.cons bridge_derive_group_attr List.empty)) in
    I64.beq (List.length generated) 2 &&
    match generated {
        List.cons first _ =>
            match bridge_call_meta_name first { Option.some m => String.beq m "derive_debug_meta", Option.none => false },
        List.empty => false,
    }

#[test]
def test_derive_bridge_derive_cli_needs_no_target_args : Bool :=
    // `#[derive_cli]` IS its own macro name -- no target mapping, and no
    // args on the attribute at all.
    let tmpl : Decl := bridge_template "derive_cli" in
    let registry : List DeclGenEntry := build_decl_gen_registry (List.cons tmpl List.empty) in
    let attr : Attribute := Attribute.mk (Identifier.id "derive_cli") List.empty in
    let generated : List Decl := derive_bridge_decls registry (bridge_struct (List.cons attr List.empty)) in
    I64.beq (List.length generated) 1 &&
    match bridge_call_arg_name generated { Option.some n => String.beq n "Point", Option.none => false }

#[test]
def test_derive_bridge_ignores_unregistered_and_unknown : Bool :=
    // Two independent "generates nothing" cases: a target with no
    // `derive_macro_name` at all (`Clone`), and a real target whose
    // macro this graph does not have (`BEq` with an empty registry).
    // The second is why `decl_derive_expands` is registry-dependent --
    // an unexpandable attribute must not count as a graph change.
    let clone_attr : Attribute := Attribute.mk (Identifier.id "derive") (List.cons (AttrArg.ident (Identifier.id "Clone")) List.empty) in
    let clone_decl : Decl := bridge_struct (List.cons clone_attr List.empty) in
    let beq_decl : Decl := bridge_struct (List.cons bridge_derive_attr List.empty) in
    let tmpl : Decl := bridge_template "derive_beq" in
    let with_beq : List DeclGenEntry := build_decl_gen_registry (List.cons tmpl List.empty) in
    I64.beq (List.length (derive_bridge_decls with_beq clone_decl)) 0 &&
    I64.beq (List.length (derive_bridge_decls List.empty beq_decl)) 0 &&
    not (decl_derive_expands List.empty beq_decl) &&
    decl_derive_expands with_beq beq_decl

#[test]
def test_derive_bridge_ignores_unattributed_and_non_type_decls : Bool :=
    // The common case by a wide margin: an ordinary undecorated struct,
    // and an attributed `def` (whose attrs are `#[test]`/`#[arg]`-class,
    // not type-level) both generate nothing.
    let plain : Decl := bridge_struct List.empty in
    let d : Decl := Decl.def_d (Def.mk dummy_path Term.hole (Term.sort (SortLevel.concrete 1)) empty_constraints (List.cons bridge_derive_attr List.empty) Visibility.package_private List.empty) in
    I64.beq (List.length (derive_bridge_decls List.empty plain)) 0 &&
    I64.beq (List.length (derive_bridge_decls List.empty d)) 0 &&
    not (has_derive_expansion List.empty (List.cons plain (List.cons d List.empty)))

#[test]
def test_decl_type_attrs_reads_struct_and_inductive_only : Bool :=
    // The two decl shapes the reference's `Decl::Type` arm covers --
    // and note the self-hosted split: a `struct` is its OWN variant here
    // (`Struct`'s own `attrs` slot is what `#[derive ...] struct` needs
    // on top of the `Inductive` one that `#[derive_cli] type` uses).
    let attr : Attribute := Attribute.mk (Identifier.id "derive_cli") List.empty in
    let struct_decl : Decl := bridge_struct (List.cons attr List.empty) in
    let ind : Inductive := Inductive.mk (NamePath.npath (List.cons (Identifier.id "Cmd") List.empty)) List.empty Term.hole List.empty (List.cons attr List.empty) Visibility.package_private in
    let def_decl : Decl := Decl.def_d (Def.mk dummy_path Term.hole (Term.sort (SortLevel.concrete 1)) empty_constraints List.empty Visibility.package_private List.empty) in
    I64.beq (List.length (decl_type_attrs struct_decl)) 1 &&
    I64.beq (List.length (decl_type_attrs (Decl.inductive_d ind))) 1 &&
    I64.beq (List.length (decl_type_attrs def_decl)) 0 &&
    I64.beq (List.length (decl_derive_macro_names (Decl.inductive_d ind))) 1
