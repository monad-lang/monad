/// `ParseTerm` -> `Term`: de Bruijn resolution, as its own pass.
///
/// Fully wired: `lang/parser.mo` builds `ParseDecl`/`ParseTerm`
/// throughout and lowers here at its three entry points
/// (`decls_parser`, `decls_parser_strict`, `decls_parser_with_locs`).
/// Nothing outside `lang/parser*` ever sees a `Parse*` type.
///
/// This is the stage the compiler did not have. The parser used to
/// resolve variables inline -- `var_term`/`find_index` against a
/// `ctx : List Identifier` threaded through ~235 of its defs -- which is
/// why there was nowhere to hang a source position and why
/// `Literal.struct_update`'s own doc comment records that "this checker
/// has no separate parse-then-lower stage the way the reference's
/// `Literal` (pre-lowering) vs `CoreLit` (post-lowering) split does".
///
/// The grammar now produces named, located `ParseTerm`s and this module
/// turns them into canonical de Bruijn `Term`s. The binder structure the
/// parser used to track by hand is recovered here from the tree itself:
/// `lam`/`forall`/`pi` and match arms say what they bind, so `ctx` is
/// threaded through this pass instead -- one place rather than the whole
/// grammar.
///
/// Name resolution lives HERE: `find_index`, `show_module_path_dotted`,
/// `name_ref_to_string` and `field_access_chain` are DEFINED in this
/// module, and `lang/parser.mo` imports `name_ref_to_string` back rather
/// than keeping the byte-identical copy it used to carry beside that
/// import -- two definitions of one bare LLVM symbol, the shape
/// `validate_no_colliding_def_symbols` (`lang/codegen/validate.mo`) now
/// rejects and AGENTS.md item 18 describes.
///
/// `sentinel` is the exception: it belongs to `Term`'s representation
/// rather than to this pass, so `lang/types.mo` owns it and both modules
/// import it from there.
///
/// `show_module_path_dotted` still duplicates `lang/parser.mo`'s
/// `module_path_to_string` body under a different name. Not a symbol
/// collision, so it is left alone here; unifying them means deciding
/// which module owns dotted-path rendering, which is a separate change.
use lang.types {
  Class, ClassDef, Con, DebugName, Decl, Def, DoStmt, Identifier,
  InductConstructor, Inductive, Instance, Literal, MatchCase, ModulePath,
  NameRef, Native, Param, ParseClass, ParseClassDef, ParseCon, ParseDecl,
  ParseDeclKind, ParseDef, ParseDoStmt, ParseInductConstructor, ParseInductive,
  ParseInstance, ParseLiteral, ParseMatchCase, ParseNative, ParseParam,
  ParseStruct, ParseStructField, ParseStructLitField, ParseTerm, ParseTermKind,
  Struct, StructField, StructLitField, Term, desugar_do, sentinel,
}
// Name resolution lives HERE now, moved out of `lang/parser.mo` for real
// (an earlier revision copied it while claiming to have moved it, arming
// the duplicate-top-level-name collision item 18 records). The grammar no
// longer resolves names at all, so nothing flows the other way: it
// imports `lower_parse_do` from here and that is the only edge.
use lang.types {FieldPattern, FieldPatternEntry, show_operator}


/// Extend `ctx` with a binder group. Each name is consed in order, so the
/// LAST-declared name ends up at `ctx`'s head (de Bruijn index 0) -- the
/// "reversed = innermost first" convention the grammar's own
/// `lambda_extend_ctx` established and every index here depends on.
#[partial]
def extend_ctx (names : List Identifier) (ctx : List Identifier) : List Identifier :=
    match names {
        List.cons n rest => extend_ctx rest (List.cons n ctx),
        List.empty => ctx,
    }


/// Resolve a written name against the binders in scope.
///
/// A dotted path is ambiguous at parse time between a module-qualified
/// global and a local struct-field access, and the parser has no scope
/// information to tell them apart -- so it always builds a path and the
/// ambiguity is settled HERE, where `ctx` is known: if the first segment
/// is a local binding, the rest of the path is a field-access chain
/// (mirroring the Rust reference's `lower_core.rs::lower_var`'s
/// `NameRef::P` arm). Otherwise the whole dotted name is kept intact for
/// the module resolver.
#[partial]
def lower_name_ref (ctx : List Identifier) (nref : NameRef) : Term :=
    match nref {
        // `find_index` directly rather than `var_term`, which only takes
        // a `String` to re-wrap it as an `Identifier` immediately -- and
        // that round trip is what tripped whole-corpus resolution.
        NameRef.nid id =>
            match find_index id ctx 0 {
                Option.some idx => Term.var idx (DebugName.named id),
                Option.none => Term.var sentinel (DebugName.named id),
            },
        NameRef.nmp mp => lower_path ctx mp nref,
        NameRef.nop _ => lower_name_global nref,
    }


#[partial]
def lower_path (ctx : List Identifier) (mp : ModulePath) (nref : NameRef) : Term :=
    match mp {
        ModulePath.mp ids => lower_path_ids ctx ids nref,
    }


#[partial]
def lower_path_ids (ctx : List Identifier) (ids : List Identifier) (nref : NameRef) : Term :=
    match ids {
        List.cons first fields =>
            match find_index first ctx 0 {
                Option.some idx =>
                    field_access_chain (Term.var idx (DebugName.named first)) fields,
                Option.none => lower_name_global nref,
            },
        List.empty => lower_name_global nref,
    }


/// An unbound name keeps its full qualified spelling -- downstream
/// resolution (`is_constructor_var` and the module resolver) extracts the
/// base name when it needs to.
#[partial]
def lower_name_global (nref : NameRef) : Term :=
    match name_ref_to_string nref {
        Option.some qualified => Term.var sentinel (DebugName.named (Identifier.id qualified)),
        Option.none => Term.var sentinel DebugName.unnamed,
    }


// --- Name resolution -------------------------------------------------
//
// `sentinel` (the free/unresolved de Bruijn index this pass emits for a
// name bound by no enclosing binder) is IMPORTED from `lang.types`, not
// declared here: codegen mangles a top-level def to its bare name, so a
// second `def sentinel` would be a second definition of the LLVM symbol
// `@sentinel` -- the shape `validate_no_colliding_def_symbols`
// (`lang/codegen/validate.mo`) now rejects outright.

#[partial]
def find_index (id: Identifier) (ctx: List Identifier) (depth: I64) : Option I64 :=
    match ctx {
        List.cons x rest =>
            if String.beq (show_identifier id) (show_identifier x)
            then Option.some depth
            else find_index id rest (depth + 1),
        List.empty => Option.none
    }


#[partial]
def show_module_path_dotted (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => List.intercalate "." (List.map show_identifier ids),
}


/// Faithful to `lang/parser.mo`'s original, INCLUDING the `nop` arm: an
/// operator keeps its spelling, because `resolve_infix_decls`
/// (`lang/scope.mo`) rewrites placeholder operator vars into their real
/// targets by that name. An earlier copy of this returned `Option.none`
/// there and would have silently discarded it.
#[partial]
def name_ref_to_string (nref : NameRef) : Option String := match nref {
    NameRef.nid id => Option.some (show_identifier id),
    NameRef.nmp mp => Option.some (show_module_path_dotted mp),
    NameRef.nop op => Option.some (show_operator op),
}


/// Nested bare-form field-pattern `Match` chain desugaring a dotted-path
/// field access into ordinary struct-field destructuring -- mirrors the
/// Rust reference's `lower_core.rs::lower_field_access_chain`.
///
/// The binder list is `[field]` inline rather than via
/// `field_pattern_binder_names`: the pattern built here has exactly one
/// entry whose binder IS `field`, so calling that helper would only add a
/// dependency back on `lang/parser.mo`, which is the edge this module
/// exists without.
#[partial]
def field_access_chain (scrutinee : Term) (fields : List Identifier) : Term :=
    match fields {
        List.empty => scrutinee,
        List.cons field rest =>
            let value : Term := field_access_chain (Term.var 0 (DebugName.named field)) rest in
            let entry : FieldPatternEntry := FieldPatternEntry.mk field field in
            let fp : FieldPattern := FieldPattern.mk (List.cons entry List.empty) true in
            let binders : List Identifier := List.cons field List.empty in
            let case_ : MatchCase := MatchCase.mc (Identifier.id "") binders value (Option.some fp) in
            Term.lit (Literal.match_ scrutinee (List.cons case_ List.empty)),
    }


// --- The lowering itself --------------------------------------------

#[partial]
def lower_parse_term (ctx : List Identifier) (pt : ParseTerm) : Term :=
    lower_parse_kind ctx pt.kind


#[partial]
def lower_parse_kind (ctx : List Identifier) (k : ParseTermKind) : Term :=
    match k {
        ParseTermKind.var nref => lower_name_ref ctx nref,
        // A macro name resolves in its own namespace at expansion time,
        // never by de Bruijn lookup -- see `Term.var_macro`'s doc comment.
        ParseTermKind.var_macro nref =>
            match name_ref_to_string nref {
                Option.some qualified =>
                    Term.var_macro sentinel (DebugName.named (Identifier.id qualified)),
                Option.none => Term.var_macro sentinel DebugName.unnamed,
            },
        // `lam`/`forall`/`pi` bind over their BODY only, never over their
        // own type/argument -- the type is lowered in the OUTER ctx.
        ParseTermKind.lam name typ body =>
            Term.lam (DebugName.named name)
                     (lower_parse_term ctx typ)
                     (lower_parse_term (List.cons name ctx) body),
        ParseTermKind.forall name typ body =>
            Term.forall (DebugName.named name)
                        (lower_parse_term ctx typ)
                        (lower_parse_term (List.cons name ctx) body),
        // `pi` does NOT extend `ctx` here, deliberately, because the
        // grammar it replaces does not: `build_pi_chain`/
        // `build_param_pi_chain` (`lang/parser.mo`) fold a "non-dependent
        // Pi chain" (their own words) with the return type at the SAME
        // depth as the argument. Note this disagrees with
        // `lang/typecheck/traverse.mo`, whose depth-aware walker treats
        // `Term.pi`'s `ret` as sitting under one binder (`f 1 ret`) --
        // a real pre-existing inconsistency between producer and
        // consumer. Matching the PRODUCER is what preserves behaviour;
        // extending `ctx` here would shift every free index in a return
        // type by one. Left as-is rather than silently changed: it is a
        // separate question from this refactor.
        ParseTermKind.pi arg ret =>
            Term.pi (lower_parse_term ctx arg) (lower_parse_term ctx ret),
        // `pi_dep` is the ONE arrow that binds: `(n : T) -> body` puts `n`
        // in scope over `body`, which is what `type_dep_arrow_tag`
        // (`lang/parser.mo`) used to do inline before the grammar stopped
        // resolving names. `Term.pi` has no field to carry `n`, so if the
        // name is not consumed HERE it is lost -- every use of `n` inside
        // `body` resolves to `sentinel` and becomes an unbound global.
        // Caught by review after exactly that regression shipped in this
        // branch; `test_dep_pi_binds_its_own_name` pins it.
        ParseTermKind.pi_dep name arg ret =>
            Term.pi (lower_parse_term ctx arg)
                    (lower_parse_term (List.cons name ctx) ret),
        ParseTermKind.app f a =>
            Term.app (lower_parse_term ctx f) (lower_parse_term ctx a),
        ParseTermKind.lit l => Term.lit (lower_parse_literal ctx l),
        ParseTermKind.ntv n => Term.ntv (lower_parse_native ctx n),
        ParseTermKind.con c => Term.con (lower_parse_con ctx c),
        ParseTermKind.type_ u => Term.type_ u,
        ParseTermKind.quote_ inner => Term.quote_ (lower_parse_term ctx inner),
        // Desugared HERE, not in the grammar -- this is the whole reason
        // the parse stage can drop `ctx`.
        ParseTermKind.do_ stmts => lower_parse_do ctx stmts,
        ParseTermKind.hole => Term.hole,
    }


#[partial]
def lower_parse_literal (ctx : List Identifier) (l : ParseLiteral) : Literal :=
    match l {
        ParseLiteral.str v => Literal.str v,
        ParseLiteral.num n suf => Literal.num n suf,
        ParseLiteral.flt t suf => Literal.flt t suf,
        ParseLiteral.if_ a b c =>
            Literal.if_ (lower_parse_term ctx a)
                        (lower_parse_term ctx b)
                        (lower_parse_term ctx c),
        // The scrutinee is OUTSIDE every arm's bindings; each arm's body
        // is inside its own.
        ParseLiteral.match_ scrut cases =>
            Literal.match_ (lower_parse_term ctx scrut)
                           (lower_parse_match_cases ctx cases),
        ParseLiteral.struct_lit fields type_name =>
            Literal.struct_lit (lower_parse_struct_lit_fields ctx fields)
                               (lower_parse_opt ctx type_name),
        ParseLiteral.struct_update base fields =>
            Literal.struct_update (lower_parse_term ctx base)
                                  (lower_parse_struct_lit_fields ctx fields),
    }


/// A match arm binds its pattern's names over its BODY. `MatchCase` is a
/// binding form and an easy one to miss -- AGENTS.md item 22 exists
/// because of exactly this.
#[partial]
def lower_parse_match_cases (ctx : List Identifier) (cases : List ParseMatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (lower_parse_match_case ctx c) (lower_parse_match_cases ctx rest),
    }


#[partial]
def lower_parse_match_case (ctx : List Identifier) (c : ParseMatchCase) : MatchCase :=
    MatchCase.mc c.name c.args (lower_parse_term (extend_ctx c.args ctx) c.body) c.field_pattern


#[partial]
def lower_parse_opt (ctx : List Identifier) (t : Option ParseTerm) : Option Term :=
    match t {
        Option.some x => Option.some (lower_parse_term ctx x),
        Option.none => Option.none,
    }


#[partial]
def lower_parse_opts (ctx : List Identifier) (ts : List (Option ParseTerm)) : List (Option Term) :=
    match ts {
        List.empty => List.empty,
        List.cons x rest => List.cons (lower_parse_opt ctx x) (lower_parse_opts ctx rest),
    }


/// Struct-LITERAL fields (`{ x := 1 }`). Distinct from
/// `lower_parse_struct_decl_fields` below, which handles a struct's
/// DECLARED fields (`x : T := default`) -- the two were briefly given the
/// same name, which the checker caught as a type mismatch rather than
/// letting it become an item-18 collision.
#[partial]
def lower_parse_struct_lit_fields (ctx : List Identifier) (fs : List ParseStructLitField) : List StructLitField :=
    match fs {
        List.empty => List.empty,
        List.cons f rest =>
            List.cons (StructLitField.mk f.name (lower_parse_term ctx f.value))
                      (lower_parse_struct_lit_fields ctx rest),
    }


#[partial]
def lower_parse_con (ctx : List Identifier) (c : ParseCon) : Con :=
    match c {
        ParseCon.mk name typ_name num_args args =>
            Con.mk name typ_name num_args (lower_parse_opts ctx args),
    }


#[partial]
def lower_parse_native (ctx : List Identifier) (n : ParseNative) : Native :=
    match n {
        ParseNative.mk name num_args args =>
            Native.mk name num_args (lower_parse_opts ctx args),
    }


// --- The declaration half -------------------------------------------
//
// Every decl-level position simply carries the incoming `ctx`: the
// grammar's binders all live INSIDE the terms, as lambda chains built by
// `lam_params_loop`. Checked rather than assumed -- `type_params_loop`
// (`lang/parser.mo`) threads no `ctx` at all, so an inductive's own
// parameters do NOT bind over its constructor types. (`elaborate.mo`'s
// `elaborate_constructor` does extend a name set with them, but that is
// the Forall-wrapping stage working on names, not de Bruijn indices --
// a different concern.)
//
// `ParseDoStmt` is the one exception, and the only part of this file
// with real semantic content.

#[partial]
def lower_parse_param (ctx : List Identifier) (p : ParseParam) : Param :=
    match p {
        ParseParam.mk name type_ mult default attrs =>
            Param.mk name (lower_parse_term ctx type_) mult (lower_parse_opt ctx default) attrs,
    }


#[partial]
def lower_parse_params (ctx : List Identifier) (ps : List ParseParam) : List Param :=
    match ps {
        List.empty => List.empty,
        List.cons p rest => List.cons (lower_parse_param ctx p) (lower_parse_params ctx rest),
    }


// --- do-notation ------------------------------------------------------
//
// Lower each statement under the context the ones before it established,
// then hand the result to the EXISTING `desugar_do` (`lang/types.mo`) --
// unchanged, and still the only place do-notation is desugared.
//
// The accumulation rule is copied exactly from the grammar's own
// `do_stmts_extend_ctx`, including the part that is easy to miss and
// expensive to get wrong: `expr_s` extends the context with an
// EMPTY-IDENTIFIER PLACEHOLDER. A bare-expression statement desugars to
// `bind expr (lam unnamed hole rest)`, so the continuation sits under one
// real binder and every later statement is de Bruijn-shifted by one.
// Without the placeholder, a do-block that references an OUTER variable
// after a bare-expression statement resolves it to the wrong binder --
// a documented off-by-one, and one that no type error would catch.
// The empty identifier is never produced by `identifier`, so
// `find_index`'s comparison can never match it.

#[partial]
def do_stmt_extend_ctx (stmt : ParseDoStmt) (ctx : List Identifier) : List Identifier :=
    match stmt {
        ParseDoStmt.bind_s name _ _ => List.cons name ctx,
        ParseDoStmt.let_s name _ _ => List.cons name ctx,
        ParseDoStmt.ret_s _ => ctx,
        ParseDoStmt.expr_s _ => List.cons (Identifier.id "") ctx,
    }


#[partial]
def lower_parse_do_stmt (ctx : List Identifier) (stmt : ParseDoStmt) : DoStmt :=
    match stmt {
        ParseDoStmt.bind_s name typ expr =>
            DoStmt.bind_s name (lower_parse_term ctx typ) (lower_parse_term ctx expr),
        ParseDoStmt.let_s name typ expr =>
            DoStmt.let_s name (lower_parse_term ctx typ) (lower_parse_term ctx expr),
        ParseDoStmt.ret_s expr => DoStmt.ret_s (lower_parse_term ctx expr),
        ParseDoStmt.expr_s expr => DoStmt.expr_s (lower_parse_term ctx expr),
    }


#[partial]
def lower_parse_do_stmts (ctx : List Identifier) (stmts : List ParseDoStmt) : List DoStmt :=
    match stmts {
        List.empty => List.empty,
        List.cons s rest =>
            List.cons (lower_parse_do_stmt ctx s)
                      (lower_parse_do_stmts (do_stmt_extend_ctx s ctx) rest),
    }


/// A whole `do { }` block: lower the statements under accumulating
/// context, then desugar exactly as the grammar does today.
#[partial]
def lower_parse_do (ctx : List Identifier) (stmts : List ParseDoStmt) : Term :=
    desugar_do (lower_parse_do_stmts ctx stmts)


// --- declarations -----------------------------------------------------

#[partial]
def lower_parse_struct_field (ctx : List Identifier) (f : ParseStructField) : StructField :=
    match f {
        ParseStructField.mk name typ default mult =>
            StructField.mk name (lower_parse_term ctx typ) (lower_parse_opt ctx default) mult,
    }


#[partial]
def lower_parse_struct_decl_fields (ctx : List Identifier) (fs : List ParseStructField) : List StructField :=
    match fs {
        List.empty => List.empty,
        List.cons f rest =>
            List.cons (lower_parse_struct_field ctx f) (lower_parse_struct_decl_fields ctx rest),
    }


#[partial]
def lower_parse_induct_ctor (ctx : List Identifier) (c : ParseInductConstructor) : InductConstructor :=
    match c {
        ParseInductConstructor.mk name params typ =>
            InductConstructor.mk name (lower_parse_params ctx params) (lower_parse_term ctx typ),
    }


#[partial]
def lower_parse_induct_ctors (ctx : List Identifier) (cs : List ParseInductConstructor) : List InductConstructor :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (lower_parse_induct_ctor ctx c) (lower_parse_induct_ctors ctx rest),
    }


#[partial]
def lower_parse_class_def (ctx : List Identifier) (m : ParseClassDef) : ClassDef :=
    match m {
        ParseClassDef.mk name typ default =>
            ClassDef.mk name (lower_parse_term ctx typ) (lower_parse_opt ctx default),
    }


#[partial]
def lower_parse_class_defs (ctx : List Identifier) (ms : List ParseClassDef) : List ClassDef :=
    match ms {
        List.empty => List.empty,
        List.cons m rest =>
            List.cons (lower_parse_class_def ctx m) (lower_parse_class_defs ctx rest),
    }


#[partial]
def lower_parse_def (ctx : List Identifier) (d : ParseDef) : Def :=
    { name := d.name,
      typ := lower_parse_term ctx d.typ,
      term := lower_parse_term ctx d.term,
      constraints := d.constraints,
      attrs := d.attrs,
      vis := d.vis }


#[partial]
def lower_parse_defs (ctx : List Identifier) (ds : List ParseDef) : List Def :=
    match ds {
        List.empty => List.empty,
        List.cons d rest => List.cons (lower_parse_def ctx d) (lower_parse_defs ctx rest),
    }


#[partial]
def lower_parse_inductive (ctx : List Identifier) (i : ParseInductive) : Inductive :=
    match i {
        ParseInductive.mk name params typ ctors attrs vis =>
            Inductive.mk name (lower_parse_params ctx params) (lower_parse_term ctx typ)
                         (lower_parse_induct_ctors ctx ctors) attrs vis,
    }


#[partial]
def lower_parse_class (ctx : List Identifier) (c : ParseClass) : Class :=
    match c {
        ParseClass.mk name params constraints methods vis =>
            Class.mk name (lower_parse_params ctx params) constraints
                     (lower_parse_class_defs ctx methods) vis,
    }


#[partial]
def lower_parse_instance (ctx : List Identifier) (i : ParseInstance) : Instance :=
    match i {
        ParseInstance.mk name cls constraints args vis implicit_params defs =>
            Instance.mk name cls constraints (lower_parse_terms ctx args) vis
                        (lower_parse_params ctx implicit_params) (lower_parse_defs ctx defs),
    }


#[partial]
def lower_parse_terms (ctx : List Identifier) (ts : List ParseTerm) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (lower_parse_term ctx t) (lower_parse_terms ctx rest),
    }


#[partial]
def lower_parse_struct (ctx : List Identifier) (s : ParseStruct) : Struct :=
    match s {
        ParseStruct.mk name fields vis =>
            Struct.mk name (lower_parse_struct_decl_fields ctx fields) vis,
    }


#[partial]
def lower_parse_decl (ctx : List Identifier) (d : ParseDecl) : Decl :=
    lower_parse_decl_kind ctx d.kind


#[partial]
def lower_parse_decl_kind (ctx : List Identifier) (k : ParseDeclKind) : Decl :=
    match k {
        ParseDeclKind.def_d d => Decl.def_d (lower_parse_def ctx d),
        ParseDeclKind.inductive_d i => Decl.inductive_d (lower_parse_inductive ctx i),
        ParseDeclKind.struct_d s => Decl.struct_d (lower_parse_struct ctx s),
        ParseDeclKind.class_d c => Decl.class_d (lower_parse_class ctx c),
        ParseDeclKind.instance_d i => Decl.instance_d (lower_parse_instance ctx i),
        ParseDeclKind.infix_d op path vis => Decl.infix_d op path vis,
        ParseDeclKind.use_d path filter public => Decl.use_d path filter public,
        ParseDeclKind.open_d path filter => Decl.open_d path filter,
        ParseDeclKind.scoped_open_d path filter inner =>
            Decl.scoped_open_d path filter (lower_parse_decl ctx inner),
        ParseDeclKind.def_macro_d d => Decl.def_macro_d (lower_parse_def ctx d),
        ParseDeclKind.decl_gen_d name params decl_list attrs =>
            Decl.decl_gen_d name (lower_parse_params ctx params)
                            (lower_parse_decls ctx decl_list) attrs,
        ParseDeclKind.macro_call_d name args =>
            Decl.macro_call_d name (lower_parse_terms ctx args),
    }


/// The single entry point. The grammar's three top-level parsers call
/// this with an empty context; everything downstream keeps seeing `Decl`.
#[partial]
def lower_parse_decls (ctx : List Identifier) (ds : List ParseDecl) : List Decl :=
    match ds {
        List.empty => List.empty,
        List.cons d rest => List.cons (lower_parse_decl ctx d) (lower_parse_decls ctx rest),
    }
