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
  Struct, StructField, StructLitField, Term, sentinel,
}
// Name resolution lives HERE now, moved out of `lang/parser.mo` for real
// (an earlier revision copied it while claiming to have moved it, arming
// the duplicate-top-level-name collision item 18 records). The grammar no
// longer resolves names at all, so nothing flows the other way: it
// imports `lower_parse_do` from here and that is the only edge.
use lang.types {FieldPattern, FieldPatternEntry, Location, ParseSpan, parse_span_is_unknown, show_operator}
// The monomorphic string map, from the leaf module -- never `Map.lookup`,
// whose generic dispatch can resolve to the wrong instance
// (`lang/codegen/util.mo` documents the live bug).
use lang.codegen.strmap {str_map_lookup}
use std.map {}


/// What lowering carries down the tree.
///
/// `ParseLowerCtx`, not `LowerCtx`: `lang/lower_core_ir.mo` already owns
/// that name, and duplicate top-level names across `lang/*.mo` silently
/// collide (AGENTS.md item 18) -- here loudly, since both are types.
///
/// Was a bare `List Identifier` of binders. It gained a second field
/// because source positions have to reach the wrap site, and the wrap site
/// is every value-position term -- there is nowhere else to put the table
/// that does not amount to threading it anyway.
///
/// `locs` absent means **no wrappers are constructed at all**, and that is
/// the whole `--debug` gate: `check`, `test` and a non-debug `compile` go
/// through entry points that leave it `none`, so their ASTs are
/// byte-identical to what they were before locations existed. The phase
/// this would otherwise slow down is 67% of elaboration (AGENTS.md item
/// 27), so the gate is structural rather than a matter of discipline.
struct ParseLowerCtx {
    binders : List Identifier,
    /// Absolute start offset (as a decimal string, since there is no
    /// `Hashable I64`) -> resolved position. Built once per file by
    /// `resolve_offsets_in_file` (`lang/parser/position.mo`).
    locs : Option (HashMap String Location),
}

/// A context that records positions from a prepared table.
///
/// The table is keyed by `ParseSpan.start_rem` -- the REMAINING-input
/// length at a construct's start, which is what a span actually stores --
/// rather than by absolute offset. The conversion needs the file's total
/// length and so can only happen where the whole file is in hand; doing it
/// once when the table is built beats doing it at each of the ~10^4
/// lookups.
#[partial]
def lower_ctx_locating (table : HashMap String Location) : ParseLowerCtx :=
    { binders := List.empty, locs := Option.some table }

/// A context that records no positions -- what every non-debug caller uses.
#[partial]
def lower_ctx_bare : ParseLowerCtx := { binders := List.empty, locs := Option.none }

/// Bind one name, innermost-first (de Bruijn index 0 at the head).
#[partial]
def lower_ctx_bind (name : Identifier) (ctx : ParseLowerCtx) : ParseLowerCtx :=
    { binders := List.cons name ctx.binders, locs := ctx.locs }

/// Bind a group, in order, so the LAST-declared name ends up innermost.
#[partial]
def lower_ctx_bind_all (names : List Identifier) (ctx : ParseLowerCtx) : ParseLowerCtx :=
    { binders := extend_ctx names ctx.binders, locs := ctx.locs }


/// The context a `Term.pi`'s return type is lowered under: extended by
/// the arrow's own binder when the source named one, unchanged when it
/// did not. Split out so both halves of that rule sit in one place
/// rather than being re-derived at the match arm.
#[partial]
def pi_ret_ctx (arg_name : Option Identifier) (ctx : ParseLowerCtx) : ParseLowerCtx :=
    match arg_name {
        Option.some n => lower_ctx_bind n ctx,
        Option.none => ctx,
    }


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
def lower_name_ref (ctx : ParseLowerCtx) (nref : NameRef) : Term :=
    match nref {
        // `find_index` directly rather than `var_term`, which only takes
        // a `String` to re-wrap it as an `Identifier` immediately -- and
        // that round trip is what tripped whole-corpus resolution.
        NameRef.nid id =>
            match find_index id ctx.binders 0 {
                Option.some idx => Term.var idx (DebugName.named id),
                Option.none => Term.var sentinel (DebugName.named id),
            },
        NameRef.nmp mp => lower_path ctx mp nref,
        NameRef.nop _ => lower_name_global nref,
    }


#[partial]
def lower_path (ctx : ParseLowerCtx) (mp : ModulePath) (nref : NameRef) : Term :=
    match mp {
        ModulePath.mp ids => lower_path_ids ctx ids nref,
    }


#[partial]
def lower_path_ids (ctx : ParseLowerCtx) (ids : List Identifier) (nref : NameRef) : Term :=
    match ids {
        List.cons first fields =>
            match find_index first ctx.binders 0 {
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

// --- Span collection -------------------------------------------------
//
// Gathers every `start_rem` the lowering will later look up, so they can
// all be resolved in one pass instead of one scan each. Visits in the same
// pre-order the lowering does, which is what makes the result ascending in
// absolute offset (a larger `start_rem` is EARLIER in the file) and so
// eligible for `resolve_offsets_in_file`'s linear path.
//
// Collected into a reversed accumulator, so callers reverse once.
//
// Only the kinds `kind_wants_loc` accepts are collected: resolving a span
// nothing will look up is wasted work, and the two must agree or the
// lookup misses and the term is silently left unlocated.

#[partial]
def collect_decl_rems (ds : List ParseDecl) (acc : List I64) : List I64 := match ds {
    List.empty => acc,
    List.cons d rest => collect_decl_rems rest (collect_decl_kind_rems d.kind acc),
}

#[partial]
def collect_decl_kind_rems (k : ParseDeclKind) (acc : List I64) : List I64 := match k {
    ParseDeclKind.def_d d => collect_def_rems d acc,
    ParseDeclKind.def_macro_d d => collect_def_rems d acc,
    ParseDeclKind.inductive_d i => collect_ctor_rems i.constructors (collect_param_rems i.params acc),
    ParseDeclKind.struct_d st => collect_field_rems st.fields acc,
    ParseDeclKind.class_d c => collect_classdef_rems c.methods (collect_param_rems c.params acc),
    ParseDeclKind.instance_d i => collect_def_list_rems i.defs (collect_param_rems i.implicit_params acc),
    ParseDeclKind.scoped_open_d _p _f inner => collect_decl_kind_rems inner.kind acc,
    ParseDeclKind.decl_gen_d _n params decls _a => collect_decl_rems decls (collect_param_rems params acc),
    ParseDeclKind.macro_call_d _n args => collect_term_list_rems args acc,
    ParseDeclKind.infix_d _o _p _v => acc,
    ParseDeclKind.use_d _p _f _pub => acc,
    ParseDeclKind.open_d _p _f => acc,
}

#[partial]
def collect_def_rems (d : ParseDef) (acc : List I64) : List I64 :=
    // `d.typ` is a type (R1) and carries no wrapper, so it is not collected.
    collect_term_rems d.term acc

#[partial]
def collect_def_list_rems (ds : List ParseDef) (acc : List I64) : List I64 := match ds {
    List.empty => acc,
    List.cons d rest => collect_def_list_rems rest (collect_def_rems d acc),
}

#[partial]
def collect_param_rems (ps : List ParseParam) (acc : List I64) : List I64 := match ps {
    List.empty => acc,
    // A parameter's type is R1; only its default value is a value.
    List.cons p rest => collect_param_rems rest (collect_opt_rems p.default acc),
}

#[partial]
def collect_field_rems (fs : List ParseStructField) (acc : List I64) : List I64 := match fs {
    List.empty => acc,
    List.cons f rest => collect_field_rems rest (collect_opt_rems f.default acc),
}

#[partial]
def collect_ctor_rems (cs : List ParseInductConstructor) (acc : List I64) : List I64 := match cs {
    List.empty => acc,
    List.cons c rest => collect_ctor_rems rest (collect_param_rems c.params acc),
}

#[partial]
def collect_classdef_rems (ms : List ParseClassDef) (acc : List I64) : List I64 := match ms {
    List.empty => acc,
    List.cons m rest => collect_classdef_rems rest (collect_opt_rems m.default acc),
}

#[partial]
def collect_opt_rems (o : Option ParseTerm) (acc : List I64) : List I64 := match o {
    Option.none => acc,
    Option.some t => collect_term_rems t acc,
}

#[partial]
def collect_term_list_rems (ts : List ParseTerm) (acc : List I64) : List I64 := match ts {
    List.empty => acc,
    List.cons t rest => collect_term_list_rems rest (collect_term_rems t acc),
}

/// This node first (pre-order), then its children left to right.
#[partial]
def collect_term_rems (pt : ParseTerm) (acc : List I64) : List I64 :=
    let acc1 : List I64 :=
        if kind_wants_loc pt.kind && (parse_span_is_unknown pt.span == false)
        then List.cons pt.span.start_rem acc
        else acc in
    collect_kind_rems pt.kind acc1

#[partial]
def collect_kind_rems (k : ParseTermKind) (acc : List I64) : List I64 := match k {
    ParseTermKind.app f a => collect_term_rems a (collect_term_rems f acc),
    ParseTermKind.lam _n _t body => collect_term_rems body acc,
    ParseTermKind.forall _n _t body => collect_term_rems body acc,
    ParseTermKind.quote_ inner => collect_term_rems inner acc,
    ParseTermKind.lit l => collect_lit_rems l acc,
    ParseTermKind.do_ stmts => collect_do_rems stmts acc,
    // R1: a pi is entirely type-level, so nothing under it is located.
    ParseTermKind.pi _n _a _r => acc,
    ParseTermKind.var _ => acc,
    ParseTermKind.var_macro _ => acc,
    ParseTermKind.con _ => acc,
    ParseTermKind.ntv _ => acc,
    ParseTermKind.type_ _ => acc,
    ParseTermKind.hole => acc,
}

#[partial]
def collect_lit_rems (l : ParseLiteral) (acc : List I64) : List I64 := match l {
    ParseLiteral.if_ c t e => collect_term_rems e (collect_term_rems t (collect_term_rems c acc)),
    ParseLiteral.match_ scrut cases => collect_case_rems cases (collect_term_rems scrut acc),
    ParseLiteral.struct_lit fields _tn => collect_litfield_rems fields acc,
    ParseLiteral.struct_update base fields => collect_litfield_rems fields (collect_term_rems base acc),
    ParseLiteral.str _ => acc,
    ParseLiteral.num _ _ => acc,
    ParseLiteral.flt _ _ => acc,
}

#[partial]
def collect_case_rems (cs : List ParseMatchCase) (acc : List I64) : List I64 := match cs {
    List.empty => acc,
    List.cons c rest => collect_case_rems rest (collect_term_rems c.body acc),
}

#[partial]
def collect_litfield_rems (fs : List ParseStructLitField) (acc : List I64) : List I64 := match fs {
    List.empty => acc,
    List.cons f rest => collect_litfield_rems rest (collect_litfield_one f acc),
}

#[partial]
def collect_litfield_one (f : ParseStructLitField) (acc : List I64) : List I64 := match f {
    ParseStructLitField.mk _name value => collect_term_rems value acc,
}

#[partial]
def collect_do_rems (stmts : List DoStmt) (acc : List I64) : List I64 := match stmts {
    List.empty => acc,
    List.cons s rest => collect_do_rems rest (collect_do_stmt_rems s acc),
}

#[partial]
def collect_do_stmt_rems (s : DoStmt) (acc : List I64) : List I64 := match s {
    DoStmt.bind_s _n _t expr => collect_term_rems expr acc,
    DoStmt.let_s _n _t expr => collect_term_rems expr acc,
    DoStmt.ret_s expr => collect_term_rems expr acc,
    DoStmt.expr_s expr => collect_term_rems expr acc,
}


/// Does a term of this shape deserve a recorded position?
///
/// The "instruction-shaped" granularity: the forms that become LLVM
/// instructions and so deserve a distinct line. Not lambdas, not
/// type-level forms, not a hole.
///
/// Expressing this as a property of the KIND rather than of the call site
/// is what implements placement rule R2 -- never wrap a `lam` or its
/// direct body. A caller-based rule would break at every function, because
/// a def body's outermost node IS a lam; and a wrapper between two lams
/// truncates `collect_db_params` (`lang/codegen/ctx.mo`), which counts
/// them to derive a compiled function's parameter count.
///
/// `quote_` is excluded because its body is syntax-as-data, not code.
#[partial]
def kind_wants_loc (k : ParseTermKind) : Bool := match k {
    ParseTermKind.var _ => true,
    ParseTermKind.var_macro _ => true,
    ParseTermKind.lit _ => true,
    ParseTermKind.app _ _ => true,
    ParseTermKind.con _ => true,
    ParseTermKind.ntv _ => true,
    ParseTermKind.do_ _ => true,
    ParseTermKind.lam _ _ _ => false,
    ParseTermKind.forall _ _ _ => false,
    ParseTermKind.pi _ _ _ => false,
    ParseTermKind.type_ _ => false,
    ParseTermKind.quote_ _ => false,
    ParseTermKind.hole => false,
}

/// Lower a term in VALUE position, recording its position when there is
/// one to record.
#[partial]
def lower_parse_term (ctx : ParseLowerCtx) (pt : ParseTerm) : Term :=
    let inner : Term := lower_parse_kind ctx pt.kind in
    if kind_wants_loc pt.kind then locate_term ctx pt.span inner else inner

/// Lower a term WITHOUT recording a position.
///
/// Used at the two positions where a wrapper would be read as structure
/// rather than annotation:
///
///   - **R1, type position.** `type_head_name` (`lang/typecheck/infer.mo`),
///     `type_head_name_local` (`lang/scope.mo`), `con_spine_result_typ`,
///     `solve_typevars` and `term_matches_carrier` all probe the shape of
///     a type. A wrapper there does not crash them; it makes them stop
///     matching, and an instance quietly fails to resolve.
///   - **R3, application head position.** Only a spine's OUTERMOST `app`
///     is located, plus each argument. That protects `class_method_ref`
///     (`lang/scope.mo`) and `spine_head`, and it is also the right
///     granularity for codegen: a call spine emits one call, so it wants
///     one position.
#[partial]
def lower_parse_term_bare (ctx : ParseLowerCtx) (pt : ParseTerm) : Term :=
    lower_parse_kind ctx pt.kind

/// Wrap with the position this span resolves to, if the context is
/// recording positions and the span is a real one. Synthesized terms
/// (`pt_hole` for an omitted annotation, `build_list_literal`'s cons
/// cells) carry `parse_span_unknown` and are left bare -- they were never
/// written anywhere, so there is no position to claim.
#[partial]
def locate_term (ctx : ParseLowerCtx) (span : ParseSpan) (inner : Term) : Term :=
    match ctx.locs {
        Option.none => inner,
        Option.some table => locate_term_from table span inner,
    }

#[partial]
def locate_term_from (table : HashMap String Location) (span : ParseSpan) (inner : Term) : Term :=
    if parse_span_is_unknown span
    then inner
    else
        match str_map_lookup (I64.to_string span.start_rem) table {
            Option.some loc => Term.ctx loc inner,
            Option.none => inner,
        }


#[partial]
def lower_parse_kind (ctx : ParseLowerCtx) (k : ParseTermKind) : Term :=
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
                     (lower_parse_term_bare ctx typ)
                     (lower_parse_term (lower_ctx_bind name ctx) body),
        ParseTermKind.forall name typ body =>
            Term.forall (DebugName.named name)
                        (lower_parse_term_bare ctx typ)
                        (lower_parse_term (lower_ctx_bind name ctx) body),
        // A `pi` binds only when the source wrote a name: `(n : T) ->
        // body` puts `n` in scope over `body`, which is what
        // `type_dep_arrow_tag` (`lang/parser.mo`) used to do inline
        // before the grammar stopped resolving names. `Term.pi` has no
        // field to carry `n`, so a name not consumed HERE is lost and
        // every use of it inside `body` resolves to `sentinel` -- a
        // regression this branch shipped once, now pinned by
        // `test_dep_pi_binds_its_own_name`.
        //
        // A NAMELESS `pi` deliberately does not extend, because the
        // grammar that produces one does not: `build_pi_chain`/
        // `build_param_pi_chain` fold a "non-dependent Pi chain" (their
        // own words) with the return type at the SAME depth as the
        // argument. Note this disagrees with `lang/typecheck/traverse.mo`,
        // whose depth-aware walker treats every `Term.pi`'s `ret` as
        // sitting under one binder (`f 1 ret`) -- a real pre-existing
        // producer/consumer inconsistency. Matching the PRODUCER is what
        // preserves behaviour; it is a separate question from this
        // refactor.
        // R1 on both sides: a pi is entirely type-level.
        ParseTermKind.pi arg_name arg ret =>
            Term.pi (lower_parse_term_bare ctx arg)
                    (lower_parse_term_bare (pi_ret_ctx arg_name ctx) ret),
        // R3: the callee is bare so a spine's inner `app`s stay visible to
        // `flatten_call_spine`; only the outermost `app` (located by
        // `lower_parse_term` on the way in) and each argument carry one.
        ParseTermKind.app f a =>
            Term.app (lower_parse_term_bare ctx f) (lower_parse_term ctx a),
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
def lower_parse_literal (ctx : ParseLowerCtx) (l : ParseLiteral) : Literal :=
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
def lower_parse_match_cases (ctx : ParseLowerCtx) (cases : List ParseMatchCase) : List MatchCase :=
    match cases {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (lower_parse_match_case ctx c) (lower_parse_match_cases ctx rest),
    }


#[partial]
def lower_parse_match_case (ctx : ParseLowerCtx) (c : ParseMatchCase) : MatchCase :=
    MatchCase.mc c.name c.args (lower_parse_term (lower_ctx_bind_all c.args ctx) c.body) c.field_pattern


#[partial]
def lower_parse_opt (ctx : ParseLowerCtx) (t : Option ParseTerm) : Option Term :=
    match t {
        Option.some x => Option.some (lower_parse_term ctx x),
        Option.none => Option.none,
    }


#[partial]
def lower_parse_opts (ctx : ParseLowerCtx) (ts : List (Option ParseTerm)) : List (Option Term) :=
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
def lower_parse_struct_lit_fields (ctx : ParseLowerCtx) (fs : List ParseStructLitField) : List StructLitField :=
    match fs {
        List.empty => List.empty,
        List.cons f rest =>
            List.cons (StructLitField.mk f.name (lower_parse_term ctx f.value))
                      (lower_parse_struct_lit_fields ctx rest),
    }


#[partial]
def lower_parse_con (ctx : ParseLowerCtx) (c : ParseCon) : Con :=
    match c {
        ParseCon.mk name typ_name num_args args =>
            Con.mk name typ_name num_args (lower_parse_opts ctx args),
    }


#[partial]
def lower_parse_native (ctx : ParseLowerCtx) (n : ParseNative) : Native :=
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
def lower_parse_param (ctx : ParseLowerCtx) (p : ParseParam) : Param :=
    Param.mk p.name (lower_parse_term_bare ctx p.type_) p.mult (lower_parse_opt ctx p.default) p.attrs


#[partial]
def lower_parse_params (ctx : ParseLowerCtx) (ps : List ParseParam) : List Param :=
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
// A `do { ... }` block is desugared HERE, into `Monad.bind`/`Monad.pure`
// applications, rather than by a separate pass over an already-lowered
// statement list. The two jobs cannot be separated cleanly: each binder a
// statement introduces is in scope for the statements that FOLLOW it, so
// the desugaring's own lambdas ARE the context accumulation. Fusing them
// means the `ctx` extension sits on the same line as the `Term.lam` that
// justifies it, instead of being restated in a parallel
// `do_stmt_extend_ctx` that a reader has to keep in sync by hand -- which
// is where the documented `expr_s` off-by-one used to live.

/// `Monad.bind`/`Monad.pure` as NAMED free variables, not
/// `DebugName.unnamed` ones, so a desugared do-block flows through the
/// same class-method-call resolution (`resolve_class_call_term`,
/// `lang/scope.mo`) every other class method gets. That function's
/// `DebugName.unnamed` arm deliberately leaves an unnamed call head
/// alone -- it has no name to resolve a class or instance from -- so an
/// unnamed sentinel reached codegen unresolved and produced a bogus
/// `void`-typed call argument. Mirrors the Rust reference's own
/// `desugar_do_statements` (`core/src/parser.rs`), which likewise
/// desugars to a real dotted `Monad.bind`/`Monad.pure`.
def monad_bind_term : Term :=
    Term.var sentinel (DebugName.named (Identifier.id "Monad.bind"))

def monad_pure_term : Term :=
    Term.var sentinel (DebugName.named (Identifier.id "Monad.pure"))


/// Desugar and lower a whole `do { }` block in one traversal.
///
/// Folds in SOURCE order -- the first statement is the OUTERMOST wrap,
/// each statement wrapping the desugaring of those that follow it, with
/// the trailing `Monad.pure hole` innermost. Mirrors the Rust
/// reference's `desugar_do_statements` (`core/src/parser.rs`).
/// Reversing the list (a real past bug) puts the LAST statement
/// outermost, which both inverts monadic evaluation order and places a
/// later statement's reference to an earlier binding OUTSIDE that
/// binding's binder -- a spurious out-of-range `bound_var`.
#[partial]
def lower_parse_do (ctx : ParseLowerCtx) (stmts : List DoStmt) : Term :=
    lower_parse_do_inner ctx stmts (Term.app monad_pure_term Term.hole)


#[partial]
def lower_parse_do_inner (ctx : ParseLowerCtx) (stmts : List DoStmt) (rest : Term) : Term :=
    match stmts {
        List.cons s ss => lower_parse_do_stmt ctx s ss rest,
        List.empty => rest,
    }


#[partial]
def lower_parse_do_stmt (ctx : ParseLowerCtx) (s : DoStmt) (ss : List DoStmt) (rest : Term) : Term :=
    match s {
        // `expr` is lowered in the OUTER ctx -- a statement's own value
        // cannot refer to the variable it binds -- while the
        // continuation is lowered one binder deeper.
        DoStmt.bind_s name typ expr =>
            Term.app (Term.app monad_bind_term (lower_parse_term ctx expr))
                     (Term.lam (DebugName.named name)
                               (lower_parse_term_bare ctx typ)
                               (lower_parse_do_inner (lower_ctx_bind name ctx) ss rest)),
        DoStmt.let_s name typ expr =>
            Term.app (Term.lam (DebugName.named name)
                               (lower_parse_term_bare ctx typ)
                               (lower_parse_do_inner (lower_ctx_bind name ctx) ss rest))
                     (lower_parse_term ctx expr),
        // `ret_s` DISCARDS the accumulated continuation, matching the
        // reference's `Return`.
        DoStmt.ret_s expr => Term.app monad_pure_term (lower_parse_term ctx expr),
        DoStmt.expr_s expr => lower_parse_do_expr_stmt ctx expr ss rest,
    }


/// A bare-expression statement.
///
/// With nothing following it, it IS the block's value and is used
/// directly -- not bound via `Monad.bind` to a discarding continuation,
/// which would silently replace it with the block's default
/// `Monad.pure hole`. Mirrors the reference's `DoStatement::Expr { value
/// } => value` for the last statement. Confirmed as a real bug through
/// the full `lang/main.mo` self-compile: a do-block ending in a bare
/// `match`/`if` containing its own `return`s had its value replaced by
/// Unit.
///
/// With statements following, it binds through a lambda whose binder is
/// UNNAMED but real, so `ctx` is extended by an empty-identifier
/// placeholder: the continuation sits one binder deeper and every later
/// statement is de Bruijn-shifted by one. Without it, a reference to an
/// OUTER variable after a bare-expression statement resolves to the
/// wrong binder -- an off-by-one no type error would catch. The empty
/// identifier can never collide with a real name because `identifier`
/// never produces one.
#[partial]
def lower_parse_do_expr_stmt (ctx : ParseLowerCtx) (expr : ParseTerm) (ss : List DoStmt) (rest : Term) : Term :=
    match ss {
        List.empty => lower_parse_term ctx expr,
        List.cons _ _ =>
            Term.app (Term.app monad_bind_term (lower_parse_term ctx expr))
                     (Term.lam DebugName.unnamed
                               Term.hole
                               (lower_parse_do_inner (lower_ctx_bind (Identifier.id "") ctx) ss rest)),
    }


// --- declarations -----------------------------------------------------
//
// Each of these reads its source by FIELD, not by a positional
// `Parse*.mk a b c d e f g` pattern. The positional form binds one
// variable per field and silently goes out of date: add a field to the
// struct and every such pattern still typechecks, then aborts at runtime
// with `expected 7 constructor fields, got 8` -- no location, no def
// name (AGENTS.md's note on adding a field to a struct). Field access
// has no arity to get wrong, and names each value at the point it is
// used.

#[partial]
def lower_parse_struct_field (ctx : ParseLowerCtx) (f : ParseStructField) : StructField :=
    StructField.mk f.name (lower_parse_term_bare ctx f.typ) (lower_parse_opt ctx f.default) f.mult


#[partial]
def lower_parse_struct_decl_fields (ctx : ParseLowerCtx) (fs : List ParseStructField) : List StructField :=
    match fs {
        List.empty => List.empty,
        List.cons f rest =>
            List.cons (lower_parse_struct_field ctx f) (lower_parse_struct_decl_fields ctx rest),
    }


#[partial]
def lower_parse_induct_ctor (ctx : ParseLowerCtx) (c : ParseInductConstructor) : InductConstructor :=
    InductConstructor.mk c.name (lower_parse_params ctx c.params) (lower_parse_term_bare ctx c.typ)


#[partial]
def lower_parse_induct_ctors (ctx : ParseLowerCtx) (cs : List ParseInductConstructor) : List InductConstructor :=
    match cs {
        List.empty => List.empty,
        List.cons c rest =>
            List.cons (lower_parse_induct_ctor ctx c) (lower_parse_induct_ctors ctx rest),
    }


#[partial]
def lower_parse_class_def (ctx : ParseLowerCtx) (m : ParseClassDef) : ClassDef :=
    ClassDef.mk m.name (lower_parse_term_bare ctx m.typ) (lower_parse_opt ctx m.default)


#[partial]
def lower_parse_class_defs (ctx : ParseLowerCtx) (ms : List ParseClassDef) : List ClassDef :=
    match ms {
        List.empty => List.empty,
        List.cons m rest =>
            List.cons (lower_parse_class_def ctx m) (lower_parse_class_defs ctx rest),
    }


#[partial]
def lower_parse_def (ctx : ParseLowerCtx) (d : ParseDef) : Def :=
    { name := d.name,
      typ := lower_parse_term_bare ctx d.typ,
      term := lower_parse_term ctx d.term,
      constraints := d.constraints,
      attrs := d.attrs,
      vis := d.vis }


#[partial]
def lower_parse_defs (ctx : ParseLowerCtx) (ds : List ParseDef) : List Def :=
    match ds {
        List.empty => List.empty,
        List.cons d rest => List.cons (lower_parse_def ctx d) (lower_parse_defs ctx rest),
    }


#[partial]
def lower_parse_inductive (ctx : ParseLowerCtx) (i : ParseInductive) : Inductive :=
    Inductive.mk i.name (lower_parse_params ctx i.params) (lower_parse_term ctx i.typ)
                 (lower_parse_induct_ctors ctx i.constructors) i.attrs i.vis


#[partial]
def lower_parse_class (ctx : ParseLowerCtx) (c : ParseClass) : Class :=
    Class.mk c.name (lower_parse_params ctx c.params) c.constraints
             (lower_parse_class_defs ctx c.methods) c.vis


#[partial]
def lower_parse_instance (ctx : ParseLowerCtx) (i : ParseInstance) : Instance :=
    Instance.mk i.name i.cls i.constraints (lower_parse_terms_bare ctx i.args) i.vis
                (lower_parse_params ctx i.implicit_params) (lower_parse_defs ctx i.defs)


/// Terms in TYPE position (R1) -- an instance's class arguments, which
/// `term_matches_carrier` (`lang/scope.mo`) probes structurally.
#[partial]
def lower_parse_terms_bare (ctx : ParseLowerCtx) (ts : List ParseTerm) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (lower_parse_term_bare ctx t) (lower_parse_terms_bare ctx rest),
    }

#[partial]
def lower_parse_terms (ctx : ParseLowerCtx) (ts : List ParseTerm) : List Term :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (lower_parse_term ctx t) (lower_parse_terms ctx rest),
    }


#[partial]
def lower_parse_struct (ctx : ParseLowerCtx) (s : ParseStruct) : Struct :=
    Struct.mk s.name (lower_parse_struct_decl_fields ctx s.fields) s.vis


#[partial]
def lower_parse_decl (ctx : ParseLowerCtx) (d : ParseDecl) : Decl :=
    lower_parse_decl_kind ctx d.kind


#[partial]
def lower_parse_decl_kind (ctx : ParseLowerCtx) (k : ParseDeclKind) : Decl :=
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
def lower_parse_decls (ctx : ParseLowerCtx) (ds : List ParseDecl) : List Decl :=
    match ds {
        List.empty => List.empty,
        List.cons d rest => List.cons (lower_parse_decl ctx d) (lower_parse_decls ctx rest),
    }
