/// `ParseTerm` -> `Term`: de Bruijn resolution, as its own pass.
///
// TODO: NOT YET WIRED. `lang/parser.mo` still builds `Term` directly and
// still threads `ctx : List Identifier` through its grammar, so nothing
// calls into this module yet. Remaining to connect it, with measured
// counts as of this commit:
//   - 199 `Term.*` construction sites -> `ParseTermKind` via `pt_`/`pt_at`
//   - 161 defs returning `ParseResult Term` -> `ParseResult ParseTerm`
//   - 235 defs taking `ctx : List Identifier` -> dropped, along with the
//     binder-extension call sites (`List.cons name ctx`,
//     `lambda_extend_ctx binders ctx`) that `extend_ctx` below replaces
//   - ~10 decl-parser sites that seed `empty_ctx` -> call
//     `lower_parse_term` on the parsed `ParseTerm` instead
// Then a second pass replaces `pt_`'s placeholder span with `pt_at`'s
// real one at each construction site.
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
/// Name resolution (`sentinel`, `find_index`, `field_access_chain`,
/// `name_ref_to_string`) is IMPORTED from
/// `lang/parser.mo`, not redefined -- duplicate top-level names across
/// `lang/*.mo` silently collide (AGENTS.md item 18).
use lang.types {
  Con, DebugName, Identifier, Literal, MatchCase, ModulePath, NameRef, Native,
  ParseCon, ParseLiteral, ParseMatchCase, ParseNative,
  ParseStructLitField, ParseTerm, ParseTermKind, StructLitField, Term,
  sentinel,
}
// Imported, NOT redefined. An earlier revision of this file copied these
// six in and claimed in its own comment to have moved them -- which armed
// exactly the duplicate-top-level-name collision AGENTS.md item 18
// records, and silently diverged (`name_ref_to_string`'s `nop` arm threw
// away the operator spelling that `resolve_infix_decls` needs). The
// layering is temporarily inverted -- a submodule importing its parent --
// and is resolved when the grammar is wired to this pass: at that point
// these move here for real and `lang/parser.mo` imports them back.
use lang.parser {
  field_access_chain, find_index, name_ref_to_string,
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
        ParseTermKind.app f a =>
            Term.app (lower_parse_term ctx f) (lower_parse_term ctx a),
        ParseTermKind.lit l => Term.lit (lower_parse_literal ctx l),
        ParseTermKind.ntv n => Term.ntv (lower_parse_native ctx n),
        ParseTermKind.con c => Term.con (lower_parse_con ctx c),
        ParseTermKind.type_ u => Term.type_ u,
        ParseTermKind.quote_ inner => Term.quote_ (lower_parse_term ctx inner),
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
            Literal.struct_lit (lower_parse_struct_fields ctx fields)
                               (lower_parse_opt ctx type_name),
        ParseLiteral.struct_update base fields =>
            Literal.struct_update (lower_parse_term ctx base)
                                  (lower_parse_struct_fields ctx fields),
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


#[partial]
def lower_parse_struct_fields (ctx : List Identifier) (fs : List ParseStructLitField) : List StructLitField :=
    match fs {
        List.empty => List.empty,
        List.cons f rest =>
            List.cons (StructLitField.mk f.name (lower_parse_term ctx f.value))
                      (lower_parse_struct_fields ctx rest),
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
