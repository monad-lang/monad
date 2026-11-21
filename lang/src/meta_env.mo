/// The environment macro meta-defs are evaluated in (`meta_eval_invoke`,
/// reached from `meta!` and `reflect_type_info!`): the defs reachable from
/// the meta-def names, elaborated, plus every non-def declaration. Building
/// it from the whole graph type-checked the entire program in post-load
/// only to evaluate a few derive/format helpers.
///
/// A def whose elaboration fails is kept in place with a body lowering
/// rejects (`poisoned_decl`), so a meta-def that reaches it fails with the
/// elaboration error instead of evaluating the unelaborated body, and a
/// def pulled in only by name and never lowered costs nothing.
///
/// Reachability is by name and over-approximates: a def is filed under its
/// bare name and under the segment after its last `.` (an opened
/// `IO.println` is referenced as `println`), and every def sharing a key is
/// kept. A reference the keys miss leaves its def out, and lowering then
/// fails on the unresolved name. Defs keep their original relative
/// order, so lowering's first-match lookup picks the same def it would in
/// the whole graph. The closure is taken over ELABORATED bodies, because
/// elaboration is what introduces the dictionary and instance-method
/// references a class call resolves to.
use lang::types {
    DebugName, Decl, Def, Identifier, Literal, MatchCase, StructLitField, Term,
    sentinel, show_identifier, show_name_path,
}
use lib::name_text {unqualify_def_name}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use std::list {}
use std::map {HashMap}

/// The name a reference or a def is matched by: its spelling after the
/// last `::`.
pub def ref_key (id : Identifier) : String := unqualify_def_name (show_identifier id)

/// Every global name `t` references: free variables, macro variables,
/// constructors and match-case constructor names.
#[partial]
pub def term_ref_names (t : Term) (acc : List String) : List String := match t {
    Term.var idx dbg => global_ref idx dbg acc,
    Term.var_macro idx dbg => global_ref idx dbg acc,
    Term.lam _b typ body => term_ref_names body (term_ref_names typ acc),
    Term.pi _b arg ret => term_ref_names ret (term_ref_names arg acc),
    Term.app f a => term_ref_names a (term_ref_names f acc),
    Term.ntv n => match n { { args, .. } => opt_terms_ref_names args acc },
    Term.con c => match c { { name, args, .. } => opt_terms_ref_names args (List.cons (ref_key name) acc) },
    Term.lit l => lit_ref_names l acc,
    Term.sort _level => acc,
    Term.hole => acc,
    Term.quote_ inner => term_ref_names inner acc,
    Term.ctx _loc inner => term_ref_names inner acc,
    Term.cubical c => match c { { prim := _, args := args } => terms_ref_names args acc },
    Term.elim e =>
        term_ref_names e.scrutinee
            (terms_ref_names e.minors
                (term_ref_names e.motive (terms_ref_names e.indices (terms_ref_names e.params acc)))),
}

/// A variable is a global reference only at index `sentinel`; any other
/// index is a bound local, whose name must not pull same-named defs in.
def global_ref (idx : I64) (dbg : DebugName) (acc : List String) : List String :=
    if I64.beq idx sentinel then
        match dbg {
            DebugName.named id => List.cons (ref_key id) acc,
            DebugName.unnamed => acc,
        }
    else acc

#[partial]
def terms_ref_names (ts : List Term) (acc : List String) : List String := match ts {
    List.empty => acc,
    List.cons t rest => terms_ref_names rest (term_ref_names t acc),
}

#[partial]
def opt_terms_ref_names (ts : List (Option Term)) (acc : List String) : List String := match ts {
    List.empty => acc,
    List.cons o rest => match o {
        Option.some t => opt_terms_ref_names rest (term_ref_names t acc),
        Option.none => opt_terms_ref_names rest acc,
    },
}

#[partial]
def lit_ref_names (l : Literal) (acc : List String) : List String := match l {
    Literal.if_ c a b => term_ref_names b (term_ref_names a (term_ref_names c acc)),
    Literal.match_ v cases => cases_ref_names cases (term_ref_names v acc),
    Literal.struct_lit fields _type_name => fields_ref_names fields acc,
    Literal.struct_update base fields => fields_ref_names fields (term_ref_names base acc),
    _ => acc,
}

#[partial]
def cases_ref_names (cases : List MatchCase) (acc : List String) : List String := match cases {
    List.empty => acc,
    List.cons c rest => match c {
        { name, body, .. } =>
            cases_ref_names rest (List.cons (ref_key name) (term_ref_names body acc)),
    },
}

#[partial]
def fields_ref_names (fields : List StructLitField) (acc : List String) : List String := match fields {
    List.empty => acc,
    List.cons f rest => match f { StructLitField.mk _name value => fields_ref_names rest (term_ref_names value acc) },
}

/// The def a declaration carries, looking through a `scoped_open_d`.
#[partial]
pub def decl_def (d : Decl) : Option Def := match d {
    Decl.def_d df => Option.some df,
    Decl.scoped_open_d _p _f inner => decl_def inner,
    _ => Option.none,
}

/// Every name a declaration's def references (type and body); a non-def
/// references nothing here.
pub def decl_ref_names (d : Decl) (acc : List String) : List String := match decl_def d {
    Option.some df => match df { Def.mk { typ, term, .. } => term_ref_names term (term_ref_names typ acc) },
    Option.none => acc,
}

/// The keys a def is filed under: its bare name and, for a dotted bare
/// name, the segment after the last `.`.
def def_keys (df : Def) : List String :=
    let bare : String := unqualify_def_name (show_name_path df.name) in
    match List.last (String.split bare ".") {
        Option.some seg => if String.beq seg bare then [bare] else [bare, seg],
        Option.none => [bare],
    }

/// A def's position in the input list, and the declaration itself.
struct MetaEnvEntry {
    pos : I64,
    decl : Decl,
}

#[partial]
def index_add (keys : List String) (e : MetaEnvEntry) (idx : HashMap String (List MetaEnvEntry))
    : HashMap String (List MetaEnvEntry) :=
    match keys {
        List.empty => idx,
        List.cons k rest =>
            let prev : List MetaEnvEntry :=
                match str_map_lookup k idx { Option.some es => es, Option.none => List.empty } in
            index_add rest e (str_map_insert k (List.cons e prev) idx),
    }

/// key -> the defs filed under it.
#[partial]
def build_index (decls : List Decl) (pos : I64) (idx : HashMap String (List MetaEnvEntry))
    : HashMap String (List MetaEnvEntry) :=
    match decls {
        List.empty => idx,
        List.cons d rest => match decl_def d {
            Option.some df =>
                let e : MetaEnvEntry := { pos := pos, decl := d } in
                build_index rest (pos + 1) (index_add (def_keys df) e idx),
            Option.none => build_index rest (pos + 1) idx,
        },
    }

struct MetaEnvClosure {
    work : List String,
    chosen : HashMap String Decl,
}

/// The prefix of the name a poisoned def's body references; lowering
/// reports it as an unresolved name, carrying the elaboration error.
pub def elaboration_failed_marker : String := "<elaboration failed> "

/// `d` with its def's body replaced by a reference lowering cannot
/// resolve, naming the def and the elaboration error.
#[partial]
pub def poisoned_decl (d : Decl) (err : String) : Decl := match d {
    Decl.def_d df =>
        let msg : String := String.concat elaboration_failed_marker
            (String.concat (show_name_path df.name) (String.concat ": " err)) in
        Decl.def_d { df with term := Term.var sentinel (DebugName.named (Identifier.id msg)) },
    Decl.scoped_open_d p f inner => Decl.scoped_open_d p f (poisoned_decl inner err),
    _ => d,
}

/// Elaborate each not-yet-chosen entry and queue what it references; a
/// def that fails to elaborate is poisoned and references nothing.
#[partial]
def take_entries (elab : Decl -> Result String Decl) (es : List MetaEnvEntry) (c : MetaEnvClosure) : MetaEnvClosure :=
    match es {
        List.empty => c,
        List.cons en rest =>
            let key : String := I64.to_string en.pos in
            match str_map_lookup key c.chosen {
                Option.some _ => take_entries elab rest c,
                Option.none =>
                    let e : Decl := match elab en.decl {
                        Result.ok ok => ok,
                        Result.err err => poisoned_decl en.decl err,
                    } in
                    let next : MetaEnvClosure :=
                        { work := decl_ref_names e c.work, chosen := str_map_insert key e c.chosen } in
                    take_entries elab rest next,
            },
    }

#[partial]
def close (elab : Decl -> Result String Decl) (idx : HashMap String (List MetaEnvEntry))
    (seen : HashMap String Bool) (c : MetaEnvClosure) : HashMap String Decl :=
    match c.work {
        List.empty => c.chosen,
        List.cons k rest =>
            let popped : MetaEnvClosure := { work := rest, chosen := c.chosen } in
            match str_map_lookup k seen {
                Option.some _ => close elab idx seen popped,
                Option.none =>
                    let seen2 := str_map_insert k true seen in
                    match str_map_lookup k idx {
                        Option.none => close elab idx seen2 popped,
                        Option.some es => close elab idx seen2 (take_entries elab es popped),
                    },
            },
    }

#[partial]
def emit_in_order (decls : List Decl) (pos : I64) (chosen : HashMap String Decl) : List Decl :=
    match decls {
        List.empty => List.empty,
        List.cons d rest => match decl_def d {
            Option.none => List.cons d (emit_in_order rest (pos + 1) chosen),
            Option.some _ => match str_map_lookup (I64.to_string pos) chosen {
                Option.some e => List.cons e (emit_in_order rest (pos + 1) chosen),
                Option.none => emit_in_order rest (pos + 1) chosen,
            },
        },
    }

/// `decls` narrowed to every non-def plus the defs reachable from `roots`,
/// each reachable def passed through `elab` exactly once (poisoned when
/// it fails), in the original order.
pub def meta_env_decls (elab : Decl -> Result String Decl) (decls : List Decl) (roots : List String) : List Decl :=
    let idx := build_index decls 0 str_map_empty in
    let start : MetaEnvClosure := { work := roots, chosen := str_map_empty } in
    emit_in_order decls 0 (close elab idx str_map_empty start)

/// Every name a declaration mentions anywhere it can spell a meta-def:
/// a def or macro body, a macro call's arguments, a decl-gen template.
#[partial]
pub def decl_all_ref_names (d : Decl) (acc : List String) : List String := match d {
    Decl.def_d df => match df { Def.mk { typ, term, .. } => term_ref_names term (term_ref_names typ acc) },
    Decl.def_macro_d df => match df { Def.mk { typ, term, .. } => term_ref_names term (term_ref_names typ acc) },
    Decl.macro_call_d _name args => terms_ref_names args acc,
    Decl.decl_gen_d _name _params inner _attrs => decls_all_ref_names inner acc,
    Decl.scoped_open_d _p _f inner => decl_all_ref_names inner acc,
    _ => acc,
}

#[partial]
pub def decls_all_ref_names (ds : List Decl) (acc : List String) : List String := match ds {
    List.empty => acc,
    List.cons d rest => decls_all_ref_names rest (decl_all_ref_names d acc),
}
