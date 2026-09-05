/// Free-variable and referenced-name analysis over `Term`.
///
/// Two families of pure traversal, extracted from
/// `lang/codegen/emit.mo` because each has two unrelated consumers and
/// so belongs to neither:
///
/// * `free_names_of_term` is binder-AWARE. It is what closure capture
///   uses to decide a lambda's environment, and what
///   `lang.codegen.qualify` uses to report an ambiguous reference --
///   the latter specifically because it must NOT count a local binder
///   as a reference (a match binder named `param_name` once made the
///   compiler report an ambiguity that did not exist).
/// * `collect_referenced_names` is binder-BLIND, and deliberately so:
///   reachability may safely over-approximate, and cheaply. Do not
///   reach for it where precision matters -- that is the other one.
use lang.types {
  Con, DebugName, FieldPattern, FieldPatternEntry, Identifier, Literal, MatchCase,
  Native, StructLitField, Term,
}
use lang.codegen.symbols {symbol_identifier}
use lang.codegen.util {ident_in_list, identifier_eq}
use std.map {}

#[partial]
def free_names_of_term (bound : List Identifier) (t : Term) : List Identifier := match t {
    Term.var _idx dbg => free_names_of_dbg bound dbg,
    Term.var_macro _idx dbg => free_names_of_dbg bound dbg,
    Term.lam dbg typ_ body_ =>
        List.append (free_names_of_term bound typ_)
            (free_names_of_term (add_bound_name bound dbg) body_),
    Term.forall dbg kind body_ =>
        List.append (free_names_of_term bound kind)
            (free_names_of_term (add_bound_name bound dbg) body_),
    Term.pi arg ret => List.append (free_names_of_term bound arg) (free_names_of_term bound ret),
    Term.app fun_ arg_ => List.append (free_names_of_term bound fun_) (free_names_of_term bound arg_),
    Term.lit lit_ => free_names_of_lit bound lit_,
    Term.ntv native => free_names_of_native bound native,
    Term.con c => free_names_of_con bound c,
    Term.type_ _universe => List.empty,
    Term.hole => List.empty,
    Term.quote_ inner => free_names_of_term bound inner,
}

#[partial]
def add_bound_name (bound : List Identifier) (dbg : DebugName) : List Identifier := match dbg {
    DebugName.named id_ => List.cons id_ bound,
    DebugName.unnamed => bound,
}

#[partial]
def free_names_of_dbg (bound : List Identifier) (dbg : DebugName) : List Identifier := match dbg {
    DebugName.named id_ => if ident_in_list bound id_ then List.empty else List.cons id_ List.empty,
    DebugName.unnamed => List.empty,
}

#[partial]
def free_names_of_lit (bound : List Identifier) (lit_ : Literal) : List Identifier := match lit_ {
    Literal.num _n _s => List.empty,
    Literal.flt _t _s => List.empty,
    Literal.str _s => List.empty,
    Literal.if_ cond then_ else_ =>
        List.append (free_names_of_term bound cond)
            (List.append (free_names_of_term bound then_) (free_names_of_term bound else_)),
    Literal.match_ scrutinee cases =>
        List.append (free_names_of_term bound scrutinee) (free_names_of_cases bound cases),
    Literal.struct_lit fields type_name =>
        List.append (free_names_of_struct_fields bound fields) (free_names_of_opt_term bound type_name),
    Literal.struct_update base fields =>
        List.append (free_names_of_term bound base) (free_names_of_struct_fields bound fields),
}

#[partial]
def free_names_of_opt_term (bound : List Identifier) (ot : Option Term) : List Identifier := match ot {
    Option.some t => free_names_of_term bound t,
    Option.none => List.empty,
}

#[partial]
def free_names_of_struct_fields (bound : List Identifier) (fields : List StructLitField) : List Identifier := match fields {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            StructLitField.mk _name value =>
                List.append (free_names_of_term bound value) (free_names_of_struct_fields bound rest),
        },
}

/// Each case's own `args` (and, defensively, its `field_pattern`
/// binders -- even though `field_pattern` isn't wired into codegen's
/// own match-arm binding yet, a separate pre-existing gap) shadow
/// `bound` inside that case's `body` ONLY, not its siblings.
#[partial]
def free_names_of_cases (bound : List Identifier) (cases : List MatchCase) : List Identifier := match cases {
    List.empty => List.empty,
    List.cons case_ rest =>
        match case_ {
            MatchCase.mc _name args body_ field_pattern =>
                let bound2 := add_field_pattern_bound (List.append args bound) field_pattern in
                List.append (free_names_of_term bound2 body_) (free_names_of_cases bound rest),
        },
}

#[partial]
def add_field_pattern_bound (bound : List Identifier) (fp : Option FieldPattern) : List Identifier := match fp {
    Option.some pat => match pat { FieldPattern.mk entries _rest => add_field_pattern_entries bound entries },
    Option.none => bound,
}

#[partial]
def add_field_pattern_entries (bound : List Identifier) (entries : List FieldPatternEntry) : List Identifier := match entries {
    List.empty => bound,
    List.cons e rest =>
        match e { FieldPatternEntry.mk _field binder => add_field_pattern_entries (List.cons binder bound) rest },
}

#[partial]
def free_names_of_native (bound : List Identifier) (n : Native) : List Identifier := match n {
    Native.mk _name _num_args args => free_names_of_opt_list bound args,
}

/// `c`'s own `name` is the constructor TAG, not a variable reference --
/// deliberately excluded (unlike `collect_referenced_names_con`, whose
/// reachability purpose needs it; free-var capture doesn't).
#[partial]
def free_names_of_con (bound : List Identifier) (c : Con) : List Identifier := match c {
    Con.mk _name _typ_name _num_args args => free_names_of_opt_list bound args,
}

#[partial]
def free_names_of_opt_list (bound : List Identifier) (args : List (Option Term)) : List Identifier := match args {
    List.empty => List.empty,
    List.cons opt_ rest =>
        match opt_ {
            Option.some t => List.append (free_names_of_term bound t) (free_names_of_opt_list bound rest),
            Option.none => free_names_of_opt_list bound rest,
        },
}

/// Collects every name referenced anywhere inside a Term -- variable
/// references, constructor names, match-case pattern names -- into
/// `acc`. Over-approximates deliberately (see reachable_defs_from's doc
/// comment): also picks up local/bound names that happen to shadow a
/// top-level Def name, but that's harmless here (worst case, an
/// unrelated same-named top-level def gets kept too).
#[partial]
def collect_referenced_names (t : Term) (acc : List String) : List String := match t {
    Term.var _idx dbg =>
        match dbg {
            DebugName.named id => List.cons (symbol_identifier id) acc,
            DebugName.unnamed => acc,
        },
    Term.lam _dbg typ body => collect_referenced_names body (collect_referenced_names typ acc),
    Term.forall _dbg kind body => collect_referenced_names body (collect_referenced_names kind acc),
    Term.pi arg ret => collect_referenced_names ret (collect_referenced_names arg acc),
    Term.app fun_ arg_ => collect_referenced_names arg_ (collect_referenced_names fun_ acc),
    Term.ntv native => collect_referenced_names_native native acc,
    Term.con con_ => collect_referenced_names_con con_ acc,
    Term.lit lit_ => collect_referenced_names_lit lit_ acc,
    Term.type_ _universe => acc,
    Term.hole => acc,
}

/// Now total (no `#[partial]`) — `struct_lit`/`struct_update` are
/// unreachable in practice (see `compile_lit_ir`'s matching doc
/// comment), but reachability analysis should still be correct for
/// them independent of that: a name referenced only from inside a
/// struct-literal field value (or a struct-update override/base) must
/// not be stripped as dead code.
def collect_referenced_names_lit (l : Literal) (acc : List String) : List String := match l {
    Literal.num _n _suffix => acc,
    Literal.flt _text _suffix => acc,
    Literal.str _s => acc,
    Literal.if_ cond then_ else_ => collect_referenced_names else_ (collect_referenced_names then_ (collect_referenced_names cond acc)),
    Literal.match_ scrutinee cases => collect_referenced_names_cases cases (collect_referenced_names scrutinee acc),
    Literal.struct_lit fields _type_name => collect_referenced_names_struct_fields fields acc,
    Literal.struct_update base fields => collect_referenced_names_struct_fields fields (collect_referenced_names base acc),
}

#[partial]
def collect_referenced_names_struct_fields (fields : List StructLitField) (acc : List String) : List String :=
    match fields {
        List.empty => acc,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value => collect_referenced_names_struct_fields rest (collect_referenced_names value acc),
            }
    }

#[partial]
def collect_referenced_names_cases (cases : List MatchCase) (acc : List String) : List String := match cases {
    List.empty => acc,
    List.cons c rest =>
        match c {
            MatchCase.mc name _args body _fp =>
                collect_referenced_names_cases rest (List.cons (symbol_identifier name) (collect_referenced_names body acc)),
        },
}

#[partial]
def collect_referenced_names_native (n : Native) (acc : List String) : List String := match n {
    Native.mk _name _num_args args => collect_referenced_names_opt_list args acc,
}

#[partial]
def collect_referenced_names_con (c : Con) (acc : List String) : List String := match c {
    Con.mk name _typ_name _num_args args => List.cons (symbol_identifier name) (collect_referenced_names_opt_list args acc),
}

#[partial]
def collect_referenced_names_opt_list (args : List (Option Term)) (acc : List String) : List String := match args {
    List.empty => acc,
    List.cons opt_ rest =>
        match opt_ {
            Option.some t => collect_referenced_names_opt_list rest (collect_referenced_names t acc),
            Option.none => collect_referenced_names_opt_list rest acc,
        },
}