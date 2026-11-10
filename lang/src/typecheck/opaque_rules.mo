/// Opaque native types, and the rule that natives may not construct empty
/// types.
///
/// A type with no constructors is the empty type (`False`). A `#[native]`
/// or `#[extern "c"]` declaration returning one would assert an inhabitant
/// of `False`, so:
///
/// 1. **`#[opaque]` types declare exactly one NULLARY witness constructor.**
///    The witness is the inhabitation proof (`At`/`Cell`, `I64`…`F64`,
///    `Ptr`). The type stays abstract because the witness is unreferenceable
///    (rule 2).
/// 2. **The witness cannot be constructed or matched.** A source reference
///    to an `#[opaque]` constructor is an error, in expression position
///    (`Term.con`/`Term.var`) and in a match pattern (`MatchCase.name`).
///    `infer.mo`'s `type_check_match` additionally rejects a match on an
///    opaque SCRUTINEE type, which catches a wildcard pattern.
/// 3. **A native's result type must be inhabited.** The constructed type
///    (the `IO`/`RawIO` payload) may not be an inductive with zero
///    constructors. `Void` is the deliberate empty type and is rejected
///    when returned; a type variable or a function type is undecidable here
///    and is left alone (`Eq.rec` returns `P b e`).
///
/// All three are ERRORS in every `[affine]` mode (logical consistency is not
/// a migration warning), on the CLI, buffer and LSP paths.
use lib::types {
    Class, ClassDef, Con, DebugName, Decl, Def, Identifier, InductConstructor, Inductive,
    Instance, Literal, MatchCase, NamePath, Native, Scope, Struct, StructField, StructLitField,
    Term, TypeError, has_attr, name_map_values, show_identifier, show_name_path,
}
use lib::scope {scope_globals}
use lib::typecheck::type_kinds {kind_head_name}
use lib::typecheck::diagnostic {render_type_error}
use std::map {HashMap}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}

/// The witness constructor's names (bare and `Ind.ctor`), for every
/// `#[opaque]` inductive in scope.
pub def opaque_ctor_names (s : Scope) : HashMap String Bool :=
    let sd := scope_globals s in
    opaque_ctor_names_go (name_map_values sd.inductives) str_map_empty

#[partial]
def opaque_ctor_names_go (inds : List Inductive) (acc : HashMap String Bool) : HashMap String Bool :=
    match inds {
        List.empty => acc,
        List.cons ind rest =>
            match ind {
                Inductive.mk name _params _typ ctors attrs _vis =>
                    if has_attr (Identifier.id "opaque") attrs
                    then opaque_ctor_names_go rest (add_ctor_names name ctors acc)
                    else opaque_ctor_names_go rest acc,
            },
    }

#[partial]
def add_ctor_names (ind : NamePath) (ctors : List InductConstructor) (acc : HashMap String Bool) : HashMap String Bool :=
    match ctors {
        List.empty => acc,
        List.cons c rest =>
            match c {
                InductConstructor.mk cname _params _typ =>
                    let full : String := show_name_path cname in
                    let bare : String := match last_segment cname.segments {
                        Option.some id => show_identifier id,
                        Option.none => full,
                    } in
                    let qualified : String := String.concat (show_name_path ind) (String.concat "." bare) in
                    add_ctor_names ind rest
                        (str_map_insert qualified true (str_map_insert bare true (str_map_insert full true acc))),
            },
    }

// ─── Validation ────────────────────────────────────────────────────

pub def check_module_opaque_diags (path : Option String) (scope : Scope) (decl_list : List Decl) : List String :=
    let names : HashMap String Bool := opaque_ctor_names scope in
    opaque_diags_go path scope names decl_list

#[partial]
def opaque_diags_go (path : Option String) (scope : Scope) (names : HashMap String Bool) (decl_list : List Decl) : List String :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            List.append (opaque_diags_decl path scope names d)
                (opaque_diags_go path scope names rest),
    }

#[partial]
def opaque_diags_decl (path : Option String) (scope : Scope) (names : HashMap String Bool) (d : Decl) : List String :=
    match d {
        Decl.inductive_d ind =>
            render_errors (inductive_name ind) path (validate_opaque_inductive ind),
        Decl.def_d df =>
            if is_dict_value_def df then List.empty
            else render_errors (show_name_path df.name) path
                (List.append (opaque_refs_in_def names df)
                    (native_return_errors scope df)),
        Decl.class_d cls => render_errors (class_name cls) path (class_default_refs names cls),
        Decl.instance_d ins => render_errors (instance_name ins) path (instance_refs names ins),
        Decl.struct_d s =>
            render_errors (struct_name s) path
                (List.append (validate_opaque_struct s) (struct_default_refs names s)),
        Decl.scoped_open_d _path _filter inner => opaque_diags_decl path scope names inner,
        _ => List.empty,
    }

/// A body-less native/extern returning an empty inductive. Split into small
/// defs: a `let ... in match` cannot sit directly in an `if`'s `else` arm in
/// this parser.
pub def native_return_errors (scope : Scope) (d : Def) : List TypeError :=
    if Bool.not (def_has_no_body d.term) then List.empty
    else if Bool.not (is_native_or_extern d) then List.empty
    else native_return_errors_of scope d (native_result_type d.typ)

def native_return_errors_of (scope : Scope) (d : Def) (ret : Term) : List TypeError :=
    match kind_head_name ret {
        Option.none => List.empty,
        Option.some head => native_return_errors_head scope d head,
    }

def native_return_errors_head (scope : Scope) (d : Def) (head : String) : List TypeError :=
    match find_unique_inductive_by_name scope head {
        Option.none => List.empty,
        Option.some ind => native_return_errors_ind d ind,
    }

def native_return_errors_ind (d : Def) (ind : Inductive) : List TypeError :=
    match ind {
        Inductive.mk name _params _typ ctors _attrs _vis =>
            if List.is_empty ctors then empty_return_error d name else List.empty,
    }

def empty_return_error (d : Def) (name : NamePath) : List TypeError :=
    List.cons (TypeError.custom
        (String.concat "native `" (String.concat (show_name_path d.name)
            (String.concat "` returns the empty type `" (String.concat (show_name_path name)
                "` (no constructors); a native may not construct an empty/False type -- give it a witness constructor or return an inhabited wrapper")))))
        List.empty

#[partial]
def find_unique_inductive_by_name (s : Scope) (head : String) : Option Inductive :=
    let sd := scope_globals s in
    find_unique_inductive_go (name_map_values sd.inductives) head Option.none 0

#[partial]
def find_unique_inductive_go (inds : List Inductive) (head : String) (found : Option Inductive) (n : I64) : Option Inductive :=
    match inds {
        List.empty => if I64.beq n 1 then found else Option.none,
        List.cons ind rest =>
            match ind {
                Inductive.mk name _params _typ _ctors _attrs _vis =>
                    if String.beq (show_name_path name) head || name_matches_bare name head
                    then find_unique_inductive_go rest head (Option.some ind) (n + 1)
                    else find_unique_inductive_go rest head found n,
            },
    }

#[partial]
def name_matches_bare (name : NamePath) (head : String) : Bool :=
    match last_segment name.segments {
        Option.some id => String.beq (show_identifier id) head,
        Option.none => false,
    }

#[partial]
def last_segment (segs : List Identifier) : Option Identifier :=
    match segs {
        List.empty => Option.none,
        List.cons x rest =>
            match rest {
                List.empty => Option.some x,
                List.cons _ _ => last_segment rest,
            },
    }

/// Peel `ctx`/`pi` to the codomain, then `IO`/`RawIO` to the payload.
#[partial]
def native_result_type (t : Term) : Term :=
    io_payload (pi_codomain t)

#[partial]
def pi_codomain (t : Term) : Term :=
    match t {
        Term.ctx _loc inner => pi_codomain inner,
        Term.pi _b _arg ret => pi_codomain ret,
        _ => t,
    }

#[partial]
def io_payload (t : Term) : Term :=
    match t {
        Term.ctx _loc inner => io_payload inner,
        Term.app f arg =>
            match kind_head_name f {
                Option.some n =>
                    if String.beq n "IO" || String.beq n "RawIO" then arg else t,
                Option.none => t,
            },
        _ => t,
    }

def is_native_or_extern (d : Def) : Bool :=
    has_attr (Identifier.id "native") d.attrs || has_attr (Identifier.id "extern") d.attrs

#[terminating]
def def_has_no_body (t : Term) : Bool :=
    match t {
        Term.ctx _loc inner => def_has_no_body inner,
        Term.lam _b _typ body => def_has_no_body body,
        Term.hole => true,
        _ => false,
    }

#[partial]
def inductive_name (ind : Inductive) : String :=
    match ind {
        Inductive.mk name _params _typ _ctors _attrs _vis => show_name_path name,
    }

#[partial]
def validate_opaque_inductive (ind : Inductive) : List TypeError :=
    match ind {
        Inductive.mk name _params _typ ctors attrs _vis =>
            if Bool.not (has_attr (Identifier.id "opaque") attrs) then List.empty
            else validate_opaque_ctors name ctors,
    }

#[partial]
def validate_opaque_ctors (name : NamePath) (ctors : List InductConstructor) : List TypeError :=
    match ctors {
        List.empty =>
            List.cons (TypeError.custom
                (String.concat "opaque type `" (String.concat (show_name_path name)
                    "` has no constructors; declare exactly one nullary witness constructor (an empty inductive is False)")))
                List.empty,
        List.cons c rest =>
            match rest {
                List.empty => validate_opaque_witness name c,
                List.cons _ _ =>
                    List.cons (TypeError.custom
                        (String.concat "opaque type `" (String.concat (show_name_path name)
                            "` declares more than one constructor; it must have exactly one nullary witness")))
                        List.empty,
            },
    }

/// An opaque type must be a `type` declaration with one nullary witness,
/// NOT a `struct`: a struct literal (`T { }`) constructs the struct's
/// constructor without ever naming it, which would bypass the opaque
/// constructor ban. Reject every `#[opaque] struct`.
#[partial]
def validate_opaque_struct (s : Struct) : List TypeError :=
    match s {
        Struct.mk name _fields attrs _vis =>
            if has_attr (Identifier.id "opaque") attrs
            then List.cons (TypeError.custom
                (String.concat "opaque struct `" (String.concat (show_identifier name)
                    "`: an opaque type must be declared as a `type` with one nullary witness constructor, not a struct (a struct literal would bypass the witness ban)")))
                List.empty
            else List.empty,
    }

#[partial]
def validate_opaque_witness (name : NamePath) (c : InductConstructor) : List TypeError :=
    match c {
        InductConstructor.mk _cname params _typ =>
            if List.is_empty params then List.empty
            else List.cons (TypeError.custom
                (String.concat "opaque type `" (String.concat (show_name_path name)
                    "`'s witness constructor must be nullary; an opaque value comes from its natives, not from source")))
                List.empty,
    }

// ─── Constructor references ────────────────────────────────────────

#[partial]
def opaque_refs_in_def (names : HashMap String Bool) (d : Def) : List TypeError :=
    if def_has_no_body d.term then List.empty
    else match opaque_ref_in_term names d.term {
        Option.none => List.empty,
        Option.some hit => List.cons (opaque_witness_ref_error hit) List.empty,
    }

def opaque_witness_ref_error (hit : String) : TypeError :=
    TypeError.custom
        (String.concat "`" (String.concat hit
            "` is an `#[opaque]` witness constructor; it may be neither constructed nor matched (values come from the type's natives)"))

#[partial]
def opaque_ref_in_term (names : HashMap String Bool) (t : Term) : Option String :=
    match t {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => name_in_opaque_set names (show_identifier id),
                DebugName.unnamed => Option.none,
            },
        Term.var_macro _idx _dbg => Option.none,
        Term.lam _b _typ body => opaque_ref_in_term names body,
        Term.pi _b arg ret =>
            match opaque_ref_in_term names arg {
                Option.some hit => Option.some hit,
                Option.none => opaque_ref_in_term names ret,
            },
        Term.app callee arg =>
            match opaque_ref_in_term names callee {
                Option.some hit => Option.some hit,
                Option.none => opaque_ref_in_term names arg,
            },
        Term.lit value => opaque_ref_in_literal names value,
        Term.ntv n =>
            match n {
                Native.mk _name _num args => opaque_ref_in_opt_args names args,
            },
        Term.con c =>
            match c {
                Con.mk cname _typ_name _num args =>
                    match name_in_opaque_set names (show_identifier cname) {
                        Option.some hit => Option.some hit,
                        Option.none => opaque_ref_in_opt_args names args,
                    },
            },
        Term.cubical c => match c { { prim := _, args := args } => opaque_ref_in_terms names args },
        Term.elim e =>
            match e {
                { inductive := _, levels := _, params := _, indices := _,
                    motive := _, minors := minors, scrutinee := scrutinee } =>
                        match opaque_ref_in_term names scrutinee {
                            Option.some hit => Option.some hit,
                            Option.none => opaque_ref_in_terms names minors,
                        },
            },
        Term.sort _level => Option.none,
        Term.hole => Option.none,
        // A quote is syntax as data, not a value; a name inside it is not
        // constructed or matched.
        Term.quote_ _inner => Option.none,
        Term.ctx _loc inner => opaque_ref_in_term names inner,
    }

def name_in_opaque_set (names : HashMap String Bool) (n : String) : Option String :=
    match str_map_lookup n names {
        Option.some _ => Option.some n,
        Option.none => Option.none,
    }

#[partial]
def opaque_ref_in_literal (names : HashMap String Bool) (l : Literal) : Option String :=
    match l {
        Literal.str _v => Option.none,
        Literal.char _v => Option.none,
        Literal.num _n _suf => Option.none,
        Literal.flt _t _suf => Option.none,
        Literal.if_ cond then_ else_ =>
            first_some (opaque_ref_in_term names cond)
                (first_some (opaque_ref_in_term names then_) (opaque_ref_in_term names else_)),
        Literal.match_ scrut cases =>
            first_some (opaque_ref_in_term names scrut) (opaque_ref_in_cases names cases),
        Literal.struct_lit fields _type_name => opaque_ref_in_fields names fields,
        Literal.struct_update base fields =>
            first_some (opaque_ref_in_term names base) (opaque_ref_in_fields names fields),
    }

#[partial]
def opaque_ref_in_cases (names : HashMap String Bool) (cases : List MatchCase) : Option String :=
    match cases {
        List.empty => Option.none,
        List.cons c rest =>
            match c {
                MatchCase.mk cname _args body _fp _typ_name =>
                    match name_in_opaque_set names (show_identifier cname) {
                        Option.some hit => Option.some hit,
                        Option.none =>
                            first_some (opaque_ref_in_term names body) (opaque_ref_in_cases names rest),
                    },
            },
    }

#[partial]
def opaque_ref_in_fields (names : HashMap String Bool) (fields : List StructLitField) : Option String :=
    match fields {
        List.empty => Option.none,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value =>
                    first_some (opaque_ref_in_term names value) (opaque_ref_in_fields names rest),
            },
    }

#[partial]
def opaque_ref_in_opt_args (names : HashMap String Bool) (args : List (Option Term)) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons a rest =>
            match a {
                Option.some t => first_some (opaque_ref_in_term names t) (opaque_ref_in_opt_args names rest),
                Option.none => opaque_ref_in_opt_args names rest,
            },
    }

#[partial]
def opaque_ref_in_terms (names : HashMap String Bool) (ts : List Term) : Option String :=
    match ts {
        List.empty => Option.none,
        List.cons t rest => first_some (opaque_ref_in_term names t) (opaque_ref_in_terms names rest),
    }

def first_some {A : Type} (a : Option A) (b : Option A) : Option A :=
    match a {
        Option.some _ => a,
        Option.none => b,
    }

#[partial]
def class_default_refs (names : HashMap String Bool) (cls : Class) : List TypeError :=
    match cls {
        Class.mk _name _params _constraints methods _vis _ => class_default_refs_go names methods,
    }

#[partial]
def class_default_refs_go (names : HashMap String Bool) (methods : List ClassDef) : List TypeError :=
    match methods {
        List.empty => List.empty,
        List.cons m rest =>
            match m {
                ClassDef.mk _name _typ default =>
                    List.append (opt_ref_errors names default) (class_default_refs_go names rest),
            },
    }

#[partial]
def instance_refs (names : HashMap String Bool) (ins : Instance) : List TypeError :=
    match ins {
        Instance.mk _name _cls _constraints _args _vis _implicit defs =>
            defs_ref_errors names defs,
    }

#[partial]
def defs_ref_errors (names : HashMap String Bool) (defs : List Def) : List TypeError :=
    match defs {
        List.empty => List.empty,
        List.cons df rest => List.append (opaque_refs_in_def names df) (defs_ref_errors names rest),
    }

#[partial]
def struct_default_refs (names : HashMap String Bool) (s : Struct) : List TypeError :=
    match s {
        Struct.mk _name fields _attrs _vis => struct_default_refs_go names fields,
    }

#[partial]
def struct_default_refs_go (names : HashMap String Bool) (fields : List StructField) : List TypeError :=
    match fields {
        List.empty => List.empty,
        List.cons f rest =>
            match f {
                StructField.mk _name _typ default _mult =>
                    List.append (opt_ref_errors names default) (struct_default_refs_go names rest),
            },
    }

#[partial]
def opt_ref_errors (names : HashMap String Bool) (t : Option Term) : List TypeError :=
    match t {
        Option.none => List.empty,
        Option.some body =>
            match opaque_ref_in_term names body {
                Option.none => List.empty,
                Option.some hit => List.cons (opaque_witness_ref_error hit) List.empty,
            },
    }

#[partial]
def class_name (cls : Class) : String :=
    match cls { Class.mk name _params _constraints _methods _vis _ => show_identifier name }

#[partial]
def instance_name (ins : Instance) : String :=
    match ins { Instance.mk name _cls _constraints _args _vis _implicit _defs => show_identifier name }

#[partial]
def struct_name (s : Struct) : String :=
    match s { Struct.mk name _fields _attrs _vis => show_identifier name }

// ─── Rendering ─────────────────────────────────────────────────────

#[partial]
def render_errors (context_name : String) (path : Option String) (errs : List TypeError) : List String :=
    match errs {
        List.empty => List.empty,
        List.cons e rest =>
            List.cons (render_type_error context_name path e)
                (render_errors context_name path rest),
    }

#[partial]
def is_dict_value_def (df : Def) : Bool :=
    String.starts_with "__Dict_" (last_name_segment (show_name_path df.name))

#[partial]
def last_name_segment (s : String) : String :=
    let idx : I64 := last_sep_index s 0 (String.length s) (0 - 1) in
    if I64.lt idx 0 then s
    else String.slice s (idx + 2) (String.length s - idx - 2)

#[partial]
def last_sep_index (s : String) (i : I64) (n : I64) (found : I64) : I64 :=
    if I64.gt (i + 2) n then found
    else if String.beq (String.slice s i 2) "::" then last_sep_index s (i + 1) n i
    else last_sep_index s (i + 1) n found
