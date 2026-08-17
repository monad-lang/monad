use std.show {Show}
// `ScopeData.def_refs` below is a `std.map` `HashMap ModulePath ScopeDef`.
// This import is required here (not just at `scope_data_empty`'s own
// call sites in `lang/scope.mo`) — a real, isolated evaluator
// limitation: a nullary class method like `Map.empty` (no argument
// whose runtime constructor tag the interpreter could otherwise
// dispatch on, unlike `Map.insert`/`Map.lookup`) fails at runtime with
// `unresolved global: Map.empty` unless `std.map`'s `Map` instances are
// also in scope in the module that DECLARES the struct field's type,
// even when every call site already imports `std.map` itself. Empty
// import: naming any of `std.map`'s `Map`-class-instance exports
// explicitly hits a separate, pre-existing latent instance/dictionary-
// resolution bug (`std/map_tests.mo`'s own documented workaround).
use std.map {}

type Identifier {
    id String
}

/// Compare two identifiers for equality (by string value).
def id_eq (a : Identifier) (b : Identifier) : Bool :=
    match a {
        Identifier.id as => match b {
            Identifier.id bs => String.beq as bs,
        },
    }

instance BEq Identifier {
    def beq (a b : Identifier) : Bool := id_eq a b
}


/// Check if an identifier is in a list of identifiers.
def id_member (id : Identifier) (ids : List Identifier) : Bool :=
    match ids {
        List.cons hd rest => if id_eq id hd then true else id_member id rest,
        List.empty => false,
    }

/// Union two lists of identifiers (deduplicated, left-biased order).
def union_ids (a : List Identifier) (b : List Identifier) : List Identifier :=
    match a {
        List.cons hd rest =>
            if id_member hd b
            then union_ids rest b
            else List.cons hd (union_ids rest b),
        List.empty => b,
    }
type Operator {
    operator String
}

type ModulePath {
    mp (List Identifier)
}

def show_identifier (id : Identifier) : String := match id {
    Identifier.id s => s,
}

def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

def show_module_path (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => join_identifiers ids,
}

def join_identifiers (ids : List Identifier) : String := match ids {
    List.empty => "",
    List.cons hd rest => join_id_rest hd rest,
}

def join_id_rest (hd : Identifier) (rest : List Identifier) : String :=
    match rest {
        List.empty => show_identifier hd,
        List.cons x y =>
            let dot := String.concat (show_identifier hd) "." in
            let rest_str := join_id_rest x y in
            String.concat dot rest_str,
        _ => show_identifier hd
    }


instance Show ModulePath {
    def show (mp : ModulePath) : String := show_module_path mp
}

/// Identifiers can't contain ".", so the dotted-string-join used by
/// show_identifier/show_module_path is collision-free as an ordering key.
instance BOrd Identifier {
    def lt (a b : Identifier) : Bool := BOrd.lt (show_identifier a) (show_identifier b)
    def gt (a b : Identifier) : Bool := BOrd.gt (show_identifier a) (show_identifier b)
}

instance BOrd ModulePath {
    def lt (a b : ModulePath) : Bool := BOrd.lt (show_module_path a) (show_module_path b)
    def gt (a b : ModulePath) : Bool := BOrd.gt (show_module_path a) (show_module_path b)
}

/// Same "collision-free as a string key" property `BOrd`'s own
/// delegation above already relies on — hash the dotted-string join
/// rather than writing a separate combining hash over the segment list.
/// Needed for `lang/scope.mo`'s `ScopeData.def_refs` to use
/// `std.map`'s `HashMap ModulePath ScopeDef` (see
/// `bench/scope_lookup.mo` for why: at realistic sizes, `HashMap`
/// clearly outperforms both `List`+linear-scan and `BTreeMap` for
/// scope's lookup-heavy access pattern).
instance Hashable Identifier {
    def hash (a : Identifier) : U64 := String.hash (show_identifier a)
}

instance Hashable ModulePath {
    def hash (mp : ModulePath) : U64 := String.hash (show_module_path mp)
}

type NameRef {
    nid (Identifier),
    nmp (ModulePath),
    nop (Operator),
}

type Multiplicity {
    zero,
    many,
    linear,
    affine,
}

struct Location {
    offset : I64,
    line : I64,
    column : I64,
}

struct SourceRange {
    start : Location,
    end : Location,
    path : Option String,
}

struct LocatedSpan {
    fragment : String,
    location : Location,
}

// Canonical Param uses de Bruijn Term. ParamV0 is the legacy V0 variant.
type Param {
    mk (name: Identifier) (type_: Term) (mult: Multiplicity) (default: Option Term)
}

/// Create a canonical Param with multiplicity=Many and no default value.
def param_many (name: Identifier) (type_: Term) : Param :=
    let none : Option Term := Option.none in
    Param.mk name type_ Multiplicity.many none

/// Create a canonical Param with explicit multiplicity and no default value.
def mk_param (name: Identifier) (type_: Term) (mult: Multiplicity) : Param :=
    let none : Option Term := Option.none in
    Param.mk name type_ mult none

// Canonical MatchCase uses de Bruijn Term. MatchCaseV0 is the legacy V0 variant.
type MatchCase {
    mc (name: Identifier) (args: List Identifier) (body: Term)
}

type NumSuffix {
    i8, i16, i32, i64, u8, u16, u32, u64, f32, f64,
}

// Canonical Literal uses de Bruijn Term. LiteralV0 is the legacy V0 variant.
type Literal {
    str (value: String),
    num (value: I64) (suffix: NumSuffix),
    /// A literal written with a decimal point (`3.0`, `3.14f32`). Kept as
    /// the exact source text rather than a numeric value: self-hosted
    /// Monad code has no native bridge to parse a decimal string into an
    /// actual float bit pattern (unlike the Rust reference's
    /// `Literal::Float { value: F64Wrap, .. }`, core/src/term.rs), so
    /// `text` is the only representation available here — sufficient for
    /// round-tripping through `show_term`/parsing back, though genuine
    /// float codegen (`lang/codegen/emit.mo` has no float `LLVMValue`
    /// variant at all yet) remains a separate, unstarted piece of work.
    flt (text: String) (suffix: NumSuffix),
    if_ (one: Term) (two: Term) (three: Term),
    match_ (value: Term) (cases: List MatchCase),
}

type Con {
    mk (name: Identifier) (typ_name: ModulePath) (num_args: I64) (args: List (Option Term))
}

type Native {
    mk (native_name: Identifier) (num_args: I64) (args: List (Option Term))
}

// Optional debug name carried by de Bruijn variables and binders.
// Names are never used for identity or equality — de Bruijn indices
// determine identity. DebugName exists solely for error messages
// and pretty-printing during debugging.
type DebugName {
    named (id: Identifier),
    unnamed,
}

/// Visibility of a declaration. Mirrors the Rust reference's
/// `core::term::Visibility` exactly: `priv` is enforced immediately
/// (module boundaries already exist), `pub` vs. the default
/// `package_private` is a no-op until a package system exists. Applies to
/// `def`/`type`/`class`/`struct`/`instance`/`infix` — NOT `use` (which
/// gets its own separate `public: Bool` field directly on `Decl.use_d`,
/// since `priv use` isn't a real form) or `open` (no visibility concept
/// at all).
type Visibility {
    pub_,
    priv_,
    package_private,
}

type ParamV0 {
    mk (name: Identifier) (type_: TermV0) (mult: Multiplicity) (default: Option TermV0)
}

/// Create a ParamV0 with multiplicity=Many and no default value.
def param_many_v0 (name: Identifier) (type_: TermV0) : ParamV0 :=
    let none : Option TermV0 := Option.none in
    ParamV0.mk name type_ Multiplicity.many none

/// Create a ParamV0 with explicit multiplicity and no default value.
def mk_param_v0 (name: Identifier) (type_: TermV0) (mult: Multiplicity) : ParamV0 :=
    let none : Option TermV0 := Option.none in
    ParamV0.mk name type_ mult none


type MatchCaseV0 {
    mc_v0 (name: Identifier) (args: List Identifier) (value: TermV0)
}

type LiteralV0 {
    str (value: String),
    num (value: I64) (suffix: NumSuffix),
    if_ (one: TermV0) (two: TermV0) (three: TermV0),
    match_ (value: TermV0) (cases: List MatchCaseV0),
}

/// ParseTerm
type TermV0 {
    forall (name: Identifier) (typ: TermV0) (body: TermV0),
    pi (arg: TermV0) (ret: TermV0),
    var (name: NameRef),
    lam (param: ParamV0) (body: TermV0),
    app (fun: TermV0) (arg: TermV0),
    lit (value: LiteralV0),
    ntv (native: Native),
    con (c: Con),
    type_ (universe: I64),
    ctx (loc : SourceRange) (term : Term),
    hole,
}

// De Bruijn TermV0 IR — staged alongside existing named TermV0.
// Phase 0: coexistence. Phase 4: replaces TermV0 entirely.
//
// De Bruijn convention: index 0 = most recently bound variable.
// Free variables use sentinel index (I64.max) and are resolved
// by the type checker or module resolver.
type Term {
    var (idx: I64) (dbg: DebugName),
    lam (dbg: DebugName) (typ: Term) (body: Term),
    forall (dbg: DebugName) (kind: Term) (body: Term),
    pi (arg: Term) (ret: Term),
    app (fun: Term) (arg: Term),
    lit (value: Literal),
    ntv (native: Native),
    con (c: Con),
    type_ (universe: I64),
    hole,
}

/// Canonical TypeError uses de Bruijn Term. TypeErrorV0 is the legacy V0 variant.
type TypeError {
    mismatch (expected: Term) (actual: Term),
    unknown_var (name: NameRef),
    unknown_type (name: NameRef),
    unknown_constructor (name: NameRef),
    not_a_function (term: Term),
    not_a_type (term: Term),
    infinite_type (term: Term),
    custom (msg: String),
}

/// Canonical EvalError uses de Bruijn Term. EvalErrorV0 is the legacy V0 variant.
type EvalError {
    undefined_var (name: NameRef),
    not_a_function (term: Term),
    match_failure (term: Term),
    custom (msg: String),
}

type TypeConstraint {
    mk (cls: ModulePath) (vars: List Identifier)
}

/// Canonical Def uses de Bruijn Term. DefV0 is the legacy V0 variant.
struct Def {
    name: ModulePath,
    typ: Term,
    term: Term,
    constraints: List TypeConstraint,
    attrs: List String,
    vis: Visibility
}

def Def.name (d : Def) : ModulePath :=
    match d {
        mk name _ _ _ _ _ => name
    }

// Canonical InductConstructor uses de Bruijn Term. InductConstructorV0 is the legacy V0 variant.
type InductConstructor {
    mk (name: ModulePath) (params: List Param) (typ: Term)
}

// Canonical Inductive uses de Bruijn Term. InductiveV0 is the legacy V0 variant.
type Inductive {
    mk (name: ModulePath) (params: List Param) (typ: Term) (constructors: List InductConstructor) (attrs: List String) (vis: Visibility)
}

// Canonical ClassDef uses de Bruijn Term. ClassDefV0 is the legacy V0 variant.
type ClassDef {
    mk (name: Identifier) (typ: Term) (default: Option Term)
}

// Canonical Class uses de Bruijn Term. ClassV0 is the legacy V0 variant.
type Class {
    mk (name: Identifier) (params: List Param) (constraints: List TypeConstraint) (methods: List ClassDef) (vis: Visibility)
}

// Canonical StructField uses de Bruijn Term. StructFieldV0 is the legacy V0 variant.
type StructField {
    /// `mult` mirrors the Rust reference's `StructField.mult`
    /// (core/src/term.rs): `!name : T` (Linear, must be consumed exactly
    /// once), `?name : T` (Affine, at most once), `%name : T` (Zero /
    /// Erased), or no prefix at all (Many, the default — the common
    /// case). See examples/structs.mo's `Buffer.data` for a live `!` use.
    mk (name: Identifier) (typ: Term) (default: Option Term) (mult: Multiplicity)
}


// Canonical Struct uses de Bruijn Term. StructV0 is the legacy V0 variant.
type Struct {
    mk (name: Identifier) (fields: List StructField) (vis: Visibility)
}

/// A single item inside a `use Module { ... }` brace filter. Mirrors the
/// Rust host's `UseItem` (core/src/term.rs).
type UseItem {
    use_name (name: Identifier),
    use_rename (name: Identifier) (alias: Identifier),
    use_glob,
    use_sub (name: Identifier) (items: List UseItem),
    use_sub_rename (name: Identifier) (alias: Identifier) (items: List UseItem),
}

/// What names a `use` declaration imports. Bare `use Module` (no braces)
/// is deprecated but still parses. Mirrors Rust's `UseFilter`.
type UseFilter {
    use_bare,
    use_items (items: List UseItem),
}

/// What names an `open` declaration makes unqualified. Mirrors Rust's
/// `OpenFilter`.
type OpenFilter {
    open_all,
    open_only (names: List Identifier),
}

// Canonical Decl uses de Bruijn Term. DeclV0 is the legacy variant.
type Decl {
    def_d (Def),
    inductive_d (Inductive),
    struct_d (Struct),
    class_d (Class),
    instance_d (Instance),
    infix_d (op: Operator) (path: ModulePath) (vis: Visibility),
    use_d (path: ModulePath) (filter: UseFilter) (public: Bool),
    open_d (path: ModulePath) (filter: OpenFilter),
    /// `open ModulePath [{filter}] in <decl>` — the module is opened only
    /// for the scope of the wrapped declaration (def/type/struct/class/
    /// instance). Mirrors Rust's `Decl::ScopedOpen`.
    scoped_open_d (path: ModulePath) (filter: OpenFilter) (decl: Decl),
}

def Decl.to_name (d : Decl) : ModulePath :=
    match d {
        def_d def_ => Def.name def_,
        _ => ModulePath.mp []
    }

// Canonical Instance uses de Bruijn Term. InstanceV0 is the legacy V0 variant.
type Instance {
    /// `implicit_params` holds any `{Name : Type}` binders written right
    /// after `instance` (before the optional `[constraints]` and the class
    /// name), e.g. `instance {A : Type} Show A { ... }`. Mirrors the Rust
    /// reference's `Instance.params` (core/src/term.rs) — load-bearing for
    /// instance resolution there (substitution-based matching against a
    /// lookup key's args), not just documentation. Empty for the common
    /// case of a fully-concrete instance like `instance Show Bool { ... }`.
    mk (name: Identifier) (cls: ModulePath) (constraints: List TypeConstraint) (args: List Term) (vis: Visibility) (implicit_params: List Param)
}

// --- Do-notation desugaring ---

// --- Do-notation desugaring ---
// Canonical DoStmt uses de Bruijn Term. DoStmtV0 is the legacy V0 variant.


// `bind_s`/`let_s` carry the statement's own declared type (`Term.hole`
// when unannotated, e.g. `let x <- expr;`/`let x := expr;`) -- without
// it, `desugar_do_inner` had no way to give the desugared binder a real
// type even when the source explicitly wrote one (`let x : T <- expr;`),
// which broke downstream typecheck precision for that binding (e.g.
// match-case validation on a do-block-bound value whose real type WAS
// written down, just never threaded through -- see
// plans/bootstrapping/self-hosted-compiler.md's changelog for the
// lang/main.mo `main` repro this was found from).
type DoStmt {
    bind_s (name: Identifier) (typ: Term) (expr: Term),
    let_s (name: Identifier) (typ: Term) (expr: Term),
    ret_s (expr: Term),
    expr_s (expr: Term),
}

def monad_bind_term : Term :=
    Term.var (-1) (DebugName.unnamed)

def monad_pure_term : Term :=
    Term.var (-1) (DebugName.unnamed)

def desugar_do (stmts : List DoStmt) : Term :=
    desugar_do_inner (list_reverse stmts) (Term.app monad_pure_term Term.hole)

def desugar_do_inner (stmts : List DoStmt) (rest : Term) : Term :=
    match stmts {
        List.cons s ss =>
            match s {
                bind_s name typ expr =>
                    Term.app (Term.app monad_bind_term expr)
                        (Term.lam (DebugName.named name) typ (desugar_do_inner ss rest)),
                let_s name typ expr =>
                    Term.app (Term.lam (DebugName.named name) typ (desugar_do_inner ss rest)) expr,
                ret_s expr => Term.app monad_pure_term expr,
                expr_s expr =>
                    Term.app (Term.app monad_bind_term expr)
                        (Term.lam (DebugName.unnamed) Term.hole (desugar_do_inner ss rest))
            },
        List.empty => rest
    }

def list_rev_loop {A : Type} (xs : List A) (acc : List A) : List A :=
    match xs {
        List.cons x rest => list_rev_loop rest (List.cons x acc),
        List.empty => acc
    }

def list_reverse {A : Type} (xs : List A) : List A :=
    list_rev_loop xs List.empty

// --- Similar class for structural comparison ---

class Similar A {
    def similar (a : A) (b : A) : Bool
}

instance Similar Identifier {
    def similar (a : Identifier) (b : Identifier) : Bool :=
        match a {
            id s1 => match b {
                id s2 => String.beq s1 s2
            }
        }
}

instance Similar Operator {
    def similar (a : Operator) (b : Operator) : Bool :=
        match a {
            operator s1 => match b {
                operator s2 => String.beq s1 s2
            }
        }
}

// List helpers (avoid generic constrained instance due to solver limitation)
def id_list_similar (a : List Identifier) (b : List Identifier) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => Similar.similar x y && id_list_similar xs ys,
            List.empty => false,
            _ => false
        },
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false,
            _ => false
        },
        _ => false
    }

def mc_list_similar (a : List MatchCase) (b : List MatchCase) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => Similar.similar x y && mc_list_similar xs ys,
            List.empty => false
        },
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false
        }
    }

def param_list_similar (a : List Param) (b : List Param) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => Similar.similar x y && param_list_similar xs ys,
            List.empty => false
        },
        List.empty => match b {
            List.cons y ys => false,
            List.empty => true
        }
    }

def opt_db_term_similar (a : Option Term) (b : Option Term) : Bool :=
    match a {
        Option.some x => match b {
            Option.some y => Similar.similar x y,
            Option.none => false
        },
        Option.none => match b {
            Option.none => true,
            Option.some _ => false
        }
    }

def opt_db_term_list_similar (a : List (Option Term)) (b : List (Option Term)) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => opt_db_term_similar x y && opt_db_term_list_similar xs ys,
            List.empty => false
        },
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false
        }
    }

instance Similar ModulePath {
    def similar (a : ModulePath) (b : ModulePath) : Bool :=
        match a {
            ModulePath.mp ids1 => match b {
                ModulePath.mp ids2 => id_list_similar ids1 ids2,
                _ => false
            },
            _ => false
        }
}

instance Similar NameRef {
    def similar (a : NameRef) (b : NameRef) : Bool :=
        match a {
            NameRef.nid id1 => match b {
                NameRef.nid id2 => Similar.similar id1 id2,
                NameRef.nmp _ => false,
                NameRef.nop _ => false
            },
            NameRef.nmp mp1 => match b {
                NameRef.nmp mp2 => Similar.similar mp1 mp2,
                NameRef.nid _ => false,
                NameRef.nop _ => false
            },
            NameRef.nop op1 => match b {
                NameRef.nop op2 => Similar.similar op1 op2,
                NameRef.nid _ => false,
                NameRef.nmp _ => false
            }
        }
}

instance Similar NumSuffix {
    def similar (a : NumSuffix) (b : NumSuffix) : Bool :=
        match a {
            i8 => match b {
                i8 => true, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            i16 => match b {
                i8 => false, i16 => true, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            i32 => match b {
                i8 => false, i16 => false, i32 => true, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            i64 => match b {
                i8 => false, i16 => false, i32 => false, i64 => true,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            u8 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => true, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            u16 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => true, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            u32 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => true, u64 => false,
                f32 => false, f64 => false
            },
            u64 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => true,
                f32 => false, f64 => false
            },
            f32 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => true, f64 => false
            },
            f64 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => true
            }
        }
}

instance Similar Con {
    def similar (a : Con) (b : Con) : Bool :=
        match a {
            mk name1 typ1 nargs1 args1 => match b {
                mk name2 typ2 nargs2 args2 =>
                    Similar.similar name1 name2 && Similar.similar typ1 typ2 && I64.beq nargs1 nargs2 && opt_db_term_list_similar args1 args2
            }
        }
}

instance Similar Native {
    def similar (a : Native) (b : Native) : Bool :=
        match a {
            mk name1 nargs1 args1 => match b {
                mk name2 nargs2 args2 =>
                    Similar.similar name1 name2 && I64.beq nargs1 nargs2 && opt_db_term_list_similar args1 args2
            }
        }
}

instance Similar MatchCase {
    def similar (a : MatchCase) (b : MatchCase) : Bool :=
        match a {
            mc name1 args1 body1 => match b {
                mc name2 args2 body2 =>
                    Similar.similar name1 name2 && id_list_similar args1 args2 && Similar.similar body1 body2
            }
        }
}

instance Similar Multiplicity {
    def similar (a : Multiplicity) (b : Multiplicity) : Bool :=
        match a {
            zero => match b { zero => true, many => false, linear => false, affine => false },
            many => match b { zero => false, many => true, linear => false, affine => false },
            linear => match b { zero => false, many => false, linear => true, affine => false },
            affine => match b { zero => false, many => false, linear => false, affine => true }
        }
}

instance Similar Param {
    def similar (a : Param) (b : Param) : Bool :=
        match a {
            mk name1 typ1 mult1 def1 => match b {
                mk name2 typ2 mult2 def2 =>
                    Similar.similar name1 name2 && Similar.similar typ1 typ2
                    && Similar.similar mult1 mult2 && opt_db_term_similar def1 def2
            }
        }
}

instance Similar Location {
    def similar (a : Location) (b : Location) : Bool :=
        match a {
            mk off1 line1 col1 => match b {
                mk off2 line2 col2 =>
                    I64.beq off1 off2 && I64.beq line1 line2 && I64.beq col1 col2
            }
        }
}

def opt_str_similar (a : Option String) (b : Option String) : Bool :=
    match a {
        Option.some x => match b {
            Option.some y => String.beq x y,
            Option.none => false
        },
        Option.none => match b {
            Option.none => true,
            Option.some _ => false
        }
    }

instance Similar SourceRange {
    def similar (a : SourceRange) (b : SourceRange) : Bool :=
        match a {
            mk start1 end1 path1 => match b {
                mk start2 end2 path2 =>
                    Similar.similar start1 start2 && Similar.similar end1 end2 && opt_str_similar path1 path2
            }
        }
}

instance Similar Literal {
    def similar (a : Literal) (b : Literal) : Bool :=
        match a {
            str s1 => match b {
                str s2 => String.beq s1 s2,
                num _ _ => false, if_ _ _ _ => false, match_ _ _ => false
            },
            num v1 s1 => match b {
                num v2 s2 => I64.beq v1 v2 && Similar.similar s1 s2,
                str _ => false, if_ _ _ _ => false, match_ _ _ => false
            },
            if_ o1 t1 th1 => match b {
                if_ o2 t2 th2 => Similar.similar o1 o2 && Similar.similar t1 t2 && Similar.similar th1 th2,
                str _ => false, num _ _ => false, match_ _ _ => false
            },
            match_ v1 cs1 => match b {
                match_ v2 cs2 => Similar.similar v1 v2 && mc_list_similar cs1 cs2,
                str _ => false, num _ _ => false, if_ _ _ _ => false
            }
        }
}


// --- Similar instances for de Bruijn types (Phase 0) ---

instance Similar DebugName {
    def similar (a : DebugName) (b : DebugName) : Bool :=
        match a {
            named id1 => match b {
                named id2 => Similar.similar id1 id2,
                unnamed => false
            },
            unnamed => match b {
                unnamed => true,
                named _ => false
            }
        }
}

instance Similar Term {
    def similar (a : Term) (b : Term) : Bool :=
        match a {
            var i1 d1 => match b {
                var i2 d2 => I64.beq i1 i2 && Similar.similar d1 d2,
                lam _ _ _ => false, forall _ _ _ => false, pi _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            lam d1 t1 bd1 => match b {
                lam d2 t2 bd2 => Similar.similar d1 d2 && Similar.similar t1 t2 && Similar.similar bd1 bd2,
                var _ _ => false, forall _ _ _ => false, pi _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            forall d1 k1 bd1 => match b {
                forall d2 k2 bd2 => Similar.similar d1 d2 && Similar.similar k1 k2 && Similar.similar bd1 bd2,
                var _ _ => false, lam _ _ _ => false, pi _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            pi a1 r1 => match b {
                pi a2 r2 => Similar.similar a1 a2 && Similar.similar r1 r2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            app f1 a1 => match b {
                app f2 a2 => Similar.similar f1 f2 && Similar.similar a1 a2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            lit v1 => match b {
                lit v2 => Similar.similar v1 v2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            ntv n1 => match b {
                ntv n2 => Similar.similar n1 n2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, lit _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            con c1 => match b {
                con c2 => Similar.similar c1 c2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, lit _ => false,
                ntv _ => false, type_ _ => false, hole => false
            },
            type_ u1 => match b {
                type_ u2 => I64.beq u1 u2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, lit _ => false,
                ntv _ => false, con _ => false, hole => false
            },
            hole => match b {
                hole => true,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, lit _ => false,
                ntv _ => false, con _ => false, type_ _ => false
            }
        }
}

// ─── Term construction tests (Phase 0) ─────────────────────────────

#[test]
def test_term_var : Bool :=
    let v : Term := Term.var 0 (DebugName.named (Identifier.id "x")) in
    true

#[test]
def test_term_lam : Bool :=
    let body : Term := Term.var 0 (DebugName.unnamed) in
    let l : Term := Term.lam DebugName.unnamed body body in
    true

#[test]
def test_term_forall : Bool :=
    let body : Term := Term.var 0 (DebugName.unnamed) in
    let f : Term := Term.forall DebugName.unnamed body body in
    true

#[test]
def test_term_pi : Bool :=
    let arg : Term := Term.type_ 1 in
    let ret : Term := Term.type_ 1 in
    let p : Term := Term.pi arg ret in
    true

#[test]
def test_term_dep_pi : Bool :=
    // Dependent pi: pi Nat (var 0 "n") — ret references arg at index 0
    let arg : Term := Term.type_ 0 in
    let ret : Term := Term.var 0 (DebugName.named (Identifier.id "n")) in
    let p : Term := Term.pi arg ret in
    true

#[test]
def test_term_app : Bool :=
    let f : Term := Term.var 0 (DebugName.unnamed) in
    let a : Term := Term.var 1 (DebugName.unnamed) in
    let app : Term := Term.app f a in
    true

#[test]
def test_term_lit : Bool :=
    let l : Term := Term.lit (Literal.str "hello") in
    true

#[test]
def test_term_ntv : Bool :=
    // Work around Native.mk forall-inference bug with List.empty
    // by using a non-empty list of args
    let none_opt : Option Term := Option.none in
    let args : List (Option Term) := List.cons none_opt List.empty in
    let ntv_val : Native := Native.mk (Identifier.id "foo") 0 args in
    let n : Term := Term.ntv ntv_val in
    true

#[test]
def test_term_con : Bool :=
    // Work around Con.mk/ModulePath.mp forall-inference bugs with List.empty
    // by using non-empty lists
    let none_opt : Option Term := Option.none in
    let args : List (Option Term) := List.cons none_opt List.empty in
    let mod_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Test") List.empty) in
    let con_val : Con := Con.mk (Identifier.id "Bar") mod_path 0 args in
    let c : Term := Term.con con_val in
    true

#[test]
def test_term_type : Bool :=
    let t : Term := Term.type_ 0 in
    true

#[test]
def test_term_hole : Bool :=
    let h : Term := Term.hole in
    true

// --- Phase 2: Scope types ---

// Infix operator binding. Maps an operator symbol to a definition path.
struct Infix {
    operator : Operator,
    name : ModulePath,
}

// Instance lookup key.
struct InstanceKey {
    cls : ModulePath,
    constraints : List TypeConstraint,
    args : List Param,
}

// A resolved definition entry in scope.
struct ScopeDef {
    name : ModulePath,
    module : ModulePath,
    sig : Term,
    body : Term,
}

// A class method entry in scope.
struct ScopeClassDef {
    class_name : ModulePath,
    full_name : ModulePath,
    name : Identifier,
    sig : Term,
}

// Instance entries grouped by class name.
struct ScopeInstance {
    class_name : ModulePath,
    instances : List Instance,
}

// Conflicting name resolution entry.
struct ScopeConflict {
    name : ModulePath,
    candidates : List ModulePath,
}

// Local variable in the scope chain.
struct LocalVar {
    name : Identifier,
    typ : Term,
    multiplicity : Multiplicity,
}

// All resolved entries for a single scope level.
struct ScopeData {
    def_refs : HashMap ModulePath ScopeDef,
    class_defs : List ScopeClassDef,
    instances : List ScopeInstance,
    inductives : List Inductive,
    classes : List Inductive,
    infixes : List Infix,
    conflicts : List ScopeConflict,
}

// A scope node in the linked list.
struct Scope {
    module_id : ModulePath,
    scope : ScopeData,
    parent : Option Scope,
}

// Compiled or loaded module entry.
struct Module {
    path : ModulePath,
    inductives : List Inductive,
    defs : List ScopeDef,
    infixs : List Infix,
    instances : List ScopeInstance,
}

// Global map of loaded module paths to modules.
struct LoadedModules {
    modules : List Module,
}

// Scope for local bindings (let expressions, case arms, lambda vars).
struct LocalScope {
    vars : List LocalVar,
    parent : Option LocalScope,
}

// Error type for scope resolution failures.
type ScopeError {
    name_not_found (name : NameRef),
    ambiguous_name (name : NameRef) (candidates : List ModulePath),
    inductive_not_found (name : ModulePath),
    instance_not_found (key : InstanceKey),
    class_not_found (name : ModulePath),
    linear_used_twice (name : Identifier),
    affine_used_multiple (name : Identifier),
}

/// Returns true if the Result is ok, false if err.
def result_is_ok {E A : Type} (r : Result E A) : Bool :=
    match r {
        Result.ok _ => true,
        Result.err _ => false,
    }
