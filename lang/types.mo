type Identifier {
    id String
}

type Operator {
    operator String
}

type ModulePath {
    mp (List Identifier)
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

type Param {
    mk (name: Identifier) (type_: Term) (mult: Multiplicity) (default: Option Term)
}

/// Create a Param with multiplicity=Many and no default value.
def param_many (name: Identifier) (type_: Term) : Param :=
    let none : Option Term := Option.none in
    Param.mk name type_ Multiplicity.many none

/// Create a Param with explicit multiplicity and no default value.
def mk_param (name: Identifier) (type_: Term) (mult: Multiplicity) : Param :=
    let none : Option Term := Option.none in
    Param.mk name type_ mult none

type MatchCase {
    mc (name: Identifier) (args: List Identifier) (value: Term)
}

type NumSuffix {
    i8, i16, i32, i64, u8, u16, u32, u64, f32, f64,
}

type Literal {
    str (value: String),
    num (value: I64) (suffix: NumSuffix),
    if_ (one: Term) (two: Term) (three: Term),
    match_ (value: Term) (cases: List MatchCase),
}

type Con {
    mk (name: Identifier) (typ_name: ModulePath) (num_args: I64) (args: List (Option Term))
}

type Native {
    mk (native_name: Identifier) (num_args: I64) (args: List (Option Term))
}

type Term {
    forall (name: Identifier) (typ: Term) (body: Term),
    pi (arg: Term) (ret: Term),
    var (name: NameRef),
    lam (param: Param) (body: Term),
    app (fun: Term) (arg: Term),
    lit (value: Literal),
    ntv (native: Native),
    con (c: Con),
    type_ (universe: I64),
    hole,
}

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

type EvalError {
    undefined_var (name: NameRef),
    not_a_function (term: Term),
    match_failure (term: Term),
    custom (msg: String),
}

type TypeConstraint {
    mk (cls: ModulePath) (vars: List Identifier)
}

type Def {
    mk (name: ModulePath) (typ: Term) (term: Term) (constraints: List TypeConstraint) (attrs: List String)
}

type InductConstructor {
    mk (name: ModulePath) (params: List Param) (typ: Term)
}

type Inductive {
    mk (name: ModulePath) (params: List Param) (typ: Term) (constructors: List InductConstructor) (attrs: List String)
}

type ClassDef {
    mk (name: Identifier) (typ: Term) (default: Option Term)
}

type Class {
    mk (name: Identifier) (params: List Param) (constraints: List TypeConstraint) (methods: List ClassDef)
}

type StructField {
    mk (name: Identifier) (typ: Term) (default: Option Term)
}

type Struct {
    mk (name: Identifier) (fields: List StructField)
}

type Decl {
    def_d (Def),
    inductive_d (Inductive),
    struct_d (Struct),
    class_d (Class),
    instance_d (Instance),
    infix_d (op: Operator) (path: ModulePath),
    use_d (path: ModulePath),
    open_d (path: ModulePath),
}

type Instance {
    mk (name: Identifier) (cls: ModulePath) (constraints: List TypeConstraint) (args: List Term)
}

// --- Do-notation desugaring ---

type DoStmt {
    bind_s (name: Identifier) (expr: Term),
    let_s (name: Identifier) (expr: Term),
    ret_s (expr: Term),
    expr_s (expr: Term),
}

def monad_bind_term : Term :=
    Term.var (NameRef.nmp (ModulePath.mp (List.cons (Identifier.id "Monad") (List.cons (Identifier.id "bind") List.empty))))

def monad_pure_term : Term :=
    Term.var (NameRef.nmp (ModulePath.mp (List.cons (Identifier.id "Monad") (List.cons (Identifier.id "pure") List.empty))))

def desugar_do (stmts : List DoStmt) : Term :=
    desugar_do_inner (list_reverse stmts) (Term.app monad_pure_term (Term.hole))

def desugar_do_inner (stmts : List DoStmt) (rest : Term) : Term :=
    match stmts {
        List.cons s ss =>
            match s {
                bind_s name expr => Term.app (Term.app monad_bind_term expr) (Term.lam (param_many name (Term.hole)) (desugar_do_inner ss rest)),
                let_s name expr => Term.app (Term.lam (param_many name (Term.hole)) (desugar_do_inner ss rest)) expr,
                ret_s expr => Term.app monad_pure_term expr,
                expr_s expr => Term.app (Term.app monad_bind_term expr) (Term.lam (param_many (Identifier.id "_") (Term.hole)) (desugar_do_inner ss rest))
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
            List.empty => false
        },
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false
        }
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
            List.empty => true,
            List.cons _ _ => false
        }
    }

def opt_term_similar (a : Option Term) (b : Option Term) : Bool :=
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

def opt_term_list_similar (a : List (Option Term)) (b : List (Option Term)) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => opt_term_similar x y && opt_term_list_similar xs ys,
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
            mp ids1 => match b {
                mp ids2 => id_list_similar ids1 ids2
            }
        }
}

instance Similar NameRef {
    def similar (a : NameRef) (b : NameRef) : Bool :=
        match a {
            nid id1 => match b {
                nid id2 => Similar.similar id1 id2,
                nmp _ => false,
                nop _ => false
            },
            nmp mp1 => match b {
                nmp mp2 => Similar.similar mp1 mp2,
                nid _ => false,
                nop _ => false
            },
            nop op1 => match b {
                nop op2 => Similar.similar op1 op2,
                nid _ => false,
                nmp _ => false
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
                    Similar.similar name1 name2 && Similar.similar typ1 typ2 && I64.beq nargs1 nargs2 && opt_term_list_similar args1 args2
            }
        }
}

instance Similar Native {
    def similar (a : Native) (b : Native) : Bool :=
        match a {
            mk name1 nargs1 args1 => match b {
                mk name2 nargs2 args2 =>
                    Similar.similar name1 name2 && I64.beq nargs1 nargs2 && opt_term_list_similar args1 args2
            }
        }
}

instance Similar MatchCase {
    def similar (a : MatchCase) (b : MatchCase) : Bool :=
        match a {
            mc name1 args1 val1 => match b {
                mc name2 args2 val2 =>
                    Similar.similar name1 name2 && id_list_similar args1 args2 && Similar.similar val1 val2
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
                    && Similar.similar mult1 mult2 && opt_term_similar def1 def2
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

instance Similar Term {
    def similar (a : Term) (b : Term) : Bool :=
        match a {
            forall n1 t1 bd1 => match b {
                forall n2 t2 bd2 => Similar.similar n1 n2 && Similar.similar t1 t2 && Similar.similar bd1 bd2,
                pi _ _ => false, var _ => false, lam _ _ => false, app _ _ => false,
                lit _ => false, ntv _ => false, con _ => false, type_ _ => false, hole => false
            },
            pi a1 r1 => match b {
                pi a2 r2 => Similar.similar a1 a2 && Similar.similar r1 r2,
                forall _ _ _ => false, var _ => false, lam _ _ => false, app _ _ => false,
                lit _ => false, ntv _ => false, con _ => false, type_ _ => false, hole => false
            },
            var n1 => match b {
                var n2 => Similar.similar n1 n2,
                forall _ _ _ => false, pi _ _ => false, lam _ _ => false, app _ _ => false,
                lit _ => false, ntv _ => false, con _ => false, type_ _ => false, hole => false
            },
            lam p1 bd1 => match b {
                lam p2 bd2 => Similar.similar p1 p2 && Similar.similar bd1 bd2,
                forall _ _ _ => false, pi _ _ => false, var _ => false, app _ _ => false,
                lit _ => false, ntv _ => false, con _ => false, type_ _ => false, hole => false
            },
            app f1 a1 => match b {
                app f2 a2 => Similar.similar f1 f2 && Similar.similar a1 a2,
                forall _ _ _ => false, pi _ _ => false, var _ => false, lam _ _ => false,
                lit _ => false, ntv _ => false, con _ => false, type_ _ => false, hole => false
            },
            lit v1 => match b {
                lit v2 => Similar.similar v1 v2,
                forall _ _ _ => false, pi _ _ => false, var _ => false, lam _ _ => false,
                app _ _ => false, ntv _ => false, con _ => false, type_ _ => false, hole => false
            },
            ntv n1 => match b {
                ntv n2 => Similar.similar n1 n2,
                forall _ _ _ => false, pi _ _ => false, var _ => false, lam _ _ => false,
                app _ _ => false, lit _ => false, con _ => false, type_ _ => false, hole => false
            },
            con c1 => match b {
                con c2 => Similar.similar c1 c2,
                forall _ _ _ => false, pi _ _ => false, var _ => false, lam _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false, type_ _ => false, hole => false
            },
            type_ u1 => match b {
                type_ u2 => I64.beq u1 u2,
                forall _ _ _ => false, pi _ _ => false, var _ => false, lam _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false, con _ => false, hole => false
            },
            hole => match b {
                hole => true,
                forall _ _ _ => false, pi _ _ => false, var _ => false, lam _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false, con _ => false, type_ _ => false
            }
        }
}

def main : I64 := 42
