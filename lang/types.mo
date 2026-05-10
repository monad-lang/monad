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

type Param {
    mk (name: Identifier) (type_: Term)
}

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

type Instance {
    mk (name: Identifier) (cls: ModulePath) (constraints: List TypeConstraint) (args: List Term)
}

def main : I64 := 42
