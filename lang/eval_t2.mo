use lang.types
open Term2
open DebugName

// ─── Term2 environment-based evaluator ─────────────────────────────────
// Evaluates Term2 using an environment (stack of values for de Bruijn
// indices). Call-by-value semantics. de Bruijn index 0 = head of env.

type T2EvalEnv {
    t2e_empty,
    t2e_push (val: Term2) (rest: T2EvalEnv),
}

open T2EvalEnv

// Look up a de Bruijn index in the evaluation environment.
// Index 0 = most recently pushed value (head of env).
@[partial]
def t2e_lookup (env: T2EvalEnv) (idx: I64) : Option Term2 :=
    match env {
        t2e_empty => Option.none,
        t2e_push val rest =>
            if I64.beq idx 0
            then Option.some val
            else t2e_lookup rest (idx - 1)
    }

type T2EvalResult {
    t2e_ok (v: Term2),
    t2e_err (msg: String),
}

open T2EvalResult

/// Evaluate a Term2 under an environment.
/// Call-by-value: lambdas are values, apps evaluate fun and arg first,
/// then if fun is a lam, push arg onto env and evaluate the body.
@[partial]
def t2e_eval (term: Term2) (env: T2EvalEnv) : T2EvalResult :=
    match term {
        var idx dbg =>
            match t2e_lookup env idx {
                Option.some val => t2e_eval val env,
                Option.none => t2e_err "unbound variable"
            },
        lam dbg typ body => t2e_ok term,
        forall dbg kind body => t2e_ok term,
        pi arg ret => t2e_ok term,
        app fun arg =>
            match t2e_eval fun env {
                t2e_ok fun_val =>
                    match t2e_eval arg env {
                        t2e_ok arg_val =>
                            match fun_val {
                                lam dbg typ body =>
                                    t2e_eval body (t2e_push arg_val env),
                                var idx dbg => t2e_ok (Term2.app fun_val arg_val),
                                app f a => t2e_ok (Term2.app fun_val arg_val),
                                lit v => t2e_ok (Term2.app fun_val arg_val),
                                ntv n => t2e_ok (Term2.app fun_val arg_val),
                                con c => t2e_ok (Term2.app fun_val arg_val),
                                type_ u => t2e_ok (Term2.app fun_val arg_val),
                                hole => t2e_ok (Term2.app fun_val arg_val),
                                forall dbg k b => t2e_ok (Term2.app fun_val arg_val),
                                pi a r => t2e_ok (Term2.app fun_val arg_val)
                            },
                        t2e_err msg => t2e_err msg
                    },
                t2e_err msg => t2e_err msg
            },
        lit val => t2e_ok term,
        ntv native_val => t2e_ok term,
        con con_val => t2e_ok term,
        type_ universe_val => t2e_ok term,
        hole => t2e_ok term
    }

// ─── Term2 evaluator tests ────────────────────────────────────────────

@[test]
def test_t2e_lit : Bool :=
    let t : Term2 := Term2.lit (Literal.str "hello") in
    match t2e_eval t t2e_empty {
        t2e_ok v =>
            match v {
                lit l =>
                    match l {
                        str s => String.beq s "hello",
                        num n s => false,
                        if_ c t_ e_ => false,
                        match_ v_ cs_ => false
                    },
                var i d => false,
                lam d ty b => false,
                forall d k b => false,
                pi a r => false,
                app f a => false,
                ntv n => false,
                con c => false,
                type_ u => false,
                hole => false
            },
        t2e_err msg => false
    }

@[test]
def test_t2e_identity : Bool :=
    // (λx. x) 42 → 42
    let body : Term2 := Term2.var 0 DebugName.unnamed in
    let lam : Term2 := Term2.lam DebugName.unnamed (Term2.type_ 1) body in
    let arg : Term2 := Term2.lit (Literal.num 42 NumSuffix.i64) in
    let app : Term2 := Term2.app lam arg in
    match t2e_eval app t2e_empty {
        t2e_ok v =>
            match v {
                lit l =>
                    match l {
                        num n s => I64.beq n 42,
                        str s => false,
                        if_ c t_ e_ => false,
                        match_ v_ cs_ => false
                    },
                var i d => false,
                lam d ty b => false,
                forall d k b => false,
                pi a r => false,
                app f a => false,
                ntv n => false,
                con c => false,
                type_ u => false,
                hole => false
            },
        t2e_err msg => false
    }

@[test]
def test_t2e_lam_value : Bool :=
    // λx. x is a value already
    let body : Term2 := Term2.var 0 DebugName.unnamed in
    let lam : Term2 := Term2.lam DebugName.unnamed (Term2.type_ 1) body in
    match t2e_eval lam t2e_empty {
        t2e_ok v =>
            match v {
                lam dbg typ b => true,
                var i d => false,
                forall d k b => false,
                pi a r => false,
                app f a => false,
                lit l => false,
                ntv n => false,
                con c => false,
                type_ u => false,
                hole => false
            },
        t2e_err msg => false
    }

@[test]
def test_t2e_nested_app : Bool :=
    // (λx. λy. y) 10 "world" → "world"
    let inner_body : Term2 := Term2.var 0 DebugName.unnamed in
    let inner_lam : Term2 := Term2.lam DebugName.unnamed (Term2.type_ 1) inner_body in
    let outer_lam : Term2 := Term2.lam DebugName.unnamed (Term2.type_ 1) inner_lam in
    let arg1 : Term2 := Term2.lit (Literal.num 10 NumSuffix.i64) in
    let arg2 : Term2 := Term2.lit (Literal.str "world") in
    let app : Term2 := Term2.app (Term2.app outer_lam arg1) arg2 in
    match t2e_eval app t2e_empty {
        t2e_ok v =>
            match v {
                lit l =>
                    match l {
                        str s => String.beq s "world",
                        num n s => false,
                        if_ c t_ e_ => false,
                        match_ v_ cs_ => false
                    },
                var i d => false,
                lam d ty b => false,
                forall d k b => false,
                pi a r => false,
                app f a => false,
                ntv n => false,
                con c => false,
                type_ u => false,
                hole => false
            },
        t2e_err msg => false
    }

@[test]
def test_t2e_shadowing : Bool :=
    // (λx. λx. x) 1 2 → 2  (inner x shadows outer)
    let inner_body : Term2 := Term2.var 0 DebugName.unnamed in
    let inner_lam : Term2 := Term2.lam DebugName.unnamed (Term2.type_ 1) inner_body in
    let outer_lam : Term2 := Term2.lam DebugName.unnamed (Term2.type_ 1) inner_lam in
    let one : Term2 := Term2.lit (Literal.num 1 NumSuffix.i64) in
    let two : Term2 := Term2.lit (Literal.num 2 NumSuffix.i64) in
    let app : Term2 := Term2.app (Term2.app outer_lam one) two in
    match t2e_eval app t2e_empty {
        t2e_ok v =>
            match v {
                lit l =>
                    match l {
                        num n s => I64.beq n 2,
                        str s => false,
                        if_ c t_ e_ => false,
                        match_ v_ cs_ => false
                    },
                var i d => false,
                lam d ty b => false,
                forall d k b => false,
                pi a r => false,
                app f a => false,
                ntv n => false,
                con c => false,
                type_ u => false,
                hole => false
            },
        t2e_err msg => false
    }

@[test]
def test_t2e_env_lookup : Bool :=
    // Resolve var 0 from explicit env
    let val_term : Term2 := Term2.lit (Literal.num 99 NumSuffix.i64) in
    let env : T2EvalEnv := t2e_push val_term t2e_empty in
    let var_term : Term2 := Term2.var 0 DebugName.unnamed in
    match t2e_eval var_term env {
        t2e_ok v =>
            match v {
                lit l =>
                    match l {
                        num n s => I64.beq n 99,
                        str s => false,
                        if_ c t_ e_ => false,
                        match_ v_ cs_ => false
                    },
                var i d => false,
                lam d ty b => false,
                forall d k b => false,
                pi a r => false,
                app f a => false,
                ntv n => false,
                con c => false,
                type_ u => false,
                hole => false
            },
        t2e_err msg => false
    }

@[test]
def test_t2e_ntv_value : Bool :=
    // native terms are values
    let none_opt : Option Term := Option.none in
    let args : List (Option Term) := List.cons none_opt List.empty in
    let nval : Native := Native.mk (Identifier.id "add") 0 args in
    let n : Term2 := Term2.ntv nval in
    match t2e_eval n t2e_empty {
        t2e_ok v =>
            match v {
                ntv n2 => true,
                var i d => false,
                lam d ty b => false,
                forall d k b => false,
                pi a r => false,
                app f a => false,
                lit l => false,
                con c => false,
                type_ u => false,
                hole => false
            },
        t2e_err msg => false
    }

@[test]
def test_t2e_con_value : Bool :=
    // constructors are values
    let none_opt : Option Term := Option.none in
    let args : List (Option Term) := List.cons none_opt List.empty in
    let mod_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "T") List.empty) in
    let cval : Con := Con.mk (Identifier.id "C") mod_path 0 args in
    let c : Term2 := Term2.con cval in
    match t2e_eval c t2e_empty {
        t2e_ok v =>
            match v {
                con c2 => true,
                var i d => false,
                lam d ty b => false,
                forall d k b => false,
                pi a r => false,
                app f a => false,
                lit l => false,
                ntv n => false,
                type_ u => false,
                hole => false
            },
        t2e_err msg => false
    }

@[test]
def test_t2e_unbound_var : Bool :=
    // unresolvable variable should be an error
    let v : Term2 := Term2.var 0 DebugName.unnamed in
    match t2e_eval v t2e_empty {
        t2e_ok v => false,
        t2e_err msg => true
    }

def main : I64 := 42
