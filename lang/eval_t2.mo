use lang.types
use lang.eval_term
open Term
open DebugName

// ─── Term environment-based evaluator ─────────────────────────────────
// Evaluates Term using an environment (stack of values for de Bruijn
// indices). Call-by-value semantics. de Bruijn index 0 = head of env.

type T2EvalEnv {
    t2e_empty,
    t2e_push (val: Term) (rest: T2EvalEnv),
}

open T2EvalEnv

// Look up a de Bruijn index in the evaluation environment.
// Index 0 = most recently pushed value (head of env).
@[partial]
def t2e_lookup (env: T2EvalEnv) (idx: I64) : Option Term :=
    match env {
        t2e_empty => Option.none,
        t2e_push val rest =>
            if I64.beq idx 0
            then Option.some val
            else t2e_lookup rest (idx - 1)
    }

type T2EvalResult {
    t2e_ok (v: Term),
    t2e_err (msg: String),
}

open T2EvalResult

/// Evaluate a Term under an environment.
/// Call-by-value: lambdas are values, apps evaluate fun and arg first,
/// then if fun is a lam, push arg onto env and evaluate the body.
@[partial]
def t2e_eval (term: Term) (env: T2EvalEnv) : T2EvalResult :=
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
                                var idx dbg => t2e_ok (Term.app fun_val arg_val),
                                app f a => t2e_ok (Term.app fun_val arg_val),
                                lit v => t2e_ok (Term.app fun_val arg_val),
                                ntv n => t2e_ok (Term.app fun_val arg_val),
                                con c => t2e_ok (Term.app fun_val arg_val),
                                type_ u => t2e_ok (Term.app fun_val arg_val),
                                hole => t2e_ok (Term.app fun_val arg_val),
                                forall dbg k b => t2e_ok (Term.app fun_val arg_val),
                                pi a r => t2e_ok (Term.app fun_val arg_val)
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

// ─── Term evaluator tests ────────────────────────────────────────────

@[test]
def test_t2e_lit : Bool :=
    let t : Term := Term.lit (Literal.str "hello") in
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
    let body : Term := Term.var 0 DebugName.unnamed in
    let lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) body in
    let arg : Term := Term.lit (Literal.num 42 NumSuffix.i64) in
    let app : Term := Term.app lam arg in
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
    let body : Term := Term.var 0 DebugName.unnamed in
    let lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) body in
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
    let inner_body : Term := Term.var 0 DebugName.unnamed in
    let inner_lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) inner_body in
    let outer_lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) inner_lam in
    let arg1 : Term := Term.lit (Literal.num 10 NumSuffix.i64) in
    let arg2 : Term := Term.lit (Literal.str "world") in
    let app : Term := Term.app (Term.app outer_lam arg1) arg2 in
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
    let inner_body : Term := Term.var 0 DebugName.unnamed in
    let inner_lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) inner_body in
    let outer_lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) inner_lam in
    let one : Term := Term.lit (Literal.num 1 NumSuffix.i64) in
    let two : Term := Term.lit (Literal.num 2 NumSuffix.i64) in
    let app : Term := Term.app (Term.app outer_lam one) two in
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
    let val_term : Term := Term.lit (Literal.num 99 NumSuffix.i64) in
    let env : T2EvalEnv := t2e_push val_term t2e_empty in
    let var_term : Term := Term.var 0 DebugName.unnamed in
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
    let none_opt : Option TermV0 := Option.none in
    let args : List (Option TermV0) := List.cons none_opt List.empty in
    let nval : Native := Native.mk (Identifier.id "add") 0 args in
    let n : Term := Term.ntv nval in
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
    let none_opt : Option TermV0 := Option.none in
    let args : List (Option TermV0) := List.cons none_opt List.empty in
    let mod_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "T") List.empty) in
    let cval : Con := Con.mk (Identifier.id "C") mod_path 0 args in
    let c : Term := Term.con cval in
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
    let v : Term := Term.var 0 DebugName.unnamed in
    match t2e_eval v t2e_empty {
        t2e_ok v => false,
        t2e_err msg => true
    }

// ─── Term to EvalTerm lowerer ───────────────────────────────────────
// Direct mapping (no find_index needed — de Bruijn indices preserved).

/// Lower a Term to EvalTerm.
/// De Bruijn indices pass through unchanged: Term.var i → EvalTerm.evar i.
/// forall and pi are erased (type-level only at eval time).
@[partial]
def lower_t2 (t: Term) : EvalTerm :=
    match t {
        var idx dbg =>
            EvalTerm.evar idx,
        lam dbg typ body =>
            let lowered_body : EvalTerm := lower_t2 body in
            EvalTerm.elam Multiplicity.many (EvalTerm.eregion Region.r_stack Multiplicity.many lowered_body),
        forall dbg kind body =>
            lower_t2 body,
        pi arg ret =>
            EvalTerm.esort 1,
        app fun arg =>
            EvalTerm.eapp (lower_t2 fun) (lower_t2 arg),
        lit value =>
            match value {
                str s => EvalTerm.elit (EvalLiteral.l_str s),
                num n suffix => EvalTerm.elit (EvalLiteral.l_int n),
                if_ cond then_ else_ => EvalTerm.elit (EvalLiteral.l_bool true),
                match_ scrutinee cases =>
                    let scrutinee_term : EvalTerm := EvalTerm.econst 0 in
                    EvalTerm.erecursor (RecursorInfo.mk 0 0 0) (List.empty : List EvalTerm) scrutinee_term
            },
        ntv native_val =>
            match native_val {
                mk native_name nargs args => EvalTerm.eprim 0 (List.empty : List EvalTerm)
            },
        con con_val =>
            match con_val {
                mk name typ nargs args => EvalTerm.econst 0
            },
        type_ level =>
            EvalTerm.esort level,
        hole =>
            EvalTerm.elit (EvalLiteral.l_int 0)
    }

// ─── Lowerer tests ───────────────────────────────────────────────────

@[test]
def test_lower_t2_var : Bool :=
    // De Bruijn index preserved directly
    let t : Term := Term.var 3 DebugName.unnamed in
    let lowered : EvalTerm := lower_t2 t in
    match lowered {
        EvalTerm.evar idx => I64.beq idx 3,
        EvalTerm.elam m b => false,
        EvalTerm.eapp f a => false,
        EvalTerm.econst i => false,
        EvalTerm.esort l => false,
        EvalTerm.elit l => false,
        EvalTerm.eprim i args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
    }

@[test]
def test_lower_t2_lam : Bool :=
    // Lambda lowers to EvalTerm.elam(body lowered with region)
    let body : Term := Term.var 0 DebugName.unnamed in
    let lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) body in
    let lowered : EvalTerm := lower_t2 lam in
    match lowered {
        EvalTerm.elam m b => true,
        EvalTerm.evar i => false,
        EvalTerm.eapp f a => false,
        EvalTerm.econst i => false,
        EvalTerm.esort l => false,
        EvalTerm.elit l => false,
        EvalTerm.eprim i args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
    }

@[test]
def test_lower_t2_app : Bool :=
    // Application lowers to EvalTerm.eapp
    let f : Term := Term.var 0 DebugName.unnamed in
    let a : Term := Term.var 1 DebugName.unnamed in
    let app : Term := Term.app f a in
    let lowered : EvalTerm := lower_t2 app in
    match lowered {
        EvalTerm.eapp fun arg => true,
        EvalTerm.evar i => false,
        EvalTerm.elam m b => false,
        EvalTerm.econst i => false,
        EvalTerm.esort l => false,
        EvalTerm.elit l => false,
        EvalTerm.eprim i args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
    }

@[test]
def test_lower_t2_lit_num : Bool :=
    // Number literal lowers to l_int
    let t : Term := Term.lit (Literal.num 42 NumSuffix.i64) in
    let lowered : EvalTerm := lower_t2 t in
    match lowered {
        EvalTerm.elit lit =>
            match lit {
                EvalLiteral.l_int n => I64.beq n 42,
                EvalLiteral.l_str s => false,
                EvalLiteral.l_float s => false,
                EvalLiteral.l_bool b => false,
                EvalLiteral.l_sort s => false
            },
        EvalTerm.evar i => false,
        EvalTerm.elam m b => false,
        EvalTerm.eapp f a => false,
        EvalTerm.econst i => false,
        EvalTerm.esort l => false,
        EvalTerm.eprim i args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
    }

@[test]
def test_lower_t2_lit_str : Bool :=
    // String literal lowers to l_str
    let t : Term := Term.lit (Literal.str "hello") in
    let lowered : EvalTerm := lower_t2 t in
    match lowered {
        EvalTerm.elit lit =>
            match lit {
                EvalLiteral.l_str s => String.beq s "hello",
                EvalLiteral.l_int n => false,
                EvalLiteral.l_float s => false,
                EvalLiteral.l_bool b => false,
                EvalLiteral.l_sort s => false
            },
        EvalTerm.evar i => false,
        EvalTerm.elam m b => false,
        EvalTerm.eapp f a => false,
        EvalTerm.econst i => false,
        EvalTerm.esort l => false,
        EvalTerm.eprim i args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
    }

@[test]
def test_lower_t2_forall_erase : Bool :=
    // forall erases to body
    let body : Term := Term.var 0 DebugName.unnamed in
    let f : Term := Term.forall DebugName.unnamed (Term.type_ 1) body in
    let lowered : EvalTerm := lower_t2 f in
    match lowered {
        EvalTerm.evar idx => true,
        EvalTerm.elam m b => false,
        EvalTerm.eapp ap1 ap2 => false,
        EvalTerm.econst i => false,
        EvalTerm.esort l => false,
        EvalTerm.elit l => false,
        EvalTerm.eprim i args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
    }

@[test]
def test_lower_t2_pi_erase : Bool :=
    // pi erases to EvalTerm.esort
    let t : Term := Term.pi (Term.type_ 1) (Term.type_ 1) in
    let lowered : EvalTerm := lower_t2 t in
    match lowered {
        EvalTerm.esort level => true,
        EvalTerm.evar i => false,
        EvalTerm.elam m b => false,
        EvalTerm.eapp f a => false,
        EvalTerm.econst i => false,
        EvalTerm.elit l => false,
        EvalTerm.eprim i args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
    }

@[test]
def test_lower_t2_type : Bool :=
    // type_ level passes through as EvalTerm.esort
    let t : Term := Term.type_ 2 in
    let lowered : EvalTerm := lower_t2 t in
    match lowered {
        EvalTerm.esort level => I64.beq level 2,
        EvalTerm.evar i => false,
        EvalTerm.elam m b => false,
        EvalTerm.eapp f a => false,
        EvalTerm.econst i => false,
        EvalTerm.elit l => false,
        EvalTerm.eprim i args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
    }

// ─── End-to-end: Term → lower_t2 → keval ────────────────────────────

// Inline keval to avoid cross-module import.
type KEvalEnv {
    kev_empty,
    kev_push (val: EvalTerm) (rest: KEvalEnv),
}

open KEvalEnv

type KEvalResult {
    kev_ok (v: EvalTerm),
    kev_err (msg: String),
}

open KEvalResult

@[partial]
def kev_lookup (env: KEvalEnv) (idx: I64) : Option EvalTerm :=
    match env {
        kev_empty => Option.none,
        kev_push val rest =>
            if I64.beq idx 0
            then Option.some val
            else kev_lookup rest (idx - 1)
    }

@[partial]
def kev_eval (term: EvalTerm) (env: KEvalEnv) : KEvalResult :=
    match term {
        EvalTerm.evar idx =>
            match kev_lookup env idx {
                Option.some val => kev_eval val env,
                Option.none => kev_err "unbound variable"
            },
        EvalTerm.eapp fun arg =>
            match kev_eval fun env {
                kev_ok fun_val =>
                    match kev_eval arg env {
                        kev_ok arg_val =>
                            match fun_val {
                                EvalTerm.elam mult body =>
                                    kev_eval body (kev_push arg_val env),
                                EvalTerm.evar idx => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.eapp f a => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.econst idx => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.esort level => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.elit lit => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.eprim idx args => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.erecursor info cases s => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.eregion r m b => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.eborrow r k b => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.eproj f a => kev_ok (EvalTerm.eapp fun_val arg_val),
                                EvalTerm.eproj_field f b => kev_ok (EvalTerm.eapp fun_val arg_val)
                            },
                        kev_err msg => kev_err msg
                    },
                kev_err msg => kev_err msg
            },
        EvalTerm.elam mult body => kev_ok term,
        EvalTerm.econst idx => kev_ok term,
        EvalTerm.esort level => kev_ok term,
        EvalTerm.elit lit =>
            match lit {
                EvalLiteral.l_int n => kev_ok term,
                EvalLiteral.l_str s => kev_ok term,
                EvalLiteral.l_float s => kev_ok term,
                EvalLiteral.l_bool b => kev_ok term,
                EvalLiteral.l_sort n => kev_ok term
            },
        EvalTerm.eprim idx args => kev_ok term,
        EvalTerm.erecursor info cases scrutinee => kev_ok term,
        EvalTerm.eregion region mult body => kev_eval body env,
        EvalTerm.eborrow region kind body => kev_eval body env,
        EvalTerm.eproj field arg => kev_eval arg env,
        EvalTerm.eproj_field field base => kev_eval base env
    }

@[test]
def test_e2e_lower_t2_identity : Bool :=
    // (λx. x) "hello" → Term → lower_t2 → kev_eval → "hello"
    let body : Term := Term.var 0 DebugName.unnamed in
    let lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) body in
    let arg : Term := Term.lit (Literal.str "hello") in
    let app : Term := Term.app lam arg in
    let lowered : EvalTerm := lower_t2 app in
    match kev_eval lowered kev_empty {
        kev_ok v =>
            match v {
                EvalTerm.elit lit =>
                    match lit {
                        EvalLiteral.l_str s => String.beq s "hello",
                        EvalLiteral.l_int n => false,
                        EvalLiteral.l_float s => false,
                        EvalLiteral.l_bool b => false,
                        EvalLiteral.l_sort n => false
                    },
                EvalTerm.evar i => false,
                EvalTerm.elam m b => false,
                EvalTerm.eapp f a => false,
                EvalTerm.econst i => false,
                EvalTerm.esort l => false,
                EvalTerm.eprim i args => false,
                EvalTerm.erecursor info cases s => false,
                EvalTerm.eregion r m b => false,
                EvalTerm.eborrow r k b => false,
                EvalTerm.eproj f a => false,
                EvalTerm.eproj_field f b => false
            },
        kev_err msg => false
    }

@[test]
def test_e2e_lower_t2_nested : Bool :=
    // (λx. λy. y) 10 "world" → "world"
    let inner_body : Term := Term.var 0 DebugName.unnamed in
    let inner_lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) inner_body in
    let outer_lam : Term := Term.lam DebugName.unnamed (Term.type_ 1) inner_lam in
    let arg1 : Term := Term.lit (Literal.num 10 NumSuffix.i64) in
    let arg2 : Term := Term.lit (Literal.str "world") in
    let app : Term := Term.app (Term.app outer_lam arg1) arg2 in
    let lowered : EvalTerm := lower_t2 app in
    match kev_eval lowered kev_empty {
        kev_ok v =>
            match v {
                EvalTerm.elit lit =>
                    match lit {
                        EvalLiteral.l_str s => String.beq s "world",
                        EvalLiteral.l_int n => false,
                        EvalLiteral.l_float s => false,
                        EvalLiteral.l_bool b => false,
                        EvalLiteral.l_sort n => false
                    },
                EvalTerm.evar i => false,
                EvalTerm.elam m b => false,
                EvalTerm.eapp f a => false,
                EvalTerm.econst i => false,
                EvalTerm.esort l => false,
                EvalTerm.eprim i args => false,
                EvalTerm.erecursor info cases s => false,
                EvalTerm.eregion r m b => false,
                EvalTerm.eborrow r k b => false,
                EvalTerm.eproj f a => false,
                EvalTerm.eproj_field f b => false
            },
        kev_err msg => false
    }
