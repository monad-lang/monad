use lang.types
use lang.eval_term
open EvalTerm

// ─── EvalTerm environment-based evaluator ──────────────────────────────
// Evaluates EvalTerm (from lang.eval_term) using an environment
// (stack of values for de Bruijn indices). Call-by-value semantics.

type KEvalEnv {
  kenv_empty,
  kenv_push (val: EvalTerm) (rest: KEvalEnv),
}

open KEvalEnv

/// Look up a de Bruijn index in the evaluation environment.
@[partial]
def kenv_lookup (env: KEvalEnv) (idx: I64) : Option EvalTerm :=
  match env {
    kenv_empty => Option.none,
    kenv_push val rest =>
      if I64.beq idx 0
      then Option.some val
      else kenv_lookup rest (idx - 1)
  }

type KernelResult {
  kr_ok (v: EvalTerm),
  kr_err (msg: String),
}

open KernelResult

/// Evaluate an EvalTerm under an environment.
/// Variables resolved via kenv_lookup. Lambdas extend the env on application.
@[partial]
def keval (term: EvalTerm) (env: KEvalEnv) : KernelResult :=
  match term {
    EvalTerm.evar idx =>
      match kenv_lookup env idx {
        Option.some val => keval val env,
        Option.none => kr_err "unbound variable"
      },
    EvalTerm.eapp fun arg =>
      match keval fun env {
        kr_ok fun_val =>
          match keval arg env {
            kr_ok arg_val =>
              match fun_val {
                EvalTerm.elam mult body =>
                  keval body (kenv_push arg_val env),
                EvalTerm.evar idx => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.eapp f a => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.econst idx => kr_err "not a function",
                EvalTerm.esort level => kr_err "not a function",
                EvalTerm.elit lit => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.eprim idx args => kr_err "not a function",
                EvalTerm.erecursor info cases s => kr_err "not a function",
                EvalTerm.eregion r m b => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.eborrow r k b => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.eproj f a => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.eproj_field f b => kr_ok (EvalTerm.eapp fun_val arg_val)
              },
            kr_err msg => kr_err msg
          },
        kr_err msg => kr_err msg
      },
    EvalTerm.elam mult body => kr_ok term,
    EvalTerm.elit lit =>
      match lit {
        EvalLiteral.l_int n => kr_ok term,
        EvalLiteral.l_str s => kr_ok term,
        EvalLiteral.l_float s => kr_ok term,
        EvalLiteral.l_bool b => kr_ok term,
        EvalLiteral.l_sort n => kr_ok term
      },
    EvalTerm.esort level => kr_ok term,
    EvalTerm.econst idx => kr_ok term,
    EvalTerm.eprim idx args => kr_ok term,
    EvalTerm.erecursor info cases scrutinee => kr_ok term,
    EvalTerm.eregion region mult body => keval body env,
    EvalTerm.eborrow region kind body => keval body env,
    EvalTerm.eproj field arg => keval arg env,
    EvalTerm.eproj_field field base => keval base env
  }

// ─── EvalTerm evaluator tests ──────────────────────────────────────────

@[test]
def test_keval_lit : Bool :=
  let t : EvalTerm := EvalTerm.elit (EvalLiteral.l_int 7) in
  match keval t kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.elit lit =>
          match lit {
            EvalLiteral.l_int n => I64.beq n 7,
            EvalLiteral.l_str s => false,
            EvalLiteral.l_float s => false,
            EvalLiteral.l_bool b => false,
            EvalLiteral.l_sort n => false
          },
        _ => false
      },
    kr_err msg => false
  }

@[test]
def test_keval_identity : Bool :=
  let body : EvalTerm := EvalTerm.evar 0 in
  let id : EvalTerm := EvalTerm.elam Multiplicity.many body in
  let arg : EvalTerm := EvalTerm.elit (EvalLiteral.l_int 99) in
  let app : EvalTerm := EvalTerm.eapp id arg in
  match keval app kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.elit lit =>
          match lit {
            EvalLiteral.l_int n => I64.beq n 99,
            _ => false
          },
        _ => false
      },
    kr_err msg => false
  }

@[test]
def test_keval_lam_value : Bool :=
  let lam : EvalTerm := EvalTerm.elam Multiplicity.many (EvalTerm.evar 0) in
  match keval lam kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.elam mult body => true,
        _ => false
      },
    kr_err msg => false
  }

@[test]
def test_keval_const : Bool :=
  let c : EvalTerm := EvalTerm.econst 5 in
  match keval c kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.econst idx => I64.beq idx 5,
        _ => false
      },
    kr_err msg => false
  }

@[test]
def test_keval_nested_app : Bool :=
  let
    body : EvalTerm := EvalTerm.evar 0;
    inner : EvalTerm := EvalTerm.elam Multiplicity.many body;
    outer : EvalTerm := EvalTerm.elam Multiplicity.many inner;
    arg1 : EvalTerm := EvalTerm.elit (EvalLiteral.l_int 10);
    arg2 : EvalTerm := EvalTerm.elit (EvalLiteral.l_int 20);
    app : EvalTerm := EvalTerm.eapp (EvalTerm.eapp outer arg1) arg2
  in
  match keval app kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.elit lit =>
          match lit {
            EvalLiteral.l_int n => I64.beq n 20,
            _ => false
          },
        _ => false
      },
    kr_err msg => false
  }
