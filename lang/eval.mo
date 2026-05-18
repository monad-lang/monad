use lang.types
use lang.eval_term
open EvalTerm
type EvalResult{ok_val(Term),err_val(EvalError)}
open EvalResult
type Scope{empty_scope,bind(name:NameRef)(value:Term)(rest:Scope)}
@[partial]
def identifier_string(i:Identifier):String:=match i{id s=>s}
@[partial]
def name_eq(a:NameRef)(b:NameRef):Bool:=
 match a{
  nid id_a=>match b{
    nid id_b=>String.beq (identifier_string id_a) (identifier_string id_b),
   nmp mp_b=>false,nop op_b=>false
  },
  nmp mp_a=>false,nop op_a=>false
 }
@[partial]
def scope_lookup(name:NameRef)(scope:Scope):Option Term:=
 match scope{
  empty_scope=>Option.none,
  bind n val rest=>if name_eq n name then Option.some val else scope_lookup name rest
 }
@[partial]
def substitute_lam(param:Param)(body:Term)(name:NameRef)(new_term:Term):Term:=
  match param{
  mk pname ptype pmult pdefault=>
    if name_eq (NameRef.nid pname) name
   then Term.lam param body
    else Term.lam param (substitute body name new_term)
 }
@[partial]
def substitute(term:Term)(name:NameRef)(new_term:Term):Term:=
 match term{
  var n=>if name_eq n name then new_term else term,
  lam param body=>substitute_lam param body name new_term,
   pi arg ret=>Term.pi (substitute arg name new_term) (substitute ret name new_term),
   app fun arg=>Term.app (substitute fun name new_term) (substitute arg name new_term),
   forall n typ body=>Term.forall n (substitute typ name new_term) (substitute body name new_term),
  lit val=>Term.lit val,
  con c=>Term.hole,
  ntv native_val=>term,
  type_ universe_val=>term,
  hole=>term
 }
@[partial]
def eval_apply(fun:Term)(arg:Term)(scope:Scope):EvalResult:=
 match fun{
   lam param body=>match param{mk pname ptype pmult pdefault=>ok_val (substitute body (NameRef.nid pname) arg)},
  var name=>match scope_lookup name scope{
   Option.some val=>eval_apply val arg scope,
    Option.none=>err_val (EvalError.undefined_var name)
  },
  app f a=>match eval_apply f a scope{
   ok_val result=>eval_apply result arg scope,
   err_val e=>err_val e
  },
   pi arg_typ ret_typ=>err_val (EvalError.not_a_function fun),
   forall fname ftyp fbody=>err_val (EvalError.not_a_function fun),
   con con_val=>err_val (EvalError.not_a_function fun),
   ntv native_val=>err_val (EvalError.not_a_function fun),
   lit lit_val=>err_val (EvalError.not_a_function fun),
   type_ universe_val=>err_val (EvalError.not_a_function fun),
   hole=>err_val (EvalError.not_a_function fun)
 }
@[partial]
def eval_step_var(name:NameRef)(scope:Scope):EvalResult:=
 match scope_lookup name scope{
  Option.some val=>eval_step val scope,
   Option.none=>err_val (EvalError.undefined_var name)
 }
@[partial]
def eval_step(term:Term)(scope:Scope):EvalResult:=
 match term{
  var name=>eval_step_var name scope,
  app fun_arg app_arg=>match eval_step fun_arg scope{
   ok_val fun_val=>match eval_step app_arg scope{
    ok_val arg_val=>eval_apply fun_val arg_val scope,
    err_val e=>err_val e
   },
   err_val e=>err_val e
  },
  lam param body=>ok_val term,
  pi arg ret=>ok_val term,
  forall fname ftyp fbody=>ok_val term,
  con con_val=>ok_val term,
  ntv native_val=>ok_val term,
  type_ universe_val=>ok_val term,
  hole=>ok_val term,
  lit val=>eval_lit val scope
  }
@[partial]
def var_term(s:String):Term:=Term.var (NameRef.nid (Identifier.id s))
@[partial]
def num_term(n:I64):Term:=Term.lit (Literal.num n NumSuffix.i64)
@[partial]
def con_name_match(c:Con)(s:String):Bool:=
  match c{
    mk cname ctyp cnum_args ccon_args=>String.beq (identifier_string cname) s
  }
@[partial]
def find_case(name:Identifier)(cases:List MatchCase):Option MatchCase:=
  match cases{
    List.cons c rest=>
      match c{mc cname cargs cvalue=>
        if String.beq (identifier_string cname) (identifier_string name)
        then Option.some c
        else find_case name rest
      },
    List.empty=>Option.none
  }
@[partial]
def substitute_args(args:List (Option Term))(params:List Identifier)(body:Term):EvalResult:=
  match args{
    List.cons a rest_args=>
      match params{
        List.cons p rest_params=>substitute_args_opt a rest_args p rest_params body,
        List.empty=>ok_val body
      },
    List.empty=>ok_val body
  }
@[partial]
def substitute_args_opt(a:Option Term)(rest_args:List (Option Term))(p:Identifier)(rest_params:List Identifier)(body:Term):EvalResult:=
  match a{
    Option.some arg_val=>substitute_args rest_args rest_params (substitute body (NameRef.nid p) arg_val),
    Option.none=>err_val (EvalError.custom "incomplete constructor args")
  }
@[partial]
def eval_match(scrutinee:Term)(cases:List MatchCase)(scope:Scope):EvalResult:=
  match eval_step scrutinee scope{
    ok_val result=>eval_match_result result cases,
    err_val e=>err_val e
  }
@[partial]
def eval_match_result(result:Term)(cases:List MatchCase):EvalResult:=
  match result{
    con c=>eval_match_con c result cases,
    forall fname ftyp fbody=>err_val (EvalError.match_failure result),
    pi arg ret=>err_val (EvalError.match_failure result),
    var name=>err_val (EvalError.match_failure result),
    lam param body=>err_val (EvalError.match_failure result),
    app fun arg=>err_val (EvalError.match_failure result),
    lit val=>err_val (EvalError.match_failure result),
    ntv n=>err_val (EvalError.match_failure result),
    type_ u=>err_val (EvalError.match_failure result),
    hole=>err_val (EvalError.match_failure result)
  }
@[partial]
def eval_match_con(c:Con)(result:Term)(cases:List MatchCase):EvalResult:=
  match c{
    mk cname ctyp cnum_args ccon_args=>
      match find_case cname cases{
        Option.some case_val=>match case_val{
          mc mcname mcparams mcbody=>substitute_args ccon_args mcparams mcbody
        },
        Option.none=>err_val (EvalError.match_failure result)
      }
  }
@[partial]
def eval_if(cond:Term)(then_b:Term)(else_b:Term)(scope:Scope):EvalResult:=
  match eval_step cond scope{
    ok_val result=>eval_if_result result then_b else_b,
    err_val e=>err_val e
  }
@[partial]
def eval_if_result(result:Term)(then_b:Term)(else_b:Term):EvalResult:=
  match result{
    con c=>eval_if_con c then_b else_b,
    var name=>err_val (EvalError.custom "if condition must be Bool"),
    lam param body=>err_val (EvalError.custom "if condition must be Bool"),
    app fun arg=>err_val (EvalError.custom "if condition must be Bool"),
    pi arg ret=>err_val (EvalError.custom "if condition must be Bool"),
    forall fname ftyp fbody=>err_val (EvalError.custom "if condition must be Bool"),
    lit val=>err_val (EvalError.custom "if condition must be Bool"),
    ntv n=>err_val (EvalError.custom "if condition must be Bool"),
    type_ u=>err_val (EvalError.custom "if condition must be Bool"),
    hole=>err_val (EvalError.custom "if condition must be Bool")
  }
@[partial]
def eval_if_con(c:Con)(then_b:Term)(else_b:Term):EvalResult:=
  if con_name_match c "true"
  then ok_val then_b
  else if con_name_match c "false"
  then ok_val else_b
  else err_val (EvalError.custom "if condition must be Bool")
@[partial]
def eval_lit(val:Literal)(scope:Scope):EvalResult:=
  match val{
    match_ scrutinee cases=>eval_match scrutinee cases scope,
    if_ cond then_b else_b=>eval_if cond then_b else_b scope,
    str s=>ok_val (Term.lit val),
    num n s=>ok_val (Term.lit val)
  }
@[test]
def test_eval_identity:Bool:=
  let id_lam:Term:=Term.lam (param_many (Identifier.id "x") (Term.type_ 1)) (var_term "x") in
  let app_term:Term:=Term.app id_lam (num_term 42) in
  match eval_step app_term Scope.empty_scope{
    ok_val result=>match result{
      lit val=>match val{
        num n s=>I64.beq n 42,
        str v=>false,match_ v cs=>false,if_ c t e=>false
      },
      forall fname ftyp fbody=>false,pi arg ret=>false,var name=>false,
      lam param body=>false,app fun arg=>false,con c=>false,
      ntv n=>false,type_ u=>false,hole=>false
    },
    err_val e=>false
  }
@[test]
def test_eval_shadowing:Bool:=
  let inner_lam:Term:=Term.lam (param_many (Identifier.id "x") (Term.type_ 1)) (var_term "x") in
  let outer_lam:Term:=Term.lam (param_many (Identifier.id "x") (Term.type_ 1)) inner_lam in
  let app_term:Term:=Term.app (Term.app outer_lam (num_term 1)) (num_term 2) in
  match eval_step app_term Scope.empty_scope{
    ok_val result=>match result{
      lit val=>match val{
        num n s=>I64.beq n 2,
        str v=>false,match_ v cs=>false,if_ c t e=>false
      },
      forall fname ftyp fbody=>false,pi arg ret=>false,var name=>false,
      lam param body=>false,app fun arg=>false,con c=>false,
      ntv n=>false,type_ u=>false,hole=>false
    },
    err_val e=>false
  }
@[test]
def test_eval_step_var:Bool:=
  let scope:Scope:=Scope.bind (NameRef.nid (Identifier.id "x")) (num_term 10) Scope.empty_scope in
  match eval_step (var_term "x") scope{
    ok_val result=>match result{
      lit val=>match val{
        num n s=>I64.beq n 10,
        str v=>false,match_ v cs=>false,if_ c t e=>false
      },
      forall fname ftyp fbody=>false,pi arg ret=>false,var name=>false,
      lam param body=>false,app fun arg=>false,con c=>false,
      ntv n=>false,type_ u=>false,hole=>false
    },
    err_val e=>false
  }
// Match and if evaluation logic is implemented but tests are blocked by
// type checker bug: Con.mk gets spurious {A : Type} forall parameter
// from the args: List (Option Term) field. Once fixed, uncomment tests below.
//
// @[test]
// def test_eval_if_true:Bool:= ...
// @[test]  
// def test_eval_if_false:Bool:= ...
// @[test]
// def test_eval_match_some:Bool:= ...

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
        EvalTerm.evar idx => false,
        EvalTerm.elam mult body => false,
        EvalTerm.eapp fun arg => false,
        EvalTerm.econst idx => false,
        EvalTerm.esort level => false,
        EvalTerm.eprim idx args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
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
            EvalLiteral.l_str s => false,
            EvalLiteral.l_float s => false,
            EvalLiteral.l_bool b => false,
            EvalLiteral.l_sort n => false
          },
        EvalTerm.evar idx => false,
        EvalTerm.elam mult body => false,
        EvalTerm.eapp fun arg => false,
        EvalTerm.econst idx => false,
        EvalTerm.esort level => false,
        EvalTerm.eprim idx args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
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
        EvalTerm.evar idx => false,
        EvalTerm.eapp fun arg => false,
        EvalTerm.econst idx => false,
        EvalTerm.esort level => false,
        EvalTerm.elit lit => false,
        EvalTerm.eprim idx args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
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
        EvalTerm.evar idx => false,
        EvalTerm.elam mult body => false,
        EvalTerm.eapp fun arg => false,
        EvalTerm.esort level => false,
        EvalTerm.elit lit => false,
        EvalTerm.eprim idx args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
      },
    kr_err msg => false
  }

@[test]
def test_keval_nested_app : Bool :=
  let body : EvalTerm := EvalTerm.evar 0 in
  let inner : EvalTerm := EvalTerm.elam Multiplicity.many body in
  let outer : EvalTerm := EvalTerm.elam Multiplicity.many inner in
  let arg1 : EvalTerm := EvalTerm.elit (EvalLiteral.l_int 10) in
  let arg2 : EvalTerm := EvalTerm.elit (EvalLiteral.l_int 20) in
  let app : EvalTerm := EvalTerm.eapp (EvalTerm.eapp outer arg1) arg2 in
  match keval app kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.elit lit =>
          match lit {
            EvalLiteral.l_int n => I64.beq n 20,
            EvalLiteral.l_str s => false,
            EvalLiteral.l_float s => false,
            EvalLiteral.l_bool b => false,
            EvalLiteral.l_sort n => false
          },
        EvalTerm.evar idx => false,
        EvalTerm.elam mult body => false,
        EvalTerm.eapp fun arg => false,
        EvalTerm.econst idx => false,
        EvalTerm.esort level => false,
        EvalTerm.eprim idx args => false,
        EvalTerm.erecursor info cases s => false,
        EvalTerm.eregion r m b => false,
        EvalTerm.eborrow r k b => false,
        EvalTerm.eproj f a => false,
        EvalTerm.eproj_field f b => false
      },
    kr_err msg => false
  }

def main:I64:=42