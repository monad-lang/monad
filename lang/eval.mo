use lang.types
type EvalResult{ok_val(Term),err_val(EvalError)}
open EvalResult
type Scope{empty_scope,bind(name:NameRef)(value:Term)(rest:Scope)}
def identifier_string(i:Identifier):String:=match i{id s=>s}
def name_eq(a:NameRef)(b:NameRef):Bool:=
 match a{
  nid id_a=>match b{
    nid id_b=>String.beq (identifier_string id_a) (identifier_string id_b),
   nmp mp_b=>false,nop op_b=>false
  },
  nmp mp_a=>false,nop op_a=>false
 }
def scope_lookup(name:NameRef)(scope:Scope):Option Term:=
 match scope{
  empty_scope=>Option.none,
  bind n val rest=>if name_eq n name then Option.some val else scope_lookup name rest
 }
def substitute_lam(param:Param)(body:Term)(name:NameRef)(new_term:Term):Term:=
 match param{
  mk pname ptype=>
    if name_eq (NameRef.nid pname) name
   then Term.lam param body
    else Term.lam param (substitute body name new_term)
 }
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
def eval_apply(fun:Term)(arg:Term)(scope:Scope):EvalResult:=
 match fun{
   lam param body=>match param{mk pname ptype=>ok_val (substitute body (NameRef.nid pname) arg)},
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
def eval_step_var(name:NameRef)(scope:Scope):EvalResult:=
 match scope_lookup name scope{
  Option.some val=>eval_step val scope,
   Option.none=>err_val (EvalError.undefined_var name)
 }
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
  lit val=>ok_val term
 }
def main:I64:=42
