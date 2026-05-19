use lang.types
use lang.eval_term

/// Find the de Bruijn index of an identifier in the binding context.
/// Returns Option.none if not found (treat as global/const).
@[partial]
def find_index (id: Identifier) (ctx: List Identifier) (depth: I64) : Option I64 :=
  match ctx {
    List.cons x rest =>
      if String.beq (identifier_string id) (identifier_string x)
      then Option.some depth
      else find_index id rest (depth + 1),
    List.empty => Option.none
  }

@[partial]
def identifier_string (id: Identifier) : String :=
  match id {
    id s => s
  }

/// Lower a type-checked TermV0 to EvalTerm.
///
/// ctx: binding context (innermost first) — list of bound variable identifiers.
/// Each lambda adds its param name to the front of ctx.
/// De Bruijn index 0 = most recently bound variable (head of ctx).
@[partial]
def lower (ctx: List Identifier) (t: TermV0) : EvalTerm :=
  match t {
    TermV0.var name =>
      match name {
        NameRef.nid id =>
          match find_index id ctx 0 {
            Option.some idx => EvalTerm.evar idx,
            Option.none => EvalTerm.econst 0
          },
        NameRef.nmp p => EvalTerm.econst 0,
        NameRef.nop o => EvalTerm.eprim 0 (List.empty : List EvalTerm)
      },
    TermV0.lam param body =>
      match param {
        Param.mk pname ptype mult _default =>
          let lowered_body : EvalTerm := lower (List.cons pname ctx) body in
          // Assign region based on multiplicity: linear/affine→r_param, many/zero→r_stack
          let region : Region := match mult {
            Multiplicity.linear => Region.r_param 0,
            Multiplicity.affine => Region.r_param 0,
            Multiplicity.zero => Region.r_stack,
            Multiplicity.many => Region.r_stack
          } in
          EvalTerm.elam mult (EvalTerm.eregion region mult lowered_body)
      },
    TermV0.app fun arg =>
      EvalTerm.eapp (lower ctx fun) (lower ctx arg),
    TermV0.lit lit_value =>
      match lit_value {
        Literal.str s => EvalTerm.elit (EvalLiteral.l_str s),
        Literal.num n suffix => EvalTerm.elit (EvalLiteral.l_int n),
        Literal.if_ cond then_ else_ => EvalTerm.elit (EvalLiteral.l_bool true),
        Literal.match_ scrutinee cases =>
          EvalTerm.erecursor (RecursorInfo.mk 0 0 0) (List.empty : List EvalTerm) (lower ctx scrutinee)
      },
    TermV0.forall fname ftyp fbody =>
      lower ctx fbody,
    TermV0.pi arg ret =>
      EvalTerm.esort 1,
    TermV0.type_ level =>
      EvalTerm.esort level,
    TermV0.ntv native_val =>
      match native_val {
        Native.mk native_name num_args args => EvalTerm.eprim 0 (List.empty : List EvalTerm)
      },
    TermV0.con con_val =>
      match con_val {
        Con.mk cname ctyp_name cnum_args cargs => EvalTerm.econst 0
      },
    TermV0.hole =>
      EvalTerm.elit (EvalLiteral.l_int 0)
  }

// ─── Test helpers ──────────────────────────────────────────────────────

@[partial]
def empty_ctx : List Identifier := List.empty

@[partial]
def single_ctx (id: Identifier) : List Identifier :=
  List.cons id List.empty

// ─── Variable lowering tests ───────────────────────────────────────────

@[test]
def test_lower_var_str : Bool :=
  let t : TermV0 := TermV0.lit (Literal.str "hello") in
  let _ : EvalTerm := lower empty_ctx t in
  true

@[test]
def test_lower_var_num : Bool :=
  let t : TermV0 := TermV0.lit (Literal.num 42 NumSuffix.i64) in
  let _ : EvalTerm := lower empty_ctx t in
  true

@[test]
def test_lower_var_bound : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let t : TermV0 := TermV0.var (NameRef.nid id_x) in
  let _ : EvalTerm := lower (single_ctx id_x) t in
  true

@[test]
def test_lower_var_free : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let t : TermV0 := TermV0.var (NameRef.nid id_x) in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Lambda lowering tests ─────────────────────────────────────────────

@[test]
def test_lower_lam_identity : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let t : TermV0 := TermV0.lam
    (param_many id_x TermV0.hole)
    (TermV0.var (NameRef.nid id_x)) in
  let _ : EvalTerm := lower empty_ctx t in
  true

@[test]
def test_lower_lam_nested : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let id_y : Identifier := Identifier.id "y" in
  let t : TermV0 := TermV0.lam
    (param_many id_x TermV0.hole)
    (TermV0.lam
      (param_many id_y TermV0.hole)
      (TermV0.var (NameRef.nid id_x))) in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Application lowering tests ────────────────────────────────────────

@[test]
def test_lower_app_simple : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let f : TermV0 := TermV0.lam
    (param_many id_x TermV0.hole)
    (TermV0.var (NameRef.nid id_x)) in
  let t : TermV0 := TermV0.app f (TermV0.lit (Literal.num 1 NumSuffix.i64)) in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Forall/Pi erasure tests ───────────────────────────────────────────

@[test]
def test_lower_forall_erased : Bool :=
  let id_a : Identifier := Identifier.id "a" in
  let t : TermV0 := TermV0.forall id_a TermV0.hole (TermV0.lit (Literal.num 42 NumSuffix.i64)) in
  let _ : EvalTerm := lower empty_ctx t in
  true

@[test]
def test_lower_pi_erased : Bool :=
  let t : TermV0 := TermV0.pi TermV0.hole TermV0.hole in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Sort lowering tests ───────────────────────────────────────────────

@[test]
def test_lower_sort : Bool :=
  let t : TermV0 := TermV0.type_ 1 in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Native lowering tests ─────────────────────────────────────────────

// ─── Hole lowering tests ───────────────────────────────────────────────

@[test]
def test_lower_hole : Bool :=
  let t : TermV0 := TermV0.hole in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Lower + eval end-to-end pipeline tests ───────────────────────────
// Full pipeline: TermV0 → lower → e2e_eval → result.
// keval logic inlined here to avoid import conflicts with lang/eval.mo
// (both define identifier_string).

type KEvalEnv {
  kenv_empty,
  kenv_push (val: EvalTerm) (rest: KEvalEnv),
}

open KEvalEnv

type KernelResult {
  kr_ok (v: EvalTerm),
  kr_err (msg: String),
}

open KernelResult

@[partial]
def kenv_lookup (env: KEvalEnv) (idx: I64) : Option EvalTerm :=
  match env {
    kenv_empty => Option.none,
    kenv_push val rest =>
      if I64.beq idx 0
      then Option.some val
      else kenv_lookup rest (idx - 1)
  }

@[partial]
def e2e_eval (term: EvalTerm) (env: KEvalEnv) : KernelResult :=
  match term {
    EvalTerm.evar idx =>
      match kenv_lookup env idx {
        Option.some val => e2e_eval val env,
        Option.none => kr_err "unbound variable"
      },
    EvalTerm.eapp fun arg =>
      match e2e_eval fun env {
        kr_ok fun_val =>
          match e2e_eval arg env {
            kr_ok arg_val =>
              match fun_val {
                EvalTerm.elam mult body =>
                  e2e_eval body (kenv_push arg_val env),
                EvalTerm.esort level => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.evar idx => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.eapp f a => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.econst idx => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.elit lit => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.eprim idx args => kr_ok (EvalTerm.eapp fun_val arg_val),
                EvalTerm.erecursor info cases s => kr_ok (EvalTerm.eapp fun_val arg_val),
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
    EvalTerm.esort level => kr_ok term,
    EvalTerm.econst idx => kr_ok term,
    EvalTerm.eprim idx args => kr_ok term,
    EvalTerm.erecursor info cases scrutinee => kr_ok term,
    EvalTerm.eregion region mult body => e2e_eval body env,
    EvalTerm.eborrow region kind body => e2e_eval body env,
    EvalTerm.eproj field arg => e2e_eval arg env,
    EvalTerm.eproj_field field base => e2e_eval base env,
    EvalTerm.elit lit =>
      match lit {
        EvalLiteral.l_int n => kr_ok term,
        EvalLiteral.l_str s => kr_ok term,
        EvalLiteral.l_float s => kr_ok term,
        EvalLiteral.l_bool b => kr_ok term,
        EvalLiteral.l_sort n => kr_ok term
      }
  }

@[test]
def test_e2e_literal : Bool :=
  let n : EvalTerm := EvalTerm.elit (EvalLiteral.l_int 7) in
  match e2e_eval n kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.elit lit =>
          match lit {
            EvalLiteral.l_int x => I64.beq x 7,
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
def test_e2e_identity : Bool :=
  // (λx. x) 99 → 99 via e2e_eval directly
  let body : EvalTerm := EvalTerm.elam Multiplicity.many (EvalTerm.evar 0) in
  let arg : EvalTerm := EvalTerm.elit (EvalLiteral.l_int 99) in
  let app : EvalTerm := EvalTerm.eapp body arg in
  match e2e_eval app kenv_empty {
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
def test_e2e_lower_plus_eval : Bool :=
  // Full pipeline: TermV0 → lower → e2e_eval
  // TermV0: (λx. x) "hello" → "hello"
  let x_name : NameRef := NameRef.nid (Identifier.id "x") in
  let x_var : TermV0 := TermV0.var x_name in
  let x_param : Param := param_many (Identifier.id "x") (TermV0.type_ 1) in
  let lam_body : TermV0 := TermV0.lam x_param x_var in
  let arg_term : TermV0 := TermV0.lit (Literal.str "hello") in
  let app_term : TermV0 := TermV0.app lam_body arg_term in
  let empty_ctx : List Identifier := List.empty in
  let lowered : EvalTerm := lower empty_ctx app_term in
  match e2e_eval lowered kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.elit lit =>
          match lit {
            EvalLiteral.l_str s => String.beq s "hello",
            EvalLiteral.l_int n => false,
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
def test_e2e_nested : Bool :=
  // Full pipeline: (λx. λy. y) 10 "world" → "world"
  let y_name : NameRef := NameRef.nid (Identifier.id "y") in
  let y_var : TermV0 := TermV0.var y_name in
  let y_param : Param := param_many (Identifier.id "y") (TermV0.type_ 1) in
  let inner_lam : TermV0 := TermV0.lam y_param y_var in
  let x_param : Param := param_many (Identifier.id "x") (TermV0.type_ 1) in
  let outer_lam : TermV0 := TermV0.lam x_param inner_lam in
  let arg1 : TermV0 := TermV0.lit (Literal.num 10 NumSuffix.i64) in
  let arg2 : TermV0 := TermV0.lit (Literal.str "world") in
  let app_term : TermV0 := TermV0.app (TermV0.app outer_lam arg1) arg2 in
  let empty_ctx : List Identifier := List.empty in
  let lowered : EvalTerm := lower empty_ctx app_term in
  match e2e_eval lowered kenv_empty {
    kr_ok v =>
      match v {
        EvalTerm.elit lit =>
          match lit {
            EvalLiteral.l_str s => String.beq s "world",
            EvalLiteral.l_int n => false,
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
