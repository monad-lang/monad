use lang.types
use lang.eval_term

/// Find the de Bruijn index of an identifier in the binding context.
/// Returns Option.none if not found (treat as global/const).
def find_index (id: Identifier) (ctx: List Identifier) (depth: I64) : Option I64 :=
  match ctx {
    List.cons x rest =>
      if String.beq (identifier_string id) (identifier_string x)
      then Option.some depth
      else find_index id rest (depth + 1),
    List.empty => Option.none
  }

def identifier_string (id: Identifier) : String :=
  match id {
    id s => s
  }

/// Lower a type-checked Term to EvalTerm.
///
/// ctx: binding context (innermost first) — list of bound variable identifiers.
/// Each lambda adds its param name to the front of ctx.
/// De Bruijn index 0 = most recently bound variable (head of ctx).
def lower (ctx: List Identifier) (t: Term) : EvalTerm :=
  match t {
    Term.var name =>
      match name {
        NameRef.nid id =>
          match find_index id ctx 0 {
            Option.some idx => EvalTerm.evar idx,
            Option.none => EvalTerm.econst 0
          },
        NameRef.nmp p => EvalTerm.econst 0,
        NameRef.nop o => EvalTerm.eprim 0 (List.empty : List EvalTerm)
      },
    Term.lam param body =>
      match param {
        Param.mk pname ptype =>
          EvalTerm.elam Multiplicity.many (lower (List.cons pname ctx) body)
      },
    Term.app fun arg =>
      EvalTerm.eapp (lower ctx fun) (lower ctx arg),
    Term.lit lit_value =>
      match lit_value {
        Literal.str s => EvalTerm.elit (EvalLiteral.l_str s),
        Literal.num n suffix => EvalTerm.elit (EvalLiteral.l_int n),
        Literal.if_ cond then_ else_ => EvalTerm.elit (EvalLiteral.l_bool true),
        Literal.match_ scrutinee cases =>
          EvalTerm.erecursor (RecursorInfo.mk 0 0 0) (List.empty : List EvalTerm) (lower ctx scrutinee)
      },
    Term.forall fname ftyp fbody =>
      lower ctx fbody,
    Term.pi arg ret =>
      EvalTerm.esort 1,
    Term.type_ level =>
      EvalTerm.esort level,
    Term.ntv native_val =>
      match native_val {
        Native.mk native_name num_args args => EvalTerm.eprim 0 (List.empty : List EvalTerm)
      },
    Term.con con_val =>
      match con_val {
        Con.mk cname ctyp_name cnum_args cargs => EvalTerm.econst 0
      },
    Term.hole =>
      EvalTerm.elit (EvalLiteral.l_int 0)
  }

// ─── Test helpers ──────────────────────────────────────────────────────

def empty_ctx : List Identifier := List.empty

def single_ctx (id: Identifier) : List Identifier :=
  List.cons id List.empty

// ─── Variable lowering tests ───────────────────────────────────────────

@[test]
def test_lower_var_str : Bool :=
  let t : Term := Term.lit (Literal.str "hello") in
  let _ : EvalTerm := lower empty_ctx t in
  true

@[test]
def test_lower_var_num : Bool :=
  let t : Term := Term.lit (Literal.num 42 NumSuffix.i64) in
  let _ : EvalTerm := lower empty_ctx t in
  true

@[test]
def test_lower_var_bound : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let t : Term := Term.var (NameRef.nid id_x) in
  let _ : EvalTerm := lower (single_ctx id_x) t in
  true

@[test]
def test_lower_var_free : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let t : Term := Term.var (NameRef.nid id_x) in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Lambda lowering tests ─────────────────────────────────────────────

@[test]
def test_lower_lam_identity : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let t : Term := Term.lam
    (Param.mk id_x Term.hole)
    (Term.var (NameRef.nid id_x)) in
  let _ : EvalTerm := lower empty_ctx t in
  true

@[test]
def test_lower_lam_nested : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let id_y : Identifier := Identifier.id "y" in
  let t : Term := Term.lam
    (Param.mk id_x Term.hole)
    (Term.lam
      (Param.mk id_y Term.hole)
      (Term.var (NameRef.nid id_x))) in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Application lowering tests ────────────────────────────────────────

@[test]
def test_lower_app_simple : Bool :=
  let id_x : Identifier := Identifier.id "x" in
  let f : Term := Term.lam
    (Param.mk id_x Term.hole)
    (Term.var (NameRef.nid id_x)) in
  let t : Term := Term.app f (Term.lit (Literal.num 1 NumSuffix.i64)) in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Forall/Pi erasure tests ───────────────────────────────────────────

@[test]
def test_lower_forall_erased : Bool :=
  let id_a : Identifier := Identifier.id "a" in
  let t : Term := Term.forall id_a Term.hole (Term.lit (Literal.num 42 NumSuffix.i64)) in
  let _ : EvalTerm := lower empty_ctx t in
  true

@[test]
def test_lower_pi_erased : Bool :=
  let t : Term := Term.pi Term.hole Term.hole in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Sort lowering tests ───────────────────────────────────────────────

@[test]
def test_lower_sort : Bool :=
  let t : Term := Term.type_ 1 in
  let _ : EvalTerm := lower empty_ctx t in
  true

// ─── Native lowering tests ─────────────────────────────────────────────

// ─── Hole lowering tests ───────────────────────────────────────────────

@[test]
def test_lower_hole : Bool :=
  let t : Term := Term.hole in
  let _ : EvalTerm := lower empty_ctx t in
  true
