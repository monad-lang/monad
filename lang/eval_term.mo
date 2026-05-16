/// Multiplicity for linear type system.
type Multiplicity {
  zero,
  many,
  linear,
  affine,
}

/// Memory region classification.
type Region {
  r_stack,
  r_heap,
  r_borrow (depth: I64),
  r_param (index: I64),
}

/// Borrow kind.
type BorrowKind {
  shared,
  unique,
}

/// Recursor metadata.
type RecursorInfo {
  mk (rec_idx: I64) (n_cases: I64) (motive_arity: I64),
}

/// EvalTerm-level literal values.
type EvalLiteral {
  l_int (v: I64),
  l_str (value: String),
  l_float (value: String),
  l_bool (v: Bool),
  l_sort (level: I64),
}

/// EvalTerm — the lowered term representation.
type EvalTerm {
  evar (idx: I64),
  elam (param_mult: Multiplicity) (body: EvalTerm),
  eapp (fun: EvalTerm) (arg: EvalTerm),
  econst (idx: I64),
  esort (level: I64),
  elit (l: EvalLiteral),
  eprim (idx: I64) (args: List EvalTerm),
  erecursor (info: RecursorInfo) (cases: List EvalTerm) (scrutinee: EvalTerm),
  eregion (region: Region) (mult: Multiplicity) (body: EvalTerm),
  eborrow (region: Region) (kind: BorrowKind) (body: EvalTerm),
  eproj (field: I64) (arg: EvalTerm),
  eproj_field (field: I64) (base: EvalTerm),
}

open EvalTerm
open Multiplicity
open Region
open BorrowKind
open EvalLiteral
open RecursorInfo

// ─── Basic constructor tests ───────────────────────────────────────────

@[test]
def test_construct_evar : Bool :=
  let v : EvalTerm := evar 0 in
  true

@[test]
def test_construct_econst : Bool :=
  let c : EvalTerm := econst 5 in
  true

@[test]
def test_construct_esort : Bool :=
  let s : EvalTerm := esort 1 in
  true

// ─── EvalLiteral tests ─────────────────────────────────────────────────

@[test]
def test_literal_int : Bool :=
  let l : EvalLiteral := l_int 42 in
  true

@[test]
def test_literal_str : Bool :=
  let l : EvalLiteral := l_str "hello" in
  true

@[test]
def test_literal_bool : Bool :=
  let l : EvalLiteral := l_bool true in
  true

@[test]
def test_literal_sort : Bool :=
  let l : EvalLiteral := l_sort 0 in
  true

@[test]
def test_elit_int : Bool :=
  let t : EvalTerm := elit (l_int 42) in
  true

@[test]
def test_elit_bool : Bool :=
  let t : EvalTerm := elit (l_bool false) in
  true

// ─── Multiplicity tests ────────────────────────────────────────────────

@[test]
def test_multiplicity_zero : Bool :=
  let m : Multiplicity := zero in
  true

@[test]
def test_multiplicity_many : Bool :=
  let m : Multiplicity := many in
  true

@[test]
def test_multiplicity_linear : Bool :=
  let m : Multiplicity := linear in
  true

@[test]
def test_multiplicity_affine : Bool :=
  let m : Multiplicity := affine in
  true

// ─── Region tests ──────────────────────────────────────────────────────

@[test]
def test_region_stack : Bool :=
  let r : Region := r_stack in
  true

@[test]
def test_region_heap : Bool :=
  let r : Region := r_heap in
  true

@[test]
def test_region_borrow : Bool :=
  let r : Region := r_borrow 0 in
  true

@[test]
def test_region_param : Bool :=
  let r : Region := r_param 1 in
  true

// ─── BorrowKind tests ──────────────────────────────────────────────────

@[test]
def test_borrow_shared : Bool :=
  let bk : BorrowKind := shared in
  true

@[test]
def test_borrow_unique : Bool :=
  let bk : BorrowKind := unique in
  true

// ─── RecursorInfo tests ────────────────────────────────────────────────

@[test]
def test_recursor_info : Bool :=
  let info : RecursorInfo := mk 0 3 1 in
  true

// ─── Complex constructor tests ─────────────────────────────────────────

@[test]
def test_construct_elam : Bool :=
  let body : EvalTerm := evar 0 in
  let l : EvalTerm := elam many body in
  true

@[test]
def test_construct_eapp : Bool :=
  let f : EvalTerm := evar 0 in
  let a : EvalTerm := evar 1 in
  let app : EvalTerm := eapp f a in
  true

@[test]
def test_construct_eprim : Bool :=
  let arg : EvalTerm := elit (l_int 1) in
  let args : List EvalTerm := List.cons arg List.empty in
  let p : EvalTerm := eprim 0 args in
  true

@[test]
def test_construct_erecursor : Bool :=
  let info : RecursorInfo := mk 0 2 1 in
  let c0 : EvalTerm := econst 0 in
  let c1 : EvalTerm := econst 1 in
  let cases : List EvalTerm := List.cons c0 (List.cons c1 List.empty) in
  let s : EvalTerm := evar 0 in
  let r : EvalTerm := erecursor info cases s in
  true

@[test]
def test_construct_eregion : Bool :=
  let r : EvalTerm := eregion r_stack many (evar 0) in
  true

@[test]
def test_construct_eborrow : Bool :=
  let r : EvalTerm := eborrow r_heap shared (evar 0) in
  true

@[test]
def test_construct_eproj : Bool :=
  let p : EvalTerm := eproj 0 (evar 0) in
  true

@[test]
def test_construct_eproj_field : Bool :=
  let p : EvalTerm := eproj_field 1 (evar 0) in
  true
