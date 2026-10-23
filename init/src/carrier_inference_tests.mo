use std::test {}

// The argument-carrier sources the retired syntactic class-call pass
// (`resolve_class_calls_decls`) provided via `infer_carrier_type` /
// `infer_all_carriers_from_args_go`, pinned on the checker alone. Each one
// is a shape where a class call has NO expectation of its own and the
// carrier exists only in a SIBLING argument or in a constructor's own
// parameter -- with the pass gone, every row below is `no instance found`
// unless the checker reads them (measured: 150/150 on lang/src/module.mo
// either way, so these are the discriminating rows).

// --- A class method's lambda argument learns its parameters from the
// call's LATER arguments. `Fold2.foldl2 f z t` pairs `f` with the still
// abstract `B -> A -> B` when arguments are checked left to right; `0` and
// `some 42` are what solve `B := I64` and `A := I64`, and only then does
// `acc + x` inside the lambda have a carrier to resolve `HAdd.add` at.
class Fold2 (T : Type -> Type) {
  def foldl2 (f : B -> A -> B) (z : B) (t : T A) : B
  def foldr2 (f : A -> B -> B) (z : B) (t : T A) : B
}

pub instance Fold2 Option {
  def foldl2 (f : B -> A -> B) (z : B) (t : Option A) : B :=
    match t {
      none => z,
      some a => f z a
    }
  def foldr2 (f : A -> B -> B) (z : B) (t : Option A) : B :=
    match t {
      none => z,
      some a => f a z
    }
}

#[test]
def test_foldl2_element_type_comes_from_its_argument : Bool :=
  let r : I64 := Fold2.foldl2 (fn acc x => acc + x) 0 (some 42) in
  r == 42

// The same call with the element type genuinely unconstrained (`none`).
// `foldr2`'s first binder is that unconstrained `A`, so the lambda's binder
// hint is REFUSED and the chain-solved codomain (`I64 -> I64`, from `0`) is
// the only expectation its body can have. MEASURED: this is
// `init/src/foldable_tests.mo`'s `test_foldr_option_none`, the row that
// stayed red without it.
#[test]
def test_foldr2_none_still_types_its_lambda : Bool :=
  Fold2.foldr2 (fn x acc => x + acc) 0 none == 0

// --- A zero-argument class call in FIRST position. It has no argument and
// no expectation of its own; only the chain's next domain (`0 : I64`) names
// the instance. MEASURED: `std/src/base.mo`'s `test_bounded_max`.
class Bnd A {
  def max_bound : A
}

pub instance Bnd I64 {
  def max_bound : I64 := 0
}

#[test]
def test_zero_arg_class_call_uses_its_siblings_type : Bool :=
  BEq.beq Bnd.max_bound 0

// --- A DEF call whose first argument is a lambda: the signature has to be
// pre-solved from the arguments whose type is recoverable before the
// lambda is paired with its (still abstract) parameter. MEASURED:
// `std/src/array.mo`'s `test_array_foldl_sums`.
def dfl (f : B -> A -> B) (z : B) (t : Option A) : B :=
  match t {
    none => z,
    some a => f z a
  }

#[test]
def test_def_call_presolves_its_lambda_argument : Bool :=
  let r : I64 := dfl (fn acc x => acc + x) 0 (some 42) in
  r == 42
