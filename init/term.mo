/// Terms defined in Monad

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
 nop (Operator)
}

struct Param {
 name: Identifier,
 type_: Term,
}

struct Let {
 name: Identifier,
 type_: Term,
 value: Term,
 body: Term
}

struct MatchCase {
  name: Identifier,
  args: List Identifier,
  value: Term,
}

struct Native {
  native_name: Identifier,
  num_args: Nat,
  args: List (Option Term),
}

type Term {
 forall (name: Identifier),
 pi (arg: Term) (ret: Term),
 var (name: NameRef),
 lam (param: Param) (body: Term),
 app (fun: Term) (arg: Term),
 let_ (let_: Let),
 lit (lit: Literal),
 match_ (value: Term) (cases: MatchCase),
 con (constructor: Con)
 ntv (native: Native),
 type_ (universe: Nat),
 prop,
 hole,
}

